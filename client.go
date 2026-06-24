//go:build !js

package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"crypto/x509"
	"encoding/binary"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"os"
	"runtime"
	"runtime/debug"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/klauspost/reedsolomon"
	utls "github.com/refraction-networking/utls"
)

const (
	NumStreams           = 6
	DataBuckets          = 8
	MSS                  = 1350
	HeaderSize           = 30
	Magic                = 0x41455448
	AuthTokenSize        = 32
	PingFlag             = 0x0001
	AuthFlag             = 0x0002
	PongFlag             = 0x0004
	AdaptiveFECFlag      = 0x0008
	ControlFrameFlag     = 0x0010
	FastLaneFlag         = 0x0020
	NackFlag             = 0x0040
	ProtocolVersion      = 6
	AetherALPN           = "http/1.1"
	DialTimeout          = 15 * time.Second
	HandshakeTimeout     = 15 * time.Second
	MaxConcurrentConns   = 2000
	ReconnectBaseDelay   = 2 * time.Second
	ReconnectMaxDelay    = 30 * time.Second
	ReconnectStagger     = 500 * time.Millisecond
	SafeMTUPayload       = 1350
	TCPBufferSize        = 2 << 20
	MaxReorderWindow     = 65536
	MaxReassemblerBuf    = 64 << 20
	ReassemblerOutputCap = 2048
	SmallPacketFastLen   = 1200
	ReassemblerGapTTL    = 10 * time.Second
	NackRetryInterval    = 1500 * time.Millisecond
	NackMaxAttempts      = 1
	RetransmitCacheSeqs  = 8192
	TunnelWriteTimeout   = 5 * time.Second
	LocalWriteTimeout    = 5 * time.Second
	ProxyIdleTimeout     = 3 * time.Minute
	LocalReadBufferSize  = 4*MSS - 7
	DebugLogging         = false
)

var (
	LocalProxyListenAddr = "0.0.0.0:11080"
	ClientCfgFile        = "aether_client.json"
	shardPool            = sync.Pool{New: func() interface{} { b := make([]byte, HeaderSize+MSS+1024); return &b }}
	framePool            = sync.Pool{New: func() interface{} { return make([]byte, 16384) }}
	outputPool           = sync.Pool{New: func() interface{} { return make([]byte, 6*MSS+1024) }}
	randSeed             = uint32(time.Now().UnixNano())
	fecPool              sync.Map
)

func debugf(format string, args ...interface{}) {
	if DebugLogging {
		log.Printf(format, args...)
	}
}

func shouldLogEvery(slot *atomic.Int64, interval time.Duration) bool {
	now := time.Now().UnixNano()
	last := slot.Load()
	if now-last < interval.Nanoseconds() {
		return false
	}
	return slot.CompareAndSwap(last, now)
}

func getEncoder(ds, ps int) reedsolomon.Encoder {
	if ds <= 0 {
		ds = 4
	}
	if ps <= 0 {
		ps = 2
	}
	key := (uint32(ds) << 16) | uint32(ps)
	if v, ok := fecPool.Load(key); ok {
		return v.(reedsolomon.Encoder)
	}
	enc, err := reedsolomon.New(ds, ps)
	if err == nil {
		fecPool.Store(key, enc)
		return enc
	}
	return nil
}

func fastRand() uint32 {
	val := atomic.AddUint32(&randSeed, 12345)
	val ^= val << 13
	val ^= val >> 17
	val ^= val << 5
	return val
}

func generateSmartPadding(payloadSize int) uint16 {
	if payloadSize >= SafeMTUPayload {
		return 0
	}
	remaining := SafeMTUPayload - payloadSize
	maxPad := 48
	switch {
	case payloadSize <= HeaderSize:
		maxPad = 64
	case payloadSize <= HeaderSize+AuthTokenSize:
		maxPad = 96
	case payloadSize < 256:
		maxPad = 128
	}
	if maxPad > remaining {
		maxPad = remaining
	}
	if maxPad <= 0 {
		return 0
	}
	minPad := 0
	if payloadSize <= HeaderSize+AuthTokenSize && maxPad >= 8 {
		minPad = 8
	}
	return uint16(minPad + int(fastRand()%uint32(maxPad-minPad+1)))
}

func GetShardPtr() *[]byte {
	bp := shardPool.Get().(*[]byte)
	*bp = (*bp)[:cap(*bp)]
	return bp
}

func PutShardPtr(bp *[]byte) {
	shardPool.Put(bp)
}

type TokenBucket struct {
	capacity  float64
	tokens    float64
	rate      float64
	lastToken time.Time
	mu        sync.Mutex
}

func NewTokenBucket(rate, capacity float64) *TokenBucket {
	return &TokenBucket{
		capacity:  capacity,
		tokens:    capacity,
		rate:      rate,
		lastToken: time.Now(),
	}
}

func (tb *TokenBucket) Wait(cost float64) {
	if tb == nil || tb.rate >= 1<<29 {
		return
	}
	tb.mu.Lock()
	now := time.Now()
	if now.After(tb.lastToken) {
		elapsed := now.Sub(tb.lastToken).Seconds()
		tb.tokens += elapsed * tb.rate
		if tb.tokens > tb.capacity {
			tb.tokens = tb.capacity
		}
		tb.lastToken = now
	}

	if tb.tokens >= cost {
		tb.tokens -= cost
		tb.mu.Unlock()
		return
	}

	deficit := cost - tb.tokens
	sleepDur := time.Duration((deficit / tb.rate) * float64(time.Second))
	tb.tokens = 0
	tb.lastToken = time.Now().Add(sleepDur)
	tb.mu.Unlock()
	time.Sleep(sleepDur)
}

func getAuthSecret(user, pass string) string {
	return fmt.Sprintf("%x", sha256.Sum256([]byte(user+":"+pass)))
}

func deriveToken(sec string, ts uint32) [32]byte {
	h := sha256.New()
	h.Write([]byte(sec))
	b := make([]byte, 4)
	binary.BigEndian.PutUint32(b, ts)
	h.Write(b)
	var t [32]byte
	copy(t[:], h.Sum(nil))
	return t
}

type PacketHeader struct {
	Magic      uint32
	ClientID   uint32
	SeqNo      uint32
	ShardIdx   uint16
	Flags      uint16
	PaddingLen uint16
	ChunkSize  uint32
	Timestamp  uint32
	Reserved   uint32
}

func (h *PacketHeader) EncodeTo(b []byte) {
	binary.BigEndian.PutUint32(b[0:4], h.Magic)
	binary.BigEndian.PutUint32(b[4:8], h.ClientID)
	binary.BigEndian.PutUint32(b[8:12], h.SeqNo)
	binary.BigEndian.PutUint16(b[12:14], h.ShardIdx)
	binary.BigEndian.PutUint16(b[14:16], h.Flags)
	binary.BigEndian.PutUint16(b[16:18], h.PaddingLen)
	binary.BigEndian.PutUint32(b[18:22], h.ChunkSize)
	binary.BigEndian.PutUint32(b[22:26], h.Timestamp)
	binary.BigEndian.PutUint32(b[26:30], h.Reserved)
}

func DecodeHeader(b []byte) *PacketHeader {
	return &PacketHeader{
		Magic:      binary.BigEndian.Uint32(b[0:4]),
		ClientID:   binary.BigEndian.Uint32(b[4:8]),
		SeqNo:      binary.BigEndian.Uint32(b[8:12]),
		ShardIdx:   binary.BigEndian.Uint16(b[12:14]),
		Flags:      binary.BigEndian.Uint16(b[14:16]),
		PaddingLen: binary.BigEndian.Uint16(b[16:18]),
		ChunkSize:  binary.BigEndian.Uint32(b[18:22]),
		Timestamp:  binary.BigEndian.Uint32(b[22:26]),
		Reserved:   binary.BigEndian.Uint32(b[26:30]),
	}
}

func (h *PacketHeader) GetFEC() (ds uint8, ps uint8) {
	if h.Flags&AdaptiveFECFlag != 0 {
		return uint8(h.Reserved >> 24), uint8((h.Reserved >> 16) & 0xFF)
	}
	return 5, 1
}

func (h *PacketHeader) SetFEC(ds uint8, ps uint8) {
	h.Flags |= AdaptiveFECFlag
	h.Reserved = (uint32(ds) << 24) | (uint32(ps) << 16) | (h.Reserved & 0xFFFF)
	h.Reserved = (h.Reserved & 0xFFFFFF00) | ProtocolVersion
}

func (h *PacketHeader) SetBucket(bucket uint8) {
	h.Reserved = (h.Reserved & 0xFFFF00FF) | (uint32(bucket) << 8)
}

func (h *PacketHeader) GetBucket() uint8 {
	return uint8((h.Reserved >> 8) & 0xFF)
}

type parsedFrame struct {
	Type    byte
	ConnID  uint32
	Payload []byte
}

func parseFrames(buf *[]byte, d []byte) ([]parsedFrame, bool) {
	c := d
	if len(*buf) > 0 {
		c = append(*buf, d...)
	}
	if len(c) > 128<<10 {
		*buf = (*buf)[:0]
		return nil, false
	}
	var fs []parsedFrame
	o := 0
	for o+7 <= len(c) {
		t := c[o]
		id := binary.BigEndian.Uint32(c[o+1 : o+5])
		pl := int(binary.BigEndian.Uint16(c[o+5 : o+7]))
		if o+7+pl > len(c) {
			break
		}
		p := make([]byte, pl)
		copy(p, c[o+7:o+7+pl])
		fs = append(fs, parsedFrame{t, id, p})
		o += 7 + pl
	}
	if o < len(c) {
		tmp := make([]byte, len(c)-o)
		copy(tmp, c[o:])
		*buf = tmp
	} else {
		*buf = (*buf)[:0]
	}
	return fs, true
}

type TCPReassemblerEntry struct {
	shards    map[uint16]*[]byte
	chunkSize uint32
	received  int
	createdAt time.Time
	ds, ps    uint8
}

type RetransmitCache struct {
	mu    sync.Mutex
	m     map[uint64]map[uint16][]byte
	order []uint64
	max   int
}

func NewRetransmitCache(max int) *RetransmitCache {
	return &RetransmitCache{m: make(map[uint64]map[uint16][]byte), max: max}
}

func rtxKey(bucket uint8, seq uint32) uint64 {
	return (uint64(bucket) << 32) | uint64(seq)
}

func splitRtxKey(key uint64) (uint8, uint32) {
	return uint8(key >> 32), uint32(key)
}

func (rc *RetransmitCache) Store(bucket uint8, seq uint32, shard uint16, pkt []byte) {
	if rc == nil || len(pkt) == 0 {
		return
	}
	cp := make([]byte, len(pkt))
	copy(cp, pkt)
	key := rtxKey(bucket, seq)
	rc.mu.Lock()
	if rc.m[key] == nil {
		rc.m[key] = make(map[uint16][]byte)
		rc.order = append(rc.order, key)
		for len(rc.order) > rc.max {
			old := rc.order[0]
			rc.order = rc.order[1:]
			delete(rc.m, old)
		}
	}
	rc.m[key][shard] = cp
	rc.mu.Unlock()
}

func (rc *RetransmitCache) Get(bucket uint8, seq uint32) [][]byte {
	if rc == nil {
		return nil
	}
	rc.mu.Lock()
	defer rc.mu.Unlock()
	shards := rc.m[rtxKey(bucket, seq)]
	if len(shards) == 0 {
		return nil
	}
	out := make([][]byte, 0, len(shards))
	for _, pkt := range shards {
		cp := make([]byte, len(pkt))
		copy(cp, pkt)
		out = append(out, cp)
	}
	return out
}

func (rc *RetransmitCache) Stats() (count int, oldestBucket uint8, oldest uint32, newestBucket uint8, newest uint32) {
	if rc == nil {
		return 0, 0, 0, 0, 0
	}
	rc.mu.Lock()
	defer rc.mu.Unlock()
	count = len(rc.m)
	if len(rc.order) > 0 {
		oldestBucket, oldest = splitRtxKey(rc.order[0])
		newestBucket, newest = splitRtxKey(rc.order[len(rc.order)-1])
	}
	return count, oldestBucket, oldest, newestBucket, newest
}

type decodedRecord struct {
	decodedAt time.Time
}

type TCPReassembler struct {
	mu              sync.Mutex
	windows         map[uint32]*TCPReassemblerEntry
	decoded         map[uint32]*decodedRecord
	outputCh        chan []byte
	nackCh          chan uint32
	clientID        uint32
	cleanupTicker   *time.Ticker
	stopCh          chan struct{}
	reasmCh         chan reasmEvent
	decodedTTL      time.Duration
	closeOnce       sync.Once
	wcOnce          sync.Once
	initialized     bool
	nextExpectedSeq uint32
	readyBuffer     map[uint32][]byte
	bufferedBytes   int
	lastAdvance     time.Time
	gapNackSeq      uint32
	gapNackAttempts int
	gapStart        time.Time
	lastNack        time.Time
}

func NewTCPReassembler(cid uint32, ttl time.Duration) *TCPReassembler {
	ar := &TCPReassembler{
		windows:     make(map[uint32]*TCPReassemblerEntry),
		decoded:     make(map[uint32]*decodedRecord),
		outputCh:    make(chan []byte, ReassemblerOutputCap),
		nackCh:      make(chan uint32, 64),
		clientID:    cid,
		stopCh:      make(chan struct{}),
		decodedTTL:  ttl,
		readyBuffer: make(map[uint32][]byte),
		lastAdvance: time.Now(),
	}
	cleanupInterval := ttl / 4
	if cleanupInterval > 500*time.Millisecond {
		cleanupInterval = 500 * time.Millisecond
	}
	if cleanupInterval < 200*time.Millisecond {
		cleanupInterval = 200 * time.Millisecond
	}
	ar.cleanupTicker = time.NewTicker(cleanupInterval)
	go ar.cleanupLoop()
	return ar
}

func (ar *TCPReassembler) AddShard(seqNo uint32, shardIdx uint16, chunkSize uint32, dataPtr *[]byte, ds, ps uint8) {
	ar.mu.Lock()
	if !ar.initialized {
		ar.nextExpectedSeq = seqNo
		ar.initialized = true
		ar.lastAdvance = time.Now()
	}
	if int32(seqNo-ar.nextExpectedSeq) < 0 || ar.decoded[seqNo] != nil {
		ar.mu.Unlock()
		PutShardPtr(dataPtr)
		return
	}
	if (seqNo-ar.nextExpectedSeq > MaxReorderWindow && len(ar.readyBuffer) > 100) || ar.bufferedBytes > MaxReassemblerBuf {
		ar.mu.Unlock()
		PutShardPtr(dataPtr)
		log.Printf("[WARN] reassembler overflow: seq=%d expected=%d buffered=%d, rebooting", seqNo, ar.nextExpectedSeq, ar.bufferedBytes)
		ar.Close()
		return
	}
	if ds == 0 {
		ds, ps = 4, 2
	}
	e, ok := ar.windows[seqNo]
	if !ok {
		e = &TCPReassemblerEntry{
			shards:    make(map[uint16]*[]byte),
			chunkSize: chunkSize,
			createdAt: time.Now(),
			ds:        ds,
			ps:        ps,
		}
		ar.windows[seqNo] = e
	}
	if _, dup := e.shards[shardIdx]; dup {
		ar.mu.Unlock()
		PutShardPtr(dataPtr)
		return
	}
	e.shards[shardIdx] = dataPtr
	e.received++
	var shardsClone map[uint16]*[]byte
	triggerDecode := e.received >= int(e.ds)
	if triggerDecode {
		shardsClone = make(map[uint16]*[]byte)
		for k, v := range e.shards {
			shardsClone[k] = v
		}
	}
	ar.mu.Unlock()
	if triggerDecode {
		if res := ar.decodeOutsideLock(chunkSize, shardsClone, e.ds, e.ps); res != nil {
			ar.mu.Lock()
			if cur := ar.windows[seqNo]; cur == e {
				delete(ar.windows, seqNo)
				for _, sp := range e.shards {
					if sp != nil {
						PutShardPtr(sp)
					}
				}
			}
			ar.mu.Unlock()
			ar.commitDecodedAndSend(seqNo, res)
		}
	}
}

func (ar *TCPReassembler) commitDecodedAndSend(seqNo uint32, data []byte) {
	ar.mu.Lock()
	if old := ar.readyBuffer[seqNo]; old != nil {
		ar.bufferedBytes -= len(old)
		outputPool.Put(old[:cap(old)])
	}
	ar.decoded[seqNo] = &decodedRecord{decodedAt: time.Now()}
	ar.readyBuffer[seqNo] = data
	ar.bufferedBytes += len(data)
	if ar.bufferedBytes > MaxReassemblerBuf {
		ar.mu.Unlock()
		log.Printf("[WARN] reassembler buffered payload exceeded %d bytes, rebooting", MaxReassemblerBuf)
		ar.Close()
		return
	}
	ar.drainReady()
	ar.mu.Unlock()
}

func (ar *TCPReassembler) decodeOutsideLock(chunkSize uint32, shardsClone map[uint16]*[]byte, ds, ps uint8) []byte {
	if chunkSize == 0 || uint64(chunkSize) > uint64(int(ds)*MSS) {
		return nil
	}
	enc := getEncoder(int(ds), int(ps))
	if enc == nil {
		return nil
	}
	ss := int((uint64(chunkSize) + uint64(ds) - 1) / uint64(ds))
	total := int(ds) + int(ps)
	matrix := make([][]byte, total)
	for i, dp := range shardsClone {
		if int(i) < total && dp != nil {
			matrix[i] = (*dp)[HeaderSize : HeaderSize+ss]
		}
	}
	if err := enc.Reconstruct(matrix); err != nil {
		return nil
	}
	res := outputPool.Get().([]byte)[:0]
	for i := 0; i < int(ds); i++ {
		if matrix[i] != nil {
			res = append(res, matrix[i]...)
		}
	}
	if len(res) > int(chunkSize) {
		res = res[:chunkSize]
	}
	return res
}

func (ar *TCPReassembler) drainReady() {
	for {
		payload, exists := ar.readyBuffer[ar.nextExpectedSeq]
		if !exists {
			break
		}

		if payload != nil {
			select {
			case ar.outputCh <- payload:
			case <-ar.stopCh:
				return
			default:
				log.Printf("[WARN] reassembler output queue full: expected=%d buffered=%d, closing reassembler", ar.nextExpectedSeq, ar.bufferedBytes)
				ar.Close()
				return
			}
		} else {
			select {
			case ar.outputCh <- nil:
			case <-ar.stopCh:
				return
			default:
				log.Printf("[WARN] reassembler gap marker blocked: expected=%d buffered=%d", ar.nextExpectedSeq, ar.bufferedBytes)
				ar.Close()
				return
			}
		}

		delete(ar.readyBuffer, ar.nextExpectedSeq)
		ar.bufferedBytes -= len(payload)
		ar.nextExpectedSeq++
		ar.lastAdvance = time.Now()
		ar.gapNackSeq = 0
		ar.gapNackAttempts = 0
		ar.lastNack = time.Time{}
	}

	for s := range ar.readyBuffer {
		if int32(s-ar.nextExpectedSeq) < 0 {
			if payload := ar.readyBuffer[s]; payload != nil {
				ar.bufferedBytes -= len(payload)
				outputPool.Put(payload[:cap(payload)])
			}
			delete(ar.readyBuffer, s)
		}
	}
}

func (ar *TCPReassembler) Output() <-chan []byte {
	return ar.outputCh
}

func (ar *TCPReassembler) NACK() <-chan uint32 {
	return ar.nackCh
}

func (ar *TCPReassembler) failGapLocked(now time.Time) {
	skipTo := ar.nextExpectedSeq + 1
	for seq, payload := range ar.readyBuffer {
		if int32(seq-skipTo) >= 0 {
			skipTo = seq + 1
		}
		if payload != nil {
			outputPool.Put(payload[:cap(payload)])
		}
	}
	for seq, e := range ar.windows {
		if int32(seq-skipTo) >= 0 {
			skipTo = seq + 1
		}
		for _, sp := range e.shards {
			if sp != nil {
				PutShardPtr(sp)
			}
		}
	}
	ar.windows = make(map[uint32]*TCPReassemblerEntry)
	ar.decoded = make(map[uint32]*decodedRecord)
	ar.readyBuffer = make(map[uint32][]byte)
	ar.bufferedBytes = 0
	ar.nextExpectedSeq = skipTo
	ar.initialized = true
	ar.gapNackSeq = 0
	ar.gapNackAttempts = 0
	ar.gapStart = time.Time{}
	ar.lastNack = time.Time{}
	ar.lastAdvance = now
	select {
	case ar.outputCh <- nil:
	case <-ar.stopCh:
	default:
		log.Printf("[WARN] reassembler gap reset marker blocked: expected=%d", ar.nextExpectedSeq)
		ar.Close()
	}
}

func (ar *TCPReassembler) cleanupLoop() {
	for {
		select {
		case <-ar.stopCh:
			return
		case <-ar.cleanupTicker.C:
			ar.cleanupStale()
		}
	}
}

func (ar *TCPReassembler) cleanupStale() {
	ar.mu.Lock()
	n := time.Now()
	if len(ar.readyBuffer) > 0 && n.Sub(ar.lastAdvance) > NackRetryInterval {
		seq := ar.nextExpectedSeq
		if ar.gapNackSeq != seq {
			if ar.gapNackSeq == 0 {
				ar.gapStart = n
				ar.gapNackAttempts = 0
			}
			ar.gapNackSeq = seq
			ar.lastNack = time.Time{}
		}
		if ar.gapNackAttempts < NackMaxAttempts && (ar.lastNack.IsZero() || n.Sub(ar.lastNack) >= NackRetryInterval) {
			select {
			case ar.nackCh <- seq:
			default:
			}
			ar.gapNackAttempts++
			ar.lastNack = n
			if ar.gapNackAttempts == 2 || ar.gapNackAttempts == NackMaxAttempts {
				log.Printf("[WARN] reassembler gap seq=%d ready=%d buffered=%d; NACK attempt %d/%d", seq, len(ar.readyBuffer), ar.bufferedBytes, ar.gapNackAttempts, NackMaxAttempts)
			}
		}
		if !ar.gapStart.IsZero() && n.Sub(ar.gapStart) > ReassemblerGapTTL {
			log.Printf("[WARN] reassembler gap timeout: expected=%d ready=%d buffered=%d; resetting data window", ar.nextExpectedSeq, len(ar.readyBuffer), ar.bufferedBytes)
			ar.failGapLocked(n)
			} else if len(ar.readyBuffer) > 200 {
				log.Printf("[WARN] reassembler buffer overflow: expected=%d ready=%d buffered=%d; force resetting", ar.nextExpectedSeq, len(ar.readyBuffer), ar.bufferedBytes)
				ar.failGapLocked(n)
		}
	}
	for k, r := range ar.decoded {
		if int32(k-ar.nextExpectedSeq) < 0 || n.Sub(r.decodedAt) > ar.decodedTTL {
			delete(ar.decoded, k)
		}
	}
	for k, e := range ar.windows {
		if n.Sub(e.createdAt) > ar.decodedTTL {
			for _, sp := range e.shards {
				if sp != nil {
					PutShardPtr(sp)
				}
			}
			delete(ar.windows, k)
		}
	}
	ar.mu.Unlock()
}

func (ar *TCPReassembler) Close() {
	ar.closeOnce.Do(func() {
		ar.cleanupTicker.Stop()
		close(ar.stopCh)
	})
}

type SafeStream struct {
	conn      net.Conn
	mu        sync.Mutex
	closed    atomic.Bool
	srtt      atomic.Int64
	rttVar    atomic.Int64
	lossCount atomic.Uint32
	pingCh    chan struct{}
}

func (s *SafeStream) Write(b []byte) (int, error) {
	if s.closed.Load() {
		return 0, io.EOF
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	s.conn.SetWriteDeadline(time.Now().Add(TunnelWriteTimeout))
	defer s.conn.SetWriteDeadline(time.Time{})
	n, err := s.conn.Write(b)
	if err != nil {
		s.Close()
	}
	return n, err
}

func (s *SafeStream) Close() {
	if s.closed.CompareAndSwap(false, true) {
		s.conn.Close()
		close(s.pingCh)
	}
}

func (s *SafeStream) IsClosed() bool {
	return s.closed.Load()
}

func (s *SafeStream) UpdateRTT(m int64) {
	sr := s.srtt.Load()
	if sr == 0 {
		s.srtt.Store(m)
		s.rttVar.Store(m / 2)
		return
	}
	v := s.rttVar.Load()
	diff := m - sr
	if diff < 0 {
		diff = -diff
	}
	s.rttVar.Store((3*v + diff) / 4)
	s.srtt.Store((7*sr + m) / 8)
}

type ProxyConn struct {
	connID       uint32
	conn         net.Conn
	cl           atomic.Bool
	lastActive   atomic.Int64
	connectAckCh chan struct{}
	connectErrCh chan struct{}
	wc           chan []byte
	done         chan struct{}
	closeOnce    sync.Once
	wcOnce       sync.Once
	udpAssoc     bool
	udpMu        sync.RWMutex
	udpAddr      *net.UDPAddr
}

func (pc *ProxyConn) touch() {
	pc.lastActive.Store(time.Now().UnixNano())
}

func (pc *ProxyConn) idleFor(now time.Time) time.Duration {
	last := pc.lastActive.Load()
	if last == 0 {
		return 0
	}
	return now.Sub(time.Unix(0, last))
}

func (pc *ProxyConn) closeWriteQueue() {
	pc.wcOnce.Do(func() {
		if pc.wc != nil {
			close(pc.wc)
		}
	})
}

func (pc *ProxyConn) closeLocal() {
	pc.cl.Store(true)
	pc.closeOnce.Do(func() { close(pc.done) })
	pc.conn.Close()
}
func (pc *ProxyConn) setUDPAddr(addr *net.UDPAddr) {
	if addr == nil {
		return
	}
	cp := *addr
	if addr.IP != nil {
		cp.IP = append(net.IP(nil), addr.IP...)
	}
	pc.udpMu.Lock()
	pc.udpAddr = &cp
	pc.udpMu.Unlock()
}

func (pc *ProxyConn) getUDPAddr() *net.UDPAddr {
	pc.udpMu.RLock()
	defer pc.udpMu.RUnlock()
	if pc.udpAddr == nil {
		return nil
	}
	cp := *pc.udpAddr
	if pc.udpAddr.IP != nil {
		cp.IP = append(net.IP(nil), pc.udpAddr.IP...)
	}
	return &cp
}

type reasmEvent struct {
	bucket  uint8
	control bool
	nack    bool
	closed  bool
	seq     uint32
	data    []byte
}

func muxBucket(data []byte) uint8 {
	if DataBuckets <= 1 || len(data) < 5 {
		return 0
	}
	id := binary.BigEndian.Uint32(data[1:5])
	return uint8(id % DataBuckets)
}

type AdaptiveDispatcher struct {
	node            NodeConfig
	clientID        uint32
	streams         []*SafeStream
	sMu             sync.RWMutex
	trs             []*TCPReassembler
	cr              *TCPReassembler
	pfbs            [][]byte
	cfb             []byte
	fws             []atomic.Uint32
	cfw             atomic.Uint32
	conns           sync.Map
	stopCh          chan struct{}
	reasmCh         chan reasmEvent
	pacing          *TokenBucket
	currentDS       uint8
	currentPS       uint8
	sdm             sync.RWMutex
	muxWriteMu      sync.Mutex
	udpMu           sync.RWMutex
	udpAssoc        *ProxyConn
	udpPeers        sync.Map
	rtx             *RetransmitCache
	nackScore       atomic.Int64
	lastNackMissLog atomic.Int64
	lastTraffic     atomic.Int64
	batchMu         sync.Mutex
	batchBufs       [][]byte
	batchActive     []bool
	// 闂佹彃绉风换娑㈠箳瑜嶉崺?	lastReconnect    time.Time
	reconnectBackoff time.Duration
	reconnectMu      sync.Mutex
	closed           atomic.Bool
}

func NewAdaptiveDispatcher(n NodeConfig) *AdaptiveDispatcher {
	cid := fastRand()
	ad := &AdaptiveDispatcher{
		node:        n,
		clientID:    cid,
		streams:     make([]*SafeStream, NumStreams),
		trs:         make([]*TCPReassembler, DataBuckets),
		pfbs:        make([][]byte, DataBuckets),
		fws:         make([]atomic.Uint32, DataBuckets),
		batchBufs:   make([][]byte, DataBuckets),
		batchActive: make([]bool, DataBuckets),
		cr:          NewTCPReassembler(cid, 30*time.Second),
		stopCh:      make(chan struct{}),
		reasmCh:     make(chan reasmEvent, DataBuckets*4+4),
		pacing:      NewTokenBucket(1<<30, 64<<20), // 濞戞挸绉村﹢顏呮償閺冨倹鏆忛悘鐐插€垮娲焻閻曞倻绀夐悹浣叉櫅缁ㄥ磭浠?TCP/BBRv3 闁煎浜滅换渚€寮ㄩ懜鍨異
		currentDS:   1,
		currentPS:   0,
		rtx:         NewRetransmitCache(RetransmitCacheSeqs),
	}
	ad.lastTraffic.Store(time.Now().UnixNano())
	for i := 0; i < DataBuckets; i++ {
		ad.trs[i] = NewTCPReassembler(cid, 30*time.Second)
		go ad.pumpReassembler(uint8(i), ad.trs[i], false)
	}
	go ad.pumpReassembler(0, ad.cr, true)
	go ad.prewarmStreams()
	go ad.monitorHealth()
	go ad.handleReassembler()
	go ad.cleanupProxyConns()
	return ad
}

func (c *AdaptiveDispatcher) pumpReassembler(bucket uint8, ar *TCPReassembler, control bool) {
	for {
		select {
		case <-c.stopCh:
			return
		case <-ar.stopCh:
			select {
			case c.reasmCh <- reasmEvent{bucket: bucket, control: control, closed: true}:
			case <-c.stopCh:
			}
			return
		case d := <-ar.Output():
			select {
			case c.reasmCh <- reasmEvent{bucket: bucket, control: control, data: d}:
			case <-c.stopCh:
				return
			}
		case seq := <-ar.NACK():
			if control {
				continue
			}
			// v5fix: handle NACK inline per-bucket to avoid blocking other buckets
			c.sendNACK(bucket, seq)
		}
	}
}
func (c *AdaptiveDispatcher) prewarmStreams() {
	var wg sync.WaitGroup
	for i := 0; i < NumStreams; i++ {
		wg.Add(1)
		go func(idx int) {
			defer wg.Done()
			select {
			case <-c.stopCh:
				return
			default:
			}
			st := c.dialStream(idx)
			if st == nil {
				return
			}
			c.sMu.Lock()
			if c.streams[idx] == nil || c.streams[idx].IsClosed() {
				c.streams[idx] = st
				st = nil
			}
			c.sMu.Unlock()
			if st != nil {
				st.Close()
			}
		}(i)
	}
	wg.Wait()
}

func (c *AdaptiveDispatcher) reboot() {
	if c.closed.Load() {
		return
	}
	log.Printf("[CLI] 妫ｅ啯鏆?鐎殿喗娲橀幖鎼佹⒐閹稿孩顦ч梻鍌涙綑娴犵姴顭ㄩ悙鏉戠仐闁轰胶澧楀畵浣该规担宄扮船闂佹彃绉靛畷顖炲锤韫囥儳绀夐柟绗涘棭鏀介悗鐟邦槸閸欏繘鎮滈銏犳闁?..")
	c.Close()
	go func() {
		time.Sleep(500 * time.Millisecond)
		applyEngine()
	}()
}

func (c *AdaptiveDispatcher) Close() {
	if c.closed.Swap(true) {
		return // 鐎规瓕灏欑划锟犲礂閹惰姤锛旈柨娑樼焸濡茶顫?double-close panic
	}
	select {
	case <-c.stopCh:
		return
	default:
		close(c.stopCh)
	}
	c.sMu.Lock()
	for i, st := range c.streams {
		if st != nil {
			st.Close()
			c.streams[i] = nil
		}
	}
	c.sMu.Unlock()
	for _, tr := range c.trs {
		if tr != nil {
			tr.Close()
		}
	}
	c.cr.Close()
	c.conns.Range(func(k, v interface{}) bool {
		pc := v.(*ProxyConn)
		pc.closeLocal()
		c.conns.Delete(k)
		return true
	})
}

func (c *AdaptiveDispatcher) cleanupProxyConns() {
	tk := time.NewTicker(30 * time.Second)
	defer tk.Stop()
	for {
		select {
		case <-c.stopCh:
			return
		case <-tk.C:
			now := time.Now()
			c.conns.Range(func(k, v interface{}) bool {
				pc := v.(*ProxyConn)
				if pc.cl.Load() {
					c.conns.Delete(k)
					return true
				}
				if pc.idleFor(now) > ProxyIdleTimeout {
					debugf("[CLI] closing idle proxy conn: connID=%d idle=%s", pc.connID, pc.idleFor(now).Round(time.Second))
					pc.closeLocal()
					c.conns.Delete(k)
				}
				return true
			})
		}
	}
}

func TuneTCPConn(conn net.Conn) {
	if tc, ok := conn.(*net.TCPConn); ok {
		tc.SetNoDelay(true)
		tc.SetReadBuffer(TCPBufferSize)
		tc.SetWriteBuffer(TCPBufferSize)
		tc.SetKeepAlive(true)
		tc.SetKeepAlivePeriod(15 * time.Second)
	}
}

func normalizeFingerprint(s string) string {
	s = strings.ToLower(strings.TrimSpace(s))
	s = strings.ReplaceAll(s, ":", "")
	s = strings.ReplaceAll(s, " ", "")
	return s
}
func (c *AdaptiveDispatcher) getTlsConfig() *utls.Config {
	sni := c.node.SNI
	if sni == "" {
		host, _, err := net.SplitHostPort(c.node.Server)
		if err == nil {
			sni = host
		} else {
			sni = c.node.Server
		}
	}
	cfg := &utls.Config{
		ServerName:         sni,
		InsecureSkipVerify: true,
		NextProtos:         []string{AetherALPN},
	}
	pin := normalizeFingerprint(c.node.CertSHA256)
	if pin != "" {
		cfg.VerifyPeerCertificate = func(rawCerts [][]byte, _ [][]*x509.Certificate) error {
			if len(rawCerts) == 0 {
				return fmt.Errorf("server certificate missing")
			}
			sum := sha256.Sum256(rawCerts[0])
			got := fmt.Sprintf("%x", sum[:])
			if got != pin {
				return fmt.Errorf("server certificate pin mismatch: got %s", got)
			}
			return nil
		}
	}
	return cfg
}

func (c *AdaptiveDispatcher) dialStream(portIdx int) *SafeStream {
	host := c.node.Server
	if idx := strings.LastIndex(host, ":"); idx > 0 {
		host = host[:idx]
	}
	addr := fmt.Sprintf("%s:%d", host, 8443+portIdx)
	rc, err := net.DialTimeout("tcp", addr, DialTimeout)
	if err != nil {
		return nil
	}
	TuneTCPConn(rc)
	uc := utls.UClient(rc, c.getTlsConfig(), utls.HelloChrome_Auto)
	uc.SetDeadline(time.Now().Add(HandshakeTimeout))
	if err := uc.Handshake(); err != nil {
		uc.Close()
		return nil
	}
	uc.SetDeadline(time.Time{})
	st := &SafeStream{conn: uc, pingCh: make(chan struct{}, 1)}
	var pl uint16
	if true {
		pl = 0 // v6: no padding
	} else {
		pl = generateSmartPadding(HeaderSize + AuthTokenSize)
	}

	ts := uint32(time.Now().UnixMilli() & 0xFFFFFFFF)
	tk := deriveToken(getAuthSecret(c.node.Username, c.node.Password), ts)

	h := &PacketHeader{
		Magic:      Magic,
		ClientID:   c.clientID,
		SeqNo:      fastRand(),
		Flags:      AuthFlag,
		PaddingLen: pl,
		ChunkSize:  AuthTokenSize,
		Timestamp:  ts,
	}
	c.sdm.RLock()
	h.SetFEC(c.currentDS, c.currentPS)
	c.sdm.RUnlock()

	b := make([]byte, HeaderSize+AuthTokenSize+int(pl))
	h.EncodeTo(b[:HeaderSize])
	copy(b[HeaderSize:HeaderSize+AuthTokenSize], tk[:])
	st.Write(b)
	go c.streamReadLoop(st)
	return st
}

func (c *AdaptiveDispatcher) streamReadLoop(st *SafeStream) {
	hb := make([]byte, HeaderSize)
	for {
		st.conn.SetReadDeadline(time.Now().Add(45 * time.Second))
		if _, e := io.ReadFull(st.conn, hb); e != nil {
			st.Close()
			return
		}
		h := DecodeHeader(hb)
		if h.Magic != Magic {
			st.Close()
			return
		}
		if h.Flags&AdaptiveFECFlag != 0 && byte(h.Reserved&0xFF) != ProtocolVersion {
			log.Printf("[CLI] protocol version mismatch: got=%d want=%d", byte(h.Reserved&0xFF), ProtocolVersion)
			st.Close()
			return
		}
		ds, ps := h.GetFEC()
		if ds > 0 && ps > 0 && h.Flags&(ControlFrameFlag|FastLaneFlag|PingFlag|PongFlag|AuthFlag|NackFlag) == 0 {
			c.sdm.Lock()
			c.currentDS = ds
			c.currentPS = ps
			c.sdm.Unlock()
		}
		ss := int((h.ChunkSize + uint32(ds) - 1) / uint32(ds))
		tl := uint32(ss) + uint32(h.PaddingLen)

		var bp *[]byte
		var bigBuf []byte
		if tl > 0 {
			if int(tl) > MSS+1024 {
				bigBuf = make([]byte, HeaderSize+int(tl))
				bp = &bigBuf
			} else {
				bp = GetShardPtr()
			}
			if _, e := io.ReadFull(st.conn, (*bp)[HeaderSize:HeaderSize+int(tl)]); e != nil {
				if bigBuf == nil {
					PutShardPtr(bp)
				}
				st.Close()
				return
			}
		}

		if h.Flags&NackFlag != 0 {
			if bp != nil && bigBuf == nil {
				PutShardPtr(bp)
			}
			c.retransmitSeq(h.GetBucket()%DataBuckets, h.SeqNo)
			continue
		}

		if h.Flags&PingFlag != 0 {
			var pl uint16 = 0 // v6: no padding for fast bypass
			p := &PacketHeader{Magic: Magic, ClientID: c.clientID, Flags: PongFlag, Timestamp: h.Timestamp, PaddingLen: pl}
			c.sdm.RLock()
			p.SetFEC(c.currentDS, c.currentPS)
			c.sdm.RUnlock()

			bo := make([]byte, HeaderSize+int(pl))
			p.EncodeTo(bo[:HeaderSize])

			if _, err := st.Write(bo); err != nil {
				st.Close()
			}

			if bp != nil && bigBuf == nil {
				PutShardPtr(bp)
			}
			continue
		}
		if h.Flags&PongFlag != 0 {
			m := time.Now().UnixMilli() - int64(h.Timestamp)
			if m > 0 && m < 5000 {
				st.UpdateRTT(m)
			}
			if bp != nil && bigBuf == nil {
				PutShardPtr(bp)
			}
			select {
			case st.pingCh <- struct{}{}:
			default:
			}
			continue
		}
		if bp != nil {
			if ds == 1 && ps == 0 {
				// v6 Split+Mirror: no FEC, direct delivery to frame parser
				payload := make([]byte, h.ChunkSize)
				copy(payload, (*bp)[HeaderSize:HeaderSize+int(h.ChunkSize)])
				if bigBuf == nil {
					PutShardPtr(bp)
				}
				if h.Flags&ControlFrameFlag != 0 {
					select {
					case c.reasmCh <- reasmEvent{bucket: 0, control: true, data: payload}:
					case <-c.stopCh:
						return
					}
				} else {
					bkt := h.GetBucket() % DataBuckets
					c.lastTraffic.Store(time.Now().UnixNano())
					select {
					case c.reasmCh <- reasmEvent{bucket: bkt, control: false, data: payload}:
					case <-c.stopCh:
						return
					}
				}
			} else {
				*bp = (*bp)[:HeaderSize+ss]
				if h.Flags&ControlFrameFlag != 0 {
					c.cr.AddShard(h.SeqNo, h.ShardIdx, h.ChunkSize, bp, ds, ps)
				} else {
					bucket := h.GetBucket() % DataBuckets
					c.lastTraffic.Store(time.Now().UnixNano())
					c.trs[bucket].AddShard(h.SeqNo, h.ShardIdx, h.ChunkSize, bp, ds, ps)
				}
			}
		}
	}
}

func (c *AdaptiveDispatcher) monitorHealth() {
	tk := time.NewTicker(5 * time.Second)
	defer tk.Stop()
	for {
		select {
		case <-c.stopCh:
			return
		case <-tk.C:
			time.Sleep(time.Duration(fastRand()%2500) * time.Millisecond)
			var wg sync.WaitGroup
			var activeCount int32
			var avgRTT int64
			var lossCount uint32

			for i := 0; i < NumStreams; i++ {
				wg.Add(1)
				go func(idx int) {
					defer wg.Done()
					c.sMu.RLock()
					st := c.streams[idx]
					c.sMu.RUnlock()

					if st == nil || st.IsClosed() {
						atomic.AddUint32(&lossCount, 1)
						time.Sleep(time.Duration(250+fastRand()%750) * time.Millisecond)
						newSt := c.dialStream(idx)
						if newSt != nil {
							c.sMu.Lock()
							c.streams[idx] = newSt
							c.sMu.Unlock()
							atomic.AddInt32(&activeCount, 1)
						}
					} else {
						atomic.AddInt32(&activeCount, 1)
						atomic.AddInt64(&avgRTT, st.srtt.Load())
						if last := c.lastTraffic.Load(); last > 0 && time.Since(time.Unix(0, last)) < 3*time.Second {
							return
						}

						var pl uint16
						if true {
							pl = 0 // v6: no padding
						} else {
							pl = generateSmartPadding(HeaderSize)
						}
						ts := uint32(time.Now().UnixMilli() & 0xFFFFFFFF)
						h := &PacketHeader{Magic: Magic, ClientID: c.clientID, Flags: PingFlag, Timestamp: ts, PaddingLen: pl}
						c.sdm.RLock()
						h.SetFEC(c.currentDS, c.currentPS)
						c.sdm.RUnlock()

						b := make([]byte, HeaderSize+int(pl))
						h.EncodeTo(b[:HeaderSize])

						if _, err := st.Write(b); err != nil {
							st.Close()
						}

						tc := time.NewTimer(6 * time.Second)
						select {
						case <-st.pingCh:
							tc.Stop()
							st.lossCount.Store(0)
						case <-tc.C:
							st.lossCount.Add(1)
							if st.lossCount.Load() > 3 {
								st.Close()
							}
						}
					}
				}(i)
			}
			wg.Wait()
			{
				var ac, cc int
				c.sMu.RLock()
				for _, st := range c.streams {
					if st == nil { continue }
					if st.IsClosed() { cc++ } else { ac++ }
				}
				c.sMu.RUnlock()
				var n int
				c.conns.Range(func(_, _ any) bool { n++; return true })
				log.Printf("[CLI] streams=%d/%d conns=%d", ac, ac+cc, n)
			}
			if score := c.nackScore.Load(); score > 0 {
				c.nackScore.Store(score * 3 / 4)
			}

			if activeCount > 0 {
				avgRTT /= int64(activeCount)
				// Active streams are healthy; reset reconnect backoff.
				c.reconnectMu.Lock()
				c.reconnectBackoff = 0
				c.reconnectMu.Unlock()
			} else {
				// All streams are down; advance reconnect backoff and reconnect one by one.
				c.reconnectMu.Lock()
				if c.reconnectBackoff == 0 {
					c.reconnectBackoff = ReconnectBaseDelay
				} else {
					c.reconnectBackoff *= 2
					if c.reconnectBackoff > ReconnectMaxDelay {
						c.reconnectBackoff = ReconnectMaxDelay
					}
				}
				delay := c.reconnectBackoff
				c.reconnectMu.Unlock()

				log.Printf("[CLI] all %d streams are down; reconnecting after %v", NumStreams, delay)
				time.Sleep(delay)

				for i := 0; i < NumStreams; i++ {
					select {
					case <-c.stopCh:
						return
					default:
					}
					c.sMu.RLock()
					st := c.streams[i]
					c.sMu.RUnlock()
					if st != nil && !st.IsClosed() {
						continue
					}
					time.Sleep(time.Duration(250+fastRand()%750) * time.Millisecond)
					newSt := c.dialStream(i)
					if newSt != nil {
						c.sMu.Lock()
						c.streams[i] = newSt
						c.sMu.Unlock()
						log.Printf("[CLI] stream %d reconnected", i)
					} else {
						log.Printf("[CLI] stream %d reconnect failed, will retry next cycle", i)
					}
					time.Sleep(ReconnectStagger)
				}
				// Reset all reassemblers after full reconnect to clear stale state
				for _, ar := range c.trs {
					ar.Close()
				}
				for i := range c.trs {
					c.trs[i] = NewTCPReassembler(c.clientID, 30*time.Second)
				}
				c.cr.Close()
				c.cr = NewTCPReassembler(c.clientID, 30*time.Second)
				log.Printf("[CLI] reassemblers reset after reconnect")
				continue
			}

			lossRate := float64(lossCount) / float64(NumStreams)
			c.sdm.Lock()
			switch {
			case activeCount >= 6 && lossRate < 0.08:
				/* c.currentDS, c.currentPS = 4, 2 */
			case activeCount >= 5:
				/* c.currentDS, c.currentPS = 3, 2 */
			case activeCount >= 4:
				/* c.currentDS, c.currentPS = 2, 2 */
			case activeCount >= 3:
				/* c.currentDS, c.currentPS = 2, 1 */
			default:
				/* c.currentDS, c.currentPS = 1, 2 */
			}
			c.sdm.Unlock()
		}
	}
}

func (c *AdaptiveDispatcher) sendFinFrame(connID uint32) {
	fb := framePool.Get().([]byte)
	fb = fb[:7]
	fb[0] = 0x06
	binary.BigEndian.PutUint32(fb[1:5], connID)
	binary.BigEndian.PutUint16(fb[5:7], 0)
	c.SendChunk(fb)
	framePool.Put(fb[:cap(fb)])
}

func (c *AdaptiveDispatcher) sendCloseFrame(connID uint32) {
	go func() {
		fb := framePool.Get().([]byte)
		fb = fb[:7]
		fb[0] = 0x03
		binary.BigEndian.PutUint32(fb[1:5], connID)
		binary.BigEndian.PutUint16(fb[5:7], 0)
		c.SendChunk(fb)
		framePool.Put(fb[:cap(fb)])
	}()
}

func (c *AdaptiveDispatcher) writeSOCKS5UDP(pc *ProxyConn, payload []byte) {
	addr := pc.getUDPAddr()
	if addr == nil {
		return
	}
	uc := localProxyUDP
	if uc == nil {
		return
	}
	pkt := buildSOCKS5UDPDatagram(payload)
	uc.SetWriteDeadline(time.Now().Add(LocalWriteTimeout))
	_, err := uc.WriteToUDP(pkt, addr)
	uc.SetWriteDeadline(time.Time{})
	if err != nil {
		debugf("[CLI] socks udp write failed connID=%d addr=%s err=%v", pc.connID, addr, err)
	}
}

func (c *AdaptiveDispatcher) sendNACK(bucket uint8, seq uint32) {
	c.sMu.RLock()
	streams := append([]*SafeStream(nil), c.streams...)
	c.sMu.RUnlock()
	var pl uint16
	if true {
		pl = 0 // v6: no padding
	} else {
		pl = generateSmartPadding(HeaderSize)
	}
	h := &PacketHeader{Magic: Magic, ClientID: c.clientID, SeqNo: seq, Flags: NackFlag, PaddingLen: pl, Timestamp: uint32(time.Now().UnixMilli() & 0xFFFFFFFF)}
	h.SetBucket(bucket)
	c.nackScore.Add(1)
	// v5fix: fire-and-forget NACK to all streams (no blocking)
	for _, st := range streams {
		if st != nil && !st.IsClosed() {
			// each stream gets its own buffer copy to avoid data races
			buf := make([]byte, HeaderSize+int(pl))
			h.EncodeTo(buf[:HeaderSize])
			go func(s *SafeStream, b []byte) {
				if _, err := s.Write(b); err != nil {
					s.Close()
				}
			}(st, buf)
		}
	}
}

func (c *AdaptiveDispatcher) retransmitSeq(bucket uint8, seq uint32) {
	pkts := c.rtx.Get(bucket, seq)
	if len(pkts) == 0 {
		if shouldLogEvery(&c.lastNackMissLog, 5*time.Second) {
			count, oldestBucket, oldest, newestBucket, newest := c.rtx.Stats()
			log.Printf("[CLI] NACK cache miss bucket=%d seq=%d cache_count=%d cache_range=%d:%d..%d:%d", bucket, seq, count, oldestBucket, oldest, newestBucket, newest)
		}
		return
	}
	c.sMu.RLock()
	var streams []*SafeStream
	for _, st := range c.streams {
		if st != nil && !st.IsClosed() {
			streams = append(streams, st)
		}
	}
	c.sMu.RUnlock()
	if len(streams) == 0 {
		return
	}
	for i, pkt := range pkts {
		st := streams[int(seq+uint32(i))%len(streams)]
		if _, err := st.Write(pkt); err != nil {
			st.Close()
		}
	}
	debugf("[CLI] retransmitted bucket=%d seq=%d shards=%d", bucket, seq, len(pkts))
}

func (c *AdaptiveDispatcher) resetProxyConns(reason string) {
	log.Printf("[WARN] resetting active local proxy conns: %s", reason)
	c.conns.Range(func(k, v interface{}) bool {
		pc := v.(*ProxyConn)
		pc.closeLocal()
		c.sendCloseFrame(pc.connID)
		c.conns.Delete(k)
		return true
	})
}

func (c *AdaptiveDispatcher) handleReassembler() {
	for {
		select {
		case <-c.stopCh:
			return
		case ev := <-c.reasmCh:
			if ev.closed {
				c.reboot()
				return
			}
			if ev.control {
				if ev.data == nil {
					c.cfb = c.cfb[:0]
					continue
				}
				if !c.handleReassembledPayload(&c.cfb, ev.data) {
					return
				}
				continue
			}
			bucket := int(ev.bucket % DataBuckets)
			if ev.data == nil {
				c.pfbs[bucket] = c.pfbs[bucket][:0]
				c.resetProxyConns(fmt.Sprintf("data bucket %d reassembler gap", bucket))
				continue
			}
			if !c.handleReassembledPayload(&c.pfbs[bucket], ev.data) {
				return
			}
		}
	}
}

func (c *AdaptiveDispatcher) handleReassembledPayload(pfb *[]byte, d []byte) bool {
	frames, ok := parseFrames(pfb, d)
	if !ok {
		outputPool.Put(d[:cap(d)])
		c.reboot()
		return false
	}
	for _, f := range frames {
		if pc, ok := c.conns.Load(f.ConnID); ok {
			pc2 := pc.(*ProxyConn)
			pc2.touch()
			switch f.Type {
			case 1:
				select {
				case pc2.connectAckCh <- struct{}{}:
				default:
				}
			case 2:
				select {
				case pc2.connectErrCh <- struct{}{}:
				default:
				}
				pc2.closeLocal()
				c.conns.Delete(f.ConnID)
			case 3:
				if pc2.udpAssoc {
					pc2.closeLocal()
				} else {
					pc2.closeWriteQueue()
				}
				c.conns.Delete(f.ConnID)
			case 4:
				if !pc2.cl.Load() {
					select {
					case pc2.wc <- f.Payload:
					default:
						log.Printf("[FATAL] local TCP write queue blocked (connID=%d), closing target", f.ConnID)
						pc2.closeLocal()
						c.sendCloseFrame(f.ConnID)
						c.conns.Delete(f.ConnID)
					}
				}
			case 5:
				if pc2.udpAssoc && !pc2.cl.Load() {
					c.writeSOCKS5UDP(pc2, f.Payload)
				}
			case 6:
				if !pc2.udpAssoc {
					pc2.closeWriteQueue()
					c.conns.Delete(f.ConnID)
				}
			}
		}
	}
	outputPool.Put(d[:cap(d)])
	return true
}

type streamStat struct {
	st  *SafeStream
	rtt int64
}

func (c *AdaptiveDispatcher) SendChunk(data []byte) bool {
	control := isClientControlFrame(data)
	if control {
		c.flushAllBatches()
	}
	return c.sendChunk(data, control)
}

func (c *AdaptiveDispatcher) enqueueData(data []byte) bool {
	if c.closed.Load() {
		return false
	}
	bucket := muxBucket(data)
	cp := make([]byte, len(data))
	copy(cp, data)
	var flush []byte
	c.batchMu.Lock()
	c.batchBufs[bucket] = append(c.batchBufs[bucket], cp...)
	if len(c.batchBufs[bucket]) >= LocalReadBufferSize {
		flush = c.batchBufs[bucket]
		c.batchBufs[bucket] = nil
		c.batchActive[bucket] = false
	} else if !c.batchActive[bucket] {
		c.batchActive[bucket] = true
		go func(b uint8) {
			time.Sleep(time.Duration(1+fastRand()%3) * time.Millisecond)
			c.flushBatch(b)
		}(bucket)
	}
	c.batchMu.Unlock()
	if len(flush) > 0 {
		return c.sendChunk(flush, false)
	}
	return true
}

func (c *AdaptiveDispatcher) flushAllBatches() {
	for i := 0; i < DataBuckets; i++ {
		c.flushBatch(uint8(i))
	}
}
func (c *AdaptiveDispatcher) flushBatch(bucket uint8) {
	c.batchMu.Lock()
	data := c.batchBufs[bucket]
	c.batchBufs[bucket] = nil
	c.batchActive[bucket] = false
	c.batchMu.Unlock()
	if len(data) > 0 && !c.closed.Load() {
		c.sendChunk(data, false)
	}
}

func isClientControlFrame(data []byte) bool {
	if len(data) < 7 {
		return false
	}
	if len(data) != 7+int(binary.BigEndian.Uint16(data[5:7])) {
		return false
	}
	return data[0] == 0x01 || data[0] == 0x03
}

func (c *AdaptiveDispatcher) chooseClientDataFEC(active, curDS, curPS, remaining int) (int, int) {
	score := c.nackScore.Load()
	if remaining <= SmallPacketFastLen {
		if score >= 4 || active <= 3 {
			return 1, 2
		}
		return 1, 1
	}
	switch {
	case active >= 6:
		if score == 0 {
			return 5, 1
		}
		if score < 4 {
			return 4, 2
		}
		return 3, 3
	case active == 5:
		if score < 3 {
			return 4, 1
		}
		return 3, 2
	case active == 4:
		if score < 3 {
			return 3, 1
		}
		return 2, 2
	case active == 3:
		if score < 3 {
			return 2, 1
		}
		return 1, 2
	default:
		return 1, 2
	}
}

func (c *AdaptiveDispatcher) sendChunk(data []byte, control bool) bool {
	if len(data) == 0 {
		return true
	}
	if c.closed.Load() {
		return false
	}

	c.pacing.Wait(float64(len(data)))

	c.muxWriteMu.Lock()
	defer c.muxWriteMu.Unlock()

	// v6: Split+Mirror — no FEC, primary + mirror streams

	c.sMu.RLock()
	var active []*SafeStream
	for _, st := range c.streams {
		if st != nil && !st.IsClosed() {
			active = append(active, st)
		}
	}
	c.sMu.RUnlock()

	if len(active) == 0 {
		log.Printf("[CLI] no active tunnel streams; dropping %d bytes", len(data))
		return false
	}

	var sq uint32
	var bucket uint8
	if control {
		sq = c.cfw.Add(1) - 1
	} else {
		bucket = muxBucket(data)
		c.lastTraffic.Store(time.Now().UnixNano())
		sq = c.fws[bucket].Add(1) - 1
	}

	ts := uint32(time.Now().UnixMilli() & 0xFFFFFFFF)
	cs := uint32(len(data))
	var padLen uint16
	if true {
		padLen = 0 // v6 Split+Mirror: no padding, server fast bypass reads ChunkSize directly
	} else {
		padLen = generateSmartPadding(HeaderSize + len(data))
	}
	buf := make([]byte, HeaderSize+len(data)+int(padLen))

	h := &PacketHeader{Magic: Magic, ClientID: c.clientID, SeqNo: sq, ShardIdx: 0, PaddingLen: padLen, ChunkSize: cs, Timestamp: ts}
	if control {
		h.Flags |= ControlFrameFlag
	}
	h.SetFEC(1, 0)
	h.SetBucket(bucket)
	h.EncodeTo(buf[:HeaderSize])
	copy(buf[HeaderSize:], data)

	pkt := buf

	// v7.4: CONNECT (cmd=0x01) sent to ONE stream only to avoid server dedup killing the connection.
	// Other control frames (CLOSE, FIN) still broadcast to all streams for reliability.
	var targets []*SafeStream
	isConnect := len(data) > 0 && data[0] == 0x01
	if control && !isConnect {
		targets = active
	} else {
		var connID uint32
		if len(data) >= 5 {
			connID = binary.BigEndian.Uint32(data[1:5])
		}
		pIdx := int(connID % 6)
		c.sMu.RLock()
		if pIdx < len(c.streams) && c.streams[pIdx] != nil && !c.streams[pIdx].IsClosed() {
			targets = append(targets, c.streams[pIdx])
		}
		c.sMu.RUnlock()
	}

	if len(targets) == 0 {
		c.sMu.RLock()
		var states []string
		for i, st := range c.streams {
			if st == nil {
				states = append(states, fmt.Sprintf("%d:nil", i))
			} else if st.IsClosed() {
				states = append(states, fmt.Sprintf("%d:closed", i))
			} else {
				states = append(states, fmt.Sprintf("%d:ok", i))
			}
		}
		c.sMu.RUnlock()
		log.Printf("[CLI] no target streams for seq=%d streams=[%s]", sq, strings.Join(states, ","))
		return false
	}

	ok := 0
	for _, st := range targets {
		if _, err := st.Write(pkt); err != nil {
			st.Close()
		} else {
			ok++
		}
	}
	if ok == 0 && len(targets) > 0 {
		log.Printf("[CLI] ALL %d target writes failed! control=%v", len(targets), control)
	}
	return ok > 0
}

func (c *AdaptiveDispatcher) DialProxy(conn net.Conn) {
	conn.SetReadDeadline(time.Now().Add(10 * time.Second))
	var first [1]byte
	if _, err := io.ReadFull(conn, first[:]); err != nil {
		conn.Close()
		return
	}

	switch first[0] {
	case 0x05:
		c.handleSOCKS5(conn)
	case 'C', 'G', 'P', 'H', 'O', 'D', 'T':
		c.handleHTTPProxy(conn, first[0])
	default:
		log.Printf("[CLI] unsupported local proxy protocol: first=0x%02x; use SOCKS5 or HTTP CONNECT", first[0])
		conn.Close()
	}
}

func (c *AdaptiveDispatcher) handleSOCKS5(conn net.Conn) {
	var nMethods [1]byte
	if _, err := io.ReadFull(conn, nMethods[:]); err != nil {
		conn.Close()
		return
	}
	methods := make([]byte, int(nMethods[0]))
	if _, err := io.ReadFull(conn, methods); err != nil {
		conn.Close()
		return
	}
	if _, err := conn.Write([]byte{0x05, 0x00}); err != nil {
		conn.Close()
		return
	}

	var hdr [4]byte
	if _, err := io.ReadFull(conn, hdr[:]); err != nil {
		conn.Close()
		return
	}
	if hdr[0] != 0x05 {
		conn.Close()
		return
	}

	cmd := hdr[1]
	addr, targetPort, err := readSOCKS5Addr(conn, hdr[3])
	if err != nil {
		conn.Write(socks5Reply(0x08, nil, 0))
		conn.Close()
		return
	}
	conn.SetReadDeadline(time.Time{})

	switch cmd {
	case 0x01:
		c.DialProxyTarget(conn, addr, targetPort, func() bool {
			_, err := conn.Write(socks5Reply(0x00, nil, 0))
			return err == nil
		})
	case 0x03:
		c.handleSOCKS5UDPAssociate(conn)
	default:
		conn.Write(socks5Reply(0x07, nil, 0))
		conn.Close()
	}
}

func readSOCKS5Addr(r io.Reader, atyp byte) (string, uint16, error) {
	var addr string
	switch atyp {
	case 0x01:
		b := make([]byte, 4)
		if _, err := io.ReadFull(r, b); err != nil {
			return "", 0, err
		}
		addr = net.IP(b).String()
	case 0x03:
		var lb [1]byte
		if _, err := io.ReadFull(r, lb[:]); err != nil {
			return "", 0, err
		}
		if lb[0] == 0 {
			return "", 0, fmt.Errorf("empty socks domain")
		}
		b := make([]byte, int(lb[0]))
		if _, err := io.ReadFull(r, b); err != nil {
			return "", 0, err
		}
		addr = string(b)
	case 0x04:
		b := make([]byte, 16)
		if _, err := io.ReadFull(r, b); err != nil {
			return "", 0, err
		}
		addr = net.IP(b).String()
	default:
		return "", 0, fmt.Errorf("unsupported socks atyp 0x%02x", atyp)
	}
	var pb [2]byte
	if _, err := io.ReadFull(r, pb[:]); err != nil {
		return "", 0, err
	}
	return addr, binary.BigEndian.Uint16(pb[:]), nil
}

func socks5Reply(rep byte, ip net.IP, port int) []byte {
	if port < 0 || port > 65535 {
		port = 0
	}
	if ip4 := ip.To4(); ip4 != nil {
		b := make([]byte, 10)
		b[0], b[1], b[2], b[3] = 0x05, rep, 0x00, 0x01
		copy(b[4:8], ip4)
		binary.BigEndian.PutUint16(b[8:10], uint16(port))
		return b
	}
	if ip16 := ip.To16(); ip16 != nil {
		b := make([]byte, 22)
		b[0], b[1], b[2], b[3] = 0x05, rep, 0x00, 0x04
		copy(b[4:20], ip16)
		binary.BigEndian.PutUint16(b[20:22], uint16(port))
		return b
	}
	b := make([]byte, 10)
	b[0], b[1], b[2], b[3] = 0x05, rep, 0x00, 0x01
	binary.BigEndian.PutUint16(b[8:10], uint16(port))
	return b
}

func localProxyBindIP(conn net.Conn) net.IP {
	if ta, ok := conn.LocalAddr().(*net.TCPAddr); ok && ta.IP != nil && !ta.IP.IsUnspecified() {
		return ta.IP
	}
	return net.IPv4(0, 0, 0, 0)
}

func localProxyUDPPort() int {
	uc := localProxyUDP
	if uc == nil {
		return 0
	}
	if ua, ok := uc.LocalAddr().(*net.UDPAddr); ok {
		return ua.Port
	}
	return 0
}

func parseSOCKS5UDPDatagram(d []byte) ([]byte, bool) {
	if len(d) < 4 || d[0] != 0 || d[1] != 0 || d[2] != 0 {
		return nil, false
	}
	p := d[3:]
	if len(p) > 65535 {
		return nil, false
	}
	switch p[0] {
	case 0x01:
		if len(p) < 7 {
			return nil, false
		}
	case 0x03:
		if len(p) < 2 {
			return nil, false
		}
		dl := int(p[1])
		if len(p) < 4+dl {
			return nil, false
		}
	case 0x04:
		if len(p) < 19 {
			return nil, false
		}
	default:
		return nil, false
	}
	out := make([]byte, len(p))
	copy(out, p)
	return out, true
}

func buildSOCKS5UDPDatagram(payload []byte) []byte {
	pkt := make([]byte, 3+len(payload))
	copy(pkt[3:], payload)
	return pkt
}

func (c *AdaptiveDispatcher) resolveUDPAssociation(addr *net.UDPAddr) *ProxyConn {
	if addr == nil {
		return nil
	}
	key := addr.String()
	if v, ok := c.udpPeers.Load(key); ok {
		pc := v.(*ProxyConn)
		if !pc.cl.Load() {
			pc.setUDPAddr(addr)
			return pc
		}
		c.udpPeers.Delete(key)
	}
	c.udpMu.RLock()
	pc := c.udpAssoc
	c.udpMu.RUnlock()
	if pc == nil || pc.cl.Load() {
		return nil
	}
	pc.setUDPAddr(addr)
	c.udpPeers.Store(key, pc)
	return pc
}

func (c *AdaptiveDispatcher) clearUDPAssociation(pc *ProxyConn) {
	c.udpMu.Lock()
	if c.udpAssoc == pc {
		c.udpAssoc = nil
	}
	c.udpMu.Unlock()
	c.udpPeers.Range(func(k, v interface{}) bool {
		if v.(*ProxyConn) == pc {
			c.udpPeers.Delete(k)
		}
		return true
	})
}

func (c *AdaptiveDispatcher) sendUDPDatagramFromLocal(addr *net.UDPAddr, payload []byte) {
	pc := c.resolveUDPAssociation(addr)
	if pc == nil || pc.cl.Load() || len(payload) > 65535 {
		return
	}
	pc.touch()
	fb := framePool.Get().([]byte)
	frameLen := 7 + len(payload)
	if cap(fb) < frameLen {
		fb = make([]byte, frameLen)
	}
	fb = fb[:frameLen]
	fb[0] = 0x05
	binary.BigEndian.PutUint32(fb[1:5], pc.connID)
	binary.BigEndian.PutUint16(fb[5:7], uint16(len(payload)))
	copy(fb[7:], payload)
	c.SendChunk(fb)
	framePool.Put(fb[:cap(fb)])
}

func (c *AdaptiveDispatcher) handleSOCKS5UDPAssociate(conn net.Conn) {
	pc := &ProxyConn{
		connID:       fastRand(),
		conn:         conn,
		connectAckCh: make(chan struct{}, 1),
		connectErrCh: make(chan struct{}, 1),
		wc:           make(chan []byte, 16),
		done:         make(chan struct{}),
		udpAssoc:     true,
	}
	pc.touch()
	c.conns.Store(pc.connID, pc)
	c.udpMu.Lock()
	c.udpAssoc = pc
	c.udpMu.Unlock()

	defer func() {
		c.clearUDPAssociation(pc)
		pc.closeLocal()
		c.conns.Delete(pc.connID)
		c.sendCloseFrame(pc.connID)
	}()

	port := localProxyUDPPort()
	if port == 0 {
		conn.Write(socks5Reply(0x01, nil, 0))
		return
	}
	if _, err := conn.Write(socks5Reply(0x00, localProxyBindIP(conn), port)); err != nil {
		return
	}

	buf := make([]byte, 1)
	for {
		if _, err := conn.Read(buf); err != nil {
			return
		}
		pc.touch()
	}
}
func (c *AdaptiveDispatcher) handleHTTPProxy(conn net.Conn, first byte) {
	br := bufio.NewReader(io.MultiReader(bytes.NewReader([]byte{first}), conn))
	req, err := http.ReadRequest(br)
	if err != nil {
		conn.Close()
		return
	}
	if req.Method != http.MethodConnect {
		io.WriteString(conn, "HTTP/1.1 405 Method Not Allowed\r\nConnection: close\r\n\r\n")
		conn.Close()
		return
	}
	host, portStr, err := net.SplitHostPort(req.Host)
	if err != nil {
		host = req.Host
		portStr = "443"
	}
	port, err := net.LookupPort("tcp", portStr)
	if err != nil || port <= 0 || port > 65535 {
		io.WriteString(conn, "HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\n")
		conn.Close()
		return
	}
	conn.SetReadDeadline(time.Time{})
	bc := &bufferedProxyConn{Conn: conn, r: br}
	c.DialProxyTarget(bc, host, uint16(port), func() bool {
		_, err := io.WriteString(conn, "HTTP/1.1 200 Connection Established\r\n\r\n")
		return err == nil
	})
}

type bufferedProxyConn struct {
	net.Conn
	r *bufio.Reader
}

func (c *bufferedProxyConn) Read(p []byte) (int, error) {
	if c.r != nil && c.r.Buffered() > 0 {
		return c.r.Read(p)
	}
	return c.Conn.Read(p)
}

func (c *AdaptiveDispatcher) DialProxyTarget(conn net.Conn, addr string, targetPort uint16, writeOK func() bool) {
	pc := &ProxyConn{
		connID:       fastRand(),
		conn:         conn,
		connectAckCh: make(chan struct{}, 1),
		connectErrCh: make(chan struct{}, 1),
		wc:           make(chan []byte, 1024),
		done:         make(chan struct{}),
	}
	pc.touch()
	c.conns.Store(pc.connID, pc)

	go func() {
		hardClose := true
		defer func() {
			pc.closeLocal()
			c.conns.Delete(pc.connID)
			if hardClose {
				c.sendCloseFrame(pc.connID)
			}
		}()

		if addr == "" || targetPort == 0 || len(addr) > 255 {
			return
		}

		serverHost, _, err := net.SplitHostPort(c.node.Server)
		if err != nil || serverHost == "" {
			serverHost = c.node.Server
		}
		isLoop := false
		if addr == serverHost {
			isLoop = true
		} else if ips, err := net.LookupIP(serverHost); err == nil {
			for _, ip := range ips {
				if addr == ip.String() {
					isLoop = true
					break
				}
			}
		}
		if isLoop {
			log.Printf("[CLI] blocked local proxy routing loop to server itself: %s", addr)
			return
		}

		debugf("[CLI] proxy target -> %s:%d", addr, targetPort)
		reqLen := 1 + len(addr) + 2
		connPayload := make([]byte, reqLen)
		connPayload[0] = byte(len(addr))
		copy(connPayload[1:1+len(addr)], addr)
		binary.BigEndian.PutUint16(connPayload[1+len(addr):], targetPort)

		fb := framePool.Get().([]byte)
		frameLen := 7 + reqLen
		if cap(fb) < frameLen {
			fb = make([]byte, frameLen)
		}
		fb = fb[:frameLen]
		fb[0] = 0x01
		binary.BigEndian.PutUint32(fb[1:5], pc.connID)
		binary.BigEndian.PutUint16(fb[5:7], uint16(reqLen))
		copy(fb[7:], connPayload)
		if !c.SendChunk(fb) {
			log.Printf("[CLI] CONNECT SendChunk FAILED connID=%d addr=%s:%d", pc.connID, addr, targetPort)
			framePool.Put(fb[:cap(fb)])
			return
		}
		log.Printf("[CLI] CONNECT sent connID=%d addr=%s:%d", pc.connID, addr, targetPort)
		pc.touch()
		framePool.Put(fb[:cap(fb)])

		// v7.5: wait for server CONNECT ACK before replying to browser
		select {
		case <-pc.connectAckCh:
			debugf("[CLI] CONNECT ACK connID=%d", pc.connID)
		case <-pc.connectErrCh:
			log.Printf("[CLI] CONNECT rejected by server connID=%d", pc.connID)
			conn.Write(socks5Reply(0x05, nil, 0))
			return
		case <-time.After(5 * time.Second):
			log.Printf("[CLI] CONNECT timeout connID=%d", pc.connID)
			conn.Write(socks5Reply(0x04, nil, 0))
			return
		}

		if writeOK != nil && !writeOK() {
			return
		}

		go func() {
			for {
				select {
				case <-pc.done:
					return
				case p, ok := <-pc.wc:
					if !ok {
						pc.closeLocal()
						return
					}
					pc.touch()
					pc.conn.SetWriteDeadline(time.Now().Add(LocalWriteTimeout))
					if _, err := pc.conn.Write(p); err != nil {
						c.sendCloseFrame(pc.connID)
						pc.closeLocal()
						return
					}
					pc.conn.SetWriteDeadline(time.Time{})
				}
			}
		}()

		buf := make([]byte, LocalReadBufferSize)
		for {
			n, err := conn.Read(buf)
			if n > 0 {
				pc.touch()
				df := framePool.Get().([]byte)
				dfLen := 7 + n
				if cap(df) < dfLen {
					df = make([]byte, dfLen)
				}
				df = df[:dfLen]
				df[0] = 0x02
				binary.BigEndian.PutUint32(df[1:5], pc.connID)
				binary.BigEndian.PutUint16(df[5:7], uint16(n))
				copy(df[7:], buf[:n])
				if !c.SendChunk(df) {
					framePool.Put(df[:cap(df)])
					return
				}
				framePool.Put(df[:cap(df)])
			}
			if err != nil {
				log.Printf("[CLI] local read err connID=%d err=%v closed=%v", pc.connID, err, pc.cl.Load())
				if pc.cl.Load() {
					hardClose = false
					return
				}
				if err == io.EOF {
					hardClose = false
					c.sendFinFrame(pc.connID)
					select {
					case <-pc.done:
					case <-time.After(2 * time.Minute):
						hardClose = true
					}
				}
				return
			}
		}
	}()
}

type NodeConfig struct {
	ID         string `json:"id"`
	Name       string `json:"name"`
	Server     string `json:"server"`
	Username   string `json:"username"`
	Password   string `json:"password"`
	SNI        string `json:"sni"`
	CertSHA256 string `json:"cert_sha256,omitempty"`
}

type AppConfig struct {
	Enable       bool         `json:"enable"`
	ActiveNodeID string       `json:"active_node_id"`
	Nodes        []NodeConfig `json:"nodes"`
}

var (
	globalConfig  AppConfig
	configMu      sync.RWMutex
	currentDisp   *AdaptiveDispatcher
	dispMu        sync.Mutex
	localProxyLN  net.Listener
	localProxyUDP *net.UDPConn
)

func initConfig() {
	globalConfig = AppConfig{
		Enable:       false,
		ActiveNodeID: "",
		Nodes:        []NodeConfig{},
	}
	if b, e := os.ReadFile(ClientCfgFile); e == nil {
		json.Unmarshal(b, &globalConfig)
	}
}

func saveConfig() {
	configMu.RLock()
	b, _ := json.MarshalIndent(globalConfig, "", "  ")
	configMu.RUnlock()
	os.WriteFile(ClientCfgFile, b, 0644)
}

func applyEngine() {
	dispMu.Lock()
	defer dispMu.Unlock()
	if currentDisp != nil {
		currentDisp.Close()
		currentDisp = nil
	}
	configMu.RLock()
	en := globalConfig.Enable
	nid := globalConfig.ActiveNodeID
	var actNode *NodeConfig
	for _, n := range globalConfig.Nodes {
		if n.ID == nid {
			actNode = &n
			break
		}
	}
	configMu.RUnlock()
	if !en || actNode == nil {
		return
	}
	currentDisp = NewAdaptiveDispatcher(*actNode)
}

func ensureLocalProxyListener() error {
	dispMu.Lock()
	if localProxyLN != nil {
		dispMu.Unlock()
		return nil
	}
	ln, err := net.Listen("tcp", LocalProxyListenAddr)
	if err != nil {
		dispMu.Unlock()
		return err
	}
	udpAddr, err := net.ResolveUDPAddr("udp", LocalProxyListenAddr)
	if err != nil {
		ln.Close()
		dispMu.Unlock()
		return err
	}
	uc, err := net.ListenUDP("udp", udpAddr)
	if err != nil {
		ln.Close()
		dispMu.Unlock()
		return err
	}
	localProxyLN = ln
	localProxyUDP = uc
	dispMu.Unlock()

	go func() {
		for {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			dispMu.Lock()
			d := currentDisp
			dispMu.Unlock()
			if d != nil {
				go func(conn net.Conn, disp *AdaptiveDispatcher) {
					defer func() {
						if r := recover(); r != nil {
							log.Printf("[CLI] local proxy handler panic: %v", r)
							conn.Close()
						}
					}()
					if tc, ok := conn.(*net.TCPConn); ok {
						tc.SetNoDelay(true)
						tc.SetKeepAlive(true)
						tc.SetKeepAlivePeriod(30 * time.Second)
					}
					disp.DialProxy(conn)
				}(c, d)
			} else {
				c.Close()
			}
		}
	}()
	go localProxyUDPLoop(uc)
	return nil
}

func localProxyUDPLoop(uc *net.UDPConn) {
	buf := make([]byte, 65535)
	for {
		n, addr, err := uc.ReadFromUDP(buf)
		if err != nil {
			return
		}
		payload, ok := parseSOCKS5UDPDatagram(buf[:n])
		if !ok {
			continue
		}
		dispMu.Lock()
		d := currentDisp
		dispMu.Unlock()
		if d == nil {
			continue
		}
		d.sendUDPDatagramFromLocal(addr, payload)
	}
}

func handleAPI(w http.ResponseWriter, r *http.Request) {
	if r.Method == "GET" {
		configMu.RLock()
		dispMu.Lock()
		rn := currentDisp != nil
		dispMu.Unlock()
		json.NewEncoder(w).Encode(map[string]interface{}{
			"running": rn,
			"conf":    globalConfig,
		})
		configMu.RUnlock()
	} else if r.Method == "POST" {
		var nc AppConfig
		json.NewDecoder(r.Body).Decode(&nc)
		configMu.Lock()
		globalConfig = nc
		configMu.Unlock()
		saveConfig()
		applyEngine()
		w.Write([]byte(`{"ok":true}`))
	}
}

func main() {
	runtime.GOMAXPROCS(runtime.NumCPU())
	debug.SetGCPercent(200)
	localProxyAddr := flag.String("listen", "0.0.0.0:11080", "SOCKS5/HTTP local proxy listen address")
	panelPort := flag.String("panel", "0.0.0.0:9999", "Web panel listen address")
	cfgFile := flag.String("config", "aether_client.json", "Config file path")
	flag.Parse()
	ClientCfgFile = *cfgFile
	LocalProxyListenAddr = *localProxyAddr
	initConfig()
	if err := ensureLocalProxyListener(); err != nil {
		log.Fatalf("[CLI] local SOCKS5/HTTP proxy listen failed on %s: %v", LocalProxyListenAddr, err)
	}
	applyEngine()
	http.HandleFunc("/api", handleAPI)
	http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/" {
			return
		}
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		w.Write([]byte(clientHTML))
	})
	log.Printf("[CLI] Panel: %s, SOCKS5/HTTP: %s", *panelPort, *localProxyAddr)
	http.ListenAndServe(*panelPort, nil)
}

const clientHTML = `<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>SuperYellow Proxy</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
:root{--bg:#0f172a;--card:#1e293b;--card2:#334155;--accent:#f59e0b;--accent2:#fbbf24;--green:#22c55e;--red:#ef4444;--text:#f1f5f9;--text2:#94a3b8;--border:#475569;--radius:12px}
body{background:var(--bg);color:var(--text);font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;min-height:100vh}
.c{max-width:960px;margin:0 auto;padding:24px 20px}
.hd{display:flex;align-items:center;justify-content:space-between;margin-bottom:28px;padding-bottom:20px;border-bottom:1px solid var(--border)}
.hd h1{font-size:22px;font-weight:700}
.hd .sub{color:var(--text2);font-size:13px;margin-top:2px}
.sb{display:flex;gap:16px;margin-bottom:24px;flex-wrap:wrap}
.st{flex:1;min-width:140px;background:var(--card);border-radius:var(--radius);padding:16px 20px}
.st .lb{font-size:12px;color:var(--text2);text-transform:uppercase;letter-spacing:.5px;margin-bottom:6px}
.st .vl{font-size:20px;font-weight:700}
.on{color:var(--green)}.off{color:var(--red)}.ac{color:var(--accent)}
.cr{background:var(--card);border-radius:var(--radius);padding:24px;margin-bottom:20px}
.cr h2{font-size:16px;font-weight:600;margin-bottom:16px;display:flex;align-items:center;gap:8px}
.nl{display:flex;flex-direction:column;gap:10px}
.nd{background:var(--card2);border-radius:10px;padding:16px 20px;display:flex;align-items:center;justify-content:space-between;cursor:pointer;transition:.2s;border:2px solid transparent}
.nd:hover{background:#3e5068}.nd.act{border-color:var(--accent);background:rgba(245,158,11,.08)}
.nd .nm{font-weight:600;font-size:15px;margin-bottom:3px}
.nd .ad{color:var(--text2);font-size:13px;font-family:monospace}
.badge{font-size:10px;background:var(--accent);color:#000;padding:1px 8px;border-radius:99px;font-weight:700;margin-left:8px}
.btn{padding:7px 16px;border-radius:8px;border:none;font-size:13px;font-weight:600;cursor:pointer;transition:.15s}
.btn:active{transform:scale(.97)}.btn-sm{padding:5px 12px;font-size:12px}
.btn-p{background:var(--accent);color:#000}.btn-p:hover{background:var(--accent2)}
.btn-g{background:transparent;color:var(--text2);border:1px solid var(--border)}.btn-g:hover{color:var(--text);border-color:var(--text2)}
.btn-d{background:transparent;color:var(--red);border:1px solid rgba(239,68,68,.3)}.btn-d:hover{background:rgba(239,68,68,.1)}
.btn-gn{background:var(--green);color:#000}.btn-gn:hover{background:#16a34a}
.btn-r{background:var(--red);color:#fff}.btn-r:hover{background:#dc2626}
.tb{display:flex;justify-content:space-between;align-items:center;margin-bottom:14px;flex-wrap:wrap;gap:8px}
.tb h2{margin:0}.cg{display:flex;gap:6px}
.emp{text-align:center;padding:40px;color:var(--text2);font-size:14px}
.mm{position:fixed;inset:0;background:rgba(0,0,0,.6);backdrop-filter:blur(4px);display:flex;align-items:center;justify-content:center;z-index:100;opacity:0;pointer-events:none;transition:.2s}
.mm.show{opacity:1;pointer-events:auto}
.md{background:var(--card);border-radius:16px;padding:28px;width:440px;max-width:90vw;transform:translateY(20px);transition:.2s}
.mm.show .md{transform:translateY(0)}
.md h3{font-size:18px;margin-bottom:20px}
.fg{margin-bottom:14px}.fg label{display:block;font-size:12px;color:var(--text2);font-weight:600;margin-bottom:5px;text-transform:uppercase;letter-spacing:.3px}
.fg input{width:100%;padding:10px 14px;background:var(--card2);border:1px solid var(--border);border-radius:8px;color:var(--text);font-size:14px;outline:none;transition:.2s}
.fg input:focus{border-color:var(--accent);box-shadow:0 0 0 3px rgba(245,158,11,.15)}
.fg input::placeholder{color:#64748b}
.fr{display:grid;grid-template-columns:1fr 1fr;gap:12px}
.ma{display:flex;gap:10px;margin-top:20px}.ma .btn{flex:1;padding:10px}
.tst{position:fixed;top:20px;right:20px;background:var(--green);color:#000;padding:12px 20px;border-radius:10px;font-weight:600;font-size:14px;z-index:200;transform:translateX(120%);transition:.3s}
.tst.show{transform:translateX(0)}
.acts{display:flex;gap:8px;margin-left:16px}
@media(max-width:640px){.sb{flex-direction:column}.fr{grid-template-columns:1fr}.hd{flex-direction:column;align-items:flex-start;gap:12px}.nd{flex-direction:column;align-items:flex-start;gap:10px}.acts{margin-left:0}}
</style>
</head>
<body>
<div class="c">
  <div class="hd">
    <div><h1 id="title">&#128992; SuperYellow Proxy</h1><div class="sub">SOCKS5/HTTP Gateway over Aether FEC</div></div>
    <div><button id="toggleBtn" class="btn btn-gn" onclick="toggle()">&#9654; 闁告凹鍨版慨鈺侇嚕閺囩喐鎯?/button></div>
  </div>

  <div class="sb">
    <div class="st"><div class="lb">鐎殿喗娲橀幖鎼佹偐閼哥鍋?/div><div class="vl" id="s1">-</div></div>
    <div class="st"><div class="lb">闁煎搫鍊婚崑锝夊极娴兼潙娅?/div><div class="vl ac" id="s2">-</div></div>
    <div class="st"><div class="lb">鐟滅増鎸告晶鐘绘嚍閸屾粌浠?/div><div class="vl" id="s3" style="font-size:15px">-</div></div>
    <div class="st"><div class="lb">闁哄牜鍓欏﹢瀵哥博椤栨艾缍?/div><div class="vl" style="font-size:15px;font-family:monospace">:11080</div></div>
  </div>

  <div class="cr">
    <div class="tb">
      <h2>&#128225; 闁煎搫鍊婚崑锝夊礆濡ゅ嫨鈧?/h2>
      <div class="cg">
        <button class="btn btn-g btn-sm" onclick="copyLocalProxy()">&#128279; 濠㈣泛绉撮崺妤呭箳閵夈儱寮?/button>
        <button class="btn btn-g btn-sm" onclick="copyJson()">&#128203; 濠㈣泛绉撮崺妤呮煀瀹ュ洨鏋?/button>
        <button class="btn btn-p btn-sm" onclick="openModal(null)">+ 婵烇綀顕ф慨鐐烘嚍閸屾粌浠?/button>
      </div>
    </div>
    <div class="nl" id="nodeList"></div>
  </div>

  <div class="cr">
    <h2>&#128214; 濞达綀娉曢弫銈囨嫚鐎涙ɑ顫?/h2>
    <div style="color:var(--text2);font-size:14px;line-height:1.8">
      <p>1. 闁绘劗鎳撻崵顕€濡? 婵烇綀顕ф慨鐐烘嚍閸屾粌浠柕鍡楃Т閿濈偤宕楅妷銈囩☉闁?SuperYellow 闁哄牆绉存慨鐔煎闯閵娿倓绻嗛柟?/p>
      <p>2. 闂侇偄顦懙鎴︽嚍閸屾粌浠柛姘嚱缁辨繈宕滃鍛獢 <strong style="color:var(--text)">PassWall 闁?闁煎搫鍊婚崑锝夊礆濡ゅ嫨鈧?/strong> 闂侇偄顦扮€氥劑濡寸€涚灝perYellow闁?/p>
      <p>3. 閻?PassWall 闁?TCP 婵☆垪鈧磭纭€閻犱礁褰炵拹鐔煎Υ鐏炵厧鈻忛柣顫妼閸亞鎮伴妸銉▎濞寸媴绲块幃濠囧Υ瀹ュ懎绁柛?/p>
      <p style="margin-top:8px;color:var(--accent)">&#128161; 闁哄牆绉存慨鐔煎闯閵娾晜浠橀悷鏇氱閸樻盯宕?Web 闂傚牄鍨哄妯衡枖閵娿儱鏂€闁活潿鍔嶉崺娑㈠箥瀹ュ牆鍘撮弶鈺冨仦鐢?/p>
    </div>
  </div>
</div>

<!-- Modal -->
<div class="mm" id="modal" onclick="if(event.target===this)closeModal()">
  <div class="md">
    <h3 id="modalTitle">婵烇綀顕ф慨鐐烘嚍閸屾粌浠?/h3>
    <div class="fg"><label>闁煎搫鍊婚崑锝夊触瀹ュ泦?/label><input id="fName" placeholder="濞撴艾顑戠槐浼村箣閹寸姵鐣遍柡鍫濈Т婵喖宕?></div>
    <div class="fg"><label>闁哄牆绉存慨鐔煎闯閵娿儲鍕鹃柛褉鍋?(IP:缂佹棏鍨拌ぐ?</label><input id="fServer" placeholder="濞撴艾顑戠槐?.2.3.4:8443" style="font-family:monospace"></div>
    <div class="fr">
      <div class="fg"><label>闁活潿鍔嶉崺娑㈠触?/label><input id="fUser" placeholder="Default"></div>
      <div class="fg"><label>閻庨潧妫涢悥?/label><input id="fPass" type="password" placeholder="闂佹潙鐡ㄥ鍫⑩偓闈涙閹?></div>
    </div>
    <div class="fg"><label>SNI (濞寸⒈浜ｉˉ濠囧春閻旈攱鍊?</label><input id="fSni" placeholder="濞撴艾顑戠槐鐧県aofanbox.top" style="font-family:monospace"></div>
    <div class="ma">
      <button class="btn btn-g" onclick="closeModal()">闁告瑦鐗楃粔?/button>
      <button class="btn btn-p" onclick="saveNode()">濞ｅ洦绻傞悺?/button>
    </div>
  </div>
</div>

<div class="tst" id="toast"></div>

<script>
var conf={enable:false,active_node_id:'',nodes:[]};
var running=false;
var editId=null;

function load(){
  fetch('/api').then(function(r){return r.json()}).then(function(d){
    running=d.running;
    conf=d.conf||conf;
    render();
  }).catch(function(){});
}

function render(){
  var dot=document.getElementById('title');
  dot.innerHTML='<span style="display:inline-block;width:10px;height:10px;border-radius:50%;margin-right:8px;background:'+(running?'#22c55e;box-shadow:0 0 10px rgba(34,197,94,.6)':'#ef4444')+'"></span>SuperYellow Proxy';

  document.getElementById('s1').innerHTML=running?'<span class="on">閺夆晜鍔橀、鎴炵▔?/span>':'<span class="off">鐎瑰憡褰冩禒鐘差潰?/span>';
  document.getElementById('s2').textContent=conf.nodes.length;
  var an=conf.nodes.find(function(n){return n.id===conf.active_node_id});
  document.getElementById('s3').textContent=an?an.name:'闁哄牜浜埀顒€顦扮€?;

  var btn=document.getElementById('toggleBtn');
  if(running){btn.className='btn btn-r';btn.innerHTML='&#9632; 闁稿绮嶉娑橆嚕閺囩喐鎯?}
  else{btn.className='btn btn-gn';btn.innerHTML='&#9654; 闁告凹鍨版慨鈺侇嚕閺囩喐鎯?}

  var list=document.getElementById('nodeList');
  if(conf.nodes.length===0){
    list.innerHTML='<div class="emp"><div style="font-size:32px;margin-bottom:8px">&#128225;</div>閺夆晜蓱閻ュ懘寮垫径鎰赋缂傚喚鍠涙俊顓㈡倷閻у摜绀夐柣鎰嚀閸ゎ噣宕ｉ崗鍛憪閻熸瑦甯囬埀? 婵烇綀顕ф慨鐐烘嚍閸屾粌浠柕鍡楃Т缁辨垶鎱?/div>';
    return;
  }
  var h='';
  conf.nodes.forEach(function(n){
    var act=n.id===conf.active_node_id;
    h+='<div class="nd'+(act?' act':'')+'" onclick="selectNode(\''+n.id+'\')">';
    h+='<div><div class="nm">'+esc(n.name)+(act?'<span class="badge">鐟滅増鎸告晶?/span>':'')+'</div>';
    h+='<div class="ad">'+esc(n.server)+' &middot; '+esc(n.username)+'</div></div>';
    h+='<div class="acts">';
    h+='<button class="btn btn-g btn-sm" onclick="event.stopPropagation();openModal(\''+n.id+'\')">&#9998; 缂傚倹鐗炵欢?/button>';
    h+='<button class="btn btn-d btn-sm" onclick="event.stopPropagation();delNode(\''+n.id+'\')">&#128465; 闁告帞濞€濞?/button>';
    h+='</div></div>';
  });
  list.innerHTML=h;
}

function esc(s){return s?s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;'):''}

function save(){
  fetch('/api',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(conf)}).then(function(){});
}

function toggle(){
  conf.enable=!conf.enable;
  save();
  setTimeout(load,1500);
}

function selectNode(id){
  conf.active_node_id=id;
  save();
}

function openModal(id){
  editId=id;
  var m=document.getElementById('modal');
  if(id){
    var n=conf.nodes.find(function(x){return x.id===id});
    if(!n)return;
    document.getElementById('modalTitle').textContent='缂傚倹鐗炵欢顐︽嚍閸屾粌浠?;
    document.getElementById('fName').value=n.name;
    document.getElementById('fServer').value=n.server;
    document.getElementById('fUser').value=n.username;
    document.getElementById('fPass').value=n.password;
    document.getElementById('fSni').value=n.sni||'';
  }else{
    document.getElementById('modalTitle').textContent='婵烇綀顕ф慨鐐烘嚍閸屾粌浠?;
    document.getElementById('fName').value='';
    document.getElementById('fServer').value='';
    document.getElementById('fUser').value='Default';
    document.getElementById('fPass').value='';
    document.getElementById('fSni').value='';
  }
  m.className='mm show';
  setTimeout(function(){document.getElementById('fName').focus()},100);
}

function closeModal(){document.getElementById('modal').className='mm'}

function saveNode(){
  var name=document.getElementById('fName').value.trim();
  var server=document.getElementById('fServer').value.trim();
  if(!name||!server){alert('闁告艾绉惰ⅷ闁告粌鏈﹢鍥礉閳ヨ櫕鐝ら柛锔芥緲濞煎啯绋夊鍫濆幋濞戞捁娅ｉ埞?);return}
  var obj={
    name:name,server:server,
    username:document.getElementById('fUser').value.trim()||'Default',
    password:document.getElementById('fPass').value,
    sni:document.getElementById('fSni').value.trim()
  };
  if(editId){
    var idx=conf.nodes.findIndex(function(x){return x.id===editId});
    if(idx>-1){obj.id=editId;conf.nodes[idx]=obj}
  }else{
    obj.id='n_'+Math.random().toString(36).substr(2,8);
    conf.nodes.push(obj);
    if(conf.nodes.length===1)conf.active_node_id=obj.id;
  }
  closeModal();save();showToast('鐎规瓕寮撶换姘扁偓?);
}

function delNode(id){
  var n=conf.nodes.find(function(x){return x.id===id});
  if(!confirm('缁绢収鍠栭悾楣冨礆閻樼粯鐝熼柕?+(n?n.name:'')+'闁靛棗绋勭槐?))return;
  conf.nodes=conf.nodes.filter(function(x){return x.id!==id});
  if(conf.active_node_id===id)conf.active_node_id=conf.nodes.length?conf.nodes[0].id:'';
  save();showToast('鐎瑰憡褰冮崹褰掓⒔?);
}

function copyLocalProxy(){
  copyText('SOCKS5 / HTTP CONNECT\nHost: 127.0.0.1\nPort: 11080\nAuth: none\nPassWall node type: Socks or HTTP');
  showToast('闁哄牜鍓欏﹢鎾箳閵夈儱寮冲ǎ鍥ｅ墲娴煎懎顔忛幓鎺濇Щ闁?);
}

function copyJson(){
  copyText(JSON.stringify(conf,null,2));showToast('闂佹澘绉堕悿?JSON 鐎瑰憡褰冮ˇ鏌ュ礆?);
}

function copyText(t){
  if(navigator.clipboard){navigator.clipboard.writeText(t)}
  else{var e=document.createElement('textarea');e.value=t;document.body.appendChild(e);e.select();document.execCommand('copy');document.body.removeChild(e)}
}

function showToast(msg){
  var t=document.getElementById('toast');t.textContent=msg;t.className='tst show';
  setTimeout(function(){t.className='tst'},2500);
}

load();
setInterval(load,3000);
</script>
</body>
</html>`
