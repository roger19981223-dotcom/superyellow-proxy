//go:build !js

package main

import (
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"math/big"
	"net"
	"net/http"
	"os"
	"os/signal"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/klauspost/reedsolomon"
	"golang.org/x/crypto/acme/autocert"

	"syscall"
)

const (
	NumStreams       = 6
	DataShards       = 5
	ParityShards     = 1
	MSS              = 1350
	HeaderSize       = 30
	Magic            = 0x41455448
	AuthTokenSize    = 32
	PingFlag         = 0x0001
	AuthFlag         = 0x0002
	PongFlag         = 0x0004
	AdaptiveFECFlag  = 0x0008
	ControlFrameFlag = 0x0010
	FastLaneFlag     = 0x0020
	ProtocolVersion  = 3
	AetherALPN       = "http/1.1"

	TargetDialTimeout  = 30 * time.Second
	MaxConcurrentConns = 2000
	ConfigFile         = "aether_config.json"
	StatsFile          = "aether_stats.json"

	SafeMTUPayload       = 1350
	TCPBufferSize        = 2 << 20
	MaxReorderWindow     = 8192
	MaxReassemblerBuf    = 64 << 20
	ReassemblerOutputCap = 2048
	SmallPacketFastLen   = 1200
	ReassemblerGapTTL    = 6 * time.Second
	TunnelWriteTimeout   = 5 * time.Second
	TargetConnIdleTTL    = 5 * time.Minute
	DebugLogging         = false
)

var (
	authReplayCache  sync.Map
	headerPool       = sync.Pool{New: func() interface{} { return make([]byte, HeaderSize) }}
	ShardPool        = sync.Pool{New: func() interface{} { b := make([]byte, HeaderSize+MSS+1024); return &b }}
	outputPool       = sync.Pool{New: func() interface{} { return make([]byte, 6*MSS+1024) }}
	randSeed         = uint32(time.Now().UnixNano())
	sysStartTime     = time.Now()
	globalDNSCache   sync.Map
	GlobalConfig     SysConfig
	configMu         sync.RWMutex
	ActiveUsers      map[string]UserConfig
	UserStats        sync.Map
	globalPanelToken string
	panelTokenMu     sync.RWMutex
	fecPool          sync.Map
)

func debugf(format string, args ...interface{}) {
	if DebugLogging {
		log.Printf(format, args...)
	}
}

func getEncoder(ds, ps int) reedsolomon.Encoder {
	if ds <= 0 {
		ds = DataShards
	}
	if ps <= 0 {
		ps = ParityShards
	}
	key := (uint32(ds) << 16) | uint32(ps)
	if v, ok := fecPool.Load(key); ok {
		return v.(reedsolomon.Encoder)
	}
	enc, err := reedsolomon.New(ds, ps)
	if err != nil {
		enc, _ = reedsolomon.New(DataShards, ParityShards)
	}
	fecPool.Store(key, enc)
	return enc
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
	bp := ShardPool.Get().(*[]byte)
	*bp = (*bp)[:cap(*bp)]
	return bp
}

func PutShardPtr(bp *[]byte) {
	ShardPool.Put(bp)
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

type dnsCacheEntry struct {
	ip     string
	expire int64
}

func resolveHostCached(host string) string {
	if net.ParseIP(host) != nil {
		return host
	}
	if v, ok := globalDNSCache.Load(host); ok && time.Now().Unix() < v.(*dnsCacheEntry).expire {
		return v.(*dnsCacheEntry).ip
	}
	ips, err := net.LookupIP(host)
	if err != nil || len(ips) == 0 {
		return host
	}
	ip := ips[0].String()
	for _, i := range ips {
		if i.To4() != nil {
			ip = i.String()
			break
		}
	}
	globalDNSCache.Store(host, &dnsCacheEntry{ip: ip, expire: time.Now().Unix() + 1800})
	return ip
}

func isLocalIP(ipStr string) bool {
	if ipStr == "127.0.0.1" || ipStr == "::1" || ipStr == "localhost" {
		return true
	}
	addrs, err := net.InterfaceAddrs()
	if err != nil {
		return false
	}
	for _, address := range addrs {
		if ipnet, ok := address.(*net.IPNet); ok {
			if ipnet.IP.String() == ipStr {
				return true
			}
		}
	}
	return false
}

type SafeWG struct {
	count     atomic.Int32
	closed    atomic.Bool
	done      chan struct{}
	once      sync.Once
	closeOnce sync.Once
	mu        sync.Mutex
}

func (s *SafeWG) init() {
	s.once.Do(func() { s.done = make(chan struct{}) })
}

func (s *SafeWG) Add() bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.init()
	if s.closed.Load() {
		return false
	}
	s.count.Add(1)
	return true
}

func (s *SafeWG) Done() {
	if v := s.count.Add(-1); v < 0 {
		s.count.Add(1)
	} else if v == 0 && s.closed.Load() {
		s.closeOnce.Do(func() { close(s.done) })
	}
}

func (s *SafeWG) Wait() {
	s.mu.Lock()
	s.init()
	s.closed.Store(true)
	if s.count.Load() == 0 {
		s.closeOnce.Do(func() { close(s.done) })
	}
	s.mu.Unlock()
	<-s.done
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

type SafeConn struct {
	conn    net.Conn
	writeMu sync.Mutex
	closed  atomic.Bool
}

func (sc *SafeConn) Write(b []byte) (int, error) {
	if sc.closed.Load() {
		return 0, io.EOF
	}
	sc.writeMu.Lock()
	defer sc.writeMu.Unlock()
	sc.conn.SetWriteDeadline(time.Now().Add(TunnelWriteTimeout))
	defer sc.conn.SetWriteDeadline(time.Time{})
	n, err := sc.conn.Write(b)
	if err != nil {
		sc.Close()
	}
	return n, err
}

func (sc *SafeConn) Close() error {
	if sc.closed.CompareAndSwap(false, true) {
		return sc.conn.Close()
	}
	return nil
}

func (sc *SafeConn) IsClosed() bool {
	return sc.closed.Load()
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

func (h *PacketHeader) Encode() []byte {
	b := headerPool.Get().([]byte)
	for i := range b {
		b[i] = 0
	}
	h.EncodeTo(b)
	return b
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
	return DataShards, ParityShards
}

func (h *PacketHeader) SetFEC(ds uint8, ps uint8) {
	h.Flags |= AdaptiveFECFlag
	h.Reserved = (uint32(ds) << 24) | (uint32(ps) << 16) | (h.Reserved & 0xFFFF)
	h.Reserved = (h.Reserved & 0xFFFFFF00) | ProtocolVersion
}

type parsedFrame struct {
	Type    byte
	ConnID  uint32
	Payload []byte
}

func encodeFrame(t byte, id uint32, p []byte) []byte {
	f := make([]byte, 7+len(p))
	f[0] = t
	binary.BigEndian.PutUint32(f[1:5], id)
	binary.BigEndian.PutUint16(f[5:7], uint16(len(p)))
	if len(p) > 0 {
		copy(f[7:], p)
	}
	return f
}

func parseConnectPayload(p []byte) (string, uint16, error) {
	if len(p) < 3 {
		return "", 0, fmt.Errorf("err")
	}
	al := int(p[0])
	if len(p) < 3+al {
		return "", 0, fmt.Errorf("err")
	}
	return string(p[1 : 1+al]), binary.BigEndian.Uint16(p[1+al:]), nil
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

type decodedRecord struct {
	decodedAt time.Time
}

type TCPReassembler struct {
	mu              sync.Mutex
	windows         map[uint32]*TCPReassemblerEntry
	decoded         map[uint32]*decodedRecord
	outputCh        chan []byte
	clientID        uint32
	cleanupTicker   *time.Ticker
	stopCh          chan struct{}
	decodedTTL      time.Duration
	closeOnce       sync.Once
	initialized     bool
	nextExpectedSeq uint32
	readyBuffer     map[uint32][]byte
	bufferedBytes   int
	lastAdvance     time.Time
}

func NewTCPReassembler(cid uint32, ttl time.Duration) *TCPReassembler {
	ar := &TCPReassembler{
		windows:     make(map[uint32]*TCPReassemblerEntry),
		decoded:     make(map[uint32]*decodedRecord),
		outputCh:    make(chan []byte, ReassemblerOutputCap),
		clientID:    cid,
		stopCh:      make(chan struct{}),
		decodedTTL:  ttl,
		readyBuffer: make(map[uint32][]byte),
		lastAdvance: time.Now(),
	}
	cleanupInterval := ttl / 4
	if cleanupInterval > 2*time.Second {
		cleanupInterval = 2 * time.Second
	}
	if cleanupInterval < time.Second {
		cleanupInterval = time.Second
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
	if seqNo-ar.nextExpectedSeq > MaxReorderWindow || ar.bufferedBytes > MaxReassemblerBuf {
		ar.mu.Unlock()
		PutShardPtr(dataPtr)
		log.Printf("[WARN] reassembler overflow: seq=%d expected=%d buffered=%d, rebooting", seqNo, ar.nextExpectedSeq, ar.bufferedBytes)
		ar.Close()
		return
	}
	if ds == 0 {
		ds = DataShards
		ps = ParityShards
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
				log.Printf("[WARN] reassembler output queue full: expected=%d buffered=%d, closing session", ar.nextExpectedSeq, ar.bufferedBytes)
				ar.Close()
				return
			}
		} else {
			log.Printf("[WARN] FEC seq %d still missing, waiting for parity", ar.nextExpectedSeq)
			break
		}

		delete(ar.readyBuffer, ar.nextExpectedSeq)
		ar.bufferedBytes -= len(payload)
		ar.nextExpectedSeq++
		ar.lastAdvance = time.Now()
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
	if len(ar.readyBuffer) > 0 && n.Sub(ar.lastAdvance) > ReassemblerGapTTL {
		log.Printf("[WARN] reassembler gap timeout: expected=%d ready=%d buffered=%d", ar.nextExpectedSeq, len(ar.readyBuffer), ar.bufferedBytes)
		ar.mu.Unlock()
		ar.Close()
		return
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

type targetConn struct {
	conn       net.Conn
	id         uint32
	cl         atomic.Bool
	lastActive atomic.Int64
	closeOnce  sync.Once
	d          chan struct{}
	wc         chan []byte
	tm         *TargetConnManager
}

func (tc *targetConn) touch() {
	tc.lastActive.Store(time.Now().UnixNano())
}

func (tc *targetConn) idleFor(now time.Time) time.Duration {
	last := tc.lastActive.Load()
	if last == 0 {
		return 0
	}
	return now.Sub(time.Unix(0, last))
}

func (tc *targetConn) Close() {
	tc.closeOnce.Do(func() {
		close(tc.d)
		if tc.conn != nil {
			tc.conn.Close()
		}
		if tc.tm != nil {
			tc.tm.Remove(tc.id)
		}
	})
	tc.cl.Store(true)
}

func (tc *targetConn) wl(s *Session) {
	defer s.wg.Done()
	defer tc.Close()
	for {
		select {
		case p, ok := <-tc.wc:
			if !ok {
				return
			}
			tc.touch()
			if p == nil {
				if tcp, ok := tc.conn.(*net.TCPConn); ok {
					tcp.CloseWrite()
					continue
				}
				return
			}
			tc.conn.SetWriteDeadline(time.Now().Add(15 * time.Second))
			if _, e := tc.conn.Write(p); e != nil {
				return
			}
			tc.conn.SetWriteDeadline(time.Time{})
		case <-tc.d:
			return
		case <-s.cc:
			return
		}
	}
}

type TargetConnManager struct {
	mu sync.RWMutex
	c  map[uint32]*targetConn
	cl bool
}

func NewTargetConnManager() *TargetConnManager {
	return &TargetConnManager{c: make(map[uint32]*targetConn)}
}

func (tm *TargetConnManager) Add(id uint32, tc *targetConn) error {
	tm.mu.Lock()
	defer tm.mu.Unlock()
	if tm.cl || len(tm.c) >= MaxConcurrentConns {
		return fmt.Errorf("err")
	}
	tm.c[id] = tc
	return nil
}

func (tm *TargetConnManager) Get(id uint32) (*targetConn, bool) {
	tm.mu.RLock()
	defer tm.mu.RUnlock()
	tc, ok := tm.c[id]
	return tc, ok
}

func (tm *TargetConnManager) Remove(id uint32) {
	tm.mu.Lock()
	delete(tm.c, id)
	tm.mu.Unlock()
}

func (tm *TargetConnManager) CloseAll() {
	tm.mu.Lock()
	tm.cl = true
	c := tm.c
	tm.c = make(map[uint32]*targetConn)
	tm.mu.Unlock()
	for _, tc := range c {
		tc.Close()
	}
}

func (tm *TargetConnManager) CloseIdle(timeout time.Duration) int {
	now := time.Now()
	var stale []*targetConn
	tm.mu.RLock()
	for _, tc := range tm.c {
		if !tc.cl.Load() && tc.idleFor(now) > timeout {
			stale = append(stale, tc)
		}
	}
	tm.mu.RUnlock()
	for _, tc := range stale {
		tc.Close()
	}
	return len(stale)
}

func (tm *TargetConnManager) Range(fn func(key uint32, tc *targetConn) bool) {
	tm.mu.RLock()
	defer tm.mu.RUnlock()
	for k, tc := range tm.c {
		if !fn(k, tc) {
			return
		}
	}
}

type Session struct {
	cid       uint32
	uid       string
	currentDS uint8
	currentPS uint8
	enc       reedsolomon.Encoder
	tm        *TargetConnManager
	pfb       []byte
	cfb       []byte
	do        sync.Once
	fw        atomic.Uint32
	cfw       atomic.Uint32
	tr        *TCPReassembler
	cr        *TCPReassembler
	la        atomic.Int64
	ic        atomic.Bool
	cs        chan struct{}
	cc        chan struct{}
	wg        SafeWG
	fs        chan struct{}
	sts       atomic.Value
	sm        sync.Mutex
	sdm       sync.RWMutex
	wm        sync.Mutex
	ut        sync.Map
}

func NewSession(cid uint32, uid string) *Session {
	s := &Session{
		cid:       cid,
		uid:       uid,
		currentDS: DataShards,
		currentPS: ParityShards,
		enc:       getEncoder(DataShards, ParityShards),
		tm:        NewTargetConnManager(),
		tr:        NewTCPReassembler(cid, 120*time.Second),
		cr:        NewTCPReassembler(cid, 120*time.Second),
		fs:        make(chan struct{}, 256),
		cs:        make(chan struct{}, MaxConcurrentConns),
		cc:        make(chan struct{}),
	}
	s.sts.Store(make([]*SafeConn, 0, NumStreams))
	s.la.Store(time.Now().Unix())
	return s
}

func (s *Session) Close() {
	if s.ic.CompareAndSwap(false, true) {
		close(s.cc)
		s.wg.closed.Store(true) // 确保立即拒绝新的 Add() 请求
		s.sm.Lock()
		cur := s.sts.Load().([]*SafeConn)
		for _, st := range cur {
			if st != nil {
				st.Close()
			}
		}
		s.sm.Unlock()
		s.tm.CloseAll()
		s.ut.Range(func(k, v interface{}) bool {
			v.(*net.UDPConn).Close()
			return true
		})
		s.tr.Close()
		s.cr.Close()
		// 核心修复 1：彻底移除导致 fdl 永久冻结的 s.wg.Wait() 死锁代码
	}
}

func (s *Session) rs(c net.Conn) *SafeConn {
	s.sm.Lock()
	defer s.sm.Unlock()
	if s.ic.Load() {
		c.Close()
		return nil
	}
	os := s.sts.Load().([]*SafeConn)
	sc := &SafeConn{conn: c}
	var ns []*SafeConn
	replaced := false
	for _, e := range os {
		if e == nil || e.IsClosed() {
			if e != nil {
				e.Close()
			}
			if !replaced {
				ns = append(ns, sc)
				replaced = true
			}
		} else {
			ns = append(ns, e)
		}
	}
	if !replaced {
		if len(ns) < NumStreams {
			ns = append(ns, sc)
		} else {
			if len(ns) > 0 {
				if ns[0] != nil {
					ns[0].Close()
				}
				ns[0] = sc
			}
		}
	}
	s.sts.Store(ns)
	return sc
}

func (s *Session) getStreams() []*SafeConn {
	return s.sts.Load().([]*SafeConn)
}

type Server struct {
	s  map[uint32]*Session
	mu sync.Mutex
}

func NewServer() *Server {
	srv := &Server{s: make(map[uint32]*Session)}
	go srv.sj()
	return srv
}

func (srv *Server) GetOrCreate(cid uint32, uid string) *Session {
	// FIX: Check existing under lock, release before creating new session.
	// Prevents deadlock where sj() holds srv.mu and calls s.Close() -> s.sm.Lock()
	// while this goroutine holds s.sm and waits for srv.mu.
	srv.mu.Lock()
	if s, ok := srv.s[cid]; ok {
		if !s.ic.Load() {
			srv.mu.Unlock()
			return s
		}
		// Zombie session - remove and replace
		delete(srv.s, cid)
	}
	srv.mu.Unlock()

	// Create session OUTSIDE global lock
	s := NewSession(cid, uid)

	srv.mu.Lock()
	// Double-check: another goroutine may have created this session
	if existing, ok := srv.s[cid]; ok {
		srv.mu.Unlock()
		if !existing.ic.Load() {
			return existing
		}
		// Existing is zombie, use our new one
		srv.mu.Lock()
	}
	srv.s[cid] = s
	srv.mu.Unlock()
	return s
}

func (srv *Server) sj() {
	tk := time.NewTicker(30 * time.Second)
	defer tk.Stop()
	for range tk.C {
		n := time.Now().Unix()
		// FIX: Collect stale session IDs under lock, release lock, THEN close them.
		// This prevents deadlock where s.Close() tries to acquire s.sm while
		// another goroutine holds s.sm and waits for srv.mu.
		var stale []*Session
		srv.mu.Lock()
		for cid, s := range srv.s {
			if n-s.la.Load() > 300 || s.ic.Load() {
				stale = append(stale, s)
				delete(srv.s, cid)
			}
		}
		srv.mu.Unlock()
		for _, s := range stale {
			s.Close()
		}
		srv.mu.Lock()
		active := make([]*Session, 0, len(srv.s))
		for _, s := range srv.s {
			active = append(active, s)
		}
		srv.mu.Unlock()
		for _, s := range active {
			if closed := s.tm.CloseIdle(TargetConnIdleTTL); closed > 0 {
				debugf("[SRV] closed %d idle target connections for cid=%d", closed, s.cid)
			}
		}
		authReplayCache.Range(func(k, v interface{}) bool {
			if n-v.(int64) > 60 {
				authReplayCache.Delete(k)
			}
			return true
		})
	}
}

func (srv *Server) hs(cn net.Conn) {
	cn.SetReadDeadline(time.Now().Add(5 * time.Second))
	hb := make([]byte, HeaderSize)
	if _, e := io.ReadFull(cn, hb); e != nil {
		cn.Close()
		return
	}
	h := DecodeHeader(hb)
	if h.Magic != Magic {
		fallbackToCamo(cn, hb)
		return
	}
	if h.Flags&AdaptiveFECFlag != 0 && byte(h.Reserved&0xFF) != ProtocolVersion {
		log.Printf("[SRV] protocol version mismatch: got=%d want=%d", byte(h.Reserved&0xFF), ProtocolVersion)
		cn.Close()
		return
	}
	nMs := uint32(time.Now().UnixMilli() & 0xFFFFFFFF)
	if h.Flags&AuthFlag == 0 || h.ChunkSize < 32 || h.ChunkSize > 512 {
		cn.Close()
		return
	}

	timeDiff := int32(nMs - h.Timestamp)
	if timeDiff < 0 {
		timeDiff = -timeDiff
	}

	// 修复：放宽时钟同步限制到120秒，防止软路由时间漂移导致的秒杀拦截
	if timeDiff > 120000 {
		log.Printf("[SRV] 拒绝连接: 客户端时间戳误差过大 (diff=%dms)！请检查并同步客户端设备(如OpenWrt)的时间！", timeDiff)
		cn.Close()
		return
	}

	ap := make([]byte, h.ChunkSize+uint32(h.PaddingLen))
	if _, e := io.ReadFull(cn, ap); e != nil {
		cn.Close()
		return
	}
	replayMaterial := make([]byte, 0, len(hb)+int(h.ChunkSize))
	replayMaterial = append(replayMaterial, hb...)
	replayMaterial = append(replayMaterial, ap[:h.ChunkSize]...)
	ah := sha256.Sum256(replayMaterial)
	if _, l := authReplayCache.LoadOrStore(string(ah[:]), time.Now().Unix()); l {
		cn.Close()
		return
	}
	configMu.RLock()
	var mUID string
	for sec, u := range ActiveUsers {
		if u.Enable && (u.ExpireAt == 0 || time.Now().Unix() < u.ExpireAt) {
			if s, ok := UserStats.Load(u.ID); !ok || u.Limit == 0 || (s.(*TrafficStat).Tx.Load()+s.(*TrafficStat).Rx.Load() < u.Limit) {
				tk := deriveToken(sec, h.Timestamp)
				if string(tk[:]) == string(ap[:32]) {
					mUID = u.ID
					break
				}
			}
		}
	}
	configMu.RUnlock()
	if mUID == "" {
		cn.Close()
		return
	}
	s := srv.GetOrCreate(h.ClientID, mUID)
	sc := s.rs(cn)
	if sc == nil {
		cn.Close()
		return
	}
	s.do.Do(func() {
		if s.wg.Add() {
			go srv.fdl(s)
		}
	})
	for {
		cn.SetReadDeadline(time.Now().Add(60 * time.Second))
		if _, e := io.ReadFull(cn, hb); e != nil {
			break
		}
		h = DecodeHeader(hb)
		if h.Magic != Magic {
			break
		}
		if h.Flags&AdaptiveFECFlag != 0 && byte(h.Reserved&0xFF) != ProtocolVersion {
			log.Printf("[SRV] protocol version mismatch on stream: got=%d want=%d", byte(h.Reserved&0xFF), ProtocolVersion)
			break
		}

		ds, ps := h.GetFEC()
		if ds > 0 && ps > 0 && h.Flags&(ControlFrameFlag|FastLaneFlag|PingFlag|PongFlag|AuthFlag) == 0 {
			s.sdm.Lock()
			if s.currentDS != ds || s.currentPS != ps {
				s.currentDS = ds
				s.currentPS = ps
				s.enc = getEncoder(int(ds), int(ps))
			}
			s.sdm.Unlock()
		}

		ss := int((h.ChunkSize + uint32(ds) - 1) / uint32(ds))
		tl := uint32(ss) + uint32(h.PaddingLen)
		if tl > MSS+512 {
			break
		}
		var bp *[]byte
		if tl > 0 {
			bp = GetShardPtr()
			if _, e := io.ReadFull(cn, (*bp)[HeaderSize:HeaderSize+int(tl)]); e != nil {
				PutShardPtr(bp)
				break
			}
		}
		recordTraffic(s.uid, 0, uint64(HeaderSize+tl))
		s.la.Store(time.Now().Unix())
		if h.Flags&PongFlag != 0 {
			if bp != nil {
				PutShardPtr(bp)
			}
			continue
		}
		if h.Flags&PingFlag != 0 {
			pl := generateSmartPadding(HeaderSize)
			p := &PacketHeader{Magic: Magic, ClientID: h.ClientID, Flags: PongFlag, Timestamp: h.Timestamp, PaddingLen: pl}
			bo := GetShardPtr()
			p.EncodeTo((*bo)[:HeaderSize])
			for i := HeaderSize; i < HeaderSize+int(pl); i++ {
				(*bo)[i] = 0
			}
			sc.Write((*bo)[:HeaderSize+int(pl)])
			PutShardPtr(bo)
			if bp != nil {
				PutShardPtr(bp)
			}
			continue
		}
		if bp != nil {
			*bp = (*bp)[:HeaderSize+ss]
			if h.Flags&ControlFrameFlag != 0 {
				s.cr.AddShard(h.SeqNo, h.ShardIdx, h.ChunkSize, bp, ds, ps)
			} else {
				s.tr.AddShard(h.SeqNo, h.ShardIdx, h.ChunkSize, bp, ds, ps)
			}
		}
	}
	sc.Close()
}

func (srv *Server) fdl(s *Session) {
	defer func() {
		s.wg.Done()
		if s.ic.CompareAndSwap(false, true) {
			close(s.cc)
		}
		s.Close() // Close all streams + FEC, force RST/FIN to client
	}()

	for {
		select {
		case <-s.tr.stopCh:
			return
		case <-s.cr.stopCh:
			return
		case <-s.cc:
			return
		case d := <-s.tr.Output():
			if !srv.handleClientFrames(s, &s.pfb, d) {
				return
			}
		case d := <-s.cr.Output():
			if !srv.handleClientFrames(s, &s.cfb, d) {
				return
			}
		}
	}
}

func (srv *Server) handleClientFrames(s *Session, pfb *[]byte, d []byte) bool {
	frames, ok := parseFrames(pfb, d)
	if !ok {
		outputPool.Put(d[:cap(d)])
		return false
	}
	for _, f := range frames {
		switch f.Type {
		case 0x01:
			wc := make(chan []byte, 1024)
			tc := &targetConn{conn: nil, id: f.ConnID, d: make(chan struct{}), wc: wc, tm: s.tm}
			tc.touch()
			if s.tm.Add(f.ConnID, tc) != nil {
				srv.stc(s, encodeFrame(2, f.ConnID, nil))
				break
			}
			select {
			case s.cs <- struct{}{}:
				go func(tc2 *targetConn, p []byte) {
					defer func() { <-s.cs }()
					srv.hcWithPreReg(s, tc2, p)
				}(tc, f.Payload)
			default:
				s.tm.Remove(f.ConnID)
				srv.stc(s, encodeFrame(2, f.ConnID, nil))
			}
		case 0x02:
			if tc, ok := s.tm.Get(f.ConnID); ok && !tc.cl.Load() {
				tc.touch()
				select {
				case tc.wc <- f.Payload:
				default:
					tc.Close()
				}
			}
		case 0x03:
			if tc, ok := s.tm.Get(f.ConnID); ok {
				tc.Close()
			}
			if uc, ok := s.ut.LoadAndDelete(f.ConnID); ok {
				uc.(*net.UDPConn).Close()
			}
		case 0x06:
			if tc, ok := s.tm.Get(f.ConnID); ok && !tc.cl.Load() {
				select {
				case tc.wc <- nil:
				default:
					tc.Close()
				}
			}
		case 0x05:
			select {
			case s.cs <- struct{}{}:
				go func(id uint32, p []byte) {
					defer func() { <-s.cs }()
					srv.hu(s, id, p)
				}(f.ConnID, f.Payload)
			default:
			}
		}
	}
	outputPool.Put(d[:cap(d)])
	return true
}

func (srv *Server) hcWithPreReg(s *Session, tc *targetConn, p []byte) {
	a, pt, e := parseConnectPayload(p)
	if e != nil {
		s.tm.Remove(tc.id)
		srv.stc(s, encodeFrame(2, tc.id, nil))
		return
	}
	if s.ic.Load() {
		s.tm.Remove(tc.id)
		return
	}

	resolvedHost := resolveHostCached(a)

	// 防治客户端透明代理引发的回环攻击 (Routing Loop)
	configMu.RLock()
	listenPorts := GlobalConfig.ListenPorts
	configMu.RUnlock()

	isSelfPort := false
	for _, lp := range strings.Split(listenPorts, ",") {
		if strings.TrimSpace(lp) == fmt.Sprint(pt) {
			isSelfPort = true
			break
		}
	}

	if isSelfPort && isLocalIP(resolvedHost) {
		log.Printf("[SRV] 🛑 拒绝回环拨号: 拦截到客户端发往服务器自身监听端口的死循环请求 -> %s:%d", resolvedHost, pt)
		s.tm.Remove(tc.id)
		srv.stc(s, encodeFrame(2, tc.id, nil))
		return
	}

	t := net.JoinHostPort(resolvedHost, fmt.Sprint(pt))
	debugf("[SRV] dialing target -> %s", t)
	cn, e := net.DialTimeout("tcp", t, TargetDialTimeout)
	if e != nil {
		debugf("[SRV] dial failed -> %s error: %v", t, e)
		s.tm.Remove(tc.id)
		srv.stc(s, encodeFrame(2, tc.id, nil))
		return
	}
	debugf("[SRV] dial ok -> %s", t)
	if !s.wg.Add() {
		cn.Close()
		s.tm.Remove(tc.id)
		return
	}
	if !s.wg.Add() {
		s.wg.Done()
		cn.Close()
		s.tm.Remove(tc.id)
		return
	}
	TuneTCPConn(cn)
	tc.conn = cn
	tc.touch()
	srv.stc(s, encodeFrame(1, tc.id, nil))
	go tc.wl(s)
	go func() {
		defer s.wg.Done()
		defer tc.Close()

		bufSize := int(s.currentDS)*MSS - 7
		if bufSize > 32768 {
			bufSize = 32768
		}
		b := make([]byte, bufSize)

		for {
			tc.conn.SetReadDeadline(time.Now().Add(15 * time.Minute))
			n, e := tc.conn.Read(b)
			if n > 0 {
				tc.touch()
				s.la.Store(time.Now().Unix())
				frame := encodeFrame(4, tc.id, b[:n])
				if len(frame) <= SmallPacketFastLen {
					srv.stcFast(s, frame)
				} else {
					srv.stc(s, frame)
				}
			}
			if e != nil {
				srv.stc(s, encodeFrame(6, tc.id, nil))
				return
			}
		}
	}()
}

func (srv *Server) hu(s *Session, id uint32, p []byte) {
	if len(p) < 4 {
		return
	}
	atyp := p[0]
	var host string
	var port uint16
	var data []byte
	switch atyp {
	case 1:
		if len(p) < 7 {
			return
		}
		host = net.IP(p[1:5]).String()
		port = binary.BigEndian.Uint16(p[5:7])
		data = p[7:]
	case 3:
		dl := int(p[1])
		if len(p) < 4+dl {
			return
		}
		host = string(p[2 : 2+dl])
		port = binary.BigEndian.Uint16(p[2+dl : 4+dl])
		data = p[4+dl:]
	case 4:
		if len(p) < 19 {
			return
		}
		host = net.IP(p[1:17]).String()
		port = binary.BigEndian.Uint16(p[17:19])
		data = p[19:]
	default:
		return
	}

	resolvedHost := resolveHostCached(host)

	// 防治 UDP 透明代理回环
	configMu.RLock()
	listenPorts := GlobalConfig.ListenPorts
	configMu.RUnlock()

	isSelfPort := false
	for _, lp := range strings.Split(listenPorts, ",") {
		if strings.TrimSpace(lp) == fmt.Sprint(port) {
			isSelfPort = true
			break
		}
	}

	if isSelfPort && isLocalIP(resolvedHost) {
		return
	}

	tg := net.JoinHostPort(resolvedHost, fmt.Sprint(port))
	addr, err := net.ResolveUDPAddr("udp", tg)
	if err != nil {
		return
	}
	ci, ok := s.ut.Load(id)
	if !ok {
		uc, err := net.ListenUDP("udp", nil)
		if err != nil {
			return
		}
		actualCI, loaded := s.ut.LoadOrStore(id, uc)
		if loaded {
			uc.Close()
			ci = actualCI
		} else {
			ci = uc
			go srv.utrl(s, id, uc)
		}
	}
	uc := ci.(*net.UDPConn)
	uc.SetWriteDeadline(time.Now().Add(5 * time.Second))
	uc.WriteToUDP(data, addr)
	recordTraffic(s.uid, 0, uint64(len(data)))
}

func (srv *Server) utrl(s *Session, id uint32, uc *net.UDPConn) {
	defer uc.Close()
	defer func() {
		if v, ok := s.ut.Load(id); ok && v.(*net.UDPConn) == uc {
			s.ut.Delete(id)
		}
	}()
	b := make([]byte, 65536)
	for {
		uc.SetReadDeadline(time.Now().Add(2 * time.Minute))
		n, a, e := uc.ReadFromUDP(b)
		if e != nil {
			return
		}
		var p []byte
		if i4 := a.IP.To4(); i4 != nil {
			p = make([]byte, 7+n)
			p[0] = 1
			copy(p[1:5], i4)
			binary.BigEndian.PutUint16(p[5:7], uint16(a.Port))
			copy(p[7:], b[:n])
		} else {
			i16 := a.IP.To16()
			p = make([]byte, 19+n)
			p[0] = 4
			copy(p[1:17], i16)
			binary.BigEndian.PutUint16(p[17:19], uint16(a.Port))
			copy(p[19:], b[:n])
		}
		if len(p) > 65535 {
			continue
		}
		srv.stc(s, encodeFrame(5, id, p))
		recordTraffic(s.uid, uint64(len(p)), 0)
	}
}

func (srv *Server) stc(s *Session, d []byte) {
	srv.stcWithMode(s, d, isServerControlFrame(d), false)
}

func (srv *Server) stcFast(s *Session, d []byte) {
	srv.stcWithMode(s, d, isServerControlFrame(d), true)
}

func isServerControlFrame(data []byte) bool {
	if len(data) < 7 {
		return false
	}
	if len(data) != 7+int(binary.BigEndian.Uint16(data[5:7])) {
		return false
	}
	return data[0] == 0x01 || data[0] == 0x02 || data[0] == 0x03
}

func chooseServerDataFEC(active, curDS, curPS, remaining int) (int, int) {
	if remaining <= SmallPacketFastLen {
		return 1, 2
	}
	switch {
	case active >= 6:
		if curDS <= 1 || curPS <= 0 {
			return DataShards, ParityShards
		}
		return curDS, curPS
	case active == 5:
		return 4, 2
	case active == 4:
		return 3, 2
	case active == 3:
		return 2, 2
	default:
		return 1, 2
	}
}

func (srv *Server) stcWithMode(s *Session, d []byte, control bool, forceFast bool) {
	if len(d) == 0 {
		return
	}
	if s.ic.Load() {
		return
	}
	s.la.Store(time.Now().Unix())
	s.wm.Lock()
	defer s.wm.Unlock()
	o := 0
	for o < len(d) {
		if s.ic.Load() {
			return
		}
		sts := s.getStreams()
		var vs []*SafeConn
		for _, st := range sts {
			if st != nil && !st.IsClosed() {
				vs = append(vs, st)
			}
		}
		if len(vs) == 0 {
			return
		}

		var ds, ps int
		var enc reedsolomon.Encoder
		var sq uint32
		var fastLane bool
		if control || forceFast {
			ds, ps = 1, 2
			enc = getEncoder(ds, ps)
			if control {
				sq = s.cfw.Add(1) - 1
			} else {
				sq = s.fw.Add(1) - 1
				fastLane = true
			}
		} else {
			s.sdm.RLock()
			ds, ps = chooseServerDataFEC(len(vs), int(s.currentDS), int(s.currentPS), len(d)-o)
			sq = s.fw.Add(1) - 1
			s.sdm.RUnlock()
			enc = getEncoder(ds, ps)
			fastLane = ds == 1 && ps >= 2
		}
		if enc == nil {
			return
		}
		total := ds + ps

		e := o + ds*MSS
		if e > len(d) {
			e = len(d)
		}
		c := d[o:e]
		cs := uint32(len(c))
		ss := int((cs + uint32(ds) - 1) / uint32(ds))
		if ss > MSS {
			ss = MSS
		}

		sh := make([][]byte, total)
		pt := make([]*[]byte, total)

		for i := 0; i < ds; i++ {
			sp := GetShardPtr()
			pt[i] = sp
			pl := (*sp)[HeaderSize : HeaderSize+ss]
			for j := range pl {
				pl[j] = 0
			}
			st, en := i*ss, i*ss+ss
			if st < int(cs) {
				if en > int(cs) {
					en = int(cs)
				}
				copy(pl, c[st:en])
			}
			sh[i] = pl
		}
		for i := ds; i < total; i++ {
			sp := GetShardPtr()
			pt[i] = sp
			pl := (*sp)[HeaderSize : HeaderSize+ss]
			for j := range pl {
				pl[j] = 0
			}
			sh[i] = pl
		}

		err := enc.Encode(sh)
		if err != nil {
			for _, sp := range pt {
				if sp != nil {
					PutShardPtr(sp)
				}
			}
			return
		}
		ts := uint32(time.Now().UnixMilli() & 0xFFFFFFFF)

		success := 0
		func(sq, cs, ts uint32, pa []*[]byte, sa [][]byte, v []*SafeConn, ds, ps uint8) {
			defer func() {
				for _, sp := range pa {
					if sp != nil {
						PutShardPtr(sp)
					}
				}
			}()
			sf := fastRand() % uint32(len(v))
			totalShards := int(ds) + int(ps)
			for i := 0; i < totalShards; i++ {
				st := v[(uint32(i)+sf)%uint32(len(v))]
				if st == nil {
					continue
				}

				actualChunkSize := HeaderSize + len(sa[i])
				pl := generateSmartPadding(actualChunkSize)

				h := &PacketHeader{Magic: Magic, ClientID: s.cid, SeqNo: sq, ShardIdx: uint16(i), PaddingLen: pl, ChunkSize: cs, Timestamp: ts}
				if control {
					h.Flags |= ControlFrameFlag
				} else if fastLane {
					h.Flags |= FastLaneFlag
				}
				h.SetFEC(ds, ps)
				sp := pa[i]
				h.EncodeTo((*sp)[:HeaderSize])
				pe := HeaderSize + len(sa[i])
				pkt := (*sp)[:pe+int(pl)]
				for j := pe; j < pe+int(pl); j++ {
					(*sp)[j] = 0
				}
				if n, err := st.Write(pkt); err != nil {
					// 仅安全移除问题流，逻辑层绝对隔离不影响业务
					st.Close()
					s.sm.Lock()
					sts := s.getStreams()
					for idx, ss := range sts {
						if ss == st {
							sts[idx] = nil
							break
						}
					}
					s.sts.Store(sts)
					s.sm.Unlock()
				} else if n == len(pkt) {
					success++
					recordTraffic(s.uid, uint64(n), 0)
				} else {
					st.Close()
				}
			}
		}(sq, cs, ts, pt, sh, vs, uint8(ds), uint8(ps))
		if success < ds {
			log.Printf("[SRV] shard write quorum failed: cid=%d seq=%d success=%d required=%d active=%d", s.cid, sq, success, ds, len(vs))
			s.Close()
			return
		}
		o = e
	}
}

type PrefixConn struct {
	net.Conn
	prefix []byte
	offset int
}

func (c *PrefixConn) Read(b []byte) (int, error) {
	if c.offset < len(c.prefix) {
		n := copy(b, c.prefix[c.offset:])
		c.offset += n
		return n, nil
	}
	return c.Conn.Read(b)
}

func extractSNI(buf []byte) (string, bool) {
	if len(buf) < 43 || buf[0] != 0x16 || buf[5] != 0x01 {
		return "", false
	}
	sessionIDLen := int(buf[43])
	if len(buf) < 44+sessionIDLen+2 {
		return "", true
	}
	cipherLen := int(binary.BigEndian.Uint16(buf[44+sessionIDLen : 44+sessionIDLen+2]))
	offset := 44 + sessionIDLen + 2 + cipherLen
	if len(buf) < offset+1 {
		return "", true
	}
	compLen := int(buf[offset])
	offset += 1 + compLen
	if len(buf) < offset+2 {
		return "", true
	}
	extLen := int(binary.BigEndian.Uint16(buf[offset : offset+2]))
	offset += 2
	end := offset + extLen
	if end > len(buf) {
		end = len(buf)
	}

	for offset+4 <= end {
		extType := binary.BigEndian.Uint16(buf[offset : offset+2])
		extL := int(binary.BigEndian.Uint16(buf[offset+2 : offset+4]))
		offset += 4
		if extType == 0x0000 {
			if offset+2 <= end {
				listLen := int(binary.BigEndian.Uint16(buf[offset : offset+2]))
				if offset+2+listLen <= end && listLen > 3 {
					nameType := buf[offset+2]
					nameLen := int(binary.BigEndian.Uint16(buf[offset+3 : offset+5]))
					if nameType == 0 && offset+5+nameLen <= end {
						return string(buf[offset+5 : offset+5+nameLen]), true
					}
				}
			}
			break
		}
		offset += extL
	}
	return "", true
}

func clientHelloHasALPN(buf []byte, want string) bool {
	if len(buf) < 43 || buf[0] != 0x16 || buf[5] != 0x01 {
		return false
	}
	sessionIDLen := int(buf[43])
	if len(buf) < 44+sessionIDLen+2 {
		return false
	}
	cipherLen := int(binary.BigEndian.Uint16(buf[44+sessionIDLen : 44+sessionIDLen+2]))
	offset := 44 + sessionIDLen + 2 + cipherLen
	if len(buf) < offset+1 {
		return false
	}
	compLen := int(buf[offset])
	offset += 1 + compLen
	if len(buf) < offset+2 {
		return false
	}
	extLen := int(binary.BigEndian.Uint16(buf[offset : offset+2]))
	offset += 2
	end := offset + extLen
	if end > len(buf) {
		end = len(buf)
	}

	for offset+4 <= end {
		extType := binary.BigEndian.Uint16(buf[offset : offset+2])
		extL := int(binary.BigEndian.Uint16(buf[offset+2 : offset+4]))
		offset += 4
		extEnd := offset + extL
		if extEnd > end {
			return false
		}
		if extType == 0x0010 {
			if offset+2 > extEnd {
				return false
			}
			listLen := int(binary.BigEndian.Uint16(buf[offset : offset+2]))
			p := offset + 2
			listEnd := p + listLen
			if listEnd > extEnd {
				return false
			}
			for p < listEnd {
				if p+1 > listEnd {
					return false
				}
				nameLen := int(buf[p])
				p++
				if p+nameLen > listEnd {
					return false
				}
				if string(buf[p:p+nameLen]) == want {
					return true
				}
				p += nameLen
			}
			return false
		}
		offset = extEnd
	}
	return false
}

type ProtocolDemux struct {
	listener   net.Listener
	tlsHandler func(net.Conn)
}

func NewProtocolDemux(addr string, tlsHandler func(net.Conn)) (*ProtocolDemux, error) {
	ln, err := net.Listen("tcp", addr)
	if err != nil {
		return nil, err
	}
	return &ProtocolDemux{listener: ln, tlsHandler: tlsHandler}, nil
}

func (dm *ProtocolDemux) Listen() {
	var tempDelay time.Duration
	for {
		conn, err := dm.listener.Accept()
		if err != nil {
			if ne, ok := err.(net.Error); ok && ne.Temporary() {
				if tempDelay == 0 {
					tempDelay = 5 * time.Millisecond
				} else {
					tempDelay *= 2
				}
				if max := 1 * time.Second; tempDelay > max {
					tempDelay = max
				}
				time.Sleep(tempDelay)
				continue
			}
			if strings.Contains(err.Error(), "use of closed") {
				return
			}
			time.Sleep(50 * time.Millisecond)
			continue
		}
		tempDelay = 0
		go dm.demuxConn(conn)
	}
}

func (dm *ProtocolDemux) Close() error {
	return dm.listener.Close()
}

func (dm *ProtocolDemux) demuxConn(conn net.Conn) {
	conn.SetReadDeadline(time.Now().Add(5 * time.Second))
	hdr := make([]byte, 5)
	_, err := io.ReadFull(conn, hdr)
	if err != nil {
		conn.Close()
		return
	}

	if hdr[0] == 0x16 {
		length := int(binary.BigEndian.Uint16(hdr[3:5]))
		if length > 16384 {
			length = 16384
		}
		payload := make([]byte, length)
		_, err = io.ReadFull(conn, payload)
		conn.SetReadDeadline(time.Time{})
		if err != nil {
			conn.Close()
			return
		}

		fullCH := append(hdr, payload...)
		wrappedConn := &PrefixConn{Conn: conn, prefix: fullCH}

		sni, isCH := extractSNI(fullCH)
		configMu.RLock()
		domain := GlobalConfig.Domain
		configMu.RUnlock()

		if domain != "" && isCH && sni != domain {
			fallbackToCamo(wrappedConn, nil)
			return
		}

		dm.tlsHandler(wrappedConn)
	} else {
		buf := make([]byte, 2048)
		n, _ := conn.Read(buf)
		conn.SetReadDeadline(time.Time{})
		full := append(hdr, buf[:n]...)
		wrappedConn := &PrefixConn{Conn: conn, prefix: full}
		fallbackToCamo(wrappedConn, nil)
	}
}

func fallbackToCamo(cn net.Conn, p []byte) {
	configMu.RLock()
	m := GlobalConfig.CamoMode
	t := GlobalConfig.CamoTarget
	configMu.RUnlock()
	if m == "local" {
		cn.Write([]byte("HTTP/1.1 400 Bad Request\r\n\r\n"))
		cn.Close()
		return
	}
	if m == "self" {
		fakeHTML := "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n\r\n<html><head><title>Welcome to nginx!</title></head><body style=\"font-family: sans-serif; padding: 40px;\"><h1>Welcome to nginx!</h1><p>If you see this page, the nginx web server is successfully installed and working.</p></body></html>"
		cn.Write([]byte(fakeHTML))
		cn.Close()
		return
	}
	if t == "" {
		t = "1.1.1.1:80"
	}
	if !strings.Contains(t, ":") {
		t += ":80"
	}
	b, e := net.DialTimeout("tcp", t, 5*time.Second)
	if e != nil {
		cn.Close()
		return
	}
	TuneTCPConn(b)
	if len(p) > 0 {
		b.SetWriteDeadline(time.Now().Add(5 * time.Second))
		b.Write(p)
		b.SetWriteDeadline(time.Time{})
	}
	go func() {
		defer b.Close()
		defer cn.Close()
		io.Copy(b, cn)
	}()
	go func() {
		defer b.Close()
		defer cn.Close()
		io.Copy(cn, b)
	}()
}

type UserConfig struct {
	ID       string `json:"id"`
	Username string `json:"username"`
	Password string `json:"password"`
	Enable   bool   `json:"enable"`
	ExpireAt int64  `json:"expire_at"`
	Limit    uint64 `json:"limit"`
}

type SysConfig struct {
	PanelPort   int          `json:"panel_port"`
	PanelUser   string       `json:"panel_user"`
	PanelPass   string       `json:"panel_pass"`
	ListenPorts string       `json:"listen_ports"`
	Domain      string       `json:"domain"`
	CamoMode    string       `json:"camo_mode"`
	CamoTarget  string       `json:"camo_target"`
	ApiToken    string       `json:"api_token"`
	Users       []UserConfig `json:"users"`
}

type TrafficStat struct {
	Tx atomic.Uint64
	Rx atomic.Uint64
}

func initConfig() {
	GlobalConfig = SysConfig{
		PanelPort:   8080,
		PanelUser:   "admin",
		PanelPass:   "admin",
		ListenPorts: "443,8443",
		CamoMode:    "proxy",
		CamoTarget:  "www.microsoft.com:443",
		ApiToken:    fmt.Sprintf("%x", fastRand()),
		Users:       []UserConfig{{ID: "u-1", Username: "Default", Password: "aether-v52-secret", Enable: true, Limit: 0}},
	}
	if d, e := os.ReadFile(ConfigFile); e == nil {
		json.Unmarshal(d, &GlobalConfig)
	} else {
		saveConfig()
	}
	if GlobalConfig.PanelPort == 0 {
		GlobalConfig.PanelPort = 8080
	}
	if GlobalConfig.ListenPorts == "" {
		GlobalConfig.ListenPorts = "443"
	}
	refreshTokens()
	loadStats()
}

func saveConfig() {
	configMu.RLock()
	d, _ := json.MarshalIndent(GlobalConfig, "", "  ")
	configMu.RUnlock()
	os.WriteFile(ConfigFile, d, 0644)
}

func refreshTokens() {
	configMu.Lock()
	defer configMu.Unlock()
	ActiveUsers = make(map[string]UserConfig)
	for _, u := range GlobalConfig.Users {
		ActiveUsers[getAuthSecret(u.Username, u.Password)] = u
		if _, ok := UserStats.Load(u.ID); !ok {
			UserStats.Store(u.ID, &TrafficStat{})
		}
	}
}

func recordTraffic(uid string, tx, rx uint64) {
	if s, ok := UserStats.Load(uid); ok {
		if tx > 0 {
			s.(*TrafficStat).Tx.Add(tx)
		}
		if rx > 0 {
			s.(*TrafficStat).Rx.Add(rx)
		}
	}
}

func saveStats() {
	s := make(map[string]map[string]uint64)
	UserStats.Range(func(k, v interface{}) bool {
		s[k.(string)] = map[string]uint64{"tx": v.(*TrafficStat).Tx.Load(), "rx": v.(*TrafficStat).Rx.Load()}
		return true
	})
	b, _ := json.Marshal(s)
	os.WriteFile(StatsFile, b, 0644)
}

func loadStats() {
	if b, e := os.ReadFile(StatsFile); e == nil {
		var s map[string]map[string]uint64
		json.Unmarshal(b, &s)
		for k, v := range s {
			if st, ok := UserStats.Load(k); ok {
				st.(*TrafficStat).Tx.Store(v["tx"])
				st.(*TrafficStat).Rx.Store(v["rx"])
			}
		}
	}
}

func getSysStats() (float64, float64) {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return float64(runtime.NumCPU()), float64(m.Sys) / 1024 / 1024
}

func startServerWeb() {
	m := http.NewServeMux()
	m.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/" {
			return
		}
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		w.Write([]byte(serverHTML))
	})
	m.HandleFunc("/api/direct", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		rnd := make([]byte, 16)
		rand.Read(rnd)
		t := fmt.Sprintf("%x", sha256.Sum256(rnd))
		panelTokenMu.Lock()
		globalPanelToken = t
		panelTokenMu.Unlock()
		http.SetCookie(w, &http.Cookie{Name: "a_sess", Value: t, Path: "/", HttpOnly: true, MaxAge: 86400, SameSite: http.SameSiteStrictMode})
		http.Redirect(w, r, "/", 302)
	})
	m.HandleFunc("/api/login", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		bodyBytes, _ := io.ReadAll(r.Body)
		var raw map[string]string
		json.Unmarshal(bodyBytes, &raw)
		reqUser := raw["User"]
		reqPass := raw["Pass"]
		if reqUser == "" {
			reqUser = raw["user"]
		}
		if reqPass == "" {
			reqPass = raw["pass"]
		}
		if reqUser == "" {
			reqUser = raw["username"]
		}
		if reqPass == "" {
			reqPass = raw["password"]
		}
		configMu.RLock()
		v := reqUser == GlobalConfig.PanelUser && reqPass == GlobalConfig.PanelPass
		configMu.RUnlock()
		if v {
			rnd := make([]byte, 16)
			rand.Read(rnd)
			t := fmt.Sprintf("%x", sha256.Sum256(rnd))
			panelTokenMu.Lock()
			globalPanelToken = t
			panelTokenMu.Unlock()
			http.SetCookie(w, &http.Cookie{Name: "a_sess", Value: t, Path: "/", HttpOnly: true, MaxAge: 86400, SameSite: http.SameSiteStrictMode})
			w.Write([]byte(`{"ok":true}`))
		} else {
			time.Sleep(1 * time.Second)
			http.Error(w, `{"error":"Unauthorized"}`, 401)
		}
	})
	mw := func(next http.HandlerFunc) http.HandlerFunc {
		return func(w http.ResponseWriter, r *http.Request) {
			c, e := r.Cookie("a_sess")
			panelTokenMu.RLock()
			t := globalPanelToken
			panelTokenMu.RUnlock()
			if e != nil || c.Value != t || t == "" {
				http.Error(w, `{"error":"Unauthorized"}`, 401)
				return
			}
			next(w, r)
		}
	}
	m.HandleFunc("/api/status", mw(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		var mem runtime.MemStats
		runtime.ReadMemStats(&mem)
		tx, rx := uint64(0), uint64(0)
		UserStats.Range(func(key, value interface{}) bool {
			s := value.(*TrafficStat)
			tx += s.Tx.Load()
			rx += s.Rx.Load()
			return true
		})
		cpu, _ := getSysStats()
		ut := time.Since(sysStartTime).String()
		json.NewEncoder(w).Encode(map[string]interface{}{
			"go":  runtime.NumGoroutine(),
			"mem": formatBytes(mem.Alloc),
			"tx":  formatBytes(tx),
			"rx":  formatBytes(rx),
			"cpu": fmt.Sprintf("%d Cores", int(cpu)),
			"ut":  ut,
		})
	}))
	m.HandleFunc("/api/settings", mw(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		if r.Method == "GET" {
			configMu.RLock()
			json.NewEncoder(w).Encode(GlobalConfig)
			configMu.RUnlock()
		} else if r.Method == "POST" {
			var nc SysConfig
			json.NewDecoder(r.Body).Decode(&nc)
			configMu.Lock()
			nc.Users = GlobalConfig.Users
			GlobalConfig = nc
			configMu.Unlock()
			saveConfig()
			refreshTokens()
			w.Write([]byte(`{"ok":true}`))
		}
	}))
	m.HandleFunc("/api/users", mw(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		if r.Method == "GET" {
			configMu.RLock()
			defer configMu.RUnlock()
			type RU struct {
				UserConfig
				Tx, Rx string
				Exp    string
			}
			var res []RU
			for _, u := range GlobalConfig.Users {
				t, x := uint64(0), uint64(0)
				if s, ok := UserStats.Load(u.ID); ok {
					t = s.(*TrafficStat).Tx.Load()
					x = s.(*TrafficStat).Rx.Load()
				}
				es := "永久"
				if u.ExpireAt > 0 {
					es = time.Unix(u.ExpireAt, 0).Format("2006-01-02")
				}
				res = append(res, RU{u, formatBytes(t), formatBytes(x), es})
			}
			json.NewEncoder(w).Encode(res)
		}
		if r.Method == "POST" {
			var nu UserConfig
			json.NewDecoder(r.Body).Decode(&nu)
			if nu.ID == "" {
				nu.ID = fmt.Sprintf("u-%x", fastRand())
			}
			configMu.Lock()
			GlobalConfig.Users = append(GlobalConfig.Users, nu)
			configMu.Unlock()
			saveConfig()
			refreshTokens()
			w.Write([]byte(`{"ok":true}`))
		}
	}))
	m.HandleFunc("/api/users/edit", mw(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		var nu UserConfig
		json.NewDecoder(r.Body).Decode(&nu)
		configMu.Lock()
		for i, u := range GlobalConfig.Users {
			if u.ID == nu.ID {
				GlobalConfig.Users[i] = nu
				break
			}
		}
		configMu.Unlock()
		saveConfig()
		refreshTokens()
		w.Write([]byte(`{"ok":true}`))
	}))
	m.HandleFunc("/api/users/del", mw(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		var req struct{ ID string }
		json.NewDecoder(r.Body).Decode(&req)
		configMu.Lock()
		for i, u := range GlobalConfig.Users {
			if u.ID == req.ID {
				GlobalConfig.Users = append(GlobalConfig.Users[:i], GlobalConfig.Users[i+1:]...)
				break
			}
		}
		configMu.Unlock()
		saveConfig()
		refreshTokens()
		w.Write([]byte(`{"ok":true}`))
	}))

	airportAuth := func(next http.HandlerFunc) http.HandlerFunc {
		return func(w http.ResponseWriter, r *http.Request) {
			token := r.Header.Get("Authorization")
			configMu.RLock()
			validToken := GlobalConfig.ApiToken
			configMu.RUnlock()
			if token != validToken || validToken == "" {
				http.Error(w, `{"error":"Unauthorized"}`, 401)
				return
			}
			next(w, r)
		}
	}

	m.HandleFunc("/api/v1/airport/sync", airportAuth(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		if r.Method != "POST" {
			return
		}
		var req struct {
			Users []UserConfig `json:"users"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, `{"error":"bad payload"}`, 400)
			return
		}
		configMu.Lock()
		GlobalConfig.Users = req.Users
		configMu.Unlock()
		saveConfig()
		refreshTokens()
		w.Write([]byte(`{"ok":true,"msg":"synced"}`))
	}))

	m.HandleFunc("/api/v1/airport/push", airportAuth(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		if r.Method != "GET" {
			return
		}
		type TrafficRecord struct {
			ID string `json:"id"`
			Tx uint64 `json:"tx"`
			Rx uint64 `json:"rx"`
		}
		var res []TrafficRecord
		UserStats.Range(func(k, v interface{}) bool {
			uid := k.(string)
			stat := v.(*TrafficStat)
			res = append(res, TrafficRecord{
				ID: uid,
				Tx: stat.Tx.Load(),
				Rx: stat.Rx.Load(),
			})
			return true
		})
		json.NewEncoder(w).Encode(map[string]interface{}{
			"ok":   true,
			"data": res,
		})
	}))

	configMu.RLock()
	pt := GlobalConfig.PanelPort
	configMu.RUnlock()
	log.Printf("Aether Server WebUI & API ready at http://0.0.0.0:%d", pt)
	http.ListenAndServe(fmt.Sprintf("0.0.0.0:%d", pt), m)
}

func formatBytes(b uint64) string {
	const u = 1024
	if b < u {
		return fmt.Sprintf("%d B", b)
	}
	d, e := int64(u), 0
	for n := b / u; n >= u; n /= u {
		d *= u
		e++
	}
	if e > 5 {
		e = 5
	}
	return fmt.Sprintf("%.1f %cB", float64(b)/float64(d), "KMGTPE"[e])
}

const serverHTML = `<!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0"><title>SuperYellow Proxy Panel</title><script src="https://cdn.tailwindcss.com"></script><script src="https://unpkg.com/vue@3/dist/vue.global.prod.js"></script><style>body{background-color:#f9fafb;color:#111827;font-family:system-ui,-apple-system,sans-serif} .ring{border-radius:50%;display:flex;align-items:center;justify-content:center;box-shadow:inset 0 0 10px rgba(0,0,0,0.05)} .copy-btn{cursor:pointer;padding:4px 12px;border-radius:6px;font-size:12px;font-weight:700;transition:all 0.2s} .copy-btn:hover{transform:scale(1.05)} .toast{position:fixed;top:20px;right:20px;background:#10b981;color:white;padding:12px 24px;border-radius:10px;font-weight:700;z-index:9999;animation:fadeIn 0.3s} @keyframes fadeIn{from{opacity:0;transform:translateY(-10px)}to{opacity:1;transform:translateY(0)}} .modal-overlay{position:fixed;top:0;left:0;width:100%;height:100%;background:rgba(0,0,0,0.4);display:flex;align-items:center;justify-content:center;z-index:50;backdrop-filter:blur(4px)} .config-box{background:#f8fafc;border:1px solid #e2e8f0;border-radius:8px;padding:12px;font-family:monospace;font-size:12px;white-space:pre-wrap;word-break:break-all;max-height:200px;overflow-y:auto;user-select:text}</style></head><body><div id="app" class="min-h-screen flex"><div v-if="!log" class="m-auto bg-white p-8 rounded-xl shadow-2xl w-96 border border-gray-100"><h2 class="text-2xl font-black mb-8 text-center tracking-tight">SuperYellow<span class="text-yellow-400">/</span><span class="text-gray-400">Admin</span></h2><div class="space-y-4"><input v-model="u" class="w-full p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black transition" placeholder="管理员账号"><input v-model="p" type="password" class="w-full p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black transition" placeholder="管理密码" @keyup.enter="li"><button @click="li" class="w-full bg-black text-white p-3 rounded font-bold hover:bg-gray-800 transition shadow-lg">登录面板</button></div></div><template v-else><div class="w-64 bg-black text-white p-6 flex flex-col shadow-2xl z-10" style="min-width:256px"><div class="text-2xl font-black mb-10 tracking-tighter">SuperYellow<span class="text-yellow-400 text-3xl leading-none">.</span></div><div class="space-y-2 flex-1"><div @click="t='s'" :class="t=='s'?'bg-gray-800 text-white':'text-gray-400 hover:text-white hover:bg-gray-900'" class="p-3 cursor-pointer rounded transition font-medium">系统状态</div><div @click="fu();t='u'" :class="t=='u'?'bg-gray-800 text-white':'text-gray-400 hover:text-white hover:bg-gray-900'" class="p-3 cursor-pointer rounded transition font-medium">客户管理</div><div @click="fc();t='c'" :class="t=='c'?'bg-gray-800 text-white':'text-gray-400 hover:text-white hover:bg-gray-900'" class="p-3 cursor-pointer rounded transition font-medium">节点配置</div></div><div class="text-xs text-gray-600 mt-auto">SuperYellow Proxy v6</div></div><div class="flex-1 p-10 overflow-y-auto" style="width:100%"><div v-if="t=='s'" class="space-y-8"><h2 class="text-3xl font-bold mb-6 tracking-tight">系统状态</h2><div class="bg-white p-8 shadow-sm rounded-2xl border border-gray-100 flex justify-around items-center text-center flex-wrap"><div class="flex flex-col items-center"><div class="w-32 h-32 ring mb-4" style="width:128px;height:128px;background:conic-gradient(#3b82f6 30%, #f3f4f6 0)"><div class="w-28 h-28 bg-white rounded-full flex flex-col items-center justify-center" style="width:112px;height:112px;background-color:white;border-radius:50%;display:flex;flex-direction:column;align-items:center;justify-content:center;"><span class="text-xl font-bold text-gray-800">{{st.cpu}}</span></div></div><div class="text-sm font-bold text-gray-500 tracking-wider">CPU</div></div><div class="flex flex-col items-center"><div class="w-32 h-32 ring mb-4" style="width:128px;height:128px;background:conic-gradient(#10b981 40%, #f3f4f6 0)"><div class="w-28 h-28 bg-white rounded-full flex flex-col items-center justify-center" style="width:112px;height:112px;background-color:white;border-radius:50%;display:flex;flex-direction:column;align-items:center;justify-content:center;"><span class="text-xl font-bold text-gray-800">{{st.mem}}</span></div></div><div class="text-sm font-bold text-gray-500 tracking-wider">内存</div></div><div class="flex flex-col items-center"><div class="w-32 h-32 ring mb-4" style="width:128px;height:128px;background:conic-gradient(#8b5cf6 60%, #f3f4f6 0)"><div class="w-28 h-28 bg-white rounded-full flex flex-col items-center justify-center" style="width:112px;height:112px;background-color:white;border-radius:50%;display:flex;flex-direction:column;align-items:center;justify-content:center;"><span class="text-xl font-bold text-gray-800">{{st.go}}</span></div></div><div class="text-sm font-bold text-gray-500 tracking-wider">协程</div></div></div><div class="grid grid-cols-3 gap-6" style="display:flex;flex-wrap:wrap;gap:1.5rem"><div class="bg-white p-6 shadow-sm rounded-2xl border border-gray-100" style="flex:1;min-width:200px"><div class="text-sm font-bold text-gray-400 mb-1">运行时间</div><div class="text-2xl font-black text-gray-800">{{st.ut}}</div></div><div class="bg-white p-6 shadow-sm rounded-2xl border border-gray-100" style="flex:1;min-width:200px"><div class="text-sm font-bold text-gray-400 mb-1">上行流量</div><div class="text-2xl font-black text-blue-600">{{st.tx}}</div></div><div class="bg-white p-6 shadow-sm rounded-2xl border border-gray-100" style="flex:1;min-width:200px"><div class="text-sm font-bold text-gray-400 mb-1">下行流量</div><div class="text-2xl font-black text-green-600">{{st.rx}}</div></div></div></div><div v-if="t=='u'"><div class="flex justify-between items-center mb-6"><h2 class="text-3xl font-bold tracking-tight">客户管理</h2><div class="flex gap-3"><button @click="rg" class="bg-yellow-400 text-black px-5 py-2 rounded-lg font-bold shadow-lg hover:bg-yellow-300 transition">🎲 随机生成客户</button><button @click="sa=true;isEdit=false;nu={enable:true,LimitGb:0,ExpStr:''}" class="bg-black text-white px-6 py-2 rounded-lg font-bold shadow-lg hover:bg-gray-800 transition">+ 手动添加</button></div></div><div class="bg-white shadow-sm rounded-2xl border border-gray-100 overflow-hidden"><table class="w-full text-left text-sm"><thead class="bg-gray-50 text-gray-500 border-b border-gray-100"><tr><th class="p-4 font-bold">状态</th><th class="p-4 font-bold">用户名</th><th class="p-4 font-bold">密码</th><th class="p-4 font-bold">到期日</th><th class="p-4 font-bold">流量</th><th class="p-4 font-bold">TX / RX</th><th class="p-4 font-bold text-right">操作</th></tr></thead><tbody><tr v-for="u in us" class="border-b border-gray-50 hover:bg-gray-50 transition"><td class="p-4"><span v-if="u.enable" class="px-2 py-1 bg-green-100 text-green-700 rounded text-xs font-bold">活动</span><span v-else class="px-2 py-1 bg-red-100 text-red-700 rounded text-xs font-bold">封禁</span></td><td class="p-4 font-bold text-gray-800">{{u.username}}</td><td class="p-4 font-mono text-gray-500 text-xs">{{u.password}}</td><td class="p-4 text-gray-600">{{u.Exp}}</td><td class="p-4 text-gray-600"><span v-if="u.limit>0">{{(u.limit/1073741824).toFixed(1)}}G</span><span v-else class="text-gray-400">无限</span></td><td class="p-4 font-mono text-gray-500 text-xs">{{u.Tx}} / {{u.Rx}}</td><td class="p-4 text-right"><button @click="cp(u,'vless')" class="copy-btn bg-blue-100 text-blue-700 hover:bg-blue-200 mr-2">📋 VLESS</button><button @click="cp(u,'json')" class="copy-btn bg-purple-100 text-purple-700 hover:bg-purple-200 mr-2">📋 JSON</button><button @click="eu(u)" class="text-blue-500 hover:text-blue-700 font-bold transition mr-3">编辑</button><button @click="du(u.id)" class="text-red-500 hover:text-red-700 font-bold transition">删除</button></td></tr></tbody></table></div></div><div v-if="t=='c'" class="space-y-6 max-w-3xl"><h2 class="text-3xl font-bold tracking-tight mb-6">节点配置</h2><div class="bg-white p-8 shadow-sm rounded-2xl border border-gray-100 space-y-5"><div class="grid grid-cols-2 gap-6" style="display:flex;gap:1.5rem"><div style="flex:1"><label class="block text-sm font-bold text-gray-500 mb-2">面板账号</label><input v-model="cf.panel_user" class="w-full p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black"></div><div style="flex:1"><label class="block text-sm font-bold text-gray-500 mb-2">面板密码</label><input v-model="cf.panel_pass" type="password" class="w-full p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black"></div></div><div><label class="block text-sm font-bold text-gray-500 mb-2">域名 (留空自签证书)</label><input v-model="cf.domain" class="w-full p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black" placeholder="your.domain.com"></div><div class="grid grid-cols-2 gap-6" style="display:flex;gap:1.5rem"><div style="flex:1"><label class="block text-sm font-bold text-gray-500 mb-2">监听端口</label><input v-model="cf.listen_ports" class="w-full p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black"></div><div style="flex:1"><label class="block text-sm font-bold text-gray-500 mb-2">伪装模式</label><select v-model="cf.camo_mode" class="w-full p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black"><option value="proxy">反向代理</option><option value="self">自建欢迎页</option><option value="local">返回400</option></select></div></div><div v-if="cf.camo_mode=='proxy'"><label class="block text-sm font-bold text-gray-500 mb-2">代理目标</label><input v-model="cf.camo_target" class="w-full p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black" placeholder="www.microsoft.com:443"></div><button @click="sc" class="bg-black text-white px-8 py-3 rounded-lg font-bold shadow-lg hover:bg-gray-800 transition w-full mt-4">保存配置</button></div></div></div><div v-if="sa" class="modal-overlay"><div class="bg-white p-8 rounded-2xl w-[420px] shadow-2xl border border-gray-100" style="width:420px"><h3 class="text-2xl font-bold mb-6 tracking-tight">{{isEdit?'编辑客户':'添加客户'}}</h3><div class="space-y-4"><div><label class="block text-sm font-bold text-gray-500 mb-1">用户名</label><input v-model="nu.username" class="w-full p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black"></div><div><label class="block text-sm font-bold text-gray-500 mb-1">密码</label><div class="flex gap-2"><input v-model="nu.password" class="flex-1 p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black font-mono"><button @click="nu.password=gp()" class="px-3 bg-gray-200 rounded hover:bg-gray-300 text-sm font-bold">随机</button></div></div><div><label class="block text-sm font-bold text-gray-500 mb-1">流量配额 (GB，0=无限)</label><input v-model.number="nu.LimitGb" type="number" class="w-full p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black"></div><div><label class="block text-sm font-bold text-gray-500 mb-1">过期时间 (空=永久)</label><input v-model="nu.ExpStr" type="date" class="w-full p-3 bg-gray-50 border border-gray-200 rounded outline-none focus:border-black text-gray-600"></div><div class="flex items-center justify-between mt-4"><span class="font-bold text-gray-700">启用</span><button @click="nu.enable=!nu.enable" :class="nu.enable?'bg-green-500':'bg-gray-300'" class="relative inline-flex h-6 w-11 items-center rounded-full transition-colors" style="width:44px;height:24px;border-radius:12px;border:none;cursor:pointer"><span :class="nu.enable?'translate-x-6':'translate-x-1'" class="inline-block h-4 w-4 transform rounded-full bg-white transition" style="display:inline-block;width:16px;height:16px;background:white;border-radius:50%;transition:transform 0.2s;transform:translateX(nu.enable?24px:4px)"></span></button></div><div class="flex gap-4 mt-8" style="display:flex;gap:1rem"><button @click="au" class="flex-1 bg-black text-white p-3 rounded-lg font-bold shadow hover:bg-gray-800 transition" style="flex:1">确认保存</button><button @click="sa=false" class="flex-1 bg-gray-100 text-gray-600 p-3 rounded-lg font-bold hover:bg-gray-200 transition" style="flex:1;background:#f3f4f6">取消</button></div></div></div></div><div v-if="scv" class="modal-overlay" @click.self="scv=false"><div class="bg-white p-8 rounded-2xl shadow-2xl border border-gray-100" style="width:520px;max-width:90vw"><h3 class="text-xl font-bold mb-4">📋 客户端配置 — {{scu.username}}</h3><div class="space-y-4"><div><div class="flex justify-between items-center mb-1"><span class="text-sm font-bold text-gray-500">VLESS 链接 (App 导入)</span><button @click="doCopy(scvless)" class="copy-btn bg-blue-500 text-white hover:bg-blue-600">复制</button></div><div class="config-box">{{scvless}}</div></div><div><div class="flex justify-between items-center mb-1"><span class="text-sm font-bold text-gray-500">JSON 配置 (软路由导入)</span><button @click="doCopy(scjson)" class="copy-btn bg-purple-500 text-white hover:bg-purple-600">复制</button></div><div class="config-box">{{scjson}}</div></div><button @click="scv=false" class="w-full mt-4 bg-gray-100 text-gray-600 p-3 rounded-lg font-bold hover:bg-gray-200 transition">关闭</button></div></div></div><div v-if="toast" class="toast">{{toast}}</div></template></div><script>Vue.createApp({data(){return{log:false,t:'s',sa:false,isEdit:false,u:'',p:'',st:{cpu:'-',mem:'-',go:'-',ut:'-',tx:'-',rx:'-'},us:[],cf:{},nu:{enable:true,LimitGb:0,ExpStr:''},scv:false,scu:{},scvless:'',scjson:'',toast:''}},methods:{uuidFor(s){let h=[2166136261,2166136261^0x9e3779b9,2166136261^0x85ebca6b,2166136261^0xc2b2ae35];for(let j=0;j<h.length;j++){for(let i=0;i<s.length;i++){h[j]^=s.charCodeAt(i)+j*31;h[j]=Math.imul(h[j],16777619)}}let hex='';for(let k=0;k<h.length;k++){hex+=(h[k]>>>0).toString(16).padStart(8,'0')}hex=hex.slice(0,12)+'4'+hex.slice(13);hex=hex.slice(0,16)+'8'+hex.slice(17);return hex.slice(0,8)+'-'+hex.slice(8,12)+'-'+hex.slice(12,16)+'-'+hex.slice(16,20)+'-'+hex.slice(20,32)},async req(p,m='GET',b){let o={method:m};if(b){o.body=JSON.stringify(b);o.headers={'Content-Type':'application/json'}};try{let r=await fetch('/api/'+p,o);if(r.status===401){this.log=false;throw new Error("401")}return await r.json()}catch(e){throw e}},async li(){try{let r=await this.req('login','POST',{User:this.u,Pass:this.p});if(r&&r.ok){this.log=true;this.fs()}}catch(e){alert('登录失败')}},async fs(){try{let r=await this.req('status');if(r)this.st=r}catch(e){}},async fu(){try{let r=await this.req('users');if(r)this.us=r}catch(e){}},async fc(){try{let r=await this.req('settings');if(r)this.cf=r}catch(e){}},gp(){const c='abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789';let r='';for(let i=0;i<16;i++)r+=c[Math.floor(Math.random()*c.length)];return r},async rg(){let nu={username:'user_'+Math.random().toString(36).slice(2,8),password:this.gp(),enable:true,LimitGb:0,expire_at:0};await this.req('users','POST',nu);this.fu();this.showToast('已生成: '+nu.username)},eu(u){this.nu=JSON.parse(JSON.stringify(u));if(u.expire_at>0){this.nu.ExpStr=new Date(u.expire_at*1000).toISOString().split('T')[0]}else{this.nu.ExpStr=''}this.nu.LimitGb=u.limit/1073741824;this.isEdit=true;this.sa=true},async au(){if(!this.nu.username||!this.nu.password){alert('账号密码必填');return}this.nu.limit=this.nu.LimitGb*1073741824;if(this.nu.ExpStr){this.nu.expire_at=new Date(this.nu.ExpStr).getTime()/1000}else{this.nu.expire_at=0}if(this.isEdit){await this.req('users/edit','POST',this.nu)}else{await this.req('users','POST',this.nu)}this.sa=false;this.fu()},async du(id){if(confirm('确定删除?')){await this.req('users/del','POST',{ID:id});this.fu()}},cp(u,type){this.scu=u;let srv=this.cf.domain||location.hostname;let port=this.cf.listen_ports||'8443';let sni=this.cf.domain||'';if(type==='vless'){this.scvless='vless://'+this.uuidFor(u.username+':'+u.password)+'@'+srv+':'+port+'?encryption=none&security='+(sni?'tls':'none')+(sni?'&sni='+sni:'')+'&type=tcp&headerType=none#'+u.username}else{this.scjson=JSON.stringify({enable:true,active_node_id:'n_main',nodes:[{id:'n_main',name:u.username,server:srv+':'+port,username:u.username,password:u.password,sni:sni}]},null,2)}this.scv=true},doCopy(text){navigator.clipboard.writeText(text).then(()=>{this.showToast('已复制到剪贴板')}).catch(()=>{let ta=document.createElement('textarea');ta.value=text;document.body.appendChild(ta);ta.select();document.execCommand('copy');document.body.removeChild(ta);this.showToast('已复制')})},showToast(msg){this.toast=msg;setTimeout(()=>{this.toast=''},2000)},async sc(){await this.req('settings','POST',this.cf);this.showToast('配置已保存')}},mounted(){this.req('status').then(r=>{if(r){this.log=true;this.fs();this.fc();setInterval(()=>{if(this.t=='s')this.fs();if(this.t=='u')this.fu()},3000)}}).catch(e=>{})}}).mount('#app')</script></body></html>
`

func generateSelfSignedCertificate() (tls.Certificate, error) {
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		return tls.Certificate{}, err
	}
	tmpl := x509.Certificate{
		SerialNumber: big.NewInt(1),
		Subject:      pkix.Name{Organization: []string{"Aether"}},
		NotBefore:    time.Now(),
		NotAfter:     time.Now().Add(8760 * time.Hour),
		KeyUsage:     x509.KeyUsageDigitalSignature | x509.KeyUsageKeyEncipherment,
		ExtKeyUsage:  []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
	}
	certDER, err := x509.CreateCertificate(rand.Reader, &tmpl, &tmpl, &key.PublicKey, key)
	if err != nil {
		return tls.Certificate{}, err
	}
	return tls.Certificate{Certificate: [][]byte{certDER}, PrivateKey: key}, nil
}

func runServer() {
	initConfig()
	go startServerWeb()
	go func() {
		tk := time.NewTicker(60 * time.Second)
		for range tk.C {
			saveStats()
		}
	}()
	var tlsCfg *tls.Config
	fallbackCert, err := generateSelfSignedCertificate()
	if err != nil {
		log.Fatalf("generate self-signed certificate failed: %v", err)
	}
	if GlobalConfig.Domain != "" {
		m := &autocert.Manager{
			Prompt:     autocert.AcceptTOS,
			HostPolicy: autocert.HostWhitelist(GlobalConfig.Domain),
			Cache:      autocert.DirCache("aether_certs"),
		}
		domain := GlobalConfig.Domain
		tlsCfg = m.TLSConfig()
		acmeGetCertificate := tlsCfg.GetCertificate
		tlsCfg.GetCertificate = func(hello *tls.ClientHelloInfo) (*tls.Certificate, error) {
			if hello != nil && strings.EqualFold(hello.ServerName, domain) && acmeGetCertificate != nil {
				return acmeGetCertificate(hello)
			}
			return &fallbackCert, nil
		}
		go func() {
			log.Println("AutoCert ACME Challenge Server running on :80")
			http.ListenAndServe(":80", m.HTTPHandler(nil))
		}()
	} else {
		tlsCfg = &tls.Config{
			Certificates: []tls.Certificate{fallbackCert},
		}
	}

	tlsCfg.MinVersion = tls.VersionTLS13
	tlsCfg.MaxVersion = tls.VersionTLS13
	tlsCfg.NextProtos = []string{AetherALPN}

	configMu.RLock()
	portsStr := GlobalConfig.ListenPorts
	configMu.RUnlock()
	var wg sync.WaitGroup
	var listeners []net.Listener
	var lMu sync.Mutex
	srv := NewServer()
	for _, p := range strings.Split(portsStr, ",") {
		port := strings.TrimSpace(p)
		if port == "" {
			continue
		}
		wg.Add(1)
		go func(listenAddr string) {
			defer wg.Done()
			demux, err := NewProtocolDemux(listenAddr, func(rawConn net.Conn) {
				TuneTCPConn(rawConn)
				tlsConn := tls.Server(rawConn, tlsCfg)
				if err := tlsConn.Handshake(); err != nil {
					tlsConn.Close()
					return
				}
				srv.hs(tlsConn)
			})
			if err != nil {
				log.Printf("[WARN] Port failed %s: %v", listenAddr, err)
				return
			}
			lMu.Lock()
			listeners = append(listeners, demux.listener)
			lMu.Unlock()
			log.Printf("Aether Enterprise Server TCP/UDP Tunnel %s", listenAddr)
			demux.Listen()
		}(":" + port)
	}
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
	<-sigCh
	log.Println("Shutting down...")
	lMu.Lock()
	for _, ln := range listeners {
		ln.Close()
	}
	lMu.Unlock()
	srv.mu.Lock()
	for _, s := range srv.s {
		s.Close()
	}
	srv.mu.Unlock()
	saveStats()
}

func main() {
	runtime.GOMAXPROCS(runtime.NumCPU())
	runServer()
}
