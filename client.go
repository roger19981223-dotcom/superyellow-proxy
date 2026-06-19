//go:build !js

package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
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
	"sort"
	"sync"
	"sync/atomic"
	"time"

	"github.com/klauspost/reedsolomon"
	utls "github.com/refraction-networking/utls"
)

const (
	NumStreams           = 6
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
	ProtocolVersion      = 3
	AetherALPN           = "http/1.1"
	DialTimeout          = 15 * time.Second
	HandshakeTimeout     = 15 * time.Second
	MaxConcurrentConns   = 2000
	ReconnectBaseDelay   = 2 * time.Second
	ReconnectMaxDelay    = 30 * time.Second
	ReconnectStagger     = 500 * time.Millisecond
	SafeMTUPayload       = 1350
	TCPBufferSize        = 2 << 20
	MaxReorderWindow     = 8192
	MaxReassemblerBuf    = 64 << 20
	ReassemblerOutputCap = 2048
	SmallPacketFastLen   = 1200
	ReassemblerGapTTL    = 6 * time.Second
	TunnelWriteTimeout   = 5 * time.Second
	LocalWriteTimeout    = 5 * time.Second
	ProxyIdleTimeout     = 3 * time.Minute
	LocalReadBufferSize  = 5*MSS - 7
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

func getEncoder(ds, ps int) reedsolomon.Encoder {
	if ds <= 0 {
		ds = 4
	}
	if ps <= 0 {
		ps = 1
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
	wcOnce          sync.Once
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
		ds, ps = 4, 1
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
				log.Printf("[WARN] reassembler output queue full: expected=%d buffered=%d, restarting engine", ar.nextExpectedSeq, ar.bufferedBytes)
				ar.Close()
				return
			}
		} else {
			log.Printf("[WARN] FEC seq %d 暂不可恢复，等待后续 parity 或重传窗口", ar.nextExpectedSeq)
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

type AdaptiveDispatcher struct {
	node       NodeConfig
	clientID   uint32
	streams    []*SafeStream
	sMu        sync.RWMutex
	tr         *TCPReassembler
	cr         *TCPReassembler
	pfb        []byte
	cfb        []byte
	fw         atomic.Uint32
	cfw        atomic.Uint32
	conns      sync.Map
	stopCh     chan struct{}
	pacing     *TokenBucket
	currentDS  uint8
	currentPS  uint8
	sdm        sync.RWMutex
	muxWriteMu sync.Mutex
	udpMu      sync.RWMutex
	udpAssoc   *ProxyConn
	udpPeers   sync.Map
	// 重连控制
	lastReconnect    time.Time
	reconnectBackoff time.Duration
	reconnectMu      sync.Mutex
	closed           atomic.Bool
}

func NewAdaptiveDispatcher(n NodeConfig) *AdaptiveDispatcher {
	cid := fastRand()
	ad := &AdaptiveDispatcher{
		node:      n,
		clientID:  cid,
		streams:   make([]*SafeStream, NumStreams),
		tr:        NewTCPReassembler(cid, 30*time.Second),
		cr:        NewTCPReassembler(cid, 30*time.Second),
		stopCh:    make(chan struct{}),
		pacing:    NewTokenBucket(1<<30, 64<<20), // 不在应用层限速，让底层 TCP/BBRv3 自己收敛
		currentDS: 5,
		currentPS: 1,
	}
	go ad.prewarmStreams()
	go ad.monitorHealth()
	go ad.handleReassembler()
	go ad.cleanupProxyConns()
	return ad
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
			st := c.dialStream()
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
	log.Printf("[CLI] 🔴 引擎长时间停滞或数据流严重损坏，执行安全热重启...")
	c.Close()
	go func() {
		time.Sleep(500 * time.Millisecond)
		applyEngine()
	}()
}

func (c *AdaptiveDispatcher) Close() {
	if c.closed.Swap(true) {
		return // 已经关闭，防止 double-close panic
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
	c.tr.Close()
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
	return &utls.Config{
		ServerName:         sni,
		InsecureSkipVerify: true,
		NextProtos:         []string{AetherALPN},
	}
}

func (c *AdaptiveDispatcher) dialStream() *SafeStream {
	rc, err := net.DialTimeout("tcp", c.node.Server, DialTimeout)
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
	pl := generateSmartPadding(HeaderSize + AuthTokenSize)

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
		if ds > 0 && ps > 0 && h.Flags&(ControlFrameFlag|FastLaneFlag|PingFlag|PongFlag|AuthFlag) == 0 {
			c.sdm.Lock()
			c.currentDS = ds
			c.currentPS = ps
			c.sdm.Unlock()
		}
		ss := int((h.ChunkSize + uint32(ds) - 1) / uint32(ds))
		tl := uint32(ss) + uint32(h.PaddingLen)

		var bp *[]byte
		if tl > 0 {
			bp = GetShardPtr()
			if _, e := io.ReadFull(st.conn, (*bp)[HeaderSize:HeaderSize+int(tl)]); e != nil {
				PutShardPtr(bp)
				st.Close()
				return
			}
		}

		if h.Flags&PingFlag != 0 {
			pl := generateSmartPadding(HeaderSize)
			p := &PacketHeader{Magic: Magic, ClientID: c.clientID, Flags: PongFlag, Timestamp: h.Timestamp, PaddingLen: pl}
			c.sdm.RLock()
			p.SetFEC(c.currentDS, c.currentPS)
			c.sdm.RUnlock()

			bo := make([]byte, HeaderSize+int(pl))
			p.EncodeTo(bo[:HeaderSize])

			if _, err := st.Write(bo); err != nil {
				st.Close()
			}

			if bp != nil {
				PutShardPtr(bp)
			}
			continue
		}
		if h.Flags&PongFlag != 0 {
			m := time.Now().UnixMilli() - int64(h.Timestamp)
			if m > 0 && m < 5000 {
				st.UpdateRTT(m)
			}
			if bp != nil {
				PutShardPtr(bp)
			}
			select {
			case st.pingCh <- struct{}{}:
			default:
			}
			continue
		}
		if bp != nil {
			*bp = (*bp)[:HeaderSize+ss]
			if h.Flags&ControlFrameFlag != 0 {
				c.cr.AddShard(h.SeqNo, h.ShardIdx, h.ChunkSize, bp, ds, ps)
			} else {
				c.tr.AddShard(h.SeqNo, h.ShardIdx, h.ChunkSize, bp, ds, ps)
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
						newSt := c.dialStream()
						if newSt != nil {
							c.sMu.Lock()
							c.streams[idx] = newSt
							c.sMu.Unlock()
							atomic.AddInt32(&activeCount, 1)
						}
					} else {
						atomic.AddInt32(&activeCount, 1)
						atomic.AddInt64(&avgRTT, st.srtt.Load())

						pl := generateSmartPadding(HeaderSize)
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

			if activeCount > 0 {
				avgRTT /= int64(activeCount)
				// 有存活流，重置退避
				c.reconnectMu.Lock()
				c.reconnectBackoff = 0
				c.reconnectMu.Unlock()
			} else {
				// 全部流死亡，触发退避重连
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

				log.Printf("[CLI] ⚠️ 全部 %d 条流断开，%v 后开始逐条重连...", NumStreams, delay)
				time.Sleep(delay)

				// 逐条重连，间隔 500ms，避免同时拨号冲击服务端
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
					newSt := c.dialStream()
					if newSt != nil {
						c.sMu.Lock()
						c.streams[i] = newSt
						c.sMu.Unlock()
						log.Printf("[CLI] ✅ 流 %d 重连成功", i)
					} else {
						log.Printf("[CLI] ❌ 流 %d 重连失败，将在下次周期重试", i)
					}
					time.Sleep(ReconnectStagger)
				}
				continue
			}

			lossRate := float64(lossCount) / float64(NumStreams)
			c.sdm.Lock()
			switch {
			case activeCount >= 6 && lossRate < 0.08:
				c.currentDS, c.currentPS = 5, 1
			case activeCount >= 5 && lossRate > 0.18:
				c.currentDS, c.currentPS = 4, 2
			case activeCount >= 5:
				c.currentDS, c.currentPS = 4, 1
			case activeCount >= 4:
				c.currentDS, c.currentPS = 3, 1
			default:
				c.currentDS, c.currentPS = 2, 1
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
	fb := framePool.Get().([]byte)
	fb = fb[:7]
	fb[0] = 0x03
	binary.BigEndian.PutUint32(fb[1:5], connID)
	binary.BigEndian.PutUint16(fb[5:7], 0)
	c.SendChunk(fb)
	framePool.Put(fb[:cap(fb)])
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

func (c *AdaptiveDispatcher) handleReassembler() {
	for {
		select {
		case <-c.stopCh:
			return
		case <-c.tr.stopCh:
			c.reboot()
			return
		case <-c.cr.stopCh:
			c.reboot()
			return
		case d := <-c.tr.Output():
			if !c.handleReassembledPayload(&c.pfb, d) {
				return
			}
		case d := <-c.cr.Output():
			if !c.handleReassembledPayload(&c.cfb, d) {
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
	return c.sendChunk(data, isClientControlFrame(data))
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

func chooseClientDataFEC(active, curDS, curPS, remaining int) (int, int) {
	if remaining <= SmallPacketFastLen {
		return 1, 2
	}
	switch {
	case active >= 6:
		if curDS <= 1 || curPS <= 0 {
			return 5, 1
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

	o := 0
	var noStreamSince time.Time
	for o < len(data) {
		if c.closed.Load() {
			return false
		}
		c.sMu.RLock()
		var stats []streamStat
		for _, st := range c.streams {
			if st != nil && !st.IsClosed() {
				stats = append(stats, streamStat{st, st.srtt.Load()})
			}
		}
		c.sMu.RUnlock()
		if len(stats) == 0 {
			if noStreamSince.IsZero() {
				noStreamSince = time.Now()
			}
			if time.Since(noStreamSince) > 10*time.Second {
				log.Printf("[CLI] no active tunnel streams; dropping %d bytes after wait", len(data)-o)
				return false
			}
			select {
			case <-c.stopCh:
				return false
			case <-time.After(20 * time.Millisecond):
			}
			continue
		}
		noStreamSince = time.Time{}
		sort.Slice(stats, func(i, j int) bool { return stats[i].rtt < stats[j].rtt })

		var ds, ps int
		var sq uint32
		var fastLane bool
		if control {
			ds, ps = 1, 2
			sq = c.cfw.Add(1) - 1
		} else {
			c.sdm.RLock()
			ds, ps = int(c.currentDS), int(c.currentPS)
			c.sdm.RUnlock()
			ds, ps = chooseClientDataFEC(len(stats), ds, ps, len(data)-o)
			sq = c.fw.Add(1) - 1
			fastLane = ds == 1 && ps >= 2
		}

		enc := getEncoder(ds, ps)
		if enc == nil {
			return false
		}
		total := ds + ps
		e := o + ds*MSS
		if e > len(data) {
			e = len(data)
		}
		ch := data[o:e]
		cs := uint32(len(ch))
		ss := int((cs + uint32(ds) - 1) / uint32(ds))
		if ss > MSS {
			ss = MSS
		}

		sh := make([][]byte, total)
		buffers := make([][]byte, total)

		for i := 0; i < total; i++ {
			maxPktLen := HeaderSize + ss + SafeMTUPayload
			buf := make([]byte, maxPktLen)
			buffers[i] = buf
			sh[i] = buf[HeaderSize : HeaderSize+ss]

			if i < ds {
				st, en := i*ss, i*ss+ss
				if st < int(cs) {
					if en > int(cs) {
						en = int(cs)
					}
					copy(sh[i], ch[st:en])
				}
			}
		}

		if err := enc.Encode(sh); err != nil {
			return false
		}

		ts := uint32(time.Now().UnixMilli() & 0xFFFFFFFF)
		success := 0
		for i := 0; i < total; i++ {
			st := stats[i%len(stats)].st
			actualChunkSize := HeaderSize + len(sh[i])
			pl := generateSmartPadding(actualChunkSize)

			h := &PacketHeader{Magic: Magic, ClientID: c.clientID, SeqNo: sq, ShardIdx: uint16(i), PaddingLen: pl, ChunkSize: cs, Timestamp: ts}
			if control {
				h.Flags |= ControlFrameFlag
			} else if fastLane {
				h.Flags |= FastLaneFlag
			}
			h.SetFEC(uint8(ds), uint8(ps))

			buf := buffers[i]
			h.EncodeTo(buf[:HeaderSize])

			pe := HeaderSize + len(sh[i])
			for j := pe; j < pe+int(pl); j++ {
				buf[j] = 0
			}

			pkt := buf[:pe+int(pl)]
			if _, err := st.Write(pkt); err != nil {
				st.Close()
			} else {
				success++
			}
		}
		if success < ds {
			log.Printf("[CLI] tunnel shard write quorum failed: seq=%d success=%d required=%d", sq, success, ds)
			return false
		}
		o = e
	}
	return true
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
			framePool.Put(fb[:cap(fb)])
			return
		}
		pc.touch()
		framePool.Put(fb[:cap(fb)])

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
	ID       string `json:"id"`
	Name     string `json:"name"`
	Server   string `json:"server"`
	Username string `json:"username"`
	Password string `json:"password"`
	SNI      string `json:"sni"`
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
    <div><button id="toggleBtn" class="btn btn-gn" onclick="toggle()">&#9654; 启动引擎</button></div>
  </div>

  <div class="sb">
    <div class="st"><div class="lb">引擎状态</div><div class="vl" id="s1">-</div></div>
    <div class="st"><div class="lb">节点数量</div><div class="vl ac" id="s2">-</div></div>
    <div class="st"><div class="lb">当前节点</div><div class="vl" id="s3" style="font-size:15px">-</div></div>
    <div class="st"><div class="lb">本地端口</div><div class="vl" style="font-size:15px;font-family:monospace">:11080</div></div>
  </div>

  <div class="cr">
    <div class="tb">
      <h2>&#128225; 节点列表</h2>
      <div class="cg">
        <button class="btn btn-g btn-sm" onclick="copyLocalProxy()">&#128279; 复制接入</button>
        <button class="btn btn-g btn-sm" onclick="copyJson()">&#128203; 复制配置</button>
        <button class="btn btn-p btn-sm" onclick="openModal(null)">+ 添加节点</button>
      </div>
    </div>
    <div class="nl" id="nodeList"></div>
  </div>

  <div class="cr">
    <h2>&#128214; 使用说明</h2>
    <div style="color:var(--text2);font-size:14px;line-height:1.8">
      <p>1. 点击「+ 添加节点」填入你的 SuperYellow 服务器信息</p>
      <p>2. 选中节点后，前往 <strong style="color:var(--text)">PassWall → 节点列表</strong> 选择「SuperYellow」</p>
      <p>3. 将 PassWall 的 TCP 模式设为「使用列表外代理」即可</p>
      <p style="margin-top:8px;color:var(--accent)">&#128161; 服务器需要先在 Web 面板注册用户才能连接</p>
    </div>
  </div>
</div>

<!-- Modal -->
<div class="mm" id="modal" onclick="if(event.target===this)closeModal()">
  <div class="md">
    <h3 id="modalTitle">添加节点</h3>
    <div class="fg"><label>节点名称</label><input id="fName" placeholder="例：我的服务器"></div>
    <div class="fg"><label>服务器地址 (IP:端口)</label><input id="fServer" placeholder="例：1.2.3.4:8443" style="font-family:monospace"></div>
    <div class="fr">
      <div class="fg"><label>用户名</label><input id="fUser" placeholder="Default"></div>
      <div class="fg"><label>密码</label><input id="fPass" type="password" placeholder="鉴权密钥"></div>
    </div>
    <div class="fg"><label>SNI (伪装域名)</label><input id="fSni" placeholder="例：chaofanbox.top" style="font-family:monospace"></div>
    <div class="ma">
      <button class="btn btn-g" onclick="closeModal()">取消</button>
      <button class="btn btn-p" onclick="saveNode()">保存</button>
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

  document.getElementById('s1').innerHTML=running?'<span class="on">运行中</span>':'<span class="off">已停止</span>';
  document.getElementById('s2').textContent=conf.nodes.length;
  var an=conf.nodes.find(function(n){return n.id===conf.active_node_id});
  document.getElementById('s3').textContent=an?an.name:'未选择';

  var btn=document.getElementById('toggleBtn');
  if(running){btn.className='btn btn-r';btn.innerHTML='&#9632; 停止引擎'}
  else{btn.className='btn btn-gn';btn.innerHTML='&#9654; 启动引擎'}

  var list=document.getElementById('nodeList');
  if(conf.nodes.length===0){
    list.innerHTML='<div class="emp"><div style="font-size:32px;margin-bottom:8px">&#128225;</div>还没有配置节点，点击右上角「+ 添加节点」开始</div>';
    return;
  }
  var h='';
  conf.nodes.forEach(function(n){
    var act=n.id===conf.active_node_id;
    h+='<div class="nd'+(act?' act':'')+'" onclick="selectNode(\''+n.id+'\')">';
    h+='<div><div class="nm">'+esc(n.name)+(act?'<span class="badge">当前</span>':'')+'</div>';
    h+='<div class="ad">'+esc(n.server)+' &middot; '+esc(n.username)+'</div></div>';
    h+='<div class="acts">';
    h+='<button class="btn btn-g btn-sm" onclick="event.stopPropagation();openModal(\''+n.id+'\')">&#9998; 编辑</button>';
    h+='<button class="btn btn-d btn-sm" onclick="event.stopPropagation();delNode(\''+n.id+'\')">&#128465; 删除</button>';
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
    document.getElementById('modalTitle').textContent='编辑节点';
    document.getElementById('fName').value=n.name;
    document.getElementById('fServer').value=n.server;
    document.getElementById('fUser').value=n.username;
    document.getElementById('fPass').value=n.password;
    document.getElementById('fSni').value=n.sni||'';
  }else{
    document.getElementById('modalTitle').textContent='添加节点';
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
  if(!name||!server){alert('名称和服务器地址不能为空');return}
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
  closeModal();save();showToast('已保存');
}

function delNode(id){
  var n=conf.nodes.find(function(x){return x.id===id});
  if(!confirm('确定删除「'+(n?n.name:'')+'」？'))return;
  conf.nodes=conf.nodes.filter(function(x){return x.id!==id});
  if(conf.active_node_id===id)conf.active_node_id=conf.nodes.length?conf.nodes[0].id:'';
  save();showToast('已删除');
}

function copyLocalProxy(){
  copyText('SOCKS5 / HTTP CONNECT\nHost: 127.0.0.1\nPort: 11080\nAuth: none\nPassWall node type: Socks or HTTP');
  showToast('本地接入信息已复制');
}

function copyJson(){
  copyText(JSON.stringify(conf,null,2));showToast('配置 JSON 已复制');
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
