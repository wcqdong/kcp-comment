//=====================================================================
//
// KCP - A Better ARQ Protocol Implementation
// skywind3000 (at) gmail.com, 2010-2011
//  
// Features:
// + Average RTT reduce 30% - 40% vs traditional ARQ like tcp.
// + Maximum RTT reduce three times vs tcp.
// + Lightweight, distributed as a single source file.
//
//=====================================================================
#include "ikcp.h"

#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdio.h>



//=====================================================================
// KCP BASIC
//=====================================================================
const IUINT32 IKCP_RTO_NDL = 30;		// no delay min rto
const IUINT32 IKCP_RTO_MIN = 100;		// normal min rto
const IUINT32 IKCP_RTO_DEF = 200;
const IUINT32 IKCP_RTO_MAX = 60000;
const IUINT32 IKCP_CMD_PUSH = 81;		// cmd: push data
const IUINT32 IKCP_CMD_ACK  = 82;		// cmd: ack
const IUINT32 IKCP_CMD_WASK = 83;		// cmd: window probe (ask)
const IUINT32 IKCP_CMD_WINS = 84;		// cmd: window size (tell)
const IUINT32 IKCP_ASK_SEND = 1;		// need to send IKCP_CMD_WASK
const IUINT32 IKCP_ASK_TELL = 2;		// need to send IKCP_CMD_WINS
const IUINT32 IKCP_WND_SND = 32;
const IUINT32 IKCP_WND_RCV = 128;       // must >= max fragment size
const IUINT32 IKCP_MTU_DEF = 1400;
const IUINT32 IKCP_ACK_FAST	= 3;
const IUINT32 IKCP_INTERVAL	= 100;
const IUINT32 IKCP_OVERHEAD = 24;       // kcp包头长度
const IUINT32 IKCP_DEADLINK = 20;
const IUINT32 IKCP_THRESH_INIT = 2;
const IUINT32 IKCP_THRESH_MIN = 2;
const IUINT32 IKCP_PROBE_INIT = 7000;		// 7 secs to probe window size
const IUINT32 IKCP_PROBE_LIMIT = 120000;	// up to 120 secs to probe window
const IUINT32 IKCP_FASTACK_LIMIT = 5;		// max times to trigger fastack


//---------------------------------------------------------------------
// encode / decode
//---------------------------------------------------------------------

/* encode 8 bits unsigned int */
static inline char *ikcp_encode8u(char *p, unsigned char c)
{
    *(unsigned char*)p++ = c;
    return p;
}

/* decode 8 bits unsigned int */
static inline const char *ikcp_decode8u(const char *p, unsigned char *c)
{
    *c = *(unsigned char*)p++;
    return p;
}

/* encode 16 bits unsigned int (lsb) */
static inline char *ikcp_encode16u(char *p, unsigned short w)
{
#if IWORDS_BIG_ENDIAN || IWORDS_MUST_ALIGN
    *(unsigned char*)(p + 0) = (w & 255);
	*(unsigned char*)(p + 1) = (w >> 8);
#else
    memcpy(p, &w, 2);
#endif
    p += 2;
    return p;
}

/* decode 16 bits unsigned int (lsb) */
static inline const char *ikcp_decode16u(const char *p, unsigned short *w)
{
#if IWORDS_BIG_ENDIAN || IWORDS_MUST_ALIGN
    *w = *(const unsigned char*)(p + 1);
	*w = *(const unsigned char*)(p + 0) + (*w << 8);
#else
    memcpy(w, p, 2);
#endif
    p += 2;
    return p;
}

/* encode 32 bits unsigned int (lsb) */
static inline char *ikcp_encode32u(char *p, IUINT32 l)
{
#if IWORDS_BIG_ENDIAN || IWORDS_MUST_ALIGN
    *(unsigned char*)(p + 0) = (unsigned char)((l >>  0) & 0xff);
	*(unsigned char*)(p + 1) = (unsigned char)((l >>  8) & 0xff);
	*(unsigned char*)(p + 2) = (unsigned char)((l >> 16) & 0xff);
	*(unsigned char*)(p + 3) = (unsigned char)((l >> 24) & 0xff);
#else
    memcpy(p, &l, 4);
#endif
    p += 4;
    return p;
}

/* decode 32 bits unsigned int (lsb) */
static inline const char *ikcp_decode32u(const char *p, IUINT32 *l)
{
#if IWORDS_BIG_ENDIAN || IWORDS_MUST_ALIGN
    *l = *(const unsigned char*)(p + 3);
	*l = *(const unsigned char*)(p + 2) + (*l << 8);
	*l = *(const unsigned char*)(p + 1) + (*l << 8);
	*l = *(const unsigned char*)(p + 0) + (*l << 8);
#else
    memcpy(l, p, 4);
#endif
    p += 4;
    return p;
}

static inline IUINT32 _imin_(IUINT32 a, IUINT32 b) {
return a <= b ? a : b;
}

static inline IUINT32 _imax_(IUINT32 a, IUINT32 b) {
return a >= b ? a : b;
}

static inline IUINT32 _ibound_(IUINT32 lower, IUINT32 middle, IUINT32 upper)
{
return _imin_(_imax_(lower, middle), upper);
}

static inline long _itimediff(IUINT32 later, IUINT32 earlier)
{
    return ((IINT32)(later - earlier));
}

//---------------------------------------------------------------------
// manage segment
//---------------------------------------------------------------------
typedef struct IKCPSEG IKCPSEG;

static void* (*ikcp_malloc_hook)(size_t) = NULL;
static void (*ikcp_free_hook)(void *) = NULL;

// internal malloc
static void* ikcp_malloc(size_t size) {
    if (ikcp_malloc_hook)
        return ikcp_malloc_hook(size);
    return malloc(size);
}

// internal free
static void ikcp_free(void *ptr) {
    if (ikcp_free_hook) {
        ikcp_free_hook(ptr);
    }	else {
        free(ptr);
    }
}

// redefine allocator
void ikcp_allocator(void* (*new_malloc)(size_t), void (*new_free)(void*))
{
    ikcp_malloc_hook = new_malloc;
    ikcp_free_hook = new_free;
}

// allocate a new kcp segment
static IKCPSEG* ikcp_segment_new(ikcpcb *kcp, int size)
{
    return (IKCPSEG*)ikcp_malloc(sizeof(IKCPSEG) + size);
}

// delete a segment
static void ikcp_segment_delete(ikcpcb *kcp, IKCPSEG *seg)
{
    ikcp_free(seg);
}

// write log
void ikcp_log(ikcpcb *kcp, int mask, const char *fmt, ...)
{
    char buffer[1024];
    va_list argptr;
    if ((mask & kcp->logmask) == 0 || kcp->writelog == 0) return;
    va_start(argptr, fmt);
    vsprintf(buffer, fmt, argptr);
    va_end(argptr);
    kcp->writelog(buffer, kcp, kcp->user);
}

// check log mask
static int ikcp_canlog(const ikcpcb *kcp, int mask)
{
    if ((mask & kcp->logmask) == 0 || kcp->writelog == NULL) return 0;
    return 1;
}

// output segment
static int ikcp_output(ikcpcb *kcp, const void *data, int size)
{
    assert(kcp);
    assert(kcp->output);
    if (ikcp_canlog(kcp, IKCP_LOG_OUTPUT)) {
        ikcp_log(kcp, IKCP_LOG_OUTPUT, "[RO] %ld bytes", (long)size);
    }
    if (size == 0) return 0;
    return kcp->output((const char*)data, size, kcp, kcp->user);
}

// output queue
void ikcp_qprint(const char *name, const struct IQUEUEHEAD *head)
{
#if 0
    const struct IQUEUEHEAD *p;
	printf("<%s>: [", name);
	for (p = head->next; p != head; p = p->next) {
		const IKCPSEG *seg = iqueue_entry(p, const IKCPSEG, node);
		printf("(%lu %d)", (unsigned long)seg->sn, (int)(seg->ts % 10000));
		if (p->next != head) printf(",");
	}
	printf("]\n");
#endif
}


//---------------------------------------------------------------------
// create a new kcpcb
//---------------------------------------------------------------------
ikcpcb* ikcp_create(IUINT32 conv, void *user)
{
    ikcpcb *kcp = (ikcpcb*)ikcp_malloc(sizeof(struct IKCPCB));
    if (kcp == NULL) return NULL;
    kcp->conv = conv;
    kcp->user = user;
    kcp->snd_una = 0;
    kcp->snd_nxt = 0;
    kcp->rcv_nxt = 0;
    kcp->ts_recent = 0;
    kcp->ts_lastack = 0;
    kcp->ts_probe = 0;
    kcp->probe_wait = 0;
    kcp->snd_wnd = IKCP_WND_SND;
    kcp->rcv_wnd = IKCP_WND_RCV;
    kcp->rmt_wnd = IKCP_WND_RCV;
    kcp->cwnd = 0;
    kcp->incr = 0;
    kcp->probe = 0;
    kcp->mtu = IKCP_MTU_DEF;
    kcp->mss = kcp->mtu - IKCP_OVERHEAD;
    kcp->stream = 0;

    kcp->buffer = (char*)ikcp_malloc((kcp->mtu + IKCP_OVERHEAD) * 3);
    if (kcp->buffer == NULL) {
        ikcp_free(kcp);
        return NULL;
    }

    iqueue_init(&kcp->snd_queue);
    iqueue_init(&kcp->rcv_queue);
    iqueue_init(&kcp->snd_buf);
    iqueue_init(&kcp->rcv_buf);
    kcp->nrcv_buf = 0;
    kcp->nsnd_buf = 0;
    kcp->nrcv_que = 0;
    kcp->nsnd_que = 0;
    kcp->state = 0;
    kcp->acklist = NULL;
    kcp->ackblock = 0;
    kcp->ackcount = 0;
    kcp->rx_srtt = 0;
    kcp->rx_rttval = 0;
    kcp->rx_rto = IKCP_RTO_DEF;
    kcp->rx_minrto = IKCP_RTO_MIN;
    kcp->current = 0;
    kcp->interval = IKCP_INTERVAL;
    kcp->ts_flush = IKCP_INTERVAL;
    kcp->nodelay = 0;
    kcp->updated = 0;
    kcp->logmask = 0;
    kcp->ssthresh = IKCP_THRESH_INIT;
    kcp->fastresend = 0;
    kcp->fastlimit = IKCP_FASTACK_LIMIT;
    kcp->nocwnd = 0;
    kcp->xmit = 0;
    kcp->dead_link = IKCP_DEADLINK;
    kcp->output = NULL;
    kcp->writelog = NULL;

    return kcp;
}


//---------------------------------------------------------------------
// release a new kcpcb
//---------------------------------------------------------------------
void ikcp_release(ikcpcb *kcp)
{
    assert(kcp);
    if (kcp) {
        IKCPSEG *seg;
        while (!iqueue_is_empty(&kcp->snd_buf)) {
            seg = iqueue_entry(kcp->snd_buf.next, IKCPSEG, node);
            iqueue_del(&seg->node);
            ikcp_segment_delete(kcp, seg);
        }
        while (!iqueue_is_empty(&kcp->rcv_buf)) {
            seg = iqueue_entry(kcp->rcv_buf.next, IKCPSEG, node);
            iqueue_del(&seg->node);
            ikcp_segment_delete(kcp, seg);
        }
        while (!iqueue_is_empty(&kcp->snd_queue)) {
            seg = iqueue_entry(kcp->snd_queue.next, IKCPSEG, node);
            iqueue_del(&seg->node);
            ikcp_segment_delete(kcp, seg);
        }
        while (!iqueue_is_empty(&kcp->rcv_queue)) {
            seg = iqueue_entry(kcp->rcv_queue.next, IKCPSEG, node);
            iqueue_del(&seg->node);
            ikcp_segment_delete(kcp, seg);
        }
        if (kcp->buffer) {
            ikcp_free(kcp->buffer);
        }
        if (kcp->acklist) {
            ikcp_free(kcp->acklist);
        }

        kcp->nrcv_buf = 0;
        kcp->nsnd_buf = 0;
        kcp->nrcv_que = 0;
        kcp->nsnd_que = 0;
        kcp->ackcount = 0;
        kcp->buffer = NULL;
        kcp->acklist = NULL;
        ikcp_free(kcp);
    }
}


//---------------------------------------------------------------------
// set output callback, which will be invoked by kcp
//---------------------------------------------------------------------
void ikcp_setoutput(ikcpcb *kcp, int (*output)(const char *buf, int len,
                                               ikcpcb *kcp, void *user))
{
    kcp->output = output;
}


//---------------------------------------------------------------------
// user/upper level recv: returns size, returns below zero for EAGAIN
//---------------------------------------------------------------------
int ikcp_recv(ikcpcb *kcp, char *buffer, int len)
{
    struct IQUEUEHEAD *p;
    int ispeek = (len < 0)? 1 : 0;
    int peeksize;
    int recover = 0;
    IKCPSEG *seg;
    assert(kcp);

    if (iqueue_is_empty(&kcp->rcv_queue))
        return -1;

    if (len < 0) len = -len;

    peeksize = ikcp_peeksize(kcp);

    if (peeksize < 0)
        return -2;

    if (peeksize > len)
        return -3;

    // 条件成立，说明此帧有大量包从rcv_buf转移到rcv_que，rcv_buf减少则可用窗口变大
    // 为什么说”大量“包呢，而不是rcv_buf全部包
    // 如果此帧开始的rcv_que里长度为0，nrcv_que最大不超过rcv_wnd，因为rcv_buf最大为rcv_wnd，即使全部转移到rcv_que，nrcv_que==rcv_wnd
    // 但实际情况可能此帧开始时rcv_que中有残留（上一帧没peek出完整包），所以可能nrcv_que>rcv_wnd
    // 不管哪种情况，只要kcp->nrcv_que >= kcp->rcv_wnd，意味着有此帧收到的很多包都转移到了rcv_que，可用窗口变大
    if (kcp->nrcv_que >= kcp->rcv_wnd)
        // 可用窗口变大
        recover = 1;

    // merge fragment
    // 合包
    for (len = 0, p = kcp->rcv_queue.next; p != &kcp->rcv_queue; ) {
        int fragment;
        seg = iqueue_entry(p, IKCPSEG, node);
        p = p->next;

        if (buffer) {
            memcpy(buffer, seg->data, seg->len);
            buffer += seg->len;
        }

        len += seg->len;
        fragment = seg->frg;

        if (ikcp_canlog(kcp, IKCP_LOG_RECV)) {
            ikcp_log(kcp, IKCP_LOG_RECV, "recv sn=%lu", (unsigned long)seg->sn);
        }
        // 删除
        if (ispeek == 0) {
            iqueue_del(&seg->node);
            ikcp_segment_delete(kcp, seg);
            kcp->nrcv_que--;
        }

        if (fragment == 0)
            break;
    }

    assert(len == peeksize);

    // move available data from rcv_buf -> rcv_queue
    // 这里为什么有又执行了一遍，input的时[4]已经做过了相同的操作
    while (! iqueue_is_empty(&kcp->rcv_buf)) {
        seg = iqueue_entry(kcp->rcv_buf.next, IKCPSEG, node);
        if (seg->sn == kcp->rcv_nxt && kcp->nrcv_que < kcp->rcv_wnd) {
            iqueue_del(&seg->node);
            kcp->nrcv_buf--;
            iqueue_add_tail(&seg->node, &kcp->rcv_queue);
            kcp->nrcv_que++;
            kcp->rcv_nxt++;
        }	else {
            break;
        }
    }

    // fast recover
    // 根据上面recover变量的判断，kcp->nrcv_que < kcp->rcv_wnd目的是想只触发一次，虽然可能触发多次，因为nrcv_que比rcv_wnd多n个
    if (kcp->nrcv_que < kcp->rcv_wnd && recover) {
        // ready to send back IKCP_CMD_WINS in ikcp_flush
        // tell remote my window size
        // flush的时候发送个cmd=IKCP_CMD_WINS的包
        // TODO 当flush的时候，每个消息都包含wnd消息，不用特意发一个[7]
        kcp->probe |= IKCP_ASK_TELL;
    }

    return len;
}


//---------------------------------------------------------------------
// peek data size
// 计算一个消息包的长度
//---------------------------------------------------------------------
int ikcp_peeksize(const ikcpcb *kcp)
{
    struct IQUEUEHEAD *p;
    IKCPSEG *seg;
    int length = 0;

    assert(kcp);

    if (iqueue_is_empty(&kcp->rcv_queue)) return -1;

    seg = iqueue_entry(kcp->rcv_queue.next, IKCPSEG, node);
    // 消息包只包含一个seg
    if (seg->frg == 0) return seg->len;

    // 消息包还没接收完整。消息包的大小为(seg->frg + 1)个seg，但nrcv_que队列不足(seg->frg + 1)个
    if (kcp->nrcv_que < seg->frg + 1) return -1;

    for (p = kcp->rcv_queue.next; p != &kcp->rcv_queue; p = p->next) {
        seg = iqueue_entry(p, IKCPSEG, node);
        length += seg->len;
        // 消息包中最后一个seg包的frg是0，因为[6]
        if (seg->frg == 0) break;
    }

    return length;
}


//---------------------------------------------------------------------
// user/upper level send, returns below zero for error
//---------------------------------------------------------------------
int ikcp_send(ikcpcb *kcp, const char *buffer, int len)
{
    IKCPSEG *seg;
    int count, i;

    assert(kcp->mss > 0);
    if (len < 0) return -1;

    // append to previous segment in streaming mode (if possible)
    if (kcp->stream != 0) {
        if (!iqueue_is_empty(&kcp->snd_queue)) {
            IKCPSEG *old = iqueue_entry(kcp->snd_queue.prev, IKCPSEG, node);
            if (old->len < kcp->mss) {
                int capacity = kcp->mss - old->len;
                int extend = (len < capacity)? len : capacity;
                seg = ikcp_segment_new(kcp, old->len + extend);
                assert(seg);
                if (seg == NULL) {
                    return -2;
                }
                iqueue_add_tail(&seg->node, &kcp->snd_queue);
                memcpy(seg->data, old->data, old->len);
                if (buffer) {
                    memcpy(seg->data + old->len, buffer, extend);
                    buffer += extend;
                }
                seg->len = old->len + extend;
                seg->frg = 0;
                len -= extend;
                iqueue_del_init(&old->node);
                ikcp_segment_delete(kcp, old);
            }
        }
        if (len <= 0) {
            return 0;
        }
    }

    // 按kcp->mss分片大小计算分片数量
    if (len <= (int)kcp->mss) count = 1;
    else count = (len + kcp->mss - 1) / kcp->mss;

    // IKCP_WND_RCV是对端接收窗口的默认值也是最大值
    if (count >= (int)IKCP_WND_RCV) return -2;

    if (count == 0) count = 1;

    // fragment
    for (i = 0; i < count; i++) {
        int size = len > (int)kcp->mss ? (int)kcp->mss : len;
        seg = ikcp_segment_new(kcp, size);
        assert(seg);
        if (seg == NULL) {
            return -2;
        }
        if (buffer && len > 0) {
            memcpy(seg->data, buffer, size);
        }
        seg->len = size;
        // [6]按遍历顺序，frg的值从大到小
        seg->frg = (kcp->stream == 0)? (count - i - 1) : 0;
        iqueue_init(&seg->node);
        iqueue_add_tail(&seg->node, &kcp->snd_queue);
        kcp->nsnd_que++;
        if (buffer) {
            buffer += size;
        }
        len -= size;
    }

    return 0;
}


//---------------------------------------------------------------------
// parse ack
// 更新rtt rttval rto
//---------------------------------------------------------------------
static void ikcp_update_ack(ikcpcb *kcp, IINT32 rtt)
{
    IINT32 rto = 0;
    if (kcp->rx_srtt == 0) {
        kcp->rx_srtt = rtt;
        kcp->rx_rttval = rtt / 2;
    }	else {
        long delta = rtt - kcp->rx_srtt;
        if (delta < 0) delta = -delta;
        // 新的delta时间占rtt浮动的1/4权重
        kcp->rx_rttval = (3 * kcp->rx_rttval + delta) / 4;
        // 新的rtt时间占rtt平滑值的1/8权重
        kcp->rx_srtt = (7 * kcp->rx_srtt + rtt) / 8;
        if (kcp->rx_srtt < 1) kcp->rx_srtt = 1;
    }
    // rto=平滑值 + max(interval， rx_rttval)
    // 解读，rto最少也要比rtt多interval，rx_rttval浮动越大，说明网络越不稳定，rto应与rx_rttval浮动成正比，4倍是经验值
    rto = kcp->rx_srtt + _imax_(kcp->interval, 4 * kcp->rx_rttval);
    kcp->rx_rto = _ibound_(kcp->rx_minrto, rto, IKCP_RTO_MAX);
}

/// 设置snd_una
static void ikcp_shrink_buf(ikcpcb *kcp)
{
    struct IQUEUEHEAD *p = kcp->snd_buf.next;
    // 如果sendbuf中有元素(因为send_buf是环状的，next==snd_buf意味着里面没有元素)
    if (p != &kcp->snd_buf) {
        IKCPSEG *seg = iqueue_entry(p, IKCPSEG, node);
        // snd_una设置为最后一个没收到ack的包编号
        kcp->snd_una = seg->sn;
    }	else {
        // snd_una设置为还没发送的包的sn，此时所有发送的包已确认
        kcp->snd_una = kcp->snd_nxt;
    }
}
/// 确认（即删除）sn对应seg
static void ikcp_parse_ack(ikcpcb *kcp, IUINT32 sn)
{
    struct IQUEUEHEAD *p, *next;

    if (_itimediff(sn, kcp->snd_una) < 0 || _itimediff(sn, kcp->snd_nxt) >= 0)
        return;

    for (p = kcp->snd_buf.next; p != &kcp->snd_buf; p = next) {
        IKCPSEG *seg = iqueue_entry(p, IKCPSEG, node);
        next = p->next;
        if (sn == seg->sn) {
            iqueue_del(p);
            ikcp_segment_delete(kcp, seg);
            kcp->nsnd_buf--;
            break;
        }
        if (_itimediff(sn, seg->sn) < 0) {
            break;
        }
    }
}
/// 根据una，移除所有已确认的包
static void ikcp_parse_una(ikcpcb *kcp, IUINT32 una)
{
    struct IQUEUEHEAD *p, *next;
    for (p = kcp->snd_buf.next; p != &kcp->snd_buf; p = next) {
        IKCPSEG *seg = iqueue_entry(p, IKCPSEG, node);
        next = p->next;
        // una之前的都认为已经确定收到，从send_buf中移除
        if (_itimediff(una, seg->sn) > 0) {
            iqueue_del(p);
            ikcp_segment_delete(kcp, seg);
            kcp->nsnd_buf--;
        }	else {
            break;
        }
    }
}

static void ikcp_parse_fastack(ikcpcb *kcp, IUINT32 sn, IUINT32 ts)
{
    struct IQUEUEHEAD *p, *next;

    if (_itimediff(sn, kcp->snd_una) < 0 || _itimediff(sn, kcp->snd_nxt) >= 0)
        return;

    // 遍历snd_buf，snd_buf中为发送但还未收到ack的包
    for (p = kcp->snd_buf.next; p != &kcp->snd_buf; p = next) {
        IKCPSEG *seg = iqueue_entry(p, IKCPSEG, node);
        next = p->next;
        // sn是本次input中收到的最大的包sn，所以超过sn
        if (_itimediff(sn, seg->sn) < 0) {
            break;
        }
        // 把sn之前seg的fastack都++
        else if (sn != seg->sn) {
#ifndef IKCP_FASTACK_CONSERVE
            seg->fastack++;
#else
            if (_itimediff(ts, seg->ts) >= 0)
				seg->fastack++;
#endif
        }
    }
}


//---------------------------------------------------------------------
// ack append
// 记录sn和ts，在flush的时候会把sn和ts赋值给segment生成ack包
//---------------------------------------------------------------------
static void ikcp_ack_push(ikcpcb *kcp, IUINT32 sn, IUINT32 ts)
{
    IUINT32 newsize = kcp->ackcount + 1;
    IUINT32 *ptr;

    // 扩容，标准的list扩容
    if (newsize > kcp->ackblock) {
        IUINT32 *acklist;
        IUINT32 newblock;
        // 双倍扩容
        for (newblock = 8; newblock < newsize; newblock <<= 1);
        // 分配内存，*2是因为要保存sn和ts
        acklist = (IUINT32*)ikcp_malloc(newblock * sizeof(IUINT32) * 2);

        if (acklist == NULL) {
            assert(acklist != NULL);
            abort();
        }

        if (kcp->acklist != NULL) {
            // 把原数据拷贝到新的acklist
            IUINT32 x;
            for (x = 0; x < kcp->ackcount; x++) {
                acklist[x * 2 + 0] = kcp->acklist[x * 2 + 0];
                acklist[x * 2 + 1] = kcp->acklist[x * 2 + 1];
            }
            // 清理掉原来的acklist
            ikcp_free(kcp->acklist);
        }

        kcp->acklist = acklist;
        kcp->ackblock = newblock;
    }

    ptr = &kcp->acklist[kcp->ackcount * 2];
    ptr[0] = sn;
    ptr[1] = ts;
    kcp->ackcount++;
}
// 赋值sn和timestamp
static void ikcp_ack_get(const ikcpcb *kcp, int p, IUINT32 *sn, IUINT32 *ts)
{
    if (sn) sn[0] = kcp->acklist[p * 2 + 0];
    if (ts) ts[0] = kcp->acklist[p * 2 + 1];
}


//---------------------------------------------------------------------
// parse data
//---------------------------------------------------------------------
void ikcp_parse_data(ikcpcb *kcp, IKCPSEG *newseg)
{
    struct IQUEUEHEAD *p, *prev;
    IUINT32 sn = newseg->sn;
    int repeat = 0;

    if (_itimediff(sn, kcp->rcv_nxt + kcp->rcv_wnd) >= 0 ||
        _itimediff(sn, kcp->rcv_nxt) < 0) {
        ikcp_segment_delete(kcp, newseg);
        return;
    }

    for (p = kcp->rcv_buf.prev; p != &kcp->rcv_buf; p = prev) {
        IKCPSEG *seg = iqueue_entry(p, IKCPSEG, node);
        prev = p->prev;
        // 接收队列里已经有了，可能发送端重发导致的
        if (seg->sn == sn) {
            repeat = 1;
            break;
        }
        if (_itimediff(sn, seg->sn) > 0) {
            break;
        }
    }

    if (repeat == 0) {
        iqueue_init(&newseg->node);
        iqueue_add(&newseg->node, p);
        kcp->nrcv_buf++;
    }	else {
        ikcp_segment_delete(kcp, newseg);
    }

#if 0
    ikcp_qprint("rcvbuf", &kcp->rcv_buf);
	printf("rcv_nxt=%lu\n", kcp->rcv_nxt);
#endif

    // move available data from rcv_buf -> rcv_queue
    // [4]
    while (! iqueue_is_empty(&kcp->rcv_buf)) {
        IKCPSEG *seg = iqueue_entry(kcp->rcv_buf.next, IKCPSEG, node);
        // 如果seg的sn是当前等待的sn（接收顺序得到了保证），则放入rcv_queue中
        if (seg->sn == kcp->rcv_nxt && kcp->nrcv_que < kcp->rcv_wnd) {
            iqueue_del(&seg->node);
            kcp->nrcv_buf--;
            iqueue_add_tail(&seg->node, &kcp->rcv_queue);
            kcp->nrcv_que++;
            kcp->rcv_nxt++;
        }	else {
            break;
        }
    }

#if 0
    ikcp_qprint("queue", &kcp->rcv_queue);
	printf("rcv_nxt=%lu\n", kcp->rcv_nxt);
#endif

#if 1
//	printf("snd(buf=%d, queue=%d)\n", kcp->nsnd_buf, kcp->nsnd_que);
//	printf("rcv(buf=%d, queue=%d)\n", kcp->nrcv_buf, kcp->nrcv_que);
#endif
}


//---------------------------------------------------------------------
// input data
//---------------------------------------------------------------------
int ikcp_input(ikcpcb *kcp, const char *data, long size)
{
    IUINT32 prev_una = kcp->snd_una;
    IUINT32 maxack = 0, latest_ts = 0;
    int flag = 0;

    if (ikcp_canlog(kcp, IKCP_LOG_INPUT)) {
        ikcp_log(kcp, IKCP_LOG_INPUT, "[RI] %d bytes", (int)size);
    }

    if (data == NULL || (int)size < (int)IKCP_OVERHEAD) return -1;

    while (1) {
        IUINT32 ts, sn, len, una, conv;
        IUINT16 wnd;
        IUINT8 cmd, frg;
        IKCPSEG *seg;

        if (size < (int)IKCP_OVERHEAD) break;

        data = ikcp_decode32u(data, &conv);
        if (conv != kcp->conv) return -1;

        data = ikcp_decode8u(data, &cmd);
        data = ikcp_decode8u(data, &frg);
        data = ikcp_decode16u(data, &wnd);
        data = ikcp_decode32u(data, &ts);
        data = ikcp_decode32u(data, &sn);
        data = ikcp_decode32u(data, &una);
        data = ikcp_decode32u(data, &len);

        size -= IKCP_OVERHEAD;

        if ((long)size < (long)len || (int)len < 0) return -2;

        if (cmd != IKCP_CMD_PUSH && cmd != IKCP_CMD_ACK &&
            cmd != IKCP_CMD_WASK && cmd != IKCP_CMD_WINS)
            return -3;

        kcp->rmt_wnd = wnd;
        // una之前的包都确认收到
        ikcp_parse_una(kcp, una);
        // [3]设置kcp->snd_unap
        ikcp_shrink_buf(kcp);

        if (cmd == IKCP_CMD_ACK) {
            if (_itimediff(kcp->current, ts) >= 0) {
                // 更新rtt rttval rto
                ikcp_update_ack(kcp, _itimediff(kcp->current, ts));
            }
            // sn对应的包确认收到
            ikcp_parse_ack(kcp, sn);
            // ?? 用确定一下snd_una吗，上面[3]已经确定过了，una应该大于等于ack的sn
            ikcp_shrink_buf(kcp);
            if (flag == 0) {
                flag = 1;
                maxack = sn;
                latest_ts = ts;
            }	else {
                if (_itimediff(sn, maxack) > 0) {
#ifndef IKCP_FASTACK_CONSERVE
                    maxack = sn;
                    latest_ts = ts;
#else
                    if (_itimediff(ts, latest_ts) > 0) {
						maxack = sn;
						latest_ts = ts;
					}
#endif
                }
            }
            if (ikcp_canlog(kcp, IKCP_LOG_IN_ACK)) {
                ikcp_log(kcp, IKCP_LOG_IN_ACK,
                         "input ack: sn=%lu rtt=%ld rto=%ld", (unsigned long)sn,
                         (long)_itimediff(kcp->current, ts),
                         (long)kcp->rx_rto);
            }
        }
        else if (cmd == IKCP_CMD_PUSH) {
            if (ikcp_canlog(kcp, IKCP_LOG_IN_DATA)) {
                ikcp_log(kcp, IKCP_LOG_IN_DATA,
                         "input psh: sn=%lu ts=%lu", (unsigned long)sn, (unsigned long)ts);
            }
            // sn大于接收窗口范围是因为对端的发送窗口过大 还未及时更新
            // 只处理可接收窗口范围内的
            if (_itimediff(sn, kcp->rcv_nxt + kcp->rcv_wnd) < 0) {
                // push ack包
                ikcp_ack_push(kcp, sn, ts);
                // rcv_nxt之前的已经确认过了,直接丢掉
                // 剩下的就是接收窗口允许的sn范围
                if (_itimediff(sn, kcp->rcv_nxt) >= 0) {
                    seg = ikcp_segment_new(kcp, len);
                    seg->conv = conv;
                    seg->cmd = cmd;
                    seg->frg = frg;
                    seg->wnd = wnd;
                    seg->ts = ts;
                    seg->sn = sn;
                    seg->una = una;
                    seg->len = len;

                    if (len > 0) {
                        memcpy(seg->data, data, len);
                    }

                    ikcp_parse_data(kcp, seg);
                }
            }
        }
        else if (cmd == IKCP_CMD_WASK) {
            // ready to send back IKCP_CMD_WINS in ikcp_flush
            // tell remote my window size
            kcp->probe |= IKCP_ASK_TELL;
            if (ikcp_canlog(kcp, IKCP_LOG_IN_PROBE)) {
                ikcp_log(kcp, IKCP_LOG_IN_PROBE, "input probe");
            }
        }
        else if (cmd == IKCP_CMD_WINS) {
            // do nothing
            if (ikcp_canlog(kcp, IKCP_LOG_IN_WINS)) {
                ikcp_log(kcp, IKCP_LOG_IN_WINS,
                         "input wins: %lu", (unsigned long)(wnd));
            }
        }
        else {
            return -3;
        }

        data += len;
        size -= len;
    }

    // 如果刚才处理的包里有ack包，则maxack之前的待确认包的fastack++，以触发快速重传
    if (flag != 0) {
        ikcp_parse_fastack(kcp, maxack, latest_ts);
    }

    if (_itimediff(kcp->snd_una, prev_una) > 0) {
        // kcp->rmt_wnd在上面的代码中发生了变化，所以要更新一下cwnd
        if (kcp->cwnd < kcp->rmt_wnd) {
            IUINT32 mss = kcp->mss;
            // 小于阈值时，阻塞窗口增加1，呈现线性增长
            if (kcp->cwnd < kcp->ssthresh) {
                // 线性增长
                kcp->cwnd++;
                kcp->incr += mss;

            // 超过阈值时，累计多帧阻塞窗口才增加1，比线性曲线小，原本的阻塞窗口比较大的话，得将近16帧，cwnd才增加1
            }	else {
                if (kcp->incr < mss) kcp->incr = mss;
                // [8]
                // 把下面的公式先转成  incr+=mss*(mss/incr + 1/16)
                // 也就说增加m个mss，m=mss/incr + 1/16
                // incr和mss的关系，incr=n*mss，n∈N+(正整数)
                // ∴ m=1/n + 1/16
                // 代入n=1 2 3 4……，得到17/16 9/16 6.3/16 5/16……
                // 随着n增大，m越来越小，也就是incr越大，增长率越低
                // 可见，超过ssthresh后，incr增长率递减
                kcp->incr += (mss * mss) / kcp->incr + (mss / 16);
                //  当多帧后，在incr上累加的值超过了一个mss的大小，则cwnd+1
                if ((kcp->cwnd + 1) * mss <= kcp->incr) {
#if 1
                    // -1是因为incr新累加的数值不会超过1，∴累加值+mss-1 < mss，再除以mss，结果就是cwnd增加了1
                    kcp->cwnd = (kcp->incr + mss - 1) / ((mss > 0)? mss : 1);
#else
                    kcp->cwnd++;
#endif
                }
            }

            // 最大不能超过rmt_wnd
            if (kcp->cwnd > kcp->rmt_wnd) {
                kcp->cwnd = kcp->rmt_wnd;
                kcp->incr = kcp->rmt_wnd * mss;
            }
        }
    }

    return 0;
}


//---------------------------------------------------------------------
// ikcp_encode_seg
// 序列化并seg，并 按大小端编码
//---------------------------------------------------------------------
static char *ikcp_encode_seg(char *ptr, const IKCPSEG *seg)
{
    ptr = ikcp_encode32u(ptr, seg->conv);
    ptr = ikcp_encode8u(ptr, (IUINT8)seg->cmd);
    ptr = ikcp_encode8u(ptr, (IUINT8)seg->frg);
    ptr = ikcp_encode16u(ptr, (IUINT16)seg->wnd);
    ptr = ikcp_encode32u(ptr, seg->ts);
    ptr = ikcp_encode32u(ptr, seg->sn);
    ptr = ikcp_encode32u(ptr, seg->una);
    ptr = ikcp_encode32u(ptr, seg->len);
    return ptr;
}
/// 可用窗口大小
static int ikcp_wnd_unused(const ikcpcb *kcp)
{
    if (kcp->nrcv_que < kcp->rcv_wnd) {
        return kcp->rcv_wnd - kcp->nrcv_que;
    }
    return 0;
}


//---------------------------------------------------------------------
// ikcp_flush
// 1. flush ack包
// 2. 告知/打探窗口大小
// 3. snd_queue转移到snd_buf
// 4. flush send_buf
// 5. 根据flush send_buf时的情况，修改阻塞窗口等信息
//---------------------------------------------------------------------
void ikcp_flush(ikcpcb *kcp)
{
    IUINT32 current = kcp->current;
    char *buffer = kcp->buffer;
    char *ptr = buffer;
    int count, size, i;
    IUINT32 resent, cwnd;
    IUINT32 rtomin;
    struct IQUEUEHEAD *p;
    int change = 0;
    int lost = 0;
    // 这个seg被序列化了好几遍，成员变量赋上不同的值，反复序列化
    IKCPSEG seg;

    // 'ikcp_update' haven't been called.
    if (kcp->updated == 0) return;

    seg.conv = kcp->conv;
    seg.cmd = IKCP_CMD_ACK;
    seg.frg = 0;
    seg.wnd = ikcp_wnd_unused(kcp);
    seg.una = kcp->rcv_nxt;
    seg.len = 0;
    seg.sn = 0;
    seg.ts = 0;

    // flush acknowledges
    count = kcp->ackcount;
    for (i = 0; i < count; i++) {
        size = (int)(ptr - buffer);
        // 超过mtu才output，flush不干净，后面代码会继续序列化到buffer里
        if (size + (int)IKCP_OVERHEAD > (int)kcp->mtu) {
            ikcp_output(kcp, buffer, size);
            ptr = buffer;
        }
        // 赋值编号和时间戳
        ikcp_ack_get(kcp, i, &seg.sn, &seg.ts);
        ptr = ikcp_encode_seg(ptr, &seg);
    }

    kcp->ackcount = 0;

    // probe window size (if remote window size equals zero)
    // 远端可用窗口在input时被赋值
    if (kcp->rmt_wnd == 0) {
        if (kcp->probe_wait == 0) {
            kcp->probe_wait = IKCP_PROBE_INIT;
            kcp->ts_probe = kcp->current + kcp->probe_wait;
        }
        else {
            if (_itimediff(kcp->current, kcp->ts_probe) >= 0) {
                if (kcp->probe_wait < IKCP_PROBE_INIT)
                    kcp->probe_wait = IKCP_PROBE_INIT;
                // 每次超时等待时间变的更长
                kcp->probe_wait += kcp->probe_wait / 2;
                if (kcp->probe_wait > IKCP_PROBE_LIMIT)
                    kcp->probe_wait = IKCP_PROBE_LIMIT;
                kcp->ts_probe = kcp->current + kcp->probe_wait;
                // 打探设置为ask，请求远端返回wnd大小
                kcp->probe |= IKCP_ASK_SEND;
            }
        }
    }	else {
        kcp->ts_probe = 0;
        kcp->probe_wait = 0;
    }

    // flush window probing commands
    // 如果需要打探远端窗口大小，序列化到buffer中
    if (kcp->probe & IKCP_ASK_SEND) {
        // 设置为请求窗口大小，远端收到后回返回一个cmd=IKCP_ASK_TELL的包
        seg.cmd = IKCP_CMD_WASK;
        size = (int)(ptr - buffer);
        if (size + (int)IKCP_OVERHEAD > (int)kcp->mtu) {
            ikcp_output(kcp, buffer, size);
            ptr = buffer;
        }
        ptr = ikcp_encode_seg(ptr, &seg);
    }

    // flush window probing commands
    // 告知远端窗口，发一个包告诉cmd的大小
    // TODO [7] 有必要发吗，每一帧都包含wnd的大小，如果此帧有其他包，就不用发IKCP_CMD_WINS消息了
    if (kcp->probe & IKCP_ASK_TELL) {
        seg.cmd = IKCP_CMD_WINS;
        size = (int)(ptr - buffer);
        if (size + (int)IKCP_OVERHEAD > (int)kcp->mtu) {
            ikcp_output(kcp, buffer, size);
            ptr = buffer;
        }
        ptr = ikcp_encode_seg(ptr, &seg);
    }

    // 每帧重置probe
    kcp->probe = 0;

    // calculate window size
    // 计算最小发送窗口
    cwnd = _imin_(kcp->snd_wnd, kcp->rmt_wnd);
    if (kcp->nocwnd == 0) cwnd = _imin_(kcp->cwnd, cwnd);

    // move data from snd_queue to snd_buf
    // 当待发送序号 小于 窗口末端序号
    // 从kcp->snd_queue转移到kcp->snd_buf
    while (_itimediff(kcp->snd_nxt, kcp->snd_una + cwnd) < 0) {
        IKCPSEG *newseg;
        if (iqueue_is_empty(&kcp->snd_queue)) break;

        // (IKCPSEG*)    ( ((char*)((IKCPSEG*)kcp->snd_queue.next)) - ((size_t) &((IKCPSEG *)0)->node));
        // iqueue_entry宏展开，kcp->snd_queue.next地址向前偏移了node字段相对IKCPSEG的长度，
        // 也就是说，修改了返回的newseg的node和kcp->snd_queue.next是同一个地址，
        // 修改newseg.node就相当于修改了kcp->snd_queue.next
        newseg = iqueue_entry(kcp->snd_queue.next, IKCPSEG, node);

        // 从kcp->snd_queue中删除自己，能起到初始化的作用？
        iqueue_del(&newseg->node);
        // [1]
        // 把自己放到kcp->snd_buf前面，上面两行和下面一行代码实现了从newseg从kcp->snd_queue移除，并添加到kcp->snd_buf
        iqueue_add_tail(&newseg->node, &kcp->snd_buf);

        kcp->nsnd_que--;
        kcp->nsnd_buf++;

        newseg->conv = kcp->conv;
        newseg->cmd = IKCP_CMD_PUSH;
        newseg->wnd = seg.wnd;
        newseg->ts = current;
        newseg->sn = kcp->snd_nxt++;
        newseg->una = kcp->rcv_nxt;
        newseg->resendts = current;
        newseg->rto = kcp->rx_rto;
        newseg->fastack = 0;
        newseg->xmit = 0;
    }

    // calculate resent
    // 超时次数超过fastresend,立刻快速重传
    resent = (kcp->fastresend > 0)? (IUINT32)kcp->fastresend : 0xffffffff;
    // 延迟ack时间,rto的1/8
    rtomin = (kcp->nodelay == 0)? (kcp->rx_rto >> 3) : 0;

    // flush data segments
    // snd_buf是一个环状双向链表，前面的代码[1]，每次新添加的seg放在snd_buf的pre，那么send_buf的pre是最新的，
    // 发送的顺序先发送最老的，也就是send_buf的next(因为是双向)，send_buf本身什么都没存，所以作为退出条件
    for (p = kcp->snd_buf.next; p != &kcp->snd_buf; p = p->next) {
        IKCPSEG *segment = iqueue_entry(p, IKCPSEG, node);
        int needsend = 0;
        // 发送的次数 == 0
        if (segment->xmit == 0) {
            needsend = 1;
            segment->xmit++;
            segment->rto = kcp->rx_rto;
            segment->resendts = current + segment->rto + rtomin;
        }
        // 超过重发时间
        else if (_itimediff(current, segment->resendts) >= 0) {
            needsend = 1;
            segment->xmit++;
            kcp->xmit++;
            if (kcp->nodelay == 0) {
                segment->rto += _imax_(segment->rto, (IUINT32)kcp->rx_rto);
            }	else {
                IINT32 step = (kcp->nodelay < 2)?
                              ((IINT32)(segment->rto)) : kcp->rx_rto;
                segment->rto += step / 2;
            }
            segment->resendts = current + segment->rto;
            lost = 1;
        }
        // segment发送以来没收到ack的帧数超过配置，则快速重发
        else if (segment->fastack >= resent) {
            // 发送次数<快速重发上限 || 没设置重发上限
            if ((int)segment->xmit <= kcp->fastlimit ||
                kcp->fastlimit <= 0) {
                needsend = 1;
                segment->xmit++;
                segment->fastack = 0;
                segment->resendts = current + segment->rto;
                change++;
            }
        }
        // 满足以上三个条件，则需要发送
        if (needsend) {
            int need;
            segment->ts = current;
            segment->wnd = seg.wnd;
            segment->una = kcp->rcv_nxt;

            size = (int)(ptr - buffer);
            need = IKCP_OVERHEAD + segment->len;

            if (size + need > (int)kcp->mtu) {
                ikcp_output(kcp, buffer, size);
                ptr = buffer;
            }

            ptr = ikcp_encode_seg(ptr, segment);
            // 把data也写入到kcp->buffer，data里还不知道是啥？
            if (segment->len > 0) {
                memcpy(ptr, segment->data, segment->len);
                ptr += segment->len;
            }
            // 任意一个segment的发送次数超过dead_link，state就变成了-1，然而state=-1只是标记一下，没有实际用途
            if (segment->xmit >= kcp->dead_link) {
                kcp->state = (IUINT32)-1;
            }
        }
    }

    // flash remain segments
    // 把剩余的buffer flush出去
    size = (int)(ptr - buffer);
    if (size > 0) {
        ikcp_output(kcp, buffer, size);
    }

    //---------------------以下是 根据这一帧发送消息的情况，动态调整kcp配置--------------------
    // update ssthresh
    // 发生了快速重发
    if (change) {
        // inflight：在飞行中的消息个数，即已发送，还未收到ack的个数
        IUINT32 inflight = kcp->snd_nxt - kcp->snd_una;
        kcp->ssthresh = inflight / 2;
        if (kcp->ssthresh < IKCP_THRESH_MIN)
            kcp->ssthresh = IKCP_THRESH_MIN;
        // 设置阻塞窗口大小，为什么+resent，可能是本来是想设置成ssthresh，但是因为这帧发生了快速重发，
        // 意味着有resent以上个正在发送中，占据了阻塞窗口的大小，所以额外加上
        kcp->cwnd = kcp->ssthresh + resent;
        kcp->incr = kcp->cwnd * kcp->mss;
    }

    // 发生超时重发
    if (lost) {
        // 阻塞窗口阈值变为当前窗口的一半
        kcp->ssthresh = cwnd / 2;
        if (kcp->ssthresh < IKCP_THRESH_MIN)
            kcp->ssthresh = IKCP_THRESH_MIN;
        kcp->cwnd = 1;
        kcp->incr = kcp->mss;
    }

    if (kcp->cwnd < 1) {
        kcp->cwnd = 1;
        kcp->incr = kcp->mss;
    }
}


//---------------------------------------------------------------------
// update state (call it repeatedly, every 10ms-100ms), or you can ask 
// ikcp_check when to call it again (without ikcp_input/_send calling).
// 'current' - current timestamp in millisec. 
//---------------------------------------------------------------------
void ikcp_update(ikcpcb *kcp, IUINT32 current)
{
    IINT32 slap;

    kcp->current = current;

    if (kcp->updated == 0) {
        kcp->updated = 1;
        kcp->ts_flush = kcp->current;
    }

    slap = _itimediff(kcp->current, kcp->ts_flush);

    if (slap >= 10000 || slap < -10000) {
        kcp->ts_flush = kcp->current;
        slap = 0;
    }

    if (slap >= 0) {
        kcp->ts_flush += kcp->interval;
        // 距离上一帧的时间间隔超过了interval，强制赋值为当前时间+interval
         if (_itimediff(kcp->current, kcp->ts_flush) >= 0) {
            kcp->ts_flush = kcp->current + kcp->interval;
        }
        ikcp_flush(kcp);
    }
}


//---------------------------------------------------------------------
// Determine when should you invoke ikcp_update:
// returns when you should invoke ikcp_update in millisec, if there 
// is no ikcp_input/_send calling. you can call ikcp_update in that
// time, instead of call update repeatly.
// Important to reduce unnacessary ikcp_update invoking. use it to 
// schedule ikcp_update (eg. implementing an epoll-like mechanism, 
// or optimize ikcp_update when handling massive kcp connections)
// 返回一个最小的下次tick的时间，通过找距离最近的超时的包和下次刷新时间
//---------------------------------------------------------------------
IUINT32 ikcp_check(const ikcpcb *kcp, IUINT32 current)
{
    IUINT32 ts_flush = kcp->ts_flush;
    IINT32 tm_flush = 0x7fffffff;
    IINT32 tm_packet = 0x7fffffff;
    IUINT32 minimal = 0;
    struct IQUEUEHEAD *p;

    if (kcp->updated == 0) {
        return current;
    }

    if (_itimediff(current, ts_flush) >= 10000 ||
        _itimediff(current, ts_flush) < -10000) {
        ts_flush = current;
    }

    if (_itimediff(current, ts_flush) >= 0) {
        return current;
    }
    // 距离刷新时间
    tm_flush = _itimediff(ts_flush, current);

    for (p = kcp->snd_buf.next; p != &kcp->snd_buf; p = p->next) {
        const IKCPSEG *seg = iqueue_entry(p, const IKCPSEG, node);
        // 距离包超时时间
        IINT32 diff = _itimediff(seg->resendts, current);
        if (diff <= 0) {
            return current;
        }
        if (diff < tm_packet) tm_packet = diff;
    }
    // 取最小的
    minimal = (IUINT32)(tm_packet < tm_flush ? tm_packet : tm_flush);
    // 不能超过interval，最少也要interval时间刷新一次
    if (minimal >= kcp->interval) minimal = kcp->interval;

    return current + minimal;
}



int ikcp_setmtu(ikcpcb *kcp, int mtu)
{
    char *buffer;
    if (mtu < 50 || mtu < (int)IKCP_OVERHEAD)
        return -1;
    buffer = (char*)ikcp_malloc((mtu + IKCP_OVERHEAD) * 3);
    if (buffer == NULL)
        return -2;
    kcp->mtu = mtu;
    kcp->mss = kcp->mtu - IKCP_OVERHEAD;
    ikcp_free(kcp->buffer);
    kcp->buffer = buffer;
    return 0;
}

int ikcp_interval(ikcpcb *kcp, int interval)
{
    if (interval > 5000) interval = 5000;
    else if (interval < 10) interval = 10;
    kcp->interval = interval;
    return 0;
}

int ikcp_nodelay(ikcpcb *kcp, int nodelay, int interval, int resend, int nc)
{
    if (nodelay >= 0) {
        kcp->nodelay = nodelay;
        if (nodelay) {
            kcp->rx_minrto = IKCP_RTO_NDL;
        }
        else {
            kcp->rx_minrto = IKCP_RTO_MIN;
        }
    }
    if (interval >= 0) {
        if (interval > 5000) interval = 5000;
        else if (interval < 10) interval = 10;
        kcp->interval = interval;
    }
    if (resend >= 0) {
        kcp->fastresend = resend;
    }
    if (nc >= 0) {
        kcp->nocwnd = nc;
    }
    return 0;
}


int ikcp_wndsize(ikcpcb *kcp, int sndwnd, int rcvwnd)
{
    if (kcp) {
        if (sndwnd > 0) {
            kcp->snd_wnd = sndwnd;
        }
        if (rcvwnd > 0) {   // must >= max fragment size
            kcp->rcv_wnd = _imax_(rcvwnd, IKCP_WND_RCV);
        }
    }
    return 0;
}

int ikcp_waitsnd(const ikcpcb *kcp)
{
    return kcp->nsnd_buf + kcp->nsnd_que;
}


// read conv
IUINT32 ikcp_getconv(const void *ptr)
{
    IUINT32 conv;
    ikcp_decode32u((const char*)ptr, &conv);
    return conv;
}
