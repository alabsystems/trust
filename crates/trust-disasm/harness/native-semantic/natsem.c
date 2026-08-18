/* natsem — NATIVE GROUND TRUTH for what a word DOES, not merely whether it runs.
 *
 * WHY THIS EXISTS. The invariant harness beside this one (native-invariant)
 * answers one question: does the CPU accept the encoding? That found the
 * CONSTRAINED UNPREDICTABLE family and closed it. But its own limits section
 * names the residual honestly: it checks FAULT vs NO-FAULT, never SEMANTICS.
 * A word that executes but whose real effect differs from
 * `Aarch64Semantics::effects` is invisible to it — and the output gate does not
 * merely require that a word runs, it BELIEVES the effect list. A wrong effect
 * is a false Proven just as surely as an unexecutable word, and it is the
 * quieter of the two.
 *
 * THE METHOD. The slot is bracketed:
 *
 *   prologue : load x0..x30, sp and NZCV from a context block at a FIXED
 *              address, so the machine starts in a state the model can be
 *              given exactly.
 *   candidate: the word under test.
 *   epilogue : brk — the trap handler reads the ENTIRE register file back out
 *              of the signal ucontext.
 *
 * Reading the outcome from the ucontext rather than from a store-out epilogue
 * is what makes this exact. An epilogue that stored registers would need a base
 * register, and it would have to clobber one to get it — so the one register it
 * needed most would be the one it destroyed. The kernel has already spilled the
 * whole file for us at the trap; take it from there.
 *
 * MEMORY is deterministic: scratch is filled from `pattern()`, so the model can
 * compute the value at any address without being handed a memory image. After
 * each candidate the window around the pointers is diffed against the template
 * — that is how a STORE is observed, and a store is exactly the case where the
 * register file alone would show nothing.
 *
 * THE FAULTING PC IS THE ANSWER for control flow. A taken branch faults at its
 * TARGET (the arena is brk-filled, and unmapped beyond), so the recorded pc IS
 * the branch target and can be compared against the model's predicted pc. That
 * is the class the dropped-`Effect::PcUpdate` bug lived in.
 *
 * NOTHING IS HAND-ENCODED. Every fixed instruction comes out of clang via the
 * asm template below; the only word this program writes is the candidate,
 * copied verbatim from the input file.
 *
 * ---------------------------------------------------------------------------
 * BLIND SPOTS OF THIS EXECUTOR
 * ---------------------------------------------------------------------------
 *
 * The full, normative inventory is the BLIND SPOTS header in `src/main.rs` —
 * if a limitation is not listed there or here, this harness is claiming to
 * cover it. What follows is the part that is a property of THIS program, i.e.
 * of what the machine is set up to hold and what is read back out.
 *
 * WHAT THE CONTEXT BLOCK LOADS, AND THEREFORE WHAT CAN BE COMPARED:
 * x0..x30, sp, NZCV, and v0..v31. THAT IS ALL.
 *
 *   - FPCR AND FPSR ARE NOT LOADED AND NOT COMPARED. Rounding mode,
 *     flush-to-zero and the cumulative IEEE exception bits are whatever the
 *     process inherited. Both sides see the same thing, so nothing is
 *     manufactured — but an instruction whose only wrong effect is a wrong
 *     FPSR bit is INVISIBLE here, and a model that never sets FPSR at all is
 *     indistinguishable from one that sets it correctly.
 *   - No system register, and no state outside EL0. One MMU configuration,
 *     one SCTLR, PAC and MTE off.
 *   - The exclusive monitor is neither set up nor observed; ordering,
 *     caches, TLBs and timing are outside a single-threaded post-state
 *     comparison by construction.
 *
 * WHAT MEMORY OBSERVATION CANNOT SEE:
 *
 *   - Only the SCRATCH window is diffed, and scratch IS the window (see the
 *     note on SCRATCH_BASE below), so an access that succeeds is inside it by
 *     construction and one that leaves it faults. A faulting candidate has no
 *     post-state and is reported unchecked, never as agreement.
 *   - At most NDIFF_MAX 8-byte words of change are recorded. More than that
 *     sets `ndiff = 0xff`, and the driver reports the memory comparison
 *     UNCHECKED rather than believing a truncated diff.
 *   - A read is invisible. The diff sees WRITES; a load from the wrong
 *     address is caught only because it lands in the destination register,
 *     which is why every 8-byte word of scratch is given a DISTINCT value.
 *
 * WHAT THE OUTCOME CLASSIFICATION CANNOT SEE:
 *
 *   - TIMEOUT is a wall-clock verdict. A candidate that would eventually
 *     finish is counted as unchecked, and the count can move slightly between
 *     runs.
 *   - A candidate that kills the process (some `brk` immediates are claimed by
 *     the kernel and deliver SIGKILL, which no handler can intercept) is
 *     recorded as KILLED at its own index. It is never dropped, because a
 *     dropped record would shift every later one and misattribute every
 *     subsequent comparison.
 *
 * THE TWO HARNESS BUGS THAT LIVED IN THIS FILE, both now guarded rather than
 * merely fixed — see `die_out_of_test` and the `_Static_assert`s on the CTX
 * layout: (1) NZCV written at bit 0 instead of PSTATE 31:28, which reported
 * every flag-reading instruction as a model disagreement; (2) a fault outside a
 * candidate `siglongjmp`ing into an uninitialized buffer, which wedged a
 * process for 29 minutes producing no output and no error. Both had the shape
 * of the bugs this program hunts: something that should have been REFUSED was
 * silently ACCEPTED and given a plausible-looking answer.
 *
 * usage: natsem --slotpc                     print the candidate's PC and exit
 *        natsem <ctx.bin> <words.bin> <recs.bin> [start-index]
 */

#include <errno.h>
#include <libkern/OSCacheControl.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <sys/ucontext.h>
#include <unistd.h>

/* ---- fixed addresses: every one of them is materialised by clang-assembled
 * movz/movk of a literal in the template, never patched by this program ---- */
/* SCRATCH IS EXACTLY THE DIFFED WINDOW, and that identity is the point. If
 * scratch were larger than the window, a store landing in the gap would be
 * unobservable to the diff AND would corrupt the pattern for every later
 * candidate — an unchecked write that silently poisons the oracle, which is the
 * same shape as the bugs being hunted. Making them the same region means every
 * memory access that SUCCEEDS is inside the checked window by construction, and
 * every access outside faults (MEMFAULT) and is reported as unchecked rather
 * than silently believed.
 *
 * +/-128 KiB of reach covers the entire immediate span of a scaled 12-bit
 * load/store offset (32760) and of every pair form, in both directions. */
#define SCRATCH_BASE 0x0000000400000000ULL
#define SCRATCH_SIZE (256ULL << 10)
#define SCRATCH_PTR  (SCRATCH_BASE + SCRATCH_SIZE / 2)
#define CTX_ADDR     0x0000000410000000ULL /* register context block */

#define WIN_BASE SCRATCH_BASE
#define WIN_SIZE SCRATCH_SIZE

#define ARENA_BASE  0x0000000800000000ULL
#define ARENA_SIZE  (512ULL << 20)
#define WINDOW_SIZE (4ULL << 20)

/* CTX layout, in bytes: x0..x30, sp, nzcv, 8 bytes of alignment padding, then
 * v0..v31 at 16 bytes each. The template below encodes these offsets as
 * literals; they must not drift apart.
 *
 * THE V FILE IS PART OF THE STARTING STATE, and it was not always. Without it
 * the SIMD registers held whatever the process happened to leave there, so no
 * SIMD-operand word could be compared — and that exclusion is exactly what hid
 * `str d13,[x28,#0xa0]` being modeled as a store of the GPR X13. An oracle that
 * does not load a register file cannot report a bug in it. `v0..v31` start at a
 * 16-byte-aligned offset because `LDP Q` requires it. */
#define CTX_SP   248
#define CTX_NZCV 256
#define CTX_V    272
#define CTX_LEN  784

/* The prologue below encodes 272..752 as LITERALS, because `LDP Q` takes an
 * immediate. These assertions are what stop that literal block and `CTX_V` from
 * drifting apart — a drift that would load the V file from the wrong offset and
 * report the harness's own mistake as a model bug, which is how the NZCV
 * bit-position error already happened once. */
_Static_assert(CTX_V == 272, "the prologue's LDP Q offsets start at 272");
_Static_assert(CTX_LEN == CTX_V + 32 * 16, "CTX_LEN must cover all 32 V registers");
_Static_assert(CTX_V % 16 == 0, "LDP Q requires a 16-byte-aligned base offset");

__asm__(".section __TEXT,__text\n"
        ".globl _slot_template\n"
        ".p2align 2\n"
        "_slot_template:\n"
        /* x30 <- CTX_ADDR */
        "    movz x30, #0x0004, lsl #32\n"
        "    movk x30, #0x1000, lsl #16\n"
        "    movk x30, #0x0000\n"
        /* flags, then sp, then every GPR — x30 last, since it is the pointer */
        "    ldr  x0, [x30, #256]\n"
        "    msr  nzcv, x0\n"
        "    ldr  x0, [x30, #248]\n"
        "    mov  sp, x0\n"
        /* the SIMD/FP file, before the GPRs — nothing below touches V */
        "    ldp  q0, q1, [x30, #272]\n"
        "    ldp  q2, q3, [x30, #304]\n"
        "    ldp  q4, q5, [x30, #336]\n"
        "    ldp  q6, q7, [x30, #368]\n"
        "    ldp  q8, q9, [x30, #400]\n"
        "    ldp  q10, q11, [x30, #432]\n"
        "    ldp  q12, q13, [x30, #464]\n"
        "    ldp  q14, q15, [x30, #496]\n"
        "    ldp  q16, q17, [x30, #528]\n"
        "    ldp  q18, q19, [x30, #560]\n"
        "    ldp  q20, q21, [x30, #592]\n"
        "    ldp  q22, q23, [x30, #624]\n"
        "    ldp  q24, q25, [x30, #656]\n"
        "    ldp  q26, q27, [x30, #688]\n"
        "    ldp  q28, q29, [x30, #720]\n"
        "    ldp  q30, q31, [x30, #752]\n"
        "    ldp  x0, x1, [x30, #0]\n"
        "    ldp  x2, x3, [x30, #16]\n"
        "    ldp  x4, x5, [x30, #32]\n"
        "    ldp  x6, x7, [x30, #48]\n"
        "    ldp  x8, x9, [x30, #64]\n"
        "    ldp  x10, x11, [x30, #80]\n"
        "    ldp  x12, x13, [x30, #96]\n"
        "    ldp  x14, x15, [x30, #112]\n"
        "    ldp  x16, x17, [x30, #128]\n"
        "    ldp  x18, x19, [x30, #144]\n"
        "    ldp  x20, x21, [x30, #160]\n"
        "    ldp  x22, x23, [x30, #176]\n"
        "    ldp  x24, x25, [x30, #192]\n"
        "    ldp  x26, x27, [x30, #208]\n"
        "    ldp  x28, x29, [x30, #224]\n"
        "    ldr  x30, [x30, #240]\n"
        ".globl _slot_word\n"
        "_slot_word:\n"
        "    nop\n" /* PLACEHOLDER, overwritten with the candidate */
        ".globl _slot_epi\n"
        "_slot_epi:\n"
        "    brk #2\n"
        ".globl _slot_tail\n"
        "_slot_tail:\n"
        "    brk #2\n");

__asm__(".section __TEXT,__text\n"
        ".globl _filler_insn\n"
        ".p2align 2\n"
        "_filler_insn:\n"
        "    brk #1\n");

extern uint32_t slot_template[], slot_word[], slot_epi[], slot_tail[], filler_insn[];

enum {
    OUT_EXECUTED = 0,
    OUT_SIGILL = 1,
    OUT_MEMFAULT = 2,
    OUT_TRAP_SELF = 3,
    OUT_ESCAPED = 4,
    OUT_SIGSYS = 5,
    OUT_SIGFPE = 6,
    OUT_TIMEOUT = 7,
    OUT_OTHER = 8,
    OUT_N = 9
};

#define NDIFF_MAX 16

typedef struct {
    uint8_t outcome;
    uint8_t ndiff; /* 0..NDIFF_MAX; 0xff = more diffs than the record holds */
    uint16_t pad0;
    uint32_t pad1;
    uint64_t x[31];
    uint64_t sp;
    uint64_t pc;
    uint64_t nzcv; /* N<<3 | Z<<2 | C<<1 | V */
    uint64_t diff_off[NDIFF_MAX];
    uint64_t diff_val[NDIFF_MAX];
    /* v0..v31, low half then high half. APPENDED, so every offset above keeps
     * the value the driver's parser already reads. */
    uint64_t v[32][2];
} rec_t;

/* The one function that must agree, byte for byte, with the driver's Rust copy.
 * splitmix64 over the 8-byte-aligned address: cheap, and every 8-byte word of
 * scratch is distinct, so a load that reads the WRONG address produces a value
 * that cannot be confused with the right one. */
static inline uint64_t sm64(uint64_t x)
{
    x += 0x9E3779B97F4A7C15ULL;
    uint64_t z = x;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static inline uint64_t pattern(uint64_t aligned_addr) { return sm64(aligned_addr >> 3); }

static sigjmp_buf jb;
static volatile sig_atomic_t in_test = 0;
static volatile uint64_t word_gen = 0;
static volatile uint64_t alarm_seen = 0;
static volatile int outcome = OUT_OTHER;
static uint64_t g_word_pc, g_epi_pc;
static rec_t g_rec;

/* A fault that arrives when NO candidate is running is a fault in THIS PROGRAM,
 * and it must not be laundered into a candidate outcome.
 *
 * The first version of this harness had no such guard, and it cost 29 minutes of
 * a wedged process to find out why: a signal arriving while libc was inside
 * `malloc` (from the very first `fread`) reached `fault_handler`, which
 * dutifully classified it — pc was neither the word nor the epilogue, so
 * "ESCAPED" — and `siglongjmp`ed into a `jb` that `sigsetjmp` had not yet
 * written. That is a jump to undefined state, and it span forever having
 * produced no records and no error.
 *
 * The shape of that bug is the shape of every bug this whole program exists to
 * find: something that should have been REFUSED was silently ACCEPTED and
 * given a plausible-looking answer. So this exits, loudly, with a code — which
 * the driver already discriminates from signal-death and reports as an executor
 * failure rather than blaming the next candidate. */
static void die_out_of_test(int sig)
{
    static const char msg[] =
        "natsem: FAULT OUTSIDE A CANDIDATE — this is a harness fault, not a "
        "candidate outcome; refusing to attribute it to a word\n";
    ssize_t ignored = write(2, msg, sizeof msg - 1);
    (void)ignored;
    (void)sig;
    _exit(3);
}

static void fault_handler(int sig, siginfo_t *si, void *ctx)
{
    (void)si;
    if (!in_test) die_out_of_test(sig);
    ucontext_t *uc = (ucontext_t *)ctx;
    uint64_t pc = (uint64_t)uc->uc_mcontext->__ss.__pc;

    /* THE WHOLE REGISTER FILE, taken from the state the kernel spilled. This is
     * the state AFTER the candidate and BEFORE anything else ran: the very next
     * instruction is what trapped. */
    for (int i = 0; i < 29; i++) g_rec.x[i] = (uint64_t)uc->uc_mcontext->__ss.__x[i];
    g_rec.x[29] = (uint64_t)uc->uc_mcontext->__ss.__fp;
    g_rec.x[30] = (uint64_t)uc->uc_mcontext->__ss.__lr;
    g_rec.sp = (uint64_t)uc->uc_mcontext->__ss.__sp;
    /* The SIMD/FP file, from the same spill. Taken as two 64-bit halves rather
     * than as `__uint128_t` so the record has one fixed little-endian byte
     * layout that the driver reads back without knowing the compiler's 128-bit
     * ABI. */
    for (int i = 0; i < 32; i++) {
        __uint128_t q = uc->uc_mcontext->__ns.__v[i];
        g_rec.v[i][0] = (uint64_t)q;
        g_rec.v[i][1] = (uint64_t)(q >> 64);
    }
    g_rec.pc = pc;
    uint64_t cpsr = (uint64_t)uc->uc_mcontext->__ss.__cpsr;
    g_rec.nzcv = ((cpsr >> 31) & 1) << 3 | ((cpsr >> 30) & 1) << 2 | ((cpsr >> 29) & 1) << 1 |
                 ((cpsr >> 28) & 1);

    if (pc == g_epi_pc) {
        outcome = OUT_EXECUTED;
    } else if (pc == g_word_pc) {
        switch (sig) {
        case SIGILL: outcome = OUT_SIGILL; break;
        case SIGSEGV:
        case SIGBUS: outcome = OUT_MEMFAULT; break;
        case SIGTRAP: outcome = OUT_TRAP_SELF; break;
        case SIGSYS: outcome = OUT_SIGSYS; break;
        case SIGFPE: outcome = OUT_SIGFPE; break;
        default: outcome = OUT_OTHER; break;
        }
    } else {
        /* Control flow LEFT the slot. `pc` is the branch target — the arena is
         * brk-filled and unmapped beyond it, so nothing ran there. */
        outcome = OUT_ESCAPED;
    }
    siglongjmp(jb, 1);
}

static void alarm_handler(int sig, siginfo_t *si, void *ctx)
{
    (void)sig; (void)si; (void)ctx;
    if (!in_test) return;
    if (alarm_seen == word_gen) {
        outcome = OUT_TIMEOUT;
        siglongjmp(jb, 1);
    }
    alarm_seen = word_gen;
}

static void exit_net(void)
{
    if (in_test) {
        outcome = OUT_ESCAPED;
        siglongjmp(jb, 1);
    }
}

static void install(int sig, void (*fn)(int, siginfo_t *, void *))
{
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_sigaction = fn;
    sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
    sigemptyset(&sa.sa_mask);
    if (sigaction(sig, &sa, NULL) != 0) { perror("sigaction"); exit(2); }
}

/* Where the candidate sits. Derived from the MAP_FIXED constants and the
 * template's own layout, so `--slotpc` and the real run cannot disagree. */
static uint64_t slot_pc(void)
{
    uint64_t win = ARENA_BASE + ARENA_SIZE / 2 - WINDOW_SIZE / 2;
    uint64_t slot = win + WINDOW_SIZE / 2;
    return slot + (uint64_t)((uint8_t *)slot_word - (uint8_t *)slot_template);
}

int main(int argc, char **argv)
{
    if (argc >= 2 && strcmp(argv[1], "--slotpc") == 0) {
        /* word pc, and the first byte of the TEMPLATE. A candidate that
         * branches BACKWARD into the prologue re-runs it, so more than one
         * instruction executed and the record is not a single word's effect;
         * the driver needs the template base to detect that. */
        /* Also the two BINARY-LAYOUT numbers the driver must agree with. A
         * record size or context length that drifts would not fault — it would
         * misparse every field silently, which is the failure mode this whole
         * harness is built to refuse. */
        printf("%llu %llu %zu %d\n", (unsigned long long)slot_pc(),
               (unsigned long long)(slot_pc() -
                                    (uint64_t)((uint8_t *)slot_word - (uint8_t *)slot_template)),
               sizeof(rec_t), CTX_LEN);
        return 0;
    }
    if (argc < 4) {
        fprintf(stderr, "usage: natsem <ctx.bin> <words.bin> <recs.bin> [start]\n");
        return 2;
    }

    /* --- scratch, filled from the pattern --- */
    void *scratch = mmap((void *)SCRATCH_BASE, SCRATCH_SIZE, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANON | MAP_FIXED, -1, 0);
    if (scratch != (void *)SCRATCH_BASE) {
        fprintf(stderr, "scratch MAP_FIXED failed: %s\n", strerror(errno));
        return 2;
    }
    for (uint64_t a = SCRATCH_BASE; a < SCRATCH_BASE + SCRATCH_SIZE; a += 8)
        *(uint64_t *)a = pattern(a);

    /* Template of the diffed window: the reference the post-state is compared
     * against, and the image the window is restored from. */
    uint64_t *tmpl = malloc(WIN_SIZE);
    if (!tmpl) { perror("malloc template"); return 2; }
    memcpy(tmpl, (void *)WIN_BASE, WIN_SIZE);

    /* --- register context block --- */
    void *ctxm = mmap((void *)CTX_ADDR, 4096, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANON | MAP_FIXED, -1, 0);
    if (ctxm != (void *)CTX_ADDR) {
        fprintf(stderr, "ctx MAP_FIXED failed: %s\n", strerror(errno));
        return 2;
    }
    uint8_t ctx_master[CTX_LEN];
    {
        FILE *fc = fopen(argv[1], "rb");
        if (!fc) { perror("open ctx"); return 2; }
        if (fread(ctx_master, 1, CTX_LEN, fc) != CTX_LEN) {
            fprintf(stderr, "ctx file must be exactly %d bytes\n", CTX_LEN);
            return 2;
        }
        fclose(fc);
    }

    /* --- containment arena (identical in shape to native-invariant's) --- */
    void *arena = mmap((void *)ARENA_BASE, ARENA_SIZE, PROT_NONE,
                       MAP_PRIVATE | MAP_ANON | MAP_FIXED | MAP_NORESERVE, -1, 0);
    if (arena != (void *)ARENA_BASE) {
        fprintf(stderr, "arena MAP_FIXED failed: %s\n", strerror(errno));
        return 2;
    }
    size_t region = (size_t)WINDOW_SIZE;
    uint8_t *code = mmap((void *)(ARENA_BASE + ARENA_SIZE / 2 - WINDOW_SIZE / 2), region,
                         PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON | MAP_FIXED, -1, 0);
    if (code == MAP_FAILED) { perror("mmap window"); return 2; }

    size_t tlen = (size_t)((uint8_t *)slot_tail - (uint8_t *)slot_template);
    size_t woff = (size_t)((uint8_t *)slot_word - (uint8_t *)slot_template);
    size_t eoff = (size_t)((uint8_t *)slot_epi - (uint8_t *)slot_template);
    uint8_t *slot = code + region / 2;

    uint32_t fill = filler_insn[0];
    for (size_t i = 0; i < region / 4; i++) ((uint32_t *)code)[i] = fill;
    memcpy(slot, slot_template, tlen);
    if (mprotect(code, region, PROT_READ | PROT_EXEC) != 0) { perror("mprotect RX"); return 2; }
    sys_icache_invalidate(code, region);

    uint32_t *wslot = (uint32_t *)(slot + woff);
    g_word_pc = (uint64_t)(slot + woff);
    g_epi_pc = (uint64_t)(slot + eoff);
    if (g_word_pc != slot_pc()) {
        fprintf(stderr, "slot pc %#llx != predicted %#llx — the driver's model PC would be "
                        "wrong; refusing to run\n",
                (unsigned long long)g_word_pc, (unsigned long long)slot_pc());
        return 2;
    }

    size_t pgsz = (size_t)getpagesize();
    void *wpage = (void *)((uint64_t)wslot & ~(uint64_t)(pgsz - 1));

    static char altstack[SIGSTKSZ * 4];
    stack_t ss = { .ss_sp = altstack, .ss_size = sizeof altstack, .ss_flags = 0 };
    if (sigaltstack(&ss, NULL) != 0) { perror("sigaltstack"); return 2; }
    install(SIGILL, fault_handler);
    install(SIGTRAP, fault_handler);
    install(SIGSEGV, fault_handler);
    install(SIGBUS, fault_handler);
    install(SIGSYS, fault_handler);
    install(SIGFPE, fault_handler);
    install(SIGEMT, fault_handler);
    install(SIGABRT, fault_handler);
    install(SIGALRM, alarm_handler);
    atexit(exit_net);

    /* THE WATCHDOG IS ARMED ONLY WHILE A CANDIDATE RUNS.
     *
     * A free-running timer means signals arrive while this program is inside
     * libc — during `fread`'s buffer allocation, during `fwrite`, during
     * `mprotect`. That is how the wedge above happened, and the guard in
     * `fault_handler` turns that from a silent spin into a loud exit but does
     * not prevent it. Arming per candidate prevents it: between candidates
     * there is no timer, so there is no signal to mishandle.
     *
     * Cost is two `setitimer` calls per word, which is nothing next to the
     * `mprotect` pair and the window scan already on this path. */
    int watchdog_us = 0;
    if (!getenv("NATSEM_NO_WATCHDOG")) {
        const char *e = getenv("NATSEM_WATCHDOG_US");
        long us = e ? atol(e) : 4000;
        if (us < 200) us = 200;
        watchdog_us = (int)us;
    }
    const struct itimerval arm = { { 0, watchdog_us }, { 0, watchdog_us } };
    const struct itimerval disarm = { { 0, 0 }, { 0, 0 } };

    FILE *fi = fopen(argv[2], "rb");
    if (!fi) { perror("open words"); return 2; }
    long start = (argc > 4) ? atol(argv[4]) : 0;
    if (start > 0 && fseek(fi, start * 4, SEEK_SET) != 0) { perror("seek words"); return 2; }
    FILE *fo = fopen(argv[3], "wb");
    if (!fo) { perror("open recs"); return 2; }
    /* UNBUFFERED, for the same reason natexec is: a candidate that draws an
     * uncatchable signal must not take other candidates' records with it. */
    setvbuf(fo, NULL, _IONBF, 0);

    uint64_t tally[OUT_N];
    memset(tally, 0, sizeof tally);
    uint32_t w;
    uint64_t n = 0;
    while (fread(&w, 4, 1, fi) == 1) {
        /* Refresh the context IN FULL every candidate. The previous candidate
         * may have stored anywhere, including here; an input block that the
         * thing under test can edit is not an input block. */
        memcpy((void *)CTX_ADDR, ctx_master, CTX_LEN);

        mprotect(wpage, pgsz, PROT_READ | PROT_WRITE);
        *wslot = w;
        mprotect(wpage, pgsz, PROT_READ | PROT_EXEC);
        sys_icache_invalidate(wslot, 4);

        memset(&g_rec, 0, sizeof g_rec);
        word_gen++;
        outcome = OUT_OTHER;
        if (sigsetjmp(jb, 1) == 0) {
            /* `jb` is written BEFORE `in_test` is raised, and the timer is
             * armed last — so there is no instant at which a handler can fire
             * believing a candidate is running while `jb` is not yet valid. */
            in_test = 1;
            if (watchdog_us) setitimer(ITIMER_REAL, &arm, NULL);
            ((void (*)(void))slot)();
            outcome = OUT_OTHER;
        }
        in_test = 0;
        if (watchdog_us) setitimer(ITIMER_REAL, &disarm, NULL);
        g_rec.outcome = (uint8_t)outcome;

        /* Memory: diff the window against the template, then restore it. */
        uint64_t *win = (uint64_t *)WIN_BASE;
        unsigned nd = 0;
        int overflow = 0;
        for (size_t i = 0; i < WIN_SIZE / 8; i++) {
            if (win[i] != tmpl[i]) {
                if (nd < NDIFF_MAX) {
                    g_rec.diff_off[nd] = (uint64_t)(i * 8);
                    g_rec.diff_val[nd] = win[i];
                    nd++;
                } else {
                    overflow = 1;
                }
                win[i] = tmpl[i];
            }
        }
        g_rec.ndiff = overflow ? 0xff : (uint8_t)nd;

        fwrite(&g_rec, sizeof g_rec, 1, fo);
        tally[g_rec.outcome]++;
        n++;
    }
    fclose(fi);
    fclose(fo);

    static const char *names[OUT_N] = { "EXECUTED", "SIGILL",  "MEMFAULT", "TRAP_SELF", "ESCAPED",
                                        "SIGSYS",   "SIGFPE",  "TIMEOUT",  "OTHER" };
    fprintf(stderr, "natsem: %llu words\n", (unsigned long long)n);
    for (int i = 0; i < OUT_N; i++)
        if (tally[i]) fprintf(stderr, "  %-10s %llu\n", names[i], (unsigned long long)tally[i]);
    return 0;
}
