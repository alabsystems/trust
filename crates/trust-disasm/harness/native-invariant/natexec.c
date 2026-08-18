/* natexec — NATIVE GROUND TRUTH for one AArch64 word at a time.
 *
 * THE QUESTION. The trust-cg output gate certifies objects by re-deriving
 * semantics from emitted bytes. If a word decodes, and the machine model
 * produces effects for it, the gate can reach Proven on an object containing
 * it. The invariant that must hold is then: THE CPU EXECUTES IT. Three
 * soundness holes this week were all the same shape — something accepted that
 * the hardware refuses. A mnemonic-level differential cannot see this class,
 * because it compares NAMES, and a refused word can have a correct name.
 *
 * THE METHOD. Each candidate word is written into a single slot in a MAP_JIT
 * region and executed for real. Every fault is caught and classified BY THE
 * FAULTING PC, which is what makes the answer unambiguous:
 *
 *   fault at the WORD's address        -> the word itself faulted
 *   trap at the EPILOGUE's address     -> the word executed and fell through
 *   fault anywhere else                -> control flow LEFT the slot (a taken
 *                                         branch); the encoding was accepted
 *
 * Without the PC test, a taken branch landing in unmapped memory would report
 * SIGSEGV and be indistinguishable from the word itself faulting. That
 * distinction is the whole harness.
 *
 * SIGILL AT THE WORD is the finding. On AArch64 an undefined or CONSTRAINED
 * UNPREDICTABLE-resolved-to-UNDEF encoding raises its exception at execution,
 * BEFORE any address is generated, so a memory abort cannot preempt it. A word
 * that reports MEMFAULT therefore PROVED it was accepted by the CPU — the
 * address was synthesised by this harness, not by the encoding.
 *
 * NOTHING IS HAND-ENCODED. Every fixed instruction in the slot comes out of
 * clang via the inline-asm template below; the only word this program writes is
 * the CANDIDATE ITSELF, copied verbatim from the input file.
 *
 * ---------------------------------------------------------------------------
 * BLIND SPOTS OF THIS EXECUTOR
 * ---------------------------------------------------------------------------
 *
 * The full, normative inventory is the BLIND SPOTS header in `src/main.rs` —
 * if a limitation is not listed there or here, this harness is claiming to
 * cover it.
 *
 * IT SEES FAULT vs NO-FAULT AND NOTHING ELSE. No register is read back, no
 * memory is diffed, no post-state is compared. A word that executes and does
 * something completely different from what the model says passes here in
 * silence, and that is a false Proven all the same. That entire class belongs
 * to ../native-semantic.
 *
 * EVERY REGISTER HOLDS THE SAME POINTER, deliberately: it maximises the chance
 * that a memory-touching candidate reaches mapped memory, which is what makes
 * MEMFAULT rare and the SIGILL signal clean. It also makes this executor
 * useless for any semantic question — with x1 == x2, an `add x0,x1,x2` that
 * read the wrong register still produces the right answer. `x16` is the one
 * exception, pinned away from any syscall number so that a candidate which
 * happens to be `SVC` cannot reach a real system call.
 *
 * LEGALITY IS HOST-RELATIVE. This is one Apple aarch64 part at EL0 with no
 * SVE/SME/PAC/MTE. An encoding UNDEFINED here for want of a FEAT_* may be legal
 * on another aarch64 CPU. A SIGILL is therefore evidence that THIS CPU refuses
 * a word the model accepts — which is precisely the gate's exposure on this
 * host — but "no SIGILL" does not establish architectural legality in general.
 *
 * OUTCOMES THAT ARE NOT VERDICTS. MEMFAULT proves the word was ACCEPTED (an
 * undefined encoding raises before any address is generated) and says nothing
 * more. ESCAPED means control flow left the slot; where it went is not this
 * program's question. TIMEOUT is a wall-clock judgement and can move slightly
 * between runs. None of the three is folded into agreement.
 *
 * NOT EVERY FAULT IS CATCHABLE — see the SIGKILL note below, which is why the
 * driver must be able to resume at an index.
 *
 * NOT EVERY FAULT IS CATCHABLE. Some `brk` immediates (e.g. `brk #0xb108`) are
 * claimed by the kernel as fatal traps and deliver SIGKILL, which no handler can
 * intercept. Such a candidate terminates this process. That is not a failure of
 * the experiment — it is an outcome, and the driver records it as KILLED — but
 * it does mean the driver must be able to resume. Hence the START index: the
 * driver re-invokes with the index after the casualty, and the cost of a
 * casualty is one process spawn rather than a rewritten chunk.
 *
 * usage: natexec <words.bin> <outcomes.bin> [start-index]
 *   words.bin    : stream of little-endian u32 candidate words
 *   outcomes.bin : one u8 outcome code per word, from `start-index` onward
 */

#include <errno.h>
#include <libkern/OSCacheControl.h>
#include <pthread.h>
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

/* Scratch is mapped at a FIXED address so the slot template can materialise the
 * pointer with clang-assembled movz/movk of a literal, rather than this program
 * patching immediates (which would be hand-encoding by another name). */
#define SCRATCH_BASE 0x0000000400000000ULL
#define SCRATCH_SIZE (64ULL << 20)
#define SCRATCH_PTR  0x0000000400800000ULL /* 8 MiB in: room either side */

/* CONTAINMENT. A candidate can be a taken branch. `b`/`bl` reach +/-128 MiB, and
 * the first version of this harness let one of them land in real library code,
 * which ran and called exit() — the process died mid-sweep and silently
 * truncated its own results. A harness that can be hijacked by the thing it is
 * testing produces no evidence at all.
 *
 * So the slot sits at the centre of a 512 MiB PROT_NONE reservation: every
 * PC-relative branch that exists on this architecture lands either in the small
 * brk-filled window around the slot or in unmapped memory. Register-indirect
 * branches (br/blr/ret) go to SCRATCH_PTR, which is mapped without PROT_EXEC.
 * No candidate can reach a single byte of real code. */
#define ARENA_BASE 0x0000000800000000ULL
#define ARENA_SIZE (512ULL << 20)
#define WINDOW_SIZE (4ULL << 20) /* brk-filled, executable, centred in the arena */

/* The slot template. x0-x30 AND sp all point at SCRATCH_PTR, so a load or store
 * in the candidate addresses live memory instead of faulting for an
 * uninteresting reason. x16 holds SCRATCH_PTR too: on macOS/arm64 the syscall
 * number is x16, and SCRATCH_PTR is not a valid syscall number, so a candidate
 * that happens to be `svc` cannot reach a real system call. That is why no
 * register needs a special value. */
__asm__(".section __TEXT,__text\n"
        ".globl _slot_template\n"
        ".p2align 2\n"
        "_slot_template:\n"
        "    movz x16, #0x0004, lsl #32\n"
        "    movk x16, #0x0080, lsl #16\n"
        "    movk x16, #0x0000\n"
        "    mov  sp, x16\n"
        "    mov  x0, x16\n"
        "    mov  x1, x16\n"
        "    mov  x2, x16\n"
        "    mov  x3, x16\n"
        "    mov  x4, x16\n"
        "    mov  x5, x16\n"
        "    mov  x6, x16\n"
        "    mov  x7, x16\n"
        "    mov  x8, x16\n"
        "    mov  x9, x16\n"
        "    mov  x10, x16\n"
        "    mov  x11, x16\n"
        "    mov  x12, x16\n"
        "    mov  x13, x16\n"
        "    mov  x14, x16\n"
        "    mov  x15, x16\n"
        "    mov  x17, x16\n"
        "    mov  x18, x16\n"
        "    mov  x19, x16\n"
        "    mov  x20, x16\n"
        "    mov  x21, x16\n"
        "    mov  x22, x16\n"
        "    mov  x23, x16\n"
        "    mov  x24, x16\n"
        "    mov  x25, x16\n"
        "    mov  x26, x16\n"
        "    mov  x27, x16\n"
        "    mov  x28, x16\n"
        "    mov  x29, x16\n"
        "    mov  x30, x16\n"
        ".globl _slot_word\n"
        "_slot_word:\n"
        "    nop\n" /* PLACEHOLDER, overwritten with the candidate */
        ".globl _slot_epi\n"
        "_slot_epi:\n"
        "    brk #2\n"
        ".globl _slot_tail\n"
        "_slot_tail:\n"
        "    brk #2\n");

/* Filler word for the rest of the region: a distinct brk, so a taken branch
 * that lands in the region stops immediately instead of running wild. */
__asm__(".section __TEXT,__text\n"
        ".globl _filler_insn\n"
        ".p2align 2\n"
        "_filler_insn:\n"
        "    brk #1\n");

extern uint32_t slot_template[], slot_word[], slot_epi[], slot_tail[], filler_insn[];

enum {
    OUT_EXECUTED = 0,   /* trapped at the epilogue: the word ran, fell through */
    OUT_SIGILL = 1,     /* SIGILL AT THE WORD: the CPU refuses this encoding */
    OUT_MEMFAULT = 2,   /* SIGSEGV/SIGBUS at the word: address, not encoding */
    OUT_TRAP_SELF = 3,  /* SIGTRAP at the word: the word is brk/hlt itself */
    OUT_ESCAPED = 4,    /* fault elsewhere: a branch was taken */
    OUT_SIGSYS = 5,
    OUT_SIGFPE = 6,
    OUT_TIMEOUT = 7,
    OUT_OTHER = 8,
    OUT_N = 9
};

static sigjmp_buf jb;
static volatile sig_atomic_t in_test = 0;
static volatile uint64_t word_gen = 0;    /* bumped per candidate */
static volatile uint64_t alarm_seen = 0;  /* generation the last alarm observed */
static volatile int outcome = OUT_OTHER;
static uint64_t g_word_pc, g_epi_pc, g_region_lo, g_region_hi;

static void fault_handler(int sig, siginfo_t *si, void *ctx)
{
    (void)si;
    ucontext_t *uc = (ucontext_t *)ctx;
    uint64_t pc = (uint64_t)uc->uc_mcontext->__ss.__pc;
    int at_word = (pc == g_word_pc);
    int at_epi = (pc == g_epi_pc);

    if (at_epi) {
        outcome = OUT_EXECUTED;
    } else if (at_word) {
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
        /* Control flow left the slot. The encoding was accepted by the CPU;
         * where it went is this harness's synthetic context, not a property of
         * the word. */
        outcome = OUT_ESCAPED;
    }
    siglongjmp(jb, 1);
}

/* Watchdog. A candidate can be a self-branch (`b #0`) and never return. A
 * repeating timer fires; the handler aborts the candidate only if it has
 * already seen this same candidate at a previous tick, so a fast candidate can
 * never be misreported as a timeout by a tick that merely lands on it. */
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

/* Last-ditch net: if a candidate somehow reaches code that calls exit(), come
 * back rather than let the process die and truncate the results. Containment
 * above should make this unreachable; it is kept because "unreachable" is what
 * was believed about the previous three holes. */
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

int main(int argc, char **argv)
{
    if (argc < 3) { fprintf(stderr, "usage: natexec <words.bin> <outcomes.bin>\n"); return 2; }

    /* --- scratch at its fixed address, or nothing works --- */
    void *scratch = mmap((void *)SCRATCH_BASE, SCRATCH_SIZE, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANON | MAP_FIXED, -1, 0);
    if (scratch != (void *)SCRATCH_BASE) {
        fprintf(stderr, "scratch MAP_FIXED at %#llx failed: %s\n", SCRATCH_BASE, strerror(errno));
        return 2;
    }

    /* --- containment arena: nothing a candidate branches to is real code --- *
     * The whole 512 MiB is reserved PROT_NONE first, so the executable window
     * carved out of its centre is guaranteed to sit at a known address with
     * >=254 MiB of unmapped space either side — more than the +/-128 MiB reach
     * of `b`/`bl`, the longest branch this architecture has. */
    void *arena = mmap((void *)ARENA_BASE, ARENA_SIZE, PROT_NONE,
                       MAP_PRIVATE | MAP_ANON | MAP_FIXED | MAP_NORESERVE, -1, 0);
    if (arena != (void *)ARENA_BASE) {
        fprintf(stderr, "arena MAP_FIXED at %#llx failed: %s\n", ARENA_BASE, strerror(errno));
        return 2;
    }

    /* --- executable window at the arena's centre: one slot in brk filler ---
     * MAP_JIT refuses MAP_FIXED, so the window is mapped RW at the address we
     * need and flipped to RX. Only the single page holding the candidate is
     * flipped back per word. */
    size_t region = (size_t)WINDOW_SIZE;
    uint8_t *code = mmap((void *)(ARENA_BASE + ARENA_SIZE / 2 - WINDOW_SIZE / 2), region,
                         PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON | MAP_FIXED, -1, 0);
    if (code == MAP_FAILED) { perror("mmap window"); return 2; }
    g_region_lo = (uint64_t)code;
    g_region_hi = g_region_lo + region;

    size_t tlen = (size_t)((uint8_t *)slot_tail - (uint8_t *)slot_template);
    size_t woff = (size_t)((uint8_t *)slot_word - (uint8_t *)slot_template);
    size_t eoff = (size_t)((uint8_t *)slot_epi - (uint8_t *)slot_template);
    uint8_t *slot = code + region / 2; /* middle, so short branches land in filler */

    uint32_t fill = filler_insn[0];
    for (size_t i = 0; i < region / 4; i++) ((uint32_t *)code)[i] = fill;
    memcpy(slot, slot_template, tlen);
    if (mprotect(code, region, PROT_READ | PROT_EXEC) != 0) { perror("mprotect RX"); return 2; }
    sys_icache_invalidate(code, region);

    uint32_t *wslot = (uint32_t *)(slot + woff);
    g_word_pc = (uint64_t)(slot + woff);
    g_epi_pc = (uint64_t)(slot + eoff);

    size_t pgsz = (size_t)getpagesize();
    void *wpage = (void *)((uint64_t)wslot & ~(uint64_t)(pgsz - 1));

    /* --- signal plumbing --- */
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
    /* Watchdog period. A candidate that does not loop completes in nanoseconds,
     * so a few milliseconds is an enormous margin; the two-tick rule below adds
     * another. The period dominates runtime in branch-dense regions of the
     * encoding space, where a large minority of candidates are backward
     * branches that loop forever, so it is worth keeping small. */
    if (!getenv("NATEXEC_NO_WATCHDOG")) {
        const char *e = getenv("NATEXEC_WATCHDOG_US");
        long us = e ? atol(e) : 4000;
        if (us < 200) us = 200;
        struct itimerval it = { { 0, (int)us }, { 0, (int)us } };
        setitimer(ITIMER_REAL, &it, NULL);
    }

    /* --- run --- */
    FILE *fi = fopen(argv[1], "rb");
    if (!fi) { perror("open words"); return 2; }
    long start = (argc > 3) ? atol(argv[3]) : 0;
    if (start > 0 && fseek(fi, start * 4, SEEK_SET) != 0) { perror("seek words"); return 2; }
    FILE *fo = fopen(argv[2], "wb");
    if (!fo) { perror("open outcomes"); return 2; }
    /* UNBUFFERED. A candidate that draws SIGKILL takes any buffered bytes with
     * it, and the driver would then attribute the death to the wrong word — by
     * up to a whole buffer's worth. The count of bytes in this file must equal
     * the count of candidates that completed, exactly, at every instant. */
    setvbuf(fo, NULL, _IONBF, 0);

    uint64_t tally[OUT_N];
    memset(tally, 0, sizeof tally);
    uint32_t w;
    uint64_t n = 0;
    while (fread(&w, 4, 1, fi) == 1) {
        mprotect(wpage, pgsz, PROT_READ | PROT_WRITE);
        *wslot = w;
        mprotect(wpage, pgsz, PROT_READ | PROT_EXEC);
        sys_icache_invalidate(wslot, 4);

        word_gen++;
        outcome = OUT_OTHER;
        if (sigsetjmp(jb, 1) == 0) {
            in_test = 1;
            ((void (*)(void))slot)();
            /* The slot always ends at a brk, so this is unreachable. */
            outcome = OUT_OTHER;
        }
        in_test = 0;
        uint8_t oc = (uint8_t)outcome;
        fwrite(&oc, 1, 1, fo);
        tally[oc]++;
        n++;
    }
    fclose(fi);
    fclose(fo);

    static const char *names[OUT_N] = { "EXECUTED", "SIGILL",  "MEMFAULT", "TRAP_SELF", "ESCAPED",
                                        "SIGSYS",   "SIGFPE",  "TIMEOUT",  "OTHER" };
    fprintf(stderr, "natexec: %llu words\n", (unsigned long long)n);
    for (int i = 0; i < OUT_N; i++)
        if (tally[i]) fprintf(stderr, "  %-10s %llu\n", names[i], (unsigned long long)tally[i]);
    return 0;
}
