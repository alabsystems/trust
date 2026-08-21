/* natsem86 — NATIVE GROUND TRUTH for what an x86-64 instruction DOES,
 * executed under Rosetta 2.
 *
 * The x86-64 counterpart of `../native-semantic/natsem.c`, and deliberately
 * the same design: prologue loads a register file from a context block at a
 * fixed address; the candidate runs; the very next instruction traps; the
 * handler reads the ENTIRE register file out of the ucontext the kernel
 * spilled. Memory is a pattern-filled window that is diffed and restored per
 * candidate. The faulting PC is the answer for control flow.
 *
 * THE ORACLE IS ROSETTA, NOT SILICON, and that is the headline caveat: this
 * program is an x86_64 Mach-O translated by Rosetta 2 on an arm64 host
 * (measured on this machine: it does not run at all until
 * `softwareupdate --install-rosetta`). Rosetta is Apple's translator — a
 * SECOND IMPLEMENTATION of x86-64 semantics, independent of both
 * `trust-machine-sem` and LLVM's disassembler, with hardware TSO and exact
 * scalar integer/flag semantics as its published fidelity contract. It is
 * strictly better than comparing two decoders (the decode differential) and
 * strictly weaker than an x86 CPU: a bug Rosetta shares with our model is
 * invisible here. The normative blind-spot inventory is in `src/main.rs`.
 *
 * WHAT THE CONTEXT BLOCK LOADS, AND THEREFORE WHAT CAN BE COMPARED:
 * rax rcx rdx rbx rsp rbp rsi rdi r8..r15 (the DECODER's register numbering,
 * 0..15) and RFLAGS. THAT IS ALL.
 *
 *   - THE XMM/YMM FILE IS NOT LOADED AND NOT COMPARED. `X86_64Semantics`
 *     refuses SSE/AVX instructions, so they are outside the antecedent; an
 *     instruction whose only effect is a vector write cannot reach the
 *     comparison at all.
 *   - PF AND AF ARE NOT COMPARED. The model carries exactly four flags
 *     (SF ZF CF OF, mapped onto the shared N Z C V state); parity and adjust
 *     exist only on the hardware side, so only the modeled four are read out.
 *   - x87 STATE IS NOT TOUCHED.
 *
 * THE FLAG-LOAD STACK TRICK. Loading RFLAGS needs `popfq`, and `popfq` needs a
 * stack — but a push into the diffed window would show up as a phantom memory
 * write on EVERY candidate. So the prologue first points rsp at a sacrificial
 * slot inside the CONTEXT PAGE (rewritten from a master copy each iteration,
 * never diffed), pops the flags there, and only then loads the real rsp from
 * the context. The order is load-bearing.
 *
 * TRAP-PC NORMALISATION. The arena and slot padding are `int3` (0xCC), and
 * SIGTRAP from `int3` reports RIP one byte PAST the trap instruction, unlike
 * every fault signal (which reports the faulting instruction itself). The
 * handler subtracts that byte for SIGTRAP only, so a recorded pc always names
 * the instruction that stopped execution: the epilogue byte for a fallthrough,
 * the branch TARGET for an escape, the candidate itself for a self-trap.
 *
 * usage: natsem86 --slotpc                   print layout facts and exit
 *        natsem86 <ctx.bin> <words.bin> <recs.bin> [start-index]
 *
 * words.bin records are FIXED 16-BYTE SLOTS: [len u8][15 bytes of code],
 * mirroring the decode differential's slot layout (16 > 15, the longest
 * x86-64 instruction), so a wrong length is contained to one slot.
 */

#include <errno.h>
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

#define SCRATCH_BASE 0x0000000400000000ULL
#define SCRATCH_SIZE (256ULL << 10)
#define SCRATCH_PTR  (SCRATCH_BASE + SCRATCH_SIZE / 2)
#define CTX_ADDR     0x0000000410000000ULL

#define WIN_BASE SCRATCH_BASE
#define WIN_SIZE SCRATCH_SIZE

/* CTX layout, bytes. The prologue encodes these as LITERAL displacements; the
 * asserts below stop the two from drifting apart — the drift failure mode is a
 * misload reported as a model bug, which already happened once on the AArch64
 * side (the NZCV bit-position error). Register order is the DECODER's:
 * rax rcx rdx rbx rsp rbp rsi rdi r8..r15. */
#define CTX_RFLAGS 128
#define CTX_LEN    136
/* The sacrificial popfq stack inside the ctx page, well past CTX_LEN. */
#define CTX_FLAGSTACK 0x800
#define SLOT_ADDR 0x0000000420000000ULL

_Static_assert(CTX_RFLAGS == 16 * 8, "RFLAGS follows the 16 GPRs");
_Static_assert(CTX_LEN == CTX_RFLAGS + 8, "CTX is 16 GPRs + RFLAGS");

#define SLOT_BYTES 16
#define NDIFF_MAX  16

/* ---- the slot template: clang-assembled, never hand-encoded ---- */
__asm__(".section __TEXT,__text\n"
        ".globl _slot_template\n"
        ".p2align 4\n"
        "_slot_template:\n"
        "    movabsq $0x410000000, %r15\n"
        /* flags first, via the sacrificial stack in the ctx page */
        "    leaq 0x800(%r15), %rsp\n"
        "    pushq 128(%r15)\n"
        "    popfq\n"
        /* the real rsp, then every GPR — r15 last, it is the pointer */
        "    movq 32(%r15), %rsp\n"
        "    movq 0(%r15), %rax\n"
        "    movq 8(%r15), %rcx\n"
        "    movq 16(%r15), %rdx\n"
        "    movq 24(%r15), %rbx\n"
        "    movq 40(%r15), %rbp\n"
        "    movq 48(%r15), %rsi\n"
        "    movq 56(%r15), %rdi\n"
        "    movq 64(%r15), %r8\n"
        "    movq 72(%r15), %r9\n"
        "    movq 80(%r15), %r10\n"
        "    movq 88(%r15), %r11\n"
        "    movq 96(%r15), %r12\n"
        "    movq 104(%r15), %r13\n"
        "    movq 112(%r15), %r14\n"
        "    movq 120(%r15), %r15\n"
        ".globl _slot_word\n"
        "_slot_word:\n"
        "    .fill 32, 1, 0xCC\n"
        ".globl _slot_end\n"
        "_slot_end:\n");

extern uint8_t slot_template[];
extern uint8_t slot_word[];
extern uint8_t slot_end[];

typedef struct {
    uint8_t outcome;
    uint8_t ndiff; /* 0..NDIFF_MAX; 0xff = more diffs than the record holds */
    uint16_t pad0;
    uint32_t pad1;
    uint64_t gpr[16]; /* decoder order: rax rcx rdx rbx rsp rbp rsi rdi r8..r15 */
    uint64_t pc;
    uint64_t flags; /* SF<<3 | ZF<<2 | CF<<1 | OF — the model's N Z C V order */
    uint64_t diff_off[NDIFF_MAX];
    uint64_t diff_val[NDIFF_MAX];
} rec_t;

enum {
    OUT_EXECUTED = 0,
    OUT_SIGILL = 1,
    OUT_MEMFAULT = 2,
    OUT_TRAP_SELF = 3,
    OUT_ESCAPED = 4,
    OUT_SIGFPE = 5,
    OUT_SIGSYS = 6,
    OUT_TIMEOUT = 7,
    OUT_OTHER = 8,
    OUT_KILLED = 9, /* written by the DRIVER for a missing record, never here */
};

static sigjmp_buf jb;
static volatile sig_atomic_t in_test = 0;
static volatile int outcome = OUT_OTHER;
static rec_t g_rec;
static uint64_t g_word_pc, g_epi_pc;

/* A fault when NO candidate is running is a fault in THIS PROGRAM. Refuse to
 * classify it as anything else — the AArch64 twin once wedged for 29 minutes
 * because an out-of-test fault longjmp'd into an uninitialized buffer. */
static void die_out_of_test(int sig)
{
    char msg[128];
    int n = snprintf(msg, sizeof msg,
                     "natsem86: FAULT OUTSIDE A CANDIDATE (signal %d) — harness fault, "
                     "not a candidate outcome\n",
                     sig);
    if (n > 0) write(2, msg, (size_t)n);
    _exit(3);
}

static void fault_handler(int sig, siginfo_t *si, void *ctx)
{
    (void)si;
    if (!in_test) die_out_of_test(sig);
    ucontext_t *uc = (ucontext_t *)ctx;
    uint64_t pc = (uint64_t)uc->uc_mcontext->__ss.__rip;
    /* int3 reports RIP one byte PAST the trap; every fault reports the
     * faulting instruction itself. Normalise so a recorded pc always names
     * the instruction that stopped execution. */
    if (sig == SIGTRAP && pc > 0) pc -= 1;

    g_rec.gpr[0] = uc->uc_mcontext->__ss.__rax;
    g_rec.gpr[1] = uc->uc_mcontext->__ss.__rcx;
    g_rec.gpr[2] = uc->uc_mcontext->__ss.__rdx;
    g_rec.gpr[3] = uc->uc_mcontext->__ss.__rbx;
    g_rec.gpr[4] = uc->uc_mcontext->__ss.__rsp;
    g_rec.gpr[5] = uc->uc_mcontext->__ss.__rbp;
    g_rec.gpr[6] = uc->uc_mcontext->__ss.__rsi;
    g_rec.gpr[7] = uc->uc_mcontext->__ss.__rdi;
    g_rec.gpr[8] = uc->uc_mcontext->__ss.__r8;
    g_rec.gpr[9] = uc->uc_mcontext->__ss.__r9;
    g_rec.gpr[10] = uc->uc_mcontext->__ss.__r10;
    g_rec.gpr[11] = uc->uc_mcontext->__ss.__r11;
    g_rec.gpr[12] = uc->uc_mcontext->__ss.__r12;
    g_rec.gpr[13] = uc->uc_mcontext->__ss.__r13;
    g_rec.gpr[14] = uc->uc_mcontext->__ss.__r14;
    g_rec.gpr[15] = uc->uc_mcontext->__ss.__r15;
    g_rec.pc = pc;
    {
        uint64_t rf = (uint64_t)uc->uc_mcontext->__ss.__rflags;
        uint64_t sf = (rf >> 7) & 1, zf = (rf >> 6) & 1, cf = rf & 1, of = (rf >> 11) & 1;
        g_rec.flags = sf << 3 | zf << 2 | cf << 1 | of;
    }

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
        /* Control flow LEFT the slot; pc is the target (int3-normalised). */
        outcome = OUT_ESCAPED;
    }
    siglongjmp(jb, 1);
}

static void alarm_handler(int sig, siginfo_t *si, void *ctx)
{
    (void)sig; (void)si; (void)ctx;
    if (!in_test) die_out_of_test(SIGALRM);
    outcome = OUT_TIMEOUT;
    siglongjmp(jb, 1);
}

static void install(int sig, void (*fn)(int, siginfo_t *, void *))
{
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_sigaction = fn;
    /* SA_ONSTACK: the candidate's rsp points INTO THE DIFFED WINDOW, so a
     * signal frame delivered on the interrupted stack would write ~15 phantom
     * "memory diffs" on every single candidate — measured on this harness's
     * very first smoke test. The alternate stack keeps the kernel's writes out
     * of the oracle's field of view. Same fix as the AArch64 twin. */
    sa.sa_flags = SA_SIGINFO | SA_NODEFER | SA_ONSTACK;
    if (sigaction(sig, &sa, NULL) != 0) { perror("sigaction"); exit(2); }
}

/* splitmix64 of (addr >> 3): BIT-IDENTICAL to the AArch64 twin's `sm64` and to
 * the driver's `ctx::pattern_u64`, so both sides of the differential compute
 * ONE memory image rather than two agreeing guesses. (A first cut used an
 * ad-hoc formula here; nothing failed yet only because the driver did not
 * exist — the identity is the contract, so it is stated and mirrored.) */
static uint64_t pattern(uint64_t addr)
{
    uint64_t x = (addr >> 3) + 0x9E3779B97F4A7C15ULL;
    uint64_t z = x;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

int main(int argc, char **argv)
{
    if (argc >= 2 && strcmp(argv[1], "--slotpc") == 0) {
        /* The candidate pc is the FIXED slot base plus the template's prologue
         * length — stable across runs by MAP_FIXED above. */
        printf("%llu %llu %zu %d\n",
               (unsigned long long)(SLOT_ADDR + (uint64_t)(slot_word - slot_template)),
               (unsigned long long)SLOT_ADDR, sizeof(rec_t), CTX_LEN);
        return 0;
    }
    if (argc < 4) {
        fprintf(stderr, "usage: natsem86 <ctx.bin> <words.bin> <recs.bin> [start]\n");
        return 2;
    }

    void *scratch = mmap((void *)SCRATCH_BASE, SCRATCH_SIZE, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANON | MAP_FIXED, -1, 0);
    if (scratch != (void *)SCRATCH_BASE) {
        fprintf(stderr, "scratch MAP_FIXED failed: %s\n", strerror(errno));
        return 2;
    }
    for (uint64_t a = SCRATCH_BASE; a < SCRATCH_BASE + SCRATCH_SIZE; a += 8)
        *(uint64_t *)a = pattern(a);
    uint64_t *tmpl = malloc(WIN_SIZE);
    if (!tmpl) { perror("malloc"); return 2; }
    memcpy(tmpl, (void *)WIN_BASE, WIN_SIZE);

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
            fprintf(stderr, "short ctx read\n");
            return 2;
        }
        fclose(fc);
    }

    /* The slot page: template + candidate live in one RWX mapping copied from
     * the assembled template. W^X on darwin x86_64 permits MAP_JIT-free RWX
     * for translated processes; if the mmap or mprotect refuses, fail loudly. */
    size_t tpl_len = (size_t)(slot_end - slot_template);
    size_t word_off = (size_t)(slot_word - slot_template);
    /* FIXED address, deliberately: RIP-relative candidates make the model's
     * prediction ADDRESS-DEPENDENT, so the driver must decode at the exact pc
     * the hardware will execute at — which `--slotpc` can only promise if the
     * slot does not move between the handshake and the run. */
    void *slot = mmap((void *)SLOT_ADDR, 4096, PROT_READ | PROT_WRITE | PROT_EXEC,
                      MAP_PRIVATE | MAP_ANON | MAP_FIXED, -1, 0);
    if (slot == MAP_FAILED) { perror("slot mmap"); return 2; }
    memcpy(slot, slot_template, tpl_len);
    memset((uint8_t *)slot + tpl_len, 0xCC, 4096 - tpl_len);
    g_word_pc = (uint64_t)slot + word_off;

    FILE *fw = fopen(argv[2], "rb");
    if (!fw) { perror("open words"); return 2; }
    FILE *fr = fopen(argv[3], "ab");
    if (!fr) { perror("open recs"); return 2; }

    uint64_t start = (argc >= 5) ? strtoull(argv[4], NULL, 0) : 0;
    if (fseeko(fw, (off_t)(start * SLOT_BYTES), SEEK_SET) != 0) { perror("seek"); return 2; }

    static uint8_t altstack[SIGSTKSZ < 65536 ? 65536 : SIGSTKSZ];
    stack_t ss = { .ss_sp = altstack, .ss_size = sizeof altstack, .ss_flags = 0 };
    if (sigaltstack(&ss, NULL) != 0) { perror("sigaltstack"); return 2; }

    install(SIGILL, fault_handler);
    install(SIGSEGV, fault_handler);
    install(SIGBUS, fault_handler);
    install(SIGTRAP, fault_handler);
    install(SIGFPE, fault_handler);
    install(SIGSYS, fault_handler);
    install(SIGALRM, alarm_handler);

    uint8_t wslot[SLOT_BYTES];
    while (fread(wslot, 1, SLOT_BYTES, fw) == SLOT_BYTES) {
        uint8_t len = wslot[0];
        if (len == 0 || len > 15) { fprintf(stderr, "bad slot len %u\n", len); return 2; }

        /* restore memory + context for this candidate */
        memcpy((void *)WIN_BASE, tmpl, WIN_SIZE);
        memcpy((void *)CTX_ADDR, ctx_master, CTX_LEN);
        /* write the candidate; everything after it in the slot is already 0xCC */
        memcpy((uint8_t *)g_word_pc, wslot + 1, len);
        memset((uint8_t *)g_word_pc + len, 0xCC, SLOT_BYTES - len);
        g_epi_pc = g_word_pc + len;

        memset(&g_rec, 0, sizeof g_rec);
        outcome = OUT_OTHER;

        struct itimerval it = { {0, 0}, {0, 200000} }; /* 200ms per word */
        setitimer(ITIMER_REAL, &it, NULL);
        if (sigsetjmp(jb, 1) == 0) {
            in_test = 1;
            ((void (*)(void))slot)();
            /* unreachable: the slot always traps */
        }
        in_test = 0;
        {
            struct itimerval off = { {0, 0}, {0, 0} };
            setitimer(ITIMER_REAL, &off, NULL);
        }

        g_rec.outcome = (uint8_t)outcome;

        /* diff the window against the template */
        unsigned nd = 0;
        int overflow = 0;
        const uint64_t *cur = (const uint64_t *)WIN_BASE;
        for (uint64_t i = 0; i < WIN_SIZE / 8; i++) {
            if (cur[i] != tmpl[i]) {
                if (nd < NDIFF_MAX) {
                    g_rec.diff_off[nd] = i * 8;
                    g_rec.diff_val[nd] = cur[i];
                }
                nd++;
            }
        }
        if (nd > NDIFF_MAX) overflow = 1;
        g_rec.ndiff = overflow ? 0xff : (uint8_t)nd;

        if (fwrite(&g_rec, sizeof g_rec, 1, fr) != 1) { perror("write rec"); return 2; }
        fflush(fr);
    }
    return 0;
}
