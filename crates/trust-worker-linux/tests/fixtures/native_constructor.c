/* Native OS qualification fixture only; no Rust macro ABI or proof authority. */
#include <stddef.h>
#include <stdint.h>

#ifndef ATTACK
#define ATTACK 0
#endif
#if defined(__aarch64__)
enum { NR_WRITE=64, NR_OPENAT=56, NR_SOCKET=198, NR_CLONE=220,
       NR_EXECVE=221, NR_MMAP=222, NR_MPROTECT=226, NR_EXIT_GROUP=94 };
static long raw(long nr, long a, long b, long c, long d, long e, long f) {
    register long x8 __asm__("x8") = nr;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    register long x3 __asm__("x3") = d;
    register long x4 __asm__("x4") = e;
    register long x5 __asm__("x5") = f;
    __asm__ volatile("svc 0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2),
                     "r"(x3), "r"(x4), "r"(x5) : "memory");
    return x0;
}
#elif defined(__x86_64__)
enum { NR_WRITE=1, NR_OPENAT=257, NR_SOCKET=41, NR_CLONE=56,
       NR_EXECVE=59, NR_MMAP=9, NR_MPROTECT=10, NR_EXIT_GROUP=231 };
static long raw(long nr, long a, long b, long c, long d, long e, long f) {
    register long r10 __asm__("r10") = d;
    register long r8 __asm__("r8") = e;
    register long r9 __asm__("r9") = f;
    long result;
    __asm__ volatile("syscall" : "=a"(result) : "a"(nr), "D"(a), "S"(b),
                     "d"(c), "r"(r10), "r"(r8), "r"(r9) : "rcx", "r11", "memory");
    return result;
}
#else
#error unsupported diagnostic architecture
#endif

static void die(int status) {
    raw(NR_EXIT_GROUP, status, 0, 0, 0, 0, 0);
    __builtin_trap();
}
static volatile int constructed;
__attribute__((constructor)) static void construct(void) {
    static const char marker = 'K';
    if (ATTACK == 1) {
        static const char path[] = "/proc/self/fd/1";
        raw(NR_OPENAT, -100, (long)path, 0, 0, 0, 0);
        die(111);
    } else if (ATTACK == 2) {
        raw(NR_SOCKET, 2, 1, 0, 0, 0, 0);
        die(112);
    } else if (ATTACK == 3) {
        raw(NR_CLONE, 17, 0, 0, 0, 0, 0);
        die(113);
    } else if (ATTACK == 4) {
        static const char path[] = "/bin/true";
        static const char *argv[] = { path, NULL };
        static const char *environment[] = { NULL };
        raw(NR_EXECVE, (long)path, (long)argv, (long)environment, 0, 0, 0);
        die(114);
    } else if (ATTACK == 5) {
        raw(NR_MMAP, 0, 4096, 7, 0x22, -1, 0);
        die(115);
    } else if (ATTACK == 6) {
        raw(NR_WRITE, 5, (long)&marker, 1, 0, 0, 0);
        die(116);
    } else if (ATTACK == 7) {
        raw(NR_MPROTECT, (long)(uintptr_t)&construct & ~4095L, 4096, 5, 0, 0, 0);
        die(117);
    } else if (ATTACK == 8) {
        for (;;) raw(NR_WRITE, 1, (long)&marker, 1, 0, 0, 0);
    }
    if (raw(NR_WRITE, 1, (long)&marker, 1, 0, 0, 0) != 1) die(118);
    constructed = 123;
}
__attribute__((visibility("default"))) int trust_native_fixture(void) {
    return constructed == 123 ? 7 : -1;
}
