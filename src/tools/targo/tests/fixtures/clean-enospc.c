/* Test-only process-wide write failure. Never linked into Targo. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

static _Atomic unsigned denied;
static int no_space(void) { atomic_fetch_add_explicit(&denied, 1, memory_order_relaxed); errno = ENOSPC; return -1; }

#ifdef __APPLE__
#define REAL(name) name
#define INTERPOSE(replacement, original) \
    __attribute__((used)) static struct { const void *replacement; const void *original; } \
    pair_##original __attribute__((section("__DATA,__interpose"))) = \
        { (const void *)(replacement), (const void *)(original) }
#else
#define REAL(name) ((__typeof__(&name))dlsym(RTLD_NEXT, #name))
#define INTERPOSE(replacement, original) \
    extern __typeof__(replacement) original __attribute__((alias(#replacement)))
#endif

static int fail_open(const char *path, int flags, ...) {
    if (flags & (O_CREAT | O_TRUNC)) return no_space();
    return REAL(open)(path, flags);
}
INTERPOSE(fail_open, open);

static int fail_openat(int dir, const char *path, int flags, ...) {
    if (flags & (O_CREAT | O_TRUNC)) return no_space();
    return REAL(openat)(dir, path, flags);
}
INTERPOSE(fail_openat, openat);

#ifndef __APPLE__
static int fail_open64(const char *path, int flags, ...) {
    if (flags & (O_CREAT | O_TRUNC)) return no_space();
    return REAL(open64)(path, flags);
}
INTERPOSE(fail_open64, open64);
static int fail_openat64(int dir, const char *path, int flags, ...) {
    if (flags & (O_CREAT | O_TRUNC)) return no_space();
    return REAL(openat64)(dir, path, flags);
}
INTERPOSE(fail_openat64, openat64);
#endif

static int fail_mkdir(const char *path, mode_t mode) {
    (void)path; (void)mode; return no_space();
}
INTERPOSE(fail_mkdir, mkdir);
static int fail_mkdirat(int dir, const char *path, mode_t mode) {
    (void)dir; (void)path; (void)mode; return no_space();
}
INTERPOSE(fail_mkdirat, mkdirat);

static ssize_t fail_write(int fd, const void *bytes, size_t count) {
    if (fd != STDOUT_FILENO && fd != STDERR_FILENO) return no_space();
    return REAL(write)(fd, bytes, count);
}
INTERPOSE(fail_write, write);
static ssize_t fail_pwrite(int fd, const void *bytes, size_t count, off_t offset) {
    (void)fd; (void)bytes; (void)count; (void)offset; return no_space();
}
INTERPOSE(fail_pwrite, pwrite);
static int fail_ftruncate(int fd, off_t size) {
    (void)fd; (void)size; return no_space();
}
INTERPOSE(fail_ftruncate, ftruncate);
static int fail_truncate(const char *path, off_t size) {
    (void)path; (void)size; return no_space();
}
INTERPOSE(fail_truncate, truncate);
static int fail_rename(const char *from, const char *to) {
    (void)from; (void)to; return no_space();
}
INTERPOSE(fail_rename, rename);
static int fail_renameat(int from_dir, const char *from, int to_dir, const char *to) {
    (void)from_dir; (void)from; (void)to_dir; (void)to; return no_space();
}
INTERPOSE(fail_renameat, renameat);

__attribute__((constructor)) static void active(void) {
    const char message[] = "CLEAN_ENOSPC_ACTIVE\n";
    REAL(write)(STDERR_FILENO, message, sizeof(message) - 1);
}
__attribute__((destructor)) static void report(void) {
    char message[80];
    int length = snprintf(message, sizeof(message), "CLEAN_ENOSPC_DENIED=%u\n", atomic_load_explicit(&denied, memory_order_relaxed));
    if (length > 0 && (size_t)length < sizeof(message))
        REAL(write)(STDERR_FILENO, message, (size_t)length);
}
