// T6 soundness control for the demand-free summary sweep: dropping the fd
// range, the count demands, and the WritesGlobal("fd") audit obligation from
// builtin_write must NOT drop the one demand that guards real UB — the
// buffer must be non-null. `write(fd, ptr::null(), 1)` asks the kernel to
// read one byte through NULL: the retained parameter-1 non-null obligation
// must refute it. This file must REFUTE (exit 1). If it ever proves, the T6
// demand relaxation over-shot and erased the buf contract.
#![crate_type = "lib"]

use std::ptr;

unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, n: usize) -> isize;
}

/// A literal null buffer with a non-zero count — the summary's buf-nonnull
/// demand is the ONLY thing standing between this and a false PROVE.
pub fn null_write(fd: i32) -> isize {
    // SAFETY: none — this is the mutant; the null `buf` is the injected bug.
    unsafe { write(fd, ptr::null(), 1) }
}
