// T1/T6 soundness control: removing the last-segment name fallback (T1) and
// the fd/count/WritesGlobal over-demands (T6) must NOT disable genuine FFI
// detection. A real `extern "C" write` import carries `is_foreign = true`
// from extraction (tcx.is_foreign_item — the authoritative signal, round-19
// #3), routes into the FFI lane, and binds the POSIX write(2) summary. The
// summary's RETAINED demand — the buffer must be non-null — must refute the
// caller-supplied, unconstrained raw pointer below. Note the fd is ALSO
// unconstrained and must NOT be what refutes: a bad fd is EBADF (errno), not
// UB, and the old [0, i128::MAX] fd-range demand was the T1/T6
// over-refutation this lane fixed. This file must REFUTE (exit 1). If it
// ever proves, either foreign routing lost the summary binding or the
// buf-nonnull demand was dropped along with the fd over-demands.
#![crate_type = "lib"]

unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, n: usize) -> isize;
}

/// `buf` is a caller-supplied raw pointer with no non-null evidence — the
/// summary's parameter-1 non-null obligation must fire.
pub fn leak_bytes(fd: i32, buf: *const u8, n: usize) -> isize {
    // SAFETY: none — this is the mutant; the wild `buf` is the injected bug.
    unsafe { write(fd, buf, n) }
}
