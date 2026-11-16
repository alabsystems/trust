//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A verify-off dependency for `inlined_sysroot_panic_refused.rs`, revisions
//! `dep_tail_inl` and `dep_asm_inl`: the two arms of the inlined-foreign-panic
//! rule (`inlined_sysroot_panic::inlined_foreign_panic_site`) that are BACKSTOPS
//! today, because the compiler refuses their shapes before the rule is asked.
//! The revisions pin those shapes' verdicts, not the arms.
#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]

/// Aborts on 7.
#[inline(never)]
pub fn inner(x: u32) -> u32 {
    if x == 7 {
        std::process::abort()
    }
    x
}

/// Tail-calls `inner`. The MIR inliner never inlines a body that contains a tail
/// call (`inline.rs`: "can't inline functions with tail calls"; the same body
/// under `#[rustc_force_inline]` is a compile error), so `-Zinline-mir=yes` leaves
/// `tl` a call, which is refused as a call into a verify-off dependency.
#[inline]
pub fn tl(x: u32) -> u32 {
    become inner(x)
}

/// Traps on 7 through `noreturn` inline assembly. Inlined under
/// `-Zinline-mir=yes`, the assembly lands in the caller.
#[inline]
pub fn trap(x: u32) -> u32 {
    if x == 7 {
        #[cfg(target_arch = "aarch64")]
        unsafe {
            core::arch::asm!("brk #0x1", options(noreturn, nomem, nostack));
        }
        #[cfg(target_arch = "x86_64")]
        unsafe {
            core::arch::asm!("ud2", options(noreturn, nomem, nostack));
        }
        #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
        std::process::abort();
    }
    x
}
