//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! An ORDINARY verify-off dependency, compiled the way `targo` compiles every
//! dependency unit, for `inlined_sysroot_panic_refused.rs`. Its `#[inline]`
//! functions are copied into a verifying caller by an explicit
//! `-Zinline-mir=yes`; at `-O0` each call to them is a fail-closed dependency
//! call. `fab` is `#[rustc_force_inline]`, which the ForceInline pass honors at
//! EVERY mir-opt-level: it is inlined even at the verifying default.
#![feature(rustc_attrs)]
#![allow(internal_features)]

/// Aborts on 7. The abort is `std::process::abort()`, a sysroot call the
/// default policy tolerates in a user's own body, reached here from a
/// DEPENDENCY's scope once inlined.
#[inline]
pub fn ab(x: u32) -> u32 {
    if x == 7 {
        std::process::abort()
    }
    x
}

/// Panics when `i` is out of range, through std's `Option::expect`.
#[inline]
pub fn gt(v: &[u32], i: usize) -> u32 {
    *v.get(i).expect("idx")
}

/// `ab` again, force-inlined: copied into the caller with no flag at all.
#[rustc_force_inline]
pub fn fab(x: u32) -> u32 {
    if x == 7 {
        std::process::abort()
    }
    x
}
