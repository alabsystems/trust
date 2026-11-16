//@ needs-trust-verify
//@ aux-build: memory_safe_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-pass
//! NEGATIVE CONTROL for `reject_lowering_gap_launders_uncharged_callee.rs`. The
//! memory-safe gate refuses a failed native lowering that no
//! `assumption:native-lowering` row accounts for, and that row is minted only for a
//! body whose every call resolves to a local verified function. Neither rule may
//! touch a body whose lowering COMPLETES: these call sysroot code (`str::parse`,
//! `u32::checked_add`, `Option::unwrap_or`, `<[T]>::get`) or read a verify-off
//! dependency's constant, the native bundle charges and discharges every call, and
//! each must keep compiling. Measured on stage-1 `b4bc7cdf9d` and `f0e3202c07`
//! (before the gate) and on the gated tree: rc=0, every function's JSON "1 proved".
extern crate memory_safe_unverified_dep as dep;

pub fn return_guarded_read(v: &[u32], i: usize) -> u32 {
    if i >= v.len() {
        return 0;
    }
    v[i]
}

pub fn parse_or_zero(s: &str) -> u64 {
    s.parse::<u64>().unwrap_or(0)
}

pub fn saturating_by_hand(a: u32, b: u32) -> u32 {
    a.checked_add(b).unwrap_or(u32::MAX)
}

pub fn get_copied(v: &[u32], i: usize) -> Option<u32> {
    v.get(i).copied()
}

pub fn scaled_by_dep_constant(x: u8) -> u32 {
    x as u32 * dep::SCALE
}
