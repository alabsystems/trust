//@ revisions: default certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//! std's `Ord` TRAIT PATH does not name the impl that runs: `Ord::min`, `max` and
//! `clamp` are provided methods any impl may override (NAME-ANCHOR-2).
//!
//! `E` below is a `#[repr(u8)]` enum whose `Ord` impl overrides `min` to return
//! `E::B` (200) and `max` to return `E::A` (0). `x.min(E::A)` is extracted as
//! `<…::E as core::cmp::Ord>::min` with `callee_key` `krate_name: core`,
//! `krate_is_real_sysroot: true` — core's trait method, the user's body. The
//! call-dest lane (`semantic_guard::ord_min_max_clamp_result_facts`) minted
//! `dest <= x` and `dest <= E::A` for it, so `(x.min(E::A) as u8) + 100` was proved
//! not to overflow; the Clean kernel certified the row and
//! `elide_kernel_certified_checks` deleted the check. `f(E::A)` returned 44 where
//! vanilla Rust panics with `attempt to add with overflow`; `g` is the `max` twin
//! (`- 100` on `E::A`). The `clamp` override in `k` got the same false
//! `overflow:add proved` row; `k` was refused only because its `clamp` call keeps
//! other rows open.
//!
//! BEFORE (stage 1 of integ/wave11 `936573497e`, `scratchpad/stage1-w11`; also
//! `stage1-w10`; each revision's flags with `--emit=metadata`, 2026-10-04): `f` and
//! `g` reported every obligation proved under all three revisions
//! (`TRUST_ELIDE_DEBUG=1`: `elided 1 kernel-certified overflow checks` in each),
//! so none of their annotations fired; `k` reported `2 obligation(s) were not
//! proved`, its overflow row `proved`.
//!
//! AFTER (the fix): every `min`/`max`/`clamp` fact asks
//! `call_facts::primitive_int_ord_method`, which requires the destination (`Self`)
//! and every argument to be one primitive integer type, whose `Ord` only `core`
//! implements. `E` is not, so no fact is minted and each overflow row is refuted.
//! The annotations are what the fixed stage 1 prints. A twin of this file with the
//! three overrides deleted (std's provided bodies run) prints exactly the same: the
//! refusal does not depend on what the user body returns, because nothing short of
//! the impl names it (the fail-closed cost on a user `Ord`). `k`'s count moves from
//! 2 to 3 because its overflow row is no longer proved.
//!
//! `std_min` is the control: genuine `x.min(10) + 1` on `u32` keeps its bound and
//! proves in every revision, so it carries no annotation (compiletest requires
//! every ERROR and WARN to be annotated, and this file does not relax that).

use core::cmp::Ordering;

#[repr(u8)]
#[derive(PartialEq, Eq, PartialOrd, Clone, Copy)]
pub enum E {
    A = 0,
    B = 200,
}

impl Ord for E {
    fn cmp(&self, o: &Self) -> Ordering {
        (*self as u8).cmp(&(*o as u8))
    }
    // User overrides: `min` always returns `B`, `max` always `A`, `clamp` always `B`.
    fn min(self, _o: Self) -> Self {
        E::B
    }
    fn max(self, _o: Self) -> Self {
        E::A
    }
    fn clamp(self, _lo: Self, _hi: Self) -> Self {
        E::B
    }
}

pub fn f(x: E) -> u8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `ord_min_max_requires_primitive_self::f`: 2 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `ord_min_max_requires_primitive_self::f`
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `ord_min_max_requires_primitive_self::f`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `ord_min_max_requires_primitive_self::f`
    (x.min(E::A) as u8) + 100
}

pub fn g(x: E) -> u8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `ord_min_max_requires_primitive_self::g`: 2 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `ord_min_max_requires_primitive_self::g`
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `ord_min_max_requires_primitive_self::g`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `ord_min_max_requires_primitive_self::g`
    (x.max(E::B) as u8) - 100
}

pub fn k(x: E) -> u8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `ord_min_max_requires_primitive_self::k`: 3 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `ord_min_max_requires_primitive_self::k`
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `ord_min_max_requires_primitive_self::k`: 3 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `ord_min_max_requires_primitive_self::k`
    (x.clamp(E::A, E::A) as u8) + 100
}

pub fn std_min(x: u32) -> u32 {
    x.min(10) + 1
}
