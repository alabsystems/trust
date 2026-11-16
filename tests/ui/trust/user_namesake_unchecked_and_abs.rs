//@ revisions: userunchecked userabs controls
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[userunchecked] check-pass
//@[userabs] check-pass
//@[controls] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A USER function merely NAMED like a core integer operation owes none of that
//! operation's rows (UNCHECKED-NAME-1, ABS-NAME-1; 2026-10-06).
//!
//! Two of `trust_vcgen`'s call-site recognizers that MINT a row decided the callee by
//! name, not by owner — the defect POW-SYMEXP-1's integration review closed for `pow`:
//!
//! * `overflow_arith_call`'s `unchecked_{add,sub,mul}` arms read the last path
//!   segment alone. A call to a user `fn unchecked_add(a: u32, b: u32) -> u32 { a ^ b }`
//!   (or `unchecked_mul`, or a trait method `T::unchecked_mul`) was charged
//!   `UncheckedArithmeticOverflow` over the user function's own arguments.
//! * `is_signed_abs_call` was `method_tail == "abs"` plus a `core::num::` /
//!   `std::num::` SUBSTRING anywhere in the rendered path, so `mycore::num::abs(x)`,
//!   `mystd::num::abs(x)` and `G::<core::num::Wrapping<i32>>::abs(x)` minted
//!   `NegationOverflow { x == i32::MIN }`.
//!
//! None of the user functions below performs arithmetic (`^` / `|`), so none can
//! overflow, panic or reach UB. Both recognizers now take only core's authenticated
//! integer inherent (`numeric_panic::int_inherent`: `core::num::<impl iN/uN>::…` under a
//! sysroot root that is not `__trust_crate@`-stamped), the identity `pow` and
//! `strict_pow` already use; `unchecked_*` also keeps the exact
//! `core::intrinsics::unchecked_*` path. trust-clean's negation-subject gates call the
//! same exported `abs` predicate instead of keeping substring twins.
//!
//! BEFORE (the stage 1 of `9e11546767`, `scratchpad/stage1-w17`, measured 2026-10-06
//! with this header's flags plus `--cfg <revision> -Zui-testing
//! -Zdeduplicate-diagnostics=no --emit=metadata -Ztrust-verify-output=json`):
//! * `userunchecked` exits 1 with 6 errors: `x_add`, `x_mul` and `x_tmul` each read
//!   `unchecked_overflow:{add,mul} | unknown` and are refused ("incomplete" + "strict
//!   failed"). `y_add` and `y_tmul` pass, but only because their phantom row reads
//!   `proved | clean-kernel-certified | unchecked arithmetic overflow (Add/Mul)` — a
//!   Certified row about an operation the program never performs. A check-pass revision
//!   cannot see that row; `crates/trust-vcgen/tests/user_namesake_unchecked_abs_realmir.rs`
//!   and `overflow_call_tests.rs` pin that it is gone. `x_sub` (`&self` receiver) had no
//!   row. The user bodies read `trivially panic-free`.
//! * `userabs` exits 1 with 9 errors: `a4`, `c1` and `s1` each read `negation | failed
//!   (ay-in-process)` at `x = -2147483648` and are reported as "Trust verification found
//!   1 guaranteed Level 0 safety violation(s)" — for functions that cannot panic.
//! * `controls` exits 1 with the 9 errors annotated below; `e2` and `i_guarded` pass.
//!
//! AFTER (predicted; not built — the fix is in `crates/` only and needs a rebuilt stage
//! 1): `userunchecked` and `userabs` exit 0, every caller `no_obligations` (`x_tmul` and
//! `y_tmul` keep their proved panic-freedom `assert` row). `controls` is unchanged: core's
//! own `i32::abs` keeps its refuted negation row (`e1`) and its proved one (`e2`), and
//! `u32::unchecked_add` / `u64::unchecked_mul` keep their `unknown` unchecked row beside
//! the `[unsafe:unmodeled-call]` refusal — the annotated "3 obligation(s)" counts that row
//! (it would read 2 without it). The intrinsic spelling reaches vcgen as
//! `BinOp::AddUnchecked`, not as a call, and is pinned here as a control only.

#![cfg_attr(controls, feature(core_intrinsics))]
#![cfg_attr(controls, allow(internal_features))]

// ---- userunchecked ----

#[cfg(userunchecked)]
#[inline(never)]
pub fn unchecked_add(a: u32, b: u32) -> u32 {
    a ^ b
}

#[cfg(userunchecked)]
#[inline(never)]
pub fn unchecked_mul(a: u64, b: u64) -> u64 {
    a | b
}

#[cfg(userunchecked)]
pub struct M(pub u32);

#[cfg(userunchecked)]
impl M {
    #[inline(never)]
    pub fn unchecked_sub(&self, b: u32) -> u32 {
        self.0 ^ b
    }
}

#[cfg(userunchecked)]
pub trait T {
    fn unchecked_mul(self, b: u32) -> u32;
}

#[cfg(userunchecked)]
impl T for u32 {
    #[inline(never)]
    fn unchecked_mul(self, b: u32) -> u32 {
        self | b
    }
}

#[cfg(userunchecked)]
pub fn x_add(a: u32, b: u32) -> u32 {
    unchecked_add(a, b)
}

#[cfg(userunchecked)]
pub fn x_mul(a: u64, b: u64) -> u64 {
    unchecked_mul(a, b)
}

#[cfg(userunchecked)]
pub fn x_sub(m: M, b: u32) -> u32 {
    m.unchecked_sub(b)
}

#[cfg(userunchecked)]
pub fn x_tmul(a: u32, b: u32) -> u32 {
    T::unchecked_mul(a, b)
}

#[cfg(userunchecked)]
pub fn y_add(a: u32, b: u32) -> u32 {
    if a < 10 && b < 10 { unchecked_add(a, b) } else { 0 }
}

#[cfg(userunchecked)]
pub fn y_tmul(a: u32, b: u32) -> u32 {
    if a < 10 && b < 10 { T::unchecked_mul(a, b) } else { 0 }
}

// ---- userabs ----

#[cfg(userabs)]
pub struct G<X>(pub X);

#[cfg(userabs)]
impl<X> G<X> {
    #[inline(never)]
    pub fn abs(x: i32) -> i32 {
        x ^ 1
    }
}

#[cfg(userabs)]
pub mod mycore {
    pub mod num {
        #[inline(never)]
        pub fn abs(x: i32) -> i32 {
            x ^ 1
        }
    }
}

#[cfg(userabs)]
pub mod mystd {
    pub mod num {
        #[inline(never)]
        pub fn abs(x: i32) -> i32 {
            x ^ 1
        }
    }
}

// The rendered callee is `…::G::<core::num::wrapping::Wrapping<i32>>::abs`.
#[cfg(userabs)]
// ZERO-ROW-GATE (2026-10-10) refused `a4` here; R43-ZERO-ROW-PARITY (2026-10-13): accepted again:
// `G::<X>::abs`'s body (`x ^ 1`) holds no panic-capable terminator and the call resolves to it,
// so the R43 parametric premises discharge `G::<Wrapping<i32>>::abs`, as this header predicted.
pub fn a4(x: i32) -> i32 {
    G::<core::num::Wrapping<i32>>::abs(x)
}

#[cfg(userabs)]
pub fn c1(x: i32) -> i32 {
    mycore::num::abs(x)
}

#[cfg(userabs)]
pub fn s1(x: i32) -> i32 {
    mystd::num::abs(x)
}

// ---- controls: core's own operations keep their rows ----

#[cfg(controls)]
pub fn e1(x: i32) -> i32 {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `user_namesake_unchecked_and_abs::e1`: 2 obligation(s) were not proved
    //[controls]~^^ ERROR Trust strict verification failed for `user_namesake_unchecked_and_abs::e1`
    // Re-pinned 2026-10-15: no longer a "guaranteed" violation, and it never was one: `x` is a
    // free parameter and `x.abs()` panics only at `i32::MIN` (the FAILED `[negation]` row's
    // counterexample); a violation that depends on an input is possible, not forced. The
    // merged compiler does not emit it (measured 2026-10-15 on the merge's stage 1, before and
    // after trust-router's `violation_is_forced` stopped binding a violation's own
    // equalities). Still refused.
    x.abs()
}

#[cfg(controls)]
pub fn e2(x: i32) -> i32 {
    if x != i32::MIN { x.abs() } else { 0 }
}

#[cfg(controls)]
pub fn m_unguarded(a: u32, b: u32) -> u32 {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `user_namesake_unchecked_and_abs::m_unguarded`: 3 obligation(s) were not proved
    //[controls]~^^ ERROR Trust strict verification failed for `user_namesake_unchecked_and_abs::m_unguarded`
    unsafe { a.unchecked_add(b) }
}

#[cfg(controls)]
pub fn path_unguarded(a: u64, b: u64) -> u64 {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `user_namesake_unchecked_and_abs::path_unguarded`: 3 obligation(s) were not proved
    //[controls]~^^ ERROR Trust strict verification failed for `user_namesake_unchecked_and_abs::path_unguarded`
    unsafe { u64::unchecked_mul(a, b) }
}

#[cfg(controls)]
pub fn i_unguarded(a: u32, b: u32) -> u32 {
    //[controls]~^ ERROR Trust Level 0 safety verification incomplete for `user_namesake_unchecked_and_abs::i_unguarded`: 1 obligation(s) were not proved
    //[controls]~^^ ERROR Trust strict verification failed for `user_namesake_unchecked_and_abs::i_unguarded`
    unsafe { core::intrinsics::unchecked_add(a, b) }
}

#[cfg(controls)]
pub fn i_guarded(a: u32, b: u32) -> u32 {
    if a < 10 && b < 10 { unsafe { core::intrinsics::unchecked_add(a, b) } } else { 0 }
}
