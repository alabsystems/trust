//@ needs-trust-verify
//@ edition: 2021
//@ revisions: s03 i04 twice helper zero contract premise
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[s03] check-pass
//@[i04] check-pass
//@[twice] check-pass
//@[helper] check-pass
//@[zero] check-fail
//@[contract] check-fail
//@[premise] check-fail
//! **A transitive Assert-bearing member whose every call site is OWNED by a local
//! body verified as its own root (Trust, 2026-09-25).**
//!
//! `x % 2` on a `&u32` calls the foreign `<&u32 as Rem<u32>>::rem`, whose body
//! carries the divide-by-zero `Assert`. When the call sits in a closure (or a
//! local helper), the ROOT's bundle reaches `rem` only through that body, and
//! `ensure_bundled_member_asserts_exactly_charged` used to refuse it: "no exact
//! direct root call can carry its derived precondition". But the closure is
//! verified as its OWN root in the same compilation, where `rem` IS a direct call
//! and its exact `Precondition` row proves. The gate now credits that site to the
//! closure's run — only under the four conjuncts in
//! `compiler/rustc_mir_transform/src/trust_verify/member_assert_ownership.rs`.
//!
//! # Before (measured on stage-1 `trustc 0.10.0+g43b8fe6ab`, 2026-09-25)
//!
//! Every revision was rc=1. In every one the ROOT was refused with
//! `refused Assert-bearing transitive member
//! `<&u32 as core::ops::arith::Rem<u32>>::rem`: no exact direct root call can
//! carry its derived precondition`, and nothing more.
//!
//! * `s03`, `i04`, `helper`: the owner's own row set was
//!   `2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2`.
//!   The root was the only error.
//! * `zero`: the closure's own `[precond] FAILED (ay-in-process); counterexample
//!   … = 0` (the divisor really can be zero), plus the root's refusal.
//! * `contract`: `rem_by` (a `requires d != 0` owner) `2 proved … 1 assumed
//!   (requires) out of 3`; the root `1 proved … out of 1` and then refused.
//! * `premise`: the closure carried `ADAPTER_YIELD` and
//!   `2 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 3`;
//!   the root refused.
//!
//! # After — PREDICTED, not yet measured (this change was written without a build)
//!
//! * `s03`, `i04`, `twice`, `helper` — POSITIVE, check-pass: the root is no
//!   longer refused. The owner's pinned row set is unchanged. The ROOT's own
//!   verdict is NOT pinned: on the snapshot, the neighbour whose member has no
//!   `Assert` (`find(|x| x & 1 == 0)`) builds rc=0 with the root's aggregate row
//!   `runtime-checked` (trust-mc cannot bound the iterator `Alloca` in the root),
//!   and that is expected here too. That residual is not this gate's.
//! * `zero` — the closure is not accepted, so it owns nothing; the root's
//!   refusal now also names why ("has not finished accepted").
//! * `contract`, `premise` — refused ON PURPOSE (rule 3): the owner's row holds
//!   only under its own `requires` / a modeled premise. Sound to widen only with
//!   its own argument; until then the refusal names the reason.
//!
//! EVERY `check-fail` REVISION MUST STAY REFUSED WITH THE PINNED NOTE. If one goes
//! green, treat it as a possible FALSE ACCEPT until shown otherwise.

#[cfg(s03)]
pub fn first_even(v: &[u32]) -> Option<u32> {
    v.iter().copied().find(|x| x % 2 == 0)
    //[s03]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
}

#[cfg(i04)]
pub fn evens(v: &[u32]) -> Vec<u32> {
    v.iter().copied().filter(|x| x % 2 == 0).collect()
    //[i04]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
}

// Two sites in one owner: the owner's charge is a call-site MULTISET.
#[cfg(twice)]
pub fn first_six(v: &[u32]) -> Option<u32> {
    v.iter().copied().find(|x| x % 2 == 0 && x % 3 == 0)
    //[twice]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 3 obligation(s)
}

// The owner is a local helper, not a closure.
#[cfg(helper)]
fn is_even(x: &u32) -> bool {
    //[helper]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
    x % 2 == 0
}

#[cfg(helper)]
pub fn check(v: &u32) -> bool {
    is_even(v)
}

#[cfg(zero)]
pub fn first_multiple(v: &[u32], d: u32) -> Option<u32> {
    //[zero]~^ ERROR Trust full verification failed
    //[zero]~| NOTE refused Assert-bearing transitive member `<&u32 as core::ops::arith::Rem<u32>>::rem`: no exact direct root call can carry its derived precondition; the site(s) in `bundled_member_assert_owned_by_own_root::first_multiple::{closure#0}` are not owned: its own verification has not finished accepted in this compilation
    v.iter().copied().find(|x| x % d == 0)
    //[zero]~^ ERROR Trust strict verification failed
    //[zero]~| NOTE [precond] FAILED
}

#[cfg(contract)]
fn rem_by(x: &u32, d: u32) -> u32 requires d != 0 {
    x % d
}

#[cfg(contract)]
pub fn half_rem(x: &u32) -> u32 {
    //[contract]~^ ERROR Trust full verification failed
    //[contract]~| NOTE refused Assert-bearing transitive member `<&u32 as core::ops::arith::Rem<u32>>::rem`: no exact direct root call can carry its derived precondition; the site(s) in `bundled_member_assert_owned_by_own_root::rem_by` are not owned: it carries a declared contract
    rem_by(x, 2)
}

#[cfg(premise)]
pub fn all_even_pairs(v: &[u32]) -> bool {
    //[premise]~^ ERROR Trust full verification failed
    //[premise]~| NOTE refused Assert-bearing transitive member `<&u32 as core::ops::arith::Rem<u32>>::rem`: no exact direct root call can carry its derived precondition; the site(s) in `bundled_member_assert_owned_by_own_root::all_even_pairs::{closure#0}` are not owned: it carries an ADAPTER_YIELD premise
    v.windows(2).all(|w| &w[0] % 2 == 0)
}
