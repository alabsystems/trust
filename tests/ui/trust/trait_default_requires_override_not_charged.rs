//@ revisions: exact_override exact_override_certify both_impls
//@ revisions: default_body_certify generic_caller dyn_caller override_owes_certify
//@ revisions: override_divides_certify through_helper_certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[exact_override_certify] compile-flags: -Ztrust-policy=certify
//@[default_body_certify] compile-flags: -Ztrust-policy=certify
//@[override_owes_certify] compile-flags: -Ztrust-policy=certify
//@[override_divides_certify] compile-flags: -Ztrust-policy=certify
//@[through_helper_certify] compile-flags: -Ztrust-policy=certify
//@[exact_override] check-pass
//@[exact_override_certify] check-pass
//@[through_helper_certify] check-pass
//@[both_impls] check-fail
//@[default_body_certify] check-fail
//@[generic_caller] check-fail
//@[dyn_caller] check-fail
//@[override_owes_certify] check-fail
//@[override_divides_certify] check-fail
//@[both_impls] forbid-output: for `trait_default_requires_override_not_charged::kc`
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! DEFAULT-REQUIRES-OVERRIDE-CHARGE-1 (docs/KNOWN_HAZARDS.md, "FIX PREPARED
//! 2026-10-06 … a trait default's `requires` was charged at a call that runs an
//! override"): the direct-call lane (`add_direct_call_contract_summaries`) reads
//! the contract of the item a call NAMES. A concrete call to a trait method
//! (`c.q(x)`, `<C as Tq>::q(&C, x)`, `C::q(&C, x)`) names the trait item, whose
//! `DefId` is the default body's, so the caller was charged the default's
//! `requires x != 0` although the call runs `C`'s override, which does not have
//! the clause and is not verified under it (`override_divides_certify`: the
//! override's own `1000 / x` is `[divzero] FAILED` at `x = 0`). `kq(&C, 0)` returns
//! 0 (the witness, `trait_default_requires_override_not_charged_run.rs`).
//!
//! BEFORE (the stage 1 of `46e9afaf95`, `scratchpad/stage1-w21before`, measured
//! 2026-10-06 by compiling each revision with its flags plus `--cfg <revision>
//! --emit=metadata`): `exact_override` and `exact_override_certify` exit 1, with
//! `kq`, `k_ufcs` and `k_path` each refused on `[precond] FAILED`, counterexample
//! `x = 0` (the row names `<C as Tq>::q`); `both_impls` exits 1 with `kc` refused the
//! same way (its `forbid-output` line), and `kboth` carries `2× [precond] FAILED`.
//! The other revisions exit 1 and carry every annotated error, and are expected to
//! after the fix too (`kdiv` is refused on `[precond] FAILED` before, and on the
//! absent-callee `runtime-checked` row of the refused override after). Unannotated
//! errors are not pinned: each refusal's Level 0 twin, and in `dyn_caller` a refusal
//! of `Tq::q` itself (an `unknown` spawn-census row through the `dyn` principal).
//!
//! AFTER (predicted; no stage 1 with the fix was built): a call that names a trait
//! default owing a `requires` and runs an override owing none is not charged the
//! default's clause (`trait_impl_requires::call_resolves_to_requires_free_override`).
//! `exact_override` and `exact_override_certify` build exit 0; `both_impls` keeps
//! `ka`'s and `kboth`'s charge (their `a.q(x)` runs the default body) and drops
//! `kc`'s. The predicted verdicts were MEASURED on the same BEFORE compiler with a
//! stand-in that makes the contract lane see what the fix makes it see: the trait
//! default written WITHOUT a `requires` (`if x != 0 { 100 / x } else { 0 }`), the
//! override and callers unchanged, at the same flags. `exact_override` and
//! `exact_override_certify` exited 0 there, each caller `1 proved, 0 failed`, and
//! `override_divides_certify` exited 1 carrying every annotated error.
//!
//! `through_helper_certify` (check-pass, added 2026-10-09) pins the second site, the
//! transitive trace walk in the same function. `kw` calls `c.q(x)` directly and through
//! the local `helper`, whose body the float tracer attaches, so the walk visits
//! `helper`'s `c.q(x)`. The DB is keyed by name, so if the walk registered the default's
//! contract under `<C as Tq>::q`, `kw`'s direct call would be charged again. BEFORE
//! (re-measured 2026-10-09 on `stage1-w21before`, these flags): exit 1, with `helper` and
//! `kw` each refused on `[precond] FAILED`, counterexample `x = 0`. AFTER (predicted):
//! exit 0. The stand-in above, applied to this revision's code, built exit 0 under
//! certify with `helper` and `kw` each `1 proved, 0 failed`.
//!
//! Controls that keep the charge, before and after:
//! * `default_body_certify`: `impl Tq for A {}`, so `a.q(x)` runs the default body,
//!   which assumes the clause;
//! * `generic_caller`: `t.q(x)` with `T: Tq` is not resolved (`Ok(None)`);
//! * `dyn_caller`: `c.q(x)` with `c: &dyn Tq` resolves to `Virtual`;
//! * `override_owes_certify`: an override with a `requires` of its own is refused at
//!   the impl, and its caller keeps the DEFAULT's charge; no `Precondition` row is
//!   minted from the impl's clause (DECISION_QUEUE ADVISORY-REQUIRES-INSTANCE);
//! * `override_divides_certify`: the override owes nothing but divides by `x`; it is
//!   refused on its own `[divzero]` row, so the clause is not inherited.

#![allow(dead_code)]

pub trait Tq {
    fn q(&self, x: u32) -> u32
        requires x != 0
    {
        100 / x
    }
}

#[cfg(any(exact_override, exact_override_certify, both_impls, dyn_caller, through_helper_certify))]
pub struct C;
#[cfg(any(exact_override, exact_override_certify, both_impls, dyn_caller, through_helper_certify))]
impl Tq for C {
    fn q(&self, x: u32) -> u32 {
        x
    }
}

#[cfg(any(exact_override, exact_override_certify))]
pub fn kq(c: &C, x: u32) -> u32 {
    c.q(x)
}
#[cfg(any(exact_override, exact_override_certify))]
pub fn k_ufcs(x: u32) -> u32 {
    <C as Tq>::q(&C, x)
}
#[cfg(any(exact_override, exact_override_certify))]
pub fn k_path(x: u32) -> u32 {
    C::q(&C, x)
}

#[cfg(any(both_impls, default_body_certify, generic_caller))]
pub struct A;
#[cfg(any(both_impls, default_body_certify, generic_caller))]
impl Tq for A {}

#[cfg(both_impls)]
pub fn kc(c: &C, x: u32) -> u32 {
    c.q(x)
}
#[cfg(both_impls)]
pub fn ka(a: &A, x: u32) -> u32 {
    //[both_impls]~^ ERROR Trust strict verification failed for `trait_default_requires_override_not_charged::ka`
    //[both_impls]~| NOTE [precond] FAILED
    a.q(x)
}
#[cfg(both_impls)]
pub fn kboth(c: &C, a: &A, x: u32) -> u32 {
    //[both_impls]~^ ERROR Trust strict verification failed for `trait_default_requires_override_not_charged::kboth`
    //[both_impls]~| NOTE [precond] FAILED
    c.q(x) ^ a.q(x)
}

#[cfg(default_body_certify)]
pub fn ka(a: &A, x: u32) -> u32 {
    //[default_body_certify]~^ ERROR Trust strict verification failed for `trait_default_requires_override_not_charged::ka`
    //[default_body_certify]~| NOTE [precond] FAILED
    a.q(x)
}

#[cfg(generic_caller)]
pub fn k_gen<T: Tq>(t: &T, x: u32) -> u32 {
    //[generic_caller]~^ ERROR Trust strict verification failed for `trait_default_requires_override_not_charged::k_gen`
    //[generic_caller]~| NOTE [precond] FAILED
    t.q(x)
}

#[cfg(dyn_caller)]
pub fn kd(c: &dyn Tq, x: u32) -> u32 {
    //[dyn_caller]~^ ERROR Trust strict verification failed for `trait_default_requires_override_not_charged::kd`
    //[dyn_caller]~| NOTE [precond] FAILED
    c.q(x)
}

#[cfg(override_owes_certify)]
pub struct S;
#[cfg(override_owes_certify)]
impl Tq for S {
    fn q(&self, x: u32) -> u32 requires x > 5 {
        //[override_owes_certify]~^ ERROR a `requires` on a trait impl method is charged to no caller
        100 / (x - 5)
    }
}
#[cfg(override_owes_certify)]
pub fn ks(s: &S, x: u32) -> u32 {
    //[override_owes_certify]~^ ERROR Trust strict verification failed for `trait_default_requires_override_not_charged::ks`
    //[override_owes_certify]~| NOTE [precond] FAILED
    s.q(x)
}

#[cfg(override_divides_certify)]
pub struct D;
#[cfg(override_divides_certify)]
impl Tq for D {
    fn q(&self, x: u32) -> u32 {
        //[override_divides_certify]~^ ERROR Trust strict verification failed for `<trait_default_requires_override_not_charged::D as trait_default_requires_override_not_charged::Tq>::q`
        //[override_divides_certify]~| NOTE [divzero] FAILED
        1000 / x
    }
}
#[cfg(override_divides_certify)]
pub fn kdiv(d: &D, x: u32) -> u32 {
    //[override_divides_certify]~^ ERROR Trust strict verification failed for `trait_default_requires_override_not_charged::kdiv`
    d.q(x)
}

#[cfg(through_helper_certify)]
fn helper(c: &C, x: u32) -> u32 {
    c.q(x)
}
#[cfg(through_helper_certify)]
pub fn kw(c: &C, x: u32) -> u32 {
    helper(c, x) ^ c.q(x)
}
