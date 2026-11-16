//@ revisions: default certify nochk
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@[nochk] compile-flags: -Coverflow-checks=off
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! D5-B ADVERSARIAL: helpers whose result `bit < 64` (or its twin) is TRUE of
//! their body, but which are outside what the body-inferred return lane may
//! summarize. No caller here may PROVE: every one must keep exactly the row it
//! had BEFORE D5-B (measured on stage-1 `4e9fe36bf`, all three revisions,
//! identical rows), because nothing is minted for its helper.
//!
//! Why each helper is refused:
//!
//! * `lp`: a loop (cyclic CFG) and a checked `+=`.
//! * `by_ref`: a reference parameter.
//! * `gen_guard`: generic (and a call to `Into::into`).
//! * `<Q as D>::m`: a trait method, not a free fn.
//! * `at_guard`: `#[trust::assume_total]`.
//! * `rq_guard`: an authored `requires` — an inferred clause never shares a
//!   summary with an authored contract.
//! * `nm_guard`: `#[no_mangle]` — the symbol can be interposed at link time.
//! * `ex_guard`: `#[export_name]` — same.
//! * `p1_guard`: arithmetic (`b + 1`); under `nochk` it WRAPS, so a mathematical
//!   reading `b <= 63` would be a false proof at `b = u32::MAX`.
//! * `skip_guard`: `#[trust::skip]` AND an unproven authored
//!   `ensures result == (bit < 32)` that is FALSE of the body (the
//!   `contract_skip_ensures_launder` shape): `shift32_skip` would falsely prove
//!   `x >> bit` on `u32` if either clause were assumed.
//! * `lying_guard`: the same false `ensures`, not skipped — its own postcondition
//!   row fails, so neither lane may lend it.
//!
//! The held rows are D5-A's; the two `FAILED` rows (generic / trait callees,
//! outside D5-A's census) are refutations over an unmodeled result and are
//! pinned only as "not proved". A pin going missing means a caller changed
//! row; a caller that stops erroring means something was minted that must not be.
//!
//! CONTROL, the one caller that proves: `S::inherent_guard`, an inherent
//! associated fn. 37029613c67 (decision queue, "Checked enum-return
//! composition", 2026-11-02) admits exact nongeneric inherent methods to this
//! lane on purpose: they have an exact item identity and static dispatch. Trait
//! methods and trait-impl methods (`<Q as D>::m` above) stay outside. Its
//! `b < 64` is true of the body and the row is kernel-certified.

pub fn lp(n: u32) -> bool {
    let mut i: u32 = 0;
    while i < n && i < 64 {
        i += 1;
    }
    i < 64
}

pub fn shift_loop(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `inferred_return_never_proves_nonfragment::lp`
    if !lp(bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn by_ref(r: &u32) -> bool {
    *r < 64
}

pub fn shift_by_ref(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `inferred_return_never_proves_nonfragment::by_ref`
    if !by_ref(&bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn gen_guard<T: Into<u32>>(t: T) -> bool {
    t.into() < 64
}

pub fn shift_generic(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [shift:right] FAILED (ay-in-process); counterexample:
    if !gen_guard(bit) {
        return None;
    }
    Some(x >> bit)
}

pub trait D {
    fn m(b: u32) -> bool;
}
pub struct Q;
impl D for Q {
    fn m(b: u32) -> bool {
        b < 64
    }
}

pub fn shift_trait(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [shift:right] FAILED (ay-in-process); counterexample:
    if !<Q as D>::m(bit) {
        return None;
    }
    Some(x >> bit)
}

pub struct S;
impl S {
    pub fn inherent_guard(b: u32) -> bool {
        b < 64
    }
}

pub fn shift_inherent(x: u64, bit: u32) -> Option<u64> {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    if !S::inherent_guard(bit) {
        return None;
    }
    Some(x >> bit)
}

#[trust::assume_total]
pub fn at_guard(b: u32) -> bool {
    b < 64
}

pub fn shift_assume_total(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `inferred_return_never_proves_nonfragment::at_guard`
    if !at_guard(bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn rq_guard(b: u32) -> bool
    requires b < 1000
{
    b < 64
}

pub fn shift_requires(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `inferred_return_never_proves_nonfragment::rq_guard`
    if bit >= 1000 {
        return None;
    }
    if !rq_guard(bit) {
        return None;
    }
    Some(x >> bit)
}

#[unsafe(no_mangle)]
pub fn nm_guard(b: u32) -> bool {
    b < 64
}

pub fn shift_no_mangle(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `inferred_return_never_proves_nonfragment::nm_guard`
    if !nm_guard(bit) {
        return None;
    }
    Some(x >> bit)
}

#[unsafe(export_name = "d5b_exported_guard")]
pub fn ex_guard(b: u32) -> bool {
    b < 64
}

pub fn shift_export_name(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `inferred_return_never_proves_nonfragment::ex_guard`
    if !ex_guard(bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn p1_guard(b: u32) -> bool {
    b + 1 <= 64
}

pub fn shift_plus_one(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `inferred_return_never_proves_nonfragment::p1_guard`
    if !p1_guard(bit) {
        return None;
    }
    Some(x >> bit)
}

#[trust::skip]
pub fn skip_guard(bit: u32) -> bool
    ensures result == (bit < 32)
{
    bit < 64
}

pub fn shift32_skip(x: u32, bit: u32) -> Option<u32> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `inferred_return_never_proves_nonfragment::skip_guard`
    if !skip_guard(bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn lying_guard(bit: u32) -> bool
    ensures result == (bit < 32)
{
    bit < 64
}

pub fn shift32_lying(x: u32, bit: u32) -> Option<u32> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `inferred_return_never_proves_nonfragment::lying_guard`
    if !lying_guard(bit) {
        return None;
    }
    Some(x >> bit)
}
