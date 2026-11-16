//~ NOTE "description":"assertion: [trust-absent-callee-assumption] call to absent callee `pointer_to_generic_carrier_refused_at_gate::helper::<T>` (body not in the lowered bundle) may panic"
//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 open shapes, adversarial review defects 1 and 3 (2026-10-05; DECISION_QUEUE
//! "OD-1" item 14). A fn pointer this body reified from a LOCAL GENERIC item is no
//! longer "verified as its own root" at the indirect-call gate
//! (`indirect_callee_is_a_reified_constant` now asks the per-instance question the
//! type-argument route asks, `local_fn_item_type_arg_is_unverified_instance`).
//!
//! `helper2<T: Tr2>` carries the instance hypothesis `<T as Tr2>::m2`. Before: `helper`
//! reified `helper2::<T>` and called it, published NO hypothesis for `m2` (only a
//! `native-verification-gap` `unknown` row the gate's carve-out tolerated), and passed
//! strict; on the open-shapes branch `caller`'s call to `helper::<T>` was then LOWERED
//! under `helper`'s hypotheses (`Tr::m` only) and `caller` passed strict while `m2`
//! was named nowhere — a `T` whose `m2` panics made `caller` panic with its published
//! condition true. Now: `helper`, `only_ptr` and the concrete `concrete_ptr` are
//! refused by strict and certify at the gate; `helper` trips the gate, so
//! `via_call_admits` declines and `caller` keeps its absent-callee row (line 1).
//! Control: `plain_ptr`, a pointer to a NON-generic local fn, still passes strict.
pub trait Tr {
    fn m(&self) -> u32;
}
pub trait Tr2 {
    fn m2(&self) -> u32;
}

pub fn helper2<T: Tr2>(t: &T) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `pointer_to_generic_carrier_refused_at_gate::helper2`
    t.m2()
}

pub fn helper<T: Tr + Tr2>(t: &T) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `pointer_to_generic_carrier_refused_at_gate::helper`
    //[certify]~^^ ERROR Trust certify verification failed for `pointer_to_generic_carrier_refused_at_gate::helper`
    //[certify]~^^^ ERROR Trust strict verification failed for `pointer_to_generic_carrier_refused_at_gate::helper`
    let f: fn(&T) -> u32 = helper2::<T>;
    let a = f(t);
    let b = t.m();
    a.wrapping_add(b)
}

pub fn caller<T: Tr + Tr2>(t: &T) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `pointer_to_generic_carrier_refused_at_gate::caller`
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^ ERROR Trust certify verification failed for `pointer_to_generic_carrier_refused_at_gate::caller`
    //[certify]~^^^^ ERROR Trust strict verification failed for `pointer_to_generic_carrier_refused_at_gate::caller`
    helper(t)
}

pub fn only_ptr<T: Tr2>(t: &T) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `pointer_to_generic_carrier_refused_at_gate::only_ptr`
    //[certify]~^^ ERROR Trust strict verification failed for `pointer_to_generic_carrier_refused_at_gate::only_ptr`
    let f: fn(&T) -> u32 = helper2::<T>;
    f(t)
}

pub struct X;
impl Tr2 for X {
    fn m2(&self) -> u32 {
        2
    }
}

pub fn concrete_ptr(x: &X) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `pointer_to_generic_carrier_refused_at_gate::concrete_ptr`
    //[certify]~^^ ERROR Trust strict verification failed for `pointer_to_generic_carrier_refused_at_gate::concrete_ptr`
    let f: fn(&X) -> u32 = helper2::<X>;
    f(x)
}

fn plain(x: u32) -> u32 {
    x / 2
}

// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[certify,strict]~vv ERROR Trust strict verification failed for `pointer_to_generic_carrier_refused_at_gate::plain_ptr`
//[certify,strict]~v NOTE this function has no obligation of its own
pub fn plain_ptr(y: u32) -> u32 {
    let f: fn(u32) -> u32 = plain;
    f(y)
}
