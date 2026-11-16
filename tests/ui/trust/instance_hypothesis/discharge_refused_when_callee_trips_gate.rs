//~ NOTE "outcome":"unknown","solver":"trust-classifier","time_ms":0,"reason":"the resolved callee is not proved panic-free: the body makes an unresolved indirect call, whose callee nothing verified
//~| NOTE "description":"instance discharge: site `<T as discharge_refused_when_callee_trips_gate::Tr>::m` of `discharge_refused_when_callee_trips_gate::helper::<discharge_refused_when_callee_trips_gate::Good>` (named at
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
//! OD-1 open shapes, adversarial review defect 2 (2026-10-05; DECISION_QUEUE "OD-1"
//! item 14). The shared panic-freedom evidence bar (`instance_discharges_panic_freedom`)
//! gained conjunct (6): the body trips no indirect-call gate. `<Boom as Tr>::m` calls
//! `u32::div_euclid` through a pointer, so it can divide by zero; its only row is a
//! `native-verification-gap` `unknown` (not a safety disposition) and strict refuses
//! it at the gate. Before, the bar read its ledger as clean and the instance discharge
//! of `helper::<Boom>` was `proved`, as was the closure's under the `Fn*` admission
//! (`apply::<{closure}>`). Now both discharges are not established, with the gate reason
//! (line 1; re-pinned 2026-10-15 to the merged compiler's wording of the same gate, "the
//! body makes an unresolved indirect call") and an error on the fail-closed lanes. Since
//! DISCHARGE-NO-EVIDENCE-1 (2026-10-19) they read `unknown`, not `failed`: nothing in
//! `Boom::m`'s or the closure's ledger is evidence of a panic (the gate refuses them for
//! what nobody verified), so the row carries the callee's own `unknown` instead of
//! reading as a refutation (line 1's outcome). Control: `helper::<Good>`'s discharge
//! stays `proved` (line 2's row carries it; the pin above matches only the refusal
//! reason).
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Boom(pub u32);
impl Tr for Boom {
    fn m(&self) -> u32 {
        //[strict]~^ ERROR Trust strict verification failed
        //[certify]~^^ ERROR Trust strict verification failed
        let p: fn(u32, u32) -> u32 = u32::div_euclid;
        p(100, self.0)
    }
}

pub struct Good;
impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

pub fn apply<F: Fn(u32) -> u32>(f: &F, x: u32) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `discharge_refused_when_callee_trips_gate::apply`
    f(x)
}

pub fn helper<T: Tr>(t: &T) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `discharge_refused_when_callee_trips_gate::helper`
    t.m()
}

pub fn use_h(b: &Boom) -> u32 {
    //[strict]~^ ERROR Trust instance discharge not established for `discharge_refused_when_callee_trips_gate::use_h`
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^ ERROR Trust instance discharge not established for `discharge_refused_when_callee_trips_gate::use_h`
    //[certify]~^^^^ ERROR Trust strict verification failed
    helper(b)
}

pub fn use_good() -> u32 {
    helper(&Good)
}

pub fn use_f(y: u32) -> u32 {
    //[strict]~^ ERROR Trust instance discharge not established for `discharge_refused_when_callee_trips_gate::use_f`
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^ ERROR Trust instance discharge not established for `discharge_refused_when_callee_trips_gate::use_f`
    //[certify]~^^^^ ERROR Trust strict verification failed
    apply(
        &|x: u32| {
            //[strict]~^ ERROR Trust strict verification failed for `discharge_refused_when_callee_trips_gate::use_f::{closure#0}`
            //[certify]~^^ ERROR Trust strict verification failed for `discharge_refused_when_callee_trips_gate::use_f::{closure#0}`
            let p: fn(u32, u32) -> u32 = u32::div_euclid;
            p(100, x)
        },
        y,
    )
}
