//~ NOTE "line_start":64,"col_start":0,"line_end":70,"col_end":1},"outcome":"runtime_checked"
//~| NOTE "proved":0,"failed":0,"unknown":2,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
//~| NOTE "line_start":88,"col_start":0,"line_end":95,"col_end":1},"outcome":"runtime_checked"
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
//! OD-1 open shapes control (2026-10-04): a virtual call is a class (c) refutation only
//! when an adversary can supply the impl (`virtual_dispatch_is_adversarial`). Not here:
//! (1) `Private` is not exported, so its impl set is closed (sealed); `private_dyn`
//! carries no absent-callee row at all (line 1, second pin: only the spawn-census row
//! and the global-alloc row); (2) `Blanket` has a blanket impl, and the predicate errs
//! toward NOT refuting there, so `blanket_dyn`'s row stays `runtime_checked` (line 1,
//! first pin), which strict and certify refuse anyway; (3) `local_dyn` calls an OPEN
//! trait through a trait object it builds ITSELF (`&Loud as &dyn Open`): no caller
//! chooses that value, so no adversary exists (`dyn_receiver_root::argument_root`); `Loud::o`
//! panics, so rung 2 declines and the row stays `runtime_checked` (line 1, third pin).
trait Private {
    fn m(&self) -> u32;
}

pub struct S;

impl Private for S {
    fn m(&self) -> u32 {
        1
    }
}

fn private_dyn(t: &dyn Private) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    t.m()
}

pub fn use_private() -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    private_dyn(&S)
}

pub trait Blanket {
    fn b(&self) -> u32;
}

impl<T: Clone> Blanket for T {
    fn b(&self) -> u32 {
        2
    }
}

pub fn blanket_dyn(t: &dyn Blanket) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    t.b()
}

pub trait Open {
    fn o(&self) -> u32;
}

pub struct Loud;

impl Open for Loud {
    fn o(&self) -> u32 {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete
        //[strict]~^^ ERROR Trust strict verification failed
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
        //[certify]~^^^^ ERROR Trust strict verification failed
        panic!("loud")
    }
}

pub fn local_dyn() -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    let d: &dyn Open = &Loud;
    d.o()
}
