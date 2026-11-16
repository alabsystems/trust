//~ NOTE "line_start":48,"col_start":0,"line_end":55,"col_end":1},"outcome":"runtime_checked"
//~| NOTE "line_start":66,"col_start":0,"line_end":71,"col_end":1},"outcome":"runtime_checked"
//~| NOTE "line_start":73,"col_start":0,"line_end":83,"col_end":1},"outcome":"runtime_checked"
//~| NOTE "line_start":78,"col_start":12,"line_end":78,"col_end":29},"outcome":"runtime_checked"
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
//! OD-1 item 14 amendment control (2026-10-06, docs/DECISION_QUEUE.md
//! "OD-1-RG-CONCRETE"): the widened receiver walk (`dyn_receiver_root::argument_root`)
//! still refutes only a trait object the CALLER chose. Not here, so each row keeps the
//! disclosed `runtime_checked` label (strict and certify refuse it anyway; `Loud::arity`
//! panics, so rung 2 declines): (1) `local_box` builds its `Box<dyn Env>` itself (an
//! unsizing coercion is never a source: the vtable is the body's choice); (2)
//! `user_deref` reaches the trait object through a USER `impl Deref` that returns a
//! static of its own (only `core`/`alloc`/`std` receiver-view methods are sources);
//! (3) the closure in `closure_upvar` reads a trait object its creator built from a
//! field of its environment, which a closure-like body never treats as the caller's.
//! Line 1 pins each row by its location.
use std::ops::Deref;

pub trait Env {
    fn arity(&self) -> u32;
}

pub struct Loud;

impl Env for Loud {
    fn arity(&self) -> u32 {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete
        //[strict]~^^ ERROR Trust strict verification failed
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
        //[certify]~^^^^ ERROR Trust strict verification failed
        panic!("loud")
    }
}

static LOUD: Loud = Loud;

pub fn local_box() -> u32 {
    //[strict]~^ WARN Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    let b: Box<dyn Env> = Box::new(Loud);
    b.arity()
}

pub struct W;

impl Deref for W {
    type Target = dyn Env;
    fn deref(&self) -> &(dyn Env + 'static) {
        &LOUD
    }
}

pub fn user_deref(w: &W) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^ ERROR Trust strict verification failed
    w.arity()
}

pub fn closure_upvar() -> u32 {
    //[strict]~^ ERROR Trust strict verification failed
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^ ERROR Trust strict verification failed
    let d: &dyn Env = &Loud;
    let c = move || d.arity();
        //[strict]~^ ERROR Trust strict verification failed
        //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
        //[certify]~^^^ ERROR Trust strict verification failed
    c()
}

// RE-PINNED 2026-10-18 (the 1.101 toolchain migration): under `strict`,
// `local_box`'s Level 0 diagnostic is now a WARNING (its only unproved
// outcome is the runtime-checked row, which strict reports nonfatally at
// L0 and refuses through the strict error beside it); `Loud::arity` keeps
// the ERROR (an unknown row). The published rows on line 1 are unchanged.
// (This note lives at the end so the line-1 location pins do not move.)
