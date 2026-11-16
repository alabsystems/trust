//~ NOTE "line_start":37,"col_start":0,"line_end":43,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":45,"col_start":0,"line_end":51,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":53,"col_start":0,"line_end":60,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":62,"col_start":0,"line_end":72,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
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
//! OD-1 item 14 amendment (2026-10-06, docs/DECISION_QUEUE.md "OD-1-RG-CONCRETE"):
//! a virtual call on an open, exported trait refutes as class (c) of "L0 refutation
//! rows" however the body reads the caller's trait object out of its arguments, not
//! only through dereferences of a `&dyn` argument. Each function below is public, so a
//! downstream `impl Env for W { fn arity(&self) -> u32 { panic!() } }` handed in makes
//! it panic. Before the amendment every row here read `runtime_checked` (item 14's
//! receiver walk accepted dereferences only), so `--allow-l0-gaps` conditional-passed
//! them; measured on stage 1 `c797f90c1`.
//! This file: the receiver-view CALL shapes — `Index::index` on a `Vec`,
//! `<Arc as Deref>::deref`, a `&Box` read after a concrete call, and a for-loop
//! (`into_iter` + `next`). The PROJECTION shapes are in
//! `dyn_receiver_reached_through_argument_is_failed.rs`. Controls:
//! `dyn_receiver_built_locally_stays_runtime_checked.rs`. Line 1 pins each stamped
//! row by its location.
use std::sync::Arc;

pub trait Env {
    fn arity(&self) -> u32;
}

pub fn c_vec(v: &Vec<Box<dyn Env>>) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    v[0].arity()
}

pub fn f_arc(e: Arc<dyn Env>) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    e.arity()
}

pub fn g_box_ref(v: &mut Vec<u32>, env: &Box<dyn Env>) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    v.push(1);
    env.arity()
}

pub fn h_iter(v: &[Box<dyn Env>]) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    let mut s = 0u32;
    for e in v {
        s = s.wrapping_add(e.arity());
    }
    s
}
