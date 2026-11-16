//~ NOTE "line_start":40,"col_start":0,"line_end":46,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":48,"col_start":0,"line_end":54,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":56,"col_start":0,"line_end":62,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":64,"col_start":0,"line_end":73,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":75,"col_start":0,"line_end":81,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
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
//! This file: the PROJECTION shapes — a `Box` deref (a transmute of its
//! `NonNull<dyn Env>`), a struct field, a slice index, an `Option` downcast and a
//! tuple field. The receiver-view CALL shapes are in
//! `dyn_receiver_through_std_view_call_is_failed.rs` (one file overran compiletest's
//! output cap). Controls: `dyn_receiver_built_locally_stays_runtime_checked.rs`.
//! Line 1 pins each stamped row by its location.
pub trait Env {
    fn arity(&self) -> u32;
}

pub struct Holder<'a> {
    pub env: &'a dyn Env,
}

pub fn a_box(env: Box<dyn Env>) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    env.arity()
}

pub fn b_field(h: &Holder<'_>) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    h.env.arity()
}

pub fn d_slice(v: &[&dyn Env]) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    v[0].arity()
}

pub fn e_option(o: Option<&dyn Env>) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    match o {
        Some(e) => e.arity(),
        None => 0,
    }
}

pub fn j_tuple(t: (u8, &dyn Env)) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    t.1.arity()
}
