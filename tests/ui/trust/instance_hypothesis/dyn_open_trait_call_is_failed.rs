//~ NOTE "line_start":29,"col_start":0,"line_end":35,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":37,"col_start":0,"line_end":43,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
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
//! OD-1 open shapes (2026-10-04; docs/DECISION_QUEUE.md "OD-1" item 14): a VIRTUAL call
//! through a trait object an adversary can construct is not admitted (a vtable has no
//! instance inventory, so no discharge could ever charge it) and is class (c) of "L0
//! refutation rows": a downstream `impl Tr for W { fn m(&self) -> u32 { panic!() } }`
//! unsized into `&dyn Tr`, or any panicking closure as `&dyn Fn() -> u32`, makes
//! "panic-free for every value" constructively false. Before this change both rows
//! read `runtime_checked` (the witness set skipped every `Ok(Some(_))` resolution,
//! virtual ones included), so `--allow-l0-gaps` conditional-passed them. Line 1 pins
//! each stamped row by its location (`via_dyn` lines 29-35, `via_dyn_fn` lines 37-43).
//! Controls: `dyn_sealed_or_blanket_trait_stays_runtime_checked.rs`.
pub trait Tr {
    fn m(&self) -> u32;
}

pub fn via_dyn(t: &dyn Tr) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    t.m()
}

pub fn via_dyn_fn(f: &dyn Fn() -> u32) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    f()
}
