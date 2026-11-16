//@ revisions: strict
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The NET under `fn_bound_admitted_site_passes_strict.rs` (EMPTY-CLOSURE-REF-VALUE-1;
//! MAIN-UI-BLIND-WINDOW-REDS-1, docs/DECISION_QUEUE.md). That file's `use_apply` proves
//! because the promoted borrow of an upvar-free closure now carries a source-reference
//! VALUE fact (`ConstValue::EmptyClosureRef`), which lets trust-mc's operand-consumption
//! guard pass the reference to `apply`. The
//! fact says only that the pointer's bits are initialized, so it must not let a panic
//! in the closure through: each caller below that hands `apply` a panicking closure
//! keeps its whole-function row unproved (its `Level 0 ... incomplete` warning is
//! pinned; trust-mc now reports a counterexample for `n3` and `n6`, where before the
//! fix it stopped at the fail-closed operand consumption), and its instance discharge
//! fails. `n2_good` is the positive twin and carries no annotation, so a warning there
//! fails this file. `n4_refref` (`&&{closure}`) and `n5_inline` (an inline `const`,
//! not a promoted) are outside the extractor's admitted shape and stay refused as
//! before. Edition 2021 so `panic!` lowers through `panic_fmt`, as in ordinary code.
pub fn apply<F: Fn(u32) -> u32>(f: &F, x: u32) -> u32 {
    //~^ WARN Trust verification advisory for `fn_bound_promoted_closure_value_fact_controls::apply`: 1 instance hypothesis row(s)
    f(x)
}

// n1: the closure panics on the argument passed (7 > 3).
pub fn n1_panics() -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `fn_bound_promoted_closure_value_fact_controls::n1_panics`: 1 obligation(s) were not proved
    //~| WARN Trust verification advisory for `fn_bound_promoted_closure_value_fact_controls::n1_panics`
    //~| ERROR Trust instance discharge not established for `fn_bound_promoted_closure_value_fact_controls::n1_panics`
    apply(&|x: u32| if x > 3 { panic!("bad") } else { x }, 7)
    //~^ ERROR Trust Level 0 safety verification incomplete for `fn_bound_promoted_closure_value_fact_controls::n1_panics::{closure#0}`
    //~| ERROR Trust strict verification failed for `fn_bound_promoted_closure_value_fact_controls::n1_panics::{closure#0}`
}

// n2: the positive twin of `use_apply`: proved, so no diagnostic.
pub fn n2_good() -> u32 {
    apply(&|x: u32| x / 2, 7)
}

// n3: division by the argument, which is 0.
pub fn n3_div_zero() -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `fn_bound_promoted_closure_value_fact_controls::n3_div_zero`: 1 obligation(s) were not proved
    //~| WARN Trust verification advisory for `fn_bound_promoted_closure_value_fact_controls::n3_div_zero`
    //~| ERROR Trust instance discharge not established for `fn_bound_promoted_closure_value_fact_controls::n3_div_zero`
    apply(&|x: u32| 100 / x, 0)
    //~^ ERROR Trust Level 0 safety verification incomplete for `fn_bound_promoted_closure_value_fact_controls::n3_div_zero::{closure#0}`
    //~| ERROR Trust strict verification failed for `fn_bound_promoted_closure_value_fact_controls::n3_div_zero::{closure#0}`
}

// n4: a promoted `&&{closure}`: not the admitted shape.
pub fn n4_refref() -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `fn_bound_promoted_closure_value_fact_controls::n4_refref`: 1 obligation(s) were not proved
    //~| WARN Trust verification advisory for `fn_bound_promoted_closure_value_fact_controls::n4_refref`
    //~| ERROR Trust instance discharge not established for `fn_bound_promoted_closure_value_fact_controls::n4_refref`
    apply(&&|x: u32| x / 2, 7)
}

// n5: an inline `const { &{closure} }`: an `Unevaluated` that is not a promoted.
pub fn n5_inline() -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `fn_bound_promoted_closure_value_fact_controls::n5_inline`: 1 obligation(s) were not proved
    //~| WARN Trust verification advisory for `fn_bound_promoted_closure_value_fact_controls::n5_inline`
    apply(const { &|x: u32| x / 2 }, 7)
}

// n6: the closure overflows on the argument.
pub fn n6_overflow() -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `fn_bound_promoted_closure_value_fact_controls::n6_overflow`: 1 obligation(s) were not proved
    //~| WARN Trust verification advisory for `fn_bound_promoted_closure_value_fact_controls::n6_overflow`
    //~| ERROR Trust instance discharge not established for `fn_bound_promoted_closure_value_fact_controls::n6_overflow`
    apply(&|x: u32| x + u32::MAX, 7)
    //~^ ERROR Trust Level 0 safety verification incomplete for `fn_bound_promoted_closure_value_fact_controls::n6_overflow::{closure#0}`
    //~| ERROR Trust strict verification failed for `fn_bound_promoted_closure_value_fact_controls::n6_overflow::{closure#0}`
}
