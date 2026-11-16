//~ NOTE "proved":1,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type lib -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! Trust (EMPTY-CLOSURE-REF-VALUE-1, 2026-11-10; `docs/TCB.md`, "Source reference
//! facts"): the reference VALUE fact for the promoted shared borrow of an
//! upvar-free closure, end to end, beside the three closure-reference shapes that
//! must NOT be claimed. Each caller hands `apply` a reference to a closure; its
//! whole-function panic-freedom row is proved only when trust-mc can consume the
//! reference argument, which needs the value fact.
//!
//! * `use_empty`: `&|x| x / 2` is `const use_empty::promoted[0]`, the carrier
//!   trust-mc's `SourceReferenceValueFact` contract names: PROVED;
//! * `use_capturing`: `&move |x| (x / 2) ^ (k & 0)` captures `k`, so it is no
//!   promoted constant (and its closure type has an upvar): not claimed,
//!   runtime-checked;
//! * `use_mut`: `&mut |x| x / 2` is a unique borrow, never promoted: not claimed,
//!   runtime-checked;
//! * `use_local`: the empty closure bound to a local and borrowed at run time is
//!   no constant at all: not claimed, runtime-checked.
//!
//! Every warning is annotated, so a `Level 0 safety verification incomplete`
//! warning on `use_empty` fails this test; line 1 pins `use_empty`'s counts (one
//! proved panic-freedom aggregate beside its `apply::<{closure}>` discharge row),
//! which no other function here reaches. Without the extractor's `EmptyClosureRef`
//! arm `use_empty` is runtime-checked like the other three (measured on the stage 1
//! before the change, as `fn_bound_admitted_site_passes_strict.rs`'s `use_apply`).

pub fn apply<F: Fn(u32) -> u32>(f: &F, x: u32) -> u32 {
    //~^ WARN Trust verification advisory for `source_reference_facts_closure_value::apply`
    f(x)
}

pub fn apply_mut<F: FnMut(u32) -> u32>(f: &mut F, x: u32) -> u32 {
    //~^ WARN Trust verification advisory for `source_reference_facts_closure_value::apply_mut`
    f(x)
}

pub fn use_empty() -> u32 {
    apply(&|x: u32| x / 2, 7)
}

pub fn use_capturing(k: u32) -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `source_reference_facts_closure_value::use_capturing`
    apply(&move |x: u32| (x / 2) ^ (k & 0), 7)
}

pub fn use_mut() -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `source_reference_facts_closure_value::use_mut`
    apply_mut(&mut |x: u32| x / 2, 7)
}

pub fn use_local() -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `source_reference_facts_closure_value::use_local`
    let f = |x: u32| x / 2;
    apply(&f, 7)
}
