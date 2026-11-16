//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! IDENTITY GATE of the body-derived callee summaries (INTERPOSE-SUM-1,
//! 2026-10-03).
//!
//! The return upper-bound, lower-bound, const-set, discriminant, trivial-setter
//! and bool-predicate summaries each read a callee's BODY and hand every call
//! site a fact about the call. A callee whose symbol can be interposed at link
//! time (`#[no_mangle]`, `#[export_name]`) need not be the body a call runs:
//! another object can define the same symbol, and the call binds to it. D5-B
//! and the field-read summary already refuse such a callee
//! (`return_field_summary_interposable_getter_not_summarised.rs`). These six did
//! not. With `#[no_mangle] fn five() -> u32 { 5 }`, `five() + (u32::MAX - 5)` was
//! kernel-certified overflow-free under certify, and a binary that linked
//! another `five` returning 100 panicked on exactly that add (measured by the
//! wave-11 scout on macOS: `ld` reports only a duplicate-symbol warning).
//!
//! BEFORE (stage 1 of `1ab78ed8e8`, each revision's own flags plus
//! `--cfg <revision> --emit=metadata`, measured 2026-10-03): both revisions
//! exit 0. Every caller row below is proved, under certify Certified, from the
//! exported callee's body.
//!
//! AFTER (predicted; it held on the stage 1 of `936573497e`, 2026-10-04): the exported callees lend no summary, so each
//! annotated caller is refused as an unmodeled same-crate call. The prediction
//! was measured on the BEFORE compiler by a proxy: the same callers over
//! exported callees whose bodies no summary recognizer reads. `set_then_check`
//! is refused under certify only. The default policy keeps its `assert` as a
//! `runtime_checked` row, a warning.
//!
//! `add_five_clean` pins the ruling that a Clean-origin def lends none of these
//! summaries either. It is left to its own definitional lane, as D5-B and the
//! field-read lane leave it (DECISION_QUEUE INTERPOSE-SUM-1). That lane
//! (`clean_origin_call_model_of_record`) deliberately models no `ConstantUint`
//! def: a caller of one stays fail-closed until that shape's own summary
//! increment lands. Before this change, the const-set summary read the def's
//! emitted body and proved the caller anyway.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): that increment had landed on
//! the soundness line before the merge (1ee563e5b11, "a caller of a CONSTANT
//! island `def` gets its value — the ConstantUint caller summary", with its own
//! verify-on fixture `clean_origin_constant_call_summary.rs`, whose `wrong_value`
//! revision keeps the overflowing twin refused). On the merged stage 1
//! `add_five_clean` is proved (kernel-certified under certify) through
//! `clean_origin_call_model_of_record`'s `ConstantUint` arm, the definitional lane
//! this ruling left it to, so it is now a control. The six body-derived lanes still
//! lend nothing: every `#[no_mangle]` caller below stays refused.
//!
//! Controls: the `*_plain` twins, the same bodies not exported, prove before and
//! after, so neither revision may report anything for them. If an annotated row
//! starts to prove again, an interposable body has started to lend a summary.

const K5: u32 = u32::MAX - 5;
const K6: u32 = u32::MAX - 6;

// Const-set and upper-bound summaries.
#[no_mangle]
pub fn return_const_summary_five() -> u32 {
    5
}

pub fn add_five() -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    return_const_summary_five() + K5
}

#[export_name = "return_const_summary_six"]
pub fn six() -> u32 {
    6
}

pub fn add_six() -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    six() + K6
}

// Lower-bound summary: the divisor is at least 1.
#[no_mangle]
pub fn return_const_summary_den(x: u32) -> u32 {
    if x > 3 { 1 } else { 2 }
}

pub fn rem_den(h: u32, x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    h % return_const_summary_den(x)
}

// Discriminant summary: the callee always returns `Some`.
#[no_mangle]
pub fn return_const_summary_always_some() -> Option<u32> {
    Some(1)
}

pub fn unwrap_some() -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    return_const_summary_always_some().unwrap()
}

// Trivial-setter summary: `*p = v`.
#[no_mangle]
pub fn return_const_summary_set(p: &mut u32, v: u32) {
    *p = v;
}

pub fn set_then_check(v: u32) -> u32 {
    //[certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    let mut a = 0;
    return_const_summary_set(&mut a, v);
    assert!(a == v);
    a
}

// Bool-predicate summary: the result is `o.is_some()`.
#[no_mangle]
pub fn return_const_summary_has(o: Option<u32>) -> bool {
    o.is_some()
}

pub fn unwrap_if_has(o: Option<u32>) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if return_const_summary_has(o) { o.unwrap() } else { 0 }
}

// A Clean-origin def: its own definitional lane, no body-derived summary.
pub mod m {
    clean {
        def five (x : UInt32) : UInt32 := 5
    }
}

pub fn add_five_clean(x: u32) -> u32 {
    m::five(x) + K5
}

// Controls: the same bodies, not exported.
pub fn five_plain() -> u32 {
    5
}

pub fn add_five_plain() -> u32 {
    five_plain() + K5
}

pub fn den_plain(x: u32) -> u32 {
    if x > 3 { 1 } else { 2 }
}

pub fn rem_den_plain(h: u32, x: u32) -> u32 {
    h % den_plain(x)
}

pub fn always_some_plain() -> Option<u32> {
    Some(1)
}

pub fn unwrap_some_plain() -> u32 {
    always_some_plain().unwrap()
}

pub fn set_plain(p: &mut u32, v: u32) {
    *p = v;
}

pub fn set_then_check_plain(v: u32) -> u32 {
    let mut a = 0;
    set_plain(&mut a, v);
    assert!(a == v);
    a
}

pub fn has_plain(o: Option<u32>) -> bool {
    o.is_some()
}

pub fn unwrap_if_has_plain(o: Option<u32>) -> u32 {
    if has_plain(o) { o.unwrap() } else { 0 }
}
