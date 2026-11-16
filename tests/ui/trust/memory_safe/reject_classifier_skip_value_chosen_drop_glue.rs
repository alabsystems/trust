//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! The FIELD half of `reject_classifier_skip_open_drop_glue.rs`. A classifier-skipped
//! body (`&raw const s.a` -> `AddressOfField`) is recorded as an authenticated
//! memory-safe assumption only when every `Drop` in it runs closed glue
//! (`memory_safe_drop_glue_open_reason`). A foundational destructor was closed when
//! no TYPE ARGUMENT of its ADT reached foreign user code — but a sysroot destructor
//! also runs code its value's FIELDS chose: `Waker`'s calls the `RawWakerVTable::drop`
//! the value carries, and `io::Error`'s `Repr` drops a boxed `dyn Error`. Neither type
//! has an argument to ask.
//!
//! MEASURED on stage-1 `f2e5ebbc0f` (r14), with a verify-off dependency whose vtable
//! `drop` and whose boxed error's `Drop` each write through a null pointer: the two
//! skipped bodies below built rc=0 under memory-safe, each recorded as an
//! `assumption:addr-of-field` row, and a verify-off `main` handing them the
//! dependency's `Waker` / `io::Error` died with SIGSEGV (rc=139) in the dependency.
//! The same bodies without the raw borrow are refused. A foundational destructor is
//! now closed only when its WHOLE type reaches no foreign user code
//! (`foundational_destructor_foreign_reach`, shared with the print-grace scan).

pub struct S {
    pub a: u32,
    pub b: u32,
}

pub fn waker_drop(s: &S, w: std::task::Waker) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_value_chosen_drop_glue::waker_drop`
    //~| NOTE can run code the value's fields choose
    let _q = &raw const s.a;
    let _w = w;
    s.b
}

pub fn io_error_drop(s: &S, e: std::io::Error) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_value_chosen_drop_glue::io_error_drop`
    //~| NOTE can run code the value's fields choose
    let _q = &raw const s.a;
    let _e = e;
    s.b
}

pub fn io_result_drop(s: &S, r: std::io::Result<u32>) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_value_chosen_drop_glue::io_result_drop`
    let _q = &raw const s.a;
    let _r = r;
    s.b
}

/// Controls: foundational owners whose whole type reaches no foreign user code keep
/// the skip an admissible memory-safe assumption.
pub fn string_and_vec_drop(s: &S, t: String, v: Vec<u32>) -> u32 {
    let _q = &raw const s.a;
    let _t = t;
    let _v = v;
    s.b
}

pub fn hash_map_drop(s: &S, m: std::collections::HashMap<u32, u32>) -> u32 {
    let _q = &raw const s.a;
    let _m = m;
    s.b
}

pub fn boxed_and_shared_drop(s: &S, b: Box<u32>, r: std::rc::Rc<String>) -> u32 {
    let _q = &raw const s.a;
    let _b = b;
    let _r = r;
    s.b
}
