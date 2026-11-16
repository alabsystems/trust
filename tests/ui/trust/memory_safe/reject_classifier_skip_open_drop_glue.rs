//@ needs-trust-verify
//@ aux-build: memory_safe_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! The DROP twin of `reject_classifier_skip_launders_uncharged_callee.rs`. A safe
//! field raw borrow (`&raw const s.a`) makes the classifier skip the body as
//! `TreatedAsAssumption(AddressOfField)`, and memory-safe records that skip as an
//! authenticated `assumption:addr-of-field` row only when the body has no edge out
//! of the verified closure (`memory_safe_assumption_uncharged_edges`). That check
//! looked at `Call`/`TailCall` terminators and at the masked-source scan, which
//! asks whether drop glue can PANIC outside the TCB and so answers "no" for glue it
//! cannot name. A `Drop` of a type parameter, `impl Sized` or `Box<dyn Any>`, and a
//! `BufWriter<dep::Sink>` whose std destructor flushes through the dependency's
//! `Write::write`, all passed.
//!
//! Measured on stage-1 `094125ac4` with a verify-off dependency whose `Drop` writes
//! through a null pointer: every refused body below built rc=0 with no error, the
//! same bodies without the raw borrow were refused (the native bundle charges the
//! drop), and a binary whose `main` handed `dep::Crash(7)` to
//! `generic_param_drop` through the skipped `caller_hands_dep_type` built rc=0 and
//! died with SIGSEGV in the dependency's `Drop`. The drop now counts as an edge
//! unless its glue is closed (`memory_safe_drop_glue_open_reason`).
extern crate memory_safe_unverified_dep as dep;

pub struct S {
    pub a: u32,
    pub b: u32,
}

pub fn generic_param_drop<T>(s: &S, t: T) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_open_drop_glue::generic_param_drop`
    //~| NOTE the drop glue of `T` in bb0 (`T` is a type parameter
    let _q = &raw const s.a;
    let _t = t;
    s.b
}

/// The caller that instantiates the generic at the dependency type. Its own body
/// has no open edge of its own, but the call it makes does: `generic_param_drop::<
/// dep::Crash>` drops a `dep::Crash`, and the skip is withheld. Trust (2026-10-14,
/// INSTANCE-WALK-1): this body used to keep its skip, on the argument that the local
/// item's POLYMORPHIC body is the one refused above for dropping `T`; that holds only
/// while the generic is refused, and an instance runs what its type arguments pick
/// whatever its polymorphic body's verdict. The callee's MIR is now walked at the
/// call's arguments (`unverified_edges`' instance walk).
pub fn caller_hands_dep_type(s: &S) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_open_drop_glue::caller_hands_dep_type`
    let _q = &raw const s.b;
    generic_param_drop(s, dep::Crash(7))
}

pub fn impl_sized_drop(s: &S, t: impl Sized) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_open_drop_glue::impl_sized_drop`
    //~| NOTE the drop glue of `impl Sized` in bb
    let _q = &raw const s.a;
    let _t = t;
    s.b
}

pub fn boxed_dyn_drop(s: &S, t: Box<dyn core::any::Any>) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_open_drop_glue::boxed_dyn_drop`
    //~| NOTE the drop glue of `std::boxed::Box<dyn std::any::Any>` in bb
    let _q = &raw const s.a;
    let _t = t;
    s.b
}

pub fn foundational_destructor_runs_dep_write(s: &S, w: std::io::BufWriter<dep::Sink>) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_open_drop_glue::foundational_destructor_runs_dep_write`
    //~| NOTE is instantiated at `dep::Sink`
    let _q = &raw const s.a;
    let _w = w;
    s.b
}

/// Controls: glue that runs no code outside the verified closure keeps the skip an
/// admissible memory-safe assumption — no glue at all (`T: Copy`), foundational
/// glue at foundational arguments, and a local destructor (a body of this crate,
/// verified as its own root).
pub fn copy_param_has_no_glue<T: Copy>(s: &S, t: T) -> u32 {
    let _q = &raw const s.a;
    let _t = t;
    s.b
}

pub fn foundational_glue_stays_closed(s: &S, v: Vec<u32>, t: String) -> u32 {
    let _q = &raw const s.a;
    let _v = v;
    let _t = t;
    s.b
}

pub struct Local(pub u32);

impl Drop for Local {
    fn drop(&mut self) {}
}

pub fn local_destructor_stays_closed(s: &S, l: Local) -> u32 {
    let _q = &raw const s.a;
    let _l = l;
    s.b
}
