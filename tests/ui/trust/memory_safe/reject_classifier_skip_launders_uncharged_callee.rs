//@ needs-trust-verify
//@ aux-build: memory_safe_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! The classifier-skip twin of `reject_lowering_gap_launders_uncharged_callee.rs`.
//! A safe raw borrow of a FIELD (`&raw const s.a`, `addr_of!(s.a)`, `&raw mut s.b`)
//! makes `supportability::classify` return `AddressOfField`, so the body is skipped
//! as `TreatedAsAssumption` and never lowered. Memory-safe recorded that skip as an
//! authenticated `assumption:addr-of-field` row, so the body's call into a
//! verify-off dependency was never charged. Measured on stage-1 436c9eb6d0 (and on
//! the 265b5afb4 / 321aaeda7 toolchains): all four refused bodies below built rc=0
//! with no error and no warning, the same bodies without the field raw-borrow are
//! refused on the `deref_raw`/`get` charge, and a memory-safe binary built this way
//! read a dangling pointer (SIGSEGV). The skip row now stands only for a body with no
//! edge out of the verified closure (`memory_safe_assumption_uncharged_edges`), the
//! rule the `assumption:native-lowering` collapse already follows.
extern crate memory_safe_unverified_dep as dep;

pub struct S {
    pub a: u32,
    pub b: u32,
}

pub fn addr_of_field_then_dep_read(s: &S, p: *const u32) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_launders_uncharged_callee::addr_of_field_then_dep_read`
    //~| NOTE `dep::deref_raw` in bb
    let _q = &raw const s.a;
    dep::deref_raw(p)
}

pub fn addr_of_field_then_dep_ub(s: &S) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_launders_uncharged_callee::addr_of_field_then_dep_ub`
    //~| NOTE `dep::get` in bb
    let _q = &raw const s.b;
    dep::get()
}

pub fn addr_of_macro_then_dep_read(s: &S, p: *const u32) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_launders_uncharged_callee::addr_of_macro_then_dep_read`
    let _q = core::ptr::addr_of!(s.a);
    dep::deref_raw(p)
}

pub fn raw_mut_field_then_dep_ub(s: &mut S) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_launders_uncharged_callee::raw_mut_field_then_dep_ub`
    let _q = &raw mut s.b;
    dep::get()
}

/// The skipped body reaches the dependency through a std consumer, not a direct
/// call: `Option::<dep::Boom>::unwrap_or_default` runs the dependency's `Default`.
/// rc=0 on stage-1 436c9eb6d0.
pub fn addr_of_field_then_dep_default(s: &S, o: Option<dep::Boom>) -> u32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_launders_uncharged_callee::addr_of_field_then_dep_default`
    //~| NOTE `std::option::Option::<T>::unwrap_or_default` in bb
    let _q = &raw const s.a;
    o.unwrap_or_default().0
}

/// Control: the same skip with no call out of the body stays an admissible
/// memory-safe assumption.
pub fn addr_of_field_only(s: &S) -> u32 {
    let _q = &raw const s.a;
    s.b
}
