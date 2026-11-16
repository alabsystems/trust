//@ needs-trust-verify
//@ edition: 2021
//@ revisions: tuple_ctor variant_ctor same_named_fn
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[tuple_ctor] check-pass
//@[variant_ctor] check-pass
//@[same_named_fn] check-fail
//! **A constructor passed as a function value is total (Trust, 2026-09-27).**
//!
//! `x.checked_add(1).map(Id)` hands the tuple-struct constructor `Id` to the
//! bundled `Option::map`, which calls it through the shim
//! `<fn(u32) -> Id {Id} as FnOnce<(u32,)>>::call_once`. That shim has no MIR the
//! bundle can carry, so the bridge used to lower it as an absent callee with a
//! may-panic marker. On the ordinary sweep's t31 that marker alone kept the root
//! runtime-checked, and `certify` refused it. A constructor only moves its
//! arguments into the new value, so the compiler now records such a call as
//! compiler-total, deciding it from `DefKind::Ctor` and the `Fn`-trait lang items
//! (`collect_ctor_shim_total_calls` in `trust_verify.rs`).
//!
//! * `tuple_ctor`, `variant_ctor`: POSITIVE, check-pass under `certify`.
//! * `same_named_fn`: the DISCRIMINATING negative. A braced struct and a
//!   same-named `fn` can coexist (types and values live in different namespaces),
//!   so the spelling `{same_named_fn::Id2}` is indistinguishable from a
//!   constructor's. This `fn` CAN panic, so it must not ride the constructor
//!   grant: the call keeps its marker and `certify` refuses `next2`. `Id2` fails
//!   on its own `assert!` as well, so unannotated errors are allowed. The
//!   annotation on `next2` is the one that discriminates: if the grant wrongly
//!   applied, `next2` would verify and that annotation would go unmatched.

#[cfg(tuple_ctor)]
pub struct Id(pub u32);

#[cfg(tuple_ctor)]
pub fn next(x: u32) -> Option<Id> {
    x.checked_add(1).map(Id)
}

#[cfg(variant_ctor)]
pub enum Wrapped {
    Value(u32),
    Empty,
}

#[cfg(variant_ctor)]
pub fn wrap(x: Option<u32>) -> Option<Wrapped> {
    x.map(Wrapped::Value)
}

#[cfg(same_named_fn)]
pub struct Id2 {
    pub v: u32,
}

#[cfg(same_named_fn)]
#[allow(non_snake_case)]
pub fn Id2(v: u32) -> Id2 {
    assert!(v != 7);
    Id2 { v }
}

#[cfg(same_named_fn)]
pub fn next2(x: u32) -> Option<Id2> {
    //[same_named_fn]~^ ERROR Trust
    x.checked_add(1).map(Id2)
}
