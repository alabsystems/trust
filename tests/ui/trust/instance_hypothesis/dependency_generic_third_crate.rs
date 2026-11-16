//@ revisions: only_b both both_plain
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: od2_dep_a.rs
//@ aux-build: od2_dep_b.rs
//@ compile-flags: -Ztrust-verify=on --crate-type=lib -Ztrust-policy=certify
//@[only_b] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_b
//@[both] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_a -Ztrust-bundle-foreign-crate=od2_dep_b
//@[both_plain] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_a -Ztrust-bundle-foreign-crate=od2_dep_b
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! OD-1 PHASE 2 REVIEW FIX (2026-10-05): `od2_dep_b::g` (`#[trust::assume_total]`)
//! reaches `od2_dep_a::f`'s site through a still-generic call into a THIRD crate.
//!
//! BEFORE (stage 1 of `20eace3baa`, certify): `only_b` BUILT rc=0 ("1 skipped out of
//! 1") and the binary panicked in `od2_dep_a`: the edge to an out-of-scope crate was
//! dropped (`foreign_scan`'s `continue`) and `g`'s axiom removed the call's row.
//! AFTER: `g`'s axiom is not read (a dependency generic), and the edge out of the
//! declared scope is an `unknown` discharge. With both crates declared the edge
//! propagates to `f`'s site; its callee `DepBad::m` was re-derived by no
//! credit-bearing check, so the discharge is `unknown` (it spends no budget).

extern crate od2_dep_a;
extern crate od2_dep_b;

pub fn use_it() -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust instance discharge not established
    //[only_b]~| NOTE runs code not re-derived here: a still-generic call to `od2_dep_a::f::<X>`, whose body is outside the declared scope [unknown]
    //[both]~| NOTE site `<X as od2_dep_a::Tr>::m` of `od2_dep_a::f::<od2_dep_a::DepBad>`
    //[both_plain]~| NOTE resolves to `<od2_dep_a::DepBad as od2_dep_a::Tr>::m` [unknown]
    //~| ERROR Trust strict verification failed
    #[cfg(any(only_b, both))]
    let r = od2_dep_b::g(&od2_dep_a::DepBad);
    #[cfg(both_plain)]
    let r = od2_dep_b::g_plain(&od2_dep_a::DepBad);
    r
}
