//@ revisions: direct closure dyn_unsize std_generic drop_glue undeclared plain
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: od2_dep_axioms.rs
//@ compile-flags: -Ztrust-verify=on --crate-type=lib -Ztrust-policy=certify
//@[direct] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_axioms
//@[closure] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_axioms
//@[dyn_unsize] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_axioms
//@[std_generic] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_axioms
//@[drop_glue] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_axioms
//@[plain] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_axioms
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[direct] check-fail
//@[closure] check-fail
//@[dyn_unsize] check-fail
//@[std_generic] check-fail
//@[drop_glue] check-fail
//@[undeclared] check-fail
//@[plain] check-pass
//! OD-1 PHASE 2 REVIEW FIX (2026-10-05): a DEPENDENCY's `#[trust::assume_total]`
//! on a GENERIC item is not spent at an instance this crate creates
//! (`instance_hypothesis::dependency_generic_axiom_is_not_read`), and the
//! dependency generic's dispatch that the site inventory cannot see is charged as
//! an `unknown` discharge (`SiteKind::Opaque`) instead of being dropped.
//!
//! BEFORE (stage 1 of `20eace3baa`, same sources, `-Ztrust-policy=certify`):
//! `closure`, `dyn_unsize`, `std_generic`, `drop_glue` and `undeclared` BUILT rc=0
//! as binaries, and each panicked when run; only `direct` refused. The call to the
//! dependency generic read as one `trust-assumed-total` row, and phase 2 saw no
//! site. AFTER: the call keeps its absent-callee row (`Level 0 ... incomplete`) and,
//! where the dependency is declared, its instance discharges `unknown` on the code
//! it reaches. `plain` is the control: a NON-generic dependency axiom is the
//! documented `AssumedTotalCalleeAssumption` hole, unchanged.

extern crate od2_dep_axioms as dep;

pub fn use_it() -> u32 {
    //[direct]~^ ERROR Trust Level 0 safety verification incomplete
    //[direct]~| ERROR Trust instance discharge not established
    //[direct]~| NOTE resolves to `<od2_dep_axioms::DepBad as od2_dep_axioms::Tr>::m`
    //[direct]~| ERROR Trust strict verification failed
    //[closure]~^^^^^ ERROR Trust Level 0 safety verification incomplete
    //[closure]~| ERROR Trust instance discharge not established
    //[closure]~| NOTE runs code not re-derived here: a still-generic call to `<{closure@od2_dep_axioms::closure<X>::{closure#0}} as core::ops::function::Fn<(&X,)>>::call`, whose body is outside the declared scope [unknown]
    //[closure]~| ERROR Trust strict verification failed
    //[dyn_unsize]~^^^^^^^^^ ERROR Trust Level 0 safety verification incomplete
    //[dyn_unsize]~| ERROR Trust instance discharge not established
    //[dyn_unsize]~| NOTE runs code not re-derived here: unsizing `&X` to `&dyn Tr` [unknown]
    //[dyn_unsize]~| ERROR Trust strict verification failed
    //[std_generic]~^^^^^^^^^^^^^ ERROR Trust Level 0 safety verification incomplete
    //[std_generic]~| ERROR Trust instance discharge not established
    //[std_generic]~| NOTE runs code not re-derived here: `<X as od2_dep_axioms::Tr>::m` handed on as a value, and 1 more [unknown]
    //[std_generic]~| ERROR Trust strict verification failed
    //[drop_glue]~^^^^^^^^^^^^^^^^^ ERROR Trust Level 0 safety verification incomplete
    //[drop_glue]~| ERROR Trust instance discharge not established
    //[drop_glue]~| NOTE runs code not re-derived here: a still-generic call to `core::mem::drop::<X>`, whose body is outside the declared scope [unknown]
    //[drop_glue]~| ERROR Trust strict verification failed
    //[undeclared]~^^^^^^^^^^^^^^^^^^^^^ ERROR Trust Level 0 safety verification incomplete
    //[undeclared]~| ERROR Trust strict verification failed
    #[cfg(direct)]
    let r = dep::direct(&dep::DepBad);
    #[cfg(any(closure, undeclared))]
    let r = dep::closure(&dep::DepBad);
    #[cfg(dyn_unsize)]
    let r = dep::dyn_unsize(&dep::DepBad);
    #[cfg(std_generic)]
    let r = dep::std_generic(Some(&dep::DepBad));
    #[cfg(drop_glue)]
    let r = {
        dep::drop_glue(dep::DropBad);
        0
    };
    #[cfg(plain)]
    let r = dep::plain();
    r
}
