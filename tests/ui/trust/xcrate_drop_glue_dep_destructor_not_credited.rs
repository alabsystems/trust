//@ needs-trust-verify
//@ aux-build:xcrate_drop_glue_dep.rs
//@ aux-build:trust_xcrate_drop_glue_dep.rs
//@ revisions: boom boom_option boom_tuple boom_nested_tuple boom_array boom_result
//@ revisions: boom_refcell boom_cell_option hollow quiet hollow_declared
//@ revisions: hollow_trust_owned_declared boom_trust_owned_declared boom_declared
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[hollow_declared] compile-flags: -Ztrust-bundle-foreign-crate=xcdrop_dep
//@[boom_declared] compile-flags: -Ztrust-bundle-foreign-crate=xcdrop_dep
//@[hollow_trust_owned_declared] compile-flags: -Ztrust-bundle-foreign-crate=trust_xcdrop_dep
//@[boom_trust_owned_declared] compile-flags: -Ztrust-bundle-foreign-crate=trust_xcdrop_dep
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@ check-fail
//! X1 (2026-09-23) — A VERIFY-OFF DEPENDENCY'S `Drop` WAS CREDITED FROM ITS MIR.
//!
//! EVERY REVISION HERE MUST STAY REFUSED. Fix the compiler, never this file.
//!
//! # The defect
//!
//! `admit_foreign_destructor` put any foreign `<T as Drop>::drop` whose MIR was
//! available into the native bundle and recorded `T` as a "bundled destructor".
//! The bridge then lowered `T`'s drop glue as `Assert(true)` — panic-free — and
//! never called the destructor body, whose own panic, as a bundle member, was
//! demanded of nobody. For the sysroot that is the disclosed TCB; for a
//! dependency it is belief. `-Zalways-encode-mir`, which `targo` injects into
//! every unit, is all it took to make a dependency's destructor "available".
//!
//! Measured on stage-1 `trustc` at `fa6661d85e`, BEFORE the fix, as a binary:
//! `drop(dep::Boom(7))` built rc=0 with ZERO warnings ("1 proved" twice) and
//! the program exited 101 ("boom"). Every `boom*` revision below built rc=0 in
//! the same way (`Some(Boom)`, `(Boom, u8)`, `((Boom,),)`, `[Boom; 1]`,
//! `Ok::<Boom, u8>`, `RefCell<Boom>`, `Cell<Option<Boom>>`), and each panicked
//! when run with 7. CONTROLS, same compiler: the same dependency built WITHOUT
//! `-Zalways-encode-mir` refused all of them, and a local copy of `Boom`
//! refused too.
//!
//! The shape is a drop that happens INSIDE a bundled sysroot body
//! (`core::mem::drop::<T>` here). A drop at the end of a scope in the verified
//! body itself was already refused, but only by the ROOT-body check
//! `body_drops_foreign_adt_argument`, which cannot see into a callee.
//!
//! # The fix
//!
//! Only a destructor defined in the compiler's own sysroot (lang-item-owning
//! `core`/`alloc`/`std`, or a crate loaded from the compiler's own target
//! library directory, such as `hashbrown`) is admitted as credit
//! (`trust_verify/foreign_destructor_admission.rs`). A dependency's destructor
//! now declines exactly as if its MIR were absent, so the member's drop-glue row
//! stays fail-closed ("drop glue for `xcdrop_dep::Boom` has unproven
//! panic-freedom").
//!
//! # The panic-free revisions are refused ON PURPOSE
//!
//! `hollow` (an empty `drop`) and `quiet` (a field write) cannot panic, and
//! they built rc=0 before the fix, through the SAME unchecked credit that let
//! `boom` through. Nothing verified those bodies, so this is a completeness
//! cost, not a lost proof. The declared-scope revisions pin that
//! `-Ztrust-bundle-foreign-crate` does not buy the credit back either:
//!
//!  * `hollow_declared` — an ordinary (`ExternalDep`) crate name. Since D4-A
//!    (2026-09-24) the declared scope re-derives `ExternalDep` bodies for the
//!    `dyn`/format bar and postcondition reuse, but that widening is WITHHELD
//!    from the drop-glue premise
//!    (`foreign_rederivation::dependency_destructor_withheld_from_rederivation`),
//!    so this revision is refused exactly as before. It must not flip, and
//!    neither may `boom_declared` (the same scope, a panicking `Drop`).
//!  * `hollow_trust_owned_declared` — a `trust_`-named crate in the declared
//!    scope. The sound re-derivation lane for this EXISTS
//!    (`drop_glue_discharges_panic_freedom`: it verifies `<T as Drop>::drop` in
//!    THIS compilation, and measured "destructor PROVES panic-free -> credited"
//!    for this body at a scope-end drop), but it is not consulted by the bundle
//!    admission. Crediting through it is a widening that belongs to the D4
//!    decision. If D4 lands that lane, THIS revision may flip to check-pass
//!    DELIBERATELY. `boom_trust_owned_declared` must never flip.
//!
//! Each `f` carries its revisions' `~ ERROR Trust strict verification failed`, so a
//! revision refused for an unrelated reason (an aux that failed to resolve, a
//! different error kind) does not satisfy this file. Measured against the
//! MIR-less model of the fix: every revision's error starts on its `f` line.
//! (Adversarial review, 2026-09-23.)
extern crate trust_xcdrop_dep;
extern crate xcdrop_dep;

#[cfg(any(boom, boom_declared))]
pub fn f(x: u32) -> u32 { //[boom,boom_declared]~ ERROR Trust strict verification failed
    let g = xcdrop_dep::Boom(x);
    let r = g.0;
    drop(g);
    r
}

#[cfg(boom_option)]
pub fn f(x: u32) -> u32 { //[boom_option]~ ERROR Trust strict verification failed
    drop(Some(xcdrop_dep::Boom(x)));
    x
}

#[cfg(boom_tuple)]
pub fn f(x: u32) -> u32 { //[boom_tuple]~ ERROR Trust strict verification failed
    drop((xcdrop_dep::Boom(x), 1u8));
    x
}

#[cfg(boom_nested_tuple)]
pub fn f(x: u32) -> u32 { //[boom_nested_tuple]~ ERROR Trust strict verification failed
    drop(((xcdrop_dep::Boom(x),),));
    x
}

#[cfg(boom_array)]
pub fn f(x: u32) -> u32 { //[boom_array]~ ERROR Trust strict verification failed
    drop([xcdrop_dep::Boom(x)]);
    x
}

#[cfg(boom_result)]
pub fn f(x: u32) -> u32 { //[boom_result]~ ERROR Trust strict verification failed
    drop(Ok::<xcdrop_dep::Boom, u8>(xcdrop_dep::Boom(x)));
    x
}

#[cfg(boom_refcell)]
pub fn f(x: u32) -> u32 { //[boom_refcell]~ ERROR Trust strict verification failed
    drop(core::cell::RefCell::new(xcdrop_dep::Boom(x)));
    x
}

#[cfg(boom_cell_option)]
pub fn f(x: u32) -> u32 { //[boom_cell_option]~ ERROR Trust strict verification failed
    drop(core::cell::Cell::new(Some(xcdrop_dep::Boom(x))));
    x
}

#[cfg(any(hollow, hollow_declared))]
pub fn f(x: u32) -> u32 { //[hollow,hollow_declared]~ ERROR Trust strict verification failed
    let g = xcdrop_dep::Hollow(x);
    let r = g.0;
    drop(g);
    r
}

#[cfg(quiet)]
pub fn f(x: u32) -> u32 { //[quiet]~ ERROR Trust strict verification failed
    let g = xcdrop_dep::Quiet(x);
    let r = g.0;
    drop(g);
    r
}

#[cfg(hollow_trust_owned_declared)]
pub fn f(x: u32) -> u32 { //[hollow_trust_owned_declared]~ ERROR Trust strict verification failed
    let g = trust_xcdrop_dep::Hollow(x);
    let r = g.0;
    drop(g);
    r
}

#[cfg(boom_trust_owned_declared)]
pub fn f(x: u32) -> u32 { //[boom_trust_owned_declared]~ ERROR Trust strict verification failed
    let g = trust_xcdrop_dep::Boom(x);
    let r = g.0;
    drop(g);
    r
}
