//@ needs-trust-verify
//@ edition: 2021
//@ aux-build:xcsealed_dep.rs
//@ aux-build:xcrate_shape_dep.rs
//@ aux-build:xcsealed_blanket_dep.rs
//@ revisions: bin_ok undeclared dep_boom dep_blanket lib_consumer local_bad dyn_root
//@ revisions: unsized_self
//@ compile-flags: -Ztrust-verify=on
//@[bin_ok] compile-flags: -Ztrust-bundle-foreign-crate=xcsealed_dep
//@[dep_boom] compile-flags: -Ztrust-bundle-foreign-crate=xcshape_dep
//@[dep_blanket] compile-flags: -Ztrust-bundle-foreign-crate=xcsealed_blanket_dep
//@[lib_consumer] compile-flags: --crate-type lib -Ztrust-bundle-foreign-crate=xcsealed_dep
//@[local_bad] compile-flags: -Ztrust-bundle-foreign-crate=xcsealed_dep
//@[dyn_root] compile-flags: -Ztrust-bundle-foreign-crate=xcsealed_dep
//@[unsized_self] compile-flags: -Ztrust-bundle-foreign-crate=xcsealed_dep
//@ dont-check-compiler-stderr
//@[undeclared] dont-require-annotations: ERROR
//@[dep_boom] dont-require-annotations: ERROR
//@[dep_blanket] dont-require-annotations: ERROR
//@[lib_consumer] dont-require-annotations: ERROR
//@[local_bad] dont-require-annotations: ERROR
//@[dyn_root] dont-require-annotations: ERROR
//@[unsized_self] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[bin_ok] check-fail
//@[undeclared] check-pass
//@[dep_boom] check-pass
//@[dep_blanket] check-pass
//@[lib_consumer] check-pass
//@[local_bad] check-fail
//@[dyn_root] check-fail
//@[unsized_self] check-pass
//! D4 increment B (2026-09-25) — RUNG 2 (sealed enumeration) for a FOREIGN
//! trait with NO `#[trust::panic_free]` declaration, at a GENERIC call site in a
//! WHOLE-PROGRAM artifact (`trust_verify/foreign_trait_closure.rs`, rung
//! `Sealed`). `dyn_trait_sealedness` answers `Open` for every foreign trait —
//! no seal is visible from here — so the impl set is closed by ENUMERATION
//! instead: every impl in the loaded crate graph, no blanket impl, and every
//! dispatch target, local or foreign, through the shared bar; each foreign one
//! RE-DERIVED here. Every dependency is built `-Ztrust-verify=off`.
//!
//! EVERY `check-fail` REVISION MUST STAY REFUSED. Fix the compiler, never this
//! file.
//!
//! Measured BEFORE (stage-1 snapshot `43b8fe6ab`, current main without D4-B,
//! compiletest-equivalent harness): EVERY revision refused, `bin_ok` included —
//! `f`'s `<X as Shape>::area` stayed the fatal generic absent-callee row, with
//! `TRUST_RUNG2_PROBE` printing `sealedness=Open`. A LOCAL copy of `bin_ok`
//! built rc=0 on the same compiler (rung 2 seals a local trait in a binary).
//! The first D4-B build (`b0cc6b172`) and the post-review fix measured every
//! revision as annotated.
//!
//! * `bin_ok` — check-pass: impls are `xcsealed_dep::Sq` (re-derived) and the
//!   local `Mine` (its own verdict, through the same bar).
//! * `undeclared` — `xcsealed_dep` not declared: `Sq` cannot be re-derived.
//! * `dep_boom` — the dependency also has `Boom`, which panics and is never
//!   constructed (`auxiliary/xcrate_shape_dep.rs`).
//! * `dep_blanket` — the dependency has a blanket impl: outside rung 2's
//!   enumerability premise, whatever its body does (it is total here).
//! * `lib_consumer` — an rlib: a crate compiled later could add an impl.
//! * `local_bad` — the LOCAL impl panics: rung 2 has no declaration to enforce
//!   at the impl, so the local target goes through the bar and refuses there.
//! * `dyn_root` / `unsized_self` — the virtual shape, and the generic shape a
//!   monomorphization can turn into it: never served for a foreign trait.
//!
//! Every refused `f` row's Level-0 label is `failed` ("1 failed"): a call the
//! closure discharges leaves no row, so a remaining row is one it declined —
//! `dep_boom` and `local_bad` on a real panicking impl. MEASURED on the first
//! D4-B build (`b0cc6b172`): a label exemption keyed on the closure's STRUCTURE
//! demoted `undeclared` and `dep_boom` to a WARNING, "0 failed … 1
//! runtime-checked"; withdrawn by the post-review fix.
//!
//! OD-1 PHASE 1 (2026-10-04; docs/DECISION_QUEUE.md "OD-1"). The ruling admits a
//! generic call site exactly when "rung 1, rung 2 and D4-B declined" (design §2.3):
//! the call this file pins is such a site, so `f` no longer claims panic-freedom for
//! every instantiation — it publishes one `assumption:instance-hypothesis` row and the
//! declined closure no longer refuses the build; each revision below that used to be
//! refused ONLY on that row now passes CONDITIONALLY (the WARN pin on `f`). The
//! panicking impls are charged where an instance is NAMED: `main` names `f::<Mine>`,
//! whose discharge row is proved; a program naming `f::<Bad>` gets a `failed`
//! discharge and a strict error (`tests/ui/trust/instance_hypothesis/
//! discharge_row_per_instance.rs`). `dyn_root` (a virtual call, never admitted) stays
//! refused. This file is changed because the ruling changed the claim, not to make it
//! green: the guard it states below still holds for every NON-admitted shape.
#![allow(dead_code)]

#[cfg(not(any(dep_boom, dep_blanket)))]
extern crate xcsealed_dep;
#[cfg(not(any(dep_boom, dep_blanket)))]
use xcsealed_dep::Shape;

#[cfg(dep_boom)]
extern crate xcshape_dep;
#[cfg(dep_boom)]
use xcshape_dep::Shape;

#[cfg(dep_blanket)]
extern crate xcsealed_blanket_dep;
#[cfg(dep_blanket)]
use xcsealed_blanket_dep::Shape;

pub struct Mine;

#[cfg(not(local_bad))]
impl Shape for Mine {
    fn area(&self) -> u32 {
        1
    }
}

#[cfg(local_bad)]
impl Shape for Mine {
    fn area(&self) -> u32 {
        panic!("mine")
    }
}

#[cfg(not(any(lib_consumer, dyn_root, unsized_self)))]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[bin_ok]~vv ERROR Trust strict verification failed for `xcrate_foreign_trait_closure_sealed::f`
//[bin_ok]~v NOTE this function has no obligation of its own
fn f<X: Shape>(x: &X) -> u32 {
    //[undeclared,dep_boom,dep_blanket,local_bad]~^ WARN 1 instance hypothesis row(s)
    x.area()
}

#[cfg(lib_consumer)]
pub fn f<X: Shape>(x: &X) -> u32 {
    //[lib_consumer]~^ WARN 1 instance hypothesis row(s)
    x.area()
}

#[cfg(unsized_self)]
fn f<X: Shape + ?Sized>(x: &X) -> u32 {
    //[unsized_self]~^ WARN 1 instance hypothesis row(s)
    x.area()
}

#[cfg(dyn_root)]
pub fn g(x: &dyn Shape) -> u32 {
    //[dyn_root]~^ ERROR Trust strict verification failed
    //[dyn_root]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    x.area()
}

#[cfg(not(any(lib_consumer, dyn_root)))]
fn main() {
    //[local_bad]~^ ERROR Trust instance discharge not established
    let _ = f(&Mine);
}

#[cfg(dyn_root)]
fn main() {
    let _ = g(&Mine);
}
