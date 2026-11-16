//@ needs-trust-verify
//@ edition: 2021
//@ aux-build:xcphi_dep.rs
//@ aux-build:xcphi_dep_bad.rs
//@ aux-build:xcphi_fwd_dep.rs
//@ aux-build:xcphi_third.rs
//@ aux-build:xcphi_third_ok.rs
//@ revisions: bin_ok undeclared dep_bad lib_consumer third_ok third_bad third_undeclared
//@ revisions: fwd_local fwd_foreign dyn_root unsized_self
//@ compile-flags: -Ztrust-verify=on
//@[bin_ok] compile-flags: -Ztrust-bundle-foreign-crate=xcphi_dep
//@[dep_bad] compile-flags: -Ztrust-bundle-foreign-crate=xcphi_dep_bad
//@[lib_consumer] compile-flags: --crate-type lib -Ztrust-bundle-foreign-crate=xcphi_dep
//@[third_ok] compile-flags: -Ztrust-bundle-foreign-crate=xcphi_dep,xcphi_third_ok
//@[third_bad] compile-flags: -Ztrust-bundle-foreign-crate=xcphi_dep,xcphi_third
//@[third_undeclared] compile-flags: -Ztrust-bundle-foreign-crate=xcphi_dep
//@[fwd_local] compile-flags: -Ztrust-bundle-foreign-crate=xcphi_dep
//@[fwd_foreign] compile-flags: -Ztrust-bundle-foreign-crate=xcphi_fwd_dep
//@[dyn_root] compile-flags: -Ztrust-bundle-foreign-crate=xcphi_dep
//@[unsized_self] compile-flags: -Ztrust-bundle-foreign-crate=xcphi_dep
//@ dont-check-compiler-stderr
//@[undeclared] dont-require-annotations: ERROR
//@[dep_bad] dont-require-annotations: ERROR
//@[lib_consumer] dont-require-annotations: ERROR
//@[third_bad] dont-require-annotations: ERROR
//@[third_undeclared] dont-require-annotations: ERROR
//@[fwd_foreign] dont-require-annotations: ERROR
//@[dyn_root] dont-require-annotations: ERROR
//@[unsized_self] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[bin_ok] check-fail
//@[undeclared] check-pass
//@[dep_bad] check-pass
//@[lib_consumer] check-pass
//@[third_ok] check-fail
//@[third_bad] check-pass
//@[third_undeclared] check-pass
//@[fwd_local] check-fail
//@[fwd_foreign] check-pass
//@[dyn_root] check-fail
//@[unsized_self] check-pass
//! D4 increment B (2026-09-25) — RUNG 1 (`#[trust::panic_free]`, Φ) for a
//! FOREIGN trait at a GENERIC call site in a WHOLE-PROGRAM artifact
//! (`trust_verify/foreign_trait_closure.rs`). The trait's impl set in the loaded
//! crate graph is ENUMERATED; every foreign dispatch target is RE-DERIVED here
//! from its declared crate's encoded MIR (`foreign_rederivation`), and every local
//! one is held to Φ at the impl by this crate's own discharge. Nothing about any
//! dependency's own verification is read — every dependency here is built
//! `-Ztrust-verify=off`.
//!
//! EVERY `check-fail` REVISION MUST STAY REFUSED. Fix the compiler, never this
//! file. The pinned row is the generic call's fatal absent-callee row in `f`
//! (or `g`): that is the call the rung discharges, and nothing else in these
//! programs can fail.
//!
//! Measured BEFORE (stage-1 snapshot `43b8fe6ab`, current main without D4-B,
//! compiletest-equivalent harness: each auxiliary built with its own flags, each
//! revision with its flags and `--emit metadata`): EVERY revision refused, the
//! three `check-pass` ones included — `f`'s `<X as T>::m` stayed the fatal
//! generic absent-callee row ("Level 0 summary: 1 failed"), because rung 1
//! returned `false` for any non-local trait; `fwd_local` also refused `W`'s impl
//! at the impl. A LOCAL copy of `bin_ok` (trait and impls in one crate) built
//! rc=0 on the same compiler. The first D4-B build (`b0cc6b172`) and the
//! post-review fix measured every revision as annotated below.
//!
//! * `bin_ok` — check-pass: impls are `xcphi_dep::Good` (re-derived) and the
//!   local `Mine` (discharged at the impl). `main` calls `f` at `Mine` only,
//!   because a CONCRETE call into a dependency's trait impl is not bundled by the
//!   declared arm (its `gen_args` carry `Self`) — a separate, pre-existing gap.
//! * `undeclared` — the same program, `xcphi_dep` not declared: `Good` cannot be
//!   re-derived, so the closure refuses, on the fail-closed generic-absent-callee
//!   gate ("Trust strict verification failed").
//! * `dep_bad` — the dependency also has `Bad`, which panics and is NEVER
//!   constructed. The closure is over the impl set, not over used types.
//!
//! THE LEVEL-0 LABEL of every refused `f` row is `failed` ("1 failed"): the
//! closure DISCHARGES a call by filing its key on the compiler-total channel,
//! which leaves no row at all, so every row still present is one it declined —
//! and `dep_bad` / `third_bad` decline on a real panicking impl, a refutation
//! witness. MEASURED on the first D4-B build (`b0cc6b172`), before the
//! post-review fix: a label exemption keyed on the closure's STRUCTURE (binary,
//! `Sized` `Self`, user trait) demoted exactly those rows to a WARNING, "0
//! failed, 0 unknown or timed out, 1 runtime-checked", though `Bad` panics. The
//! pins below keep the witness visible; the build was refused either way.
//! * `lib_consumer` — an rlib: a crate compiled later could add a panicking impl.
//! * `third_ok` / `third_bad` / `third_undeclared` — a THIRD crate implements the
//!   trait. Declared and total: passes (the control, which shows the enumeration
//!   reaches beyond the trait's own crate). Declared and panicking: refused.
//!   Total but undeclared: refused (it cannot be re-derived).
//! * `fwd_local` — check-pass: a LOCAL forwarding impl `impl<S: T> T for W<S>`
//!   relies on the closure it is part of, which is sound by the innermost-frame
//!   argument and is exactly the local-trait rung's premise; its Φ discharge at
//!   the impl (refused BEFORE, as "this implementation of `#[trust::panic_free]`
//!   trait method `xcphi_dep::T::m` is not proved panic-free") now passes. `main`
//!   does not call `f` at `W<Mine>`: a concrete call into an INSTANTIATED generic
//!   impl method is refused even when everything is local (measured on the
//!   snapshot: the all-local copy refuses `main` with `NOT-IN-LEDGER
//!   <W<Mine> as T>::m`), a separate gap.
//! * `fwd_foreign` — the same forwarding impl in the DEPENDENCY: its re-derived
//!   body's `<S as T>::m` asks for the closure being computed, which declines
//!   (self-reliance), so the closure refuses. A recorded completeness cost.
//! * `dyn_root` — `fn g(x: &dyn T)`: a `dyn` call over a foreign trait is never
//!   served (a vtable can be forged in dependency bodies nobody walked).
//! * `unsized_self` — `fn f<X: T + ?Sized>`: a monomorphization at `dyn T` would
//!   be that same virtual call, so an unsized `Self` is refused too.
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

#[cfg(not(any(dep_bad, fwd_foreign)))]
extern crate xcphi_dep;
#[cfg(not(any(dep_bad, fwd_foreign)))]
use xcphi_dep::T;

#[cfg(dep_bad)]
extern crate xcphi_dep_bad;
#[cfg(dep_bad)]
use xcphi_dep_bad::T;

#[cfg(fwd_foreign)]
extern crate xcphi_fwd_dep;
#[cfg(fwd_foreign)]
use xcphi_fwd_dep::T;

#[cfg(third_bad)]
extern crate xcphi_third;
#[cfg(any(third_ok, third_undeclared))]
extern crate xcphi_third_ok;

pub struct Mine;
impl T for Mine {
    fn m(&self) -> u32 {
        1
    }
}

#[cfg(fwd_local)]
pub struct W<S>(pub S);
#[cfg(fwd_local)]
impl<S: T> T for W<S> {
    // ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
    //[fwd_local]~vv ERROR Trust strict verification failed for `<xcrate_foreign_trait_closure_phi::W<S> as xcphi_dep::T>::m`
    //[fwd_local]~v NOTE this function has no obligation of its own
    fn m(&self) -> u32 {
        self.0.m()
    }
}

#[cfg(not(any(lib_consumer, dyn_root, unsized_self)))]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[bin_ok,fwd_local,third_ok]~vv ERROR Trust strict verification failed for `xcrate_foreign_trait_closure_phi::f`
//[bin_ok,fwd_local,third_ok]~v NOTE this function has no obligation of its own
fn f<X: T>(x: &X) -> u32 {
    //[undeclared,dep_bad,third_bad,third_undeclared,fwd_foreign]~^ WARN 1 instance hypothesis row(s)
    x.m()
}

#[cfg(lib_consumer)]
pub fn f<X: T>(x: &X) -> u32 {
    //[lib_consumer]~^ WARN 1 instance hypothesis row(s)
    x.m()
}

#[cfg(unsized_self)]
fn f<X: T + ?Sized>(x: &X) -> u32 {
    //[unsized_self]~^ WARN 1 instance hypothesis row(s)
    x.m()
}

#[cfg(dyn_root)]
pub fn g(x: &dyn T) -> u32 {
    //[dyn_root]~^ ERROR Trust strict verification failed
    //[dyn_root]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    x.m()
}

#[cfg(not(any(lib_consumer, dyn_root, third_ok, third_bad, third_undeclared)))]
fn main() {
    let _ = f(&Mine);
}

#[cfg(third_bad)]
fn main() {
    let _ = f(&Mine);
    let _ = &xcphi_third::Third;
}

#[cfg(any(third_ok, third_undeclared))]
fn main() {
    let _ = f(&Mine);
    let _ = &xcphi_third_ok::Third;
}

#[cfg(dyn_root)]
fn main() {
    let _ = g(&Mine);
}
