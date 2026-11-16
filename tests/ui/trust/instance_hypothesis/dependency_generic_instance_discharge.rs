//@ revisions: good_local bad_local good_dep bad_dep bad_dep_advisory bad_dep_certify
//@ revisions: propagated_dep propagated_local claimed undeclared bad_dep_admitted good_dep_admitted
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: od2_dep_off.rs
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[good_local] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off
//@[bad_local] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off
//@[good_dep] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off
//@[bad_dep] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off
//@[bad_dep_advisory] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off -Ztrust-policy=advisory
//@[bad_dep_certify] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off -Ztrust-policy=certify
//@[propagated_dep] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off
//@[propagated_local] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off
//@[claimed] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off
//@[bad_dep_admitted] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off
//@[good_dep_admitted] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[good_local] check-fail
//@[bad_local] check-fail
//@[good_dep] check-fail
//@[bad_dep] check-fail
//@[bad_dep_advisory] check-pass
//@[bad_dep_certify] check-fail
//@[propagated_dep] check-fail
//@[propagated_local] check-fail
//@[claimed] check-fail
//@[undeclared] check-fail
//@[bad_dep_admitted] check-fail
//@[good_dep_admitted] check-fail
//@[bad_dep_admitted] forbid-output: this function has no obligation of its own
//! ZERO-ROW-GATE AMENDMENT (2026-10-10, docs/DECISION_QUEUE.md ZERO-ROW-GATE): `good_dep_admitted` now carries
//! one more ERROR: `admit` has zero obligations (pinned NOTE) and its call publishes
//! an `unknown` row. The good/bad differential is kept: `bad_dep_admitted` FORBIDS the
//! zero-row note, so it must still refuse for its own reason.
//!
//! OD-1 PHASE 2 (2026-10-05): the open dispatch lives in a DEPENDENCY's generic
//! (`od2_dep_off::f`, compiled `-Ztrust-verify=off`); this crate creates its
//! instances. The dependency exports nothing: this compilation re-derives `f`'s
//! site from the dependency's encoded MIR (D4's channel: declared by identity,
//! statically linked, non-sysroot) and charges one `instance-hypothesis:discharge`
//! row per (site, instance) it names, carrying the resolved callee's own verdict.
//!
//! BEFORE (stage 1 of main `8364c5a6af`, same sources): every revision but
//! `claimed` refused ONLY on the call's generic absent-callee row, which a correct
//! instance shares (`good_dep` and `bad_dep` printed the same summary, "1
//! runtime-checked out of 1"), and `claimed` BUILT rc=0 under strict — the
//! dependency's own `#[trust::assume_total]` on `f_claimed` stood for an instance
//! at a panicking impl. AFTER: the discharge itself is the reason.
//!
//! * `good_local` — the instance's callee is a local impl proved here: the discharge
//!   row is `assumed (instance discharge)` (no credit). The crate still refuses on the
//!   call's own generic absent-callee row: a dependency's generic instance is not
//!   bundled (pre-existing; its relative verdict is not re-derived).
//! * `good_dep` / `bad_dep` / `bad_dep_advisory` / `bad_dep_certify` — the callee
//!   is a dependency impl (verify-off, verified NOWHERE else) that no credit-bearing
//!   check of this compilation re-derived: the discharge is `unknown` (review fix
//!   2026-10-05: a discharge carries no credit and spends no re-derivation budget),
//!   an error on strict and certify and a warning under advisory.
//! * `bad_dep_admitted` / `good_dep_admitted` — an EARLIER body's `dyn` call made
//!   the C-FLOW case split re-derive the impl (D4-A, charged there): the discharge
//!   reads that verdict, `failed` for the panicking impl and `assumed (instance
//!   discharge)` for the correct one.
//! * `bad_local` — a panicking LOCAL impl (also refused as its own root): `failed`.
//! * `propagated_dep` — `dep::g::<DepBad>` reaches `f`'s site through the
//!   dependency's own still-generic call `f::<Y>`.
//! * `propagated_local` — a LOCAL generic `h<U>` calls `dep::f::<U>`: `h` publishes
//!   `f`'s site as its own propagated hypothesis row (the call keeps its
//!   absent-callee row), and `h::<DepBad>` is discharged through it.
//! * `claimed` — the dependency marks `f_claimed` `#[trust::assume_total]`: a
//!   dependency's axiom on a GENERIC is not read (review fix 2026-10-05), so the call
//!   keeps its absent-callee row, and the site is discharged.
//! * `undeclared` — the dependency is not in the declared scope: its MIR is not
//!   read, nothing changes (the call keeps its fail-closed row).

extern crate od2_dep_off as dep;

#[cfg(good_local)]
pub struct Good;
#[cfg(good_local)]
impl dep::Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

#[cfg(bad_local)]
pub struct Bad;
#[cfg(bad_local)]
impl dep::Tr for Bad {
    fn m(&self) -> u32 {
        //[bad_local]~^ ERROR Trust Level 0 safety verification incomplete
        //[bad_local]~^^ ERROR Trust strict verification failed
        panic!("bad")
    }
}

#[cfg(propagated_local)]
pub fn h<U: dep::Tr>(u: &U) -> u32 {
    //[propagated_local]~^ WARN Trust verification advisory for `dependency_generic_instance_discharge::h`: 1 instance hypothesis row(s)
    //[propagated_local]~^^ ERROR Trust strict verification failed for `dependency_generic_instance_discharge::h`
    dep::f(u)
}

#[cfg(any(bad_dep_admitted, good_dep_admitted))]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[good_dep_admitted]~vv ERROR Trust strict verification failed for `dependency_generic_instance_discharge::admit`
//[good_dep_admitted]~v NOTE this function has no obligation of its own
pub fn admit() -> u32 {
    //[bad_dep_admitted]~^ ERROR Trust strict verification failed
    #[cfg(bad_dep_admitted)]
    let d: &dyn dep::Tr = &dep::DepBad;
    #[cfg(good_dep_admitted)]
    let d: &dyn dep::Tr = &dep::DepGood;
    d.m()
}

pub fn use_it() -> u32 {
    //[good_local]~^ NOTE 1 runtime-checked, 1 assumed (instance discharge), 1 skipped out of 3 obligation(s)
    //[good_local]~| ERROR Trust strict verification failed
    //[good_dep]~^^^ ERROR Trust instance discharge not established for `dependency_generic_instance_discharge::use_it`: 1 instance(s)
    //[good_dep]~| NOTE resolves to `<od2_dep_off::DepGood as od2_dep_off::Tr>::m` [unknown]
    //[good_dep]~| ERROR Trust strict verification failed
    //[bad_local]~^^^^^^ ERROR Trust instance discharge not established for `dependency_generic_instance_discharge::use_it`: 1 instance(s)
    //[bad_local]~| NOTE Bad as od2_dep_off::Tr>::m` [failed]
    //[bad_local]~| ERROR Trust strict verification failed
    //[bad_dep]~^^^^^^^^^ ERROR Trust instance discharge not established for `dependency_generic_instance_discharge::use_it`: 1 instance(s)
    //[bad_dep]~| NOTE site `<X as od2_dep_off::Tr>::m` of `od2_dep_off::f::<od2_dep_off::DepBad>` (named at
    //[bad_dep]~| ERROR Trust strict verification failed
    //[bad_dep_advisory]~^^^^^^^^^^^^ WARN Trust instance discharge not established for `dependency_generic_instance_discharge::use_it`: 1 instance(s)
    //[bad_dep_advisory]~| NOTE resolves to `<od2_dep_off::DepBad as od2_dep_off::Tr>::m` [unknown]
    //[bad_dep_certify]~^^^^^^^^^^^^^^ ERROR Trust Level 0 safety verification incomplete
    //[bad_dep_certify]~| ERROR Trust instance discharge not established for `dependency_generic_instance_discharge::use_it`: 1 instance(s)
    //[bad_dep_certify]~| NOTE resolves to `<od2_dep_off::DepBad as od2_dep_off::Tr>::m` [unknown]
    //[bad_dep_certify]~| ERROR Trust strict verification failed
    //[propagated_dep]~^^^^^^^^^^^^^^^^^^ ERROR Trust instance discharge not established for `dependency_generic_instance_discharge::use_it`: 1 instance(s)
    //[propagated_dep]~| NOTE resolves to `<od2_dep_off::DepBad as od2_dep_off::Tr>::m` [unknown]
    //[propagated_dep]~| ERROR Trust strict verification failed
    //[propagated_local]~^^^^^^^^^^^^^^^^^^^^^ ERROR Trust instance discharge not established for `dependency_generic_instance_discharge::use_it`: 1 instance(s)
    //[propagated_local]~| NOTE resolves to `<od2_dep_off::DepBad as od2_dep_off::Tr>::m` [unknown]
    //[propagated_local]~| ERROR Trust strict verification failed
    //[claimed]~^^^^^^^^^^^^^^^^^^^^^^^^ ERROR Trust instance discharge not established for `dependency_generic_instance_discharge::use_it`: 1 instance(s)
    //[claimed]~| NOTE of `od2_dep_off::f_claimed::<od2_dep_off::DepBad>`
    //[claimed]~| ERROR Trust strict verification failed
    //[undeclared]~^^^^^^^^^^^^^^^^^^^^^^^^^^^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 1 obligation(s)
    //[undeclared]~| ERROR Trust strict verification failed
    //[bad_dep_admitted]~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR Trust instance discharge not established for `dependency_generic_instance_discharge::use_it`: 1 instance(s)
    //[bad_dep_admitted]~| NOTE resolves to `<od2_dep_off::DepBad as od2_dep_off::Tr>::m` [failed]
    //[bad_dep_admitted]~| ERROR Trust strict verification failed
    //[good_dep_admitted]~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ NOTE 1 runtime-checked, 1 assumed (instance discharge)
    //[good_dep_admitted]~| ERROR Trust strict verification failed
    #[cfg(good_local)]
    let r = dep::f(&Good);
    #[cfg(bad_local)]
    let r = dep::f(&Bad);
    #[cfg(any(good_dep, good_dep_admitted))]
    let r = dep::f(&dep::DepGood);
    #[cfg(any(bad_dep, bad_dep_advisory, bad_dep_certify, undeclared, bad_dep_admitted))]
    let r = dep::f(&dep::DepBad);
    #[cfg(propagated_dep)]
    let r = dep::g(&dep::DepBad);
    #[cfg(propagated_local)]
    let r = h(&dep::DepBad);
    #[cfg(claimed)]
    let r = dep::f_claimed(&dep::DepBad);
    r
}

// ZERO-ROW-GATE (2026-10-10): this rail must refuse for its OWN reason; a refusal by the
// zero-row gate (whose note is forbidden here) would mean the gate under test regressed
// into discharging and the zero-row gate masked it.
