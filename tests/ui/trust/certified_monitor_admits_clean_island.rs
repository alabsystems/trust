//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ no-prefer-dynamic
//@ revisions: inline unit harness
//@ compile-flags: -Ztrust-verify=off -Ztrust-verify-session=clean-island-ui
//@ compile-flags: -Ztrust-targo-test-monitor -Awarnings
//@ rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION=clean-island-ui
//@[harness] compile-flags: --test
//@ check-pass
//! CB3 regression (2026-09-28): a `clean { … }` island is NOT global assembly.
//!
//! `rustc_resolve::def_collector` gives an island `DefKind::GlobalAsm`
//! (`DefKind` has no island variant). The certified-monitor startup-surface
//! check keyed on that def kind alone, so every crate with an island was
//! refused under `-Ztrust-targo-test-monitor` — i.e. in every
//! `targo trust test` lane — with "evidence-grade certified-monitor tests
//! reject unauthenticated global assembly" (measured with the installed pack's
//! `trustc` on an island-plus-`pub fn` crate: exit 1 with the flag, exit 0
//! without it or without the island). An island lowers no machine code (the
//! mono collector never roots it), so it cannot install startup code; the
//! check now asks `trust_def_is_clean_island` and admits it.
//!
//! Revisions: `inline` is the measured repro shape plus a `main`; `unit` is the out-of-line
//! `clean mod` spelling (apdf's shape); `harness` is the `--test` unit
//! `targo trust test` actually compiles.
//!
//! Negative controls, kept separate: `certified_monitor_rejects_startup_controls.rs`
//! `[global_asm]` (a real `global_asm!` is still refused) and
//! `[island_global_asm]` (a real `global_asm!` BESIDE an island is still
//! refused — the admission is per def, not per crate). The dependency path is
//! `certified_monitor_dependency_clean_island.rs`.

#[cfg(any(inline, harness))]
clean {
    theorem monitor_island_holds : 0 = 0 := rfl
}

#[cfg(unit)]
clean mod certified_monitor_admits_clean_island_unit;

pub fn f(x: u8) -> u8 {
    x
}

#[cfg(not(harness))]
fn main() {
    let _ = f(1);
}

#[cfg(harness)]
#[test]
fn island_crate_reaches_the_harness() {
    assert_eq!(f(1), 1);
}
