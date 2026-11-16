//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ needs-asm-support
//@ no-prefer-dynamic
//@ aux-build:certified_monitor_island_dependency.rs
//@ revisions: island island_global_asm
//@ compile-flags: -Ztrust-verify=off -Ztrust-verify-session=dependency-island-ui
//@ compile-flags: -Ztrust-targo-test-monitor -Awarnings
//@ rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION=dependency-island-ui
//@[island] check-pass
//@[island_global_asm] check-fail
//[island_global_asm]~? ERROR certified-monitor tests reject unauthenticated global assembly in dependency
//! CB3 regression (2026-09-28), dependency path.
//!
//! The dependency half of the certified-monitor startup-surface check walks
//! every def of every non-sysroot dependency through metadata, where there is
//! no HIR to tell a `clean { … }` island from a `global_asm!`: both are
//! `DefKind::GlobalAsm`. It used to refuse any crate that merely DEPENDED on an
//! island crate (measured: "reject unauthenticated global assembly in
//! dependency crate `depisl`"). The island is now admitted by the dependency's
//! per-def `trust_clean_island_item` rmeta marker.
//!
//! * `island`: the dependency has only an island — admitted.
//! * `island_global_asm`: the SAME dependency also carries a real
//!   `global_asm!` — still refused. A per-crate "has islands" exemption would
//!   pass this revision; the per-def marker does not.
//!
//! The pure `global_asm!` control is
//! `certified_monitor_rejects_dependency_startup_controls.rs` `[global_asm]`.

extern crate certified_monitor_island_dependency;

fn main() {
    certified_monitor_island_dependency::ordinary_rust_symbol();
}
