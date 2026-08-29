//@ battery-lane: E-ir-spine
//@ battery-expect: ir-links-clean-origin
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//@ battery-ir-clean-def: trust_battery_linked_def
//! LANE E, FIXTURE 2 (IR-5) — do the two languages actually MEET in the IR?
//!
//! e1 witnesses marker PRESENCE: both languages' functions appear in one
//! module. That is deliberately weak — a module can carry both languages as
//! disconnected rows. This fixture witnesses LINKAGE: the Rust caller's call
//! edge in the assembled module must target the appended Clean-origin
//! definition (coverage `linked` row + `call @func.<id>` in the canonical
//! text), not the fail-closed bodyless declaration assemble minted for it.
//!
//! The honest fail-closed verdict when recording works but linking does not is
//! `ir-clean-declared-only` — the pre-IR-5 state, kept in the permitted set so
//! the lane stays a measurement (exactly as `ir-rust-only` was for e1).

mod m {
    clean {
        def trust_battery_linked_def (a : UInt64) (b : UInt64) : UInt64 := a + b
    }
}

/// The Rust half CALLS the island def in its body — the edge under test.
pub fn trust_battery_rust_caller(x: u64) -> u64 {
    m::trust_battery_linked_def(x, 1)
}
