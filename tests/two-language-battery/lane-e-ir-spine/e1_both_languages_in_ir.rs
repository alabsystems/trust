//@ battery-lane: E-ir-spine
//@ battery-expect: ir-carries-both-languages
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//@ battery-ir-rust-marker: trust_battery_rust_fn
//@ battery-ir-lean-marker: trust_battery_island_def
//! LANE E (THE SPINE) — does the IR actually carry BOTH languages?
//!
//! Lanes A–C ask "does the program verify?". A toolchain can answer yes to
//! all of them while the ratified architecture is still unbuilt, because a
//! passing verdict says nothing about WHERE the two languages meet.
//!
//! The ratified target (docs/design/2026-07-09-two-language-spec-surface.md)
//! is that Rust and Lean feed THE SAME TrustIr module, with the Clean kernel
//! as the sole trust root. So this lane compiles one file containing both
//! languages, dumps the crate-level TrustIr artifact (`-Ztrust-dump=ir:`, the
//! `--emit=trust-ir` spelling), and looks inside for each language's marker.
//!
//! Two facts established from source, which this lane exists to CONFIRM
//! EMPIRICALLY rather than take on trust:
//!   * Rust reaches TrustIr directly — `trust_thir_lower` lowers source
//!     (THIR) straight to trust-ir under a differential gate against MIR
//!     (rustc_mir_build/src/builder/mod.rs), so the Rust marker appears.
//!   * The island NOW DOES TOO (flipped 2026-08-27, increment IR-1 of
//!     docs/design/2026-08-27-two-language-direct-to-trust-ir.md): the
//!     Clean-origin recording path re-earns the kernel verdict per def at the
//!     finalize seam and appends the trust-ir spelling to the same Module,
//!     tier `structural`, claim-free, `Producer::Clean`. The Lean marker is
//!     expected PRESENT under verification.
//!
//! This lane's earlier prose said `ir-rust-only` was "the honest expected
//! result today" and that if the Lean marker ever appeared "this lane flips to
//! `ir-carries-both-languages` and the claim is earned." It appeared; the
//! verdict flipped; the claim is earned AT MARKER-PRESENCE STRENGTH ONLY:
//! Rust→Clean call edges in the Module still target the fail-closed bodyless
//! declarations (linkage is increment IR-5), and the Clean rows are ungated
//! below tier `gate` — no codegen may consume them.

clean {
    def trust_battery_island_def (x : UInt64) : UInt64 := x

    theorem trust_battery_island_thm : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

/// The Rust half. Named distinctively so its presence in the IR dump is
/// unambiguous evidence rather than a substring coincidence.
pub fn trust_battery_rust_fn(x: u64) -> u64
    ensures result == trust_battery_island_def(x)
{
    x
}
