//@ battery-lane: A-rust
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A (Rust, native clauses) — TERMINATION, inside the modelled fragment.
//!
//! Termination is the obligation class where the five ledgered false-accepts
//! lived (non-terminating logic definitions verifying through holes in the
//! termination callgraph). A real recursive program is the honest exercise of
//! the fixed lane.
//!
//! This file deliberately holds only the shape the E5 recursion lane binds
//! exactly: the checked-subtraction chain `n - 1`
//! (`crates/trust-vcgen/src/termination.rs` `resolve_checked_arg_chain`).
//! Euclid's `gcd(b, a % b)` used to live here and does not belong: a `%`-derived
//! measure argument is outside that fragment, so it yields an UnsupportedMir
//! row rather than a proof. It moved to `a11_FRONTIER_rem_measure.rs`, where it
//! is scored as the capability gap it is instead of as a failure of this file.

/// Two recursive call sites, both strictly decreasing — the shape that
/// requires a per-call-site measure check rather than one blanket claim.
pub fn countdown_pair(n: u32)
    decreases n
{
    if n > 0 {
        countdown_pair(n - 1);
        countdown_pair(n - 1);
    }
}
