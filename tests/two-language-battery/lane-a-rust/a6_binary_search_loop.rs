//@ battery-lane: A-rust
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A (Rust, native clauses) — FIRST-CLASS LOOP CLAUSES, inside the
//! modelled fragment.
//!
//! `invariant` and `decreases` in the grammar position vanilla Rust rejects
//! (between the loop condition and the body), on a loop the E4/E5 lane can
//! actually execute symbolically.
//!
//! This file used to hold binary search, copied from
//! `tests/ui/trust/native_loop_clauses.rs`. That was a mistake worth recording:
//! the source fixture runs `-Ztrust-verify=off // check-pass`, so it pins the
//! GRAMMAR only and is not evidence that the program verifies. The E4/E5 lane
//! now explores bounded acyclic multi-path bodies and accounts for every
//! backedge, so that old single-path explanation is retired. Binary search
//! remains in `a12_FRONTIER_multipath_loop.rs` because its `usize` loop state
//! is guarded by `u32` element comparisons and therefore crosses the current
//! one-principal-machine-domain boundary.
//!
//! What remains is a genuine slice walk: `.len()` appears in both the invariant
//! and the measure, and `i += 1` under the guard `i < xs.len()` is what makes
//! the increment's no-overflow obligation discharge with no hidden assumption.

/// Walk a slice to its end, carrying a bound and a strictly decreasing measure.
pub fn walk_to_end(xs: &[u8]) -> usize {
    let mut i = 0usize;
    while i < xs.len()
        invariant i <= xs.len()
        decreases xs.len() - i
    {
        i += 1;
    }
    i
}
