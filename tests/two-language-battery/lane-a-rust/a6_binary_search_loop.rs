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
//! GRAMMAR only and is not evidence that the program verifies. The loop-contract
//! lane walks one body path, following only `Goto` and `Assert` terminators
//! (`single_path_loop_transition_blocks`); binary search's `if/else if/else`
//! introduces two `SwitchInt` terminators and a second loop exit, so both its
//! clauses become UnsupportedMir rows. Binary search now lives in
//! `a12_FRONTIER_multipath_loop.rs`, scored as the frontier it is.
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
