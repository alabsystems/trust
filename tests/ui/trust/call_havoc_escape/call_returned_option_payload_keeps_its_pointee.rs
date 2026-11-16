//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Cpanic=abort --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ forbid-output: FAILED
//@ forbid-output: withheld
//! RETURN-PAYLOAD-RETAG-1 (2026-10-18; candidate-gate RCA precision D2): the reference a
//! `for t in &v` loop reads out of `Iterator::next`'s `Option<&T>` carries the retag of
//! the call's return place, so a guard on `*t` survives a later call. `t.col + 1` under
//! `t.col >= cols => continue` cannot overflow (`t.col < cols <= usize::MAX`), and in a
//! defined execution nothing can change `t.col` across `row_is_uniform(..)` (a write
//! through any other pointer makes `t`'s later read UB), so the add must prove. The
//! element is named `TrailCell`, as aterm-core's is: a user type whose name contains
//! `Cell` is decided by its fields, not refused as a cell wrapper (CELL-NAME-TAIL-1).
//!
//! The shape is aterm-render `lib.rs:17913` (`draw_trail`), which the seal 321aaeda75
//! proved and the 2026-10-16 candidate (CALL-HAVOC-ESCAPE-2, `c871ae5f40`) left with a
//! withheld counterexample. The negative controls are
//! `loaded_option_payload_stays_havocked.rs`.

pub struct TrailCell {
    pub row: usize,
    pub col: usize,
}

pub struct TrailInput {
    pub rows: usize,
    pub cols: usize,
    pub trail: Vec<TrailCell>,
    pub sizes: Vec<u8>,
}

#[inline(never)]
pub fn row_is_uniform(input: &TrailInput, row: usize) -> bool {
    row < input.sizes.len()
}

pub fn draw_trail(input: &TrailInput) -> usize {
    let cols = input.cols;
    let mut acc = 0;
    for t in &input.trail {
        if t.row >= input.rows || t.col >= cols {
            continue;
        }
        if row_is_uniform(input, t.row) {
            acc ^= t.col + 1;
        }
    }
    acc
}

pub fn draw_trail_enumerate(input: &TrailInput) -> usize {
    let mut acc = 0;
    for (i, t) in input.trail.iter().enumerate() {
        if t.col >= input.cols {
            continue;
        }
        if row_is_uniform(input, i) {
            acc ^= t.col + 1;
        }
    }
    acc
}
