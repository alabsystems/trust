//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Cpanic=abort --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ forbid-output: FAILED
//! FRESH-CAPTURE-1 (2026-10-18; candidate-gate RCA precision T1): a closure's
//! by-reference capture whose every value the compiler certified a FRESH shared borrow
//! (`rustc_mir_transform::trust_verify::fresh_capture`: one construction, every other
//! use a direct call of the closure, nothing that could forge a value of its type)
//! keeps its pointee across a call. `w` is captured by reference, the closure returns
//! early on `w == 0`, divides, a call runs, and `p % w` reads `w` again: in a defined
//! execution nothing can change `w` in between (a write through any other pointer makes
//! the capture's later read UB), so the remainder must not be refuted.
//!
//! The shapes are aterm-conformance `scan.rs:1460` and aterm-control
//! `selection.rs:357`, which the seal 321aaeda75 proved and the 2026-10-16 candidate
//! (CALL-HAVOC-ESCAPE-2, `c871ae5f40`) refuted with `w = 0`. The negative controls,
//! where the compiler certifies nothing, are
//! `uncertified_closure_capture_stays_havocked.rs`.

#[inline(never)]
pub fn opaque_sink(x: usize) -> usize {
    core::hint::black_box(x)
}

pub fn capture_ref_div_rem(w: usize, p: usize) -> usize {
    let f = |p: usize| {
        if w == 0 {
            return 0;
        }
        let q = p / w;
        opaque_sink(q);
        p % w
    };
    f(p)
}

pub fn word_cells(first_row: i32, cols: usize, start: usize, last: usize) -> ((i32, u16), (i32, u16)) {
    let cell = |g: usize| -> (i32, u16) {
        if cols == 0 {
            return (first_row, 0);
        }
        let dr = i32::try_from(g / cols).unwrap_or(i32::MAX);
        let c = u16::try_from(g % cols).unwrap_or(u16::MAX);
        (first_row.saturating_add(dr), c)
    };
    (cell(start), cell(last))
}
