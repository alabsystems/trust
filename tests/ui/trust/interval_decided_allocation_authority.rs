//@ needs-trust-verify
//@ revisions: s20 folded_sibling starved_s20 starved_sibling unbounded nonzero_start nonzero_literal_start starved_nonzero_literal_start byte_boundary starved_byte_boundary
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[starved_s20] compile-flags: -Ztrust-verify-timeout-ms=1
//@[starved_sibling] compile-flags: -Ztrust-verify-timeout-ms=1
//@[starved_nonzero_literal_start] compile-flags: -Ztrust-verify-timeout-ms=1
//@[starved_byte_boundary] compile-flags: -Ztrust-verify-timeout-ms=1
//@[s20] check-pass
//@[folded_sibling] check-pass
//@[starved_s20] check-pass
//@[starved_sibling] check-pass
//@[unbounded] check-fail
//@[nonzero_start] check-fail
//@[nonzero_literal_start] check-fail
//@[starved_nonzero_literal_start] check-fail
//@[byte_boundary] check-fail
//@[starved_byte_boundary] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (2026-09-23, D3 / W1a): WHICH authority an interval-decided
//! allocation row carries, and that it never carries the interval engine's own.
//!
//! The interval domain is NOT proof authority (docs/TCB.md). A row it decides
//! earns authority only when an independent mechanism re-derives the same
//! violation formula: `ay` to strict UNSAT (`SolverRevalidated`, W1,
//! `5c6ad769b9`) or the Clean kernel (`certify_vc`, `Certified`).
//!
//! DEFECT PINNED. Sweep `s20`, `(0..n.min(8) as u32).collect()`, counted
//! `Sub(end, Int(0))`; the kernel's scaled-chain recognizer needs a bare
//! variable under `Mul(stride, _)`, so the row could reach only
//! `SolverRevalidated` — and with `ay` starved (`-Ztrust-verify-timeout-ms=1`)
//! it fell back to the authority-free interval `Proved` and reported
//! `[unbounded_allocation] UNKNOWN (interval): Proved label lacked exact
//! kernel/native proof authority` (measured on stage-1 `de437e35d`: rc=1; the
//! same program at the default budget rc=0). `trust-vcgen`'s
//! `fold_sub_literal_zero` rewrites `end - 0` to `end` IN THE OBLIGATION (exact
//! over the integers), and `certify_vc` certifies the captured formula once
//! folded (`crates/trust-certify/tests/unbounded_allocation_scaled_count_certification.rs`).
//!
//! `starved_s20` / `starved_sibling` FLIPPED from check-fail to check-pass with
//! that fold: with `ay` given 1 ms the only authority left is the kernel's, so a
//! pass here is a `Certified` row, never an interval one.
//!
//! RAILS (must stay refused, starved or not):
//!   * `unbounded`: no bound at all.
//!   * `nonzero_literal_start`: `-268435456i64..` counts `end + 268435456`, which
//!     reaches 2^28. A fold that dropped any literal other than 0 would certify
//!     it — the false proof the literal-zero-only rule prevents.
//!   * `nonzero_start`: the same start as a computed local (`Sub(end, start)`).
//!   * `byte_boundary`: `n.min(1 << 29)` reaches the byte/element ceiling.

#[cfg(any(s20, starved_s20))]
pub fn build(n: usize) -> Vec<u32> {
    (0..n.min(8) as u32).collect()
}

#[cfg(any(folded_sibling, starved_sibling))]
pub fn collect_clamped_u32(n: usize) -> Vec<u32> {
    (0..(n as u32).min(8)).collect()
}

#[cfg(any(folded_sibling, starved_sibling))]
pub fn with_clamped_capacity(n: usize) -> Vec<u32> {
    Vec::with_capacity(n.min(8))
}

#[cfg(unbounded)]
pub fn build(n: usize) -> Vec<u32> {
    //[unbounded]~^ NOTE [unbounded_allocation] FAILED
    (0..n as u32).collect()
}

#[cfg(nonzero_start)]
pub fn build(n: usize) -> Vec<i64> {
    //[nonzero_start]~^ NOTE [unbounded_allocation] FAILED
    (-(1i64 << 28)..(n.min(8) as i64)).collect::<Vec<i64>>()
}

#[cfg(any(nonzero_literal_start, starved_nonzero_literal_start))]
pub fn build(n: usize) -> Vec<i64> {
    //[nonzero_literal_start]~^ NOTE [unbounded_allocation] FAILED
    //[starved_nonzero_literal_start]~^^ NOTE [unbounded_allocation]
    (-268435456i64..(n.min(8) as i64)).collect::<Vec<i64>>()
}

#[cfg(any(byte_boundary, starved_byte_boundary))]
pub fn build(n: usize) -> Vec<u32> {
    //[byte_boundary]~^ NOTE [unbounded_allocation] FAILED
    //[starved_byte_boundary]~^^ NOTE [unbounded_allocation]
    (0..n.min(1 << 29) as u32).collect()
}
