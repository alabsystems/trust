// Trust: rust-lang#127553 — RedundantBoundsCheckElim removes a bounds check that is
// dominated by an identical check on the same (SSA) index and length locals. GVN is
// force-enabled so duplicate index/length computations get merged into the same
// locals before the pass runs (matching its position in the real pipeline).
//@ test-mir-pass: RedundantBoundsCheckElim
//@ compile-flags: -Zmir-enable-passes=+GVN
// Trust: single host panic-strategy variant. RedundantBoundsCheckElim removes the same
// dominated bounds check regardless of panic strategy (only the retained assert's unwind
// edge differs, which the pass does not touch), so one variant fully exercises the pass;
// EMIT_MIR_FOR_EACH_PANIC_STRATEGY is intentionally not used (the aarch64 synthetic-abort
// mir-opt target is unavailable on the macOS host used to bless this seed).

// EMIT_MIR redundant_bounds_check.dominated_index.RedundantBoundsCheckElim.diff
pub fn dominated_index(x: &[i32], i: usize) -> (i32, i32) {
    // The first bounds check dominates the second; the second must become a goto.
    // CHECK-LABEL: fn dominated_index(
    // CHECK: assert(
    // CHECK-NOT: assert(
    // CHECK: goto
    (x[i], x[i])
}

// EMIT_MIR redundant_bounds_check.different_indices.RedundantBoundsCheckElim.diff
pub fn different_indices(x: &[i32], i: usize, j: usize) -> (i32, i32) {
    // Different index locals: both bounds checks must survive.
    // CHECK-LABEL: fn different_indices(
    // CHECK: assert(
    // CHECK: assert(
    (x[i], x[j])
}

fn main() {
    let _ = dominated_index(&[1, 2, 3], 1);
    let _ = different_indices(&[1, 2, 3], 1, 2);
}
