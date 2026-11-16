// Trust: rust-lang#127553 — RedundantBoundsCheckElim removes a bounds check that is
// dominated by an identical check on the same (SSA) index and length locals. GVN is
// force-enabled so duplicate index/length computations get merged into the same
// locals before the pass runs (matching its position in the real pipeline).
//@ test-mir-pass: RedundantBoundsCheckElim
//@ compile-flags: -Zmir-enable-passes=+GVN -Coverflow-checks=on
// Trust: `-Coverflow-checks=on` makes `-x` emit its optional `OverflowNeg` assert in this
// crate (RBCE-OPTIONAL-DOMINATOR-1 below). The bounds-check functions do no arithmetic, so
// their MIR, and their two .diff files, do not depend on it.
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

// Trust: RBCE-OPTIONAL-DOMINATOR-1. GVN gives `-x`'s optional `OverflowNeg` assert and
// `x / -1`'s mandatory overflow assert ONE condition local, `Eq(x, i32::MIN)`. The
// optional assert dominates, but codegen erases it in any session with overflow checks
// off, which may be a downstream crate codegenning this MIR. So it guarantees nothing,
// and the mandatory "attempt to compute `{} / {}`, which would overflow" assert must
// survive (before the fix it became `goto`, and `x / -1` at `i32::MIN` ran unchecked).
// EMIT_MIR redundant_bounds_check.optional_overflow_dominator.RedundantBoundsCheckElim.diff
pub fn optional_overflow_dominator(x: i32) -> (i32, i32) {
    // CHECK-LABEL: fn optional_overflow_dominator(
    // CHECK: assert(!copy [[COND:_[0-9]+]], "attempt to negate
    // CHECK: assert(!copy [[COND]], "attempt to compute
    (-x, x / -1)
}

// Trust: the other direction is still deduplicated: the mandatory Div overflow assert
// dominates the optional negate assert on the same condition, and a mandatory assert
// runs in every session, so the dominated optional assert becomes `goto`.
// EMIT_MIR redundant_bounds_check.mandatory_dominates_optional.RedundantBoundsCheckElim.diff
pub fn mandatory_dominates_optional(x: i32) -> (i32, i32) {
    // CHECK-LABEL: fn mandatory_dominates_optional(
    // CHECK: assert(!copy [[COND:_[0-9]+]], "attempt to compute
    // CHECK-NOT: "attempt to negate
    (x / -1, -x)
}

// Trust: the accepted cost of RBCE-OPTIONAL-DOMINATOR-1: two optional asserts on one
// condition are no longer deduplicated, because an optional assert never dominates.
// EMIT_MIR redundant_bounds_check.optional_pair.RedundantBoundsCheckElim.diff
pub fn optional_pair(x: i32) -> (i32, i32) {
    // CHECK-LABEL: fn optional_pair(
    // CHECK: assert(!copy [[COND:_[0-9]+]], "attempt to negate
    // CHECK: assert(!copy [[COND]], "attempt to negate
    (-x, -x)
}

fn main() {
    let _ = dominated_index(&[1, 2, 3], 1);
    let _ = different_indices(&[1, 2, 3], 1, 2);
    let _ = optional_overflow_dominator(1);
    let _ = mandatory_dominates_optional(1);
    let _ = optional_pair(1);
}
