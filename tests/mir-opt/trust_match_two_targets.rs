// Trust: Regression test for #934 (rust-lang#110737)
// Trust: Verify that SwitchInt with exactly 2 targets (one value + otherwise)
// Trust: is converted into an Eq comparison + bool SwitchInt, matching the
// Trust: code shape produced by if/else.
//@ test-mir-pass: MatchBranchSimplification
#![crate_type = "lib"]
#![feature(custom_mir)]
#![feature(core_intrinsics)]

use std::intrinsics::mir::*;

// Trust: Test case using custom MIR with unequal branch bodies so that the
// Trust: existing unify_by_eq_op / candidate_match cannot fire. The new
// Trust: simplify_switch_two_targets pass should still convert the SwitchInt
// Trust: to an Eq comparison.

// EMIT_MIR trust_match_two_targets.switch_to_eq_unequal.MatchBranchSimplification.diff
#[custom_mir(dialect = "built")]
pub fn switch_to_eq_unequal(x: u32, y: &mut u32) -> u32 {
    // CHECK-LABEL: fn switch_to_eq_unequal(
    // Trust: The 2-target SwitchInt should be converted to Eq even though
    // Trust: the branches have different numbers of statements.
    // CHECK: Eq(
    mir! {
        {
            match x {
                42 => bb1,
                _ => bb2,
            }
        }
        bb1 = {
            // Two statements — different count from bb2
            *y = 1;
            RET = 100;
            Goto(ret)
        }
        bb2 = {
            // One statement — different count from bb1
            RET = 200;
            Goto(ret)
        }
        ret = {
            Return()
        }
    }
}
