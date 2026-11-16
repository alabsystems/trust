// Trust (RANGE-FOLD-MID-DEF-1, 2026-10-11): `MatchBranchSimplification`'s contiguous-range fold
// (`simplify_range_comparison`, rust-lang#123305) must not fire when the second comparison's
// local `_c2` is mentioned outside its own block `mid`. The fold jumps from the first test
// straight past `mid`, so on those paths `_c2 = Le(copy x, const hi)` no longer runs.
//
// The fold does not fire under `test-mir-pass` (opt-level 0 leaves temps in `mid`), so this test
// runs the default `-O` pipeline (`-Zmir-opt-level=2`), where the miscompile happened.
//
// BEFORE (2026-10-11, the stage 1 of integ7 after wave 23, main = 1213387e6d,
// `scratchpad/stage1-w24probe/bin/rustc`, compiletest's mir-opt flags, the default lane's
// `-Ztrust-verify=off`, then this file's flags): in `user_var` the fold fired,
// `_2 = Le(copy _1, const 20_u8)` vanished, and the final MIR was `debug b => const false; ...
// _0 = const false; return;` for every input. FileCheck over that final MIR exited 1 on the
// `Le(copy _1, const 20_u8)` CHECK below. `temp_only` folded, and its CHECKs passed.
// AFTER (predicted from the same compiler with `-Zmir-enable-passes=-MatchBranchSimplification`,
// which for `user_var` differs from the fix in nothing: MBS has no other rewrite for a bool
// switch whose arms do not unify): `_0 = Le(copy _1, const 20_u8)` survives and FileCheck
// exits 0. The integrator blesses the two `.diff` files; `user_var`'s must show no change.
//@ compile-flags: -O -Zmir-opt-level=2
#![crate_type = "lib"]

// `b` is `_c2`, and it is read after the join: the fold must be declined.
// EMIT_MIR trust_match_range_fold_mid_def.user_var.MatchBranchSimplification.diff
pub fn user_var(x: u8) -> bool {
    // CHECK-LABEL: fn user_var(
    // CHECK-NOT: Sub(
    // CHECK: = Le(copy _1, const 20_u8);
    // CHECK: return;
    let mut b = false;
    if let 10.. = x {
        b = x <= 20;
        if let true = b {
            std::hint::black_box(());
        }
    }
    b
}

// Positive control: `_c2` is a match temp mentioned only in `mid`, so the fold still fires. A fix
// that simply stopped folding would fail here.
// EMIT_MIR trust_match_range_fold_mid_def.temp_only.MatchBranchSimplification.diff
pub fn temp_only(x: u8) -> bool {
    // CHECK-LABEL: fn temp_only(
    // CHECK: [[sub:_.*]] = Sub(copy _1, const 10_u8);
    // CHECK: Le(copy [[sub]], const 10_u8);
    // CHECK-NOT: Le(copy _1, const 20_u8)
    // CHECK: return;
    matches!(x, 10..=20)
}
