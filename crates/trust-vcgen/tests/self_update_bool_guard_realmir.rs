// Real-MIR regression for a compiler CRASH on valid code: a stack overflow in
// guard resolution (`trustc interrupted by SIGBUS`, compiling ay's `ay-dpll` on
// the verified lane). Measured on ay-dpll's own extracted MIR (2026-09-25): VC
// generation overflows an 8 MiB stack on
// `ay_dpll::combined_solvers::combiner_check::<impl TheoryCombiner<'_>>::nelson_oppen_check`
// (crates/ay-dpll/src/combined_solvers/combiner_check/mod.rs:287-319):
//
//     Ok(arr_new) => { has_new_eqs |= arr_new; }
//     ...
//     if !has_new_eqs && !arith.new_disequalities && .. {
//
// and three more ay-dpll bodies carry the same self-update-then-switch block
// (`build_dt_egraph_assignment`'s `changed |= ..; if !changed { break; }`,
// `restore_reachable_authored_assume_surface_overrides`'s `changed |= sealed;
// if changed`, and a closure in `rewrite_dense_bv_array_term`); they only
// escaped because no generated row's path guard happens to read that switch.
//
// Reduced (the fixture's source; the stage-1 compiler dies with SIGBUS on it):
//
//   #[inline(never)] fn reconcile(v: u32) -> bool { v > 3 }
//   pub fn fixpoint(a: &[u32]) -> u32 {
//       let mut n = 0u32;
//       for &v in a {
//           let mut changed = false;
//           changed |= reconcile(v);
//           changed |= reconcile(v / 2);
//           if !changed { break; }
//           n = v / 2 + 1;
//       }
//       n
//   }
//
// The calls split the updates across blocks, so `changed` is not SSA and survives
// optimization as one local, and the `!` folds into swapped switch targets. The
// last update and the switch share a block that reads the self-updated local
// DIRECTLY:
//
//   bb7: _8 = BitOr(copy _8, move _10); switchInt(move _8) -> [0: bb8, otherwise: bb9]
//
// `guards::latest_same_block_bool_definition` resolved the `BitOr`'s operand `_8`
// against the LATEST definition of `_8` in the block — the `BitOr` itself — and
// recursed with `resolve_same_block_bool_operand` until the stack ran out. The
// operand is read AT that statement, so it must be resolved against the
// statements BEFORE it (here: none, so it stays the opaque `changed`, exact by
// idempotence of `|`).
//
// Fixtures: `-Ztrust-dump=mir-only:<dir>` from the stage-1 compiler
// (0.10.0+gfb304b993) with ay-dpll's dev flags `-C opt-level=1
// -C debug-assertions=on`. `range_match` in the same crate is the positive
// control: an ordinary single-block `(x >= 2) & (x <= 9)` read by a `match`.
use trust_types::{
    BinOp, Formula, Sort, VcKind, VerifiableFunction, VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn self_update_fixture() -> VerifiableFunction {
    load(include_str!("fixtures/self_update_bool_switch_guard_mir.json"))
}

fn range_control_fixture() -> VerifiableFunction {
    load(include_str!("fixtures/range_bitand_match_guard_mir.json"))
}

/// VC generation on a thread with an explicit, ORDINARY 8 MiB stack (the main
/// thread's default), so the outcome does not depend on `RUST_MIN_STACK` or the
/// harness's thread size. Before the fix this thread overflowed its stack on
/// `self_update_fixture` — deterministically, since the recursion never ends —
/// and the test binary aborted.
fn generate_on_ordinary_stack(func: VerifiableFunction) -> Vec<VerificationCondition> {
    std::thread::Builder::new()
        .name("vcgen-ordinary-stack".into())
        .stack_size(8 << 20)
        .spawn(move || trust_vcgen::generate_vcs(&func))
        .expect("spawn the VC-generation thread")
        .join()
        .expect("VC generation must return, not panic")
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    let router = test_router::deterministic_test_router();
    router.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

fn is_arithmetic_row(vc: &VerificationCondition) -> bool {
    matches!(
        vc.kind,
        VcKind::ArithmeticOverflow { .. } | VcKind::DivisionByZero | VcKind::RemainderByZero
    )
}

fn is_bool_var_rooted_at(f: &Formula, root: &str) -> bool {
    matches!(f, Formula::Var(name, Sort::Bool) if name.split('#').next() == Some(root))
}

/// `Or([changed, _10])` somewhere in `f`: the `if !changed` guard's taken edge,
/// resolved through the self-update to the old value's own name and the second
/// call's result.
fn has_resolved_self_update_guard(f: &Formula) -> bool {
    let here = matches!(f, Formula::Or(xs)
        if xs.len() == 2
            && is_bool_var_rooted_at(&xs[0], "changed")
            && is_bool_var_rooted_at(&xs[1], "_10"));
    here || f.children().into_iter().any(has_resolved_self_update_guard)
}

#[test]
fn self_updated_bool_read_by_its_switch_does_not_overflow_the_stack() {
    let vcs = generate_on_ordinary_stack(self_update_fixture());
    // The `v / 2 + 1` row sits UNDER the `if !changed` guard, so its formula carries
    // the lowered guard — the step that used to recurse forever.
    let add_rows: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();
    assert!(
        !add_rows.is_empty(),
        "the guarded `v / 2 + 1` overflow row must be generated; got {:#?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
    for vc in &add_rows {
        assert!(
            has_resolved_self_update_guard(&vc.formula),
            "the `if !changed` guard must be lowered as `changed | _10`, not dropped; \
             formula: {:?}",
            vc.formula
        );
    }
    // The function is safe (`v / 2 + 1 <= u32::MAX / 2 + 1`), so no row may be
    // refuted. This lane stops at "not refuted": the deterministic in-process ay
    // lane answers `Unknown (incomplete self-check-rejected)` — strict certification
    // of its UNSAT proof — for this row's arithmetic even on an `if c { .. }` twin
    // with no self-update read (measured 2026-09-25), which the stage-1 compiler
    // proves and kernel-certifies. That verdict is a property of the lane, not of
    // the guard.
    for vc in vcs.iter().filter(|vc| is_arithmetic_row(vc)) {
        let result = verdict(vc);
        assert!(
            !matches!(result, VerificationResult::Failed { .. }),
            "{:?} under `if !changed` is safe; a refutation is a false refutation of valid \
             Rust. got {result:?}\nformula: {:?}",
            vc.kind,
            vc.formula
        );
    }
}

#[test]
fn ordinary_single_block_bitand_guard_still_discharges_its_arm() {
    // Positive control: `ok = (x >= 2) & (x <= 9); match ok { true => 100 / (x - 1) }`.
    // The division holds only under the guard's `x >= 2`.
    let vcs = generate_on_ordinary_stack(range_control_fixture());
    let rows: Vec<_> = vcs.iter().filter(|vc| is_arithmetic_row(vc)).collect();
    assert!(
        rows.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "the guarded `100 / (x - 1)` division row must be generated; got {:#?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
    for vc in rows {
        let result = verdict(vc);
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "{:?} under `(x >= 2) & (x <= 9)` must be PROVED; got {result:?}\nformula: {:?}",
            vc.kind,
            vc.formula
        );
    }
}
