// Regression (over-refutation audit #8): a `#[ensures]` over the result of an
// integer std `Ord::clamp`/`min`/`max` call was FALSELY REFUTED when the function
// returns the ordered result directly (the `range_usize` shape
// `…unwrap_or(lo).clamp(lo, hi)` with `#[ensures(|r| lo <= *r <= hi)]`).
//
// The min/max/clamp result bound WAS modeled (`build_semantic_guard_map`), but it
// named the Call dest via the `place_to_var_name` alias `__ret` — which does NOT
// reach the postcondition's `_0` in the postcondition lane
// (`normalize_ssa_version_tokens` collapses `__ret#tok` to the debug base `__ret`,
// never `_0`). So the `¬(lo <= _0 <= hi)` obligation stayed havoc'd and the
// valid postcondition refuted (and, under the strict default, the trust-mc/native
// CHC lane that solves this same VC formula produced a counterexample).
//
// The fix re-emits the SAME (sound) result bound under the RAW `_0` the `#[ensures]`
// reads — identical to the saturating/wrapping_neg return pins — via the shared
// `ord_min_max_clamp_result_facts`. These tests assert the postcondition VC formula
// now CARRIES the bound over `_0`, in the sound shape:
//   * min/max — an UNCONDITIONAL bound (`_0 <= a`, `_0 >= a`);
//   * clamp — the GUARDED bound `(lo <= hi) -> lo <= _0 <= hi` (vacuous when `lo > hi`,
//     since clamp PANICS there — so a clamp cannot false-prove its postcondition).
//
// The actual UNSAT/SAT verdicts were separately confirmed with the in-process ay
// solver (structural checks here keep the suite free of the ay-backend dep):
//   correct clamp post + precond lo<=hi  -> PROVED
//   correct clamp post, NO lo<=hi        -> not proved (guarded fact vacuous)
//   FALSE clamp post (_0<lo / _0>hi)     -> not proved
//   min post (_0<=a) / max post (_0>=a)  -> PROVED
//   FALSE min post (_0<a)                -> not proved
//   const lo>hi clamp                    -> not proved (guarded fact vacuous)
use trust_types::*;

/// A `range_usize`-shaped function: `_0 = clamp(_3, lo, hi); return`, with the
/// `#[ensures(|r| lo <= *r <= hi)]` postcondition. `precond` toggles a declared
/// `#[requires(lo <= hi)]` (in `range_usize` this comes from a body `assert!`).
fn clamp_ret_fn(precond: bool) -> VerifiableFunction {
    let usize_ty = Ty::Int { width: 64, signed: false };
    let preconditions = if precond {
        vec![Formula::Le(
            Box::new(Formula::Var("lo".into(), Sort::Int)),
            Box::new(Formula::Var("hi".into(), Sort::Int)),
        )]
    } else {
        vec![]
    };
    VerifiableFunction {
        name: "range_usize".into(),
        def_path: "range_usize".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: usize_ty.clone(), name: Some("__ret".into()) },
                LocalDecl { index: 1, ty: usize_ty.clone(), name: Some("lo".into()) },
                LocalDecl { index: 2, ty: usize_ty.clone(), name: Some("hi".into()) },
                LocalDecl { index: 3, ty: usize_ty.clone(), name: Some("x".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,
                        func: "core::cmp::Ord::clamp".into(),
                        args: vec![
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 3,
            return_ty: usize_ty,
        },
        contracts: vec![],
        preconditions,
        // lo <= _0 && _0 <= hi
        postconditions: vec![Formula::And(vec![
            Formula::Le(
                Box::new(Formula::Var("lo".into(), Sort::Int)),
                Box::new(Formula::Var("_0".into(), Sort::Int)),
            ),
            Formula::Le(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Var("hi".into(), Sort::Int)),
            ),
        ])],
        spec: Default::default(),
    }
}

/// A clamp with CONSTANT `lo`/`hi` bounds and an arbitrary postcondition.
fn clamp_const_ret_fn(lo: i128, hi: i128, post: Formula) -> VerifiableFunction {
    let mut f = clamp_ret_fn(false);
    f.body.blocks[0].terminator = Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,
        func: "core::cmp::Ord::clamp".into(),
        args: vec![
            Operand::Copy(Place::local(3)),
            Operand::Constant(ConstValue::Int(lo)),
            Operand::Constant(ConstValue::Int(hi)),
        ],
        dest: Place::local(0),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        is_foreign: false,
    };
    f.postconditions = vec![post];
    f
}

/// `_0 = <method>(a, b); return` with an arbitrary postcondition (min/max).
fn ord2_ret_fn(method: &str, post: Formula) -> VerifiableFunction {
    let mut f = clamp_ret_fn(false);
    f.body.locals[1].name = Some("a".into());
    f.body.locals[2].name = Some("b".into());
    f.body.blocks[0].terminator = Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,
        func: format!("core::cmp::Ord::{method}"),
        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        dest: Place::local(0),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        is_foreign: false,
    };
    f.postconditions = vec![post];
    f
}

fn postcondition_dbg(func: &VerifiableFunction) -> String {
    let vcs = trust_vcgen::generate_vcs(func);
    let post = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Postcondition))
        .expect("the #[ensures] clause should produce a Postcondition VC");
    format!("{:?}", post.formula)
}

// (1) A `range_usize`-shaped clamp return with `#[requires(lo <= hi)]`: the
// Postcondition VC must CARRY the clamp result bound over the RETURN slot `_0`
// AND the `lo <= hi` hypothesis, so `¬(lo<=_0<=hi) ∧ (lo<=hi) ∧ ((lo<=hi)->lo<=_0<=hi)`
// is UNSAT (provable). Confirmed PROVED by the in-process ay solver.
#[test]
fn clamp_return_carries_guarded_bound_over_ret_and_is_provable_with_lo_le_hi() {
    let dbg = postcondition_dbg(&clamp_ret_fn(true));
    // The clamp bound is pinned to `_0` (NOT only the disconnected `__ret` alias).
    assert!(
        dbg.contains(
            "And([Ge(Var(\"_0\", Int), Var(\"lo\", Int)), Le(Var(\"_0\", Int), Var(\"hi\", Int))])"
        ),
        "clamp result bound must be pinned to the return slot `_0`: {dbg}"
    );
    // It is emitted in the sound GUARDED form `(lo > hi) OR (lo <= _0 <= hi)`.
    assert!(
        dbg.contains("Or([Gt(Var(\"lo\", Int), Var(\"hi\", Int)), And([Ge(Var(\"_0\", Int)"),
        "clamp bound over `_0` must be GUARDED by `Gt(lo, hi)`: {dbg}"
    );
    // The `lo <= hi` hypothesis is present (from the precondition), which discharges
    // the guard and makes the obligation UNSAT.
    assert!(
        dbg.contains("Le(Var(\"lo\", Int), Var(\"hi\", Int))"),
        "the `lo <= hi` hypothesis must be present so the guarded bound discharges: {dbg}"
    );
}

// (2) SOUNDNESS — no `lo <= hi` guarantee: the clamp bound over `_0` is still emitted,
// but GUARDED, and NO `lo <= hi` hypothesis is present, so the guarded fact is vacuous
// (satisfiable via `lo > hi`) and the postcondition is NOT falsely proved.
// Confirmed NOT-proved by the in-process ay solver.
#[test]
fn clamp_return_without_lo_le_hi_stays_vacuously_guarded() {
    let dbg = postcondition_dbg(&clamp_ret_fn(false));
    assert!(
        dbg.contains("Or([Gt(Var(\"lo\", Int), Var(\"hi\", Int)), And([Ge(Var(\"_0\", Int)"),
        "clamp bound over `_0` must remain GUARDED by `Gt(lo, hi)`: {dbg}"
    );
    // With no precondition, `lo <= hi` is never established, so the guard is never
    // discharged — the fact contributes nothing and cannot false-prove.
    assert!(
        !dbg.contains("Le(Var(\"lo\", Int), Var(\"hi\", Int))"),
        "no `lo <= hi` hypothesis may appear without a declared requires: {dbg}"
    );
}

// (2b) SOUNDNESS — a CONSTANT `lo > hi` clamp (which PANICS at runtime): the bound
// must be the GUARDED disjunction (never the unconditional `5 <= _0 <= 2`
// contradiction that would vacuously false-prove any obligation). Confirmed
// NOT-proved by the in-process ay solver.
#[test]
fn clamp_const_lo_gt_hi_is_guarded_never_unconditional() {
    let dbg = postcondition_dbg(&clamp_const_ret_fn(
        5,
        2,
        Formula::Le(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        ),
    ));
    // The guard `Gt(5, 2)` proves the GUARDED arm was chosen (not the unconditional
    // bound). ay does not fold the constant comparison, so the disjunct stays
    // vacuously satisfiable and never discharges the obligation.
    assert!(
        dbg.contains("Or([Gt(Int(5), Int(2)), And([Ge(Var(\"_0\", Int), Int(5))"),
        "a constant `lo > hi` clamp must keep the guarded (Or) form: {dbg}"
    );
}

// (3) A `min`-return postcondition: the UNCONDITIONAL bound `_0 <= a` must be pinned
// to `_0`, so `#[ensures(|r| *r <= a)]` proves. Confirmed PROVED by the ay solver.
#[test]
fn min_return_carries_unconditional_bound_over_ret() {
    let dbg = postcondition_dbg(&ord2_ret_fn(
        "min",
        Formula::Le(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Var("a".into(), Sort::Int)),
        ),
    ));
    assert!(
        dbg.contains("Le(Var(\"_0\", Int), Var(\"a\", Int))")
            && dbg.contains("Le(Var(\"_0\", Int), Var(\"b\", Int))"),
        "min result must pin `_0 <= a` AND `_0 <= b` over the return slot: {dbg}"
    );
}

// (3b) A `max`-return postcondition: the UNCONDITIONAL bound `_0 >= a` over `_0`.
// Confirmed PROVED by the ay solver.
#[test]
fn max_return_carries_unconditional_bound_over_ret() {
    let dbg = postcondition_dbg(&ord2_ret_fn(
        "max",
        Formula::Ge(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Var("a".into(), Sort::Int)),
        ),
    ));
    assert!(
        dbg.contains("Ge(Var(\"_0\", Int), Var(\"a\", Int))")
            && dbg.contains("Ge(Var(\"_0\", Int), Var(\"b\", Int))"),
        "max result must pin `_0 >= a` AND `_0 >= b` over the return slot: {dbg}"
    );
}
