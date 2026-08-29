// Callsite L0 replay (refutation-only) — unit tests.
//
// The load-bearing invariant under test: a replay candidate is emitted ONLY
// when the composed formula is fully caller-scoped (no residual callee local,
// no σ-fresh free var, no modeling-gap sentinel), because the driver treats a
// SAT model of a candidate as a GENUINE counterexample execution. Every gate
// is drop-only, so each negative test is a soundness test (a dropped candidate
// can only lose a refutation, an admitted unsound one would mint a false L0
// refutation).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, Formula, LocalDecl, Operand, Place, Projection,
    Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody,
    VerifiableFunction,
};

use super::{
    composed_formula_is_caller_entry_grounded, generate_callsite_l0_replay_candidates,
    replay_substituted_callee_violation,
};
use crate::modular::{FunctionSummary, SummaryDatabase};

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// A distinctive call span so the site-matching (name AND span) is exercised
/// rather than defaulted.
fn call_span() -> SourceSpan {
    SourceSpan { file: "replay.rs".into(), line_start: 7, col_start: 5, line_end: 7, col_end: 20 }
}

/// The mutant fixture's callee: `fn helper(a: [u8; 4], i: usize) -> u8 { a[i] }`
/// in the MIR bounds-assert shape rustc emits (Len / Lt / Assert / read),
/// mirroring `bounds_const_index_tests::array_read_fn`. Its `#[requires
/// (i < 4)]` is carried in `preconditions`, so `generate_vcs` on the UNSTRIPPED
/// body discharges the bounds VC and the replay's strip step is observable.
fn helper_callee() -> VerifiableFunction {
    VerifiableFunction {
        name: "helper".to_string(),
        def_path: "test::helper".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u8(), name: Some("_0".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 4 },
                    name: Some("a".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("i".into()),
                },
                LocalDecl { index: 3, ty: Ty::Int { width: 64, signed: false }, name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        assign(Place::local(3), Rvalue::Len(Place::local(1))),
                        assign(
                            Place::local(4),
                            Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(3)),
                            ),
                        ),
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::local(4)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Index(2)],
                        })),
                    )],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u8(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![
            // #[requires(i < 4)]
            Formula::Lt(Box::new(Formula::var("i", Sort::Int)), Box::new(Formula::Int(4))),
        ],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The mutant fixture's caller: `fn caller(a: [u8; 4], i: usize) -> u8
/// { helper(a, i) }` — the index flows through UNCONSTRAINED.
fn unguarded_caller() -> VerifiableFunction {
    VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u8(), name: Some("_0".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 4 },
                    name: Some("a".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("i".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
                        func: "test::helper".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: call_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u8(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn helper_summary_with_body() -> FunctionSummary {
    FunctionSummary::new("test::helper")
        .with_param_names(vec!["a".to_string(), "i".to_string()])
        .with_precondition(Formula::Lt(
            Box::new(Formula::var("i", Sort::Int)),
            Box::new(Formula::Int(4)),
        ))
        .with_extracted_body(std::sync::Arc::new(helper_callee()))
}

fn sigma_i_to_x() -> Vec<(String, Formula)> {
    vec![("i".to_string(), Formula::var("x", Sort::Int))]
}

// ---------------------------------------------------------------------------
// The substitution filter (caller-scoped-only formulas retained).
// ---------------------------------------------------------------------------

#[test]
fn filter_retains_fully_caller_scoped_violation() {
    // Callee violation `i >= 4` over the σ-mapped formal `i` → `x >= 4`.
    let violation = Formula::Ge(Box::new(Formula::var("i", Sort::Int)), Box::new(Formula::Int(4)));
    let out = replay_substituted_callee_violation(&violation, &sigma_i_to_x())
        .expect("formal-only violation must survive the filter");
    assert_eq!(
        out,
        Formula::Ge(Box::new(Formula::var("x", Sort::Int)), Box::new(Formula::Int(4))),
        "substitution must rebind the formal to the caller actual"
    );
}

#[test]
fn filter_drops_residual_callee_local() {
    // `_5 >= 4`: a callee temp with no σ entry. Left free it would either be
    // an unconstrained model dimension or be captured by the caller's `_5`.
    let violation = Formula::Ge(Box::new(Formula::var("_5", Sort::Int)), Box::new(Formula::Int(4)));
    assert!(
        replay_substituted_callee_violation(&violation, &sigma_i_to_x()).is_none(),
        "residual callee local must drop the candidate"
    );
}

#[test]
fn filter_drops_unpinned_temp_in_conjunction() {
    // `_7` appears only under an INEQUALITY — no `Eq` pin, so it is an
    // unconstrained model dimension. The WHOLE candidate must drop.
    let violation = Formula::And(vec![
        Formula::Ge(Box::new(Formula::var("i", Sort::Int)), Box::new(Formula::Int(4))),
        Formula::Ge(Box::new(Formula::var("_7", Sort::Int)), Box::new(Formula::Int(0))),
    ]);
    assert!(replay_substituted_callee_violation(&violation, &sigma_i_to_x()).is_none());
}

#[test]
fn filter_renames_def_pinned_temps_into_replay_namespace() {
    // The real body-VC shape: violation beside its def chain
    // (`_3 == 4`, `_4 == (i < _3)`, `i >= _3`). Both temps are Eq-pinned and
    // ground out in the σ domain, so the candidate is RETAINED with the temps
    // alpha-renamed into the capture-proof `__trust_replay__` namespace and
    // the formal rebound to the caller actual.
    let violation = Formula::And(vec![
        Formula::Eq(Box::new(Formula::var("_3", Sort::Int)), Box::new(Formula::Int(4))),
        Formula::Eq(
            Box::new(Formula::var("_4", Sort::Bool)),
            Box::new(Formula::Lt(
                Box::new(Formula::var("i", Sort::Int)),
                Box::new(Formula::var("_3", Sort::Int)),
            )),
        ),
        Formula::Ge(
            Box::new(Formula::var("i", Sort::Int)),
            Box::new(Formula::var("_3", Sort::Int)),
        ),
    ]);
    let out = replay_substituted_callee_violation(&violation, &sigma_i_to_x())
        .expect("def-pinned temps must be admitted");
    let fv = out.free_variables();
    assert!(fv.contains("x"), "σ image must appear: {fv:?}");
    assert!(fv.contains("__trust_replay___3"), "temp _3 renamed: {fv:?}");
    assert!(fv.contains("__trust_replay___4"), "temp _4 renamed: {fv:?}");
    assert!(
        !fv.contains("_3") && !fv.contains("_4") && !fv.contains("i"),
        "no raw callee names: {fv:?}"
    );
}

#[test]
fn filter_drops_temp_pinned_only_through_unpinned_temp() {
    // `_4 == _5 + 1` pins `_4` only if `_5` grounds out — it does not, so the
    // fixpoint must reject the whole candidate.
    let violation = Formula::And(vec![
        Formula::Eq(
            Box::new(Formula::var("_4", Sort::Int)),
            Box::new(Formula::Add(
                Box::new(Formula::var("_5", Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
        ),
        Formula::Ge(
            Box::new(Formula::var("i", Sort::Int)),
            Box::new(Formula::var("_4", Sort::Int)),
        ),
    ]);
    assert!(replay_substituted_callee_violation(&violation, &sigma_i_to_x()).is_none());
}

#[test]
fn filter_drops_bool_sentinels() {
    // `Bool(true)` fail-close markers and `Bool(false)` reconstruction
    // placeholders model no operation; "refuting" one is a false refutation.
    assert!(
        replay_substituted_callee_violation(&Formula::Bool(true), &sigma_i_to_x()).is_none(),
        "Bool(true) fail-close sentinel must be skipped"
    );
    assert!(
        replay_substituted_callee_violation(&Formula::Bool(false), &sigma_i_to_x()).is_none(),
        "Bool(false) placeholder sentinel must be skipped"
    );
}

#[test]
fn filter_drops_sigma_opaque_replacement_values() {
    // σ maps `i` to the aliasing-opaque fresh var (`sigma_actual_formula`'s
    // fallback for an unevaluated-const actual). The substituted formula's
    // model would range freely over it — not a witness of any execution.
    let sigma = vec![(
        "i".to_string(),
        Formula::var_owned("__trust_sigma_opaque__i".to_string(), Sort::Int),
    )];
    let violation = Formula::Ge(Box::new(Formula::var("i", Sort::Int)), Box::new(Formula::Int(4)));
    assert!(
        replay_substituted_callee_violation(&violation, &sigma).is_none(),
        "a σ-fresh opaque replacement must drop the candidate"
    );
}

#[test]
fn filter_drops_projected_formal_rebound_to_fresh_field_var() {
    // `self.0` under `self -> <compound expr>`: `rebind_projected_actual`
    // falls back to the fresh `__trust_sigma_field__` namespace (no bare
    // caller place to reattach the projection to). Fine for the fail-closed
    // precondition lane; free model dimension here — must drop.
    let sigma = vec![(
        "self".to_string(),
        Formula::Add(Box::new(Formula::var("x", Sort::Int)), Box::new(Formula::Int(1))),
    )];
    let violation =
        Formula::Ge(Box::new(Formula::var("self.0", Sort::Int)), Box::new(Formula::Int(4)));
    assert!(
        replay_substituted_callee_violation(&violation, &sigma).is_none(),
        "a σ-field fresh rebind must drop the candidate"
    );
}

#[test]
fn filter_retains_projected_formal_rebound_to_bare_actual_place() {
    // `self.0` under `self -> a` reattaches to the caller's `a.0` — a real
    // caller place, fully scoped. Retained.
    let sigma = vec![("self".to_string(), Formula::var("a", Sort::Int))];
    let violation =
        Formula::Ge(Box::new(Formula::var("self.0", Sort::Int)), Box::new(Formula::Int(4)));
    let out = replay_substituted_callee_violation(&violation, &sigma)
        .expect("bare-place projection rebind is caller-scoped");
    assert_eq!(
        out,
        Formula::Ge(Box::new(Formula::var("a.0", Sort::Int)), Box::new(Formula::Int(4)))
    );
}

#[test]
fn filter_ignores_quantifier_bound_names() {
    // `free_variables` is binder-aware: a bound `k` outside the σ domain is
    // NOT a residual callee local.
    let violation = Formula::Forall(
        vec![("k".into(), Sort::Int)],
        Box::new(Formula::Or(vec![
            Formula::Lt(Box::new(Formula::var("k", Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(Formula::var("i", Sort::Int)), Box::new(Formula::Int(4))),
        ])),
    );
    assert!(
        replay_substituted_callee_violation(&violation, &sigma_i_to_x()).is_some(),
        "binder-bound names must not be mistaken for callee locals"
    );
}

// ---------------------------------------------------------------------------
// The composed-candidate producer.
// ---------------------------------------------------------------------------

#[test]
fn composed_candidate_carries_def_pinned_violation_over_caller_inputs() {
    // The composed formula for the mutant-fixture shape must be exactly the
    // callee's def-pinned violation rebound to caller inputs:
    //   __trust_replay___3 == 4
    //   __trust_replay___4 == (i < __trust_replay___3)
    //   i >= __trust_replay___3        <- the violation, i = the CALLER's i
    // SAT with i = 4 — the real OOB witness — while every temp is renamed
    // into the capture-proof replay namespace and functionally pinned.
    let caller = unguarded_caller();
    let mut summaries = SummaryDatabase::new();
    summaries.insert(helper_summary_with_body());
    let candidates =
        generate_callsite_l0_replay_candidates(&caller, &summaries, "test::helper", &call_span());
    assert_eq!(candidates.len(), 1);
    let Formula::And(conjuncts) = &candidates[0].formula else {
        panic!("composed candidate must be a flat And: {:?}", candidates[0].formula);
    };
    let violation = Formula::Ge(
        Box::new(Formula::var("i", Sort::Int)),
        Box::new(Formula::var("__trust_replay___3", Sort::Int)),
    );
    assert!(
        conjuncts.contains(&violation),
        "the σ-rebound violation must be a DIRECT conjunct: {conjuncts:#?}"
    );
    let len_pin = Formula::Eq(
        Box::new(Formula::var("__trust_replay___3", Sort::Int)),
        Box::new(Formula::Int(4)),
    );
    assert!(
        conjuncts.contains(&len_pin),
        "the callee's Len def must pin the renamed temp: {conjuncts:#?}"
    );
}

#[test]
fn unguarded_caller_yields_l0_candidate_at_call_span() {
    let caller = unguarded_caller();
    let mut summaries = SummaryDatabase::new();
    summaries.insert(helper_summary_with_body());

    let candidates =
        generate_callsite_l0_replay_candidates(&caller, &summaries, "test::helper", &call_span());
    assert_eq!(candidates.len(), 1, "exactly one composed bounds candidate: {candidates:#?}");
    let candidate = &candidates[0];
    assert!(
        matches!(candidate.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck),
        "candidate must carry the callee's REAL L0 kind, got {:?}",
        candidate.kind
    );
    assert_eq!(candidate.location, call_span(), "candidate must sit at the CALL span");
    assert_eq!(candidate.function.as_str(), "caller", "candidate is a CALLER row");
    // Fully caller-scoped: every free var of the composed formula must be a
    // caller-namespace name (here the caller's own locals `a`/`i`; never the
    // callee temps `_3`/`_4`, which vcgen folds into the violation).
    for var in candidate.formula.free_variables() {
        assert!(!var.starts_with("__trust_sigma_"), "no σ-fresh free var may survive: {var}");
    }
}

#[test]
fn candidate_absent_when_extracted_body_missing() {
    // Cross-crate callee: contracts summarize but no body attaches. Replay
    // must decline (honest incomplete residual), never approximate.
    let caller = unguarded_caller();
    let mut summaries = SummaryDatabase::new();
    let mut summary = helper_summary_with_body();
    summary.extracted_body = None;
    summaries.insert(summary);

    assert!(
        generate_callsite_l0_replay_candidates(&caller, &summaries, "test::helper", &call_span(),)
            .is_empty(),
        "no extracted body -> no replay candidates"
    );
}

#[test]
fn candidate_absent_at_wrong_span_or_callee() {
    let caller = unguarded_caller();
    let mut summaries = SummaryDatabase::new();
    summaries.insert(helper_summary_with_body());

    assert!(
        generate_callsite_l0_replay_candidates(
            &caller,
            &summaries,
            "test::helper",
            &SourceSpan::default(),
        )
        .is_empty(),
        "span mismatch must not match a different call site"
    );
    assert!(
        generate_callsite_l0_replay_candidates(&caller, &summaries, "test::other", &call_span())
            .is_empty(),
        "callee-name mismatch must yield nothing"
    );
}

#[test]
fn candidate_absent_for_self_recursive_callee() {
    // #5-PRE-A scoping: the self-call precondition remains an ordinary proof
    // request, but this refutation-only helper must not recursively replay the
    // caller body as its own callee. Candidate absence supplies no authority.
    let mut caller = unguarded_caller();
    // Make the call a self-call in both name spellings.
    if let Terminator::Call { func: callee, .. } = &mut caller.body.blocks[0].terminator {
        *callee = "test::caller".to_string();
    }
    let mut summaries = SummaryDatabase::new();
    let mut summary = helper_summary_with_body();
    summary.name = "test::caller".to_string();
    summaries.insert(summary);

    assert!(
        generate_callsite_l0_replay_candidates(&caller, &summaries, "test::caller", &call_span(),)
            .is_empty(),
        "self-recursive call sites are exempt from replay"
    );
}

#[test]
fn candidate_absent_on_arity_mismatch() {
    let caller = unguarded_caller();
    let mut summaries = SummaryDatabase::new();
    let mut summary = helper_summary_with_body();
    summary.param_names = vec!["a".to_string()]; // one formal, two actuals
    summaries.insert(summary);

    assert!(
        generate_callsite_l0_replay_candidates(&caller, &summaries, "test::helper", &call_span(),)
            .is_empty(),
        "σ would be partial on arity mismatch — must decline"
    );
}

/// `fn guarded(a: [u8; 4], i: usize) { if i < 4 { helper(a, i) } }` — the call
/// is dominated by the exact guard the callee's requires needs.
fn guarded_caller() -> VerifiableFunction {
    let mut func = unguarded_caller();
    func.name = "guarded".to_string();
    func.def_path = "test::guarded".to_string();
    func.body.locals.push(LocalDecl { index: 3, ty: Ty::Bool, name: None });
    let call_terminator = func.body.blocks[0].terminator.clone();
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(3),
                Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(2)),
                    Operand::Constant(trust_types::ConstValue::Uint(4, 64)),
                ),
            )],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(3)),
                targets: vec![(0, BlockId(2))],
                otherwise: BlockId(1),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: call_terminator },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
    ];
    if let Terminator::Call { target, .. } = &mut func.body.blocks[1].terminator {
        *target = Some(BlockId(2));
    }
    func
}

/// The composed candidates' SOLVER semantics — the exact SAT/UNSAT split the
/// driver's replay lane keys refutation on (in-process ay, the same backend
/// `trust_verify.rs` dispatches to):
///   * UNGUARDED caller: SAT with a model naming the caller's `i` — a genuine
///     composed counterexample (`caller([0;4], 4)` really panics OOB).
///   * GUARDED caller (`if i < 4 { helper(a, i) }`): the conjoined path guard
///     makes the violation UNSAT — no refutation may be minted for valid Rust
///     (the anti-over-rejection control).
#[test]
fn solver_refutes_unguarded_and_never_guarded_composition() {
    use trust_router::{InProcessAyBackend, VerificationBackend};
    let backend = InProcessAyBackend::new();

    let mut summaries = SummaryDatabase::new();
    summaries.insert(helper_summary_with_body());

    let caller = unguarded_caller();
    let candidates =
        generate_callsite_l0_replay_candidates(&caller, &summaries, "test::helper", &call_span());
    assert_eq!(candidates.len(), 1);
    assert!(backend.can_handle(&candidates[0]), "ay must admit the composed L0 kind");
    let result = backend.verify(&candidates[0]);
    let trust_types::VerificationResult::Failed { counterexample: Some(cex), .. } = &result else {
        panic!("unguarded composition must be SAT with a model, got {result:?}");
    };
    let index_witness = cex
        .assignments
        .iter()
        .find(|(name, _)| name == "i")
        .expect("the witness must assign the caller's index input");
    if let trust_types::CounterexampleValue::Int(value) = &index_witness.1 {
        assert!(*value >= 4, "the OOB witness must violate i < 4, got {value}");
    }

    let guarded = guarded_caller();
    let guarded_candidates =
        generate_callsite_l0_replay_candidates(&guarded, &summaries, "test::helper", &call_span());
    for candidate in &guarded_candidates {
        let result = backend.verify(candidate);
        assert!(
            !matches!(result, trust_types::VerificationResult::Failed { .. }),
            "a guarded caller must never compose to SAT (false refutation): {result:?}\ncandidate: {:?}",
            candidate.formula
        );
    }

    // CONSERVATIVE-CONTRACT control: the callee's requires is stricter than
    // its actual safety need (a `requires(i < 2)` shielding a len-4 array).
    // A caller passing the constant 3 REFUTES the precondition (3 >= 2, an
    // honest L1 contract violation) but the entailed OOB replay `3 >= 4` is
    // UNSAT — no L0 claim may be minted, so the build still classifies as the
    // (honest) incomplete, never a false refutation.
    let mut constant_caller = unguarded_caller();
    if let Terminator::Call { args, .. } = &mut constant_caller.body.blocks[0].terminator {
        args[1] = Operand::Constant(trust_types::ConstValue::Uint(3, 64));
    }
    let constant_candidates = generate_callsite_l0_replay_candidates(
        &constant_caller,
        &summaries,
        "test::helper",
        &call_span(),
    );
    for candidate in &constant_candidates {
        let result = backend.verify(candidate);
        assert!(
            !matches!(result, trust_types::VerificationResult::Failed { .. }),
            "an in-bounds constant caller must never compose to SAT: {result:?}\ncandidate: {:?}",
            candidate.formula
        );
    }
}

#[test]
fn replay_regenerates_callee_vcs_without_the_requires_shield() {
    // Control for the strip step: the callee's own `generate_vcs` (WITH its
    // `#[requires(i < 4)]` hypothesis) discharges or at least shields the
    // bounds obligation, while the replay candidate must expose the violation
    // over the caller's namespace. The observable here: the composed formula
    // constrains the CALLER's `i` (σ image), proving the callee VC set used by
    // the replay was generated with the hypothesis stripped — otherwise the
    // candidate formula would carry the requires as an entry fact and the
    // composed violation would be structurally UNSAT-by-assumption.
    let caller = unguarded_caller();
    let mut summaries = SummaryDatabase::new();
    summaries.insert(helper_summary_with_body());

    let candidates =
        generate_callsite_l0_replay_candidates(&caller, &summaries, "test::helper", &call_span());
    assert_eq!(candidates.len(), 1);
    let rendered = format!("{:?}", candidates[0].formula);
    assert!(
        !rendered.contains("__trust_sigma_"),
        "composed formula must be σ-fresh-free: {rendered}"
    );
}

// ---------------------------------------------------------------------------
// The caller-side entry-grounding gate (the refutation-side soundness gate:
// no free var of a composed formula may be an unconstrained model dimension).
// ---------------------------------------------------------------------------

/// `fn safe(a: [u8; 4], i: usize) -> u8 { let j = ext::clamp3(i); helper(a, j) }`
/// — `j` is the havoc'd dest of an UNMODELED cross-crate call (no summary, no
/// facts). The real clamp3 keeps `j < 4`, so the caller is SAFE; nothing in
/// the composed model constrains `j`, so a solver model over free `j` (e.g.
/// `j = 9`) denotes NO real execution.
fn havoc_dest_caller() -> VerifiableFunction {
    let mut func = unguarded_caller();
    func.name = "safe".to_string();
    func.def_path = "test::safe".to_string();
    func.body.locals.push(LocalDecl {
        index: 3,
        ty: Ty::Int { width: 64, signed: false },
        name: Some("j".into()),
    });
    let mut helper_call = func.body.blocks[0].terminator.clone();
    if let Terminator::Call { args, target, .. } = &mut helper_call {
        // helper's index actual is now the havoc'd `j`, not the entry `i`.
        args[1] = Operand::Copy(Place::local(3));
        *target = Some(BlockId(2));
    }
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                callee_identity: None,
                is_foreign: false,
                func: "ext::clamp3".to_string(),
                args: vec![Operand::Copy(Place::local(2))],
                dest: Place::local(3),
                target: Some(BlockId(1)),
                span: SourceSpan::default(),
                atomic: None,
            },
        },
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: helper_call },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
    ];
    func
}

#[test]
fn caller_gate_rejects_havocd_call_dest_free_var() {
    // `j >= 4` free over the havoc'd call dest: `j` names a NON-parameter
    // local whose value is chosen by the unmodeled callee, and no conjunct
    // pins it — an unconstrained dimension, so the gate must fail.
    let func = havoc_dest_caller();
    let formula = Formula::Ge(Box::new(Formula::var("j", Sort::Int)), Box::new(Formula::Int(4)));
    assert!(
        !composed_formula_is_caller_entry_grounded(&func, &formula),
        "a havoc'd call-dest free var must fail the caller-side gate"
    );
}

#[test]
fn caller_gate_rejects_r1occ_freshened_opaque_vars() {
    // A `freshen_aliasing_opaque_occurrences` per-occurrence alias is
    // unclassifiable BY NAME — even when an Eq conjunct appears to pin
    // through it, the split-occurrence semantics make it a fabricated model
    // dimension for the SAT direction.
    let func = unguarded_caller();
    let hypothesis_only = Formula::And(vec![
        Formula::Lt(
            Box::new(Formula::var("i", Sort::Int)),
            Box::new(Formula::var("__trust_opaque_scalar_u64__r1occ0", Sort::Int)),
        ),
        Formula::Ge(Box::new(Formula::var("i", Sort::Int)), Box::new(Formula::Int(4))),
    ]);
    assert!(!composed_formula_is_caller_entry_grounded(&func, &hypothesis_only));
    let eq_pinned = Formula::And(vec![
        Formula::Eq(
            Box::new(Formula::var("__trust_constparam_0_N__r1occ1", Sort::Int)),
            Box::new(Formula::Int(4)),
        ),
        Formula::Ge(
            Box::new(Formula::var("i", Sort::Int)),
            Box::new(Formula::var("__trust_constparam_0_N__r1occ1", Sort::Int)),
        ),
    ]);
    assert!(
        !composed_formula_is_caller_entry_grounded(&func, &eq_pinned),
        "an __r1occ var must be rejected by NAME, pin or no pin"
    );
}

#[test]
fn caller_gate_retains_fully_entry_pinned_formulas() {
    let func = unguarded_caller();
    // Bare entry params (never written, no call-dest write, source-stable).
    let over_params =
        Formula::Ge(Box::new(Formula::var("i", Sort::Int)), Box::new(Formula::Int(4)));
    assert!(composed_formula_is_caller_entry_grounded(&func, &over_params));
    // Entry-param projections and __slice_len companions are entry state too.
    let over_projections = Formula::And(vec![
        Formula::Ge(Box::new(Formula::var("a.0", Sort::Int)), Box::new(Formula::Int(1))),
        Formula::Ge(Box::new(Formula::var("a__slice_len", Sort::Int)), Box::new(Formula::Int(4))),
    ]);
    assert!(composed_formula_is_caller_entry_grounded(&func, &over_projections));
    // A non-entry name is admitted exactly when an Eq conjunct grounds it in
    // entry state (the def-pin fixpoint) — this is the computed-actual and
    // `__trust_replay__*` temp admission.
    let def_pinned = Formula::And(vec![
        Formula::Eq(
            Box::new(Formula::var("__trust_replay___3", Sort::Int)),
            Box::new(Formula::Add(
                Box::new(Formula::var("i", Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
        ),
        Formula::Ge(
            Box::new(Formula::var("__trust_replay___3", Sort::Int)),
            Box::new(Formula::Int(4)),
        ),
    ]);
    assert!(composed_formula_is_caller_entry_grounded(&func, &def_pinned));
}

#[test]
fn caller_gate_rejects_unpinned_versioned_and_unknown_names() {
    let func = unguarded_caller();
    // A residual versioned read of a (hypothetically reassigned) local: not a
    // caller place spelling, not pinned — unclassifiable.
    let versioned =
        Formula::Ge(Box::new(Formula::var("i#s0_t", Sort::Int)), Box::new(Formula::Int(4)));
    assert!(!composed_formula_is_caller_entry_grounded(&func, &versioned));
    // A name that resolves to no local at all, unpinned.
    let unknown =
        Formula::Ge(Box::new(Formula::var("ghost", Sort::Int)), Box::new(Formula::Int(4)));
    assert!(!composed_formula_is_caller_entry_grounded(&func, &unknown));
}

// ---------------------------------------------------------------------------
// The ORDINARY BODY-VC shapes. `bridge_v1_ay_proofs_into_native_results` also
// asks this gate about `generate_vcs` output, which is NOT the flat conjunction
// the callsite composer emits. Measured 2026-08-28: every one of the four
// shapes below was judged ungrounded, which silently deleted every Level-0
// refutation the compiler had — `a / d`, `a % d`, `a + b` and `s[i]` all built
// clean under the default policy. These pin the exact formulas the compiler
// produced for those four programs.
// ---------------------------------------------------------------------------

/// `pub fn f(a: u64, d: u64) -> u64 { a / d }`, verbatim from
/// `TRUST_GROUND_DEBUG=1` on stage1 `f402338a5`: a type-range block and a
/// defs/violation block, conjoined — so `_3 == (d == 0)` is two `And` levels
/// below the root.
fn body_vc_two_param_caller() -> VerifiableFunction {
    let mut func = unguarded_caller();
    func.body.locals[1] =
        LocalDecl { index: 1, ty: Ty::Int { width: 64, signed: false }, name: Some("a".into()) };
    func.body.locals[2] =
        LocalDecl { index: 2, ty: Ty::Int { width: 64, signed: false }, name: Some("d".into()) };
    func
}

fn u64_range(name: &str) -> Formula {
    Formula::And(vec![
        Formula::Ge(Box::new(Formula::var(name, Sort::Int)), Box::new(Formula::Int(0))),
        Formula::Le(
            Box::new(Formula::var(name, Sort::Int)),
            Box::new(Formula::Int(18446744073709551615)),
        ),
    ])
}

#[test]
fn caller_gate_admits_a_temp_pinned_in_a_NESTED_and_block() {
    let func = body_vc_two_param_caller();
    // The div-by-zero body VC exactly as emitted.
    let div_by_zero = Formula::And(vec![
        Formula::And(vec![u64_range("a"), u64_range("d")]),
        Formula::And(vec![
            u64_range("a"),
            u64_range("d"),
            Formula::And(vec![
                Formula::Eq(
                    Box::new(Formula::var("_3", Sort::Bool)),
                    Box::new(Formula::Eq(
                        Box::new(Formula::var("d", Sort::Int)),
                        Box::new(Formula::Int(0)),
                    )),
                ),
                Formula::var("_3", Sort::Bool),
            ]),
        ]),
    ]);
    assert!(
        composed_formula_is_caller_entry_grounded(&func, &div_by_zero),
        "`_3 == (d == 0)` pins `_3` in entry state; `∧` is associative, so nesting \
         the conjunct cannot make a grounded refutation ungrounded"
    );
}

#[test]
fn caller_gate_admits_chained_nested_pins_through_a_slice_len() {
    // `pub fn f(s: &[u64], i: usize) -> u64 { s[i] }`, as emitted: `_3` pins to
    // the `__slice_len` companion and `_4` chains off `_3`.
    let mut func = body_vc_two_param_caller();
    func.body.locals[1] = LocalDecl {
        index: 1,
        ty: Ty::Array { elem: Box::new(Ty::u8()), len: 4 },
        name: Some("s".into()),
    };
    func.body.locals[2] =
        LocalDecl { index: 2, ty: Ty::Int { width: 64, signed: false }, name: Some("i".into()) };
    let bounds = Formula::And(vec![
        u64_range("i"),
        Formula::And(vec![
            u64_range("i"),
            Formula::And(vec![
                Formula::Eq(
                    Box::new(Formula::var("_3", Sort::Int)),
                    Box::new(Formula::var("s__slice_len", Sort::Int)),
                ),
                Formula::Eq(
                    Box::new(Formula::var("_4", Sort::Bool)),
                    Box::new(Formula::Lt(
                        Box::new(Formula::var("i", Sort::Int)),
                        Box::new(Formula::var("_3", Sort::Int)),
                    )),
                ),
                Formula::Ge(
                    Box::new(Formula::var("i", Sort::Int)),
                    Box::new(Formula::var("_3", Sort::Int)),
                ),
            ]),
        ]),
    ]);
    assert!(composed_formula_is_caller_entry_grounded(&func, &bounds));
}

/// The `a + b` overflow shape: rustc conditions the destination definition on
/// NOT overflowing, so `_0` is pinned only inside a disjunction — and nowhere
/// else in the formula.
fn overflow_add_body_vc() -> Formula {
    let sum = || {
        Formula::Add(
            Box::new(Formula::var("a", Sort::Int)),
            Box::new(Formula::var("b", Sort::Int)),
        )
    };
    let overflowed = || {
        Formula::Gt(Box::new(sum()), Box::new(Formula::Int(18446744073709551615)))
    };
    Formula::And(vec![
        Formula::And(vec![u64_range("a"), u64_range("b")]),
        Formula::And(vec![
            Formula::Or(vec![
                overflowed(),
                Formula::Eq(Box::new(Formula::var("_0", Sort::Int)), Box::new(sum())),
            ]),
            Formula::Or(vec![
                Formula::Lt(Box::new(sum()), Box::new(Formula::Int(0))),
                overflowed(),
            ]),
        ]),
    ])
}

#[test]
fn caller_gate_admits_a_dest_pinned_only_under_its_non_overflow_disjunct() {
    let func = body_vc_two_param_caller();
    let mut func = func;
    func.body.locals[2] =
        LocalDecl { index: 2, ty: Ty::Int { width: 64, signed: false }, name: Some("b".into()) };
    assert!(
        composed_formula_is_caller_entry_grounded(&func, &overflow_add_body_vc()),
        "`_0` occurs in exactly one conjunct and is repairable to `a + b` there, \
         so the model's input projection denotes a real execution"
    );
}

#[test]
fn caller_gate_still_rejects_a_disjunctively_pinned_temp_used_elsewhere() {
    // Same disjunctive pin, but the temp is ALSO read by the violation. The
    // repair would change that conjunct's truth value, so it must fail closed.
    let mut func = body_vc_two_param_caller();
    func.body.locals[2] =
        LocalDecl { index: 2, ty: Ty::Int { width: 64, signed: false }, name: Some("b".into()) };
    let Formula::And(mut blocks) = overflow_add_body_vc() else { unreachable!() };
    blocks.push(Formula::Gt(
        Box::new(Formula::var("_0", Sort::Int)),
        Box::new(Formula::Int(7)),
    ));
    assert!(!composed_formula_is_caller_entry_grounded(&func, &Formula::And(blocks)));
}

#[test]
fn caller_gate_still_rejects_a_havocd_dest_pinned_by_no_disjunct() {
    // The campaign's case, re-stated in the nested shape the flattening now
    // walks: `j` is the unmodeled callee's return, so NO conjunct and no
    // disjunct defines it. Flattening must not invent a pin for it.
    let func = havoc_dest_caller();
    let formula = Formula::And(vec![
        Formula::And(vec![u64_range("i")]),
        Formula::And(vec![Formula::Or(vec![
            Formula::Ge(Box::new(Formula::var("i", Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(Formula::var("j", Sort::Int)), Box::new(Formula::Int(4))),
        ])]),
    ]);
    assert!(
        !composed_formula_is_caller_entry_grounded(&func, &formula),
        "a havoc'd call-dest free var stays an unconstrained model dimension"
    );
}

#[test]
fn caller_gate_still_rejects_a_bare_eq_over_an_opaque_value() {
    // `opaque_call_result == 0` as the WHOLE formula is the obligation's
    // violation, not a definition of its subject. Reading it as a pin is the
    // exact false refutation the campaign closed, so the top of the formula
    // must still be required to be a conjunction.
    let func = havoc_dest_caller();
    let violation = Formula::Eq(
        Box::new(Formula::var("j", Sort::Int)),
        Box::new(Formula::Int(0)),
    );
    assert!(!composed_formula_is_caller_entry_grounded(&func, &violation));
    // SCOPE, stated rather than implied: the fixpoint cannot tell `_3 == 4`
    // (a legitimate constant block def, named as such in
    // `callee_temps_are_def_pinned`'s own doc) from `j == 0` (a violation over
    // an opaque value) once either is a conjunct, so `And([j == 0])` DOES
    // ground `j` — and did before the flattening landed, one level up. That
    // ambiguity is pre-existing and is deliberately not touched here; what this
    // test pins is that the ROOT of the formula must still be a conjunction, so
    // the campaign's `opaque_call_result == 0` case keeps failing closed.
}

// ---------------------------------------------------------------------------
// The end-to-end fixture PAIR at the composition level: the gate must drop the
// SAFE havoc-dest caller's composition before any solver sees it, while the
// genuine-violation caller's composition survives the gate and stays SAT.
// ---------------------------------------------------------------------------

#[test]
fn safe_havoc_dest_caller_composition_is_dropped_by_the_gate() {
    // `let j = ext::clamp3(i); helper(a, j)`: pre-gate, σ renders helper's
    // index actual as the free `j` (the stable-copy-root fold refuses a
    // call-dest local), and no caller fact pins it — the exact false-SAT
    // vector (`j = 9` "witnesses" an OOB the real clamp3 makes unreachable).
    // The caller-side gate must yield NO candidate at all.
    let caller = havoc_dest_caller();
    let mut summaries = SummaryDatabase::new();
    summaries.insert(helper_summary_with_body()); // ext::clamp3 stays unmodeled
    let candidates =
        generate_callsite_l0_replay_candidates(&caller, &summaries, "test::helper", &call_span());
    assert!(
        candidates.is_empty(),
        "a havoc'd-actual composition must be DROPPED (never reach a solver): {candidates:#?}"
    );
}

#[test]
fn genuine_violation_caller_composition_survives_gate_and_stays_sat() {
    use trust_router::{InProcessAyBackend, VerificationBackend};
    // The pair's other half: the unguarded caller passes the ENTRY `i` raw,
    // every free var of the composition is entry state or def-pinned, so the
    // gate retains it and the solver still finds the real OOB witness.
    let caller = unguarded_caller();
    let mut summaries = SummaryDatabase::new();
    summaries.insert(helper_summary_with_body());
    let candidates =
        generate_callsite_l0_replay_candidates(&caller, &summaries, "test::helper", &call_span());
    assert_eq!(candidates.len(), 1, "the genuine composition must survive the gate");
    let backend = InProcessAyBackend::new();
    let result = backend.verify(&candidates[0]);
    assert!(
        matches!(
            &result,
            trust_types::VerificationResult::Failed { counterexample: Some(cex), .. }
                if !cex.assignments.is_empty()
        ),
        "the genuine composition must stay SAT with a model after the gate: {result:?}"
    );
}
