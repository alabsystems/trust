// trust-certify: the kernel may not mint proof authority for an obligation whose
// violation formula is not a statement about the program.
//
// WHY THIS TEST EXISTS.
//
// `certify_vc` mints a zero-trust `CleanCic` certificate on a kernel-checked
// UNSAT of `vc.formula`, and two compiler routes turn that certificate into a
// `Proved { solver: "clean-kernel-certified" }` row — `promote_kernel_certifiable`
// and the bridge certify-fallback, both in `rustc_mir_transform::trust_verify`.
// Neither inspected `vc.kind`. Their shared soundness argument is the fallback's
// comment: "a genuinely-violable obligation has a SAT violation, so it stays
// undecided (never a false Proved)."
//
// That argument holds only when `vc.formula` conjoins the reaching program state
// with the negated predicate. `VcKind::ContractInvariant` does not: an
// item-position `#[invariant(..)]` names no program point, so vcgen mints
// `formula: Not(parsed)` with nothing else. UNSAT of `¬P` is validity of `P`, so
// the row is provable exactly when P constrains nothing.
//
// MEASURED on the sealed toolchain `trust-e26541e3` through the `register_tool`
// surface, over `pub fn f(x: u32) -> u32 { x / 2 }`:
//
//     #[trust::invariant(1 == 1)] -> proved, solver=clean-kernel-certified
//     #[trust::invariant(x == x)] -> proved, solver=clean-kernel-certified
//     #[trust::invariant(x >= 0)] -> unknown   (true of EVERY u32)
//     #[trust::invariant(true)]   -> unknown
//     #[trust::invariant(false)]  -> unknown
//
// The provable set is EXACTLY the tautologies — the signature of a false-proof
// class. Those rows carry `kind: "invariant"` at `ProofLevel::L1Functional`,
// i.e. they are precisely what a ratchet counts as `proved_by_kind.invariant`
// and `kernel_certified`.
//
// The kernel is not at fault and the certificate is not forged: the kernel is
// asked a true question ("is ¬(1 == 1) unsatisfiable?") and answers truthfully.
// The defect is that the question is not about the program. So the fix is an
// admission gate on the KIND, applied before any solver or kernel work.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

fn span() -> SourceSpan {
    SourceSpan {
        file: "src/lib.rs".to_string(),
        line_start: 3,
        col_start: 1,
        line_end: 3,
        col_end: 28,
    }
}

fn vc(kind: VcKind, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: "f".into(),
        location: span(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

/// `¬(1 == 1)` — the violation formula vcgen mints for `#[invariant(1 == 1)]`.
/// It is UNSAT, and it is UNSAT for a reason that has nothing to do with any
/// program: the clause text is a tautology.
fn tautology_violation() -> Formula {
    Formula::Not(Box::new(Formula::Eq(Box::new(Formula::Int(1)), Box::new(Formula::Int(1)))))
}

/// `¬(x == x)` — the second measured leak. UNSAT over a FREE variable, which is
/// exactly the "free variables standing for program values" case: nothing binds
/// `x` to anything the program computes.
fn free_var_tautology_violation() -> Formula {
    let x = || Formula::Var("x".to_string(), Sort::Int);
    Formula::Not(Box::new(Formula::Eq(Box::new(x()), Box::new(x()))))
}

/// An order-shaped unsigned-BV contradiction in the exact bounded family the
/// native-planning certificate route recognizes: `idx < 10 ∧ 10 ≤ idx`.
/// Unlike the equality tautologies above, this reaches the planning recognizer,
/// so it detects a kind gate missing specifically from that second entry point.
fn native_planning_tautology_violation() -> Formula {
    let width = 64;
    let idx = || Box::new(Formula::Var("idx".to_string(), Sort::BitVec(width)));
    let bv = |value: i128| Box::new(Formula::BitVec { value, width });
    Formula::And(vec![
        Formula::And(vec![
            Formula::BvULe(bv(0), idx(), width),
            Formula::BvULe(idx(), bv(u64::MAX as i128), width),
        ]),
        Formula::BvULt(idx(), bv(10), width),
        Formula::BvULe(bv(10), idx(), width),
    ])
}

/// THE PRIMARY LOCK.
///
/// A `ContractInvariant` row whose violation formula is UNSAT must NOT mint a
/// certificate. Both measured leaks are covered.
///
/// MUTATION PROOF: delete the `kernel_authority_refusal` early return from
/// `certify_vc` and this test fails — `certify_with_identity` certifies both
/// formulas (they are exactly the linear-integer contradictions the lane is
/// built to refute), which is how the leak arose in the first place. The
/// assertion is on the PRODUCED ARTIFACT (`is_none()`), not on a status string,
/// so it cannot pass vacuously.
#[test]
fn contract_invariant_never_mints_kernel_authority() {
    for (label, violation) in
        [("1 == 1", tautology_violation()), ("x == x", free_var_tautology_violation())]
    {
        let vc = vc(VcKind::ContractInvariant { expression: label.to_string() }, violation);
        assert!(
            trust_certify::certify_vc(&vc).is_none(),
            "item-position `invariant({label})` minted a kernel certificate; UNSAT of its \
             violation formula proves only that the clause text is a tautology, and such a row \
             lands in proved_by_kind.invariant AND kernel_certified"
        );
    }
}

/// The bounded native-planning API is a second whole-VC certificate route and
/// must enforce the same kind boundary as `certify_vc`.
///
/// The SAME formula is used for every row. Both refused kinds (and a record-less TINV row,
/// refused by the row gate since step 7.7 admitted the kind) must mint no artifact;
/// `IndexOutOfBounds` must still mint one. The resource preflight also
/// restricts the current family to `IndexOutOfBounds`, giving two independent
/// fail-closed layers; this test pins the public artifact boundary rather than
/// depending on which one refuses first.
#[test]
fn native_planning_certificate_route_obeys_the_kind_gate() {
    let formula = native_planning_tautology_violation();
    for kind in [
        VcKind::ContractInvariant { expression: "idx <= idx".to_string() },
        VcKind::TypeRefinementViolation {
            variable: "idx".to_string(),
            predicate: "idx <= idx".to_string(),
        },
        tinv_kind(),
    ] {
        let refused = vc(kind, formula.clone());
        assert!(
            !trust_certify::vc_fits_native_planning_certification_budget(&refused),
            "the resource preflight must independently keep its exact bounds-check kind gate"
        );
        assert!(
            trust_certify::certify_vc_for_native_planning(&refused).is_none(),
            "a refused kind minted CleanCic evidence through the native-planning route"
        );
    }

    let faithful = vc(VcKind::IndexOutOfBounds, formula);
    assert!(
        trust_certify::vc_fits_native_planning_certification_budget(&faithful),
        "the same bounded formula must fit under the admitted kind"
    );
    assert!(
        trust_certify::certify_vc_for_native_planning(&faithful).is_some(),
        "the identical program-point-bearing bounds obligation must retain planning authority"
    );
}

/// The gate keys on the KIND, not on the formula.
///
/// This is the test that makes the previous one meaningful. The SAME UNSAT
/// formula is presented under a kind whose formula IS faithful — a loop clause,
/// which carries a `header_block` program point — and it still certifies. So
/// `certify_vc` did not simply lose the ability to certify this formula shape;
/// it refuses the shape only where the shape means nothing about the program.
///
/// Without this assertion, deleting the whole body of `certify_vc` and returning
/// `None` would pass the primary lock. That would be a test that cannot fail
/// usefully.
#[test]
fn the_same_formula_still_certifies_under_a_program_point_bearing_kind() {
    let faithful = vc(
        VcKind::LoopInvariantInitiation { invariant: "1 == 1".to_string(), header_block: 0 },
        tautology_violation(),
    );
    assert!(
        trust_certify::certify_vc(&faithful).is_some(),
        "the kind gate must not disturb a loop-clause obligation: it carries a header_block \
         program point and conjoins the loop state, so a kernel-checked UNSAT of it IS a fact \
         about the program"
    );
}

/// The REAL loop-invariant initiation shape — state binding conjoined with the
/// negated invariant — is untouched.
///
/// `Eq(sum, 0) ∧ ¬(sum >= 0)`: the pre-state binding AND the negated predicate.
/// This is what a faithful contract obligation looks like, and the contrast with
/// the bare `Not(P)` above is the entire content of the gate. It is also the
/// obligation class `certify_vc`'s own unit suite calls "the first REAL provable
/// obligation class (loop invariants) certified end-to-end", so a regression
/// here would be a genuine loss of proof strength.
#[test]
fn faithful_loop_initiation_shape_is_unaffected() {
    let sum = || Formula::Var("sum".to_string(), Sort::Int);
    let faithful = vc(
        VcKind::LoopInvariantInitiation { invariant: "sum >= 0".to_string(), header_block: 0 },
        Formula::And(vec![
            Formula::Eq(Box::new(sum()), Box::new(Formula::Int(0))),
            Formula::Not(Box::new(Formula::Ge(Box::new(sum()), Box::new(Formula::Int(0))))),
        ]),
    );
    assert!(
        trust_certify::certify_vc(&faithful).is_some(),
        "the faithful loop-initiation obligation must still kernel-certify"
    );
}

/// The postcondition lane — the one door that IS open and IS faithful — keeps
/// its authority.
///
/// MEASURED on `trust-e26541e3`, same body, same surface: `ensures` proves
/// `result <= x` on `{ x / 2 }` and `result == 7` on `{ 7 }`, while REFUSING
/// `result > x` and `result == 7` on `{ x / 2 }`. That is a body-aware lane, so
/// the gate must not touch it — refusing it would delete real proofs.
#[test]
fn postcondition_authority_is_not_withdrawn() {
    assert!(
        vc(VcKind::Postcondition, tautology_violation()).kernel_authority_refusal().is_none(),
        "the ensures lane is body-aware and measured faithful; refusing it would delete real \
         proofs rather than fake ones"
    );
}

/// Safety kinds are untouched. These are every obligation ay actually proves
/// today, so a gate that caught any of them would be a regression, not a fix.
#[test]
fn safety_kinds_keep_kernel_authority() {
    for kind in [
        VcKind::DivisionByZero,
        VcKind::RemainderByZero,
        VcKind::IndexOutOfBounds,
        VcKind::SliceBoundsCheck,
        VcKind::Unreachable,
        VcKind::Assertion { message: "assert".to_string() },
        VcKind::Precondition { callee: "callee".to_string() },
    ] {
        assert!(
            vc(kind.clone(), tautology_violation()).kernel_authority_refusal().is_none(),
            "{kind:?} is minted from MIR with its reaching path condition; it must keep kernel \
             authority"
        );
    }
}

/// The refusal must NAME THE CONSTRUCT, per the standing directive that an
/// honest refusal is a correct outcome but a silent one is not.
#[test]
fn the_refusal_explains_itself() {
    let reason =
        vc(VcKind::ContractInvariant { expression: "1 == 1".to_string() }, tautology_violation())
            .kernel_authority_refusal()
            .expect("item-position invariant must be refused");
    assert!(
        reason.contains("no program point"),
        "the refusal must say WHY, naming the missing program point: {reason}"
    );
    assert!(
        reason.contains("tautology"),
        "the refusal must name the failure mode it prevents: {reason}"
    );
}

/// v6/D2: concurrency obligations carry no concurrency model yet, so the
/// kernel lane must not certify them around the router's refusal.
///
/// MUTATION PROOF: move `DataRace`/`InsufficientOrdering` back to the ADMITTED
/// arm of `kernel_authority_refusal` and this test fails — the same UNSAT
/// formulas certify, exactly as `contract_invariant_never_mints_kernel_authority`
/// shows for its kind.
#[test]
fn concurrency_kinds_never_mint_kernel_authority() {
    for kind in [
        VcKind::DataRace {
            variable: "x".to_string(),
            thread_a: "t0".to_string(),
            thread_b: "t1".to_string(),
        },
        VcKind::InsufficientOrdering {
            variable: "x".to_string(),
            actual: "Relaxed".to_string(),
            required: "Acquire".to_string(),
        },
    ] {
        let reason = vc(kind.clone(), tautology_violation())
            .kernel_authority_refusal()
            .unwrap_or_else(|| panic!("{kind:?} must be refused kernel authority (v6/D2)"));
        assert!(reason.contains("v6/D2"), "the refusal must cite its ruling: {reason}");
        for violation in [tautology_violation(), free_var_tautology_violation()] {
            let vc = vc(kind.clone(), violation);
            assert!(
                trust_certify::certify_vc(&vc).is_none(),
                "{kind:?} minted a kernel certificate without a concurrency model"
            );
        }
    }
}

/// TINV-8 (2026-10-05): `VcKind::TypeInvariant` was refused by kind from step 2 until the
/// step-7 producer landed; since step 7.7 the kind is ADMITTED and every row goes through the
/// VC-level situatedness gate (`type_invariant_situatedness_refusal`, TINV-9(j)).
fn tinv_kind() -> VcKind {
    tinv_kind_edge(None)
}

fn tinv_kind_edge(edge: Option<usize>) -> VcKind {
    VcKind::TypeInvariant {
        ty: "mycrate::Screen".to_string(),
        point: trust_types::TypeInvariantPoint::Call,
        site: trust_types::TypeInvariantSite { block: 1, statement_index: 0 },
        conjunct: 0,
        ordinal: 0,
        edge,
    }
}

fn int(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

/// `¬(i1 <= n)`: the negated core of json-`Parser`'s `i <= len(b)` after the write.
fn tinv_neg_core() -> Formula {
    Formula::Not(Box::new(Formula::Le(Box::new(int("i1")), Box::new(int("n")))))
}

/// The design §9 0(b)(c) linear preservation row `i1 = i0 + 1 ∧ i0 < n ∧ ¬(i1 <= n)`:
/// the hypotheses bind both core names, and it is UNSAT over ℤ.
fn tinv_linear_row() -> Formula {
    Formula::And(vec![
        Formula::Eq(
            Box::new(int("i1")),
            Box::new(Formula::Add(Box::new(int("i0")), Box::new(Formula::Int(1)))),
        ),
        Formula::Lt(Box::new(int("i0")), Box::new(int("n"))),
        tinv_neg_core(),
    ])
}

fn exact_record(body: Formula) -> trust_types::ObligationRecord {
    trust_types::ObligationRecord { body, wrappers: Vec::new(), subject: None, width: None }
}

fn recorded(kind: VcKind, formula: Formula, body: Formula) -> VerificationCondition {
    VerificationCondition { obligation: Some(exact_record(body)), ..vc(kind, formula) }
}

/// TINV step 7.7, THE POSITIVE PIN. A recorded, situated TINV row mints `CleanCic`
/// evidence through `certify_vc`, and the evidence replays through `recheck_vc_cleancic`
/// against the same row and no other.
///
/// MUTATION PROOF: move `VcKind::TypeInvariant` back to the REFUSED arm of
/// `VcKind::kind_authority_refusal` (trust-types `vc_kind.rs`) and this test fails at the
/// first `expect`: the same row then mints nothing.
#[test]
fn a_recorded_situated_type_invariant_row_mints_and_replays() {
    let row = recorded(tinv_kind(), tinv_linear_row(), tinv_linear_row());
    assert_eq!(row.kernel_authority_refusal(), None);
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } =
        trust_certify::certify_vc(&row).expect("the recorded linear TINV row must mint")
    else {
        panic!("expected CleanCic evidence");
    };
    assert!(trust_certify::recheck_vc_cleancic(&term, &context, &lineage, &row));
    // The evidence is bound to the row's identity: another conjunct's row does not replay it.
    let mut other = row.clone();
    other.kind = VcKind::TypeInvariant {
        ty: "mycrate::Screen".to_string(),
        point: trust_types::TypeInvariantPoint::Call,
        site: trust_types::TypeInvariantSite { block: 1, statement_index: 0 },
        conjunct: 1,
        ordinal: 0,
        edge: None,
    };
    assert!(!trust_certify::recheck_vc_cleancic(&term, &context, &lineage, &other));
    // The replay obeys the row gate: the same evidence against the record-less row fails.
    let mut stripped = row.clone();
    stripped.obligation = None;
    assert!(!trust_certify::recheck_vc_cleancic(&term, &context, &lineage, &stripped));
    // The same certificate under an admitted kind with the same formula is not a TINV
    // identity either (the identity binds the kind).
    let postcondition = vc(VcKind::Postcondition, tinv_linear_row());
    assert!(!trust_certify::recheck_vc_cleancic(&term, &context, &lineage, &postcondition));
}

/// The rows the situatedness gate exists for mint nothing, although every formula below
/// is UNSAT (each certifies under an admitted kind, asserted first, so the refusal is the
/// row gate and not the formula).
#[test]
fn unsituated_type_invariant_rows_never_mint() {
    let loop_kind = || VcKind::LoopInvariantInitiation { invariant: "p".into(), header_block: 0 };
    // The record-less tautology and free-variable rows of TINV step 2.
    for formula in [tautology_violation(), free_var_tautology_violation(), tinv_linear_row()] {
        assert!(trust_certify::certify_vc(&vc(loop_kind(), formula.clone())).is_some());
        assert!(
            trust_certify::certify_vc(&vc(tinv_kind(), formula)).is_none(),
            "a record-less TINV row minted kernel evidence"
        );
    }
    // A forged record: it does not replay to the formula it claims to account for.
    let forged = recorded(tinv_kind(), tinv_linear_row(), tinv_neg_core());
    assert!(trust_certify::certify_vc(&forged).is_none(), "a forged record minted");
    let forged_ground = recorded(tinv_kind(), tautology_violation(), tinv_linear_row());
    assert!(trust_certify::certify_vc(&forged_ground).is_none(), "a forged record minted");
    // Bare: the core with no hypothesis (`¬(x == x)` is UNSAT, recorded exactly).
    let bare =
        recorded(tinv_kind(), free_var_tautology_violation(), free_var_tautology_violation());
    assert!(trust_certify::certify_vc(&bare).is_none(), "a bare core minted");
    // Unbound core: the hypothesis names `a`; the core's `x` is bound by nothing.
    let x = || Box::new(int("x"));
    let unbound = Formula::And(vec![
        Formula::Eq(Box::new(int("a")), Box::new(Formula::Int(1))),
        Formula::Not(Box::new(Formula::Eq(x(), x()))),
    ]);
    assert!(trust_certify::certify_vc(&vc(loop_kind(), unbound.clone())).is_some());
    let unbound_row = recorded(tinv_kind(), unbound.clone(), unbound);
    assert!(trust_certify::certify_vc(&unbound_row).is_none(), "an unbound core minted");
    // An edge part (TINV-9(a)) whose core names only its edge guard binds: the guard is a
    // routing condition, never a binding of program state.
    let guard_only =
        Formula::And(vec![Formula::Le(Box::new(int("i1")), Box::new(int("n"))), tinv_neg_core()]);
    assert!(trust_certify::certify_vc(&vc(loop_kind(), guard_only.clone())).is_some());
    let part = recorded(tinv_kind_edge(Some(0)), guard_only.clone(), guard_only.clone());
    assert!(trust_certify::certify_vc(&part).is_none(), "a guard-only edge part minted");
    // Control: the SAME body on a whole row counts its first conjunct as a hypothesis.
    let whole = recorded(tinv_kind(), guard_only.clone(), guard_only);
    assert!(trust_certify::certify_vc(&whole).is_some(), "the whole-row control must mint");
}

/// Native planning stays closed to TINV after the flip: its resource preflight admits only
/// `IndexOutOfBounds`, so even the recorded, situated row mints nothing on that route.
#[test]
fn native_planning_still_refuses_a_situated_type_invariant_row() {
    let row = recorded(tinv_kind(), tinv_linear_row(), tinv_linear_row());
    assert_eq!(row.kernel_authority_refusal(), None);
    assert!(!trust_certify::vc_fits_native_planning_certification_budget(&row));
    assert!(trust_certify::certify_vc_for_native_planning(&row).is_none());
}

/// Certificate identity is bincode of the whole VC, which encodes the variant's
/// DECLARATION INDEX. `TypeInvariant` is appended last: every earlier variant keeps
/// its index (so its identity bytes), and the new one sits right after
/// `FrameConditionViolation`. A mid-enum insert fails this test.
#[test]
fn type_invariant_is_appended_after_every_existing_vc_kind() {
    fn index(kind: &VcKind) -> u32 {
        let bytes = bincode::serialize(kind).expect("serialize");
        u32::from_le_bytes(bytes[..4].try_into().expect("variant index"))
    }
    let frame =
        VcKind::FrameConditionViolation { variable: String::new(), function: String::new() };
    // The declaration indices at `efa8829d7c` (2026-10-05), before TINV existed.
    assert_eq!(index(&VcKind::DivisionByZero), 3);
    assert_eq!(index(&frame), 55);
    assert_eq!(index(&tinv_kind()), 56);
}
