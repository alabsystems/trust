// trust-certify: TINV step 10.1 (TINV-23). A VC that carries a type-invariant
// assumption tag (`trust_types::type_invariant_assume_tag`) rests on a TINV
// certificate's whole-crate induction, which no kernel re-check of that VC covers.
// So no kernel entry may mint or replay evidence for it, whatever its kind; there is
// deliberately no entry that accepts a tagged VC.
//
// Every test pairs the tagged VC with its UNTAGGED TWIN, which mints through the same
// entry, so the refusal is the tag gate and not the formula.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    Formula, ObligationRecord, ObligationWrapper, Sort, SourceSpan, VcKind, VerificationCondition,
    type_invariant_assume_tag,
};

fn vc(kind: VcKind, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: "f".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

fn int(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn tag() -> Formula {
    Formula::Var(type_invariant_assume_tag("mycrate::Screen", 0), Sort::Bool)
}

/// The use-site fact shape `And([tag, I])`, here `tag ∧ sum <= 100`.
fn tagged_fact() -> Formula {
    Formula::And(vec![tag(), Formula::Le(Box::new(int("sum")), Box::new(Formula::Int(100)))])
}

/// `sum == 0 ∧ ¬(sum >= 0)`: the faithful loop-initiation shape, which kernel-certifies.
fn initiation() -> Formula {
    Formula::And(vec![
        Formula::Eq(Box::new(int("sum")), Box::new(Formula::Int(0))),
        Formula::Not(Box::new(Formula::Ge(Box::new(int("sum")), Box::new(Formula::Int(0))))),
    ])
}

fn with_fact(f: Formula) -> Formula {
    Formula::And(vec![tagged_fact(), f])
}

fn loop_kind() -> VcKind {
    VcKind::LoopInvariantInitiation { invariant: "sum >= 0".into(), header_block: 0 }
}

/// `certify_vc`, and the replay entries against the twin's evidence.
#[test]
fn certify_vc_and_replay_refuse_a_tagged_vc_whose_twin_certifies() {
    let twin = vc(loop_kind(), initiation());
    let evidence = trust_certify::certify_vc(&twin).expect("the untagged twin must mint");
    assert!(trust_certify::replay_vc_evidence(&twin, &evidence), "the twin replays");

    let tagged = vc(loop_kind(), with_fact(initiation()));
    assert!(tagged.kernel_authority_refusal().is_some());
    assert!(trust_certify::certify_vc(&tagged).is_none(), "a tagged VC minted CleanCic evidence");
    assert!(!trust_certify::replay_vc_evidence(&tagged, &evidence));
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = &evidence else {
        panic!("expected CleanCic evidence");
    };
    assert!(!trust_certify::recheck_vc_cleancic(term, context, lineage, &tagged));

    // The tag in the record only (a wrapper fact): refused just the same.
    let mut hidden = twin.clone();
    hidden.formula = with_fact(initiation());
    hidden.obligation = Some(ObligationRecord {
        body: initiation(),
        wrappers: vec![ObligationWrapper::ConjoinFactsLast { facts: vec![tagged_fact()] }],
        subject: None,
        width: None,
    });
    assert!(trust_certify::certify_vc(&hidden).is_none());
    assert!(!trust_certify::recheck_vc_cleancic(term, context, lineage, &hidden));
}

/// A recorded, situated `TypeInvariant` row: the untagged row mints (the step-7.7 positive
/// pin); the same row with a tagged use-site fact conjoined through a recorded wrapper is
/// still situated but mints nothing.
#[test]
fn a_tagged_type_invariant_row_never_mints() {
    let kind = VcKind::TypeInvariant {
        ty: "mycrate::Screen".to_string(),
        point: trust_types::TypeInvariantPoint::Call,
        site: trust_types::TypeInvariantSite { block: 1, statement_index: 0 },
        conjunct: 0,
        ordinal: 0,
        edge: None,
    };
    // `i1 = i0 + 1 ∧ i0 < n ∧ ¬(i1 <= n)`.
    let body = Formula::And(vec![
        Formula::Eq(
            Box::new(int("i1")),
            Box::new(Formula::Add(Box::new(int("i0")), Box::new(Formula::Int(1)))),
        ),
        Formula::Lt(Box::new(int("i0")), Box::new(int("n"))),
        Formula::Not(Box::new(Formula::Le(Box::new(int("i1")), Box::new(int("n"))))),
    ]);
    let twin = VerificationCondition {
        obligation: Some(ObligationRecord {
            body: body.clone(),
            wrappers: Vec::new(),
            subject: None,
            width: None,
        }),
        ..vc(kind.clone(), body.clone())
    };
    assert!(trust_certify::certify_vc(&twin).is_some(), "the untagged row must mint");

    let tagged = VerificationCondition {
        obligation: Some(ObligationRecord {
            body: body.clone(),
            wrappers: vec![ObligationWrapper::ConjoinFactsLast { facts: vec![tagged_fact()] }],
            subject: None,
            width: None,
        }),
        ..vc(kind, with_fact(body))
    };
    assert_eq!(tagged.type_invariant_situatedness_refusal(), None, "still situated");
    assert!(trust_certify::certify_vc(&tagged).is_none(), "a tagged TINV row minted");
    assert!(trust_certify::certify_vc_for_native_planning(&tagged).is_none());
}

/// `idx < 10 ∧ 10 ≤ idx` over a bounded u64 `idx`, the family the native-planning route
/// recognises (see `kernel_authority_kind_gate.rs`).
fn native_planning_violation() -> Formula {
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

#[test]
fn certify_vc_for_native_planning_refuses_a_tagged_vc_whose_twin_certifies() {
    let twin = vc(VcKind::IndexOutOfBounds, native_planning_violation());
    assert!(
        trust_certify::certify_vc_for_native_planning(&twin).is_some(),
        "the untagged bounds twin must mint on the planning route"
    );
    let tagged =
        vc(VcKind::IndexOutOfBounds, Formula::And(vec![tag(), native_planning_violation()]));
    assert!(tagged.kernel_authority_refusal().is_some());
    assert!(trust_certify::certify_vc_for_native_planning(&tagged).is_none());
    assert!(trust_certify::certify_vc(&tagged).is_none());
}
