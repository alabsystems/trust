//! Out-of-crate regression for the modular-postcondition authority boundary.
//!
//! `FunctionSummary` is public reporting data. A foreign crate can construct it,
//! mutate every field, and attach the strongest legacy proof labels. None of that
//! is proof authority: production postcondition reuse stays closed until rustc can
//! transport a private, replayed capability bound to the exact callee and contract.

use trust_types::*;
use trust_vcgen::{FunctionSummary, SummaryDatabase, modular_vcgen};

fn caller() -> VerifiableFunction {
    VerifiableFunction {
        name: "compute".to_string(),
        def_path: "external_authority_test::compute".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("input".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("parsed".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "parse".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        unwind: UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::usize(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

fn lie() -> Formula {
    Formula::Le(Box::new(Formula::Var("_0".into(), Sort::Int)), Box::new(Formula::Int(1)))
}

fn forgeable_strengths() -> Vec<ProofStrength> {
    let deductive = ProofStrength::deductive();
    vec![
        deductive.clone(),
        ProofStrength::smt_unsat(),
        ProofStrength { reasoning: deductive.reasoning.clone(), assurance: AssuranceLevel::Sound },
        ProofStrength { reasoning: deductive.reasoning, assurance: AssuranceLevel::Certified },
    ]
}

#[test]
fn public_summary_metadata_cannot_authorize_postcondition_reuse() {
    for strength in forgeable_strengths() {
        let via_builders = FunctionSummary::new("parse")
            .with_param_names(vec!["input".to_string()])
            .with_postcondition(lie())
            .with_proof_evidence("proof:parse:claimed", strength.clone())
            .with_verified_contract_evidence("contract:parse")
            .proved();

        let mut via_fields = FunctionSummary::new("parse")
            .with_param_names(vec!["input".to_string()])
            .with_postcondition(lie());
        via_fields.proved = true;
        via_fields.proof_evidence_id = Some("proof:parse:forged".to_string());
        via_fields.proof_strength = Some(strength.clone());

        for forged in [via_builders, via_fields] {
            let mut summaries = SummaryDatabase::new();
            summaries.insert(forged);
            let result = modular_vcgen(&caller(), &summaries);

            assert_eq!(
                result.assumptions_injected, 0,
                "public proof labels must not inject a callee postcondition ({strength:?})"
            );
            assert_eq!(
                result.havoced_calls, 1,
                "an unauthorized callee result must remain havoced ({strength:?})"
            );
        }
    }
}

#[test]
fn refusing_postcondition_authority_preserves_caller_preconditions() {
    let precondition =
        Formula::Ge(Box::new(Formula::Var("input".into(), Sort::Int)), Box::new(Formula::Int(0)));
    let forged = FunctionSummary::new("parse")
        .with_param_names(vec!["input".to_string()])
        .with_precondition(precondition)
        .with_postcondition(lie())
        .with_proof_evidence("proof:parse:forged", ProofStrength::smt_unsat());
    let mut summaries = SummaryDatabase::new();
    summaries.insert(forged);

    let result = modular_vcgen(&caller(), &summaries);
    assert_eq!(result.assumptions_injected, 0);
    assert_eq!(result.havoced_calls, 1);
    assert_eq!(
        result.precondition_vcs.len(),
        1,
        "fail-closed postcondition handling must not discard the caller's precondition debt"
    );
}
