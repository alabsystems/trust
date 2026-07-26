//! Exact source-produced E4 shapes needed by the proof-gated E4 -> E5 lane.
//!
//! The compiler admits an invariant as an E5 assumption only when both rows
//! carry Clean-kernel authority, so this test pins the certificate frontier to
//! the byte-semantic formulas emitted by the native UI fixture rather than a
//! hand-simplified approximation.

use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

fn int_var(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn e4_vc(kind: VcKind, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: "feedback_closes".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
    }
}

#[test]
fn exact_native_e4_pair_is_clean_kernel_certifiable() {
    let phase = || int_var("phase");
    let remaining = || int_var("remaining");
    let machine_range = || {
        Formula::And(vec![
            Formula::Ge(Box::new(phase()), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(phase()), Box::new(Formula::Int(u32::MAX.into()))),
        ])
    };
    let initiation = e4_vc(
        VcKind::LoopInvariantInitiation {
            invariant: "remaining >= phase".to_string(),
            header_block: 1,
        },
        Formula::And(vec![
            Formula::Le(Box::new(phase()), Box::new(Formula::Int(1))),
            machine_range(),
            Formula::Not(Box::new(Formula::Ge(Box::new(Formula::Int(1)), Box::new(phase())))),
        ]),
    );
    let consecution = e4_vc(
        VcKind::LoopInvariantConsecution {
            invariant: "remaining >= phase".to_string(),
            header_block: 1,
        },
        Formula::And(vec![
            Formula::Ge(Box::new(remaining()), Box::new(phase())),
            Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Gt(Box::new(phase()), Box::new(Formula::Int(0)))),
                Box::new(Formula::Bool(false)),
            ))),
            Formula::Not(Box::new(Formula::Ge(
                Box::new(Formula::Int(0)),
                Box::new(Formula::Int(0)),
            ))),
        ]),
    );

    let initiation_certifies = trust_certify::certify_vc(&initiation).is_some();
    let consecution_certifies = trust_certify::certify_vc(&consecution).is_some();
    assert!(
        initiation_certifies,
        "the exact native E4 initiation row must carry Clean-kernel authority; \
         consecution_certifies={consecution_certifies}"
    );
    assert!(
        consecution_certifies,
        "the exact native E4 consecution row must carry Clean-kernel authority"
    );
}
