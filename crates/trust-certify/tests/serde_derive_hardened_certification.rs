// Kernel-certificate regression for the real serde derive compatibility fixture.
// The captured formula and its source are recorded in the sibling fixture.
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_certify::{certify_vc, recheck_vc_cleancic};
use trust_ir::ProofEvidence;
use trust_types::{Formula, HardenedVcCategory, Sort, SourceSpan, VcKind, VerificationCondition};

#[path = "fixtures/serde_derive_hardened_add.rs"]
mod captured;

use captured::captured_violation;

fn vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: "mir_assert::Overflow(Add)".into(),
            detail: "MIR arithmetic assert can panic; hardened code needs proven arithmetic preconditions".into(),
        },
        function: "serde_derive_hardened_certification::serialize".into(),
        location: SourceSpan {
            file: "serde_derive_hardened_certification.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 1,
        },
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

#[test]
fn actual_second_checked_add_mints_an_exact_kernel_certificate() {
    let vc = vc(captured_violation());
    let ProofEvidence::CleanCic { term, context, lineage, .. } =
        certify_vc(&vc).expect("the actual safe second checked addition must kernel-certify")
    else {
        panic!("expected CleanCic evidence");
    };
    assert!(
        recheck_vc_cleancic(&term, &context, &lineage, &vc),
        "the exact captured obligation must regenerate and recheck its certificate"
    );
    let mut changed = vc.clone();
    changed.function = "serde_derive_hardened_certification::different_owner".into();
    assert!(
        !recheck_vc_cleancic(&term, &context, &lineage, &changed),
        "a certificate cannot move to another owner"
    );
}

#[test]
fn removing_the_tight_start_facts_keeps_real_overflow_uncertified() {
    // Remove only the starting-value facts, retaining the SSA definitions,
    // type ranges, first-add in-range facts, and the entire overflow goal.
    // A model now exists: _9=MAX-1, _10.0=MAX, _8=MAX, _11.1=true,
    // _10.1=false; the first addition fits and the second addition overflows.
    let mut removed = 0;
    let satisfiable = captured_violation().map(&mut |node| {
        let remove = match &node {
            Formula::Eq(a, b) => {
                matches!(a.as_ref(), Formula::Var(name, Sort::Int) if name == "_9")
                    && matches!(b.as_ref(), Formula::Int(0))
            }
            Formula::Le(a, b) => {
                matches!(a.as_ref(), Formula::Var(name, Sort::Int) if name == "_9")
                    && matches!(b.as_ref(), Formula::Int(1))
            }
            _ => false,
        };
        if remove {
            removed += 1;
            Formula::Bool(true)
        } else {
            node
        }
    });
    assert_eq!(removed, 6, "all copies of the captured start facts must be removed");
    assert!(
        certify_vc(&vc(satisfiable)).is_none(),
        "a genuinely overflowing second checked addition must stay uncertified"
    );
}

#[test]
fn two_affine_alias_steps_certify_with_small_and_usize_thresholds() {
    let var = |name: &str| Formula::Var(name.into(), Sort::Int);
    let eq = |a, b| Formula::Eq(Box::new(a), Box::new(b));
    let add = |a, b| Formula::Add(Box::new(a), Box::new(b));
    for maximum in [3, u64::MAX as i128] {
        let sum = || add(var("second"), Formula::Int(1));
        let formula = Formula::And(vec![
            eq(var("start"), Formula::Int(0)),
            eq(var("first"), add(var("start"), Formula::Int(1))),
            eq(var("second"), var("first")),
            Formula::Or(vec![
                Formula::Lt(Box::new(sum()), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(sum()), Box::new(Formula::Int(maximum))),
            ]),
        ]);
        assert!(
            certify_vc(&vc(formula)).is_some(),
            "the two-step alias chain must certify at threshold {maximum}"
        );
    }
}
