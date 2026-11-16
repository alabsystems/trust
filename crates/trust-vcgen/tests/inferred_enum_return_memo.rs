// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.
//! Same-state continuations must not repeat candidate evaluation. The adjacent
//! fixture is the complete three-function mir-only inventory from diagnostic
//! compiler 8f2a1a676886, with its source retained byte-for-byte. The decision
//! method is 29 blocks, but visiting every switch edge without reuse takes 68
//! evaluations. The existing 64-work and 256-expression limits remain intact.

use trust_types::{Formula, Sort, VerifiableFunction};

#[path = "fixtures/d5b_enum_decision_table.rs"]
mod table;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Scalar {
    Bool(bool),
    Int(i128),
}

// An ordinary finite test oracle over the actual compiled Rust fixture. This
// checks the proposed expression; it does not replace any kernel admission.
fn value(formula: &Formula, bindings: &[(String, Scalar)]) -> Scalar {
    let boolean = |formula| match value(formula, bindings) {
        Scalar::Bool(value) => value,
        other => panic!("expected Bool, got {other:?}"),
    };
    match formula {
        Formula::Bool(value) => Scalar::Bool(*value),
        Formula::Int(value) => Scalar::Int(*value),
        Formula::Var(name, _) => bindings.iter().find(|(key, _)| key == name).unwrap().1,
        Formula::Eq(lhs, rhs) => Scalar::Bool(value(lhs, bindings) == value(rhs, bindings)),
        Formula::Not(inner) => Scalar::Bool(!boolean(inner)),
        Formula::And(terms) => Scalar::Bool(terms.iter().all(boolean)),
        Formula::Or(terms) => Scalar::Bool(terms.iter().any(boolean)),
        Formula::Ite(condition, yes, no) => {
            value(if boolean(condition) { yes } else { no }, bindings)
        }
        other => panic!("unexpected decision-table expression: {other:?}"),
    }
}

#[test]
fn repeated_enum_continuations_still_require_every_original_kernel_check() {
    let functions: Vec<VerifiableFunction> =
        serde_json::from_str(include_str!("fixtures/d5b_enum_decision_table.json")).unwrap();
    assert_eq!(functions.len(), 3, "retain the complete original source inventory");
    let source = functions
        .into_iter()
        .find(|function| function.def_path == "call_vc_tables::Site::admits")
        .unwrap();
    assert_eq!(source.body.blocks.len(), 29);
    assert_eq!(source.body.arg_count, 2);
    let inferred = trust_vcgen::infer_return_candidate(&source)
        .expect("identical continuation states should reuse their candidate result");
    assert!(!inferred.check_vcs().is_empty());
    use table::Kind::*;
    let kinds = [
        Precondition,
        Postcondition,
        LoopInvariant,
        TypeInvariant,
        RefinementType,
        TranslationValidation,
        MemorySafety,
        PanicFreedom,
        TemporalSafety,
        Liveness,
        Arithmetic,
        BoundsCheck,
        GiveBackRefinement,
        Termination,
        Ownership,
        Custom,
    ];
    let sites =
        [table::Site::Summary, table::Site::Inherited, table::Site::Call, table::Site::Handle];
    for site in sites {
        for kind in kinds {
            let bindings = [
                (inferred.param_names()[0].clone(), Scalar::Int(site as i128)),
                (inferred.param_names()[1].clone(), Scalar::Int(kind as i128)),
                ("_0".into(), Scalar::Bool(site.admits(kind))),
            ];
            assert_eq!(value(inferred.postcondition(), &bindings), Scalar::Bool(true));
        }
    }
    let wrong = Formula::Eq(
        Box::new(Formula::Var("_0".into(), Sort::Bool)),
        Box::new(Formula::Bool(false)),
    );
    let wrong_rows = trust_vcgen::inferred_enum_return_check_vcs(&source, &wrong).unwrap();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let good: Vec<_> = inferred
                .check_vcs()
                .iter()
                .enumerate()
                .map(|(index, row)| {
                    eprintln!(
                        "ORIGINAL_CHECK_ROW {index} bytes={}",
                        serde_json::to_vec(row).unwrap().len()
                    );
                    let (evidence, stop) = trust_certify::certify_vc_reporting_stop(row);
                    if let Some(evidence) = &evidence {
                        assert!(trust_certify::reference_certificate_for(evidence).is_some());
                        // Exercise the serialized consumer boundary without
                        // adding an IR dependency to this generator crate.
                        let encoded = serde_json::to_value(evidence).unwrap();
                        let parts = encoded.get("CleanCic").expect("real kernel certificate");
                        let term: Vec<u8> = serde_json::from_value(parts["term"].clone()).unwrap();
                        let context: Vec<u8> =
                            serde_json::from_value(parts["context"].clone()).unwrap();
                        let lineage = serde_json::from_value(parts["lineage"].clone()).unwrap();
                        assert!(
                            trust_certify::recheck_vc_cleancic(&term, &context, &lineage, row),
                            "consumer must replay the unchanged original row {index}"
                        );
                    }
                    if evidence.is_none() {
                        eprintln!(
                            "UNCERTIFIED_ORIGINAL_ROW {index} stop={stop:?} {}",
                            serde_json::to_string(row).unwrap()
                        );
                    }
                    evidence.is_some()
                })
                .collect();
            let bad: Vec<_> =
                wrong_rows.iter().map(|row| trust_certify::certify_vc(row).is_some()).collect();
            eprintln!("reused enum continuations: original={good:?}, wrong={bad:?}");
            // The true and false arms join the SAME blocks. A cache keyed by
            // block alone proposes the wrong function and fails these checks.
            assert!(good.iter().all(|checked| *checked), "every original row must certify");
            assert!(bad.iter().any(|checked| !checked), "a wrong relation must still refuse");
        })
        .unwrap()
        .join()
        .unwrap();
}
