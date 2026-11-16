//! Execute newly emitted modules, not handwritten substitutes for producer output.
//! The outer compiler harness must bind these inputs to its actual compile receipt.
//! These tests check concrete semantics; they do not grant refinement authority.

mod array_support;
#[allow(dead_code)]
mod support;
mod unit_support;

fn module(variable: &str) -> trust_ir::Module {
    let path = std::env::var_os(variable)
        .unwrap_or_else(|| panic!("{variable} must name a freshly emitted, compiler-bound module"));
    support::read_module(std::path::Path::new(&path))
}

#[test]
#[ignore = "requires freshly emitted slice and place-order modules from the subject compiler"]
fn actual_slice_bounds_and_place_order() {
    let observations = support::observe_original_cases(
        &module("TRUST_SLICE_BOUNDS_IR"),
        &module("TRUST_SLICE_PLACE_IR"),
    );
    assert_eq!(observations.len(), 15);
    for observation in observations {
        assert!(observation.agrees(), "slice disagrees with Rust: {observation:?}");
    }
}

#[test]
#[ignore = "requires the freshly emitted effect-order module from the subject compiler"]
fn actual_effectful_bases_evaluate_once_in_order() {
    let effects = module("TRUST_SLICE_EFFECT_IR");
    let observations = support::observe_effect_cases(&effects);
    assert_eq!(observations.len(), 2);
    for observation in observations {
        assert!(observation.agrees(), "effectful base disagrees with Rust: {observation:?}");
    }
    // Other computational rows remain in the producer census. Absence here is
    // a disclosed lowering gap, not evidence of execution or product totality.
    eprintln!("unexecuted effect siblings: {:?}", support::missing_effect_functions(&effects));
}

#[test]
#[ignore = "requires freshly emitted, fixed subject modules; never runs on stale baseline IR"]
fn actual_slice_regression_controls_detect_changed_ir() {
    let observations = support::observe_subject_mutants(
        &module("TRUST_SLICE_BOUNDS_IR"),
        &module("TRUST_SLICE_PLACE_IR"),
    );
    assert_eq!(observations.len(), 4);
    for observation in observations {
        assert!(!observation.agrees(), "changed implementation escaped control: {observation:?}");
        assert!(
            !matches!(observation.actual, support::Outcome::Other(_)),
            "a type/IR/interpreter error is not the required differing runtime result: {observation:?}",
        );
    }
}
