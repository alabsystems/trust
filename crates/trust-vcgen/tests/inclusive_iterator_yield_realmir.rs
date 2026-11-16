//! Inclusive endpoints must remain modeled, including the panicking endpoint.
//! The fixture is the actual Clean canary body, captured by the D9 compiler;
//! see its README for the source, command, hashes, and span-only normalization.

use trust_types::{Formula, VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

#[path = "fixtures/inclusive_iterator_yield/programs.rs"]
// Returning on the first yield is the control-flow case under test.
#[allow(clippy::never_loop)]
mod programs;

fn load_control(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/inclusive_iterator_yield/{name}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    serde_json::from_str(&std::fs::read_to_string(path).expect("control fixture"))
        .expect("real control MIR")
}

#[test]
fn inclusive_interval_facts_do_not_authorize_unreachable_counterexamples() {
    // These are the exact Rust bodies captured in the fixtures. Exhaust every
    // possible byte input: both functions read only index0 of the one-byte array.
    for value in 0..=u8::MAX {
        assert_eq!(programs::inclusive_first_yield_returns(&[value]), value);
        assert_eq!(programs::inclusive_step_skips_past_end(&[value]), value);
        assert_eq!(programs::exclusive_first_yield_returns(&[value]), value);
    }
    for name in ["inclusive_first_yield_returns", "inclusive_step_skips_past_end"] {
        let func = load_control(name);
        let vcs = trust_vcgen::generate_vcs(&func);
        let scope = trust_vcgen::GenericRefutationScope::for_function(&func, &vcs, &[]);
        let router = test_router::deterministic_test_router();
        let rows: Vec<_> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).collect();
        assert!(!rows.is_empty(), "{name}: retain the actual bounds obligation");
        for row in rows {
            let result = router.verify_all(std::slice::from_ref(row))[0].1.clone();
            if matches!(result, VerificationResult::Failed { .. }) {
                assert!(
                    scope.rejection_reason(row).is_some(),
                    "{name}: a yield-set interval is not an execution: {result:?}\n{row:#?}"
                );
            }
        }
    }
}

#[test]
fn an_inclusive_interval_can_still_prove_a_safe_bound() {
    let func = load_control("inclusive_safe_bound");
    let router = test_router::deterministic_test_router();
    let vcs = trust_vcgen::generate_vcs(&func);
    let rows: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).collect();
    assert!(!rows.is_empty(), "keep the positive control's real bounds row");
    for row in rows {
        let result = router.verify_all(std::slice::from_ref(row))[0].1.clone();
        assert!(matches!(result, VerificationResult::Proved { .. }), "{result:?}");
    }
}

#[test]
fn the_original_inclusive_canary_keeps_its_recorded_bounds_check() {
    let func: VerifiableFunction = serde_json::from_str(include_str!(
        "fixtures/inclusive_iterator_yield/loop_off_by_one.json"
    ))
    .expect("real MIR fixture");
    let vcs = trust_vcgen::generate_vcs(&func);
    let rows: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(vc.kind, VcKind::SliceBoundsCheck)
                && vc.location.line_start == 135
                && vc.location.col_start == 31
        })
        .collect();
    assert_eq!(rows.len(), 1, "the original typed obligation must survive: {vcs:#?}");
    let row = rows[0];
    assert!(row.obligation.is_some(), "a synthetic alarm is not the bounds VC");
    assert_ne!(row.formula, Formula::Bool(true), "the actual violation must remain");
    let router = test_router::deterministic_test_router();
    let result = router.verify_all(std::slice::from_ref(row))[0].1.clone();
    assert!(
        !matches!(result, VerificationResult::Proved { .. }),
        "the inclusive endpoint indexes past the slice: {result:?}"
    );
}
