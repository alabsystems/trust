// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use clean_kernel::Name;

use super::*;
use crate::clean_island::CleanIslandModelVerdict;

const LOCKSTEP: &str =
    include_str!("../../../../trust-spec-temporal/examples/clean_scalar_lockstep.lean");
const HARNESS: &str =
    include_str!("../../../../trust-spec-temporal/examples/harness_policy_one_writer.lean");

fn assert_same_batch(actual: &CleanIslandBatch, expected: &CleanIslandBatch) {
    // Compare observable diagnostics, authored order, spans, disclosures, data
    // and model results, including their real kernel-derived verdicts.
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
}

fn checking_session() -> CleanIslandSession {
    let mut session = CleanIslandSession::new();
    session.enable_model_checks();
    session
}

#[test]
fn late_reporting_keeps_safe_unsafe_and_undecided_models_in_the_original_delta() {
    for (source, budget, verdict) in [
        (format!("import Trust.FiniteModel\n{LOCKSTEP}"), 256, "safe"),
        (
            format!("import Trust.FiniteModel\n{}", LOCKSTEP.replace("\"Buggy\" 0", "\"Buggy\" 1")),
            256,
            "unsafe",
        ),
        (format!("import Trust.FiniteModel\n{LOCKSTEP}"), 1, "undecided"),
    ] {
        let mut fresh = checking_session();
        fresh.set_model_state_budget(budget);
        let expected = fresh.check_all(&[&source]);

        let mut prepared = CleanIslandSession::new().prepare_all(&[&source]);
        assert!(!prepared.declarations().is_rejected(), "{verdict}");
        assert!(prepared.declarations().outcomes[0].model_checks.is_empty());
        let theorem = Name::from_string("trust_checked_safe.Example.Lockstep");
        assert!(prepared.session.env().get_const(&theorem).is_none());
        prepared.enable_model_checks();
        prepared.set_model_state_budget(budget);
        let (continued, actual) = prepared.finish();
        assert_same_batch(&actual, &expected);
        assert_eq!(continued.is_tainted(), fresh.is_tainted());
        let [check] = actual.outcomes[0].model_checks.as_slice() else {
            panic!("{verdict}: {:?}", actual.outcomes);
        };
        match (&check.verdict, verdict) {
            (CleanIslandModelVerdict::Safe { .. }, "safe") => {
                assert_eq!(
                    continued.env().get_const(&theorem).unwrap().type_,
                    fresh.env().get_const(&theorem).unwrap().type_,
                );
            }
            (CleanIslandModelVerdict::Unsafe { run, .. }, "unsafe") => {
                assert!(!run.is_empty());
                assert!(actual.is_rejected());
                assert!(continued.environment().is_none());
            }
            (CleanIslandModelVerdict::Undecided { .. }, "undecided") => {
                assert!(continued.env().get_const(&theorem).is_none());
            }
            other => panic!("unexpected {other:?}"),
        }
    }
}

#[test]
fn a_retained_baseline_does_not_enable_models_or_binding_reads() {
    for source in [
        format!("import Trust.FiniteModel\n{LOCKSTEP}"),
        "import Trust.Binding\nopen Trust.Protocol\n\
         def policy : Trust.Protocol.Binding := binds \"n\" [\"Tick\"] []\n"
            .into(),
    ] {
        let expected = CleanIslandSession::new().check_all(&[&source]);
        let (session, actual) = CleanIslandSession::new().prepare_all(&[&source]).finish();
        assert_same_batch(&actual, &expected);
        assert!(!session.is_tainted());
        for outcome in actual.outcomes {
            assert!(outcome.model_checks.is_empty());
            assert!(outcome.bindings.is_empty());
            assert!(outcome.seals.is_empty());
        }
    }
}

#[test]
fn late_binding_reads_preserve_seals_spans_and_unreadable_data_refusal() {
    for source in [
        "import Trust.Binding\nnamespace Policy\nopen Trust.Protocol\n\
         def cell : Trust.Protocol.Seal := seals \"Cell\" [\"put\"] [\"new\"] [] []\n\
         def binding : Trust.Protocol.Binding := binds \"n\" [\"Tick\"] []\nend Policy\n",
        "import Trust.Binding\nopen Trust.Protocol\n\
         def cell : Trust.Protocol.Seal := seals \"\" [] [] [] []\n",
    ] {
        let mut fresh = CleanIslandSession::new();
        fresh.enable_binding_reads();
        let expected = fresh.check_all(&[source]);
        let mut prepared = CleanIslandSession::new().prepare_all(&[source]);
        prepared.enable_binding_reads();
        let (session, actual) = prepared.finish();
        assert_same_batch(&actual, &expected);
        assert_eq!(session.is_tainted(), fresh.is_tainted());
        if source.contains("namespace Policy") {
            assert_eq!(actual.outcomes[0].bindings.len(), 1);
            assert_eq!(actual.outcomes[0].seals.len(), 1);
            assert!(actual.outcomes[0].model_checks.is_empty());
        } else {
            assert!(actual.is_rejected());
            assert!(session.environment().is_none());
        }
    }
}

#[test]
fn finishing_continues_the_original_file_context_and_excludes_older_models() {
    let original = format!("import Trust.FiniteModel\n{LOCKSTEP}");
    let mut session = CleanIslandSession::new();
    assert!(!session.check(&original).is_rejected());
    let mut prepared = session.prepare_all(&[
        "namespace Shared\ndef value : Bool := true\nend Shared\nopen Shared\n",
        "theorem exact : value = true := rfl\n",
    ]);
    prepared.enable_model_checks();
    let (mut continued, batch) = prepared.finish();
    assert!(!batch.is_rejected(), "{batch:?}");
    assert!(batch.outcomes.iter().all(|outcome| outcome.model_checks.is_empty()));
    assert!(
        continued
            .env()
            .get_const(&Name::from_string("trust_checked_safe.Example.Lockstep"))
            .is_none()
    );
    let later = continued.check("theorem still_open : value = true := rfl");
    assert!(!later.is_rejected(), "{later:?}");
}

#[test]
fn late_progress_reporting_preserves_live_and_livelock_kernel_results() {
    let claim = |name: &str, model: &str| {
        format!(
            "def HarnessPolicy.{name} : Trust.Temporal.FiniteModel.ScalarProgress :=\n  \
             progress ({model})\n    \
             (v \"committed\" ≐ n 0 ⋎ v \"in_force\" ≐ v \"disk\")\n    \
             [\"Poll\", \"Deliver\", \"Forget\"] []\n"
        )
    };
    let source = format!(
        "import Trust.Protocol\n{HARNESS}\nopen Trust.Protocol\n{}{}",
        claim("CatchesUp", "HarnessPolicy.OneWriter"),
        claim("MutantCatchesUp", "HarnessPolicy.Protocol 1"),
    );
    let expected = checking_session().check_all(&[&source]);
    let mut prepared = CleanIslandSession::new().prepare_all(&[&source]);
    prepared.enable_model_checks();
    let (session, actual) = prepared.finish();
    assert_same_batch(&actual, &expected);
    assert!(actual.is_rejected());
    assert!(session.is_tainted());
    assert!(
        actual.outcomes[0]
            .model_checks
            .iter()
            .any(|check| matches!(check.verdict, CleanIslandModelVerdict::Live { .. }))
    );
    assert!(
        actual.outcomes[0]
            .model_checks
            .iter()
            .any(|check| matches!(check.verdict, CleanIslandModelVerdict::Livelock { .. }))
    );
}

#[test]
fn rejected_declarations_never_finish_with_a_positive_environment() {
    for sources in [
        vec!["def good : Bool := true", "theorem bad : true = false := rfl"],
        vec!["def first : Bool := second", "def second : Bool := first"],
        vec!["import Not.A.Real.Module\ndef value : Bool := true"],
    ] {
        let expected = checking_session().check_all(&sources);
        let mut prepared = CleanIslandSession::new().prepare_all(&sources);
        assert!(prepared.declarations().is_rejected());
        prepared.enable_model_checks();
        let (session, actual) = prepared.finish();
        assert_same_batch(&actual, &expected);
        assert!(actual.is_rejected());
        assert!(session.is_tainted());
        assert!(session.environment().is_none());
    }
}

#[test]
fn reporting_boundary_model_policy_keeps_binding_only_imports_unreported() {
    let source = "import Trust.Binding\nopen Trust.Protocol\n\
                  def policy : Trust.Protocol.Binding := binds \"n\" [\"Tick\"] []\n";
    let expected = checking_session().check_all(&[source]);
    let mut prepared = CleanIslandSession::new().prepare_all(&[source]);
    prepared.enable_model_checks();
    let (session, actual) = prepared.finish();
    assert_same_batch(&actual, &expected);
    assert!(!actual.is_rejected());
    assert!(!session.is_tainted());
    assert_eq!(session.served_trust_modules(), ["Trust.Binding"]);
    assert!(actual.outcomes[0].model_checks.is_empty());
    assert!(actual.outcomes[0].bindings.is_empty());
    assert!(actual.outcomes[0].seals.is_empty());
}

#[test]
fn reporting_boundary_preserves_session_standin_disclosures_after_model_rejection() {
    // Two reachable states suffice for this disclosure boundary: the existing
    // larger models above already qualify the model/progress result paths.
    let two_states = LOCKSTEP.replace("\"Limit\" 2", "\"Limit\" 1");
    assert_ne!(two_states, LOCKSTEP);
    for model in [two_states.clone(), two_states.replace("\"Buggy\" 0", "\"Buggy\" 1")] {
        let source = format!("import Lean\nimport Trust.FiniteModel\n{model}");
        let sources = ["import Lean\ndef sibling : Bool := true", source.as_str()];
        let mut fresh = checking_session();
        let expected = fresh.check_all(&sources);
        let mut prepared = CleanIslandSession::new().prepare_all(&sources);
        prepared.enable_model_checks();
        let (session, actual) = prepared.finish();
        assert_same_batch(&actual, &expected);
        assert_eq!(
            format!("{:?}", session.standin_imports()),
            format!("{:?}", fresh.standin_imports())
        );
        assert_eq!(session.standin_imports().len(), 1);
        assert_eq!(session.standin_imports()[0].module, "Lean");
        assert!(!actual.outcomes[0].standin_imports.is_empty());
        if actual.is_rejected() {
            assert!(actual.outcomes[1].standin_imports.is_empty());
            assert!(session.is_tainted());
        } else {
            assert!(!actual.outcomes[1].standin_imports.is_empty());
            assert!(!session.is_tainted());
        }
    }
}

#[test]
fn declaration_preview_keeps_original_context_policy_and_report_rows_unmodified() {
    let source = "import Trust.Binding\nnamespace Policy\nopen Trust.Protocol\n\
                  def cell : Trust.Protocol.Seal := seals \"Cell\" [\"put\"] [\"new\"] [] []\n\
                  def binding : Trust.Protocol.Binding := binds \"n\" [\"Tick\"] []\nend Policy\n";
    let mut prepared = CleanIslandSession::new().prepare_all(&[source]);
    let (mut preview, batch) = prepared.declaration_preview(true);
    assert!(!batch.is_rejected());
    assert_eq!(batch.outcomes[0].bindings.len(), 1);
    assert_eq!(batch.outcomes[0].seals.len(), 1);
    assert!(prepared.declarations().outcomes[0].bindings.is_empty());
    assert!(!prepared.session.binding_reads);
    assert!(!prepared.session.model_checks);
    assert!(!preview.check("def preview_only : Bool := true").is_rejected());
    prepared.enable_model_checks();
    prepared.enable_binding_reads();
    let (session, actual) = prepared.finish();
    let mut fresh = checking_session();
    fresh.enable_binding_reads();
    let expected = fresh.check_all(&[source]);
    assert_same_batch(&actual, &expected);
    assert_eq!(actual.outcomes[0].bindings.len(), 1);
    assert_eq!(actual.outcomes[0].seals.len(), 1);
    assert!(session.environment().unwrap().get_const(&Name::from_string("preview_only")).is_none());
}
