// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;

fn hash(byte: char) -> String {
    byte.to_string().repeat(64)
}

fn fixture(repetitions: u32) -> (ComparisonSpec, RunObservations, RunObservations) {
    let baseline = ProgramIdentity { build_source_sha256: hash('a'), program_sha256: hash('b') };
    let candidate = ProgramIdentity { build_source_sha256: hash('c'), program_sha256: hash('d') };
    let workload = WorkloadIdentity {
        source_sha256: hash('e'),
        configuration_sha256: hash('f'),
        coverage_sha256: hash('0'),
    };
    let sdk = hash('1');
    let names = ["build", "verify", "test"];
    let observations = |program, id, elapsed| RunObservations {
        run_sha256: hash(id),
        program,
        workload: workload.clone(),
        sdk_sha256: sdk.clone(),
        actions: names
            .iter()
            .flat_map(|name| {
                (1..=repetitions).map(move |repetition| ActionObservation {
                    action: (*name).into(),
                    repetition,
                    outcome: Outcome::Succeeded,
                    elapsed_ns: Some(elapsed),
                    scope: IntervalScope::ParentActionIntervalV1,
                })
            })
            .collect(),
    };
    let before = observations(baseline.clone(), '2', 100);
    let after = observations(candidate.clone(), '3', 90);
    let spec = ComparisonSpec::new(
        baseline,
        candidate,
        workload,
        sdk,
        names.into_iter().map(str::to_owned).collect(),
        repetitions,
        "build".into(),
    )
    .unwrap();
    (spec, before, after)
}

fn problems(assessment: Assessment) -> Vec<Problem> {
    match assessment {
        Assessment::Incomplete { issues } => {
            issues.into_iter().map(|issue| issue.problem).collect()
        }
        other => panic!("must not compare incomplete observations: {other:?}"),
    }
}

#[test]
fn full_upper_medians_are_integer_exact_without_adding_overlapping_stages() {
    let (spec, mut before, mut after) = fixture(2);
    for row in &mut before.actions {
        row.elapsed_ns = Some(if row.repetition == 1 { u64::MAX - 2 } else { u64::MAX });
    }
    for row in &mut after.actions {
        row.elapsed_ns = Some(if row.repetition == 1 { 1 } else { 2 });
    }
    after.actions.reverse();
    let Assessment::Comparable { focus, actions } = spec.assess(&before, &after) else { panic!() };
    assert_eq!(focus, "build");
    assert_eq!(actions.len(), 3);
    for action in actions {
        assert_eq!(action.baseline_upper_median_ns, u64::MAX);
        assert_eq!(action.candidate_upper_median_ns, 2);
        assert_eq!(action.direction, Direction::Lower);
        assert_eq!(action.absolute_delta_ns, u64::MAX - 2);
    }
    let (spec, mut before, mut after) = fixture(3);
    for row in &mut before.actions {
        row.elapsed_ns = Some([50, 100, 200][row.repetition as usize - 1]);
    }
    for row in &mut after.actions {
        row.elapsed_ns = Some([90, 1, u64::MAX][row.repetition as usize - 1]);
    }
    let Assessment::Comparable { actions, .. } = spec.assess(&before, &after) else { panic!() };
    assert!(
        actions
            .iter()
            .all(|a| a.baseline_upper_median_ns == 100 && a.candidate_upper_median_ns == 90)
    );
}

#[test]
fn every_failure_and_unknown_stays_in_the_required_population() {
    for outcome in [
        Outcome::Failed,
        Outcome::TimedOut,
        Outcome::Cancelled,
        Outcome::CouldNotRun,
        Outcome::Unknown,
    ] {
        let (spec, before, mut after) = fixture(3);
        after.actions[0].outcome = outcome;
        after.actions[1].elapsed_ns = None;
        after.actions[2].scope = IntervalScope::Unknown;
        let issues = problems(spec.assess(&before, &after));
        assert!(issues.contains(&Problem::Outcome(outcome)));
        assert!(issues.contains(&Problem::MissingInterval));
        assert!(issues.contains(&Problem::IntervalScope));
        assert_eq!(after.actions.len(), 9, "failed observations remain with their live caller");
    }
}

#[test]
fn duplicate_extra_skipped_or_unselected_actions_never_shrink_the_denominator() {
    for case in 0..5 {
        let (spec, before, mut after) = fixture(2);
        match case {
            0 => {
                after.actions.remove(0);
            }
            1 => {
                after.actions[0] = after.actions[1].clone();
            }
            2 => {
                after.actions[0].action = "unselected".into();
            }
            3 => {
                after.actions[0].repetition = 0;
            }
            _ => {
                after.actions.push(after.actions[0].clone());
            }
        }
        let issues = problems(spec.assess(&before, &after));
        if case != 4 {
            assert!(issues.contains(&Problem::MissingAction));
        }
        match case {
            1 | 4 => assert!(issues.contains(&Problem::DuplicateAction)),
            2 => assert!(issues.contains(&Problem::UnselectedAction)),
            3 => assert!(issues.contains(&Problem::Repetition)),
            _ => {}
        }
        if case == 4 {
            assert!(issues.contains(&Problem::PopulationTooLarge));
        }
    }
}

#[test]
fn source_program_configuration_coverage_sdk_and_original_run_must_match_selection() {
    for case in 0..8 {
        let (spec, before, mut after) = fixture(1);
        let expected = match case {
            0 => {
                after.program.build_source_sha256 = hash('9');
                Problem::ProgramIdentity
            }
            1 => {
                after.program.program_sha256 = hash('9');
                Problem::ProgramIdentity
            }
            2 => {
                after.workload.source_sha256 = hash('9');
                Problem::WorkloadIdentity
            }
            3 => {
                after.workload.configuration_sha256 = hash('9');
                Problem::WorkloadIdentity
            }
            4 => {
                after.workload.coverage_sha256 = hash('9');
                Problem::WorkloadIdentity
            }
            5 => {
                after.sdk_sha256 = hash('9');
                Problem::SdkIdentity
            }
            6 => {
                after.run_sha256 = before.run_sha256.clone();
                Problem::SameRun
            }
            _ => {
                after.run_sha256.clear();
                Problem::InvalidRunIdentity
            }
        };
        assert!(problems(spec.assess(&before, &after)).contains(&expected));
    }
}

#[test]
fn faster_focus_cannot_hide_another_required_action_regression() {
    let (spec, before, mut after) = fixture(3);
    for row in after.actions.iter_mut().filter(|row| row.action == "verify") {
        row.elapsed_ns = Some(101);
    }
    let Assessment::Regressed { actions, .. } = spec.assess(&before, &after) else { panic!() };
    assert!(actions.iter().any(|a| a.action == "build" && a.direction == Direction::Lower));
    let slower = actions.iter().find(|a| a.action == "verify").unwrap();
    assert_eq!(slower.direction, Direction::Higher);
    assert_eq!(slower.absolute_delta_ns, 1);
}

#[test]
fn malformed_preselection_cannot_authorize_a_different_or_empty_comparison() {
    let (spec, before, after) = fixture(1);
    for (actions, repetitions, focus) in [
        (vec![], 1, "build"),
        (vec!["build".into(), "build".into()], 1, "build"),
        (vec!["build".into()], 0, "build"),
        (vec!["build".into()], 32, "build"),
        (vec!["build".into()], 1, "unknown"),
        ((0..65).map(|n| format!("action-{n}")).collect(), 1, "action-0"),
        (vec!["x".repeat(257)], 1, "build"),
    ] {
        assert!(
            ComparisonSpec::new(
                before.program.clone(),
                after.program.clone(),
                spec.workload.clone(),
                spec.sdk_sha256.clone(),
                actions,
                repetitions,
                focus.into()
            )
            .is_err()
        );
    }
    assert!(
        ComparisonSpec::new(
            before.program.clone(),
            before.program.clone(),
            spec.workload.clone(),
            spec.sdk_sha256.clone(),
            vec!["build".into()],
            1,
            "build".into()
        )
        .is_err()
    );
}
