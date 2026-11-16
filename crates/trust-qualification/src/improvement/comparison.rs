// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Comparison of independently selected, parent-observed action intervals.
//!
//! Every public value here is observation DATA. Neither an assessment nor an
//! identity string constructs execution, proof, SDK or publication authority.
//! The native caller retains its original source/program/output/admission
//! owners, checks them at both boundaries, and independently validates required
//! behavior and proof grades before recording a successful action. In
//! particular, candidate stdout and JSON cannot establish that success.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::{Result, canonical_hex, refusal};

const MAX_ACTIONS: usize = 64;
const MAX_REPETITIONS: u32 = 31;
const MAX_NAME: usize = 256;

/// Logical workload inputs selected independently of the two output programs.
/// Configuration includes logical argv/environment and cold/warm/cache policy;
/// coverage includes the complete required behavior and grade population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct WorkloadIdentity {
    pub source_sha256: String,
    pub configuration_sha256: String,
    pub coverage_sha256: String,
}

/// Expected produced program and the source from which it was actually built.
/// This is not a functional SDK identity or a produced-program owner.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProgramIdentity {
    pub build_source_sha256: String,
    pub program_sha256: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Side {
    Baseline,
    Candidate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum IntervalScope {
    /// The original parent times this action through its actual owning wait.
    /// Includes delivery/capture overhead; not a claim about CPU cause or quiet.
    ParentActionIntervalV1,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Outcome {
    /// Parent-confirmed success: retirement, physical capture completion,
    /// original inputs and independently required behavior/grades all passed.
    /// A successful exit alone is insufficient. This enum remains DATA.
    Succeeded,
    Failed,
    TimedOut,
    Cancelled,
    CouldNotRun,
    Unknown,
}

#[derive(Clone, Debug, Serialize)]
pub struct ActionObservation {
    pub action: String,
    pub repetition: u32,
    pub outcome: Outcome,
    pub elapsed_ns: Option<u64>,
    pub scope: IntervalScope,
}

/// Observations from one original run, not a deserialized running graph.
#[derive(Clone, Debug, Serialize)]
pub struct RunObservations {
    /// Parent-derived original run identity, including original process birth.
    pub run_sha256: String,
    pub program: ProgramIdentity,
    pub workload: WorkloadIdentity,
    pub sdk_sha256: String,
    pub actions: Vec<ActionObservation>,
}

/// Select BEFORE delivery. Source changes belong to the program identities;
/// the workload, SDK, configuration, coverage and population stay identical.
pub struct ComparisonSpec {
    baseline: ProgramIdentity,
    candidate: ProgramIdentity,
    workload: WorkloadIdentity,
    sdk_sha256: String,
    actions: BTreeSet<String>,
    repetitions: u32,
    focus: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum Problem {
    InvalidRunIdentity,
    SameRun,
    ProgramIdentity,
    WorkloadIdentity,
    SdkIdentity,
    PopulationTooLarge,
    UnselectedAction,
    Repetition,
    DuplicateAction,
    MissingAction,
    Outcome(Outcome),
    MissingInterval,
    IntervalScope,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Issue {
    pub side: Side,
    pub action: Option<String>,
    pub repetition: Option<u32>,
    pub problem: Problem,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Direction {
    Lower,
    Equal,
    Higher,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ActionComparison {
    pub action: String,
    pub baseline_upper_median_ns: u64,
    pub candidate_upper_median_ns: u64,
    pub direction: Direction,
    pub absolute_delta_ns: u64,
}

/// Observed intervals only: no qualified/Ready/ships/landing flag. Even lower
/// intervals do not establish statistical significance or causation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum Assessment {
    Incomplete { issues: Vec<Issue> },
    Regressed { focus: String, actions: Vec<ActionComparison> },
    Comparable { focus: String, actions: Vec<ActionComparison> },
}

impl ComparisonSpec {
    pub fn new(
        baseline: ProgramIdentity,
        candidate: ProgramIdentity,
        workload: WorkloadIdentity,
        sdk_sha256: String,
        actions: Vec<String>,
        repetitions: u32,
        focus: String,
    ) -> Result<Self> {
        for value in [
            &baseline.build_source_sha256,
            &baseline.program_sha256,
            &candidate.build_source_sha256,
            &candidate.program_sha256,
            &workload.source_sha256,
            &workload.configuration_sha256,
            &workload.coverage_sha256,
            &sdk_sha256,
        ] {
            if !canonical_hex(value, 64) {
                return Err(refusal("comparison identities must be canonical SHA-256 data"));
            }
        }
        if baseline.build_source_sha256 == candidate.build_source_sha256 {
            return Err(refusal("repair comparison requires distinct actual program sources"));
        }
        if actions.is_empty()
            || actions.len() > MAX_ACTIONS
            || actions.iter().any(|name| name.is_empty() || name.len() > MAX_NAME)
            || !(1..=MAX_REPETITIONS).contains(&repetitions)
        {
            return Err(refusal(
                "comparison requires an exact bounded action population and focus",
            ));
        }
        let selected = actions.iter().cloned().collect::<BTreeSet<_>>();
        if selected.len() != actions.len() || !selected.contains(&focus) {
            return Err(refusal(
                "comparison action population must be unique and include its focus",
            ));
        }
        Ok(Self {
            baseline,
            candidate,
            workload,
            sdk_sha256,
            actions: selected,
            repetitions,
            focus,
        })
    }

    pub fn assess(&self, baseline: &RunObservations, candidate: &RunObservations) -> Assessment {
        let mut issues = Vec::new();
        let before = self.collect(Side::Baseline, &self.baseline, baseline, &mut issues);
        let after = self.collect(Side::Candidate, &self.candidate, candidate, &mut issues);
        if baseline.run_sha256 == candidate.run_sha256 {
            issues.push(Issue {
                side: Side::Candidate,
                action: None,
                repetition: None,
                problem: Problem::SameRun,
            });
        }
        if !issues.is_empty() {
            return Assessment::Incomplete { issues };
        }
        let actions = self
            .actions
            .iter()
            .map(|action| {
                let mut before = before[action.as_str()].clone();
                let mut after = after[action.as_str()].clone();
                before.sort_unstable();
                after.sort_unstable();
                let baseline = before[before.len() / 2];
                let candidate = after[after.len() / 2];
                ActionComparison {
                    action: action.clone(),
                    baseline_upper_median_ns: baseline,
                    candidate_upper_median_ns: candidate,
                    direction: if candidate < baseline {
                        Direction::Lower
                    } else if candidate == baseline {
                        Direction::Equal
                    } else {
                        Direction::Higher
                    },
                    absolute_delta_ns: baseline.abs_diff(candidate),
                }
            })
            .collect::<Vec<_>>();
        if actions.iter().any(|action| action.direction == Direction::Higher) {
            Assessment::Regressed { focus: self.focus.clone(), actions }
        } else {
            Assessment::Comparable { focus: self.focus.clone(), actions }
        }
    }

    fn collect<'a>(
        &self,
        side: Side,
        expected: &ProgramIdentity,
        run: &'a RunObservations,
        issues: &mut Vec<Issue>,
    ) -> BTreeMap<&'a str, Vec<u64>> {
        let mut issue =
            |problem| issues.push(Issue { side, action: None, repetition: None, problem });
        if !canonical_hex(&run.run_sha256, 64) {
            issue(Problem::InvalidRunIdentity);
        }
        if &run.program != expected {
            issue(Problem::ProgramIdentity);
        }
        if run.workload != self.workload {
            issue(Problem::WorkloadIdentity);
        }
        if run.sdk_sha256 != self.sdk_sha256 {
            issue(Problem::SdkIdentity);
        }
        let count = self.actions.len() * self.repetitions as usize;
        if run.actions.len() > count {
            issue(Problem::PopulationTooLarge);
        }
        let mut seen = BTreeSet::new();
        let mut values = BTreeMap::<&str, Vec<u64>>::new();
        // Raw observations remain with the caller. Bound inspection/diagnostic
        // allocation while keeping every required missing slot explicit.
        for row in run.actions.iter().take(count + 1) {
            let mut issue = |problem| {
                issues.push(Issue {
                    side,
                    action: (row.action.len() <= MAX_NAME).then(|| row.action.clone()),
                    repetition: Some(row.repetition),
                    problem,
                })
            };
            if !self.actions.contains(&row.action) {
                issue(Problem::UnselectedAction);
                continue;
            }
            if !(1..=self.repetitions).contains(&row.repetition) {
                issue(Problem::Repetition);
                continue;
            }
            if !seen.insert((row.action.as_str(), row.repetition)) {
                issue(Problem::DuplicateAction);
                continue;
            }
            if row.outcome != Outcome::Succeeded {
                issue(Problem::Outcome(row.outcome));
            }
            if row.scope != IntervalScope::ParentActionIntervalV1 {
                issue(Problem::IntervalScope);
            }
            match row.elapsed_ns {
                Some(ns) => values.entry(&row.action).or_default().push(ns),
                None => issue(Problem::MissingInterval),
            }
        }
        for action in &self.actions {
            for repetition in 1..=self.repetitions {
                if !seen.contains(&(action.as_str(), repetition)) {
                    issues.push(Issue {
                        side,
                        action: Some(action.clone()),
                        repetition: Some(repetition),
                        problem: Problem::MissingAction,
                    });
                }
            }
        }
        values
    }
}

#[cfg(test)]
mod tests;
