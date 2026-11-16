//! Trust: compilation queue outcomes observed by the native scheduler.
//! Dispatch is separate from primary-process observations. Owning-wait CPU/RSS
//! plus a successful full unit terminal establish a measured unit process;
//! queries, wrapper subprocesses, tests, proof and resource release are separate.

use std::collections::BTreeMap;
use std::io::BufRead;
use std::path::{Path, PathBuf};

use anyhow::{Context as _, bail};
use serde::Serialize;

use super::log_reader::{MAX_UNITS, read_checked, read_records, require_workspace};
use super::util::find_log_file;
use crate::compiler::{CompileMode, UnitIndex};
use crate::util::log_message::{
    COMPILER_OBSERVATION_VERSION, EXECUTION_VERSION, ExecutionGraphOutcome, ExecutionUnitOutcome,
    INPUT_WORK_VERSION, LogMessage, SHARED_DEPENDENCY_POLICY_VERSION, SharedDependencyDecision,
    Target,
};
use crate::util::logger::RunId;
use crate::workspace::Workspace;
use crate::{CargoResult, GlobalContext};

mod shared;

pub struct ReportExecutionOptions {
    pub id: Option<RunId>,
    pub json: bool,
}

pub fn report_execution(
    gctx: &GlobalContext,
    ws: Option<&Workspace<'_>>,
    opts: ReportExecutionOptions,
) -> CargoResult<()> {
    let selection_ws = if opts.id.is_some() { None } else { ws };
    let (path, run) = find_log_file(gctx, selection_ws, opts.id.as_ref())?.context(
        "no matching build-analysis session; enable -Zbuild-analysis and build.analysis.enabled",
    )?;
    let report = read_report(&path, &run.to_string())
        .with_context(|| format!("failed to analyze execution at `{}`", path.display()))?;
    if let Some(ws) = ws {
        require_workspace(report.workspace_root.as_deref(), ws.root())?;
    }
    let bytes = if opts.json {
        let mut bytes = serde_json::to_vec(&report)?;
        bytes.push(b'\n');
        bytes
    } else {
        let mut text = if let Some(counts) = &report.execution {
            format!(
                "Session: {}\nCompilation execution: {} ({:?})\nRegistered: {}; scheduled: {} ({} fresh, {} dirty); completed: {}; not executed: {}; unresolved: {}\nSucceeded: {}; failed: {}; tolerated failures: {}; cancelled: {}\n",
                report.run_id,
                report.availability,
                report.graph_outcome.unwrap(),
                report.registered_units,
                counts.scheduled,
                counts.scheduled_fresh,
                counts.scheduled_dirty,
                counts.completed,
                counts.not_executed,
                counts.unresolved,
                counts.succeeded,
                counts.failed,
                counts.tolerated_failure,
                counts.cancelled,
            )
        } else {
            format!(
                "Session: {}\nCompilation execution: unavailable\n",
                report.run_id
            )
        };
        match report.compiler_activity.successful_primary_processes {
            Some(count) => text.push_str(&format!(
                "Compiler-unit primary processes: {count} (complete owning-wait evidence)\n"
            )),
            None => text.push_str(&format!(
                "Compiler-unit primary processes: {}; measured successful units: {}; unmeasured starts: {}\n",
                report.compiler_activity.availability,
                report.compiler_activity.observed_successful_units,
                report.compiler_activity.unmeasured_starts,
            )),
        }
        if let Some(eligible) = report.shared_dependency_frontier.eligible_units {
            text.push_str(&format!(
                "Shared dependency frontier: {eligible} eligible; {} dependency-blocked; {} excluded\n",
                report.shared_dependency_frontier.dependency_blocked_units.unwrap(),
                report.shared_dependency_frontier.excluded_units.unwrap(),
            ));
        } else {
            text.push_str(&format!(
                "Shared dependency frontier: {}\n",
                report.shared_dependency_frontier.availability
            ));
        }
        text.into_bytes()
    };
    gctx.shell().print_ansi_stdout(&bytes)?;
    Ok(())
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    run_id: String,
    scope: &'static str,
    availability: &'static str,
    graph_outcome: Option<ExecutionGraphOutcome>,
    elapsed_seconds: Option<f64>,
    registered_units: u64,
    execution: Option<Counts>,
    compiler_activity: CompilerActivity,
    shared_dependency_frontier: shared::Frontier,
    units: Vec<UnitRow>,
    #[serde(skip)]
    workspace_root: Option<PathBuf>,
}

#[derive(Default, Serialize)]
struct Counts {
    scheduled: u64,
    scheduled_fresh: u64,
    scheduled_dirty: u64,
    completed: u64,
    succeeded: u64,
    failed: u64,
    tolerated_failure: u64,
    cancelled: u64,
    not_executed: u64,
    unresolved: u64,
}

#[derive(Serialize)]
struct UnitRow {
    index: UnitIndex,
    package_id: String,
    target: Target,
    mode: CompileMode,
    platform: String,
    features: Vec<String>,
    requested: bool,
    dependencies: Vec<UnitIndex>,
    // Trust: this is the queue's initial classification. A dirty job can reuse
    // another process's result after acquiring its lock; no process count is
    // inferred from this field.
    scheduled_fresh: Option<bool>,
    scheduled_elapsed_seconds: Option<f64>,
    outcome: Option<ExecutionUnitOutcome>,
    outcome_elapsed_seconds: Option<f64>,
    duration_seconds: Option<f64>,
    process: ProcessObservation,
    shared_dependency: Option<SharedDependencyDecision>,
}

#[derive(Default, Serialize)]
struct ProcessObservation {
    command_started_seconds: Option<f64>,
    finished_seconds: Option<f64>,
    peak_rss_bytes: Option<u64>,
    owning_wait_cpu: Option<OwningCpu>,
}

#[derive(Serialize)]
struct OwningCpu {
    user_ns: u64,
    system_ns: u64,
    scope: &'static str,
}

#[derive(Serialize)]
struct CompilerActivity {
    scope: &'static str,
    availability: &'static str,
    rusage_requested: Option<bool>,
    // A complete total exists only for the declared producer contract and a
    // successful closed graph. Observed partial evidence is retained below.
    successful_primary_processes: Option<u64>,
    observed_successful_units: u64,
    unmeasured_starts: u64,
    completed_without_start: u64,
}

fn compiler_unit(mode: CompileMode) -> bool {
    matches!(
        mode,
        CompileMode::Build | CompileMode::Check { .. } | CompileMode::Test
    )
}

fn compiler_activity(
    units: &BTreeMap<UnitIndex, UnitRow>,
    declared: Option<bool>,
    graph: Option<ExecutionGraphOutcome>,
) -> CompilerActivity {
    let mut observed = 0;
    let mut unmeasured = 0;
    let mut without_start = 0;
    for unit in units.values().filter(|unit| compiler_unit(unit.mode)) {
        let process = &unit.process;
        if process.command_started_seconds.is_none() {
            without_start += u64::from(unit.outcome == Some(ExecutionUnitOutcome::Succeeded));
        } else if process.finished_seconds.is_some()
            && process.owning_wait_cpu.is_some()
            && process.peak_rss_bytes.is_some()
            && unit.outcome == Some(ExecutionUnitOutcome::Succeeded)
        {
            observed += 1;
        } else {
            unmeasured += 1;
        }
    }
    let availability = if declared.is_none() {
        "unavailable"
    } else if graph != Some(ExecutionGraphOutcome::Succeeded) {
        "incomplete"
    } else if unmeasured != 0 {
        "unavailable"
    } else {
        "complete"
    };
    CompilerActivity {
        scope: "compiler-unit-primary-processes-v1",
        availability,
        rusage_requested: declared,
        successful_primary_processes: (availability == "complete").then_some(observed),
        observed_successful_units: observed,
        unmeasured_starts: unmeasured,
        completed_without_start: without_start,
    }
}

fn read_report(path: &Path, run: &str) -> CargoResult<Report> {
    read_checked(path, |reader| analyze(reader, run))
}

/// Project the SAME strict reducer used by `report execution`. The caller
/// supplies its original closed native writer's bytes/run, never a freshness
/// boolean or a saved cache record. These counts remain diagnostic data.
pub(crate) fn native_compiler_counts(
    reader: impl BufRead,
    run: &str,
) -> CargoResult<
    trust_resource_controller::paired_qualification::service::compiler_observation::Counts,
> {
    use trust_resource_controller::paired_qualification::service::compiler_observation::{
        Counts, GraphOutcome,
    };
    let report = analyze(reader, run)?;
    let graph_outcome = match report
        .graph_outcome
        .context("original compiler graph contract unavailable")?
    {
        ExecutionGraphOutcome::Succeeded => GraphOutcome::Succeeded,
        ExecutionGraphOutcome::Failed => GraphOutcome::Failed,
        ExecutionGraphOutcome::Cancelled => GraphOutcome::Cancelled,
    };
    let execution = report
        .execution
        .context("original execution denominator unavailable")?;
    let activity = report.compiler_activity;
    let counts = Counts {
        graph_outcome,
        registered: report.registered_units,
        scheduled: execution.scheduled,
        scheduled_fresh: execution.scheduled_fresh,
        completed: execution.completed,
        succeeded: execution.succeeded,
        failed: execution.failed,
        tolerated_failure: execution.tolerated_failure,
        cancelled: execution.cancelled,
        not_executed: execution.not_executed,
        rusage_requested: activity.rusage_requested,
        successful_primary_processes: activity.successful_primary_processes,
        observed_successful_units: activity.observed_successful_units,
        unmeasured_starts: activity.unmeasured_starts,
        completed_without_start: activity.completed_without_start,
    };
    counts.validate()?;
    Ok(counts)
}

fn elapsed(value: f64) -> CargoResult<()> {
    if !value.is_finite() || value < 0.0 {
        bail!("invalid execution elapsed time");
    }
    Ok(())
}

fn analyze(reader: impl BufRead, run: &str) -> CargoResult<Report> {
    let mut units = BTreeMap::<UnitIndex, UnitRow>::new();
    let mut enabled = false;
    let mut pre_execution_process_observed = false;
    let mut compiler_observations = None;
    let mut shared_policy = None;
    let mut graph_registered = false;
    let mut build_started = false;
    let mut workspace_root = None;
    let mut input_enabled = false;
    let mut closed = false;
    let mut terminal = None;
    let mut records = 0usize;
    let mut counts = Counts::default();
    read_records(reader, run, |message| {
        if closed {
            bail!("data after terminal log record");
        }
        match message {
            LogMessage::InputWorkEnabled { version } => {
                if records != 0 || input_enabled || version != INPUT_WORK_VERSION {
                    bail!("unsupported or misplaced log schema");
                }
                input_enabled = true;
            }
            LogMessage::BuildStarted {
                workspace_root: root,
                ..
            } => {
                if build_started || !units.is_empty() || enabled {
                    bail!("duplicate or late build-started record");
                }
                build_started = true;
                workspace_root = Some(root);
            }
            LogMessage::UnitRegistered {
                index,
                package_id,
                target,
                mode,
                platform,
                features,
                requested,
                dependencies,
            } => {
                if !build_started
                    || graph_registered
                    || units.len() >= MAX_UNITS
                    || units.contains_key(&index)
                {
                    bail!("duplicate, late, or excessive unit registration");
                }
                if dependencies.contains(&index) {
                    bail!("invalid unit dependency list");
                }
                units.insert(
                    index,
                    UnitRow {
                        index,
                        package_id: package_id.to_string(),
                        target,
                        mode,
                        platform,
                        features,
                        requested,
                        dependencies,
                        scheduled_fresh: None,
                        scheduled_elapsed_seconds: None,
                        outcome: None,
                        outcome_elapsed_seconds: None,
                        duration_seconds: None,
                        process: ProcessObservation::default(),
                        shared_dependency: None,
                    },
                );
            }
            LogMessage::UnitGraphFinished { elapsed: time } => {
                elapsed(time)?;
                if !build_started || graph_registered {
                    bail!("duplicate or premature unit graph completion");
                }
                for unit in units.values() {
                    if unit
                        .dependencies
                        .iter()
                        .any(|index| !units.contains_key(index))
                    {
                        bail!("unit graph references an unregistered dependency");
                    }
                }
                graph_registered = true;
            }
            LogMessage::ExecutionEnabled { version } => {
                if !input_enabled
                    || !graph_registered
                    || enabled
                    || pre_execution_process_observed
                    || version != EXECUTION_VERSION
                {
                    bail!("unsupported or misplaced execution schema");
                }
                enabled = true;
            }
            LogMessage::UnitStarted { .. }
            | LogMessage::UnitFinished { .. }
            | LogMessage::UnitCpuTimes { .. }
            | LogMessage::UnitPeakMemory { .. }
                if !enabled =>
            {
                // Legacy logs may contain these events without an execution
                // protocol, but a later declaration cannot erase an already
                // observed process and manufacture complete coverage or zero.
                pre_execution_process_observed = true;
            }
            LogMessage::CompilerObservationsEnabled {
                version,
                rusage_requested,
            } => {
                if !enabled
                    || compiler_observations.is_some()
                    || counts.scheduled != 0
                    || terminal.is_some()
                    || version != COMPILER_OBSERVATION_VERSION
                {
                    bail!("unsupported, duplicate or late compiler observation contract");
                }
                compiler_observations = Some(rusage_requested);
            }
            LogMessage::SharedDependencyPolicy {
                version,
                enabled: sharing,
            } => {
                if !graph_registered
                    || shared_policy.is_some()
                    || counts.scheduled != 0
                    || terminal.is_some()
                    || version != SHARED_DEPENDENCY_POLICY_VERSION
                {
                    bail!("unsupported, duplicate or late shared dependency policy");
                }
                shared_policy = Some(sharing);
            }
            LogMessage::SharedDependencyDecision { index, decision } => {
                if shared_policy != Some(true) || counts.scheduled != 0 || terminal.is_some() {
                    bail!("shared dependency decision outside its declared planning phase");
                }
                let unit = units
                    .get_mut(&index)
                    .context("shared dependency decision is unregistered")?;
                if unit.shared_dependency.replace(decision).is_some() {
                    bail!("duplicate shared dependency decision");
                }
            }
            LogMessage::UnitStarted {
                index,
                elapsed: time,
            } if enabled => {
                elapsed(time)?;
                if terminal.is_some() {
                    bail!("process start after execution graph terminal");
                }
                let unit = units
                    .get_mut(&index)
                    .context("process start is unregistered")?;
                let scheduled = unit
                    .scheduled_elapsed_seconds
                    .context("process start lacks dispatch")?;
                if unit.process.command_started_seconds.is_some()
                    || unit.outcome.is_some()
                    || time < scheduled
                {
                    bail!("duplicate, late or invalid process start");
                }
                unit.process.command_started_seconds = Some(time);
            }
            LogMessage::UnitFinished {
                index,
                elapsed: time,
                ..
            } if enabled => {
                elapsed(time)?;
                let unit = units
                    .get_mut(&index)
                    .context("process finish is unregistered")?;
                let start = unit
                    .process
                    .command_started_seconds
                    .context("process finish lacks start")?;
                if terminal.is_some()
                    || unit.outcome.is_some()
                    || unit.process.finished_seconds.is_some()
                    || time < start
                {
                    bail!("duplicate, late or invalid process finish");
                }
                unit.process.finished_seconds = Some(time);
            }
            LogMessage::UnitCpuTimes {
                index,
                user_ns,
                system_ns,
            } if enabled => {
                let unit = units
                    .get_mut(&index)
                    .context("CPU observation is unregistered")?;
                if terminal.is_some()
                    || unit.process.command_started_seconds.is_none()
                    || unit.process.finished_seconds.is_some()
                    || unit.outcome.is_some()
                    || unit.process.owning_wait_cpu.is_some()
                {
                    bail!("CPU observation lacks a current unique process owner");
                }
                unit.process.owning_wait_cpu = Some(OwningCpu {
                    user_ns,
                    system_ns,
                    scope: "reaped-child-and-waited-descendants",
                });
            }
            LogMessage::UnitPeakMemory { index, bytes } if enabled => {
                let unit = units
                    .get_mut(&index)
                    .context("RSS observation is unregistered")?;
                if terminal.is_some()
                    || unit.process.command_started_seconds.is_none()
                    || unit.process.finished_seconds.is_some()
                    || unit.outcome.is_some()
                    || unit.process.peak_rss_bytes.is_some()
                {
                    bail!("RSS observation lacks a current unique process owner");
                }
                unit.process.peak_rss_bytes = Some(bytes);
            }
            LogMessage::UnitScheduled {
                index,
                elapsed: time,
                fresh,
            } => {
                elapsed(time)?;
                if !enabled || terminal.is_some() {
                    bail!("unit dispatch outside execution graph");
                }
                if counts.scheduled == 0 {
                    shared::validate(&units, shared_policy)?;
                }
                let unit = units
                    .get_mut(&index)
                    .context("scheduled unit is unregistered")?;
                if unit.scheduled_fresh.is_some() {
                    bail!("duplicate unit dispatch");
                }
                unit.scheduled_fresh = Some(fresh);
                unit.scheduled_elapsed_seconds = Some(time);
                counts.scheduled += 1;
                if fresh {
                    counts.scheduled_fresh += 1;
                } else {
                    counts.scheduled_dirty += 1;
                }
            }
            LogMessage::UnitOutcome {
                index,
                elapsed: time,
                outcome,
            } => {
                elapsed(time)?;
                if !enabled || terminal.is_some() {
                    bail!("unit outcome outside execution graph");
                }
                let unit = units
                    .get_mut(&index)
                    .context("unit outcome is unregistered")?;
                let start = unit
                    .scheduled_elapsed_seconds
                    .context("unit outcome lacks dispatch")?;
                if unit.outcome.is_some()
                    || time < start
                    || unit
                        .process
                        .command_started_seconds
                        .is_some_and(|started| time < started)
                    || unit
                        .process
                        .finished_seconds
                        .is_some_and(|finished| time < finished)
                {
                    bail!("duplicate or invalid unit outcome");
                }
                unit.outcome = Some(outcome);
                unit.outcome_elapsed_seconds = Some(time);
                unit.duration_seconds = Some(time - start);
                counts.completed += 1;
                match outcome {
                    ExecutionUnitOutcome::Succeeded => counts.succeeded += 1,
                    ExecutionUnitOutcome::Failed => counts.failed += 1,
                    ExecutionUnitOutcome::ToleratedFailure => counts.tolerated_failure += 1,
                    ExecutionUnitOutcome::Cancelled => counts.cancelled += 1,
                }
            }
            LogMessage::ExecutionGraphFinished {
                elapsed: time,
                outcome,
                scheduled,
                completed,
                not_executed,
            } => {
                elapsed(time)?;
                shared::validate(&units, shared_policy)?;
                if !enabled
                    || terminal.is_some()
                    || scheduled != counts.scheduled
                    || completed != counts.completed
                    || completed > scheduled
                    || not_executed.checked_add(scheduled) != Some(units.len() as u64)
                    || units.values().any(|unit| {
                        unit.scheduled_elapsed_seconds
                            .is_some_and(|start| start > time)
                            || unit
                                .outcome_elapsed_seconds
                                .is_some_and(|finish| finish > time)
                            || unit
                                .process
                                .command_started_seconds
                                .is_some_and(|start| start > time)
                            || unit
                                .process
                                .finished_seconds
                                .is_some_and(|finish| finish > time)
                    })
                {
                    bail!("invalid execution graph terminal census");
                }
                counts.not_executed = not_executed;
                counts.unresolved = scheduled - completed;
                if matches!(outcome, ExecutionGraphOutcome::Succeeded)
                    && (counts.unresolved != 0 || counts.failed != 0 || counts.cancelled != 0)
                {
                    bail!("successful execution graph contains failed or unresolved work");
                }
                terminal = Some((outcome, time));
            }
            LogMessage::InputWorkClosed { version, .. } => {
                if !input_enabled
                    || version != INPUT_WORK_VERSION
                    || (enabled && terminal.is_none())
                {
                    bail!("execution log lacks a completed supported graph");
                }
                // This marker closes the stream only. Failed input capture or
                // absent InputWorkFinalized cannot erase execution failures.
                closed = true;
            }
            _ => {}
        }
        records += 1;
        Ok(())
    })?;
    if enabled && (!closed || terminal.is_none()) {
        bail!("execution log lacks a terminal graph and stream closure");
    }
    let availability = if !enabled {
        "unavailable"
    } else if counts.unresolved == 0 {
        "complete"
    } else {
        "incomplete"
    };
    let compiler_activity = compiler_activity(
        &units,
        compiler_observations,
        terminal.map(|(outcome, _)| outcome),
    );
    let shared_dependency_frontier = shared::summarize(
        &units,
        shared_policy,
        compiler_activity.successful_primary_processes.is_some(),
    )?;
    Ok(Report {
        schema: "targo-execution-report-v1",
        run_id: run.to_owned(),
        scope: "compilation-units-v1",
        availability,
        graph_outcome: terminal.map(|(outcome, _)| outcome),
        elapsed_seconds: terminal.map(|(_, time)| time),
        registered_units: units.len() as u64,
        execution: enabled.then_some(counts),
        compiler_activity,
        shared_dependency_frontier,
        units: units.into_values().collect(),
        workspace_root,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value, json};
    use std::io::Cursor;

    const RUN: &str = "20261106T010203004Z-0123456789abcdef";

    fn frame(mut value: Value) -> String {
        value["run_id"] = json!(RUN);
        value["timestamp"] = json!("2026-11-06T01:02:03Z");
        format!("{value}\n")
    }

    fn base() -> Vec<Value> {
        vec![
            json!({"reason":"input-work-enabled","version":1}),
            json!({"reason":"build-started","command":[],"cwd":"/fixture","host":"host","jobs":1,
                "num_cpus":null,"profile":"dev","rustc_version":"test","rustc_version_verbose":"test",
                "target_dir":"/target","workspace_root":"/fixture"}),
            json!({"reason":"unit-registered","index":0,"package_id":"path+file:///fixture#sample@0.1.0",
                "target":{"name":"sample","kind":"lib"},"mode":"build","platform":"host"}),
            json!({"reason":"unit-registered","index":1,"package_id":"path+file:///fixture#sample@0.1.0",
                "target":{"name":"sample","kind":"bin"},"mode":"build","platform":"host",
                "dependencies":[0],"requested":true}),
            json!({"reason":"unit-graph-finished","elapsed":0.0}),
            json!({"reason":"execution-enabled","version":1}),
        ]
    }

    fn scheduled(index: u64, fresh: bool) -> Value {
        json!({"reason":"unit-scheduled","index":index,"elapsed":1.0,"fresh":fresh})
    }

    fn outcome(index: u64, outcome: &str) -> Value {
        json!({"reason":"unit-outcome","index":index,"elapsed":2.0,"outcome":outcome})
    }

    fn terminal(outcome: &str, scheduled: u64, completed: u64) -> Value {
        json!({"reason":"execution-graph-finished","elapsed":3.0,"outcome":outcome,
            "scheduled":scheduled,"completed":completed,"not_executed":2-scheduled})
    }

    fn close() -> Value {
        json!({"reason":"input-work-closed","version":1,"started":0,"finished":0})
    }

    fn parse(values: Vec<Value>) -> CargoResult<Report> {
        analyze(
            Cursor::new(values.into_iter().map(frame).collect::<String>()),
            RUN,
        )
    }

    #[test]
    fn pipelined_graph_keeps_dispatch_classes_and_full_outcomes() {
        let mut values = base();
        values.extend([
            scheduled(0, false),
            // A metadata edge can unblock a job before its dependency's full
            // outcome. The registered graph does not encode artifact edges.
            json!({"reason":"unit-rmeta-finished","index":0,"elapsed":1.0,"unblocked":[1]}),
            scheduled(1, true),
            outcome(1, "succeeded"),
            outcome(0, "succeeded"),
            terminal("succeeded", 2, 2),
            close(),
        ]);
        let report = parse(values).unwrap();
        assert_eq!(report.availability, "complete");
        assert_eq!(report.graph_outcome, Some(ExecutionGraphOutcome::Succeeded));
        let counts = report.execution.unwrap();
        assert_eq!((counts.scheduled_fresh, counts.scheduled_dirty), (1, 1));
        assert_eq!(counts.succeeded, 2);
        assert_eq!(report.units[0].duration_seconds, Some(1.0));
    }

    #[test]
    fn failed_graph_keeps_unscheduled_population_without_inventing_block_cause() {
        let mut values = base();
        values.extend([
            scheduled(0, false),
            outcome(0, "failed"),
            terminal("failed", 1, 1),
            close(),
        ]);
        let report = parse(values).unwrap();
        assert_eq!(report.availability, "complete");
        let counts = report.execution.unwrap();
        assert_eq!((counts.failed, counts.not_executed), (1, 1));
        assert!(report.units[1].scheduled_fresh.is_none());
        assert!(report.units[1].outcome.is_none());
    }

    #[test]
    fn tolerated_failure_and_cancellation_are_distinct() {
        for (unit_outcome, graph_outcome) in [
            ("tolerated-failure", "succeeded"),
            ("cancelled", "cancelled"),
        ] {
            let mut values = base();
            values.extend([
                scheduled(0, false),
                outcome(0, unit_outcome),
                terminal(graph_outcome, 1, 1),
                close(),
            ]);
            let counts = parse(values).unwrap().execution.unwrap();
            assert_eq!(counts.succeeded, 0);
            assert_eq!(counts.tolerated_failure + counts.cancelled, 1);
        }
    }

    #[test]
    fn joined_queue_with_unresolved_dispatch_is_explicitly_incomplete() {
        let mut values = base();
        values.extend([scheduled(0, false), terminal("failed", 1, 0), close()]);
        let report = parse(values).unwrap();
        assert_eq!(report.availability, "incomplete");
        assert_eq!(report.execution.unwrap().unresolved, 1);
        assert!(report.units[0].outcome.is_none());
    }

    #[test]
    fn legacy_log_cannot_be_mistaken_for_zero_execution() {
        let mut values = base();
        values.pop();
        let report = parse(values).unwrap();
        assert_eq!(report.availability, "unavailable");
        assert!(report.execution.is_none());
        assert!(report.graph_outcome.is_none());
        assert!(
            report
                .compiler_activity
                .successful_primary_processes
                .is_none()
        );
    }

    fn observation_contract() -> Value {
        json!({"reason":"compiler-observations-enabled","version":1,"rusage_requested":true})
    }

    fn shared_policy(enabled: bool) -> Value {
        json!({"reason":"shared-dependency-policy","version":1,"enabled":enabled})
    }

    fn shared_decision(index: u64, decision: Value) -> Value {
        json!({"reason":"shared-dependency-decision","index":index,"decision":decision})
    }

    fn shared_base() -> Vec<Value> {
        let mut values = base();
        for (row, name) in [(2, "leaf"), (3, "parent")] {
            values[row]["package_id"] = json!(format!(
                "registry+https://github.com/rust-lang/crates.io-index#{name}@1.0.0"
            ));
            values[row]["target"] = json!({"name":name,"kind":"lib"});
            values[row]["requested"] = json!(false);
        }
        values
    }

    #[test]
    fn native_shared_frontier_retains_actual_blockers_and_separate_process_costs() {
        let mut values = shared_base();
        values.extend([
            observation_contract(),
            shared_policy(true),
            shared_decision(
                0,
                json!({"status":"excluded","reason":"build-script-package"}),
            ),
            shared_decision(1, json!({"status":"dependency-blocked","dependencies":[0]})),
            scheduled(0, false),
        ]);
        values.extend(measured_process(0));
        values.extend([
            outcome(0, "succeeded"),
            scheduled(1, true),
            outcome(1, "succeeded"),
            terminal("succeeded", 2, 2),
            close(),
        ]);
        let report = serde_json::to_value(parse(values).unwrap()).unwrap();
        let frontier = &report["shared_dependency_frontier"];
        assert_eq!(frontier["availability"], "complete");
        assert_eq!(frontier["eligible_units"], 0);
        assert_eq!(frontier["dependency_blocked_units"], 1);
        assert_eq!(frontier["excluded_units"], 1);
        assert_eq!(frontier["direct_exclusions"]["build-script-package"], 1);
        assert_eq!(
            frontier["measured_compiler_commands"]["excluded"]["primary_processes"],
            1
        );
        assert_eq!(
            frontier["measured_compiler_commands"]["dependency_blocked"]["successful_units_without_start"],
            1
        );
        assert_eq!(
            report["units"][1]["shared_dependency"]["dependencies"],
            json!([0])
        );
    }

    #[test]
    fn shared_frontier_absent_disabled_and_incomplete_process_costs_are_distinct() {
        for policy in [None, Some(false), Some(true)] {
            let mut values = shared_base();
            if let Some(enabled) = policy {
                values.push(shared_policy(enabled));
            }
            if policy == Some(true) {
                values.extend([
                    shared_decision(0, json!({"status":"eligible"})),
                    shared_decision(1, json!({"status":"eligible"})),
                ]);
            }
            values.extend([
                scheduled(0, true),
                outcome(0, "succeeded"),
                terminal("succeeded", 1, 1),
                close(),
            ]);
            let report = serde_json::to_value(parse(values).unwrap()).unwrap();
            let frontier = &report["shared_dependency_frontier"];
            assert_eq!(
                frontier["availability"],
                match policy {
                    None => "unavailable",
                    Some(false) => "disabled",
                    Some(true) => "complete",
                }
            );
            assert!(frontier["measured_compiler_commands"].is_null());
            assert_eq!(
                frontier["eligible_units"],
                if policy == Some(true) {
                    json!(2)
                } else {
                    Value::Null
                }
            );
        }
    }

    #[test]
    fn planning_only_frontier_does_not_invent_an_execution_protocol_or_zero_costs() {
        let mut values = shared_base();
        values.pop(); // No execution was requested by the unit-graph planner.
        values.extend([
            shared_policy(true),
            shared_decision(0, json!({"status":"eligible"})),
            shared_decision(1, json!({"status":"eligible"})),
            close(),
        ]);
        let report = serde_json::to_value(parse(values).unwrap()).unwrap();
        assert_eq!(report["shared_dependency_frontier"]["eligible_units"], 2);
        assert_eq!(
            report["shared_dependency_frontier"]["availability"],
            "complete"
        );
        assert!(report["shared_dependency_frontier"]["measured_compiler_commands"].is_null());
        assert!(report["execution"].is_null());
        assert!(report["compiler_activity"]["successful_primary_processes"].is_null());
    }

    #[test]
    fn locally_closed_cycle_cannot_claim_the_producers_least_fixed_point() {
        for eligible in [true, false] {
            let mut values = shared_base();
            values[2]["dependencies"] = json!([1]);
            values.pop();
            values.push(shared_policy(true));
            for (index, dependency) in [(0, 1), (1, 0)] {
                values.push(shared_decision(
                    index,
                    if eligible {
                        json!({"status":"eligible"})
                    } else {
                        json!({"status":"dependency-blocked","dependencies":[dependency]})
                    },
                ));
            }
            values.push(close());
            assert!(
                parse(values).is_err(),
                "cyclic graph accepted: eligible={eligible}"
            );
        }
    }

    #[test]
    fn shared_frontier_requires_full_unique_phase_bound_dependency_closed_coverage() {
        let mut valid = shared_base();
        valid.extend([
            shared_policy(true),
            shared_decision(0, json!({"status":"eligible"})),
            shared_decision(1, json!({"status":"eligible"})),
            scheduled(0, true),
            outcome(0, "succeeded"),
            terminal("succeeded", 1, 1),
            close(),
        ]);
        assert!(parse(valid.clone()).is_ok());
        for mutation in 0..13 {
            // Every case retains the complete, otherwise valid graph/closure.
            let mut values = valid.clone();
            match mutation {
                0 => {
                    values.remove(6);
                }
                1 => values[6]["enabled"] = json!(false),
                2 => values.insert(6, shared_policy(true)),
                3 => values.insert(7, values[7].clone()),
                4 => values[7]["index"] = json!(2),
                5 => {
                    values.remove(8);
                }
                6 => {
                    values[7]["decision"] =
                        json!({"status":"excluded","reason":"build-script-package"})
                }
                7 | 8 | 9 => {
                    values[7]["decision"] =
                        json!({"status":"excluded","reason":"build-script-package"});
                    values[8]["decision"] = json!({"status":"dependency-blocked","dependencies":match mutation {7=>vec![],8=>vec![2],_=>vec![0,0]}});
                }
                10 => values.insert(10, shared_decision(0, json!({"status":"eligible"}))),
                11 => values[7]["decision"]["invented"] = json!(true),
                12 => values[2]["requested"] = json!(true),
                _ => unreachable!(),
            }
            assert!(parse(values).is_err(), "mutation {mutation} accepted");
        }
    }

    fn measured_process(index: u64) -> Vec<Value> {
        vec![
            json!({"reason":"unit-started","index":index,"elapsed":1.1}),
            // Actual zeros remain observations; missing records are different.
            json!({"reason":"unit-cpu-times","index":index,"user_ns":0,"system_ns":0}),
            json!({"reason":"unit-peak-memory","index":index,"bytes":0}),
            json!({"reason":"unit-finished","index":index,"elapsed":1.9}),
        ]
    }

    #[test]
    fn compiler_observations_distinguish_under_lock_reuse_from_dirty_dispatch() {
        let mut values = base();
        values.extend([observation_contract(), scheduled(0, false)]);
        values.extend(measured_process(0));
        values.extend([
            outcome(0, "succeeded"),
            // A dirty dispatch reuses an existing result after its lock-time
            // recheck. Dispatch classification cannot manufacture a process.
            scheduled(1, false),
            outcome(1, "succeeded"),
            terminal("succeeded", 2, 2),
            close(),
        ]);
        let report = parse(values).unwrap();
        assert_eq!(report.execution.unwrap().scheduled_dirty, 2);
        assert_eq!(
            report.compiler_activity.successful_primary_processes,
            Some(1)
        );
        assert_eq!(report.compiler_activity.completed_without_start, 1);
        assert_eq!(report.compiler_activity.unmeasured_starts, 0);
        assert_eq!(report.units[0].process.peak_rss_bytes, Some(0));
        assert_eq!(
            report.units[0]
                .process
                .owning_wait_cpu
                .as_ref()
                .unwrap()
                .user_ns,
            0
        );
    }

    #[test]
    fn complete_zero_processes_requires_the_explicit_producer_contract() {
        for declared in [false, true] {
            let mut values = base();
            if declared {
                values.push(observation_contract());
            }
            values.extend([
                scheduled(0, true),
                outcome(0, "succeeded"),
                terminal("succeeded", 1, 1),
                close(),
            ]);
            let activity = parse(values).unwrap().compiler_activity;
            assert_eq!(activity.successful_primary_processes, declared.then_some(0));
            assert_eq!(
                activity.availability,
                if declared { "complete" } else { "unavailable" }
            );
        }
    }

    #[test]
    fn native_projection_uses_the_same_checked_physical_processes_and_full_denominator() {
        for measured in [false, true] {
            let mut values = base();
            values.extend([observation_contract(), scheduled(0, false)]);
            if measured {
                values.extend(measured_process(0));
            }
            values.extend([
                outcome(0, "succeeded"),
                scheduled(1, false),
                outcome(1, "succeeded"),
                terminal("succeeded", 2, 2),
                close(),
            ]);
            let bytes = values.into_iter().map(frame).collect::<String>();
            let counts = native_compiler_counts(Cursor::new(bytes.as_bytes()), RUN).unwrap();
            assert_eq!(counts.registered, 2);
            assert_eq!(
                counts.scheduled_fresh, 0,
                "dirty→under-lock-fresh is no physical launch"
            );
            assert_eq!(
                counts.successful_primary_processes,
                Some(u64::from(measured))
            );
            assert_eq!(counts.completed_without_start, if measured { 1 } else { 2 });
            assert!(native_compiler_counts(Cursor::new(bytes.as_bytes()), "foreign-run").is_err());
            assert!(
                native_compiler_counts(Cursor::new(&bytes.as_bytes()[..bytes.len() - 1]), RUN)
                    .is_err()
            );
        }
    }

    #[test]
    fn native_projection_never_turns_missing_owning_wait_or_legacy_into_zero() {
        let mut values = base();
        values.extend([observation_contract(), scheduled(0, false)]);
        values.extend(
            measured_process(0)
                .into_iter()
                .filter(|value| value["reason"] != "unit-cpu-times"),
        );
        values.extend([
            outcome(0, "succeeded"),
            terminal("succeeded", 1, 1),
            close(),
        ]);
        let counts = native_compiler_counts(
            Cursor::new(values.into_iter().map(frame).collect::<String>()),
            RUN,
        )
        .unwrap();
        assert_eq!(counts.successful_primary_processes, None);
        assert_eq!(counts.unmeasured_starts, 1);
        let mut legacy = base();
        legacy.pop();
        legacy.push(close());
        assert!(
            native_compiler_counts(
                Cursor::new(legacy.into_iter().map(frame).collect::<String>()),
                RUN
            )
            .is_err()
        );
    }

    #[test]
    fn pre_execution_process_observations_cannot_disappear_into_a_complete_zero() {
        for event in measured_process(0) {
            let mut values = base();
            values.insert(values.len() - 1, event.clone());
            values.extend([
                observation_contract(),
                scheduled(0, true),
                outcome(0, "succeeded"),
                terminal("succeeded", 1, 1),
                close(),
            ]);
            assert!(
                parse(values).is_err(),
                "early observation was ignored: {event}"
            );
        }

        // Historical logs without the execution protocol remain readable, but
        // they never acquire a complete compiler count from these old events.
        let mut legacy = base();
        legacy.pop();
        legacy.extend(measured_process(0));
        legacy.push(close());
        let activity = parse(legacy).unwrap().compiler_activity;
        assert_eq!(activity.availability, "unavailable");
        assert!(activity.successful_primary_processes.is_none());
    }

    #[test]
    fn missing_process_facts_remain_unavailable_in_a_successful_queue() {
        for missing in 1..4 {
            let mut values = base();
            values.extend([observation_contract(), scheduled(0, false)]);
            values.extend(
                measured_process(0)
                    .into_iter()
                    .enumerate()
                    .filter_map(|(i, value)| (i != missing).then_some(value)),
            );
            values.extend([
                outcome(0, "succeeded"),
                terminal("succeeded", 1, 1),
                close(),
            ]);
            let activity = parse(values).unwrap().compiler_activity;
            assert!(activity.successful_primary_processes.is_none(), "{missing}");
            assert_eq!(activity.unmeasured_starts, 1);
        }
    }

    #[test]
    fn failed_compiler_and_foreign_script_do_not_become_successful_compiler_totals() {
        let mut values = base();
        values.extend([observation_contract(), scheduled(0, false)]);
        values.extend(measured_process(0).into_iter().take(3));
        values.extend([outcome(0, "failed"), terminal("failed", 1, 1), close()]);
        let report = parse(values).unwrap();
        assert_eq!(report.compiler_activity.availability, "incomplete");
        assert!(
            report
                .compiler_activity
                .successful_primary_processes
                .is_none()
        );
        assert!(report.units[0].process.owning_wait_cpu.is_some());

        let mut values = base();
        values[3]["mode"] = json!("run-custom-build");
        values[3]["target"]["kind"] = json!("custom-build");
        values.extend([observation_contract(), scheduled(0, false)]);
        values.extend(measured_process(0));
        values.extend([outcome(0, "succeeded"), scheduled(1, false)]);
        values.push(json!({"reason":"unit-started","index":1,"elapsed":1.1}));
        values.push(json!({"reason":"unit-finished","index":1,"elapsed":1.9}));
        values.extend([
            outcome(1, "succeeded"),
            terminal("succeeded", 2, 2),
            close(),
        ]);
        let activity = parse(values).unwrap().compiler_activity;
        assert_eq!(activity.successful_primary_processes, Some(1));
        assert_eq!(activity.unmeasured_starts, 0);
    }

    #[test]
    fn observation_contract_and_process_records_reject_duplicates_skew_and_foreign_units() {
        let start = json!({"reason":"unit-started","index":0,"elapsed":1.1});
        let cpu = json!({"reason":"unit-cpu-times","index":0,"user_ns":1,"system_ns":2});
        let rss = json!({"reason":"unit-peak-memory","index":0,"bytes":10});
        for events in [
            vec![observation_contract(), observation_contract()],
            vec![scheduled(0, false), observation_contract()],
            vec![cpu.clone()],
            vec![rss.clone()],
            vec![scheduled(0, false), start.clone(), start.clone()],
            vec![scheduled(0, false), start.clone(), cpu.clone(), cpu.clone()],
            vec![scheduled(0, false), start.clone(), rss.clone(), rss.clone()],
            vec![
                scheduled(0, false),
                json!({"reason":"unit-started","index":2,"elapsed":1.1}),
            ],
            vec![
                scheduled(0, false),
                json!({"reason":"unit-started","index":0,"elapsed":0.1}),
            ],
            vec![scheduled(0, false), start, outcome(0, "succeeded"), cpu],
        ] {
            let mut values = base();
            values.extend(events);
            assert!(parse(values).is_err());
        }
    }

    #[test]
    fn invalid_census_and_unfinished_or_duplicate_events_are_rejected() {
        for events in [
            vec![outcome(0, "succeeded")],
            vec![scheduled(0, false), scheduled(0, true)],
            vec![scheduled(2, false)],
            vec![
                scheduled(0, false),
                outcome(0, "failed"),
                terminal("succeeded", 1, 1),
                close(),
            ],
            vec![scheduled(0, false), terminal("succeeded", 1, 0), close()],
            vec![
                scheduled(0, false),
                outcome(0, "succeeded"),
                outcome(0, "succeeded"),
            ],
            vec![terminal("failed", 1, 0), close()],
            vec![terminal("failed", 0, 0)],
            vec![close()],
            vec![terminal("failed", 0, 0), close(), scheduled(0, false)],
        ] {
            let mut values = base();
            values.extend(events);
            assert!(parse(values).is_err());
        }
    }

    #[test]
    fn unknown_fields_foreign_runs_duplicate_json_and_bad_clocks_are_rejected() {
        let mut values = base();
        let mut row = scheduled(0, false);
        row["elapsed"] = json!(-1.0);
        values.push(row);
        assert!(parse(values).is_err());
        let mut values = base();
        let mut row = scheduled(0, false);
        row["invented"] = json!(0);
        values.push(row);
        assert!(parse(values).is_err());
        let mut values = base();
        values.extend([
            scheduled(0, false),
            json!({"reason":"unit-outcome","index":0,"elapsed":0.5,"outcome":"succeeded"}),
        ]);
        assert!(parse(values).is_err());
        let log = base().into_iter().map(frame).collect::<String>();
        assert!(analyze(Cursor::new(log.replace(RUN, "foreign")), RUN).is_err());
        let duplicate = log.replacen("\"version\":1", "\"version\":1,\"version\":1", 1);
        assert!(analyze(Cursor::new(duplicate), RUN).is_err());
        assert!(analyze(Cursor::new(log.trim_end()), RUN).is_err());
    }
}
