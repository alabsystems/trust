//! Trust: strict observational reports of build-script input capture work.
//! Complete means a healthy log covered every announced capture attempt. It
//! does not establish build success, proof, or resource-release authority.

use std::collections::BTreeMap;
use std::io::BufRead;
use std::path::{Path, PathBuf};

use anyhow::{Context as _, bail};
use serde::Serialize;

use crate::compiler::{CompileMode, UnitIndex};
use crate::ops::cargo_report::util::find_log_file;
use crate::util::log_message::{
    INPUT_WORK_VERSION, InputWork, InputWorkOutcome, InputWorkPhase, LogMessage, Target,
};
use crate::util::logger::RunId;
use crate::workspace::Workspace;
use crate::{CargoResult, GlobalContext};

use super::log_reader::MAX_UNITS;
const MAX_CAPTURES: usize = 262_144;

pub struct ReportCacheWorkOptions {
    pub id: Option<RunId>,
    pub json: bool,
}

pub fn report_cache_work(
    gctx: &GlobalContext,
    ws: Option<&Workspace<'_>>,
    opts: ReportCacheWorkOptions,
) -> CargoResult<()> {
    // Trust: a RunId hashes the original workspace spelling. An explicit ID
    // selects that exact session before checking the physical workspace below;
    // otherwise aliases such as /tmp and /private/tmp hide valid sessions.
    let selection_ws = if opts.id.is_some() { None } else { ws };
    let (path, run) = find_log_file(gctx, selection_ws, opts.id.as_ref())?.context(
        "no matching build-analysis session; enable -Zbuild-analysis and build.analysis.enabled",
    )?;
    let report = read_report(&path, &run.to_string())
        .with_context(|| format!("failed to analyze cache work at `{}`", path.display()))?;
    if let Some(ws) = ws {
        require_workspace(&report, ws.root())?;
    }
    let bytes = if opts.json {
        let mut bytes = serde_json::to_vec(&report)?;
        bytes.push(b'\n');
        bytes
    } else {
        let text = match &report.totals {
            Some(work) => format!(
                "Session: {}\nCache work: {} attempts ({} captured, {} uncacheable), {} units\nFile bytes hashed: {}; path metadata reads: {}\n",
                report.run_id,
                report.denominators.attempts_finished,
                report.denominators.captured_attempts,
                report.denominators.uncacheable_attempts,
                report.denominators.observed_units,
                work.bytes_hashed,
                work.metadata_reads,
            ),
            None => format!(
                "Session: {}\nCache work: unavailable (legacy log)\n",
                report.run_id
            ),
        };
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
    unavailable_reason: Option<&'static str>,
    build_outcome: &'static str,
    denominators: Denominators,
    units: Vec<UnitRow>,
    totals: Option<InputWork>,
    // Trust: selection evidence, not an extra machine-report field.
    #[serde(skip)]
    workspace_root: Option<PathBuf>,
}

fn require_workspace(report: &Report, requested: &Path) -> CargoResult<()> {
    super::log_reader::require_workspace(report.workspace_root.as_deref(), requested)
}

#[derive(Default, Serialize)]
struct Denominators {
    registered_units: u64,
    run_script_units: u64,
    observed_units: u64,
    units_without_attempts: u64,
    attempts_started: u64,
    attempts_finished: u64,
    captured_attempts: u64,
    uncacheable_attempts: u64,
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
    attempts: u64,
    captured_attempts: u64,
    uncacheable_attempts: u64,
    phases: Vec<PhaseRow>,
    work: Option<InputWork>,
}

#[derive(Serialize)]
struct PhaseRow {
    phase: InputWorkPhase,
    attempts: u64,
    captured_attempts: u64,
    uncacheable_attempts: u64,
    work: InputWork,
}

struct UnitState {
    row: UnitRow,
    dependencies: Vec<UnitIndex>,
    phases: BTreeMap<u8, PhaseRow>,
}

struct Attempt {
    index: UnitIndex,
    phase: u8,
    finished: bool,
}

fn zero_work() -> InputWork {
    InputWork {
        entries: 0,
        input_bytes: 0,
        bytes_hashed: 0,
        metadata_reads: 0,
        resolution_steps: 0,
        link_reads: 0,
        observations: 0,
        revalidations: 0,
    }
}

fn increment(value: &mut u64, amount: u64) -> CargoResult<()> {
    *value = value
        .checked_add(amount)
        .context("cache-work counter overflow")?;
    Ok(())
}

fn add_work(total: &mut InputWork, work: &InputWork) -> CargoResult<()> {
    increment(&mut total.entries, work.entries)?;
    increment(&mut total.input_bytes, work.input_bytes)?;
    increment(&mut total.bytes_hashed, work.bytes_hashed)?;
    increment(&mut total.metadata_reads, work.metadata_reads)?;
    increment(&mut total.resolution_steps, work.resolution_steps)?;
    increment(&mut total.link_reads, work.link_reads)?;
    increment(&mut total.observations, work.observations)?;
    increment(&mut total.revalidations, work.revalidations)?;
    Ok(())
}

fn phase_id(phase: &InputWorkPhase) -> u8 {
    match phase {
        InputWorkPhase::ExecutionWindow => 0,
        InputWorkPhase::Freshness => 1,
        InputWorkPhase::Publication => 2,
    }
}

fn read_report(path: &Path, run: &str) -> CargoResult<Report> {
    super::log_reader::read_checked(path, |reader| analyze(reader, run))
}

fn analyze(reader: impl BufRead, run: &str) -> CargoResult<Report> {
    let mut units = BTreeMap::<UnitIndex, UnitState>::new();
    let mut attempts = BTreeMap::<u64, Attempt>::new();
    let mut denominator = Denominators::default();
    let mut totals = zero_work();
    let mut enabled = false;
    let mut closed = false;
    let mut build_started = false;
    let mut workspace_root = None;
    let mut graph_finished = false;
    let mut finalized = None;
    let mut records = 0usize;
    super::log_reader::read_records(reader, run, |message| {
        if closed {
            bail!("data after terminal record");
        }
        if enabled && !build_started && !matches!(&message, LogMessage::BuildStarted { .. }) {
            bail!("input-work session has no original build-started record");
        }
        match message {
            LogMessage::InputWorkEnabled { version } => {
                if records != 0 || enabled || version != INPUT_WORK_VERSION {
                    bail!("unsupported or misplaced input-work schema");
                }
                enabled = true;
            }
            LogMessage::InputWorkClosed {
                version,
                started,
                finished,
            } => {
                if !enabled || version != INPUT_WORK_VERSION || !build_started || !graph_finished {
                    bail!("input-work terminal record lacks a complete supported session");
                }
                if finalized != Some(started)
                    || started != denominator.attempts_started
                    || finished != denominator.attempts_finished
                    || started != finished
                    || attempts.values().any(|attempt| !attempt.finished)
                    || attempts
                        .keys()
                        .enumerate()
                        .any(|(expected, observed)| expected as u64 != *observed)
                {
                    bail!("input-work attempt denominator is incomplete");
                }
                closed = true;
            }
            LogMessage::InputWorkFinalized { captures } => {
                if !enabled
                    || !graph_finished
                    || finalized.is_some()
                    || captures > MAX_CAPTURES as u64
                {
                    bail!("invalid or duplicate input-work finalization acknowledgement");
                }
                finalized = Some(captures);
            }
            LogMessage::BuildStarted {
                workspace_root: root,
                ..
            } => {
                if build_started {
                    bail!("duplicate build-started record");
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
                if graph_finished || units.len() >= MAX_UNITS || units.contains_key(&index) {
                    bail!("duplicate, late, or excessive unit registration");
                }
                increment(&mut denominator.registered_units, 1)?;
                if mode.is_run_custom_build() {
                    increment(&mut denominator.run_script_units, 1)?;
                }
                units.insert(
                    index,
                    UnitState {
                        row: UnitRow {
                            index,
                            package_id: package_id.to_string(),
                            target,
                            mode,
                            platform,
                            features,
                            requested,
                            attempts: 0,
                            captured_attempts: 0,
                            uncacheable_attempts: 0,
                            phases: Vec::new(),
                            work: None,
                        },
                        dependencies,
                        phases: BTreeMap::new(),
                    },
                );
            }
            LogMessage::UnitGraphFinished { .. } => {
                if graph_finished {
                    bail!("duplicate unit-graph-finished record");
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
                graph_finished = true;
            }
            LogMessage::InputWorkStarted {
                capture,
                index,
                phase,
            } => {
                if !enabled
                    || !graph_finished
                    || finalized.is_some()
                    || capture >= MAX_CAPTURES as u64
                    || attempts.contains_key(&capture)
                {
                    bail!("unannounced, duplicate, or excessive input capture attempt");
                }
                let unit = units
                    .get_mut(&index)
                    .context("input work references an unregistered unit")?;
                if !unit.row.mode.is_run_custom_build() || unit.row.target.kind != "build-script" {
                    bail!("input work belongs to a non-build-script run unit");
                }
                if unit.row.attempts == 0 {
                    increment(&mut denominator.observed_units, 1)?;
                }
                increment(&mut unit.row.attempts, 1)?;
                increment(&mut denominator.attempts_started, 1)?;
                let key = phase_id(&phase);
                let phase = unit.phases.entry(key).or_insert_with(|| PhaseRow {
                    phase,
                    attempts: 0,
                    captured_attempts: 0,
                    uncacheable_attempts: 0,
                    work: zero_work(),
                });
                increment(&mut phase.attempts, 1)?;
                attempts.insert(
                    capture,
                    Attempt {
                        index,
                        phase: key,
                        finished: false,
                    },
                );
            }
            LogMessage::InputWorkFinished {
                capture,
                index,
                phase,
                outcome,
                work,
            } => {
                if !enabled || finalized.is_some() {
                    bail!("input capture completion lacks an active schema session");
                }
                let attempt = attempts
                    .get_mut(&capture)
                    .context("capture completion lacks original start")?;
                let key = phase_id(&phase);
                if attempt.finished || attempt.index != index || attempt.phase != key {
                    bail!("duplicate or mismatched capture completion");
                }
                attempt.finished = true;
                increment(&mut denominator.attempts_finished, 1)?;
                let unit = units
                    .get_mut(&index)
                    .context("capture completion references unknown unit")?;
                let phase = unit
                    .phases
                    .get_mut(&key)
                    .context("capture completion references unknown phase")?;
                match outcome {
                    InputWorkOutcome::Captured => {
                        increment(&mut denominator.captured_attempts, 1)?;
                        increment(&mut unit.row.captured_attempts, 1)?;
                        increment(&mut phase.captured_attempts, 1)?;
                    }
                    InputWorkOutcome::Uncacheable => {
                        increment(&mut denominator.uncacheable_attempts, 1)?;
                        increment(&mut unit.row.uncacheable_attempts, 1)?;
                        increment(&mut phase.uncacheable_attempts, 1)?;
                    }
                }
                add_work(unit.row.work.get_or_insert_with(zero_work), &work)?;
                add_work(&mut phase.work, &work)?;
                add_work(&mut totals, &work)?;
            }
            LogMessage::UnitStarted { index, .. }
            | LogMessage::UnitFingerprint { index, .. }
            | LogMessage::UnitSectionStarted { index, .. }
            | LogMessage::UnitSectionFinished { index, .. }
            | LogMessage::UnitPeakMemory { index, .. }
            | LogMessage::UnitCpuTimes { index, .. } => {
                if !units.contains_key(&index) {
                    bail!("log event references unregistered unit");
                }
            }
            LogMessage::UnitFinished {
                index, unblocked, ..
            }
            | LogMessage::UnitRmetaFinished {
                index, unblocked, ..
            } => {
                if !units.contains_key(&index)
                    || unblocked.iter().any(|index| !units.contains_key(index))
                {
                    bail!("log completion references unregistered unit");
                }
            }
            _ => {}
        }
        records += 1;
        Ok(())
    })?;
    if enabled && !closed {
        bail!("input-work log has no terminal completeness record");
    }
    denominator.units_without_attempts = denominator
        .registered_units
        .checked_sub(denominator.observed_units)
        .context("invalid observed-unit denominator")?;
    let rows = units
        .into_values()
        .map(|mut unit| {
            unit.row.phases = unit.phases.into_values().collect();
            unit.row
        })
        .collect();
    Ok(Report {
        schema: "targo-cache-work-report-v1",
        run_id: run.to_owned(),
        scope: "build-script-inputs-v1",
        availability: if enabled { "complete" } else { "unavailable" },
        unavailable_reason: (!enabled).then_some("legacy-log"),
        build_outcome: "not-recorded",
        denominators: denominator,
        units: rows,
        totals: enabled.then_some(totals),
        workspace_root,
    })
}

#[cfg(test)]
mod tests {
    use super::super::log_reader::MAX_LINE_BYTES;
    use super::*;
    use serde_json::{Value, json};
    use std::fs;
    use std::io::Cursor;

    const RUN: &str = "20261105T010203004Z-0123456789abcdef";
    fn frame(mut value: Value) -> String {
        let object = value.as_object_mut().unwrap();
        object.insert("run_id".into(), json!(RUN));
        object.insert("timestamp".into(), json!("2026-11-05T01:02:03Z"));
        format!("{}\n", serde_json::to_string(&value).unwrap())
    }
    fn unit(index: u64, mode: &str) -> Value {
        json!({"reason":"unit-registered","index":index,"package_id":"path+file:///fixture#sample@0.1.0",
            "target":{"name":"build-script-build","kind":"build-script"},"mode":mode,"platform":"test-host"})
    }
    fn base() -> Vec<Value> {
        vec![
            json!({"reason":"input-work-enabled","version":INPUT_WORK_VERSION}),
            json!({"reason":"build-started","command":[],"cwd":"/fixture","host":"test-host","jobs":1,
                "num_cpus":null,"profile":"dev","rustc_version":"test","rustc_version_verbose":"test",
                "target_dir":"/target","workspace_root":"/fixture"}),
            unit(0, "run-custom-build"),
            unit(1, "build"),
            json!({"reason":"unit-graph-finished","elapsed":0.0}),
        ]
    }
    fn start(id: u64) -> Value {
        json!({"reason":"input-work-started","capture":id,"index":0,"phase":"freshness"})
    }
    fn finish(id: u64, outcome: &str, bytes: u64) -> Value {
        json!({"reason":"input-work-finished","capture":id,"index":0,"phase":"freshness","outcome":outcome,
            "work":{"entries":1,"input_bytes":0,"bytes_hashed":bytes,"metadata_reads":2,"resolution_steps":3,"link_reads":0,"observations":4,"revalidations":1}})
    }
    fn close(count: u64) -> Value {
        json!({"reason":"input-work-closed","version":INPUT_WORK_VERSION,"started":count,"finished":count})
    }
    fn finalized(count: u64) -> Value {
        json!({"reason":"input-work-finalized","captures":count})
    }
    fn parse(values: Vec<Value>) -> CargoResult<Report> {
        analyze(
            Cursor::new(values.into_iter().map(frame).collect::<String>()),
            RUN,
        )
    }

    #[test]
    fn interleaved_attempts_keep_complete_denominators_and_partial_failure_work() {
        let mut values = base();
        values.extend([
            start(1),
            start(0),
            finish(0, "captured", 5),
            finish(1, "uncacheable", 7),
            finalized(2),
            close(2),
        ]);
        let report = parse(values).unwrap();
        assert_eq!(report.availability, "complete");
        assert_eq!(report.denominators.registered_units, 2);
        assert_eq!(report.denominators.run_script_units, 1);
        assert_eq!(report.denominators.observed_units, 1);
        assert_eq!(report.denominators.attempts_finished, 2);
        assert_eq!(report.denominators.uncacheable_attempts, 1);
        assert_eq!(report.totals.unwrap().bytes_hashed, 12);
        assert!(report.units[1].work.is_none());
        assert_eq!(report.units[0].phases.len(), 1);
    }

    #[test]
    fn incomplete_duplicate_foreign_unknown_and_overflow_evidence_is_rejected() {
        for extra in [
            vec![start(0), finalized(1), close(1)],
            vec![start(0), start(0)],
            vec![finish(0, "captured", 0)],
            vec![start(1), finish(1, "captured", 0), finalized(1), close(1)],
            vec![
                start(0),
                finish(0, "captured", 0),
                finish(0, "captured", 0),
                finalized(1),
                close(1),
            ],
            vec![
                start(0),
                finish(0, "captured", u64::MAX),
                start(1),
                finish(1, "captured", 1),
                finalized(2),
                close(2),
            ],
            vec![unit(0, "run-custom-build")],
        ] {
            let mut values = base();
            values.extend(extra);
            assert!(parse(values).is_err());
        }
        let mut values = base();
        let mut unknown = start(0);
        unknown["index"] = json!(55);
        values.push(unknown);
        assert!(parse(values).is_err());
        let mut values = base();
        let mut wrong = start(0);
        wrong["phase"] = json!("unknown");
        values.push(wrong);
        assert!(parse(values).is_err());
        let mut values = base();
        values.extend([finalized(0), close(0), start(0)]);
        assert!(parse(values).is_err());
        let mut log = base().into_iter().map(frame).collect::<String>();
        log.push_str(&frame(start(0)).replace(RUN, "20261105T010203004Z-ffffffffffffffff"));
        assert!(analyze(Cursor::new(log), RUN).is_err());
    }

    #[test]
    fn legacy_costs_are_unavailable_and_only_sealed_zero_is_complete() {
        let mut legacy = base();
        legacy.remove(0);
        let report = parse(legacy).unwrap();
        assert_eq!(report.availability, "unavailable");
        assert!(report.totals.is_none());
        let mut values = base();
        values.extend([finalized(0), close(0)]);
        assert_eq!(parse(values).unwrap().totals.unwrap().bytes_hashed, 0);
    }

    #[test]
    fn producer_acknowledgement_exposes_lost_or_aborted_capture_events() {
        for extra in [
            vec![finalized(1), close(0)], // Both start and finish were lost.
            vec![start(0), finish(0, "captured", 0), close(1)], // Queue never finalized.
            vec![finalized(0), finalized(0), close(0)],
            vec![finalized(0), start(0), finish(0, "captured", 0), close(1)],
        ] {
            let mut values = base();
            values.extend(extra);
            assert!(parse(values).is_err());
        }
    }

    #[cfg(unix)]
    #[test]
    fn explicit_session_accepts_workspace_alias_and_refuses_different_workspace() {
        let world = tempfile::tempdir().unwrap();
        let workspace = world.path().join("workspace");
        let other = world.path().join("other");
        let alias = world.path().join("alias");
        fs::create_dir(&workspace).unwrap();
        fs::create_dir(&other).unwrap();
        std::os::unix::fs::symlink(&workspace, &alias).unwrap();
        let mut values = base();
        values[1]
            .as_object_mut()
            .unwrap()
            .insert("workspace_root".into(), json!(workspace));
        values.extend([finalized(0), close(0)]);
        let report = parse(values).unwrap();
        require_workspace(&report, &alias).unwrap();
        assert!(require_workspace(&report, &other).is_err());
        assert!(require_workspace(&report, &world.path().join("missing")).is_err());
        assert!(
            serde_json::to_value(&report)
                .unwrap()
                .get("workspace_root")
                .is_none()
        );
    }

    #[test]
    fn malformed_duplicate_fields_truncated_and_oversized_frames_are_rejected() {
        let duplicate = format!(
            "{{\"run_id\":\"{RUN}\",\"run_id\":\"{RUN}\",\"timestamp\":\"2026-11-05T01:02:03Z\",\"reason\":\"input-work-enabled\",\"version\":1}}\n"
        );
        for log in [
            duplicate,
            "not JSON\n".into(),
            "{}".into(),
            " ".repeat(MAX_LINE_BYTES as usize + 1),
        ] {
            assert!(analyze(Cursor::new(log), RUN).is_err());
        }
    }
}
