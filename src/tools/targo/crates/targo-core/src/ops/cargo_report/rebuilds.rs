//! The `cargo report rebuilds` command.

use crate::util::data_structures::{HashMap, HashSet};
use std::io::BufRead;
use std::path::{Path, PathBuf};

use anyhow::{Context as _, bail};
use cargo_util_schemas::core::PackageIdSpec;
use cargo_util_terminal::report::Group;
use cargo_util_terminal::report::Level;
use itertools::Itertools as _;
use serde::Serialize;

use crate::AlreadyPrintedError;
use crate::CargoResult;
use crate::GlobalContext;
use crate::compiler::CompileMode;
use crate::compiler::UnitIndex;
use crate::compiler::fingerprint::DirtyReason;
use crate::compiler::fingerprint::FsStatus;
use crate::compiler::fingerprint::StaleItem;
use crate::ops::cargo_report::log_reader::{
    MAX_UNITS, read_checked, read_records, require_workspace,
};
use crate::ops::cargo_report::util::find_log_file;
use crate::ops::cargo_report::util::unit_target_description;
use crate::util::log_message::{
    EXECUTION_VERSION, ExecutionGraphOutcome, ExecutionUnitOutcome, FingerprintStatus,
    INPUT_WORK_VERSION, LogMessage, Target,
};
use crate::util::logger::RunId;
use crate::util::machine_message::UnitRebuildCause;
use crate::util::style;
use crate::workspace::Workspace;

const DEFAULT_DISPLAY_LIMIT: usize = 5;
// Trust: shared roots can expand a small recorded graph quadratically. Bound
// every traversed reverse edge across the whole report, including repeats, so
// both traversal work and retained affected-unit entries stay bounded.
const MAX_FRONTIER_EDGE_INSPECTIONS: usize = MAX_UNITS * 16;

pub struct ReportRebuildsOptions {
    pub id: Option<RunId>,
    pub json: bool,
}

pub fn report_rebuilds(
    gctx: &GlobalContext,
    ws: Option<&Workspace<'_>>,
    opts: ReportRebuildsOptions,
) -> CargoResult<()> {
    let selection_ws = if opts.id.is_some() { None } else { ws };
    let Some((log, run_id)) = find_log_file(gctx, selection_ws, opts.id.as_ref())? else {
        let context = if let Some(ws) = ws {
            format!(" for workspace at `{}`", ws.root().display())
        } else {
            String::new()
        };
        let (title, note) = if let Some(id) = &opts.id {
            (
                format!("session `{id}` not found{context}"),
                "run `cargo report sessions` to list available sessions",
            )
        } else {
            (
                format!("no sessions found{context}"),
                "run command with `-Z build-analysis` to generate log files",
            )
        };
        let report = [Level::ERROR
            .primary_title(title)
            .element(Level::NOTE.message(note))];
        gctx.shell().print_report(&report, false)?;
        return Err(AlreadyPrintedError::new(anyhow::anyhow!("")).into());
    };

    let ctx = prepare_context(&log, &run_id.to_string(), !opts.json)
        .with_context(|| format!("failed to analyze log at `{}`", log.display()))?;
    if let Some(ws) = ws {
        require_workspace(Some(&ctx.workspace_root), ws.root())?;
    }
    // Trust: validate the recorded workspace above, while keeping displayed
    // paths relative to the invocation when querying from outside a workspace.
    let ws_root = ws.map(|ws| ws.root()).unwrap_or(gctx.cwd());

    if opts.json {
        let mut bytes = serde_json::to_vec(&json_report(&ctx, &run_id.to_string()))?;
        bytes.push(b'\n');
        gctx.shell().print_ansi_stdout(&bytes)?;
    } else {
        display_report(gctx, ctx, &run_id, ws_root)?;
    }

    Ok(())
}

struct Context {
    root_rebuilds: Vec<RootRebuild>,
    units: HashMap<UnitIndex, UnitInfo>,
    total_cached: usize,
    total_new: usize,
    total_rebuilt: usize,
    // Trust: legacy logs have no terminal record; do not claim stream completeness.
    stream_complete: bool,
    input_accounting_unavailable: bool,
    input_accounting_finalized: bool,
    workspace_root: PathBuf,
}

struct UnitInfo {
    package_id: PackageIdSpec,
    target: Target,
    mode: CompileMode,
    platform: String,
    features: Vec<String>,
    requested: bool,
    dependencies: Vec<UnitIndex>,
    fingerprint: Option<FingerprintObservation>,
}

// Trust: retain only the validated final classification and the existing
// payload-free category. Raw diagnostic values remain in the human context.
#[derive(Serialize)]
struct FingerprintObservation {
    status: FingerprintStatus,
    reason: Option<UnitRebuildCause>,
    rechecked: bool,
}

#[derive(Serialize)]
struct JsonReport<'a> {
    schema: &'static str,
    run_id: &'a str,
    scope: &'static str,
    stream_completeness: &'static str,
    input_accounting: &'static str,
    registered_units: usize,
    classified_units: usize,
    unclassified_units: usize,
    observed_counts: ObservedCounts,
    units: Vec<JsonUnit<'a>>,
    non_cached_dependency_frontier_roots: Vec<UnitIndex>,
}

#[derive(Serialize)]
struct ObservedCounts {
    cached: usize,
    dirty: usize,
    new: usize,
}

#[derive(Serialize)]
struct JsonUnit<'a> {
    index: UnitIndex,
    package_id: String,
    target: &'a Target,
    mode: CompileMode,
    platform: &'a str,
    features: Vec<&'a str>,
    requested: bool,
    dependencies: Vec<UnitIndex>,
    fingerprint: Option<&'a FingerprintObservation>,
}

fn json_report<'a>(ctx: &'a Context, run_id: &'a str) -> JsonReport<'a> {
    let classified = ctx
        .units
        .values()
        .filter(|unit| unit.fingerprint.is_some())
        .count();
    JsonReport {
        schema: "targo-rebuilds-v1",
        run_id,
        scope: "observed-fingerprint-classifications",
        stream_completeness: if ctx.stream_complete {
            "complete"
        } else {
            "unavailable"
        },
        input_accounting: if ctx.input_accounting_finalized {
            "finalized"
        } else {
            "unavailable"
        },
        registered_units: ctx.units.len(),
        classified_units: classified,
        unclassified_units: ctx.units.len() - classified,
        observed_counts: ObservedCounts {
            cached: ctx.total_cached,
            dirty: ctx.total_rebuilt,
            new: ctx.total_new,
        },
        units: ctx
            .units
            .iter()
            .sorted_by_key(|(index, _)| **index)
            .map(|(&index, unit)| JsonUnit {
                index,
                package_id: unit.package_id.to_string(),
                target: &unit.target,
                mode: unit.mode,
                platform: &unit.platform,
                features: unit.features.iter().map(String::as_str).sorted().collect(),
                requested: unit.requested,
                dependencies: unit.dependencies.iter().copied().sorted().collect(),
                fingerprint: unit.fingerprint.as_ref(),
            })
            .collect(),
        // Reuse the existing non-cached dependency frontier. These indices do
        // not establish which compiler ran or what caused any measured CPU.
        non_cached_dependency_frontier_roots: ctx
            .root_rebuilds
            .iter()
            .map(|root| root.unit_index)
            .sorted()
            .collect(),
    }
}

struct RootRebuild {
    unit_index: UnitIndex,
    reason: DirtyReason,
    affected_units: Vec<UnitIndex>,
}

// Trust: preserve only explicitly marked, bounded post-lock rechecks. They
// replace a unit's classification, never add another unit to the denominator.
struct FingerprintState {
    status: FingerprintStatus,
    cause: Option<DirtyReason>,
    rechecked: bool,
}

fn prepare_context(log: &Path, run: &str, include_expanded_impact: bool) -> CargoResult<Context> {
    read_checked(log, |reader| {
        if include_expanded_impact {
            analyze(reader, run)
        } else {
            analyze_with_impact(reader, run, false)
        }
    })
}

// Trust: framing, run identity, and record decoding are shared with the other
// strict reports; this state machine checks rebuild-specific event semantics.
fn analyze(reader: impl BufRead, run: &str) -> CargoResult<Context> {
    analyze_with_impact(reader, run, true)
}

fn analyze_with_impact(
    reader: impl BufRead,
    run: &str,
    include_expanded_impact: bool,
) -> CargoResult<Context> {
    let mut units: HashMap<UnitIndex, UnitInfo> = HashMap::default();
    let mut dependencies: HashMap<UnitIndex, Vec<UnitIndex>> = HashMap::default();
    let mut fingerprints = HashMap::<UnitIndex, FingerprintState>::default();
    let mut scheduled = HashMap::<UnitIndex, bool>::default();
    let mut completed = HashSet::default();
    let mut outcomes = HashMap::default();
    let mut workspace_root = None;
    let mut graph_finished = false;
    let mut input_enabled = false;
    let mut execution_enabled = false;
    let mut execution_finished = false;
    let mut execution_outcome = None;
    let mut closed = false;
    let mut records = 0usize;
    let mut captures_started = 0u64;
    let mut captures_finished = 0u64;
    let mut finalized_captures = None;
    read_records(reader, run, |message| {
        if closed {
            bail!("data after terminal rebuild log record");
        }
        if input_enabled
            && workspace_root.is_none()
            && !matches!(&message, LogMessage::BuildStarted { .. })
        {
            bail!("rebuild session lacks its original build-started record");
        }
        let capture_started = matches!(&message, LogMessage::InputWorkStarted { .. });
        let capture_finished = matches!(&message, LogMessage::InputWorkFinished { .. });
        if (capture_started || capture_finished) && finalized_captures.is_some() {
            bail!("rebuild input work follows its finalization");
        }
        match message {
            LogMessage::InputWorkEnabled { version } => {
                if records != 0 || input_enabled || version != INPUT_WORK_VERSION {
                    bail!("unsupported or misplaced rebuild log schema");
                }
                input_enabled = true;
            }
            LogMessage::BuildStarted {
                workspace_root: root,
                ..
            } => {
                if workspace_root.is_some() || !units.is_empty() || !root.is_absolute() {
                    bail!("duplicate, late, or invalid rebuild workspace record");
                }
                workspace_root = Some(root);
            }
            LogMessage::UnitRegistered {
                package_id,
                target,
                mode,
                index,
                dependencies: deps,
                platform,
                features,
                requested,
            } => {
                if workspace_root.is_none()
                    || graph_finished
                    || units.len() >= MAX_UNITS
                    || units.contains_key(&index)
                    || deps.contains(&index)
                {
                    bail!("duplicate, late, or invalid rebuild unit registration");
                }
                units.insert(
                    index,
                    UnitInfo {
                        package_id,
                        target,
                        mode,
                        platform,
                        features,
                        requested,
                        dependencies: deps.clone(),
                        fingerprint: None,
                    },
                );
                dependencies.insert(index, deps);
            }
            LogMessage::UnitGraphFinished { elapsed } => {
                if workspace_root.is_none()
                    || graph_finished
                    || !elapsed.is_finite()
                    || elapsed < 0.0
                    || dependencies
                        .values()
                        .flatten()
                        .any(|index| !units.contains_key(index))
                {
                    bail!("invalid or duplicate rebuild unit graph completion");
                }
                graph_finished = true;
            }
            LogMessage::UnitFingerprint {
                index,
                status,
                cause,
                recheck,
            } => {
                if !graph_finished || execution_finished || !units.contains_key(&index) {
                    bail!("rebuild fingerprint references an unavailable unit");
                }
                if !recheck && (execution_enabled || completed.contains(&index)) {
                    bail!("late initial rebuild fingerprint");
                }
                match (&status, &cause) {
                    (FingerprintStatus::Dirty, Some(reason)) if !reason.is_fresh_build() => {}
                    (FingerprintStatus::Fresh | FingerprintStatus::New, None) => {}
                    _ => bail!("rebuild fingerprint status contradicts its cause"),
                }
                if recheck {
                    let previous = fingerprints
                        .get_mut(&index)
                        .context("rebuild recheck lacks an initial fingerprint")?;
                    if previous.rechecked
                        || matches!(&previous.status, FingerprintStatus::Fresh)
                        || !execution_enabled
                        || scheduled.get(&index) != Some(&false)
                        || completed.contains(&index)
                    {
                        bail!("duplicate, late, or invalid rebuild fingerprint recheck");
                    }
                    previous.status = status;
                    previous.cause = cause;
                    previous.rechecked = true;
                } else if fingerprints
                    .insert(
                        index,
                        FingerprintState {
                            status,
                            cause,
                            rechecked: false,
                        },
                    )
                    .is_some()
                {
                    bail!("duplicate initial rebuild fingerprint");
                }
            }
            LogMessage::ExecutionEnabled { version } => {
                if !input_enabled
                    || !graph_finished
                    || execution_enabled
                    || version != EXECUTION_VERSION
                {
                    bail!("unsupported or misplaced rebuild execution schema");
                }
                execution_enabled = true;
            }
            LogMessage::UnitScheduled { index, fresh, .. } => {
                if !execution_enabled
                    || execution_finished
                    || !units.contains_key(&index)
                    // Trust: doctest jobs deliberately bypass prepare_target;
                    // every other scheduled compile job has a prior read-set classification.
                    || (!fingerprints.contains_key(&index)
                        && !units[&index].mode.is_doc_test())
                    || fingerprints.get(&index).is_some_and(|fingerprint| {
                        fresh != matches!(&fingerprint.status, FingerprintStatus::Fresh)
                    })
                    || scheduled.insert(index, fresh).is_some()
                {
                    bail!("duplicate or invalid rebuild unit dispatch");
                }
            }
            LogMessage::UnitOutcome { index, outcome, .. } => {
                if !execution_enabled
                    || execution_finished
                    || !scheduled.contains_key(&index)
                    || outcomes.insert(index, outcome).is_some()
                {
                    bail!("duplicate or invalid rebuild unit outcome");
                }
                completed.insert(index);
            }
            LogMessage::ExecutionGraphFinished {
                outcome,
                scheduled: observed_scheduled,
                completed: observed_completed,
                not_executed,
                ..
            } => {
                if !execution_enabled
                    || execution_finished
                    || observed_scheduled != scheduled.len() as u64
                    || observed_completed != outcomes.len() as u64
                    || observed_completed > observed_scheduled
                    || not_executed.checked_add(observed_scheduled) != Some(units.len() as u64)
                    || (outcome == ExecutionGraphOutcome::Succeeded
                        && (observed_completed != observed_scheduled
                            || outcomes.values().any(|outcome| {
                                matches!(
                                    outcome,
                                    ExecutionUnitOutcome::Failed | ExecutionUnitOutcome::Cancelled
                                )
                            })))
                {
                    bail!("invalid or duplicate rebuild execution completion");
                }
                execution_finished = true;
                execution_outcome = Some(outcome);
            }
            LogMessage::InputWorkStarted { index, .. }
            | LogMessage::InputWorkFinished { index, .. }
            | LogMessage::UnitStarted { index, .. }
            | LogMessage::UnitSectionStarted { index, .. }
            | LogMessage::UnitSectionFinished { index, .. }
            | LogMessage::UnitPeakMemory { index, .. }
            | LogMessage::UnitCpuTimes { index, .. } => {
                if !units.contains_key(&index) {
                    bail!("rebuild log event references an unregistered unit");
                }
            }
            LogMessage::UnitFinished {
                index, unblocked, ..
            } => {
                if !units.contains_key(&index)
                    || unblocked.iter().any(|index| !units.contains_key(index))
                {
                    bail!("rebuild completion references an unregistered unit");
                }
                completed.insert(index);
            }
            LogMessage::UnitRmetaFinished {
                index, unblocked, ..
            } => {
                if !units.contains_key(&index)
                    || unblocked.iter().any(|index| !units.contains_key(index))
                {
                    bail!("rebuild completion references an unregistered unit");
                }
            }
            LogMessage::InputWorkClosed {
                version,
                started,
                finished,
            } => {
                if !input_enabled
                    || version != INPUT_WORK_VERSION
                    || !graph_finished
                    || (execution_enabled && !execution_finished)
                    || started != captures_started
                    || finished != captures_finished
                    || match finalized_captures {
                        Some(captures) => captures != started,
                        // Trust: failed/cancelled queues close their actual log
                        // but do not publish successful input finalization.
                        None => !matches!(
                            execution_outcome,
                            Some(ExecutionGraphOutcome::Failed | ExecutionGraphOutcome::Cancelled)
                        ),
                    }
                {
                    bail!("rebuild log lacks a complete supported stream closure");
                }
                closed = true;
            }
            LogMessage::InputWorkFinalized { captures } => {
                if !input_enabled
                    || !graph_finished
                    || finalized_captures.is_some()
                    || (execution_enabled && !execution_finished)
                {
                    bail!("invalid or duplicate rebuild input finalization");
                }
                finalized_captures = Some(captures);
            }
            _ => {}
        }
        // Trust: compare closure framing counts without claiming capture success.
        captures_started += u64::from(capture_started);
        captures_finished += u64::from(capture_finished);
        records += 1;
        Ok(())
    })?;
    if input_enabled && !closed {
        bail!("rebuild log has no terminal stream closure");
    }
    if !graph_finished {
        bail!("rebuild log has no complete unit graph");
    }
    let workspace_root = workspace_root.context("rebuild log lacks its original workspace")?;
    let mut dirty_reasons = HashMap::default();
    let mut total_cached = 0;
    let mut total_new = 0;
    let mut total_rebuilt = 0;
    for (index, fingerprint) in fingerprints {
        units
            .get_mut(&index)
            .expect("validated fingerprint unit")
            .fingerprint = Some(FingerprintObservation {
            status: fingerprint.status.clone(),
            reason: fingerprint.cause.as_ref().map(DirtyReason::dispatch_cause),
            rechecked: fingerprint.rechecked,
        });
        match fingerprint.status {
            FingerprintStatus::Fresh => total_cached += 1,
            FingerprintStatus::Dirty => {
                total_rebuilt += 1;
                dirty_reasons.insert(
                    index,
                    fingerprint.cause.context("dirty fingerprint lacks cause")?,
                );
            }
            FingerprintStatus::New => {
                total_new += 1;
                dirty_reasons.insert(index, DirtyReason::FreshBuild);
            }
        }
    }

    // reverse dependency graph (dependents of each unit)
    let mut reverse_deps: HashMap<UnitIndex, Vec<UnitIndex>> = HashMap::default();
    if include_expanded_impact {
        for (unit_id, deps) in &dependencies {
            for dep_id in deps {
                reverse_deps.entry(*dep_id).or_default().push(*unit_id);
            }
        }
    }

    let rebuilt_units: HashSet<UnitIndex> = dirty_reasons.keys().copied().collect();
    let mut frontier_edges_left = MAX_FRONTIER_EDGE_INSPECTIONS;

    // Root rebuilds: units that rebuilt but none of their dependencies rebuilt
    let root_rebuilds: Vec<_> = dirty_reasons
        .iter()
        .filter(|(unit_index, _)| {
            let has_rebuilt_deps = dependencies
                .get(unit_index)
                .map(|deps| deps.iter().any(|dep| rebuilt_units.contains(dep)))
                .unwrap_or_default();
            !has_rebuilt_deps
        })
        .map(|(&unit_index, reason)| {
            let affected_units = if include_expanded_impact {
                find_cascading_rebuilds(
                    unit_index,
                    &reverse_deps,
                    &rebuilt_units,
                    &mut frontier_edges_left,
                )?
            } else {
                Vec::new()
            };
            Ok(RootRebuild {
                unit_index,
                reason: reason.clone(),
                affected_units,
            })
        })
        .collect::<CargoResult<Vec<_>>>()?
        .into_iter()
        .sorted_by(|a, b| {
            b.affected_units
                .len()
                .cmp(&a.affected_units.len())
                .then_with(|| {
                    let a_name = units.get(&a.unit_index).map(|u| u.package_id.name());
                    let b_name = units.get(&b.unit_index).map(|u| u.package_id.name());
                    a_name.cmp(&b_name)
                })
        })
        .collect();

    Ok(Context {
        root_rebuilds,
        units,
        total_cached,
        total_new,
        total_rebuilt,
        stream_complete: closed,
        input_accounting_unavailable: input_enabled && finalized_captures.is_none(),
        input_accounting_finalized: finalized_captures.is_some(),
        workspace_root,
    })
}

/// Finds classified non-cached dependents within the report's shared edge budget.
fn find_cascading_rebuilds(
    root_rebuild: UnitIndex,
    dependents: &HashMap<UnitIndex, Vec<UnitIndex>>,
    rebuilt_units: &HashSet<UnitIndex>,
    frontier_edges_left: &mut usize,
) -> CargoResult<Vec<UnitIndex>> {
    let mut affected = Vec::new();
    let mut visited = HashSet::default();
    let mut queue = vec![root_rebuild];
    visited.insert(root_rebuild);

    while let Some(unit) = queue.pop() {
        if let Some(deps) = dependents.get(&unit) {
            for &dep in deps {
                *frontier_edges_left = frontier_edges_left
                    .checked_sub(1)
                    .context("rebuild dependency frontier expansion budget exhausted; use --json for compact dependency topology")?;
                if !visited.contains(&dep) && rebuilt_units.contains(&dep) {
                    visited.insert(dep);
                    affected.push(dep);
                    queue.push(dep);
                }
            }
        }
    }

    affected.sort_unstable();
    Ok(affected)
}

fn display_report(
    gctx: &GlobalContext,
    ctx: Context,
    run_id: &RunId,
    ws_root: &Path,
) -> CargoResult<()> {
    let verbose = gctx.shell().verbosity() == cargo_util_terminal::Verbosity::Verbose;
    let extra_verbose = gctx.extra_verbose();

    let Context {
        root_rebuilds,
        units,
        total_cached,
        total_new,
        total_rebuilt,
        stream_complete,
        input_accounting_unavailable,
        input_accounting_finalized: _,
        workspace_root: _,
    } = ctx;

    let header = style::HEADER;
    let subheader = style::LITERAL;
    let mut shell = gctx.shell();
    let stderr = shell.err();

    writeln!(stderr, "{header}Session:{header:#} {run_id}")?;
    if !stream_complete {
        writeln!(stderr, "Legacy log: stream completeness is unavailable")?;
    }
    if input_accounting_unavailable {
        writeln!(
            stderr,
            "Input accounting: unavailable after unsuccessful execution"
        )?;
    }

    // Render summary
    let rebuilt_plural = plural(total_rebuilt);

    writeln!(
        stderr,
        "{header}Status:{header:#} {total_rebuilt} unit{rebuilt_plural} rebuilt, {total_cached} cached, {total_new} new"
    )?;
    writeln!(stderr)?;

    if total_rebuilt == 0 && total_new == 0 {
        // Don't show detailed report if all units are cached.
        return Ok(());
    }

    if total_rebuilt == 0 && total_cached == 0 {
        // Don't show detailed report if all units are new build.
        return Ok(());
    }

    // Render root rebuilds and cascading count
    let root_rebuild_count = root_rebuilds.len();
    let cascading_count: usize = root_rebuilds.iter().map(|r| r.affected_units.len()).sum();

    let root_plural = plural(root_rebuild_count);
    let cascading_plural = plural(cascading_count);

    writeln!(stderr, "{header}Rebuild impact:{header:#}",)?;
    writeln!(
        stderr,
        "  root rebuilds: {root_rebuild_count} unit{root_plural}"
    )?;
    writeln!(
        stderr,
        "  cascading:     {cascading_count} unit{cascading_plural}"
    )?;
    writeln!(stderr)?;

    // Render each root rebuilds
    let display_limit = if verbose {
        root_rebuilds.len()
    } else {
        DEFAULT_DISPLAY_LIMIT.min(root_rebuilds.len())
    };
    let truncated_count = root_rebuilds.len().saturating_sub(display_limit);

    if truncated_count > 0 {
        let count = root_rebuilds.len();
        writeln!(
            stderr,
            "{header}Root rebuilds:{header:#} (top {display_limit} of {count} by impact)",
        )?;
    } else {
        writeln!(stderr, "{header}Root rebuilds:{header:#}",)?;
    }

    for (idx, root_rebuild) in root_rebuilds.iter().take(display_limit).enumerate() {
        let unit_desc = units
            .get(&root_rebuild.unit_index)
            .map(unit_description)
            .expect("must have the unit");

        let reason_str = format_dirty_reason(&root_rebuild.reason, &units, ws_root);

        writeln!(
            stderr,
            "  {subheader}{idx}. {unit_desc}:{subheader:#} {reason_str}",
        )?;

        if root_rebuild.affected_units.is_empty() {
            writeln!(stderr, "     impact: no cascading rebuilds")?;
        } else {
            let count = root_rebuild.affected_units.len();
            let plural = plural(count);
            writeln!(
                stderr,
                "     impact: {count} dependent unit{plural} rebuilt"
            )?;

            if extra_verbose {
                for affected in &root_rebuild.affected_units {
                    if let Some(affected) = units.get(affected) {
                        let desc = unit_description(affected);
                        writeln!(stderr, "       - {desc}")?;
                    }
                }
            }
        }
    }

    // Render --verbose notes
    drop(shell);
    let has_cascading_rebuilds = root_rebuilds.iter().any(|rr| !rr.affected_units.is_empty());

    if !verbose && truncated_count > 0 {
        writeln!(gctx.shell().err())?;
        let note = "pass `--verbose` to show all root rebuilds";
        gctx.shell().print_report(
            &[Group::with_title(Level::NOTE.secondary_title(note))],
            false,
        )?;
    } else if !extra_verbose && has_cascading_rebuilds {
        writeln!(gctx.shell().err())?;
        let note = "pass `-vv` to show all affected rebuilt unit lists";
        gctx.shell().print_report(
            &[Group::with_title(Level::NOTE.secondary_title(note))],
            false,
        )?;
    }

    Ok(())
}

fn unit_description(unit: &UnitInfo) -> String {
    let name = unit.package_id.name();
    let version = unit
        .package_id
        .version()
        .map(|v| v.to_string())
        .unwrap_or_else(|| "<n/a>".into());
    let target = unit_target_description(&unit.target, unit.mode);

    let literal = style::LITERAL;
    let nop = style::NOP;

    format!("{literal}{name}@{version}{literal:#}{nop}{target}{nop:#}")
}

fn plural(len: usize) -> &'static str {
    if len == 1 { "" } else { "s" }
}

fn format_dirty_reason(
    reason: &DirtyReason,
    units: &HashMap<UnitIndex, UnitInfo>,
    ws_root: &Path,
) -> String {
    match reason {
        DirtyReason::RustcChanged => "toolchain changed".to_string(),
        DirtyReason::FeaturesChanged { old, new } => {
            format!("activated features changed: {old} -> {new}")
        }
        DirtyReason::DeclaredFeaturesChanged { old, new } => {
            format!("declared features changed: {old} -> {new}")
        }
        DirtyReason::TargetConfigurationChanged => "target configuration changed".to_string(),
        DirtyReason::PathToSourceChanged => "path to source changed".to_string(),
        DirtyReason::ProfileConfigurationChanged => "profile configuration changed".to_string(),
        DirtyReason::RustflagsChanged { old, new } => {
            let old = old.join(", ");
            let new = new.join(", ");
            format!("rustflags changed: {old} -> {new}")
        }
        DirtyReason::ConfigSettingsChanged => "config settings changed".to_string(),
        DirtyReason::CompileKindChanged => "compile target changed".to_string(),
        DirtyReason::FsStatusOutdated(status) => match status {
            FsStatus::Stale => "filesystem status stale".to_string(),
            FsStatus::StaleItem(item) => match item {
                StaleItem::MissingFile { path } => {
                    let path = path.strip_prefix(ws_root).unwrap_or(path).display();
                    format!("file missing: {path}")
                }
                StaleItem::UnableToReadFile { path } => {
                    let path = path.strip_prefix(ws_root).unwrap_or(path).display();
                    format!("unable to read file: {path}")
                }
                // Trust: this names an input-fact refusal, not output I/O.
                StaleItem::BuildScriptInputsUnavailable { output_anchor } => {
                    let output = output_anchor
                        .strip_prefix(ws_root)
                        .unwrap_or(output_anchor)
                        .display();
                    format!(
                        "build-script input observation unavailable or invalid (output anchor {output})"
                    )
                }
                // Trust: explain the actual dependency-cache rejection, not a missing file.
                StaleItem::DepInfoUnavailable { path, reason } => {
                    let path = path.strip_prefix(ws_root).unwrap_or(path).display();
                    format!("dependency cache `{path}`: {reason}")
                }
                StaleItem::OutputIntegrity { path, reason } => {
                    let path = path.strip_prefix(ws_root).unwrap_or(path).display();
                    format!("cached output integrity failed at {path}: {reason}")
                }
                StaleItem::FailedToReadMetadata { path } => {
                    let path = path.strip_prefix(ws_root).unwrap_or(path).display();
                    format!("failed to read file metadata: {path}")
                }
                StaleItem::FileSizeChanged {
                    path,
                    old_size: old,
                    new_size: new,
                } => {
                    let path = path.strip_prefix(ws_root).unwrap_or(path).display();
                    format!("file size changed: {path} ({old} -> {new} bytes)")
                }
                StaleItem::ChangedFile { stale, .. } => {
                    let path = stale.strip_prefix(ws_root).unwrap_or(stale).display();
                    format!("file modified: {path}")
                }
                StaleItem::ChangedChecksum {
                    source,
                    stored_checksum: old,
                    new_checksum: new,
                } => {
                    let path = source.strip_prefix(ws_root).unwrap_or(source).display();
                    format!("file checksum changed: {path} ({old} -> {new})")
                }
                StaleItem::MissingChecksum { path } => {
                    let path = path.strip_prefix(ws_root).unwrap_or(path).display();
                    format!("checksum missing: {path}")
                }
                StaleItem::ModuleCandidateChanged {
                    path,
                    previous,
                    current,
                } => {
                    let path = path.strip_prefix(ws_root).unwrap_or(path).display();
                    let state = |present| match present {
                        Some(false) => "absent",
                        Some(true) => "present",
                        None => "unavailable",
                    };
                    format!(
                        "Rust module candidate changed: {path} ({} -> {})",
                        state(*previous),
                        state(*current)
                    )
                }
                StaleItem::ChangedEnv {
                    var,
                    previous,
                    current,
                } => {
                    let old = previous.as_deref().unwrap_or("<unset>");
                    let new = current.as_deref().unwrap_or("<unset>");
                    format!("environment variable changed ({var}): {old} -> {new}")
                }
            },
            FsStatus::StaleDepFingerprint { unit } => units
                .get(unit)
                .map(|u| format!("dependency rebuilt: {}", unit_description(u)))
                .unwrap_or_else(|| format!("dependency rebuilt: unit {unit}")),
            FsStatus::StaleDependency { unit, .. } => units
                .get(unit)
                .map(|u| format!("dependency rebuilt: {}", unit_description(u)))
                .unwrap_or_else(|| format!("dependency rebuilt: unit {unit}")),
            FsStatus::UpToDate { .. } => "up to date".to_string(),
        },
        DirtyReason::EnvVarChanged {
            name,
            old_value,
            new_value,
        } => {
            let old = old_value.as_deref().unwrap_or("<unset>");
            let new = new_value.as_deref().unwrap_or("<unset>");
            format!("environment variable changed ({name}): {old} -> {new}")
        }
        DirtyReason::EnvVarsChanged { old, new } => {
            format!("environment variables changed: {old} -> {new}")
        }
        DirtyReason::LocalFingerprintTypeChanged { old, new } => {
            format!("local fingerprint type changed: {old} -> {new}")
        }
        DirtyReason::NumberOfDependenciesChanged { old, new } => {
            format!("number of dependencies changed: {old} -> {new}")
        }
        DirtyReason::UnitDependencyNameChanged { old, new } => {
            format!("dependency name changed: {old} -> {new}")
        }
        DirtyReason::UnitDependencyInfoChanged { unit } => units
            .get(unit)
            .map(|u| format!("dependency info changed: {}", unit_description(u)))
            .unwrap_or_else(|| "dependency info changed".to_string()),
        DirtyReason::LocalLengthsChanged => "local lengths changed".to_string(),
        DirtyReason::PrecalculatedComponentsChanged { old, new } => {
            format!("precalculated components changed: {old} -> {new}")
        }
        DirtyReason::FingerprintMethodChanged { old, new } => {
            format!("fingerprinty changed: {old} -> {new}")
        }
        DirtyReason::DepInfoOutputChanged { old, new } => {
            let old = old.strip_prefix(ws_root).unwrap_or(old).display();
            let new = new.strip_prefix(ws_root).unwrap_or(new).display();
            format!("dependency info output changed: {old} -> {new}")
        }
        DirtyReason::RerunIfChangedOutputFileChanged { old, new } => {
            let old = old.strip_prefix(ws_root).unwrap_or(old).display();
            let new = new.strip_prefix(ws_root).unwrap_or(new).display();
            format!("rerun-if-changed output file changed: {old} -> {new}")
        }
        DirtyReason::RerunIfChangedOutputPathsChanged { old, new } => {
            let old = old.len();
            let new = new.len();
            format!("rerun-if-changed paths changed: {old} path(s) -> {new} path(s)",)
        }
        DirtyReason::NothingObvious => "nothing obvious".to_string(),
        // Trust: distinguish an existing content miss from first enrollment.
        DirtyReason::ContentFingerprintChanged => {
            "recorded content fingerprint does not match".to_string()
        }
        DirtyReason::ContentFingerprintUnavailable => {
            "recorded content fingerprint could not be read".to_string()
        }
        DirtyReason::FingerprintRecordMismatch => {
            "recorded fingerprint key and data disagree".to_string()
        }
        DirtyReason::Forced => "forced rebuild".to_string(),
        DirtyReason::FreshBuild => "fresh build".to_string(),
    }
}

#[cfg(test)]
// Trust: a small recorded graph must not amplify into unbounded report work.
mod frontier_budget_tests {
    use super::*;
    use serde_json::{Value, json};
    use std::io::Cursor;

    #[test]
    fn shared_frontiers_preserve_topology_and_consume_one_budget() {
        let dependents = HashMap::from_iter([
            (UnitIndex(0), vec![UnitIndex(2)]),
            (UnitIndex(1), vec![UnitIndex(2)]),
            (UnitIndex(2), vec![UnitIndex(3)]),
            (UnitIndex(3), vec![UnitIndex(4)]),
        ]);
        let rebuilt = (0..5).map(UnitIndex).collect();
        let mut remaining = 6;
        for root in [UnitIndex(0), UnitIndex(1)] {
            assert_eq!(
                find_cascading_rebuilds(root, &dependents, &rebuilt, &mut remaining).unwrap(),
                [UnitIndex(2), UnitIndex(3), UnitIndex(4)]
            );
        }
        assert_eq!(remaining, 0);
        assert!(
            find_cascading_rebuilds(UnitIndex(2), &dependents, &rebuilt, &mut remaining)
                .unwrap_err()
                .to_string()
                .contains("frontier expansion budget exhausted")
        );
        assert_eq!(remaining, 0);
    }

    #[test]
    fn repeated_and_excluded_edges_consume_budget_without_counter_underflow() {
        let dependents =
            HashMap::from_iter([(UnitIndex(0), vec![UnitIndex(1), UnitIndex(1), UnitIndex(2)])]);
        let rebuilt = HashSet::from_iter([UnitIndex(0), UnitIndex(1)]);
        let mut exact = 3;
        assert_eq!(
            find_cascading_rebuilds(UnitIndex(0), &dependents, &rebuilt, &mut exact).unwrap(),
            [UnitIndex(1)]
        );
        assert_eq!(exact, 0);

        let mut short = 2;
        assert!(find_cascading_rebuilds(UnitIndex(0), &dependents, &rebuilt, &mut short).is_err());
        assert_eq!(short, 0);
        assert!(find_cascading_rebuilds(UnitIndex(0), &dependents, &rebuilt, &mut short).is_err());
        assert_eq!(short, 0);
        assert!(
            find_cascading_rebuilds(UnitIndex(2), &dependents, &rebuilt, &mut short)
                .unwrap()
                .is_empty()
        );
    }

    // Decoder inputs, not claims that these synthetic units actually compiled.
    fn shared_chain_log(roots: usize, chain: usize, current: bool) -> String {
        const RUN: &str = "20261109T000000000Z-0123456789abcdef";
        let workspace = std::env::current_dir().unwrap();
        let total = roots + chain;
        let mut records = Vec::new();
        if current {
            records.push(json!({"reason":"input-work-enabled","version":INPUT_WORK_VERSION}));
        }
        records.push(
            json!({"reason":"build-started","command":[],"cwd":workspace,
            "host":"host","jobs":1,"num_cpus":null,"profile":"dev",
            "rustc_version":"test","rustc_version_verbose":"test",
            "target_dir":workspace.join("target"),"workspace_root":workspace}),
        );
        for index in 0..total {
            let dependencies: Vec<_> = if index < roots {
                Vec::new()
            } else if index == roots {
                (0..roots).collect()
            } else {
                vec![index - 1]
            };
            records.push(json!({"reason":"unit-registered","index":index,
                "package_id":format!("frontier-{index}@0.1.0"),
                "target":{"name":format!("frontier-{index}"),"kind":"lib"},
                "mode":"build","platform":"host","dependencies":dependencies}));
        }
        records.push(json!({"reason":"unit-graph-finished","elapsed":0.0}));
        for index in 0..total {
            records.push(json!({"reason":"unit-fingerprint","index":index,
                "status":"dirty","cause":DirtyReason::Forced}));
        }
        if current {
            records.push(json!({"reason":"execution-enabled","version":EXECUTION_VERSION}));
            for index in 0..total {
                records.extend([
                    json!({"reason":"unit-scheduled","index":index,"elapsed":0.0,"fresh":false}),
                    json!({"reason":"unit-finished","index":index,"elapsed":1.0}),
                    json!({"reason":"unit-outcome","index":index,"elapsed":1.0,"outcome":"succeeded"}),
                ]);
            }
            records.extend([
                json!({"reason":"execution-graph-finished","elapsed":1.0,
                    "outcome":"succeeded","scheduled":total,"completed":total,"not_executed":0}),
                json!({"reason":"input-work-finalized","captures":0}),
                json!({"reason":"input-work-closed","version":INPUT_WORK_VERSION,
                    "started":0,"finished":0}),
            ]);
        }
        records
            .into_iter()
            .map(|mut record: Value| {
                record["run_id"] = json!(RUN);
                record["timestamp"] = json!("2026-11-09T00:00:00Z");
                format!("{record}\n")
            })
            .collect()
    }

    #[test]
    fn small_current_and_legacy_shared_chain_reports_keep_complete_frontiers() {
        for current in [false, true] {
            let log = shared_chain_log(2, 3, current);
            let context = analyze(
                Cursor::new(log.as_bytes()),
                "20261109T000000000Z-0123456789abcdef",
            )
            .unwrap();
            assert_eq!(context.total_rebuilt, 5);
            assert_eq!(context.root_rebuilds.len(), 2);
            assert_eq!(context.stream_complete, current);
            for root in context.root_rebuilds {
                assert_eq!(
                    root.affected_units,
                    [UnitIndex(2), UnitIndex(3), UnitIndex(4)]
                );
            }
        }
    }

    #[test]
    fn default_budget_refuses_linear_logs_with_quadratic_shared_frontiers() {
        let roots = 1024;
        let chain = 1025;
        assert!(roots + chain < MAX_UNITS);
        assert!(roots * chain > MAX_FRONTIER_EDGE_INSPECTIONS);
        for current in [false, true] {
            let log = shared_chain_log(roots, chain, current);
            assert!(log.len() < 4 * 1024 * 1024);
            let error = analyze(
                Cursor::new(log.as_bytes()),
                "20261109T000000000Z-0123456789abcdef",
            )
            .err()
            .expect("refuse the bounded log's excessive frontier expansion");
            assert!(
                error
                    .to_string()
                    .contains("frontier expansion budget exhausted"),
                "{error:#}"
            );
        }
    }

    #[test]
    fn compact_json_keeps_the_amplifying_graph_without_expanding_impact() {
        const RUN: &str = "20261109T000000000Z-0123456789abcdef";
        let roots = 1024;
        let chain = 1025;
        for current in [false, true] {
            let log = shared_chain_log(roots, chain, current);
            let context = analyze_with_impact(Cursor::new(log.as_bytes()), RUN, false).unwrap();
            assert!(
                context
                    .root_rebuilds
                    .iter()
                    .all(|root| root.affected_units.is_empty())
            );
            let report = serde_json::to_value(json_report(&context, RUN)).unwrap();
            assert_eq!(report["registered_units"], roots + chain);
            assert_eq!(report["classified_units"], roots + chain);
            assert_eq!(report["unclassified_units"], 0);
            let units = report["units"].as_array().unwrap();
            let edge_count: usize = units
                .iter()
                .map(|unit| unit["dependencies"].as_array().unwrap().len())
                .sum();
            assert_eq!(edge_count, roots + chain - 1);
            let frontiers = report["non_cached_dependency_frontier_roots"]
                .as_array()
                .unwrap();
            assert_eq!(frontiers.len(), roots);
            assert_eq!(frontiers.first().unwrap(), 0);
            assert_eq!(frontiers.last().unwrap(), roots - 1);
        }
    }
}

#[cfg(test)]
// Trust: reports preserve every typed dependency-cache cause and its actual path.
mod dep_info_diagnostic_tests {
    use super::*;
    use crate::compiler::fingerprint::DepInfoUnavailable;

    #[test]
    fn dependency_cache_reasons_keep_paths_and_display_causes() {
        let root = std::path::PathBuf::from("workspace");
        let relative = std::path::PathBuf::from("target/debug/fingerprint/dep-bin-foo");
        let units = HashMap::default();
        for reason in [
            DepInfoUnavailable::Missing,
            DepInfoUnavailable::Unreadable,
            DepInfoUnavailable::Malformed,
            DepInfoUnavailable::FormatMismatch {
                recorded: 2,
                current: 3,
            },
            DepInfoUnavailable::RelocationRootUnavailable,
            DepInfoUnavailable::FilenameInventoryIncomplete,
        ] {
            for (path, displayed) in [
                (root.join(&relative), relative.clone()),
                (
                    std::path::PathBuf::from("outside/dep-info"),
                    "outside/dep-info".into(),
                ),
            ] {
                let diagnostic = format_dirty_reason(
                    &DirtyReason::FsStatusOutdated(FsStatus::StaleItem(
                        StaleItem::DepInfoUnavailable {
                            path,
                            reason: reason.clone(),
                        },
                    )),
                    &units,
                    &root,
                );
                assert_eq!(
                    diagnostic,
                    format!("dependency cache `{}`: {reason}", displayed.display())
                );
            }
        }
    }
}

#[cfg(test)]
// Trust: malformed evidence cannot become partial successful rebuild summaries.
mod strict_log_tests {
    use super::*;
    use crate::compiler::fingerprint::DepInfoUnavailable;
    use serde_json::{Value, json};
    use std::io::Cursor;

    const RUN: &str = "20261106T010203004Z-0123456789abcdef";

    fn base(current: bool) -> Vec<Value> {
        let workspace = std::env::current_dir().unwrap();
        let mut records = Vec::new();
        if current {
            records.push(json!({"reason":"input-work-enabled","version":INPUT_WORK_VERSION}));
        }
        records.extend([
            json!({"reason":"build-started","command":[],"cwd":workspace,"host":"host","jobs":1,
                "num_cpus":null,"profile":"dev","rustc_version":"test","rustc_version_verbose":"test",
                "target_dir":workspace.join("target"),"workspace_root":workspace}),
            json!({"reason":"unit-registered","index":0,"package_id":"sample@0.1.0",
                "target":{"name":"sample","kind":"lib"},"mode":"build","platform":"host"}),
            json!({"reason":"unit-graph-finished","elapsed":0.0}),
        ]);
        records
    }

    fn dirty() -> DirtyReason {
        DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::DepInfoUnavailable {
            path: "target/fingerprint/dep-lib-sample".into(),
            reason: DepInfoUnavailable::FormatMismatch {
                recorded: 2,
                current: 3,
            },
        }))
    }

    fn fingerprint(status: &str, cause: Option<DirtyReason>, recheck: bool) -> Value {
        let mut value = json!({"reason":"unit-fingerprint","index":0,"status":status});
        if let Some(cause) = cause {
            value["cause"] = serde_json::to_value(cause).unwrap();
        }
        if recheck {
            value["recheck"] = json!(true);
        }
        value
    }

    fn execution() -> Value {
        json!({"reason":"execution-enabled","version":EXECUTION_VERSION})
    }

    fn dispatch(fresh: bool) -> Value {
        json!({"reason":"unit-scheduled","index":0,"elapsed":0.0,"fresh":fresh})
    }

    fn outcome() -> Value {
        json!({"reason":"unit-outcome","index":0,"elapsed":1.0,"outcome":"succeeded"})
    }

    fn finished() -> Value {
        json!({"reason":"unit-finished","index":0,"elapsed":1.0})
    }

    fn terminal() -> Value {
        json!({"reason":"execution-graph-finished","elapsed":1.0,"outcome":"succeeded",
            "scheduled":1,"completed":1,"not_executed":0})
    }

    fn close() -> Value {
        json!({"reason":"input-work-closed","version":INPUT_WORK_VERSION,"started":0,"finished":0})
    }

    fn finalize() -> Value {
        json!({"reason":"input-work-finalized","captures":0})
    }

    fn frames(values: Vec<Value>) -> String {
        values
            .into_iter()
            .map(|mut value| {
                value["run_id"] = json!(RUN);
                value["timestamp"] = json!("2026-11-06T01:02:03Z");
                format!("{value}\n")
            })
            .collect()
    }

    fn parse(values: Vec<Value>) -> CargoResult<Context> {
        analyze(Cursor::new(frames(values)), RUN)
    }

    fn json_context(values: Vec<Value>) -> CargoResult<Context> {
        analyze_with_impact(Cursor::new(frames(values)), RUN, false)
    }

    fn json_value(values: Vec<Value>) -> CargoResult<Value> {
        let context = json_context(values)?;
        Ok(serde_json::to_value(json_report(&context, RUN))?)
    }

    fn registered(index: u32, name: &str, kind: &str, dependencies: &[u32]) -> Value {
        json!({"reason":"unit-registered","index":index,"package_id":"sample@0.1.0",
            "target":{"name":name,"kind":kind},"mode":"build","platform":"host",
            "features":["z","a"],"requested":true,"dependencies":dependencies})
    }

    fn fingerprint_at(index: u32, status: &str, cause: Option<DirtyReason>) -> Value {
        let mut value = fingerprint(status, cause, false);
        value["index"] = json!(index);
        value
    }

    #[test]
    fn json_keeps_exact_units_and_observed_classifications_without_expanded_impact() {
        let mut values = base(true);
        values.insert(3, registered(2, "sample-bin", "bin", &[1, 0]));
        values.insert(4, registered(1, "dependency", "lib", &[]));
        values.extend([
            fingerprint_at(2, "dirty", Some(DirtyReason::Forced)),
            fingerprint_at(1, "fresh", None),
            fingerprint_at(0, "new", None),
            finalize(),
            close(),
        ]);
        let context = json_context(values).unwrap();
        assert_eq!(context.root_rebuilds.len(), 1);
        assert!(context.root_rebuilds[0].affected_units.is_empty());
        let report = serde_json::to_value(json_report(&context, RUN)).unwrap();
        assert_eq!(report["schema"], "targo-rebuilds-v1");
        assert_eq!(report["run_id"], RUN);
        assert_eq!(report["scope"], "observed-fingerprint-classifications");
        assert_eq!(report["stream_completeness"], "complete");
        assert_eq!(report["input_accounting"], "finalized");
        assert_eq!(report["registered_units"], 3);
        assert_eq!(report["classified_units"], 3);
        assert_eq!(report["unclassified_units"], 0);
        assert_eq!(
            report["observed_counts"],
            json!({"cached":1,"dirty":1,"new":1})
        );
        assert_eq!(report["non_cached_dependency_frontier_roots"], json!([0]));
        let rows = report["units"].as_array().unwrap();
        assert_eq!(
            rows.iter()
                .map(|row| row["index"].clone())
                .collect::<Vec<_>>(),
            vec![json!(0), json!(1), json!(2)]
        );
        assert_eq!(rows[0]["package_id"], rows[2]["package_id"]);
        assert_ne!(rows[0]["target"], rows[2]["target"]);
        assert_eq!(rows[2]["target"], json!({"name":"sample-bin","kind":"bin"}));
        assert_eq!(rows[2]["mode"], "build");
        assert_eq!(rows[2]["platform"], "host");
        assert_eq!(rows[2]["features"], json!(["a", "z"]));
        assert_eq!(rows[2]["requested"], true);
        assert_eq!(rows[2]["dependencies"], json!([0, 1]));
        assert_eq!(
            rows[0]["fingerprint"],
            json!({"status":"new","reason":null,"rechecked":false})
        );
        assert_eq!(
            rows[1]["fingerprint"],
            json!({"status":"fresh","reason":null,"rechecked":false})
        );
        assert_eq!(
            rows[2]["fingerprint"],
            json!({"status":"dirty","reason":"forced","rechecked":false})
        );
    }

    #[test]
    fn json_post_lock_recheck_replaces_classification_without_adding_a_unit() {
        let mut values = base(true);
        values.extend([
            fingerprint("dirty", Some(dirty()), false),
            execution(),
            dispatch(false),
            fingerprint("fresh", None, true),
            finished(),
            outcome(),
            terminal(),
            finalize(),
            close(),
        ]);
        let report = json_value(values).unwrap();
        assert_eq!(report["registered_units"], 1);
        assert_eq!(report["classified_units"], 1);
        assert_eq!(
            report["observed_counts"],
            json!({"cached":1,"dirty":0,"new":0})
        );
        assert_eq!(
            report["units"][0]["fingerprint"],
            json!({"status":"fresh","reason":null,"rechecked":true})
        );
        assert_eq!(report["non_cached_dependency_frontier_roots"], json!([]));
    }

    #[test]
    fn json_keeps_legacy_and_missing_classification_explicit() {
        let mut legacy = base(false);
        legacy.push(fingerprint("fresh", None, false));
        let report = json_value(legacy).unwrap();
        assert_eq!(report["stream_completeness"], "unavailable");
        assert_eq!(report["input_accounting"], "unavailable");

        let mut missing = base(true);
        missing.extend([finalize(), close()]);
        let report = json_value(missing).unwrap();
        assert_eq!(report["stream_completeness"], "complete");
        assert_eq!(report["input_accounting"], "finalized");
        assert_eq!(report["registered_units"], 1);
        assert_eq!(report["classified_units"], 0);
        assert_eq!(report["unclassified_units"], 1);
        assert_eq!(
            report["observed_counts"],
            json!({"cached":0,"dirty":0,"new":0})
        );
        assert!(report["units"][0]["fingerprint"].is_null());

        let mut failed = base(true);
        let mut end = terminal();
        end["outcome"] = json!("failed");
        let mut failed_outcome = outcome();
        failed_outcome["outcome"] = json!("failed");
        failed.extend([
            fingerprint("dirty", Some(dirty()), false),
            execution(),
            dispatch(false),
            failed_outcome,
            end,
            close(),
        ]);
        let report = json_value(failed).unwrap();
        assert_eq!(report["stream_completeness"], "complete");
        assert_eq!(report["input_accounting"], "unavailable");
    }

    #[test]
    fn json_order_is_independent_of_registration_and_hash_map_order() {
        let make = |indices: &[u32]| {
            let mut values = base(true);
            values.remove(2);
            for &index in indices.iter().rev() {
                values.insert(2, registered(index, &format!("target-{index}"), "lib", &[]));
            }
            for &index in indices {
                values.push(fingerprint_at(index, "new", None));
            }
            values.extend([finalize(), close()]);
            values
        };
        let first = json_value(make(&[7, 0, 2])).unwrap();
        let second = json_value(make(&[2, 7, 0])).unwrap();
        assert_eq!(first, second);
        assert_eq!(
            first["non_cached_dependency_frontier_roots"],
            json!([0, 2, 7])
        );
    }

    #[test]
    fn json_categories_omit_raw_environment_flags_paths_and_diagnostic_values() {
        const PRIVATE: &str = "PRIVATE_REBUILDS_JSON_SENTINEL";
        for (reason, category) in [
            (
                DirtyReason::EnvVarChanged {
                    name: PRIVATE.into(),
                    old_value: Some(PRIVATE.into()),
                    new_value: Some(PRIVATE.into()),
                },
                "env-var-changed",
            ),
            (
                DirtyReason::RustflagsChanged {
                    old: vec![PRIVATE.into()],
                    new: vec![PRIVATE.into()],
                },
                "rustflags-changed",
            ),
            (
                DirtyReason::PrecalculatedComponentsChanged {
                    old: PRIVATE.into(),
                    new: PRIVATE.into(),
                },
                "precalculated-components-changed",
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::ChangedEnv {
                    var: PRIVATE.into(),
                    previous: Some(PRIVATE.into()),
                    current: Some(PRIVATE.into()),
                })),
                "changed-env",
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::OutputIntegrity {
                    path: PRIVATE.into(),
                    reason: PRIVATE.into(),
                })),
                "output-integrity",
            ),
        ] {
            let mut values = base(true);
            values.extend([
                fingerprint("dirty", Some(reason), false),
                finalize(),
                close(),
            ]);
            let report = json_value(values).unwrap();
            assert_eq!(report["units"][0]["fingerprint"]["reason"], category);
            assert!(!report.to_string().contains(PRIVATE));
        }
    }

    #[test]
    fn json_path_retains_existing_strict_reader_refusals() {
        for events in [
            vec![fingerprint_at(99, "fresh", None)],
            vec![fingerprint("dirty", None, false)],
            vec![
                fingerprint("fresh", None, false),
                fingerprint("fresh", None, false),
            ],
            vec![fingerprint("fresh", None, true)],
            vec![
                fingerprint("fresh", None, false),
                finalize(),
                close(),
                fingerprint("fresh", None, false),
            ],
        ] {
            let mut values = base(true);
            values.extend(events);
            values.extend([finalize(), close()]);
            assert!(json_context(values).is_err());
        }
        assert!(json_context(base(true)).is_err());
    }

    #[test]
    fn complete_current_log_preserves_typed_rebuild_cause() {
        let mut values = base(true);
        values.extend([
            fingerprint("dirty", Some(dirty()), false),
            execution(),
            dispatch(false),
            finished(),
            outcome(),
            terminal(),
            finalize(),
            close(),
        ]);
        let context = parse(values).unwrap();
        assert!(context.stream_complete);
        assert!(!context.input_accounting_unavailable);
        assert_eq!(
            (
                context.total_cached,
                context.total_new,
                context.total_rebuilt
            ),
            (0, 0, 1)
        );
        assert_eq!(context.root_rebuilds.len(), 1);
        assert_eq!(
            serde_json::to_value(&context.root_rebuilds[0].reason).unwrap(),
            serde_json::to_value(dirty()).unwrap()
        );
    }

    #[test]
    fn module_candidate_rebuild_explains_presence_and_unavailable_observations() {
        for (previous, current, expected) in [
            (Some(false), Some(true), "absent -> present"),
            (Some(true), Some(false), "present -> absent"),
            (None, Some(false), "unavailable -> absent"),
            (Some(false), None, "absent -> unavailable"),
        ] {
            let cause = DirtyReason::FsStatusOutdated(FsStatus::StaleItem(
                StaleItem::ModuleCandidateChanged {
                    path: "/workspace/src/foo/mod.rs".into(),
                    previous,
                    current,
                },
            ));
            let explanation =
                format_dirty_reason(&cause, &HashMap::default(), Path::new("/workspace"));
            assert_eq!(
                explanation,
                format!("Rust module candidate changed: src/foo/mod.rs ({expected})")
            );
        }
    }

    // Trust: rebuild reports must preserve the input/output distinction.
    #[test]
    fn build_script_inputs_unavailable_report_names_only_an_output_anchor() {
        let cause = DirtyReason::FsStatusOutdated(FsStatus::StaleItem(
            StaleItem::BuildScriptInputsUnavailable {
                output_anchor: "/workspace/build/script/run/stdout".into(),
            },
        ));
        assert_eq!(
            format_dirty_reason(&cause, &HashMap::default(), Path::new("/workspace")),
            "build-script input observation unavailable or invalid (output anchor build/script/run/stdout)"
        );
    }

    #[test]
    fn legacy_log_keeps_observations_without_claiming_terminal_completeness() {
        let mut values = base(false);
        values.push(fingerprint("fresh", None, false));
        let context = parse(values).unwrap();
        assert!(!context.stream_complete);
        assert!(!context.input_accounting_unavailable);
        assert_eq!(
            (
                context.total_cached,
                context.total_new,
                context.total_rebuilt
            ),
            (1, 0, 0)
        );
        assert!(context.root_rebuilds.is_empty());
    }

    #[test]
    fn duplicate_unknown_and_contradictory_fingerprints_are_rejected() {
        let mut unknown = fingerprint("fresh", None, false);
        unknown["index"] = json!(99);
        for events in [
            vec![unknown],
            vec![
                fingerprint("fresh", None, false),
                fingerprint("fresh", None, false),
            ],
            vec![fingerprint("dirty", None, false)],
            vec![fingerprint("fresh", Some(dirty()), false)],
            vec![fingerprint("new", Some(dirty()), false)],
            vec![fingerprint("dirty", Some(DirtyReason::FreshBuild), false)],
        ] {
            let mut values = base(true);
            values.extend(events);
            values.extend([finalize(), close()]);
            assert!(parse(values).is_err());
        }
        let mut duplicate = base(true);
        duplicate.insert(3, duplicate[2].clone());
        duplicate.extend([finalize(), close()]);
        assert!(parse(duplicate).is_err());
        let mut unknown_dependency = base(true);
        unknown_dependency[2]["dependencies"] = json!([99]);
        unknown_dependency.extend([finalize(), close()]);
        assert!(parse(unknown_dependency).is_err());
    }

    #[test]
    fn current_logs_require_supported_final_closure() {
        let mut missing = base(true);
        missing.push(fingerprint("fresh", None, false));
        assert!(parse(missing).is_err());
        for events in [
            vec![finalize(), close(), fingerprint("fresh", None, false)],
            vec![execution(), dispatch(false), finalize(), close()],
            vec![execution(), terminal(), terminal(), finalize(), close()],
            vec![close()],
            vec![finalize(), finalize(), close()],
        ] {
            let mut values = base(true);
            values.extend(events);
            assert!(parse(values).is_err());
        }
        let mut bad_counts = base(true);
        let mut end = close();
        end["started"] = json!(1);
        bad_counts.extend([finalize(), end]);
        assert!(parse(bad_counts).is_err());
        let mut bad_version = base(true);
        let mut end = close();
        end["version"] = json!(INPUT_WORK_VERSION + 1);
        bad_version.extend([finalize(), end]);
        assert!(parse(bad_version).is_err());
    }

    #[test]
    fn one_marked_post_lock_recheck_replaces_instead_of_double_counting() {
        for initial in ["new", "dirty"] {
            for final_status in ["fresh", "new", "dirty"] {
                let final_cause = (final_status == "dirty").then(|| {
                    DirtyReason::FsStatusOutdated(FsStatus::StaleItem(
                        StaleItem::DepInfoUnavailable {
                            path: "target/fingerprint/dep-lib-sample".into(),
                            reason: DepInfoUnavailable::Unreadable,
                        },
                    ))
                });
                let mut values = base(true);
                values.extend([
                    fingerprint(initial, (initial == "dirty").then(dirty), false),
                    execution(),
                    dispatch(false),
                    fingerprint(final_status, final_cause.clone(), true),
                    finished(),
                    outcome(),
                    terminal(),
                    finalize(),
                    close(),
                ]);
                let context = parse(values).unwrap();
                assert_eq!(
                    context.total_cached + context.total_new + context.total_rebuilt,
                    1
                );
                assert_eq!(context.total_cached, usize::from(final_status == "fresh"));
                assert_eq!(context.total_new, usize::from(final_status == "new"));
                assert_eq!(context.total_rebuilt, usize::from(final_status == "dirty"));
                if final_status == "dirty" {
                    assert_eq!(
                        serde_json::to_value(&context.root_rebuilds[0].reason).unwrap(),
                        serde_json::to_value(final_cause.unwrap()).unwrap()
                    );
                }
            }
        }
    }

    #[test]
    fn rechecks_need_one_dirty_dispatch_before_actual_completion() {
        for events in [
            vec![fingerprint("fresh", None, true)],
            vec![
                fingerprint("dirty", Some(dirty()), false),
                fingerprint("fresh", None, true),
            ],
            vec![
                fingerprint("fresh", None, false),
                execution(),
                dispatch(true),
                fingerprint("fresh", None, true),
            ],
            vec![
                fingerprint("dirty", Some(dirty()), false),
                execution(),
                dispatch(true),
                fingerprint("fresh", None, true),
            ],
            vec![
                fingerprint("dirty", Some(dirty()), false),
                execution(),
                dispatch(false),
                fingerprint("dirty", Some(dirty()), true),
                fingerprint("fresh", None, true),
            ],
            vec![
                fingerprint("dirty", Some(dirty()), false),
                execution(),
                dispatch(false),
                outcome(),
                fingerprint("fresh", None, true),
            ],
            vec![
                fingerprint("dirty", Some(dirty()), false),
                execution(),
                dispatch(false),
                finished(),
                fingerprint("fresh", None, true),
            ],
            vec![
                fingerprint("dirty", Some(dirty()), false),
                execution(),
                dispatch(false),
                fingerprint("fresh", None, false),
            ],
        ] {
            let mut values = base(true);
            values.extend(events);
            values.extend([terminal(), finalize(), close()]);
            assert!(parse(values).is_err());
        }
    }

    #[test]
    fn checked_file_reader_binds_selected_run_and_recorded_workspace() {
        let directory = tempfile::tempdir().unwrap();
        let workspace = directory.path().canonicalize().unwrap();
        let file = workspace.join("analysis.jsonl");
        let mut values = base(true);
        values[1]["workspace_root"] = json!(workspace);
        values.extend([fingerprint("fresh", None, false), finalize(), close()]);
        std::fs::write(&file, frames(values)).unwrap();
        let other = tempfile::tempdir().unwrap();
        for include_expanded_impact in [true, false] {
            let context = prepare_context(&file, RUN, include_expanded_impact).unwrap();
            require_workspace(Some(&context.workspace_root), &workspace).unwrap();
            assert!(require_workspace(Some(&context.workspace_root), other.path()).is_err());
            assert!(prepare_context(&file, "another-run", include_expanded_impact).is_err());
        }
        let mut bytes = std::fs::read(&file).unwrap();
        assert_eq!(bytes.pop(), Some(b'\n'));
        std::fs::write(&file, bytes).unwrap();
        for include_expanded_impact in [true, false] {
            assert!(prepare_context(&file, RUN, include_expanded_impact).is_err());
        }
    }

    #[test]
    fn scheduled_compilation_needs_a_fingerprint_but_doctest_jobs_do_not() {
        for fresh in [false, true] {
            let mut values = base(true);
            values.extend([
                execution(),
                dispatch(fresh),
                outcome(),
                terminal(),
                finalize(),
                close(),
            ]);
            assert!(parse(values.clone()).is_err());
            // Both no-op legacy doctests and the authenticated census bypass
            // prepare_target; the latter deliberately uses a dirty job.
            values[2]["mode"] = json!("doctest");
            let context = parse(values).unwrap();
            assert_eq!(
                context.total_cached + context.total_new + context.total_rebuilt,
                0
            );
        }
    }

    #[test]
    fn execution_census_and_finalization_must_match_observed_population() {
        for (field, value) in [("scheduled", 2), ("completed", 0), ("not_executed", 1)] {
            let mut values = base(true);
            let mut end = terminal();
            end[field] = json!(value);
            values.extend([
                fingerprint("fresh", None, false),
                execution(),
                dispatch(true),
                outcome(),
                end,
                finalize(),
                close(),
            ]);
            assert!(parse(values).is_err(), "accepted wrong {field}");
        }
        let mut values = base(true);
        let mut failed = outcome();
        failed["outcome"] = json!("failed");
        values.extend([
            fingerprint("fresh", None, false),
            execution(),
            dispatch(true),
            failed,
            terminal(),
            finalize(),
            close(),
        ]);
        assert!(parse(values).is_err());

        let mut values = base(true);
        let mut finalization = finalize();
        finalization["captures"] = json!(1);
        values.extend([fingerprint("fresh", None, false), finalization, close()]);
        assert!(parse(values).is_err());
    }

    #[test]
    fn unsuccessful_execution_preserves_closed_stream_without_input_accounting() {
        for outcome_name in ["failed", "cancelled"] {
            let mut unit_end = outcome();
            unit_end["outcome"] = json!(outcome_name);
            let mut graph_end = terminal();
            graph_end["outcome"] = json!(outcome_name);
            let mut values = base(true);
            values.extend([
                fingerprint("dirty", Some(dirty()), false),
                execution(),
                dispatch(false),
                unit_end,
                graph_end,
            ]);
            let mut without_finalization = values.clone();
            without_finalization.push(close());
            let context = parse(without_finalization).unwrap();
            assert!(context.stream_complete);
            assert!(context.input_accounting_unavailable);
            assert_eq!(context.total_rebuilt, 1);

            let mut wrong = finalize();
            wrong["captures"] = json!(1);
            values.extend([wrong, close()]);
            assert!(parse(values).is_err());
        }
        let mut success = base(true);
        success.extend([
            fingerprint("fresh", None, false),
            execution(),
            dispatch(true),
            outcome(),
            terminal(),
            close(),
        ]);
        assert!(parse(success).is_err());
    }
}
