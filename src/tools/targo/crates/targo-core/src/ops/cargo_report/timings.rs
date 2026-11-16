//! The `cargo report timings` command.

use crate::util::data_structures::HashSet;
use std::path::PathBuf;

use crate::util::data_structures::IndexMap;
use anyhow::Context as _;
use cargo_util::paths;
use cargo_util_terminal::report::Level;
use indexmap::map::Entry;
use itertools::Itertools as _;
use tempfile::TempDir;

use crate::AlreadyPrintedError;
use crate::CargoResult;
use crate::GlobalContext;
use crate::compiler::UnitIndex;
use crate::compiler::timings::CompilationSection;
use crate::compiler::timings::report::RenderContext;
use crate::compiler::timings::report::aggregate_sections;
use crate::compiler::timings::report::compute_concurrency;
use crate::compiler::timings::report::round_to_centisecond;
use crate::compiler::timings::report::write_html;
use crate::compiler::timings::{UnitCpuTimes, UnitData};
use crate::ops::cargo_report::log_reader::{MAX_UNITS, read_checked, records, require_workspace};
use crate::ops::cargo_report::util::find_log_file;
use crate::ops::cargo_report::util::unit_target_description;
use crate::util::log_message::LogMessage;
use crate::util::log_message::Target;
use crate::util::log_message::{EXECUTION_VERSION, FingerprintStatus, INPUT_WORK_VERSION};
use crate::util::logger::RunId;
use crate::util::style;
use crate::workspace::Workspace;

pub struct ReportTimingsOptions<'gctx> {
    /// Whether to attempt to open the browser after the report is generated
    pub open_result: bool,
    pub gctx: &'gctx GlobalContext,
    pub id: Option<RunId>,
}

/// Collects sections data for later post-processing through [`aggregate_sections`].
struct UnitEntry {
    target: Target,
    data: UnitData,
    sections: IndexMap<String, CompilationSection>,
    rmeta_time: Option<f64>,
    /// Whether the job queue actually ran this unit.
    started: bool,
    finished: bool,
    last_elapsed: f64,
    requires_fingerprint: bool,
}

// Trust: a post-lock observation replaces one unit's classification; it is
// never another compiled unit or an inferred recheck in a legacy log.
struct FingerprintEntry {
    status: FingerprintStatus,
    rechecked: bool,
}

// Trust: the original workspace and stream closure travel with the one-pass
// timing analysis. A closed diagnostic stream says nothing about build success.
pub(crate) struct PreparedTimings<'a> {
    pub(crate) render: RenderContext<'a>,
    workspace_root: Option<PathBuf>,
    stream_complete: bool,
}

pub fn report_timings(
    gctx: &GlobalContext,
    ws: Option<&Workspace<'_>>,
    opts: ReportTimingsOptions<'_>,
) -> CargoResult<()> {
    let search_workspace = if opts.id.is_some() { None } else { ws };
    let Some((log, run_id)) = find_log_file(gctx, search_workspace, opts.id.as_ref())? else {
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

    let prepared = read_checked(&log, |reader| {
        prepare_context(records(reader, &run_id.to_string()), &run_id, true)
    })
    .with_context(|| format!("failed to analyze log at `{}`", log.display()))?;
    if let Some(ws) = ws {
        require_workspace(prepared.workspace_root.as_deref(), ws.root())?;
    }
    if !prepared.stream_complete {
        gctx.shell().warn(
            "legacy timing log has no terminal stream closure; timing data may be incomplete",
        )?;
    }

    // If we are in a workspace,
    // put timing reports in <target-dir>/cargo-timings/` as usual for easy access.
    // Otherwise in a temporary directory
    let reports_dir = if let Some(ws) = ws {
        let target_dir = ws.target_dir();
        let target_dir = target_dir.as_path_unlocked();
        paths::create_dir_all_excluded_from_backups_atomic(target_dir)?;
        let timings_dir = target_dir.join("cargo-timings");
        paths::create_dir_all(&timings_dir)?;
        timings_dir
    } else if let Ok(path) = gctx.get_env("__CARGO_TEST_REPORT_TIMINGS_TEMPDIR") {
        PathBuf::from(path.to_owned())
    } else {
        TempDir::with_prefix("cargo-timings-")?.keep()
    };

    let timing_path = reports_dir.join(format!("cargo-timing-{run_id}.html"));

    let mut out_file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&timing_path)
        .with_context(|| format!("failed to open `{}`", timing_path.display()))?;

    write_html(prepared.render, &mut out_file)?;

    let link = gctx.shell().err_file_hyperlink(&timing_path);
    let msg = format!("report saved to {link}{}{link:#}", timing_path.display());
    gctx.shell()
        .status_with_color("Timing", msg, &style::NOTE)?;

    if opts.open_result {
        crate::util::open::open(&timing_path, gctx)?;
    }

    Ok(())
}

pub(crate) fn prepare_context<I>(
    log: I,
    run_id: &RunId,
    recorded: bool,
) -> CargoResult<PreparedTimings<'_>>
where
    I: Iterator<Item = CargoResult<LogMessage>>,
{
    let mut ctx = RenderContext {
        start_str: run_id.timestamp().to_string(),
        root_units: Default::default(),
        profile: Default::default(),
        total_fresh: Default::default(),
        total_dirty: Default::default(),
        unit_data: Default::default(),
        concurrency: Default::default(),
        cpu_usage: Default::default(),
        rustc_version: Default::default(),
        host: Default::default(),
        requested_targets: Default::default(),
        jobs: 0,
        num_cpus: None,
        error: &None,
    };
    let mut units: IndexMap<UnitIndex, UnitEntry> = IndexMap::default();
    let mut fingerprints: IndexMap<UnitIndex, FingerprintEntry> = IndexMap::default();

    let mut platform_targets = HashSet::default();

    let mut requested_units: HashSet<UnitIndex> = HashSet::default();
    let mut workspace_root = None;
    let mut input_enabled = false;
    let mut closed = false;
    let mut record_count = 0usize;
    let mut captures_started = 0u64;
    let mut captures_finished = 0u64;
    let mut graph_finished = false;
    let mut execution_enabled = false;
    let mut execution_finished = false;
    let mut scheduled = HashSet::default();

    for msg in log {
        let msg = msg?;
        if recorded && closed {
            anyhow::bail!("data after terminal timing log record");
        }
        if recorded
            && workspace_root.is_none()
            && !matches!(
                &msg,
                LogMessage::InputWorkEnabled { .. } | LogMessage::BuildStarted { .. }
            )
        {
            anyhow::bail!("timing log lacks its original build-started record");
        }
        if recorded {
            if let LogMessage::UnitRmetaFinished { unblocked, .. }
            | LogMessage::UnitFinished { unblocked, .. } = &msg
            {
                if unblocked.iter().any(|index| !units.contains_key(index)) {
                    anyhow::bail!("timing completion references an unregistered unit");
                }
            }
            match &msg {
                LogMessage::UnitStarted { index, elapsed } => {
                    let unit = units
                        .get_mut(index)
                        .context("timing start references an unregistered unit")?;
                    if !graph_finished
                        || unit.started
                        || !elapsed.is_finite()
                        || *elapsed < 0.0
                        || (unit.requires_fingerprint && !fingerprints.contains_key(index))
                    {
                        anyhow::bail!("duplicate or invalid timing start");
                    }
                    unit.last_elapsed = *elapsed;
                }
                LogMessage::UnitRmetaFinished { index, elapsed, .. }
                | LogMessage::UnitSectionStarted { index, elapsed, .. }
                | LogMessage::UnitSectionFinished { index, elapsed, .. }
                | LogMessage::UnitFinished { index, elapsed, .. } => {
                    let unit = units
                        .get_mut(index)
                        .context("timing detail references an unregistered unit")?;
                    if !unit.started
                        || unit.finished
                        || !elapsed.is_finite()
                        || *elapsed < unit.last_elapsed
                    {
                        anyhow::bail!("timing detail is outside its unit's active interval");
                    }
                    if matches!(&msg, LogMessage::UnitRmetaFinished { .. })
                        && unit.rmeta_time.is_some()
                    {
                        anyhow::bail!("duplicate timing metadata completion");
                    }
                    if let LogMessage::UnitSectionFinished { section, .. } = &msg {
                        if !unit.sections.contains_key(section) {
                            anyhow::bail!("timing section completion lacks its start");
                        }
                    }
                    unit.last_elapsed = *elapsed;
                }
                LogMessage::UnitPeakMemory { index, .. }
                | LogMessage::UnitCpuTimes { index, .. } => {
                    let unit = units
                        .get(index)
                        .context("timing memory event references an unregistered unit")?;
                    if !unit.started || unit.finished {
                        anyhow::bail!("timing memory event is outside its unit's active interval");
                    }
                }
                _ => {}
            }
        }
        match msg {
            LogMessage::InputWorkEnabled { version } => {
                if recorded {
                    if record_count != 0 || input_enabled || version != INPUT_WORK_VERSION {
                        anyhow::bail!("unsupported or misplaced timing log schema");
                    }
                    input_enabled = true;
                }
            }
            LogMessage::BuildStarted {
                command: _,
                cwd: _,
                host,
                jobs,
                num_cpus,
                profile,
                rustc_version,
                rustc_version_verbose,
                target_dir: _,
                workspace_root: root,
            } => {
                if recorded
                    && (workspace_root.is_some() || !units.is_empty() || !root.is_absolute())
                {
                    anyhow::bail!("duplicate, late, or invalid timing workspace record");
                }
                workspace_root = Some(root);
                let rustc_version = rustc_version_verbose
                    .lines()
                    .next()
                    .map(ToOwned::to_owned)
                    .unwrap_or(rustc_version);
                ctx.host = host;
                ctx.jobs = jobs;
                ctx.num_cpus = num_cpus;
                ctx.profile = profile;
                ctx.rustc_version = rustc_version;
            }
            LogMessage::UnitRegistered {
                package_id,
                target,
                mode,
                platform,
                index,
                features,
                requested,
                dependencies: _,
            } => {
                if recorded
                    && (graph_finished || units.len() >= MAX_UNITS || units.contains_key(&index))
                {
                    anyhow::bail!("duplicate or late timing unit registration");
                }
                if requested {
                    requested_units.insert(index);
                }
                platform_targets.insert(platform);

                let version = package_id
                    .version()
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| "N/A".into());

                let target_str = unit_target_description(&target, mode);

                let mode_str = if mode.is_run_custom_build() {
                    "run-custom-build"
                } else {
                    "todo"
                };

                let data = UnitData {
                    i: index,
                    name: package_id.name().to_string(),
                    version,
                    mode: mode_str.to_owned(),
                    target: target_str,
                    features,
                    start: 0.0,
                    duration: 0.0,
                    peak_memory: None,
                    cpu_times: None,
                    unblocked_units: Vec::new(),
                    unblocked_rmeta_units: Vec::new(),
                    sections: None,
                };

                units.insert(
                    index,
                    UnitEntry {
                        target,
                        data,
                        sections: IndexMap::default(),
                        rmeta_time: None,
                        started: false,
                        finished: false,
                        last_elapsed: 0.0,
                        requires_fingerprint: !mode.is_doc_test(),
                    },
                );
            }
            LogMessage::UnitFingerprint {
                index,
                status,
                cause,
                recheck,
            } => {
                let unit = units
                    .get(&index)
                    .context("timing fingerprint references an unregistered unit")?;
                if unit.started {
                    anyhow::bail!("timing fingerprint follows the unit's execution");
                }
                match (&status, &cause) {
                    (FingerprintStatus::Dirty, Some(reason)) if !reason.is_fresh_build() => {}
                    (FingerprintStatus::Fresh | FingerprintStatus::New, None) => {}
                    _ => anyhow::bail!("timing fingerprint status contradicts its cause"),
                }
                if recheck {
                    let previous = fingerprints
                        .get_mut(&index)
                        .context("timing recheck lacks an initial fingerprint")?;
                    if previous.rechecked || matches!(&previous.status, FingerprintStatus::Fresh) {
                        anyhow::bail!("duplicate or invalid timing fingerprint recheck");
                    }
                    previous.status = status;
                    previous.rechecked = true;
                } else if fingerprints
                    .insert(
                        index,
                        FingerprintEntry {
                            status,
                            rechecked: false,
                        },
                    )
                    .is_some()
                {
                    anyhow::bail!("duplicate initial timing fingerprint");
                }
            }
            LogMessage::UnitStarted { index, elapsed } => {
                units
                    .entry(index)
                    .and_modify(|unit| {
                        unit.data.start = elapsed;
                        unit.started = true;
                    })
                    .or_insert_with(|| {
                        unreachable!("unit {index} must have been registered first")
                    });
            }
            LogMessage::UnitRmetaFinished {
                index,
                elapsed,
                unblocked,
            } => match units.entry(index) {
                Entry::Occupied(mut e) => {
                    let elapsed = f64::max(elapsed - e.get().data.start, 0.0);
                    e.get_mut().data.unblocked_rmeta_units = unblocked;
                    e.get_mut().data.duration = elapsed;
                    e.get_mut().rmeta_time = Some(elapsed);
                }
                Entry::Vacant(_) => {
                    tracing::warn!(
                        "section `frontend` ended, but unit {index} has no start recorded"
                    )
                }
            },
            LogMessage::UnitSectionStarted {
                index,
                elapsed,
                section,
            } => match units.entry(index) {
                Entry::Occupied(mut e) => {
                    let elapsed = f64::max(elapsed - e.get().data.start, 0.0);
                    if e.get_mut()
                        .sections
                        .insert(
                            section.clone(),
                            CompilationSection {
                                start: elapsed,
                                end: None,
                            },
                        )
                        .is_some()
                    {
                        tracing::warn!(
                            "section `{section}` for unit {index} started more than once",
                        );
                    }
                }
                Entry::Vacant(_) => {
                    tracing::warn!(
                        "section `{section}` started, but unit {index} has no start recorded"
                    )
                }
            },
            LogMessage::UnitSectionFinished {
                index,
                elapsed,
                section,
            } => match units.entry(index) {
                Entry::Occupied(mut e) => {
                    let elapsed = f64::max(elapsed - e.get().data.start, 0.0);
                    if let Some(section) = e.get_mut().sections.get_mut(&section) {
                        section.end = Some(elapsed);
                    } else {
                        tracing::warn!(
                            "section `{section}` for unit {index} ended, but section `{section}` has no start recorded"
                        );
                    }
                }
                Entry::Vacant(_) => {
                    tracing::warn!(
                        "section `{section}` ended, but unit {index} has no start recorded"
                    )
                }
            },
            LogMessage::UnitPeakMemory { index, bytes } => match units.entry(index) {
                Entry::Occupied(mut e) => {
                    e.get_mut().data.peak_memory = Some(bytes);
                }
                Entry::Vacant(_) => {
                    tracing::warn!("peak memory reported, but unit {index} has no start recorded")
                }
            },
            LogMessage::UnitCpuTimes {
                index,
                user_ns,
                system_ns,
            } => {
                let unit = units
                    .get_mut(&index)
                    .context("CPU accounting references an unregistered unit")?;
                if unit.data.cpu_times.is_some() {
                    anyhow::bail!("duplicate owning CPU accounting for unit {index}");
                }
                unit.data.cpu_times = Some(UnitCpuTimes {
                    user_ns,
                    system_ns,
                    scope: "reaped-child-and-waited-descendants",
                });
            }
            LogMessage::UnitFinished {
                index,
                elapsed,
                unblocked,
            } => match units.entry(index) {
                Entry::Occupied(mut e) => {
                    let elapsed = f64::max(elapsed - e.get().data.start, 0.0);
                    e.get_mut().data.duration = elapsed;
                    e.get_mut().data.unblocked_units = unblocked;
                    e.get_mut().finished = true;
                }
                Entry::Vacant(_) => {
                    tracing::warn!("unit {index} ended, but it has no start recorded");
                }
            },
            LogMessage::UnitGraphFinished { elapsed } if recorded => {
                if graph_finished || !elapsed.is_finite() || elapsed < 0.0 {
                    anyhow::bail!("duplicate or invalid timing unit graph completion");
                }
                graph_finished = true;
            }
            LogMessage::ExecutionEnabled { version } if recorded => {
                if !graph_finished || execution_enabled || version != EXECUTION_VERSION {
                    anyhow::bail!("unsupported or misplaced timing execution schema");
                }
                execution_enabled = true;
            }
            LogMessage::UnitScheduled {
                index,
                elapsed,
                fresh,
            } if recorded => {
                let unit = units
                    .get(&index)
                    .context("timing dispatch references an unregistered unit")?;
                if !execution_enabled
                    || execution_finished
                    || !elapsed.is_finite()
                    || elapsed < 0.0
                    || (unit.requires_fingerprint && !fingerprints.contains_key(&index))
                    || fingerprints.get(&index).is_some_and(|fingerprint| {
                        fresh != matches!(&fingerprint.status, FingerprintStatus::Fresh)
                    })
                    || !scheduled.insert(index)
                {
                    anyhow::bail!("duplicate or unclassified timing unit dispatch");
                }
            }
            LogMessage::ExecutionGraphFinished { elapsed, .. } if recorded => {
                if !execution_enabled || execution_finished || !elapsed.is_finite() || elapsed < 0.0
                {
                    anyhow::bail!("duplicate or invalid timing execution completion");
                }
                execution_finished = true;
            }
            LogMessage::InputWorkStarted { index, .. } if recorded => {
                if !units.contains_key(&index) {
                    anyhow::bail!("timing input work references an unregistered unit");
                }
                captures_started = captures_started
                    .checked_add(1)
                    .context("timing input work count overflow")?;
            }
            LogMessage::InputWorkFinished { index, .. } if recorded => {
                if !units.contains_key(&index) {
                    anyhow::bail!("timing input work references an unregistered unit");
                }
                captures_finished = captures_finished
                    .checked_add(1)
                    .context("timing input work count overflow")?;
            }
            LogMessage::InputWorkClosed {
                version,
                started,
                finished,
            } if recorded => {
                if !input_enabled
                    || workspace_root.is_none()
                    || !graph_finished
                    || (execution_enabled && !execution_finished)
                    || version != INPUT_WORK_VERSION
                    || started != captures_started
                    || finished != captures_finished
                {
                    anyhow::bail!("timing log lacks a complete supported stream closure");
                }
                closed = true;
            }
            _ => {} // skip non-timing logs
        }
        record_count += 1;
    }

    if recorded && input_enabled && !closed {
        anyhow::bail!("timing log has no terminal stream closure");
    }
    if recorded && workspace_root.is_none() {
        anyhow::bail!("timing log lacks its original workspace");
    }
    if recorded && !graph_finished {
        anyhow::bail!("timing log has no complete unit graph");
    }

    // Trust: count final classifications once per unit in both live --timings
    // and recorded reports. Timeline/section observations are independent.
    for fingerprint in fingerprints.into_values() {
        match fingerprint.status {
            FingerprintStatus::New | FingerprintStatus::Dirty => ctx.total_dirty += 1,
            FingerprintStatus::Fresh => ctx.total_fresh += 1,
        }
    }

    // A build can legitimately have no units at all, such as an idle
    // `cargo test` with `test = false` and `doctest = false`,
    // so `--timings` always renders its report.
    // `cargo report timings` instead treats a unit-less
    // log as corrupted or truncated and errors out.
    // See https://github.com/rust-lang/cargo/issues/17212.
    if recorded && units.is_empty() {
        anyhow::bail!("no timing data found in log");
    }

    ctx.root_units = {
        let mut root_map: IndexMap<_, Vec<_>> = IndexMap::default();
        for index in requested_units {
            let unit = &units[&index];
            // Pretty much like `workspace::Target::description_named`
            let target_desc = if unit.target.kind == "lib" {
                "lib".to_owned()
            } else if unit.target.kind == "build-script" {
                "build script".to_owned()
            } else {
                format!(r#" {} "{}""#, unit.target.name, unit.target.kind)
            };
            root_map.entry(index).or_default().push(target_desc);
        }
        root_map
            .into_iter()
            .sorted_by_key(|(i, _)| *i)
            .map(|(index, targets)| {
                let unit = &units[&index];
                let pkg_desc = format!("{} {}", unit.data.name, unit.data.version);
                (pkg_desc, targets)
            })
            .collect()
    };

    let started: HashSet<UnitIndex> = units
        .iter()
        .filter(|(_, entry)| entry.started)
        .map(|(index, _)| *index)
        .collect();

    // Units that never started, like fresh units, and
    // units that were run outside the job queue are
    // excluded so they don't show up as zero-duration rows.
    // See https://github.com/rust-lang/cargo/issues/17212.
    let unit_data: Vec<_> = units
        .into_values()
        .filter(|entry| entry.started)
        .map(
            |UnitEntry {
                 target: _,
                 mut data,
                 sections,
                 rmeta_time,
                 started: _,
                 finished: _,
                 last_elapsed: _,
                 requires_fingerprint: _,
             }| {
                // A finished unit can unblock units that never started, like
                // fresh units. Drop them so rows never reference units absent
                // from the report.
                data.unblocked_units.retain(|index| started.contains(index));
                data.unblocked_rmeta_units
                    .retain(|index| started.contains(index));

                // Post-processing for compilation sections we've collected so far.
                data.sections = aggregate_sections(sections, data.duration, rmeta_time);
                data.start = round_to_centisecond(data.start);
                data.duration = round_to_centisecond(data.duration);
                data
            },
        )
        .sorted_unstable_by(|a, b| a.start.partial_cmp(&b.start).unwrap())
        .collect();

    ctx.unit_data = unit_data;
    ctx.concurrency = compute_concurrency(&ctx.unit_data);
    ctx.requested_targets = platform_targets.into_iter().sorted_unstable().collect();

    Ok(PreparedTimings {
        render: ctx,
        workspace_root,
        stream_complete: closed,
    })
}

#[cfg(test)]
// Trust: counters describe units, not the number of freshness observations.
mod fingerprint_count_tests {
    use super::*;
    use crate::compiler::CompileMode;
    use crate::compiler::fingerprint::{DepInfoUnavailable, DirtyReason, FsStatus, StaleItem};
    use crate::util::log_message::ExecutionGraphOutcome;

    fn unit(index: u64) -> LogMessage {
        LogMessage::UnitRegistered {
            package_id: cargo_util_schemas::core::PackageIdSpec::parse("foo@0.0.1").unwrap(),
            target: Target {
                name: "foo".into(),
                kind: "bin".into(),
            },
            mode: CompileMode::Build,
            platform: "aarch64-apple-darwin".into(),
            index: UnitIndex(index),
            features: Vec::new(),
            requested: true,
            dependencies: Vec::new(),
        }
    }

    fn dirty() -> DirtyReason {
        DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::DepInfoUnavailable {
            path: "target/debug/fingerprint/dep-bin-foo".into(),
            reason: DepInfoUnavailable::FormatMismatch {
                recorded: 2,
                current: 3,
            },
        }))
    }

    fn fingerprint(
        index: u64,
        status: FingerprintStatus,
        cause: Option<DirtyReason>,
        recheck: bool,
    ) -> LogMessage {
        LogMessage::UnitFingerprint {
            index: UnitIndex(index),
            status,
            cause,
            recheck,
        }
    }

    fn counts(messages: Vec<LogMessage>) -> CargoResult<(u32, u32)> {
        let id = "20261106T000000000Z-0000000000000000".parse().unwrap();
        let context = prepare_context(messages.into_iter().map(Ok), &id, false)?.render;
        Ok((context.total_dirty, context.total_fresh))
    }

    fn recorded_prefix() -> Vec<LogMessage> {
        vec![
            LogMessage::InputWorkEnabled {
                version: INPUT_WORK_VERSION,
            },
            LogMessage::BuildStarted {
                command: Vec::new(),
                cwd: std::env::current_dir().unwrap(),
                host: "host".into(),
                jobs: 1,
                num_cpus: None,
                profile: "dev".into(),
                rustc_version: "trustc".into(),
                rustc_version_verbose: "trustc".into(),
                target_dir: std::env::current_dir().unwrap().join("target"),
                workspace_root: std::env::current_dir().unwrap(),
            },
            unit(0),
            LogMessage::UnitGraphFinished { elapsed: 0.0 },
            fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), false),
            LogMessage::ExecutionEnabled {
                version: EXECUTION_VERSION,
            },
            LogMessage::UnitScheduled {
                index: UnitIndex(0),
                elapsed: 0.5,
                fresh: false,
            },
            LogMessage::UnitStarted {
                index: UnitIndex(0),
                elapsed: 1.0,
            },
        ]
    }

    fn close_failed(messages: &mut Vec<LogMessage>) {
        messages.extend([
            LogMessage::ExecutionGraphFinished {
                elapsed: 3.0,
                outcome: ExecutionGraphOutcome::Failed,
                scheduled: 1,
                completed: 1,
                not_executed: 0,
            },
            LogMessage::InputWorkClosed {
                version: INPUT_WORK_VERSION,
                started: 0,
                finished: 0,
            },
        ]);
    }

    #[test]
    fn failed_units_retain_owning_cpu_and_missing_zero_and_duplicate_are_distinct() {
        fn checked(messages: &[LogMessage], id: &RunId) -> CargoResult<Vec<LogMessage>> {
            use std::io::Write as _;
            let mut file = tempfile::NamedTempFile::new()?;
            for message in messages {
                let mut value = serde_json::to_value(message)?;
                value["run_id"] = serde_json::json!(id.to_string());
                value["timestamp"] = serde_json::json!("2026-11-06T00:00:00Z");
                serde_json::to_writer(file.as_file_mut(), &value)?;
                file.as_file_mut().write_all(b"\n")?;
            }
            file.flush()?;
            read_checked(file.path(), |reader| {
                records(reader, &id.to_string()).collect()
            })
        }
        let id = "20261106T000000000Z-0000000000000000".parse().unwrap();
        for measurement in [None, Some((0, 0)), Some((123_000, 45_000))] {
            let mut messages = recorded_prefix();
            if let Some((user_ns, system_ns)) = measurement {
                messages.push(LogMessage::UnitCpuTimes {
                    index: UnitIndex(0),
                    user_ns,
                    system_ns,
                });
            }
            close_failed(&mut messages);
            let decoded = checked(&messages, &id).unwrap();
            let prepared = prepare_context(decoded.into_iter().map(Ok), &id, true).unwrap();
            let actual = &prepared.render.unit_data[0].cpu_times;
            assert_eq!(
                actual.as_ref().map(|time| (time.user_ns, time.system_ns)),
                measurement
            );
            if let Some(time) = actual {
                assert_eq!(time.scope, "reaped-child-and-waited-descendants");
            }
        }
        let cpu = LogMessage::UnitCpuTimes {
            index: UnitIndex(0),
            user_ns: 1,
            system_ns: 2,
        };
        let mut duplicate = recorded_prefix();
        duplicate.extend([cpu.clone(), cpu.clone()]);
        close_failed(&mut duplicate);
        assert!(
            prepare_context(
                checked(&duplicate, &id).unwrap().into_iter().map(Ok),
                &id,
                true
            )
            .is_err()
        );
        let mut unbound = recorded_prefix();
        unbound.push(LogMessage::UnitCpuTimes {
            index: UnitIndex(1),
            user_ns: 1,
            system_ns: 2,
        });
        close_failed(&mut unbound);
        assert!(
            prepare_context(
                checked(&unbound, &id).unwrap().into_iter().map(Ok),
                &id,
                true
            )
            .is_err()
        );
        let mut before_start = recorded_prefix();
        before_start.pop();
        before_start.push(cpu);
        close_failed(&mut before_start);
        assert!(
            prepare_context(
                checked(&before_start, &id).unwrap().into_iter().map(Ok),
                &id,
                true
            )
            .is_err()
        );
    }

    #[test]
    fn recorded_stream_requires_closure_and_consumes_errors_after_it() {
        let id = "20261106T000000000Z-0000000000000000".parse().unwrap();
        let mut messages = recorded_prefix();
        assert!(prepare_context(messages.clone().into_iter().map(Ok), &id, true).is_err());
        close_failed(&mut messages);
        let prepared = prepare_context(messages.clone().into_iter().map(Ok), &id, true).unwrap();
        assert!(prepared.stream_complete);
        assert_eq!(
            prepared.workspace_root.unwrap(),
            std::env::current_dir().unwrap()
        );
        // Failure is allowed to leave a unit and its sections unfinished.
        assert_eq!(prepared.render.unit_data.len(), 1);
        assert_eq!(prepared.render.total_dirty, 1);
        let stream = messages
            .into_iter()
            .map(Ok)
            .chain(std::iter::once(Err(anyhow::anyhow!(
                "trailing decode error"
            ))));
        assert!(prepare_context(stream, &id, true).is_err());
    }

    #[test]
    fn recorded_timeline_rejects_missing_classification_and_invalid_events() {
        let id = "20261106T000000000Z-0000000000000000".parse().unwrap();
        let mut missing = recorded_prefix();
        missing.retain(|message| !matches!(message, LogMessage::UnitFingerprint { .. }));
        close_failed(&mut missing);
        assert!(prepare_context(missing.into_iter().map(Ok), &id, true).is_err());
        for invalid in [
            unit(0),
            LogMessage::UnitStarted {
                index: UnitIndex(0),
                elapsed: 2.0,
            },
            LogMessage::UnitFinished {
                index: UnitIndex(1),
                elapsed: 2.0,
                unblocked: Vec::new(),
            },
            LogMessage::UnitFinished {
                index: UnitIndex(0),
                elapsed: 0.5,
                unblocked: Vec::new(),
            },
            LogMessage::UnitSectionStarted {
                index: UnitIndex(0),
                elapsed: f64::NAN,
                section: "phase".into(),
            },
        ] {
            let mut messages = recorded_prefix();
            messages.push(invalid);
            close_failed(&mut messages);
            assert!(prepare_context(messages.into_iter().map(Ok), &id, true).is_err());
        }
    }

    #[test]
    fn live_and_legacy_timing_completeness_are_not_invented() {
        let id = "20261106T000000000Z-0000000000000000".parse().unwrap();
        let messages = recorded_prefix();
        let live = messages
            .clone()
            .into_iter()
            .filter(|message| !matches!(message, LogMessage::InputWorkEnabled { .. }));
        let live = prepare_context(live.map(Ok), &id, false).unwrap();
        assert!(!live.stream_complete);
        assert_eq!(live.render.unit_data.len(), 1);
        let legacy = messages
            .into_iter()
            .filter(|message| !matches!(message, LogMessage::InputWorkEnabled { .. }));
        let legacy = prepare_context(legacy.map(Ok), &id, true).unwrap();
        assert!(!legacy.stream_complete);
        assert_eq!(legacy.render.total_dirty, 1);
    }

    #[test]
    fn marked_dirty_recheck_counts_one_unit_and_preserves_its_timeline() {
        let messages = vec![
            unit(0),
            fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), false),
            fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), true),
            LogMessage::UnitStarted {
                index: UnitIndex(0),
                elapsed: 1.0,
            },
            LogMessage::UnitFinished {
                index: UnitIndex(0),
                elapsed: 3.0,
                unblocked: Vec::new(),
            },
        ];
        let id = "20261106T000000000Z-0000000000000000".parse().unwrap();
        let context = prepare_context(messages.into_iter().map(Ok), &id, false)
            .unwrap()
            .render;
        assert_eq!((context.total_dirty, context.total_fresh), (1, 0));
        assert_eq!(context.unit_data.len(), 1);
        assert_eq!(context.unit_data[0].start, 1.0);
        assert_eq!(context.unit_data[0].duration, 2.0);
    }

    #[test]
    fn marked_fresh_recheck_replaces_the_initial_dirty_classification() {
        assert_eq!(
            counts(vec![
                unit(0),
                fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), false),
                fingerprint(0, FingerprintStatus::Fresh, None, true),
            ])
            .unwrap(),
            (0, 1)
        );
    }

    #[test]
    fn distinct_initial_units_keep_their_legacy_counts() {
        assert_eq!(
            counts(vec![
                unit(0),
                unit(1),
                unit(2),
                fingerprint(0, FingerprintStatus::New, None, false),
                fingerprint(1, FingerprintStatus::Dirty, Some(dirty()), false),
                fingerprint(2, FingerprintStatus::Fresh, None, false),
            ])
            .unwrap(),
            (2, 1)
        );
    }

    #[test]
    fn repeated_or_unbound_classifications_are_not_inferred_rechecks() {
        for messages in [
            vec![
                unit(0),
                fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), false),
                fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), false),
            ],
            vec![
                unit(0),
                fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), true),
            ],
            vec![
                unit(0),
                fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), false),
                fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), true),
                fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), true),
            ],
            vec![
                unit(0),
                fingerprint(0, FingerprintStatus::Fresh, None, false),
                fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), true),
            ],
            vec![fingerprint(0, FingerprintStatus::New, None, false)],
            vec![
                unit(0),
                fingerprint(0, FingerprintStatus::Dirty, Some(dirty()), false),
                LogMessage::UnitStarted {
                    index: UnitIndex(0),
                    elapsed: 1.0,
                },
                fingerprint(0, FingerprintStatus::Fresh, None, true),
            ],
        ] {
            assert!(counts(messages).is_err());
        }
    }

    #[test]
    fn status_and_cause_must_agree_for_initial_and_recheck_observations() {
        for recheck in [false, true] {
            for (status, cause) in [
                (FingerprintStatus::Dirty, None),
                (FingerprintStatus::Dirty, Some(DirtyReason::FreshBuild)),
                (FingerprintStatus::Fresh, Some(dirty())),
                (FingerprintStatus::New, Some(dirty())),
            ] {
                let mut messages = vec![unit(0)];
                if recheck {
                    messages.push(fingerprint(
                        0,
                        FingerprintStatus::Dirty,
                        Some(dirty()),
                        false,
                    ));
                }
                messages.push(fingerprint(0, status, cause, recheck));
                assert!(counts(messages).is_err());
            }
        }
    }
}
