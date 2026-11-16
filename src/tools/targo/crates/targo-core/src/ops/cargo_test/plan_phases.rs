//! Trust: the phases of a `targo test --plan` run that lie outside the
//! plan's own build graph: `[[tool]]` and `[[workspace]]`.
//!
//! One build graph has one lockfile, one patch table, one profile and one
//! intent, so a crate that is its own workspace cannot be units of the plan's
//! graph, and neither can a binary the tests run, which is built as `targo
//! build` builds it, in this workspace or another. Each is a phase of its own
//! manifest instead: resolved, built and (for a workspace) tested in this
//! process, one after another and before the plan's own requests. Nothing of
//! a phase overlaps another phase or the requests.
//!
//! * A `[[tool]]` is built, as `targo build --bin <bin>` under its manifest
//!   builds it, when a request this run performs tests a member its
//!   `needed-by` names. The file is then copied aside, and the copy's path
//!   is exported as the tool's `env` variable to the test executables of
//!   those members and to no other (`ResolvedPlan::export_tools`): every
//!   other test executable of the run, a `[[workspace]]`'s too, has the
//!   variable removed, whatever the invocation's environment holds. The
//!   copy is what runs: another build that relinks the target directory's
//!   file while the tests run does not change the binary under test. A
//!   changed path in a tool's directory selects the members that run it
//!   (`plan_select`).
//! * A `[[workspace]]` is tested, as `targo test --tests` under its manifest
//!   tests it, when a changed path lies in its directory, or when the
//!   invocation names no change. Its `cfg`, if it has one, is held against
//!   the build's target first: where it does not hold the workspace is
//!   reported as not run on this target, never as tested. The phase is a
//!   plan run of its own (`[default]` over that workspace's default
//!   members), so each harness is held to its closing line and counted, and
//!   the plan's `[default] min-tests` is asked of each of its members. A
//!   run that reports no test at all fails, whatever the plan asks.
//!
//! A phase that fails fails the run. With `--no-fail-fast` a workspace whose
//! run ran to its end with failures does not stop the phases and requests
//! after it; a tool that fails to build, or a phase that did not run to its
//! end, stops the invocation, as a failed build of the plan's graph does. A
//! phase that wrote a `started` record always writes its closing one, `failed`
//! where the invocation ends in it.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::str::FromStr as _;

use anyhow::Context as _;
use cargo_platform::{Cfg, CfgExpr};
use serde::Serialize;

use super::TestOptions;
use super::plan::{
    DefaultRun, DefaultTargets, Members, OwnWorkspace, ResolvedPlan, Run, SCHEMA, Select, TestPlan,
    Tool,
};
use super::plan_select;
use crate::compiler::{CompileKind, RustcTargetData, UserIntent};
use crate::context::FeatureUnification;
use crate::ops::{self, CompileFilter, CompileOptions};
use crate::resolver::features::CliFeatures;
use crate::util::machine_message::Message;
use crate::util::{CargoResult, CliError};
use crate::workspace::{TargetKind, Workspace};

pub const TEST_PLAN_PHASE_SCHEMA_V1: &str = "targo.test-plan-phase.v1";

/// What became of one `[[tool]]` or `[[workspace]]` entry in this run.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum PhaseState {
    /// The phase is about to build; only in a `test-plan-phase` record.
    Started,
    /// A tool, or with `--no-run` a workspace's tests, built.
    Built,
    /// A tool no request of this run needs.
    NotNeeded,
    /// A workspace in whose directory nothing changed.
    NotSelected,
    /// A selected workspace that `--request` narrowed out of the run.
    LeftOut,
    /// A workspace whose `cfg` does not hold for the build's target.
    NotApplicable,
    /// A tool or workspace a run of this selection would build and run;
    /// only in a `--select-only` listing, which builds nothing.
    Selected,
    /// A workspace whose run ran to its end with nothing failed or unmet.
    Passed,
    /// A workspace whose run failed, left a requirement unmet or did not
    /// reach its end, or a tool that did not build.
    Failed,
}

/// One entry's outcome: a row of the result record's `phases`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PhaseRow {
    /// `tool` or `workspace`.
    pub kind: &'static str,
    /// The entry's manifest, as the plan writes it.
    pub manifest: String,
    pub state: PhaseState,
    pub why: String,
    /// A tool's variable; `null` for a workspace.
    pub env: Option<String>,
    /// The tests a workspace's run reported (passed + failed); `null` where
    /// no run ran to its end.
    pub tests: Option<u64>,
}

impl PhaseRow {
    /// Why this row fails the plan's run, if it does.
    pub(crate) fn unmet(&self) -> Option<String> {
        (self.state == PhaseState::Failed).then(|| {
            format!(
                "{} `{}` failed: {} (its own records name the failures)",
                self.kind, self.manifest, self.why
            )
        })
    }
}

/// A `test-plan-phase` record: one when a phase starts and one when it
/// ends. Every record between the two is that phase's own, and a test
/// action's `index` is counted within its phase.
#[derive(Debug, Serialize)]
struct PhaseRecord<'a> {
    schema: &'static str,
    plan: String,
    #[serde(flatten)]
    row: &'a PhaseRow,
}

impl Message for PhaseRecord<'_> {
    fn reason(&self) -> &str {
        "test-plan-phase"
    }
}

/// Marks the plan of a `[[workspace]]` phase and holds what its run
/// concluded.
#[derive(Clone, Debug)]
pub struct Phase {
    /// The workspace's manifest, as the plan writes it.
    pub manifest: String,
    /// The same manifest as a path any directory can name.
    pub path: PathBuf,
    /// The variables of the plan's `[[tool]]`s: no test of a workspace of
    /// its own is a tool's `needed-by` member, so none sees one.
    pub withheld: Vec<String>,
    outcome: Rc<RefCell<Option<Outcome>>>,
}

/// What a phase's run concluded, set only by a run that ran to its end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Outcome {
    pub passed: bool,
    /// The tests its harnesses reported (passed + failed).
    pub tests: u64,
}

impl Phase {
    /// Records the verdict of this phase's run.
    pub(crate) fn conclude(&self, outcome: Outcome) {
        *self.outcome.borrow_mut() = Some(outcome);
    }
}

/// A tool this run built: the variable, the private copy it names, and the
/// members whose test executables get it.
#[derive(Clone, Debug)]
pub struct BuiltTool {
    pub env: String,
    pub path: PathBuf,
    pub needed_by: Vec<String>,
}

/// Holds the private copies of the run's tools; dropping it deletes them.
#[derive(Default)]
#[must_use = "the tools' private copies are deleted when this is dropped"]
pub struct Private {
    _directories: Vec<tempfile::TempDir>,
}

/// What a run ended from outside its phases still owes (`plan_clock`'s
/// watcher, when no job queue is left to end it): the closing record of a
/// phase that wrote its `started` one, and the tools' private copies, which
/// no drop removes when the process exits.
struct Owed {
    /// The plan as the run's records spell it, and the phase's row.
    open: Option<(String, PhaseRow)>,
    aside: Vec<PathBuf>,
    /// Set once the run was ended from outside: no phase record follows.
    ended: bool,
}

static OWED: std::sync::Mutex<Owed> = std::sync::Mutex::new(Owed {
    open: None,
    aside: Vec::new(),
    ended: false,
});

/// Settles what the phases owe a run that ends now as `why` says: removes
/// the tools' private copies, and writes to `out` the closing record (state
/// `failed`) of the phase that was running, if one was. No phase record is
/// written after it.
pub(crate) fn abandon(why: &str, out: &mut dyn std::io::Write) {
    let mut owed = OWED.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    owed.ended = true;
    for directory in owed.aside.drain(..) {
        let _ = std::fs::remove_dir_all(directory);
    }
    if let Some((plan, mut row)) = owed.open.take() {
        row.state = PhaseState::Failed;
        row.why = why.to_owned();
        let record = PhaseRecord {
            schema: TEST_PLAN_PHASE_SCHEMA_V1,
            plan,
            row: &row,
        };
        let _ = writeln!(out, "{}", record.to_json_string());
    }
}

/// Checks a `[[tool]]` and `[[workspace]]` entry's own text, without a
/// workspace (`TestPlan::parse`).
pub(super) fn check_entries(plan: &TestPlan) -> CargoResult<()> {
    let named = |what: &str, manifest: &str| -> CargoResult<()> {
        // As a changed path is held (`plan_select::parse_paths`): the
        // manifest's directory owns changed paths as text, and one written
        // with a `.` or an empty part would own none and be listed twice
        // unseen. `Path::components` drops both, so the text is held too.
        let normal = manifest
            .split('/')
            .all(|part| !part.is_empty() && part != "." && part != "..")
            && Path::new(manifest)
                .components()
                .all(|part| matches!(part, std::path::Component::Normal(_)))
            && !manifest.contains('\\');
        anyhow::ensure!(
            normal && Path::new(manifest).file_name() == Some("Cargo.toml".as_ref()),
            "{what} manifest `{manifest}` is not a `Cargo.toml` named by a normal path \
             relative to the workspace root"
        );
        Ok(())
    };
    let mut variables = BTreeMap::new();
    for tool in &plan.tool {
        named("`[[tool]]`", &tool.manifest)?;
        anyhow::ensure!(
            !tool.bin.is_empty(),
            "`[[tool]]` `{}` names an empty `bin`",
            tool.manifest
        );
        let plain = tool
            .env
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
            && !tool.env.is_empty()
            && !tool.env.as_bytes()[0].is_ascii_digit();
        anyhow::ensure!(
            plain,
            "`[[tool]]` `{}`: `env = \"{}\"` is not a variable name (ASCII letters, digits \
             and `_`, not starting with a digit)",
            tool.manifest,
            tool.env
        );
        // The build and the loader read these; a tool's path is not one.
        let reserved = ["CARGO", "RUST", "TARGO", "DYLD_", "LD_"]
            .iter()
            .any(|prefix| tool.env.starts_with(prefix))
            || ["PATH", "HOME", "TMPDIR"].contains(&tool.env.as_str());
        anyhow::ensure!(
            !reserved,
            "`[[tool]]` `{}`: `env = \"{}\"` is a variable the build or the system reads",
            tool.manifest,
            tool.env
        );
        if let Some(other) = variables.insert(tool.env.as_str(), tool.manifest.as_str()) {
            anyhow::bail!(
                "`[[tool]]` `{}` and `{other}` both export `{}`",
                tool.manifest,
                tool.env
            );
        }
        // A tool is built for the members that need it; one nobody needs
        // would never be built and reads as if it were.
        anyhow::ensure!(
            !tool.needed_by.is_empty(),
            "`[[tool]]` `{}` names no member in `needed-by`, so nothing would build it",
            tool.manifest
        );
    }
    let mut manifests = std::collections::BTreeSet::new();
    for own in &plan.workspace {
        named("`[[workspace]]`", &own.manifest)?;
        // A manifest in the root's own directory is the invocation's.
        anyhow::ensure!(
            own.manifest.contains('/'),
            "`[[workspace]]` manifest `{}` is the invocation's own workspace",
            own.manifest
        );
        anyhow::ensure!(
            manifests.insert(own.manifest.as_str()),
            "`[[workspace]]` `{}` is listed twice",
            own.manifest
        );
        if let Some(cfg) = &own.cfg {
            let expression = CfgExpr::from_str(cfg).with_context(|| {
                format!(
                    "`[[workspace]]` `{}`: `cfg = '{cfg}'` is not a cfg expression",
                    own.manifest
                )
            })?;
            if let Err(why) = of_the_target(&expression) {
                anyhow::bail!(
                    "`[[workspace]]` `{}`: `cfg = '{cfg}'`: {why}; a `cfg` says for which \
                     targets the workspace is tested ({}, or {} with a value)",
                    own.manifest,
                    TARGET_NAMES.join(", "),
                    TARGET_KEYS.join(", ")
                );
            }
        }
    }
    Ok(())
}

/// The cfg names a `[[workspace]]` `cfg` may test: those a target alone
/// decides.
const TARGET_NAMES: [&str; 2] = ["unix", "windows"];

/// The cfg keys a `[[workspace]]` `cfg` may test; see `TARGET_NAMES`.
const TARGET_KEYS: [&str; 8] = [
    "target_abi",
    "target_arch",
    "target_endian",
    "target_env",
    "target_family",
    "target_os",
    "target_pointer_width",
    "target_vendor",
];

/// Visits each `key = "value"` of `expression`.
fn key_values<'a>(expression: &'a CfgExpr, visit: &mut dyn FnMut(&'a str, &'a str)) {
    match expression {
        CfgExpr::Not(inner) => key_values(inner, visit),
        CfgExpr::All(list) | CfgExpr::Any(list) => {
            list.iter().for_each(|inner| key_values(inner, visit));
        }
        CfgExpr::Value(Cfg::KeyPair(key, value)) => visit(key.as_str(), value),
        CfgExpr::Value(Cfg::Name(_)) | CfgExpr::True | CfgExpr::False => {}
    }
}

/// Holds `expression` to what the build's target alone decides. A workspace
/// whose `cfg` does not hold is not tested and the run can still pass, so a
/// `cfg` that no target can satisfy (`linux`, `feature = "x"`, `test`), or
/// one the profile decides (`debug_assertions`), would turn the workspace off
/// on every host, or on some for no reason of the target's.
fn of_the_target(expression: &CfgExpr) -> Result<(), String> {
    match expression {
        CfgExpr::Not(inner) => of_the_target(inner),
        CfgExpr::All(list) | CfgExpr::Any(list) => list.iter().try_for_each(of_the_target),
        CfgExpr::Value(Cfg::Name(name)) if TARGET_NAMES.contains(&name.as_str()) => Ok(()),
        CfgExpr::Value(Cfg::KeyPair(key, _)) if TARGET_KEYS.contains(&key.as_str()) => Ok(()),
        CfgExpr::Value(cfg) => Err(format!("`{cfg}` is not a cfg of the target")),
        CfgExpr::True | CfgExpr::False => {
            Err(format!("`{expression}` is the same on every target"))
        }
    }
}

/// The values the compiler knows for each cfg key, as `rustc
/// --print=check-cfg` lists them.
fn known_values(ws: &Workspace<'_>) -> CargoResult<BTreeMap<String, BTreeSet<String>>> {
    let rustc = ws.gctx().load_global_rustc(Some(ws))?;
    let mut command = rustc.process();
    // Without a `--check-cfg` the compiler checks, and so lists, nothing.
    command.args(&[
        "--print=check-cfg",
        "-Zunstable-options",
        "--check-cfg=cfg()",
    ]);
    // Asked as every compiler probe is, through `Rustc::cached_output`: that
    // gives the query a scheduler. Run bare, the compiler of a build-slot job
    // (`BUILD_SLOT_CPU_PROTOCOL`) refuses it with exit status 75, "native
    // compiler work has no captured inherited GNU scheduler", and the whole
    // plan with it.
    let (stdout, _) = rustc
        .cached_output(&command, 0)
        .context("cannot ask the compiler which cfg values it knows")?;
    Ok(parse_check_cfg(&stdout))
}

/// Reads lines of the form `cfg(key, values("a", "b", none()))`.
fn parse_check_cfg(text: &str) -> BTreeMap<String, BTreeSet<String>> {
    let mut known = BTreeMap::new();
    for line in text.lines() {
        let Some((key, values)) = line
            .strip_prefix("cfg(")
            .and_then(|rest| rest.split_once(", values("))
        else {
            continue;
        };
        // Every second piece between quotes is a value; none holds a quote.
        known.insert(
            key.to_owned(),
            values
                .split('"')
                .skip(1)
                .step_by(2)
                .map(str::to_owned)
                .collect(),
        );
    }
    known
}

/// Refuses a `[[workspace]]` `cfg` that tests a value the compiler knows of
/// no target (`target_os = "Linux"`): it could never hold, and the workspace
/// would be reported as not for this target on every one.
fn check_values(ws: &Workspace<'_>, plan: &TestPlan) -> CargoResult<()> {
    let mut known = None;
    for own in &plan.workspace {
        let Some(cfg) = &own.cfg else { continue };
        let expression = CfgExpr::from_str(cfg)?;
        let mut tested = Vec::new();
        key_values(&expression, &mut |key, value| tested.push((key, value)));
        for (key, value) in tested {
            let known = match &known {
                Some(known) => known,
                None => known.insert(known_values(ws)?),
            };
            let values = known.get(key).with_context(|| {
                format!(
                    "`[[workspace]]` `{}`: `cfg = '{cfg}'`: the compiler lists no values of \
                     `{key}`, so `{key} = \"{value}\"` cannot be held to them",
                    own.manifest
                )
            })?;
            anyhow::ensure!(
                values.contains(value),
                "`[[workspace]]` `{}`: `cfg = '{cfg}'`: `{key} = \"{value}\"` holds for no \
                 target the compiler knows, so the workspace would be tested on none; `{key}` \
                 is one of: {}",
                own.manifest,
                values
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
    }
    Ok(())
}

/// What a run of this selection would do with each `[[tool]]` and
/// `[[workspace]]` entry, in the plan's order, decided as [`run`] decides it
/// and with nothing built: a tool is `selected` or `not-needed`, a workspace
/// `selected`, `not-selected`, `left-out` or `not-applicable`. A
/// `--select-only` listing carries these rows, so that a caller that plans
/// around the lane (which members it tests on this host) asks the lane and
/// keeps no copy of its rules.
pub(super) fn describe(
    ws: &Workspace<'_>,
    options: &CompileOptions,
    plan: &ResolvedPlan,
) -> CargoResult<Vec<PhaseRow>> {
    if !plan.plan.workspace.is_empty() {
        check_values(ws, &plan.plan)
            .with_context(|| format!("test plan `{}`", plan.path.display()))?;
    }
    let mut rows = Vec::new();
    for tool in &plan.plan.tool {
        let consumers = plan.consumers(tool);
        rows.push(PhaseRow {
            kind: "tool",
            manifest: tool.manifest.clone(),
            state: if consumers.is_empty() {
                PhaseState::NotNeeded
            } else {
                PhaseState::Selected
            },
            why: if consumers.is_empty() {
                format!(
                    "no request of this run tests a member that needs it ({})",
                    tool.needed_by.join(", ")
                )
            } else {
                format!("built for {}", consumers.join(", "))
            },
            env: Some(tool.env.clone()),
            tests: None,
        });
    }
    for own in &plan.plan.workspace {
        let (state, why) = if !plan.selection.workspaces.contains(&own.manifest) {
            (
                PhaseState::NotSelected,
                "no changed path lies in its directory".to_owned(),
            )
        } else if !plan.only.is_empty() {
            (PhaseState::LeftOut, "left out by --request".to_owned())
        } else {
            let named = || {
                format!(
                    "test plan `{}`, workspace `{}`",
                    plan.path.display(),
                    own.manifest
                )
            };
            // As a run would: an entry the plan states wrongly judges nothing.
            let phase_ws = own_workspace(ws, options, own)
                .with_context(named)
                .map_err(super::plan_outcome::cannot_judge)?;
            match applies(&phase_ws, &options.build_config.requested_kinds, own)
                .with_context(named)
                .map_err(super::plan_outcome::cannot_judge)?
            {
                Err(why) => (PhaseState::NotApplicable, why),
                Ok(()) => (
                    PhaseState::Selected,
                    "tested under its own manifest".to_owned(),
                ),
            }
        };
        rows.push(PhaseRow {
            kind: "workspace",
            manifest: own.manifest.clone(),
            state,
            why,
            env: None,
            tests: None,
        });
    }
    Ok(rows)
}

/// Performs the plan's `[[tool]]` and `[[workspace]]` phases, in the plan's
/// order, tools first. Their outcomes go into the plan, whose verdict and
/// result record carry them, and the built tools with them, for the test
/// actions that follow. The result holds the tools' private copies and must
/// outlive the run of the plan's requests.
///
/// `--unit-graph` performs none: its output is one graph of one workspace
/// (`ResolvedPlan::require_supported` says so).
pub fn run(
    ws: &Workspace<'_>,
    options: &mut CompileOptions,
    no_run: bool,
    no_fail_fast: bool,
) -> Result<Private, CliError> {
    let mut private = Private::default();
    let unit_graph = options.build_config.unit_graph || options.build_config.dry_run;
    let Some(plan) = options.build_config.test_plan.clone() else {
        return Ok(private);
    };
    if unit_graph || (plan.plan.tool.is_empty() && plan.plan.workspace.is_empty()) {
        return Ok(private);
    }
    // Nothing is built for a plan the invocation is about to refuse.
    plan.refusals(no_run, no_fail_fast)
        .map_err(super::plan_outcome::cannot_judge)?;
    check_values(ws, &plan.plan)
        .with_context(|| format!("test plan `{}`", plan.path.display()))
        .map_err(super::plan_outcome::cannot_judge)?;
    let gctx = ws.gctx();
    let emit = |row: &PhaseRow| -> CargoResult<()> {
        if options.build_config.emit_json() {
            let record = PhaseRecord {
                schema: TEST_PLAN_PHASE_SCHEMA_V1,
                plan: plan.path.to_string_lossy().into_owned(),
                row,
            };
            // A phase's records are written under the lock that says which
            // one is open, so a run ended from outside closes it once.
            let mut owed = OWED.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
            if owed.ended {
                return Ok(());
            }
            writeln!(gctx.shell().out(), "{}", record.to_json_string())?;
            owed.open = (row.state == PhaseState::Started).then(|| (record.plan, row.clone()));
        }
        Ok(())
    };
    let started = |row: &PhaseRow| {
        emit(&PhaseRow {
            state: PhaseState::Started,
            why: String::new(),
            tests: None,
            ..row.clone()
        })
    };
    let mut rows = Vec::new();
    let mut tools = Vec::new();

    for tool in &plan.plan.tool {
        let mut row = PhaseRow {
            kind: "tool",
            manifest: tool.manifest.clone(),
            state: PhaseState::NotNeeded,
            why: String::new(),
            env: Some(tool.env.clone()),
            tests: None,
        };
        let consumers = plan.consumers(tool);
        if consumers.is_empty() {
            row.why = format!(
                "no request of this run tests a member that needs it ({})",
                tool.needed_by.join(", ")
            );
            emit(&row)?;
            rows.push(row);
            continue;
        }
        started(&row)?;
        gctx.shell().status(
            "Phase",
            format!(
                "tool `{}` of `{}` for {}",
                tool.bin,
                tool.manifest,
                consumers.join(", ")
            ),
        )?;
        // The invocation ends in a phase that fails here; its `started`
        // record is closed first, so that a reader can tell the two apart.
        let ended = |row: &mut PhaseRow, error: anyhow::Error| -> anyhow::Error {
            row.state = PhaseState::Failed;
            row.why = first_line(&error);
            match emit(row) {
                Ok(()) => error,
                Err(unwritten) => unwritten,
            }
        };
        let built = match build_tool(ws, options, tool) {
            Ok(built) => built,
            Err(error) => {
                return Err(ended(&mut row, error)
                    .context(format!(
                        "test plan `{}`: tool `{}` of `{}` failed to build; the tests of {} \
                         that run it cannot run",
                        plan.path.display(),
                        tool.bin,
                        tool.manifest,
                        consumers.join(", ")
                    ))
                    .into());
            }
        };
        row.state = PhaseState::Built;
        if no_run {
            row.why = "built; --no-run runs no test that needs it".to_owned();
        } else {
            let (directory, copy) = match set_aside(&built) {
                Ok(aside) => aside,
                Err(error) => {
                    return Err(ended(&mut row, error)
                        .context(format!(
                            "test plan `{}`: tool `{}` of `{}`",
                            plan.path.display(),
                            tool.bin,
                            tool.manifest
                        ))
                        .into());
                }
            };
            row.why = format!(
                "built `{}`; {} get{} the copy `{}`",
                built.display(),
                consumers.join(", "),
                if consumers.len() == 1 { "s" } else { "" },
                copy.display()
            );
            OWED.lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .aside
                .push(directory.path().to_path_buf());
            private._directories.push(directory);
            tools.push(BuiltTool {
                env: tool.env.clone(),
                path: copy,
                needed_by: tool.needed_by.clone(),
            });
        }
        emit(&row)?;
        rows.push(row);
    }

    let mut left_out = false;
    for own in &plan.plan.workspace {
        let mut row = PhaseRow {
            kind: "workspace",
            manifest: own.manifest.clone(),
            state: PhaseState::NotSelected,
            why: String::new(),
            env: None,
            tests: None,
        };
        if !plan.selection.workspaces.contains(&own.manifest) {
            row.why = "no changed path lies in its directory".to_owned();
        } else if !plan.only.is_empty() {
            // `--request` reproduces named requests; a workspace is none.
            row.state = PhaseState::LeftOut;
            row.why = "left out by --request".to_owned();
            left_out = true;
            gctx.shell().warn(format!(
                "test plan `{}`: --request leaves workspace `{}` out of this run",
                plan.path.display(),
                own.manifest
            ))?;
        } else {
            let named = || {
                format!(
                    "test plan `{}`, workspace `{}`",
                    plan.path.display(),
                    own.manifest
                )
            };
            // A `[[workspace]]` entry the plan states wrongly is no red
            // test: the run cannot judge it.
            let mut phase_ws = own_workspace(ws, options, own)
                .with_context(named)
                .map_err(super::plan_outcome::cannot_judge)?;
            match applies(&phase_ws, &options.build_config.requested_kinds, own)
                .with_context(named)
                .map_err(super::plan_outcome::cannot_judge)?
            {
                Err(why) => {
                    row.state = PhaseState::NotApplicable;
                    gctx.shell()
                        .note(format!("workspace `{}` was NOT RUN: {why}", own.manifest))?;
                    row.why = why;
                }
                Ok(()) => {
                    started(&row)?;
                    gctx.shell()
                        .status("Phase", format!("workspace `{}`", own.manifest))?;
                    let outcome = match test_workspace(
                        &mut phase_ws,
                        options,
                        &plan,
                        own,
                        no_run,
                        no_fail_fast,
                    ) {
                        Ok(outcome) => outcome,
                        // The invocation ends in this phase; its `started`
                        // record is closed first.
                        Err((error, tests)) => {
                            row.state = PhaseState::Failed;
                            row.tests = tests;
                            row.why = match &error.error {
                                Some(error) => first_line(error),
                                None => format!("exit code {}", error.exit_code),
                            };
                            emit(&row)?;
                            return Err(in_phase(error, &named()));
                        }
                    };
                    match outcome {
                        None => {
                            row.state = PhaseState::Built;
                            row.why = "built; --no-run runs no test".to_owned();
                        }
                        Some((outcome, why)) => {
                            row.tests = Some(outcome.tests);
                            row.state = if outcome.passed {
                                PhaseState::Passed
                            } else {
                                PhaseState::Failed
                            };
                            row.why = why;
                        }
                    }
                }
            }
        }
        emit(&row)?;
        rows.push(row);
    }

    let mut plan = plan;
    let resolved = Rc::make_mut(&mut plan);
    resolved.phases = rows;
    resolved.tools = tools;
    // A selected workspace this run left out: not the selection's verdict.
    resolved.narrowed |= left_out;
    options.build_config.test_plan = Some(plan);
    Ok(private)
}

/// Names the phase in an error that ends the invocation inside it.
fn in_phase(error: CliError, named: &str) -> CliError {
    let exit_code = error.exit_code;
    let error = match error.error {
        Some(error) => error.context(named.to_owned()),
        None => anyhow::anyhow!("{named} failed"),
    };
    CliError::new(error, exit_code)
}

/// The first line of `error`, for a row's `why`.
fn first_line(error: &anyhow::Error) -> String {
    format!("{error}")
        .lines()
        .next()
        .unwrap_or_default()
        .to_owned()
}

/// Loads the workspace of `manifest` as the invocation loaded its own, with
/// features unified as for the plan's requests (`plan::select`): over what
/// is built and nothing else.
fn load<'gctx>(
    root: &Workspace<'gctx>,
    options: &CompileOptions,
    manifest: &str,
) -> CargoResult<Workspace<'gctx>> {
    let path = root.root().join(manifest);
    let mut ws = Workspace::new(&path, root.gctx())?;
    ws.set_resolve_honors_rust_version(options.honor_rust_version);
    if root.gctx().cli_unstable().avoid_dev_deps {
        ws.set_require_optional_deps(false);
    }
    ws.set_resolve_feature_unification(FeatureUnification::Selected);
    Ok(ws)
}

/// Builds `tool` as `targo build --bin <bin>` under its manifest builds it,
/// with the invocation's jobs, targets and message format, and returns the
/// file it linked. The manifest may be a member of the invocation's own
/// workspace: the tool is still a build of its own, of another intent and
/// profile than the plan's tests.
fn build_tool(root: &Workspace<'_>, outer: &CompileOptions, tool: &Tool) -> CargoResult<PathBuf> {
    let ws = load(root, outer, &tool.manifest)?;
    let mut options = CompileOptions::new(root.gctx(), UserIntent::Build)?;
    options.build_config = outer.build_config.clone();
    options.build_config.intent = UserIntent::Build;
    options.build_config.requested_profile = "dev".into();
    options.build_config.test_plan = None;
    options.honor_rust_version = outer.honor_rust_version;
    options.filter = CompileFilter::from_raw_arguments(
        false,
        vec![tool.bin.clone()],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
        false,
    );
    let compilation = ops::compile(&ws, &options)?;
    let built = compilation
        .binaries
        .iter()
        .filter(|output| {
            output.unit.target.kind() == &TargetKind::Bin && output.unit.target.name() == tool.bin
        })
        .map(|output| output.path.clone())
        .collect::<Vec<_>>();
    // One file is exported: none, or one per `--target`, is not it.
    let [built] = &built[..] else {
        anyhow::bail!(
            "the build linked {} files for bin `{}`; a tool is one executable",
            built.len(),
            tool.bin
        );
    };
    Ok(built.clone())
}

/// Copies a built tool into a new directory beside it, where no build
/// writes. Beside it means on its volume, where a copy can be a clone.
fn set_aside(built: &Path) -> CargoResult<(tempfile::TempDir, PathBuf)> {
    let (Some(parent), Some(name)) = (built.parent(), built.file_name()) else {
        anyhow::bail!("built file `{}` has no directory", built.display());
    };
    let directory = tempfile::Builder::new()
        .prefix(".targo-plan-tool-")
        .tempdir_in(parent)
        .with_context(|| format!("cannot make a private directory in `{}`", parent.display()))?;
    let copy = directory.path().join(name);
    std::fs::copy(built, &copy)
        .with_context(|| format!("cannot copy `{}` to `{}`", built.display(), copy.display()))?;
    Ok((directory, copy))
}

/// The workspace of a `[[workspace]]` entry, which must be the root of its
/// own.
fn own_workspace<'gctx>(
    root: &Workspace<'gctx>,
    options: &CompileOptions,
    own: &OwnWorkspace,
) -> CargoResult<Workspace<'gctx>> {
    let ws = load(root, options, &own.manifest)?;
    // A member of the invocation's workspace is in the plan's own graph.
    anyhow::ensure!(
        ws.root_manifest() != root.root_manifest(),
        "`{}` belongs to the invocation's own workspace; test it by a request",
        own.manifest
    );
    anyhow::ensure!(
        ws.root_manifest() == root.root().join(&own.manifest),
        "`{}` is a member of the workspace `{}`; a `[[workspace]]` entry names a workspace's \
         root manifest",
        own.manifest,
        ws.root_manifest().display()
    );
    // Configuration is read from the invocation's directory upwards, once
    // per process. A file between the plan's root and this workspace is read
    // by `targo test` run inside the workspace and not by this phase, which
    // would then test another build than the one its people run.
    let mut directory = ws.root();
    while directory != root.root() && directory.starts_with(root.root()) {
        for name in ["config.toml", "config"] {
            let config = directory.join(".cargo").join(name);
            anyhow::ensure!(
                !config.exists(),
                "`{}` configures a run inside `{}` and is not read by a phase of this \
                 invocation, which reads configuration from `{}` upwards; move what the \
                 workspace's tests need into its manifest, or test it by a command of its own",
                config.display(),
                directory.display(),
                root.root().display()
            );
        }
        let Some(parent) = directory.parent() else {
            break;
        };
        directory = parent;
    }
    Ok(ws)
}

/// Whether `own`'s `cfg` holds for what this invocation builds for: `Ok`,
/// or why its tests are not run. A workspace gated on a cfg has tests that
/// compile only where it holds; elsewhere a run could only fail or report
/// nothing, and neither would say anything about the change.
///
/// The entry's `cfg` is the gate its libraries carry (`library_gate`), and
/// an entry that states another is refused, on every target: a `cfg` the
/// library has since lost would take a workspace whose tests do run here out
/// of the run, and the run would pass without them.
fn applies(
    ws: &Workspace<'_>,
    kinds: &[CompileKind],
    own: &OwnWorkspace,
) -> CargoResult<Result<(), String>> {
    let stated = own.cfg.as_deref().map(CfgExpr::from_str).transpose()?;
    for package in ws.default_members() {
        let Some(library) = package.targets().iter().find(|target| target.is_lib()) else {
            continue;
        };
        let Some(source) = library.src_path().path() else {
            continue;
        };
        let text = std::fs::read_to_string(source)
            .with_context(|| format!("cannot read `{}` for its gate", source.display()))?;
        let gate = library_gate(&text)
            .map_err(|error| anyhow::anyhow!("`{}`: {error}", source.display()))?;
        let spelled = |cfg: &Option<CfgExpr>| match cfg {
            Some(cfg) => format!("`cfg = '{cfg}'`"),
            None => "no `cfg`".to_owned(),
        };
        anyhow::ensure!(
            gate == stated,
            "the entry states {} and the library of `{}` is gated on {} (`{}`); an entry's \
             `cfg` is the crate-level `#![cfg(..)]` its libraries carry, so that no workspace \
             is taken out of a run that its own code does not take out",
            spelled(&stated),
            package.name(),
            spelled(&gate),
            source.display()
        );
    }
    let Some(expression) = stated else {
        return Ok(Ok(()));
    };
    let cfg = own.cfg.as_deref().unwrap_or_default();
    let data = RustcTargetData::new(ws, kinds)?;
    let holds = kinds
        .iter()
        .map(|kind| (data.short_name(kind), expression.matches(data.cfg(*kind))))
        .collect::<Vec<_>>();
    let name = |wanted: bool| {
        holds
            .iter()
            .filter(|(_, holds)| *holds == wanted)
            .map(|(name, _)| *name)
            .collect::<Vec<_>>()
            .join(", ")
    };
    if holds.iter().all(|(_, holds)| *holds) {
        return Ok(Ok(()));
    }
    // One run tests every target; a cfg that splits them has no one answer.
    anyhow::ensure!(
        holds.iter().all(|(_, holds)| !*holds),
        "`cfg = '{cfg}'` holds for {} and not for {}; run the plan for one target at a time",
        name(true),
        name(false)
    );
    Ok(Err(format!(
        "its `cfg = '{cfg}'` does not hold for {}",
        name(false)
    )))
}

/// The crate-level `#![cfg(..)]` of a library whose source is `text`: the
/// inner attributes at its head, before its first item (`all(..)` of
/// several), or `None`. Comments, a shebang and other inner attributes are
/// passed over; an attribute whose brackets do not close is an error.
fn library_gate(text: &str) -> Result<Option<CfgExpr>, String> {
    let mut rest = text;
    let mut gates = Vec::new();
    loop {
        rest = rest.trim_start();
        if let Some(comment) = rest.strip_prefix("//") {
            rest = comment.split_once('\n').map_or("", |(_, after)| after);
        } else if rest.starts_with("/*") {
            let mut depth = 0usize;
            let mut end = None;
            let bytes = rest.as_bytes();
            let mut at = 0;
            while at + 1 < bytes.len() {
                match &bytes[at..at + 2] {
                    b"/*" => {
                        depth += 1;
                        at += 2;
                    }
                    b"*/" => {
                        depth -= 1;
                        at += 2;
                        if depth == 0 {
                            end = Some(at);
                            break;
                        }
                    }
                    _ => at += 1,
                }
            }
            rest = &rest[end.ok_or("a block comment at its head does not end")?..];
        } else if let Some(attribute) = rest.strip_prefix("#!") {
            let Some(body) = attribute.trim_start().strip_prefix('[') else {
                // A shebang line.
                rest = attribute.split_once('\n').map_or("", |(_, after)| after);
                continue;
            };
            let (inner, after) = bracketed(body)?;
            rest = after;
            let inner = inner.trim();
            if let Some(predicate) = inner
                .strip_prefix("cfg")
                .map(str::trim_start)
                .and_then(|inner| inner.strip_prefix('('))
                .and_then(|inner| inner.strip_suffix(')'))
            {
                gates.push(
                    CfgExpr::from_str(predicate)
                        .map_err(|error| format!("its `#![cfg({predicate})]`: {error}"))?,
                );
            }
        } else {
            break;
        }
    }
    Ok(match gates.len() {
        0 => None,
        1 => gates.pop(),
        _ => Some(CfgExpr::All(gates)),
    })
}

/// `text` up to the `]` that closes an attribute opened just before it, and
/// what follows that `]`. Brackets inside string literals do not count.
fn bracketed(text: &str) -> Result<(&str, &str), String> {
    let mut depth = 0usize;
    let mut chars = text.char_indices();
    while let Some((at, c)) = chars.next() {
        match c {
            '"' => loop {
                match chars.next() {
                    Some((_, '\\')) => {
                        chars.next();
                    }
                    Some((_, '"')) => break,
                    Some(_) => {}
                    None => {
                        return Err("an attribute at its head has an unterminated string".into());
                    }
                }
            },
            '[' | '(' | '{' => depth += 1,
            ')' | '}' => depth = depth.saturating_sub(1),
            ']' if depth == 0 => return Ok((&text[..at], &text[at + 1..])),
            ']' => depth -= 1,
            _ => {}
        }
    }
    Err("an attribute at its head does not close".into())
}

/// Tests `own` as `targo test --tests` under its manifest does, as a plan
/// run of its own. Returns what the run concluded and why, or `None` for
/// `--no-run`. An error is a run that did not reach its end, or one whose
/// failure stops the invocation; it carries the tests the run reported, if it
/// ran to its end.
fn test_workspace(
    ws: &mut Workspace<'_>,
    outer: &CompileOptions,
    plan: &ResolvedPlan,
    own: &OwnWorkspace,
    no_run: bool,
    no_fail_fast: bool,
) -> Result<Option<(Outcome, String)>, (CliError, Option<u64>)> {
    let unreached = |error: anyhow::Error| (CliError::from(error), None);
    let default = DefaultRun {
        targets: DefaultTargets::Tests,
        // What the plan asks of each member it tests, it asks of these.
        min_tests: plan.plan.default.as_ref().and_then(|run| run.min_tests),
    };
    let text = TestPlan {
        schema: SCHEMA.to_owned(),
        select: Select {
            members: Members::DefaultMembers,
            attribute_under: Vec::new(),
            whole_plan_when_changed: Vec::new(),
            elsewhere: BTreeMap::new(),
            base: None,
        },
        default: Some(default),
        expect: None,
        // The phase runs under the invocation's clock (`plan_clock`), and in
        // the lane's pool: its harnesses take the plan's credits and are
        // counted for the plan's memory, as the members' are.
        run: Run {
            test_jobs: plan.plan.run.test_jobs,
            test_weight: plan.plan.run.test_weight,
            harness_memory_mib: plan.plan.run.harness_memory_mib,
            ..Default::default()
        },
        harness: BTreeMap::new(),
        variant: Vec::new(),
        instrument: Vec::new(),
        tool: Vec::new(),
        workspace: Vec::new(),
    };
    let phase = Phase {
        manifest: own.manifest.clone(),
        path: ws.root_manifest().to_path_buf(),
        withheld: plan.plan.tool.iter().map(|tool| tool.env.clone()).collect(),
        outcome: Rc::new(RefCell::new(None)),
    };
    let mut resolved =
        ResolvedPlan::resolve(ws, &plan.path, text, &[], plan_select::Input::default())
            .map_err(unreached)?;
    resolved.sha256 = plan.sha256.clone();
    resolved.phase = Some(phase.clone());
    let mut options = outer.clone();
    options.spec = resolved.packages();
    options.cli_features = CliFeatures::new_all(false);
    options.build_config.test_plan = Some(Rc::new(resolved));
    let options = TestOptions {
        no_run,
        no_fail_fast,
        required_test_bins: Vec::new(),
        compile_opts: options,
    };
    let result = super::run_tests(ws, &options, &[]);
    let outcome = *phase.outcome.borrow();
    let result = match (result, outcome) {
        // A workspace is listed to be tested. One whose run judged no test
        // (every test behind a cfg or a feature, or none written) has not
        // been, whether or not the plan sets a `min-tests`.
        (Ok(()), Some(outcome)) if outcome.passed && outcome.tests == 0 => {
            Err(CliError::from(anyhow::anyhow!(
                "its run reported 0 tests; a workspace that judges no test has not been tested"
            )))
        }
        (result, _) => result,
    };
    match (result, outcome) {
        (Ok(()), None) if no_run => Ok(None),
        (Ok(()), Some(outcome)) if outcome.passed => Ok(Some((
            outcome,
            format!("its run reported {} tests", outcome.tests),
        ))),
        // A run that reports success without a passing verdict is not one
        // this phase can vouch for.
        (Ok(()), _) => Err(unreached(anyhow::anyhow!(
            "its run ended without a passing verdict"
        ))),
        // The run ran to its end and failed: with `--no-fail-fast` what
        // follows still runs, and the failure is shown here, where it is.
        (Err(error), Some(outcome)) if no_fail_fast => {
            let why = match &error.error {
                Some(error) => {
                    crate::display_error(error, &mut ws.gctx().shell());
                    first_line(error)
                }
                None => format!("exit code {}", error.exit_code),
            };
            Ok(Some((
                Outcome {
                    passed: false,
                    ..outcome
                },
                why,
            )))
        }
        (Err(error), outcome) => Err((error, outcome.map(|outcome| outcome.tests))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const HEADER: &str =
        "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n";

    fn refusal(entries: &str) -> String {
        format!(
            "{:#}",
            TestPlan::parse(&format!("{HEADER}{entries}")).unwrap_err()
        )
    }

    #[test]
    fn an_entry_names_a_manifest_outside_the_root_and_a_tool_a_plain_variable() {
        let tool = |manifest: &str, env: &str, needed: &str| {
            format!(
                "[[tool]]\nmanifest = \"{manifest}\"\nbin = \"b\"\nenv = \"{env}\"\n\
                 needed-by = [{needed}]\n"
            )
        };
        TestPlan::parse(&format!(
            "{HEADER}{}[[workspace]]\nmanifest = \"own/Cargo.toml\"\ncfg = 'unix'\n",
            tool("t/Cargo.toml", "TOOL_BIN", "\"a\"")
        ))
        .unwrap();
        // A tool may be a package of the invocation's own workspace.
        TestPlan::parse(&format!("{HEADER}{}", tool("Cargo.toml", "E", "\"a\""))).unwrap();
        for (entries, expected) in [
            (
                tool("t/../Cargo.toml", "E", "\"a\""),
                "is not a `Cargo.toml` named by a normal path",
            ),
            (
                tool("/t/Cargo.toml", "E", "\"a\""),
                "is not a `Cargo.toml` named by a normal path",
            ),
            (
                tool("t/Other.toml", "E", "\"a\""),
                "is not a `Cargo.toml` named by a normal path",
            ),
            (
                tool("t/Cargo.toml", "1E", "\"a\""),
                "is not a variable name",
            ),
            (
                tool("t/Cargo.toml", "A B", "\"a\""),
                "is not a variable name",
            ),
            (tool("t/Cargo.toml", "", "\"a\""), "is not a variable name"),
            (
                tool("t/Cargo.toml", "CARGO_HOME", "\"a\""),
                "the build or the system reads",
            ),
            (
                tool("t/Cargo.toml", "PATH", "\"a\""),
                "the build or the system reads",
            ),
            (
                tool("t/Cargo.toml", "E", ""),
                "names no member in `needed-by`",
            ),
            (
                format!(
                    "{}{}",
                    tool("t/Cargo.toml", "E", "\"a\""),
                    tool("u/Cargo.toml", "E", "\"a\"")
                ),
                "both export `E`",
            ),
            (
                "[[workspace]]\nmanifest = \"own/Cargo.toml\"\n[[workspace]]\n\
                 manifest = \"own/Cargo.toml\"\n"
                    .to_owned(),
                "is listed twice",
            ),
            (
                "[[workspace]]\nmanifest = \"own/Cargo.toml\"\ncfg = 'all('\n".to_owned(),
                "is not a cfg expression",
            ),
            (
                "[[workspace]]\nmanifest = \"Cargo.toml\"\n".to_owned(),
                "is the invocation's own workspace",
            ),
        ] {
            let refusal = refusal(&entries);
            assert!(refusal.contains(expected), "{entries}: {refusal}");
        }
    }

    #[test]
    fn only_a_failed_workspace_is_unmet() {
        let row = |state| PhaseRow {
            kind: "workspace",
            manifest: "own/Cargo.toml".to_owned(),
            state,
            why: "1 target failed:".to_owned(),
            env: None,
            tests: Some(2),
        };
        assert_eq!(
            row(PhaseState::Failed).unmet().as_deref(),
            Some(
                "workspace `own/Cargo.toml` failed: 1 target failed: (its own records name \
                 the failures)"
            )
        );
        for state in [
            PhaseState::Built,
            PhaseState::NotNeeded,
            PhaseState::NotSelected,
            PhaseState::LeftOut,
            PhaseState::NotApplicable,
            PhaseState::Passed,
        ] {
            assert_eq!(row(state).unmet(), None);
        }
    }

    #[test]
    fn a_manifest_is_written_one_way() {
        let workspace = |manifest: &str| format!("[[workspace]]\nmanifest = \"{manifest}\"\n");
        let tool = |manifest: &str| {
            format!(
                "[[tool]]\nmanifest = \"{manifest}\"\nbin = \"b\"\nenv = \"E\"\n\
                 needed-by = [\"a\"]\n"
            )
        };
        // `Path::components` reads each of these as `own/Cargo.toml`.
        for manifest in [
            "own/./Cargo.toml",
            "own//Cargo.toml",
            "./own/Cargo.toml",
            "own/Cargo.toml/",
            "own/../own/Cargo.toml",
        ] {
            for entry in [workspace(manifest), tool(manifest)] {
                let refusal = refusal(&entry);
                assert!(
                    refusal.contains("is not a `Cargo.toml` named by a normal path"),
                    "{entry}: {refusal}"
                );
            }
        }
        // So one workspace cannot be listed twice under two spellings.
        let twice = refusal(&format!(
            "{}{}",
            workspace("own/Cargo.toml"),
            workspace("own//Cargo.toml")
        ));
        assert!(twice.contains("is not a `Cargo.toml` named by a normal path"));
    }

    #[test]
    fn a_librarys_gate_is_the_cfg_at_its_head() {
        let gate = |text: &str| library_gate(text).map(|gate| gate.map(|gate| gate.to_string()));
        assert_eq!(gate("pub fn f() {}\n"), Ok(None));
        assert_eq!(
            gate("#![cfg(target_os = \"linux\")]\n#![deny(unsafe_op_in_unsafe_fn)]\n"),
            Ok(Some("target_os = \"linux\"".to_owned()))
        );
        // Comments, doc comments, a shebang and other attributes (one over
        // several lines, with brackets in a string) come before it.
        assert_eq!(
            gate(
                "#!/usr/bin/env run\n// SPDX\n/* a /* nested */ block */\n//! Docs.\n\
                 #![cfg_attr(\n    all(unix, feature = \"a]\"),\n    feature(x)\n)]\n\
                 #![cfg(all(unix, not(target_os = \"none\")))]\npub mod m;\n"
            ),
            Ok(Some("all(unix, not(target_os = \"none\"))".to_owned()))
        );
        // Several are all of them; one after the first item is no gate.
        assert_eq!(
            gate("#![cfg(unix)]\n#![cfg(target_pointer_width = \"64\")]\n"),
            Ok(Some("all(unix, target_pointer_width = \"64\")".to_owned()))
        );
        assert_eq!(gate("pub mod m;\n#![cfg(unix)]\n"), Ok(None));
        assert_eq!(gate("#[cfg(unix)]\npub mod m;\n"), Ok(None));
        // What cannot be read is an error, never "ungated".
        assert!(gate("#![cfg(unix)\n").is_err());
        assert!(gate("#![cfg(=)]\n").is_err());
        assert!(gate("/* open\n#![cfg(unix)]\n").is_err());
    }

    #[test]
    fn a_cfg_tests_the_target_and_nothing_else() {
        let cfg =
            |cfg: &str| format!("[[workspace]]\nmanifest = \"own/Cargo.toml\"\ncfg = '{cfg}'\n");
        for accepted in [
            "unix",
            "windows",
            "target_os = \"linux\"",
            "all(unix, not(target_os = \"none\"))",
            "any(target_arch = \"x86_64\", target_pointer_width = \"64\")",
        ] {
            TestPlan::parse(&format!("{HEADER}{}", cfg(accepted)))
                .unwrap_or_else(|error| panic!("{accepted}: {error:#}"));
        }
        for (refused, atom) in [
            ("linux", "`linux` is not a cfg of the target"),
            ("test", "`test` is not a cfg of the target"),
            (
                "debug_assertions",
                "`debug_assertions` is not a cfg of the target",
            ),
            ("proc_macro", "`proc_macro` is not a cfg of the target"),
            (
                "feature = \"x\"",
                "`feature = \"x\"` is not a cfg of the target",
            ),
            (
                "panic = \"unwind\"",
                "`panic = \"unwind\"` is not a cfg of the target",
            ),
            (
                "target_feature = \"neon\"",
                "`target_feature = \"neon\"` is not a cfg of the target",
            ),
            (
                "all(unix, not(any(windows, miri)))",
                "`miri` is not a cfg of the target",
            ),
            ("false", "`false` is the same on every target"),
            ("all(unix, true)", "`true` is the same on every target"),
        ] {
            let refusal = refusal(&cfg(refused));
            assert!(refusal.contains(atom), "{refused}: {refusal}");
        }
    }

    #[test]
    fn the_compilers_known_values_are_read_from_its_check_cfg_lines() {
        let known = parse_check_cfg(
            "cfg(debug_assertions, values(none()))\n\
             cfg(target_abi, values(\"\", \"abi64\", \"x32\"))\n\
             cfg(target_has_atomic, values(\"8\", \"ptr\", none()))\n\
             cfg(target_os, values(\"linux\", \"macos\"))\n\
             not a line of it\n",
        );
        let values = |key: &str| known[key].iter().map(String::as_str).collect::<Vec<_>>();
        assert_eq!(values("debug_assertions"), [""; 0]);
        assert_eq!(values("target_abi"), ["", "abi64", "x32"]);
        assert_eq!(values("target_has_atomic"), ["8", "ptr"]);
        assert_eq!(values("target_os"), ["linux", "macos"]);
        assert_eq!(known.len(), 4);
        let mut tested = Vec::new();
        let expression =
            CfgExpr::from_str("all(unix, not(any(target_os = \"a\", target_env = \"\")))").unwrap();
        key_values(&expression, &mut |key, value| tested.push((key, value)));
        assert_eq!(tested, [("target_os", "a"), ("target_env", "")]);
    }
}
