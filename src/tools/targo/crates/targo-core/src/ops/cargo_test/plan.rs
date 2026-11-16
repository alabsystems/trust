//! Trust: `targo test --plan <FILE>`: several test requests in one build graph.
//!
//! A plan file names requests: the members' default run, feature variants of
//! one member, and instruments. Each request is what one `targo test -p ..`
//! command would select: its own packages, features and target filter. One
//! invocation resolves every active request on its own and builds the union
//! (`ops::cargo_compile::plan_graph`), so a request's units equal those of
//! its standalone command.
//!
//! Each test executable then runs once per distinct argument list of the
//! requests that selected it, always in the build's own queue
//! (`ops::cargo_test::graph`), and never beside another run of its test
//! target, under whatever features that run was built.
//!
//! Which requests one run performs is decided from what the invocation says
//! changed (`ops::cargo_test::plan_select`), and reported first.
//!
//! What the plan names outside this graph, a `[[tool]]` binary and a
//! `[[workspace]]` crate, is built and tested before the requests, each under
//! its own manifest (`ops::cargo_test::plan_phases`).
//!
//! The plan is a named file, never Cargo config: config merges the home
//! directory, the environment and `--config`, and a gate must read one source.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read as _;
use std::path::{Component, Path, PathBuf};
use std::rc::Rc;

use anyhow::Context as _;
use serde::Deserialize;

use super::harness_policy::HarnessPolicy;
use super::plan_expect::KnownRed;
use super::plan_phases::{self, BuiltTool, Phase, PhaseRow};
use super::plan_select::{
    self, Inputs, Layout, Owner, RequestRow, Selection, TestPlanRecord, UnattributedPaths,
};
use crate::context::{
    FeatureUnification, GlobalContext, TestHarnessConfig, TestHarnessPackageConfig,
};
use crate::ops::{CompileFilter, CompileOptions, Packages};
use crate::resolver::ResolveBehavior;
use crate::resolver::features::CliFeatures;
use crate::util::CargoResult;
use crate::util::restricted_names;
use crate::workspace::{Package, PackageIdSpec, PackageIdSpecQuery as _, Target, Workspace};

/// The only schema this Targo reads.
pub const SCHEMA: &str = "targo.test-plan.v1";
/// The id of the request made from `[default]`.
pub const DEFAULT_REQUEST: &str = "default";
/// Harness arguments with which libtest prints something and exits 0
/// without running a test.
const RUNS_NO_TEST: [&str; 3] = ["--list", "--help", "-h"];
/// The libtest formats that print the lines a plan run reads.
const PLAIN_FORMATS: [&str; 2] = ["pretty", "terse"];

/// A plan file as written. Unknown keys are errors at every level.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct TestPlan {
    pub schema: String,
    pub select: Select,
    pub default: Option<DefaultRun>,
    pub expect: Option<Expect>,
    /// The bounds of a run of the plan.
    #[serde(default)]
    pub run: Run,
    #[serde(default)]
    pub harness: BTreeMap<String, HarnessTargets>,
    #[serde(default)]
    pub variant: Vec<Variant>,
    #[serde(default)]
    pub instrument: Vec<Instrument>,
    #[serde(default)]
    pub tool: Vec<Tool>,
    #[serde(default)]
    pub workspace: Vec<OwnWorkspace>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct Select {
    pub members: Members,
    /// Directories whose every changed path must belong to a plan member.
    #[serde(default)]
    pub attribute_under: Vec<String>,
    /// Path prefixes of the lane's own policy: a changed path under one
    /// runs every request, as `--whole-plan` does. The plan file and its
    /// known-red file belong here: a change to either changes what every
    /// request's result means.
    #[serde(default)]
    pub whole_plan_when_changed: Vec<String>,
    /// Members another lane tests, each with the command that does.
    #[serde(default)]
    pub elsewhere: BTreeMap<String, String>,
    /// The revision a new branch is compared with: `--changed-pushed-refs`
    /// reads a pushed branch the remote does not have as `<base>...<sha>`.
    pub base: Option<String>,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum Members {
    /// The workspace's `default-members`.
    DefaultMembers,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct DefaultRun {
    pub targets: DefaultTargets,
    /// Tests each member must report, summed over this run and its variants.
    pub min_tests: Option<u64>,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum DefaultTargets {
    /// `--tests`: every target with `test = true`.
    Tests,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct Expect {
    pub known_red: Option<String>,
}

/// What bounds a run of the plan. A bound is policy of the lane, so it is
/// in the file with the rest; `build.test-wall-seconds` and
/// `build.test-stall-seconds` override it on a host that needs another.
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct Run {
    /// Seconds the whole invocation may take: phases, build and tests.
    pub wall_seconds: Option<u64>,
    /// Seconds per member the run tests; the bound is the larger of this
    /// product and `wall-seconds`.
    pub wall_seconds_per_member: Option<u64>,
    /// Seconds a running test executable may go without printing a line.
    pub stall_seconds: Option<u64>,
    /// Credits the run's test executables may hold together: the plan's
    /// `build.test-jobs`, which stands where the configuration sets none.
    pub test_jobs: Option<usize>,
    /// Credits (and libtest threads) of each harness without a `weight` of
    /// its own: the plan's `build.test-weight`, which stands where the
    /// configuration sets none. On a pool that cannot grant more than one
    /// credit at once it lowers to 1.
    pub test_weight: Option<usize>,
    /// Seconds a run held at a barrier (`--run-after`) waits for it with
    /// nothing else to do; such a run is refused without it.
    pub run_after_seconds: Option<u64>,
    /// Mebibytes each test executable is counted for against the memory
    /// budget, unless its `[harness]` entry says otherwise. Without it (and
    /// without any `memory-mib`) memory admits nothing and refuses nothing.
    pub harness_memory_mib: Option<usize>,
}

impl Run {
    fn check(&self) -> CargoResult<()> {
        for (key, value) in [
            ("wall-seconds", self.wall_seconds),
            ("wall-seconds-per-member", self.wall_seconds_per_member),
            ("stall-seconds", self.stall_seconds),
            ("run-after-seconds", self.run_after_seconds),
            (
                "harness-memory-mib",
                self.harness_memory_mib.map(|mib| mib as u64),
            ),
            ("test-jobs", self.test_jobs.map(|jobs| jobs as u64)),
            ("test-weight", self.test_weight.map(|weight| weight as u64)),
        ] {
            anyhow::ensure!(value != Some(0), "`[run] {key}` must be 1 or more");
        }
        Ok(())
    }
}

/// One package's harness settings, spelled like `build.test-harnesses`.
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct HarnessTargets {
    pub lib: Option<Harness>,
    #[serde(default)]
    pub bin: BTreeMap<String, Harness>,
    #[serde(default)]
    pub test: BTreeMap<String, Harness>,
    #[serde(default)]
    pub bench: BTreeMap<String, Harness>,
    #[serde(default)]
    pub example: BTreeMap<String, Harness>,
}

impl HarnessTargets {
    /// Every entry names a target `package` has; a misspelt one would set
    /// nothing and say nothing.
    fn check_targets(&self, package: &Package) -> CargoResult<()> {
        let name = package.name();
        let has = |kind: fn(&Target) -> bool, target: &str| {
            package
                .targets()
                .iter()
                .any(|found| kind(found) && found.name() == target)
        };
        anyhow::ensure!(
            self.lib.is_none() || package.targets().iter().any(Target::is_lib),
            "`[harness.{name}.lib]`: package `{name}` has no lib target"
        );
        let named: [(&str, &BTreeMap<String, Harness>, fn(&Target) -> bool); 4] = [
            ("bin", &self.bin, Target::is_bin),
            ("test", &self.test, Target::is_test),
            ("bench", &self.bench, Target::is_bench),
            ("example", &self.example, Target::is_example),
        ];
        for (kind, entries, is_kind) in named {
            for target in entries.keys() {
                anyhow::ensure!(
                    has(is_kind, target),
                    "`[harness.{name}.{kind}.{target}]`: package `{name}` has no {kind} target \
                     `{target}`"
                );
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Default, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct Harness {
    pub weight: Option<usize>,
    pub exclusive: Option<bool>,
    /// Mebibytes the harness is counted for against the memory budget.
    pub memory_mib: Option<usize>,
    /// Expected run time in seconds; the longest ready harness starts first.
    pub seconds: Option<u64>,
}

/// A second run of one member under other features.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct Variant {
    pub id: String,
    pub package: String,
    #[serde(default)]
    pub features: Vec<String>,
    #[serde(default)]
    pub lib: bool,
    #[serde(default)]
    pub test: Vec<String>,
}

/// A run that judges something outside its host package.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct Instrument {
    pub id: String,
    pub package: String,
    #[serde(default)]
    pub lib: bool,
    #[serde(default)]
    pub test: Vec<String>,
    /// Arguments for the harness, as after `--`.
    #[serde(default)]
    pub args: Vec<String>,
    #[serde(default)]
    pub when_changed: Vec<String>,
    pub when_changed_suffix: Option<String>,
    #[serde(default)]
    pub not_under: Vec<String>,
    #[serde(default)]
    pub require_pass: Vec<String>,
}

/// A binary that a member's tests run, built as `targo build` builds it
/// under its manifest: in another workspace, or a member of this one.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct Tool {
    /// The manifest that builds it, from this workspace's root.
    pub manifest: String,
    pub bin: String,
    /// The variable that names the built file to the tests that need it.
    pub env: String,
    /// The members whose test executables run it.
    #[serde(default)]
    pub needed_by: Vec<String>,
}

/// A crate that is its own workspace.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct OwnWorkspace {
    /// Its root manifest, from this workspace's root.
    pub manifest: String,
    /// A cfg expression its tests need of the target; where it does not
    /// hold, the workspace is not run.
    pub cfg: Option<String>,
}

impl TestPlan {
    /// Parses and checks a plan without a workspace: the schema, every key,
    /// and that each request has an id of its own and selects a target.
    pub fn parse(text: &str) -> CargoResult<TestPlan> {
        let plan: TestPlan = toml::from_str(text)?;
        anyhow::ensure!(
            plan.schema == SCHEMA,
            "schema `{}` is not `{SCHEMA}`",
            plan.schema
        );
        plan.run.check()?;
        let mut ids = BTreeSet::new();
        let runs = plan
            .variant
            .iter()
            .map(|run| ("variant", &run.id, run.lib, &run.test))
            .chain(
                plan.instrument
                    .iter()
                    .map(|run| ("instrument", &run.id, run.lib, &run.test)),
            );
        for (role, id, lib, test) in runs {
            anyhow::ensure!(!id.is_empty(), "a {role} has an empty id");
            // An id is typed after `--request` and printed in the command
            // that reruns a failure, so it is one plain shell word that no
            // option parser reads as a flag.
            anyhow::ensure!(
                id.bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || b"_.-".contains(&byte))
                    && !id.starts_with('-'),
                "{role} id `{id}` is not a plain word: use ASCII letters, digits, `_`, `.` and \
                 `-`, not starting with `-`"
            );
            anyhow::ensure!(
                id != DEFAULT_REQUEST,
                "{role} id `{DEFAULT_REQUEST}` names the `[default]` request"
            );
            anyhow::ensure!(ids.insert(id.as_str()), "request id `{id}` is used twice");
            anyhow::ensure!(
                lib || !test.is_empty(),
                "{role} `{id}` selects no target; set `lib = true` or name a `test`"
            );
            // A plan names exact targets: a pattern would select whatever
            // matches on the day, and an empty name selects nothing.
            for name in test {
                anyhow::ensure!(!name.is_empty(), "{role} `{id}` names an empty `test`");
                anyhow::ensure!(
                    !restricted_names::is_glob_pattern(name),
                    "{role} `{id}` names test `{name}`; a plan names each test target exactly, \
                     not by pattern"
                );
            }
        }
        // `min-tests = 0` asks nothing and reads as a requirement.
        anyhow::ensure!(
            plan.default.as_ref().and_then(|run| run.min_tests) != Some(0),
            "`[default] min-tests = 0` requires nothing; leave it out or require a test"
        );
        // A condition is matched as text against each changed path; an empty
        // one matches every path and reads as a condition.
        let conditions = plan
            .select
            .attribute_under
            .iter()
            .map(|prefix| ("`select.attribute-under`".to_owned(), prefix))
            .chain(
                plan.select
                    .whole_plan_when_changed
                    .iter()
                    .map(|prefix| ("`select.whole-plan-when-changed`".to_owned(), prefix)),
            )
            .chain(plan.instrument.iter().flat_map(|run| {
                let named = |key: &str| format!("instrument `{}`: `{key}`", run.id);
                (run.when_changed
                    .iter()
                    .map(move |text| (named("when-changed"), text)))
                .chain(
                    run.not_under
                        .iter()
                        .map(move |text| (named("not-under"), text)),
                )
                .chain(
                    run.when_changed_suffix
                        .iter()
                        .map(move |text| (named("when-changed-suffix"), text)),
                )
            }));
        for (key, text) in conditions {
            anyhow::ensure!(
                !text.is_empty(),
                "{key} has an empty entry, which every path matches"
            );
        }
        for run in &plan.instrument {
            for name in &run.require_pass {
                // A result line is `test <name> ... ok` (`test <name> - should
                // panic ... ok` for a `#[should_panic]` test, which is named
                // here by its path alone); a name that is not one whole test
                // path could never match one.
                anyhow::ensure!(
                    !name.is_empty() && !name.contains(char::is_whitespace),
                    "instrument `{}` has a `require-pass` entry `{name}` that is not a test's \
                     full path",
                    run.id
                );
            }
        }
        plan_phases::check_entries(&plan)?;
        Ok(plan)
    }
}

/// Why a request is in the plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RequestRole {
    Default,
    Variant,
    Instrument,
}

impl RequestRole {
    fn name(self) -> &'static str {
        match self {
            RequestRole::Default => "default",
            RequestRole::Variant => "variant",
            RequestRole::Instrument => "instrument",
        }
    }
}

/// One active request: what a standalone `targo test` command would select.
#[derive(Clone, Debug)]
pub struct PlanRequest {
    pub id: String,
    pub role: RequestRole,
    pub packages: Packages,
    pub cli_features: CliFeatures,
    pub filter: CompileFilter,
    /// Arguments for this request's harnesses.
    pub args: Vec<String>,
}

/// A plan bound to a workspace and narrowed to the requests of this run.
#[derive(Clone, Debug)]
pub struct ResolvedPlan {
    pub path: PathBuf,
    pub plan: TestPlan,
    /// The requests of this run: those the selection performs, after
    /// `--request` narrowing. A request index anywhere in the build is an
    /// index into this list, not into the file's order.
    pub requests: Vec<PlanRequest>,
    /// The package names of the members `[default]` tests in this run (the
    /// selected ones); empty without a `[default]`.
    pub members: Vec<String>,
    /// `--request` left out some request the selection performs.
    pub narrowed: bool,
    /// `--request` left out `[default]` or a variant the selection performs:
    /// this run has only part of the sum `min-tests` asks of a member. An
    /// instrument credits no member, so leaving one out takes nothing from
    /// the sum.
    pub sum_partial: bool,
    /// SHA-256 of the plan file's bytes, in hex.
    pub sha256: String,
    /// What the invocation said changed, as given.
    pub input: plan_select::Input,
    /// The `--request` ids, as given.
    pub only: Vec<String>,
    /// The changed paths attributed to the plan's members.
    pub selection: Selection,
    /// Every request of the file, performed by this run or not, in the
    /// order of `requests`.
    pub rows: Vec<RequestRow>,
    /// The rows of the `[expect] known-red` file, if the plan names one.
    pub known_red: Option<KnownRed>,
    /// Set on the plan of a `[[workspace]]` phase: this is the run of that
    /// workspace's own manifest, not of the plan file's workspace.
    pub phase: Option<Phase>,
    /// What became of each `[[tool]]` and `[[workspace]]` entry, once the
    /// phases ran (`plan_phases::run`); empty before, and in a phase.
    pub phases: Vec<PhaseRow>,
    /// The tools this run built for its test executables.
    pub tools: Vec<BuiltTool>,
}

impl ResolvedPlan {
    /// Reads `path` and resolves its requests against `ws`. `input` selects
    /// the requests this run performs; `only` then narrows the run to the
    /// named request ids, empty meaning every one selected.
    pub fn load(
        ws: &Workspace<'_>,
        path: &Path,
        only: &[String],
        input: plan_select::Input,
    ) -> CargoResult<ResolvedPlan> {
        let text = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read test plan `{}`", path.display()))?;
        let plan = TestPlan::parse(&text)
            .with_context(|| format!("invalid test plan `{}`", path.display()))?;
        let mut resolved = Self::resolve(ws, path, plan, only, input).with_context(|| {
            format!("test plan `{}` does not fit this workspace", path.display())
        })?;
        resolved.sha256 = cargo_util::Sha256::new()
            .update(text.as_bytes())
            .finish_hex();
        // Read on every route, so that a plan whose ratchet file is missing
        // or malformed is refused by a build as by a run. Like a changed
        // path, the file is named from the workspace root.
        let known_red = resolved
            .plan
            .expect
            .as_ref()
            .and_then(|expect| expect.known_red.as_deref());
        if let Some(file) = known_red {
            let known = KnownRed::load(ws.root(), file)
                .with_context(|| format!("test plan `{}`", path.display()))?;
            // A row names its binary by crate name. Every target a run of
            // this plan may test is counted, whatever this run selects, so
            // that what a row excuses does not depend on the selection.
            let mut carriers = BTreeMap::<String, Vec<String>>::new();
            let elsewhere = &resolved.plan.select.elsewhere;
            for package in ws.members() {
                if elsewhere.contains_key(package.name().as_str()) {
                    continue;
                }
                for target in package.targets() {
                    if target.is_lib() || target.is_bin() || target.is_test() || target.tested() {
                        carriers
                            .entry(target.crate_name())
                            .or_default()
                            .push(format!(
                                "{} `{}` of `{}`",
                                super::harness_policy::kind_key(target),
                                target.name(),
                                package.name()
                            ));
                    }
                }
            }
            known
                .require_one_binary(&carriers)
                .with_context(|| format!("test plan `{}`", path.display()))?;
            resolved.known_red = Some(known);
        }
        Ok(resolved)
    }

    pub(super) fn resolve(
        ws: &Workspace<'_>,
        path: &Path,
        plan: TestPlan,
        only: &[String],
        input: plan_select::Input,
    ) -> CargoResult<ResolvedPlan> {
        // Resolver 1 unifies features over the whole workspace, so a request
        // could not equal its standalone command.
        anyhow::ensure!(
            ws.resolve_behavior() != ResolveBehavior::V1,
            "a test plan requires feature resolver 2 or later"
        );
        // A member's name can also be a dependency's; its full spec cannot.
        let package_of: BTreeMap<&str, &Package> = ws
            .members()
            .map(|member| (member.name().as_str(), member))
            .collect();
        let spec_of: BTreeMap<&str, String> = package_of
            .iter()
            .map(|(name, member)| (*name, member.package_id().to_spec().to_string()))
            .collect();
        for name in plan.select.elsewhere.keys() {
            anyhow::ensure!(
                spec_of.contains_key(name.as_str()),
                "`select.elsewhere` names `{name}`, which is not a workspace member"
            );
        }
        let Members::DefaultMembers = plan.select.members;
        let members: BTreeSet<&str> = ws
            .default_members()
            .map(|member| member.name().as_str())
            .filter(|name| !plan.select.elsewhere.contains_key(*name))
            .collect();

        // The members some request tests. Without a `[default]` that is the
        // packages of the variants: a path or `-p` of any other member would
        // select nothing and exit as if it had been tested.
        let tested: BTreeSet<&str> = if plan.default.is_some() {
            members.clone()
        } else {
            plan.variant
                .iter()
                .map(|run| run.package.as_str())
                .filter(|name| members.contains(name))
                .collect()
        };
        let mut reached = reached_members(ws, &plan, &members, &tested, &input.packages)?;
        let (layout, unplaced) = layout(ws, &plan, &members, &tested);
        let (by_directory, reached_workspaces) = reached_directories(&layout, &input.reached)?;
        reached.extend(by_directory);
        // A changed path is relative to the workspace root, so none can name
        // a file of a member outside it: its changes would never select it.
        if input.changed_paths.is_some()
            && let Some(name) = unplaced.iter().find(|name| members.contains(name.as_str()))
        {
            anyhow::bail!(
                "--changed-paths cannot select for this plan: plan member `{name}` has no \
                 directory under the workspace root, so no changed path can name its files"
            );
        }
        let mut selection = Selection::attribute(
            &layout,
            &plan.select.attribute_under,
            &plan.select.whole_plan_when_changed,
            &input,
            &members,
            reached,
        );
        // A `[[workspace]]` named by its directory is performed as one a
        // changed path lies in is.
        selection.workspaces.extend(reached_workspaces);

        // Every request of the file with whether the selection performs it.
        let mut candidates = Vec::new();
        let mut default_members = Vec::new();
        if let Some(default) = &plan.default {
            let DefaultTargets::Tests = default.targets;
            // A `[default]` that tests nothing is a plan that lost its
            // members, not a plan of variants and instruments only.
            anyhow::ensure!(
                !members.is_empty(),
                "`[default]` selects no member: the workspace has no default member that \
                 `select.elsewhere` leaves to this plan"
            );
            // `[default]` tests the selected members, as one command over
            // them would.
            default_members.extend(
                members
                    .iter()
                    .filter(|name| selection.selected.contains(**name))
                    .map(|name| (*name).to_owned()),
            );
            candidates.push((
                PlanRequest {
                    id: DEFAULT_REQUEST.to_owned(),
                    role: RequestRole::Default,
                    packages: Packages::Packages(
                        default_members
                            .iter()
                            .map(|name| spec_of[name.as_str()].clone())
                            .collect(),
                    ),
                    cli_features: CliFeatures::new_all(false),
                    filter: target_filter(false, &[], true),
                    args: Vec::new(),
                },
                default_members.clone(),
                selection.default_run(),
            ));
        }
        for run in &plan.variant {
            anyhow::ensure!(
                members.contains(run.package.as_str()),
                "variant `{}` names package `{}`, which is not a plan member",
                run.id,
                run.package
            );
            candidates.push((
                PlanRequest {
                    id: run.id.clone(),
                    role: RequestRole::Variant,
                    packages: Packages::Packages(vec![spec_of[run.package.as_str()].clone()]),
                    cli_features: CliFeatures::from_command_line(&run.features, false, true)
                        .with_context(|| format!("variant `{}`", run.id))?,
                    filter: target_filter(run.lib, &run.test, false),
                    args: Vec::new(),
                },
                vec![run.package.clone()],
                selection.variant(&run.package),
            ));
        }
        // An instrument's host may be any member this lane can build: one
        // outside the default members, but never one another lane owns.
        let hosted_here = |what: &str, package: &str| -> CargoResult<()> {
            anyhow::ensure!(
                spec_of.contains_key(package),
                "{what} names package `{package}`, which is not a workspace member"
            );
            if let Some(owner) = plan.select.elsewhere.get(package) {
                anyhow::bail!(
                    "{what} names package `{package}`, which `select.elsewhere` leaves to \
                     `{owner}`"
                );
            }
            Ok(())
        };
        for (package, targets) in &plan.harness {
            let what = format!("`[harness.{package}]`");
            hosted_here(&what, package)?;
            targets.check_targets(package_of[package.as_str()])?;
        }
        // A tool is built when a request tests a member that needs it; a
        // name no request can test would leave it unbuilt in silence.
        for tool in &plan.tool {
            for name in &tool.needed_by {
                hosted_here(
                    &format!("`[[tool]]` `{}`: `needed-by`", tool.manifest),
                    name,
                )?;
            }
        }
        for run in &plan.instrument {
            hosted_here(&format!("instrument `{}`", run.id), &run.package)?;
            let spec = &spec_of[run.package.as_str()];
            // The default run tests a host only if the host is its member,
            // and then only what `--tests` with no argument performs.
            let covered = if plan.default.is_some() && members.contains(run.package.as_str()) {
                default_run_covers(run, package_of[run.package.as_str()])
            } else {
                Err("no default run tests it".to_owned())
            };
            candidates.push((
                PlanRequest {
                    id: run.id.clone(),
                    role: RequestRole::Instrument,
                    packages: Packages::Packages(vec![spec.clone()]),
                    cli_features: CliFeatures::new_all(false),
                    filter: target_filter(run.lib, &run.test, false),
                    args: run.args.clone(),
                },
                vec![run.package.clone()],
                selection.instrument(run, &covered),
            ));
        }

        let mut requests = Vec::new();
        let mut rows = Vec::new();
        for (request, packages, decision) in candidates {
            rows.push(RequestRow {
                id: request.id.clone(),
                role: request.role.name(),
                packages,
                active: decision.active,
                why: decision.why,
            });
            if decision.active {
                requests.push(request);
            }
        }
        // A change to a tool is tested by the tests that run it. Where no
        // request of the selection tests a member that does, the run would
        // exit as if the change had been tested.
        for tool in &selection.tools {
            let tested = rows.iter().any(|row| {
                row.active && row.packages.iter().any(|name| tool.members.contains(name))
            });
            anyhow::ensure!(
                tested,
                "`{}` changed, in the directory of tool `{}`, and no request of the plan \
                 tests a member that runs it ({}); this run would be read as having tested it",
                tool.paths[0],
                tool.manifest,
                tool.members.join(", ")
            );
        }
        for id in only {
            let Some(row) = rows.iter().find(|row| row.id == *id) else {
                anyhow::bail!(
                    "--request `{id}` is not a request of the plan; it has: {}",
                    rows.iter()
                        .map(|row| row.id.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            };
            // `--request` narrows what the selection performs; it never
            // adds a request the selection left out.
            anyhow::ensure!(
                row.active,
                "--request `{id}` is not performed under this selection: {}",
                row.why
            );
        }
        let all = requests.len();
        let mut sum_partial = false;
        if !only.is_empty() {
            sum_partial = requests.iter().any(|request| {
                request.role != RequestRole::Instrument && !only.contains(&request.id)
            });
            requests.retain(|request| only.contains(&request.id));
            for row in rows.iter_mut().filter(|row| row.active) {
                if !only.contains(&row.id) {
                    row.active = false;
                    row.why = "left out by --request".to_owned();
                }
            }
        }
        // A selection may perform nothing; a plan with nothing to perform
        // is not a plan.
        anyhow::ensure!(
            !requests.is_empty() || !selection.whole_plan,
            "the plan selects no request"
        );
        Ok(ResolvedPlan {
            path: path.to_path_buf(),
            plan,
            narrowed: requests.len() < all,
            sum_partial,
            requests,
            members: default_members,
            sha256: String::new(),
            input,
            only: only.to_vec(),
            selection,
            rows,
            known_red: None,
            phase: None,
            phases: Vec::new(),
            tools: Vec::new(),
        })
    }

    /// The plan's `[harness]` entries as the harness policy reads them. A
    /// plan run takes its policy from here and from nowhere else
    /// (`HarnessPolicy::load`).
    pub(crate) fn harness_config(&self) -> BTreeMap<String, TestHarnessPackageConfig> {
        let entry = |harness: &Harness| TestHarnessConfig {
            weight: harness.weight,
            exclusive: harness.exclusive,
            memory_mib: harness.memory_mib,
            seconds: harness.seconds,
        };
        let named = |targets: &BTreeMap<String, Harness>| {
            (!targets.is_empty()).then(|| {
                targets
                    .iter()
                    .map(|(name, harness)| (name.clone(), entry(harness)))
                    .collect()
            })
        };
        self.plan
            .harness
            .iter()
            .map(|(package, targets)| {
                (
                    package.clone(),
                    TestHarnessPackageConfig {
                        lib: targets.lib.as_ref().map(entry),
                        bin: named(&targets.bin),
                        test: named(&targets.test),
                        bench: named(&targets.bench),
                        example: named(&targets.example),
                    },
                )
            })
            .collect()
    }

    /// The `test-plan` record: the first line of a plan invocation's JSON.
    pub(crate) fn record(&self) -> String {
        self.record_with(None)
    }

    /// The `test-plan` record of a `--select-only` listing: the same record,
    /// with what a run would do with each `[[tool]]` and `[[workspace]]`.
    fn record_with(&self, phases: Option<&[super::plan_phases::PhaseRow]>) -> String {
        use crate::util::machine_message::Message as _;
        TestPlanRecord {
            phases,
            schema: plan_select::TEST_PLAN_SELECTION_SCHEMA_V1,
            plan: self.path.to_string_lossy().into_owned(),
            sha256: &self.sha256,
            selection: Inputs {
                changed_paths: self.input.changed_paths.as_deref(),
                changed_ranges: &self.input.ranges,
                packages: &self.input.packages,
                reached: &self.input.reached,
                whole_plan: self.selection.whole_plan,
                requests: &self.only,
            },
            members: plan_select::Members {
                touched: &self.selection.touched,
                reached: &self.selection.reached,
                selected: &self.selection.selected,
            },
            requests: &self.rows,
            elsewhere: &self.selection.elsewhere,
            workspaces: &self.selection.workspaces,
            tools: &self.selection.tools,
            unattributed: &self.selection.unattributed,
        }
        .to_json_string()
    }

    /// Tells a person what a selection left of the plan.
    fn report(&self, gctx: &GlobalContext) -> CargoResult<()> {
        let mut shell = gctx.shell();
        if let Some((path, prefix)) = &self.selection.whole_because {
            shell.status(
                "Selected",
                format!(
                    "every request of the plan: changed path `{path}` is under `{prefix}` \
                     (`select.whole-plan-when-changed`)"
                ),
            )?;
        }
        if !self.selection.whole_plan {
            let active = self
                .rows
                .iter()
                .filter(|row| row.active)
                .map(|row| row.id.as_str())
                .collect::<Vec<_>>();
            shell.status(
                "Selected",
                format!(
                    "{} of {} plan requests{}{}",
                    active.len(),
                    self.rows.len(),
                    if active.is_empty() { "" } else { ": " },
                    active.join(", ")
                ),
            )?;
        }
        // A changed member this plan does not test is named with the lane
        // that does, never summarised away.
        for elsewhere in &self.selection.elsewhere {
            shell.note(format!(
                "`{}` changed ({} path{}) and this plan does not test it; `{}` does",
                elsewhere.member,
                elsewhere.paths.len(),
                if elsewhere.paths.len() == 1 { "" } else { "s" },
                elsewhere.command
            ))?;
        }
        Ok(())
    }

    /// The tests each member of `[default]` must report in this run, if the
    /// run can show them. `min-tests` sums a member's default run and its
    /// variants; a run from which `--request` left one of those out has only
    /// part of the sum, so it judges none of it (`require_honored` and the
    /// result record say so).
    pub(crate) fn min_tests(&self) -> Option<u64> {
        let min_tests = self.plan.default.as_ref()?.min_tests?;
        (!self.sum_partial).then_some(min_tests)
    }

    /// The plan sets `[default] min-tests`, judged in this run or not.
    pub(crate) fn min_tests_set(&self) -> bool {
        self.plan
            .default
            .as_ref()
            .is_some_and(|run| run.min_tests.is_some())
    }

    /// The actions one test executable runs as, given the requests (indices
    /// into `requests`, ascending) that selected it: one per distinct
    /// argument list, in plan order, each with the ids of the requests it
    /// runs for. Requests with the same arguments would run the same process
    /// twice, so they share one action and it credits them all.
    pub(crate) fn actions(&self, requests: &[usize]) -> Vec<(Vec<String>, Vec<String>)> {
        let mut actions: Vec<(Vec<String>, Vec<String>)> = Vec::new();
        for request in requests.iter().map(|index| &self.requests[*index]) {
            match actions.iter_mut().find(|(args, _)| *args == request.args) {
                Some((_, ids)) => ids.push(request.id.clone()),
                None => actions.push((request.args.clone(), vec![request.id.clone()])),
            }
        }
        actions
    }

    /// Checks each request's harness arguments as the command line's are
    /// checked, naming the request. A plan's arguments are read by a gate
    /// from a checked-in file, so one that makes the harness exit 0 without
    /// running a test is refused here too. Every request of the file is
    /// checked, performed by this run or not (only an instrument has
    /// arguments): what the file may say does not depend on what changed.
    fn validate_arguments(&self) -> CargoResult<()> {
        for request in &self.plan.instrument {
            let args = request.args.iter().map(String::as_str).collect::<Vec<_>>();
            let named = || {
                format!(
                    "test plan `{}`, request `{}`",
                    self.path.display(),
                    request.id
                )
            };
            super::validate_native_test_arguments(&args).with_context(named)?;
            if let Some(inert) = args.iter().find(|arg| RUNS_NO_TEST.contains(arg)) {
                return Err(anyhow::anyhow!(
                    "`{inert}` makes a test harness exit successfully without running a test"
                )
                .context(named()));
            }
            // A plan run reads libtest's `running N tests`, result and
            // closing lines; another format prints none of them.
            let mut rest = args.iter();
            while let Some(arg) = rest.next() {
                let format = match arg.strip_prefix("--format") {
                    Some("") => rest.next().copied(),
                    Some(value) => value.strip_prefix('='),
                    None => None,
                };
                if let Some(format) = format.filter(|format| !PLAIN_FORMATS.contains(format)) {
                    return Err(anyhow::anyhow!(
                        "`--format {format}` replaces the result lines a plan run reads; a \
                         request's harness prints libtest's `pretty` or `terse` format"
                    )
                    .context(named()));
                }
            }
        }
        Ok(())
    }

    /// The arguments that rerun an action credited to the requests `ids`:
    /// the plan and one of them. Any of them selects the action's executable
    /// with its arguments; one other than `[default]` selects a single
    /// package and is the narrower run. The result is pasted into a shell.
    pub(super) fn rerun(&self, ids: &[String]) -> Option<Rerun> {
        // A `[[workspace]]` phase has no request of the plan file to name;
        // it is the run of its own manifest, which is a command of its own:
        // added to this invocation, `--manifest-path` would run the plan
        // against that workspace.
        if let Some(phase) = &self.phase {
            return Some(Rerun::Command(format!(
                "targo --unverified test --manifest-path {} --tests",
                shell_escape::escape(phase.path.to_string_lossy())
            )));
        }
        let id = ids
            .iter()
            .find(|id| *id != DEFAULT_REQUEST)
            .or(ids.first())?;
        let path = self.path.to_string_lossy();
        // Ids are plain words (`TestPlan::parse`); the path is anything.
        Some(Rerun::Arguments(format!(
            "--plan {} --request {id}",
            shell_escape::escape(path)
        )))
    }

    /// What tells two runs of one executable apart in a `Running` line: the
    /// requests of the action, or in a `[[workspace]]` phase, whose one
    /// request is not the plan's `[default]`, the workspace.
    pub(crate) fn label(&self, ids: &[String]) -> String {
        match &self.phase {
            Some(phase) => format!("workspace {}", phase.manifest),
            None => ids.join(", "),
        }
    }

    /// Who requires an action credited to the requests `ids` to judge a
    /// test: an instrument judges something outside its host package, and
    /// nothing else in the plan would notice that it ran no test.
    pub(crate) fn must_judge(&self, ids: &[String]) -> Option<String> {
        self.requests
            .iter()
            .find(|request| request.role == RequestRole::Instrument && ids.contains(&request.id))
            .map(|request| format!("instrument `{}`", request.id))
    }

    /// Refuses a run in which some request has no action. `credited` holds
    /// the request ids of the run's actions. A request that selected no test
    /// executable would otherwise pass by running nothing.
    pub(crate) fn require_actions<'a>(
        &self,
        credited: impl IntoIterator<Item = &'a String>,
    ) -> CargoResult<()> {
        let credited: BTreeSet<&str> = credited.into_iter().map(String::as_str).collect();
        let idle = self
            .requests
            .iter()
            .map(|request| request.id.as_str())
            .filter(|id| !credited.contains(id))
            .collect::<Vec<_>>();
        anyhow::ensure!(
            idle.is_empty(),
            "test plan `{}`: no test executable was selected for request{} `{}`; a run of \
             nothing would pass",
            self.path.display(),
            if idle.len() == 1 { "" } else { "s" },
            idle.join("`, `")
        );
        Ok(())
    }

    /// Refuses a finished run that left actions unrun for no reported
    /// reason. `blocked` holds the requests of each action that never ran;
    /// `explained` says the run already reports a failure or interruption.
    pub(super) fn require_all_ran(
        &self,
        blocked: &[&[String]],
        explained: bool,
    ) -> CargoResult<()> {
        anyhow::ensure!(
            explained || blocked.is_empty(),
            "test plan `{}`: {} test action{} never ran though nothing failed (request{} `{}`)",
            self.path.display(),
            blocked.len(),
            if blocked.len() == 1 { "" } else { "s" },
            if blocked.iter().map(|ids| ids.len()).sum::<usize>() == 1 {
                ""
            } else {
                "s"
            },
            blocked
                .iter()
                .flat_map(|ids| ids.iter().map(String::as_str))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
                .join("`, `")
        );
        Ok(())
    }

    /// The members this run tests that need `tool`: the packages of the
    /// requests it performs that `needed-by` names, in the tool's order.
    pub(super) fn consumers(&self, tool: &Tool) -> Vec<String> {
        tool.needed_by
            .iter()
            .filter(|name| {
                self.rows
                    .iter()
                    .any(|row| row.active && row.packages.contains(name))
            })
            .cloned()
            .collect()
    }

    /// Hands a test executable of `package` the tools this run built for
    /// it: each tool's variable, naming the private copy. Only the members
    /// a tool's `needed-by` names get it, so a test that reads the variable
    /// without being listed fails here as it would in a run that built no
    /// tool. Every other test executable has the variable removed: one the
    /// invocation's environment carries names a file this run did not
    /// build, and a test that ran it would pass on another binary.
    pub(crate) fn export_tools(&self, package: &str, command: &mut cargo_util::ProcessBuilder) {
        let withheld = self.phase.iter().flat_map(|phase| &phase.withheld);
        for variable in self.plan.tool.iter().map(|tool| &tool.env).chain(withheld) {
            command.env_remove(variable);
        }
        for tool in &self.tools {
            if tool.needed_by.iter().any(|name| name == package) {
                command.env(&tool.env, &tool.path);
            }
        }
    }

    /// How many crates this run tests, for the wall bound's per-member
    /// product: every package some request of the run tests (a member, a
    /// variant's package, an instrument's host that is no selected member)
    /// and every `[[workspace]]` the selection performs. The script lane
    /// counted the same (`Plan.crates()`).
    pub(crate) fn crates(&self) -> usize {
        let Packages::Packages(packages) = self.packages() else {
            unreachable!("`packages` names its packages")
        };
        packages.len() + self.selection.workspaces.len()
    }

    /// Every package some request selects, as one selection.
    pub fn packages(&self) -> Packages {
        let mut specs = BTreeSet::new();
        for request in &self.requests {
            if let Packages::Packages(packages) = &request.packages {
                specs.extend(packages.iter().cloned());
            }
        }
        Packages::Packages(specs.into_iter().collect())
    }
}

/// How a failed action is run again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Rerun {
    /// Arguments to pass to `targo test`.
    Arguments(String),
    /// A command of its own.
    Command(String),
}

#[cfg(test)]
impl ResolvedPlan {
    /// A plan bound to no workspace: `text`, its active requests, and the
    /// members `[default]` tests.
    pub(crate) fn unbound(
        path: &str,
        text: &str,
        requests: &[(&str, RequestRole)],
        members: &[&str],
    ) -> ResolvedPlan {
        ResolvedPlan {
            path: PathBuf::from(path),
            plan: TestPlan::parse(text).unwrap(),
            members: members.iter().map(|name| (*name).to_owned()).collect(),
            narrowed: false,
            sum_partial: false,
            sha256: String::new(),
            input: plan_select::Input::default(),
            only: Vec::new(),
            selection: Selection {
                whole_plan: true,
                ..Selection::default()
            },
            rows: Vec::new(),
            known_red: None,
            phase: None,
            phases: Vec::new(),
            tools: Vec::new(),
            requests: requests
                .iter()
                .map(|(id, role)| PlanRequest {
                    id: (*id).to_owned(),
                    role: *role,
                    packages: Packages::Packages(Vec::new()),
                    cli_features: CliFeatures::new_all(false),
                    filter: target_filter(true, &[], false),
                    args: Vec::new(),
                })
                .collect(),
        }
    }
}

/// Whether the default run of `host`, when it is touched, performs
/// everything the instrument `run` would judge: `Ok`, or what it leaves out.
/// The default run is `--tests` under default features with no harness
/// argument, held to no test by name. It therefore stands in for an
/// instrument only if it runs each of the instrument's targets, runs every
/// test the instrument's arguments would (an option such as `--ignored` runs
/// others), and the instrument requires no test by name.
fn default_run_covers(run: &Instrument, host: &Package) -> Result<(), String> {
    if !run.require_pass.is_empty() {
        return Err("the default run is not held to its `require-pass`".to_owned());
    }
    if let Some(option) = run.args.iter().find(|arg| arg.starts_with('-')) {
        return Err(format!(
            "the default run does not pass its argument `{option}`"
        ));
    }
    let runs = |target: &&Target| target.tested() && target.required_features().is_none();
    if run.lib
        && !host
            .targets()
            .iter()
            .any(|target| target.is_lib() && runs(&target))
    {
        return Err("the default run does not run the host's lib tests".to_owned());
    }
    for name in &run.test {
        let selected = host
            .targets()
            .iter()
            .any(|target| target.is_test() && target.name() == name && runs(&target));
        if !selected {
            return Err(format!(
                "the default run does not run test target `{name}` (`test = false` or \
                 `required-features`)"
            ));
        }
    }
    Ok(())
}

/// The directories of the workspace that own changed paths, each with what
/// it is to the plan, and the names of the members with no directory under
/// the workspace root. `members` holds the plan's members and `tested` those
/// some request tests.
fn layout(
    ws: &Workspace<'_>,
    plan: &TestPlan,
    members: &BTreeSet<&str>,
    tested: &BTreeSet<&str>,
) -> (Layout, Vec<String>) {
    // Written from the workspace root with `/`, as a changed path is.
    let slashed = |dir: &Path| {
        dir.components()
            .map(|part| match part {
                Component::Normal(part) => part.to_str(),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
            .map(|parts| parts.join("/"))
    };
    let mut owners = Vec::new();
    let mut unplaced = Vec::new();
    // A crate that is its own workspace is no member of this one; listed
    // first so that a member in the same directory would own its paths.
    for own in &plan.workspace {
        if let Some((dir, _)) = own.manifest.rsplit_once('/') {
            owners.push((dir.to_owned(), own.manifest.clone(), Owner::OwnWorkspace));
        }
    }
    for member in ws.members() {
        let name = member.name().as_str();
        // A member outside the workspace root owns no path under it.
        let Some(dir) = member.root().strip_prefix(ws.root()).ok().and_then(slashed) else {
            unplaced.push(name.to_owned());
            continue;
        };
        let owner = if tested.contains(name) {
            Owner::Member
        } else if members.contains(name) {
            Owner::Untested
        } else if let Some(command) = plan.select.elsewhere.get(name) {
            Owner::Elsewhere(command.clone())
        } else {
            Owner::Outside
        };
        owners.push((dir, name.to_owned(), owner));
    }
    // A tool's directory, written as its manifest is; the root for a
    // manifest in it.
    let tools = plan
        .tool
        .iter()
        .map(|tool| {
            let dir = tool.manifest.rsplit_once('/').map_or("", |(dir, _)| dir);
            (
                dir.to_owned(),
                tool.manifest.clone(),
                tool.needed_by.clone(),
            )
        })
        .collect();
    (Layout { owners, tools }, unplaced)
}

/// The plan members the `-p` values name. A value names exactly one member
/// this plan tests: a run that accepted another would exit as if it had
/// tested it. `members` holds the plan's members and `tested` those some
/// request tests.
fn reached_members(
    ws: &Workspace<'_>,
    plan: &TestPlan,
    members: &BTreeSet<&str>,
    tested: &BTreeSet<&str>,
    packages: &[String],
) -> CargoResult<BTreeSet<String>> {
    let mut reached = BTreeSet::new();
    for value in packages {
        anyhow::ensure!(
            !restricted_names::is_glob_pattern(value),
            "-p `{value}`: a plan run names each reached member exactly, not by pattern"
        );
        let spec = PackageIdSpec::parse(value).with_context(|| format!("-p `{value}`"))?;
        let found = ws
            .members()
            .filter(|member| spec.matches(member.package_id()))
            .collect::<Vec<_>>();
        let [member] = found[..] else {
            anyhow::bail!(
                "-p `{value}` names {} workspace members; with a plan it names one member \
                 the plan tests",
                found.len()
            );
        };
        let name = member.name().as_str();
        if let Some(owner) = plan.select.elsewhere.get(name) {
            anyhow::bail!(
                "-p `{value}`: `select.elsewhere` leaves `{name}` to `{owner}`; this plan does \
                 not test it"
            );
        }
        anyhow::ensure!(
            members.contains(name),
            "-p `{value}`: `{name}` is not a plan member, so this plan does not test it"
        );
        anyhow::ensure!(
            tested.contains(name),
            "-p `{value}`: no request of the plan tests `{name}`: the plan has no `[default]` \
             and no variant names `{name}`"
        );
        reached.insert(name.to_owned());
    }
    Ok(reached)
}

/// The plan members and the `[[workspace]]` manifests the `--reached` values
/// name, each by its directory from the workspace root. A value names
/// exactly one of the two: a run that accepted any other directory would
/// exit as if it had tested what lies there, so it is refused and nothing
/// runs.
fn reached_directories(
    layout: &Layout,
    directories: &[String],
) -> CargoResult<(BTreeSet<String>, BTreeSet<String>)> {
    let mut members = BTreeSet::new();
    let mut workspaces = BTreeSet::new();
    for value in directories {
        let dir = value.strip_suffix('/').unwrap_or(value);
        anyhow::ensure!(
            !dir.is_empty()
                && !dir.starts_with('/')
                && dir
                    .split('/')
                    .all(|part| !part.is_empty() && part != "." && part != ".."),
            "--reached `{value}` is not a directory written from the workspace root with \
             `/` (no leading `/`, no `.`, `..` or empty part)"
        );
        let here = |role: fn(&Owner) -> bool| {
            layout
                .owners
                .iter()
                .find(|(owned, _, owner)| owned == dir && role(owner))
        };
        // A member in the directory of a `[[workspace]]` manifest owns its
        // paths (`layout`), and so its directory names the member.
        if let Some((_, name, _)) = here(|owner| *owner == Owner::Member) {
            members.insert(name.clone());
        } else if let Some((_, manifest, _)) = here(|owner| *owner == Owner::OwnWorkspace) {
            workspaces.insert(manifest.clone());
        } else if let Some((_, name, Owner::Elsewhere(command))) =
            here(|owner| matches!(owner, Owner::Elsewhere(_)))
        {
            anyhow::bail!(
                "--reached `{value}`: `select.elsewhere` leaves `{name}` to `{command}`; this \
                 plan does not test it"
            );
        } else {
            anyhow::bail!(
                "--reached `{value}` names no directory this plan tests: it is neither the \
                 directory of a member a request of the plan tests nor that of a `[[workspace]]` manifest. Nothing ran: a pass would be counted for a crate no run tested"
            );
        }
    }
    Ok((members, workspaces))
}

/// Reads what `--changed-paths` or `--changed-pushed-refs` names: a file, or
/// standard input for `-`.
fn read_input(gctx: &GlobalContext, flag: &str, from: &str) -> CargoResult<Vec<u8>> {
    if from == "-" {
        let mut bytes = Vec::new();
        std::io::stdin()
            .lock()
            .read_to_end(&mut bytes)
            .with_context(|| format!("failed to read {flag} from standard input"))?;
        Ok(bytes)
    } else {
        let path = gctx.cwd().join(from);
        std::fs::read(&path).with_context(|| format!("failed to read {flag} `{}`", path.display()))
    }
}

/// Reads the paths `--changed-paths` names.
fn read_paths(gctx: &GlobalContext, from: &str) -> CargoResult<Vec<String>> {
    let bytes = read_input(gctx, "--changed-paths", from)?;
    plan_select::parse_paths(&bytes).with_context(|| format!("invalid --changed-paths `{from}`"))
}

/// What the command line says of the change a plan run judges.
#[derive(Clone, Copy, Debug, Default)]
pub struct Change<'a> {
    /// `--changed-paths <FILE|->`.
    pub paths: Option<&'a str>,
    /// `--changed-range <RANGE>`, each as typed.
    pub ranges: &'a [String],
    /// `--changed-pushed-refs <FILE|->`.
    pub pushed_refs: Option<&'a str>,
    /// `-p <SPEC>`: members the change reaches.
    pub packages: &'a [String],
    /// `--reached <DIR>`: members and `[[workspace]]`s the change reaches.
    pub reached: &'a [String],
    /// `--whole-plan`.
    pub whole: bool,
    /// `--run-after <FILE>`: the barrier the run's tests are held at.
    pub run_after: Option<&'a Path>,
    /// `--run-after-owner <PID>`: the process that is to release it.
    pub run_after_owner: Option<&'a str>,
    /// `--select-only`: say what the plan selects for this change and stop.
    pub select_only: bool,
}

impl Change<'_> {
    /// The selection input: the paths of every range and file, as one list.
    /// git is asked here, once per range (`plan_change`).
    fn input(&self, ws: &Workspace<'_>, plan: &Path) -> CargoResult<plan_select::Input> {
        let gctx = ws.gctx();
        let mut paths = self.paths.map(|from| read_paths(gctx, from)).transpose()?;
        let mut ranges = self.ranges.to_vec();
        for range in &ranges {
            super::plan_change::check_range(range)?;
        }
        if let Some(from) = self.pushed_refs {
            let bytes = read_input(gctx, "--changed-pushed-refs", from)?;
            let text = String::from_utf8(bytes)
                .map_err(|_| anyhow::anyhow!("--changed-pushed-refs `{from}` is not UTF-8"))?;
            // Only the plan says what a new branch is compared with. A plan
            // that cannot be read or parsed says so itself, not that it
            // lacks a key.
            let read = std::fs::read_to_string(plan)
                .with_context(|| format!("failed to read test plan `{}`", plan.display()))?;
            let base = TestPlan::parse(&read)
                .with_context(|| format!("invalid test plan `{}`", plan.display()))?
                .select
                .base;
            let base = base.as_deref().ok_or_else(|| {
                anyhow::anyhow!(
                    "--changed-pushed-refs needs the plan's `[select] base`: the revision a \
                     pushed branch the remote does not have is compared with"
                )
            })?;
            // Never empty: input that names no pushed tree is the standing
            // change since `base` (`plan_change::pushed_ranges`).
            ranges.extend(super::plan_change::pushed_ranges(&text, base)?);
        }
        if !ranges.is_empty() {
            let changed = super::plan_change::range_paths(ws.root(), &ranges)?;
            let paths = paths.get_or_insert_with(Vec::new);
            paths.extend(changed);
            paths.sort();
            paths.dedup();
        }
        let input = plan_select::Input {
            changed_paths: paths,
            packages: self.packages.to_vec(),
            reached: self.reached.to_vec(),
            ranges,
        };
        // Running every member is asked for, never fallen into: a caller
        // that lost its range would otherwise run the whole plan, or read a
        // run of everything as the verdict on its change.
        anyhow::ensure!(
            !self.whole || input.is_whole_plan(),
            "--whole-plan runs every request of the plan; it cannot be combined with \
             --changed-range, --changed-paths, --changed-pushed-refs, --reached or -p"
        );
        anyhow::ensure!(
            self.whole || !input.is_whole_plan(),
            "a test plan run says what it judges: name the change with --changed-range, \
             --changed-paths, --changed-pushed-refs, --reached or -p, or pass --whole-plan to run every request"
        );
        Ok(input)
    }
}

/// Binds the invocation to the plan at `path`: features unify per request,
/// and the packages built are those some request selects. `change` says
/// what changed and so which requests this run performs; `only` narrows
/// those. Returns whether any request is left: a
/// selection that performs none has nothing to build (`idle`).
///
/// A changed path the plan must account for and does not is refused with
/// [`UnattributedPaths`], after the record that lists it.
pub fn select(
    ws: &mut Workspace<'_>,
    options: &mut CompileOptions,
    path: &Path,
    only: &[String],
    change: Change<'_>,
) -> CargoResult<bool> {
    anyhow::ensure!(
        crate::is_targo_invocation() && !crate::trust_verified_targo(),
        "a test plan requires native unverified Targo"
    );
    // Each request resolves as its standalone command does under
    // `resolver.feature-unification = "selected"`, whatever the config says.
    ws.set_resolve_feature_unification(FeatureUnification::Selected);
    let input = change.input(ws, path)?;
    let plan = ResolvedPlan::load(ws, path, only, input)?;
    if change.select_only {
        // The listing is the whole of the standard output: one record, the
        // one a run of this selection would begin with, and with it what
        // that run would do with each tool and workspace. Nothing is built,
        // no clock is armed and nothing is judged, so no result record
        // follows; a listing that is not one whole JSON line was cut off.
        anyhow::ensure!(
            change.run_after.is_none() && change.run_after_owner.is_none(),
            "--select-only runs nothing; it cannot be combined with --run-after"
        );
        let phases = super::plan_phases::describe(ws, options, &plan)?;
        writeln!(
            ws.gctx().shell().out(),
            "{}",
            plan.record_with(Some(&phases))
        )?;
        if !plan.selection.unattributed.is_empty() {
            return Err(UnattributedPaths {
                plan: plan.path.display().to_string(),
                paths: plan.selection.unattributed.clone(),
            }
            .into());
        }
        return Ok(!plan.requests.is_empty());
    }
    // The record goes first on every route but `--unit-graph`, whose
    // standard output is one JSON document of its own.
    if options.build_config.emit_json() && !options.build_config.unit_graph {
        writeln!(ws.gctx().shell().out(), "{}", plan.record())?;
    }
    plan.report(ws.gctx())?;
    if !plan.selection.unattributed.is_empty() {
        return Err(UnattributedPaths {
            plan: plan.path.display().to_string(),
            paths: plan.selection.unattributed.clone(),
        }
        .into());
    }
    let performs = !plan.requests.is_empty();
    // The run's clock starts here: its bounds cover the phases, the build
    // and the tests.
    anyhow::ensure!(
        change.run_after.is_some() || change.run_after_owner.is_none(),
        "--run-after-owner names who releases a barrier; it needs --run-after"
    );
    let barrier = change
        .run_after
        .map(|path| {
            super::plan_clock::Barrier::new(
                &plan.plan.run,
                path.to_path_buf(),
                change.run_after_owner,
            )
        })
        .transpose()?;
    super::plan_clock::arm(
        ws.gctx(),
        &plan.plan.run,
        plan.crates(),
        barrier,
        &plan.path,
        options.build_config.emit_json(),
    )?;
    // The requests' own features and filters are applied per request; these
    // cover what remains of the invocation: one lockfile and one package set.
    options.spec = plan.packages();
    options.cli_features = CliFeatures::new_all(false);
    options.build_config.test_plan = Some(Rc::new(plan));
    Ok(performs)
}

/// Ends an invocation whose selection performs no request: nothing of this
/// workspace is resolved, built or run, so nothing reads its lockfile
/// (`--locked` has nothing to hold). The plan's phases have run by now
/// (`plan_phases::run`), and a workspace among them that failed fails this
/// run. A run still closes its JSON with the result record, so that a reader
/// can tell a run of nothing from a cut-off one.
///
/// The plan is held to what every other route holds it to first: an exit 0
/// here is read as this plan's verdict on the change, which a plan this
/// Targo cannot perform in full does not have.
pub fn idle(
    ws: &Workspace<'_>,
    options: &CompileOptions,
    no_run: bool,
    no_fail_fast: bool,
) -> CargoResult<()> {
    let build_config = &options.build_config;
    let Some(plan) = build_config.test_plan.as_deref() else {
        return Ok(());
    };
    debug_assert!(plan.requests.is_empty());
    plan.require_supported(ws.gctx(), no_run, build_config.unit_graph, no_fail_fast)
        .map_err(super::plan_outcome::cannot_judge)?;
    // The harness policy is checked on every other route (`graph::request`).
    HarnessPolicy::load(ws, Some(plan)).map_err(super::plan_outcome::cannot_judge)?;
    let path = plan.path.display();
    if build_config.unit_graph {
        ws.gctx().shell().warn(format!(
            "test plan `{path}`: the selection performs no request, so there is no unit graph"
        ))?;
        return Ok(());
    }
    ws.gctx().shell().status(
        "Finished",
        format!("test plan `{path}`: the selection performs no request"),
    )?;
    if !no_run {
        // A stop that came first is how the run ended (`plan_outcome::conclude`).
        if plan.phase.is_none()
            && let Err((_, why)) = super::plan_outcome::conclude()
        {
            return Err(anyhow::anyhow!(why));
        }
        // No request ran; a `[[workspace]]` phase may have, and failed.
        let verdict = super::plan_judge::Verdict::of(plan, &[]);
        if build_config.emit_json() {
            writeln!(ws.gctx().shell().out(), "{}", verdict.record(plan))?;
        }
        // Exit 0 from a run of nothing is no pass. A caller that reads only
        // the status and the text (a push hook, a gate leg) tells the two
        // apart by this line, which the repository's lanes all print for a
        // run that judged nothing: `SKIPPED: ` at the start of a line.
        if verdict.outcome(plan) == super::plan_outcome::Outcome::NothingSelected {
            writeln!(
                ws.gctx().shell().err(),
                "SKIPPED: test plan `{path}`: the change selects no request and no workspace \
                 this target tests; nothing was built or run"
            )?;
        }
        if let Some(unmet) = verdict.refusal(plan) {
            let error = anyhow::anyhow!("{unmet}");
            return Err(
                if verdict.outcome(plan) == super::plan_outcome::Outcome::Failed {
                    error
                } else {
                    super::plan_outcome::cannot_judge(error)
                },
            );
        }
    }
    Ok(())
}

/// Refuses a plan that asks for something this invocation would not do. A
/// gate reads the exit status as the plan's verdict, so a section this Targo
/// does not perform is an error, never a quieter run.
///
/// Selection is applied before this (`select`): the requests left are the
/// ones this run performs.
pub(super) fn require_honored(
    ws: &Workspace<'_>,
    options: &super::TestOptions,
    args: &[&str],
) -> CargoResult<()> {
    let build_config = &options.compile_opts.build_config;
    let Some(plan) = build_config.test_plan.as_deref() else {
        return Ok(());
    };
    let honored = || {
        anyhow::ensure!(
            args.is_empty(),
            "a test plan names each request's test arguments itself"
        );
        plan.require_supported(
            ws.gctx(),
            options.no_run,
            build_config.unit_graph,
            options.no_fail_fast,
        )
    };
    honored().map_err(super::plan_outcome::cannot_judge)
}

impl ResolvedPlan {
    /// What refuses the plan before anything is built: on every route, and
    /// before the first phase (`plan_phases::run`). `builds_only` is a
    /// `--no-run` or `--unit-graph` invocation.
    pub(super) fn refusals(&self, builds_only: bool, no_fail_fast: bool) -> CargoResult<()> {
        self.validate_arguments()?;
        if builds_only {
            return Ok(());
        }
        // The known-red file excuses a failure in the verdict of a run that
        // ran to its end. A run that stops at its first failure has no
        // verdict, so there a listed failure would fail the run and still
        // read as the file's judgement.
        anyhow::ensure!(
            no_fail_fast || self.known_red.is_none(),
            "test plan `{}` sets `[expect] known-red`, which is judged over a run that ran \
             to its end; pass --no-fail-fast",
            self.path.display()
        );
        Ok(())
    }

    /// Refuses a plan this invocation cannot perform in full, whatever the
    /// selection left of it: with requests to run (`require_honored`) or
    /// with none (`idle`).
    fn require_supported(
        &self,
        gctx: &GlobalContext,
        no_run: bool,
        unit_graph: bool,
        no_fail_fast: bool,
    ) -> CargoResult<()> {
        let plan = self;
        plan.refusals(no_run || unit_graph, no_fail_fast)?;
        let path = plan.path.display();
        // `[[tool]]` and `[[workspace]]` are phases of other manifests
        // (`plan_phases`). A unit graph is one workspace's and shows none
        // of them.
        let outside = [
            ("[[tool]]", plan.plan.tool.len()),
            ("[[workspace]]", plan.plan.workspace.len()),
        ];
        for (section, entries) in outside {
            if entries != 0 && unit_graph {
                gctx.shell().warn(format!(
                    "test plan `{path}`: the unit graph leaves out its {section} entries \
                     ({entries}), which are built under their own manifests"
                ))?;
            }
        }
        if no_run || unit_graph {
            return Ok(());
        }
        // `min-tests` sums a member's default run and its variants. A run
        // without one of them has only part of the sum: it is a reproduction,
        // not the gate's run.
        if plan.sum_partial && plan.min_tests_set() {
            gctx.shell().warn(format!(
                "test plan `{path}`: --request leaves requests out of this run, so `[default] \
                 min-tests` is not judged"
            ))?;
        }
        Ok(())
    }
}

/// `--lib`, `--test <name>` and `--tests`, built as the command line builds
/// them so that a request selects what its standalone command selects.
fn target_filter(lib: bool, tests: &[String], all_tests: bool) -> CompileFilter {
    CompileFilter::from_raw_arguments(
        lib,
        Vec::new(),
        false,
        tests.to_vec(),
        all_tests,
        Vec::new(),
        false,
        Vec::new(),
        false,
        false,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const MINIMAL: &str = r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
"#;

    fn refusal(text: &str) -> String {
        format!("{:#}", TestPlan::parse(text).unwrap_err())
    }

    #[test]
    fn the_design_plan_parses_with_every_section() {
        let plan = TestPlan::parse(
            r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
attribute-under = ["crates/"]
[select.elsewhere]
trust-witness = "x.py test --stage 1 crates/trust-witness"
[default]
targets = "tests"
min-tests = 1
[expect]
known-red = "tests/known-red/crates-tests.txt"
[harness.trust-clean.test.clean_pipeline_integration]
exclusive = true
[harness.trust-clean.lib]
weight = 2
[[variant]]
id = "router-setter"
package = "trust-router"
features = ["ay-backend"]
test = ["setter_assert_refute_lane"]
[[instrument]]
id = "prelude-digest"
package = "trust-model-prelude"
lib = true
args = ["tests::digest::"]
when-changed = ["crates/trust-spec-temporal/clean/Trust/"]
require-pass = ["tests::digest::source_digest_matches"]
[[instrument]]
id = "json-corpus"
package = "trust-json"
test = ["acceptance_gate"]
when-changed-suffix = ".json"
not-under = ["first-party/", "vendor/"]
[[tool]]
manifest = "targo-trust/Cargo.toml"
bin = "targo-trust"
env = "TRUST_TARGO_TRUST_BIN"
needed-by = ["trust-integration-tests"]
[[workspace]]
manifest = "crates/trust-worker-linux/Cargo.toml"
cfg = 'target_os = "linux"'
"#,
        )
        .unwrap();
        assert_eq!(plan.default.as_ref().unwrap().min_tests, Some(1));
        assert_eq!(plan.select.elsewhere.len(), 1);
        let clean = &plan.harness["trust-clean"];
        assert_eq!(
            clean.test["clean_pipeline_integration"].exclusive,
            Some(true)
        );
        assert_eq!(clean.lib.unwrap().weight, Some(2));
        // The table as the harness policy reads it: a kind with no entry
        // is absent, as in `build.test-harnesses`.
        let bound = ResolvedPlan {
            plan: plan.clone(),
            ..ResolvedPlan::unbound("p.toml", MINIMAL, &[], &[])
        };
        let policy = bound.harness_config();
        assert_eq!(policy.keys().collect::<Vec<_>>(), ["trust-clean"]);
        let entries = &policy["trust-clean"];
        assert_eq!(entries.lib.unwrap().weight, Some(2));
        assert_eq!(entries.lib.unwrap().exclusive, None);
        let tests = entries.test.as_ref().unwrap();
        assert_eq!(tests.len(), 1);
        assert_eq!(tests["clean_pipeline_integration"].exclusive, Some(true));
        assert_eq!(tests["clean_pipeline_integration"].weight, None);
        assert!(entries.bin.is_none() && entries.bench.is_none() && entries.example.is_none());
        assert_eq!(plan.variant[0].features, ["ay-backend"]);
        assert!(!plan.variant[0].lib);
        assert_eq!(plan.instrument[0].args, ["tests::digest::"]);
        assert_eq!(
            plan.instrument[1].when_changed_suffix.as_deref(),
            Some(".json")
        );
        assert_eq!(plan.tool[0].needed_by, ["trust-integration-tests"]);
        assert_eq!(
            plan.workspace[0].cfg.as_deref(),
            Some(r#"target_os = "linux""#)
        );
    }

    #[test]
    fn a_minimal_plan_has_no_requests_of_its_own() {
        let plan = TestPlan::parse(MINIMAL).unwrap();
        assert!(plan.default.is_none());
        assert!(plan.variant.is_empty() && plan.instrument.is_empty());
    }

    #[test]
    fn another_schema_is_refused() {
        let text = MINIMAL.replace("v1", "v2");
        assert!(refusal(&text).contains("is not `targo.test-plan.v1`"));
    }

    #[test]
    fn an_unknown_key_is_refused_at_every_level() {
        for extra in [
            "\n[selct]\nmembers = \"default-members\"\n",
            "\n[default]\ntargets = \"tests\"\nmin-test = 1\n",
            "\n[harness.a.test.t]\nwieght = 2\n",
            "\n[harness.a.tests.t]\nweight = 2\n",
            "\n[[variant]]\nid = \"v\"\npackage = \"a\"\nlib = true\nargs = [\"x\"]\n",
            "\n[[instrument]]\nid = \"i\"\npackage = \"a\"\nlib = true\nfeatures = [\"x\"]\n",
            "\n[[tool]]\nmanifest = \"m\"\nbin = \"b\"\nenv = \"E\"\nneeded = []\n",
            "\n[[workspace]]\nmanifest = \"m\"\ntarget = \"x\"\n",
        ] {
            let message = refusal(&format!("{MINIMAL}{extra}"));
            assert!(message.contains("unknown field"), "{extra}: {message}");
        }
        let message = refusal(&MINIMAL.replace("[select]", "[select]\nmember = 1"));
        assert!(message.contains("unknown field"), "{message}");
    }

    #[test]
    fn an_unknown_member_set_or_target_set_is_refused() {
        let text = MINIMAL.replace("default-members", "members");
        assert!(refusal(&text).contains("unknown variant"));
        let text = format!("{MINIMAL}\n[default]\ntargets = \"all\"\n");
        assert!(refusal(&text).contains("unknown variant"));
    }

    #[test]
    fn request_ids_are_unique_and_never_the_default_one() {
        let run = |id: &str| format!("\n[[variant]]\nid = \"{id}\"\npackage = \"a\"\nlib = true\n");
        let twice = format!(
            "{MINIMAL}{}\n[[instrument]]\nid = \"x\"\npackage = \"a\"\nlib = true\n",
            run("x")
        );
        assert!(refusal(&twice).contains("request id `x` is used twice"));
        let reserved = format!("{MINIMAL}{}", run("default"));
        assert!(refusal(&reserved).contains("names the `[default]` request"));
        let empty = format!("{MINIMAL}{}", run(""));
        assert!(refusal(&empty).contains("empty id"));
    }

    #[test]
    fn a_request_id_is_one_plain_shell_word() {
        let run = |id: &str| {
            format!("{MINIMAL}\n[[instrument]]\nid = \"{id}\"\npackage = \"a\"\nlib = true\n")
        };
        for id in [
            "my id", "a;b", "$(x)", "a`b", "a'b", "-x", "--no-run", "é", "a/b", "a,b",
        ] {
            let message = refusal(&run(id));
            assert!(
                message.contains(&format!("instrument id `{id}` is not a plain word")),
                "{id}: {message}"
            );
        }
        for id in ["a", "A-1_b.c", "_x", ".x", "9"] {
            assert_eq!(TestPlan::parse(&run(id)).unwrap().instrument[0].id, id);
        }
    }

    /// A plan of these requests, as if resolved, at `path`.
    fn resolved(path: &str, requests: &[(&str, RequestRole)]) -> ResolvedPlan {
        ResolvedPlan::unbound(path, MINIMAL, requests, &[])
    }

    fn ids(ids: &[&str]) -> Vec<String> {
        ids.iter().map(|id| (*id).to_owned()).collect()
    }

    #[test]
    fn a_rerun_names_the_narrowest_request_and_quotes_the_path() {
        let plan = resolved("/a dir/it's.toml", &[]);
        assert_eq!(
            plan.rerun(&ids(&["default", "v", "w"])).unwrap(),
            Rerun::Arguments(r"--plan '/a dir/it'\''s.toml' --request v".to_owned())
        );
        let plan = resolved("plans/crates.toml", &[]);
        assert_eq!(
            plan.rerun(&ids(&["default"])).unwrap(),
            Rerun::Arguments("--plan plans/crates.toml --request default".to_owned())
        );
        assert_eq!(plan.rerun(&[]), None);
    }

    #[test]
    fn only_an_instrument_requires_its_action_to_judge_a_test() {
        let plan = resolved(
            "p.toml",
            &[
                (DEFAULT_REQUEST, RequestRole::Default),
                ("v", RequestRole::Variant),
                ("i", RequestRole::Instrument),
                ("j", RequestRole::Instrument),
            ],
        );
        assert_eq!(plan.must_judge(&ids(&["default", "v"])), None);
        assert_eq!(
            plan.must_judge(&ids(&["default", "j"])).unwrap(),
            "instrument `j`"
        );
        assert_eq!(
            plan.must_judge(&ids(&["i", "j"])).unwrap(),
            "instrument `i`"
        );
    }

    #[test]
    fn every_request_needs_an_action() {
        let plan = resolved(
            "p.toml",
            &[
                (DEFAULT_REQUEST, RequestRole::Default),
                ("v", RequestRole::Variant),
                ("i", RequestRole::Instrument),
            ],
        );
        plan.require_actions(&ids(&["i", "default", "v", "i"]))
            .unwrap();
        let message = format!("{:#}", plan.require_actions(&ids(&["v"])).unwrap_err());
        assert!(
            message
                .contains("`p.toml`: no test executable was selected for requests `default`, `i`;"),
            "{message}"
        );
        let message = format!("{:#}", plan.require_actions(&ids(&["v", "i"])).unwrap_err());
        assert!(message.contains("for request `default`;"), "{message}");
    }

    #[test]
    fn an_unrun_action_is_an_error_unless_a_failure_already_explains_it() {
        let plan = resolved("p.toml", &[]);
        let (one, two) = (ids(&["b", "a"]), ids(&["c"]));
        plan.require_all_ran(&[], false).unwrap();
        plan.require_all_ran(&[], true).unwrap();
        plan.require_all_ran(&[&one, &two], true).unwrap();
        let message = format!(
            "{:#}",
            plan.require_all_ran(&[&one, &two], false).unwrap_err()
        );
        assert!(
            message.contains(
                "`p.toml`: 2 test actions never ran though nothing failed (requests `a`, `b`, `c`)"
            ),
            "{message}"
        );
        let message = format!("{:#}", plan.require_all_ran(&[&two], false).unwrap_err());
        assert!(
            message.contains("1 test action never ran though nothing failed (request `c`)"),
            "{message}"
        );
    }

    #[test]
    fn a_test_is_named_exactly() {
        let run = |role: &str, test: &str| {
            refusal(&format!(
                "{MINIMAL}\n[[{role}]]\nid = \"r\"\npackage = \"a\"\ntest = [\"{test}\"]\n"
            ))
        };
        for role in ["variant", "instrument"] {
            for pattern in ["set*", "sette?", "[s]etter"] {
                let message = run(role, pattern);
                assert!(
                    message.contains(&format!("{role} `r` names test `{pattern}`"))
                        && message.contains("not by pattern"),
                    "{message}"
                );
            }
            let message = run(role, "");
            assert!(
                message.contains(&format!("{role} `r` names an empty `test`")),
                "{message}"
            );
        }
        let exact = format!(
            "{MINIMAL}\n[[variant]]\nid = \"r\"\npackage = \"a\"\ntest = [\"setter-1_a\"]\n"
        );
        assert_eq!(
            TestPlan::parse(&exact).unwrap().variant[0].test,
            ["setter-1_a"]
        );
    }

    #[test]
    fn a_request_without_a_target_is_refused() {
        let text = format!("{MINIMAL}\n[[variant]]\nid = \"v\"\npackage = \"a\"\n");
        assert!(refusal(&text).contains("variant `v` selects no target"));
        let text = format!("{MINIMAL}\n[[instrument]]\nid = \"i\"\npackage = \"a\"\n");
        assert!(refusal(&text).contains("instrument `i` selects no target"));
    }
}
