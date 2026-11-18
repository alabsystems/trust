//! Trust: per-user storage for confined dependencies with stable source paths.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use anyhow::bail;
use cargo_util::Sha256;

use super::action_inputs::SourceInputs;
use super::{CompileMode, CrateType, Unit, unit_graph::UnitGraph};
use crate::CargoResult;
use crate::util::data_structures::{HashMap, HashSet};
use crate::util::log_message::SharedDependencyExclusion;
use crate::workspace::{GitReference, PackageId, SourceId};

/// Git checkout paths use abbreviated object names and ordinary SourceId
/// hashing omits the precise revision. Shared actions require the resolved,
/// full object name independently of both of those lookup accelerators.
pub(super) fn resolved_git_commit(source: SourceId) -> Option<&'static str> {
    if !source.is_git() {
        return None;
    }
    let revision = source.precise_git_fragment()?;
    (revision.len() == 40 && revision.bytes().all(|byte| byte.is_ascii_hexdigit()))
        .then_some(revision)
}

pub(super) fn git_source_identity(source: SourceId) -> Option<String> {
    let revision = resolved_git_commit(source)?;
    let (kind, selector) = match source.git_reference()? {
        GitReference::Tag(value) => ("tag", value.as_str()),
        GitReference::Branch(value) => ("branch", value.as_str()),
        GitReference::Rev(value) => ("rev", value.as_str()),
        GitReference::DefaultBranch => ("default", ""),
    };
    let mut hash = Sha256::new();
    for field in [
        "targo-shared-git-source-v1",
        source.url().as_str(),
        kind,
        selector,
        revision,
    ] {
        hash.update(&(field.len() as u64).to_le_bytes());
        hash.update(field.as_bytes());
    }
    Some(hash.finish_hex())
}

/// Trust (DC-17a): what decides whether `build.shared-dependency-cache` takes
/// effect for one build. [`cache_policy`] reads only these fields, so a
/// repository can check the key in and every lane builds: the lanes that
/// cannot share run exactly as with the key unset.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CacheLane<'a> {
    /// The key's value (`false` when unset).
    pub(crate) requested: bool,
    /// The frontend is Targo, not a cargo-named invocation.
    pub(crate) targo: bool,
    /// The verified lane (`targo trust`), which never reads or writes the store.
    pub(crate) verified: bool,
    /// `std::env::consts::OS` of this Targo.
    pub(crate) os: &'a str,
    /// `std::env::consts::ARCH` of this Targo.
    pub(crate) arch: &'a str,
    /// The host triple the compiler reports.
    pub(crate) compiler_host: &'a str,
    /// A `build.rustc-wrapper` or `build.rustc-workspace-wrapper` is in force.
    pub(crate) compiler_wrapper: bool,
    /// The new build-dir layout is in force (it is unless its test-only
    /// opt-out is set); fine-grain locking needs it.
    pub(crate) new_layout: bool,
    /// `-Zfine-grain-locking` was given.
    pub(crate) fine_grain_flag: bool,
}

/// Trust (DC-17a): the cache key's effect on one build.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CachePolicy {
    /// Eligible dependency units use the shared store.
    pub(crate) shares: bool,
    /// The build uses fine-grain locking: given by `-Zfine-grain-locking`, or
    /// turned on because the build shares (the store's per-unit locks need it),
    /// as `-Zfine-grain-locking` itself turns on the new build-dir layout.
    pub(crate) fine_grain_locking: bool,
}

/// Trust (DC-17a): the one decision for `build.shared-dependency-cache`. A
/// native unverified Targo build on macOS, with the compiler's host the native
/// one, no compiler wrapper and the new layout, shares and turns on the
/// fine-grain locking it needs. Every other lane (`targo trust`, another OS, a
/// cargo-named invocation, a compiler wrapper, a foreign host architecture)
/// gets the policy of an unset key.
pub(crate) fn cache_policy(lane: CacheLane<'_>) -> CachePolicy {
    let shares = lane.requested
        && lane.targo
        && !lane.verified
        && lane.os == "macos"
        && lane.new_layout
        && !lane.compiler_wrapper
        && lane.compiler_host == format!("{}-apple-darwin", lane.arch);
    CachePolicy {
        shares,
        fine_grain_locking: lane.fine_grain_flag || shares,
    }
}

/// Trust (DC-18b): what deciding whether a workspace member may be shared
/// reads, besides the unit.
pub(crate) struct EligibilityInputs<'b> {
    /// `--artifact-dir`, a directory a build writes.
    pub(crate) export_dir: Option<&'b Path>,
    /// The store (`storage_root`), made private before members are judged.
    pub(crate) store: Option<&'b Path>,
    /// The environment a shared unit's compiler sees.
    pub(crate) environment: Option<&'b cargo_util::EnvironmentInputs>,
    /// The compiler's content identity, hex.
    pub(crate) compiler: Option<String>,
    /// The compiler takes `-Ztrust-path-free`.
    pub(crate) path_free: bool,
    /// A `targo fix` proxy or a forced rebuild drives the build: its primary
    /// units are rewritten in place or always compiled, never read from a slot.
    pub(crate) driven: bool,
    /// The caller's extra compiler arguments (`targo rustc -- …`).
    pub(crate) extra_args: &'b HashMap<Unit, Vec<String>>,
}

/// Trust (DC-18b): what deciding a unit's eligibility reads beyond the unit.
/// One value serves selection and the logged exclusion reasons alike.
#[derive(Debug, Default)]
pub(crate) struct Eligibility {
    workspace: PathBuf,
    members: HashSet<PackageId>,
    /// Members may be shared at all: the compiler takes `-Ztrust-path-free`
    /// and has a content identity, no native resource owner runs this build
    /// (a member's source is then captured by the legacy capture, which can
    /// digest it without its path), no `targo fix` proxy or forced rebuild
    /// drives it, and no earlier attempt of this process withdrew members.
    members_admitted: bool,
    /// Build outputs, the store and any export directory: a confined member's
    /// package directory must neither hold one nor sit inside one.
    writable: Vec<PathBuf>,
    home: PathBuf,
    /// Member units whose compiler would be given a path remap of the
    /// caller's (`RUSTFLAGS`, `build.rustflags`, `targo rustc -- …`): a remap
    /// that names neither checkout can still write one into the bytes.
    remapped: HashSet<Unit>,
    /// Paths git reports changed below the workspace (modified, staged,
    /// untracked, conflicted). `None` where the workspace is in no git work
    /// tree, which shares every member as it is.
    uncommitted: Option<Vec<PathBuf>>,
    /// What a member's private record binds besides its sources.
    environment: String,
    compiler: String,
    lockfile: PathBuf,
    /// Each member package's relocatable source capture, made once, on first
    /// need; `None` where the tree cannot be captured.
    sources: Mutex<HashMap<PackageId, Option<Arc<SourceInputs>>>>,
    /// This checkout's private records (`<build-dir>/.targo-member-private`),
    /// read once: a member key and its record's line.
    records: HashMap<String, String>,
    records_dir: PathBuf,
    /// Trust (DC-18c): libraries outside the workspace that link a member
    /// whose package has a build script: that script's output reaches their
    /// command, and their slots, named by their units, do not hold it.
    script_dependents: HashSet<Unit>,
}

impl Eligibility {
    pub(crate) fn new(
        ws: &crate::workspace::Workspace<'_>,
        graph: &UnitGraph,
        inputs: EligibilityInputs<'_>,
    ) -> CargoResult<Self> {
        let gctx = ws.gctx();
        let home = gctx.home().as_path_unlocked().to_path_buf();
        let mut writable = vec![
            ws.target_dir().into_path_unlocked(),
            ws.build_dir().into_path_unlocked(),
            home.join("trust"),
        ];
        if let Some(export) = inputs.export_dir {
            writable.push(gctx.cwd().join(export));
        }
        // A member's package is judged against the directories a build
        // writes, which must exist to be judged: a writable directory that
        // does not exist yet is never assumed to land outside the sources.
        // A build that shares makes them now, as it would make them later;
        // the store and its parent `storage_root` already made private.
        let members_admitted = inputs.path_free
            && inputs.store.is_some()
            && inputs.environment.is_some()
            && inputs.compiler.is_some()
            && !inputs.driven
            && crate::resource_v3::current().is_none()
            && !WITHDRAWN.load(Ordering::SeqCst)
            && writable.iter().all(|path| fs::create_dir_all(path).is_ok());
        let workspace = ws.root().to_path_buf();
        let members: HashSet<PackageId> = ws.members().map(|member| member.package_id()).collect();
        let records_dir = ws
            .build_dir()
            .into_path_unlocked()
            .join(".targo-member-private");
        let mut eligibility = Eligibility {
            members,
            members_admitted,
            writable,
            home,
            environment: inputs
                .environment
                .map(|environment| environment.digest().to_string())
                .unwrap_or_default(),
            compiler: inputs.compiler.unwrap_or_default(),
            lockfile: ws.lock_root().as_path_unlocked().join("Cargo.lock"),
            records_dir,
            workspace,
            ..Default::default()
        };
        if !members_admitted {
            return Ok(eligibility);
        }
        eligibility.remapped = graph
            .keys()
            .filter(|unit| {
                let extra = inputs.extra_args.get(unit).into_iter().flatten();
                eligibility.member(unit)
                    && remaps_paths(unit.rustflags.iter().chain(extra).map(String::as_str))
            })
            .cloned()
            .collect();
        eligibility.script_dependents = script_dependents(graph, &eligibility);
        eligibility.uncommitted = uncommitted_paths(&eligibility.workspace);
        if let Ok(entries) = fs::read_dir(&eligibility.records_dir) {
            for entry in entries.flatten() {
                if let (Some(name), Ok(line)) = (
                    entry.file_name().to_str().map(str::to_owned),
                    fs::read_to_string(entry.path()),
                ) {
                    eligibility.records.insert(name, line.trim().to_owned());
                }
            }
        }
        Ok(eligibility)
    }

    /// A workspace member, inside the workspace directory: a unit whose
    /// sources are named relative to that directory once it is remapped.
    pub(crate) fn member(&self, unit: &Unit) -> bool {
        let id = unit.pkg.package_id();
        id.source_id().is_path()
            && !unit.is_std
            && unit.pkg.root().starts_with(&self.workspace)
            && self.members.contains(&id)
    }

    /// Trust (DC-18c): `dep` is one a member is keyed on rather than one it
    /// shares: its own build-script run, or a proc macro it loads.
    pub(crate) fn keyed(&self, parent: &Unit, dep: &Unit) -> bool {
        self.member(parent) && keyed_kind(parent, dep)
    }

    fn member_exclusion(&self, unit: &Unit) -> Option<SharedDependencyExclusion> {
        use SharedDependencyExclusion::*;
        if !self.members_admitted
            || !super::action_inputs::source_is_read_only(
                unit.pkg.root(),
                &self.writable,
                &self.home,
            )
            || super::trim_paths::should_emit_unremap_file(unit)
            || self.remapped.contains(unit)
        {
            return Some(MemberNotConfined);
        }
        if self.uncommitted(unit.pkg.root()) {
            return Some(MemberUncommitted);
        }
        let key = member_key(unit);
        if let Some(reason) = PRIVATE
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(&key)
        {
            return Some(*reason);
        }
        let Some(source) = self.source(unit) else {
            return Some(MemberSourceUncaptured);
        };
        let record = self.records.get(&key)?;
        let Ok(bindings) = self.bindings(unit, &source) else {
            // A record that cannot be judged here holds.
            return Some(MemberCompileFailed);
        };
        bindings.reason(record)
    }

    /// Whether git reports a change at or below `root`, or above it in a
    /// directory git does not track; a root that cannot be resolved counts
    /// as changed.
    fn uncommitted(&self, root: &Path) -> bool {
        let Some(changed) = &self.uncommitted else {
            return false;
        };
        let Ok(root) = root.canonicalize() else {
            return true;
        };
        changed
            .iter()
            .any(|path| path.starts_with(&root) || root.starts_with(path))
    }

    /// Trust (DC-18b): the member package's relocatable source capture, made
    /// on first need and reused by the slot key, the command and the records.
    pub(crate) fn source(&self, unit: &Unit) -> Option<Arc<SourceInputs>> {
        let mut sources = self.sources.lock().unwrap_or_else(PoisonError::into_inner);
        sources
            .entry(unit.pkg.package_id())
            .or_insert_with(|| {
                match SourceInputs::capture_relocatable(unit.pkg.root(), &self.workspace) {
                    Ok(source) => Some(Arc::new(source)),
                    Err(error) => {
                        tracing::debug!(
                            "member {} stays private: {error:#}",
                            unit.pkg.package_id()
                        );
                        None
                    }
                }
            })
            .clone()
    }

    fn bindings(&self, unit: &Unit, source: &SourceInputs) -> CargoResult<Bindings> {
        let file = |path: &Path| -> CargoResult<String> {
            let mut hash = Sha256::new();
            match fs::read(path) {
                Ok(bytes) => {
                    hash.update(b"present");
                    hash.update(&bytes);
                }
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    hash.update(b"absent");
                }
                Err(error) => return Err(error.into()),
            }
            Ok(hash.finish_hex())
        };
        let lockfile = file(&self.lockfile)?;
        let manifest = file(&unit.pkg.manifest_path())?;
        Ok(Bindings {
            stable: digest_fields(&[
                "targo-member-private-stable-v1",
                &self.environment,
                &self.compiler,
                &lockfile,
                &manifest,
            ]),
            sources: digest_fields(&[
                "targo-member-private-sources-v1",
                source.digest(),
                &self.environment,
                &self.compiler,
            ]),
        })
    }

    /// Trust (DC-18b): what a shared member's refusal records, prepared while
    /// the build is planned.
    pub(crate) fn recorder(&self, unit: &Unit) -> CargoResult<MemberRecorder> {
        let source = self
            .source(unit)
            .ok_or_else(|| anyhow::anyhow!("shared member has no source capture"))?;
        let key = member_key(unit);
        Ok(MemberRecorder {
            path: self.records_dir.join(&key),
            key,
            package: unit.pkg.name().to_string(),
            bindings: self.bindings(unit, &source)?,
        })
    }
}

/// Whether the caller's compiler flags remap paths.
fn remaps_paths<'s>(flags: impl IntoIterator<Item = &'s str>) -> bool {
    let mut after_z = false;
    for flag in flags {
        let unstable = if after_z {
            Some(flag)
        } else {
            flag.strip_prefix("-Z")
        };
        if flag.starts_with("--remap-path")
            || unstable.is_some_and(|option| option.trim_start().starts_with("remap"))
        {
            return true;
        }
        after_z = flag == "-Z";
    }
    false
}

/// Trust (DC-18c): a dependency that stays per checkout and that a member's
/// slot is named by the output of, rather than shared: the member's own
/// build-script run (its directives and `OUT_DIR`), or a proc macro (its
/// library's bytes).
pub(crate) fn keyed_kind(parent: &Unit, dep: &Unit) -> bool {
    (dep.mode.is_run_custom_build() && dep.pkg.package_id() == parent.pkg.package_id())
        || dep.target.proc_macro()
}

/// Trust (DC-18c): the build-script runs whose output Targo lays over a
/// unit's command when it runs (`custom_build::build_map`'s `to_link` and
/// `plugins` for the unit): its own scripts, and those of each library it
/// links or proc macro it loads, through the libraries they link.
pub(crate) fn overlay_scripts(graph: &UnitGraph, unit: &Unit) -> Vec<Unit> {
    fn own(graph: &UnitGraph, unit: &Unit, found: &mut Vec<Unit>) {
        if unit.target.is_custom_build() {
            return;
        }
        for dep in &graph[unit] {
            if dep.unit.mode.is_run_custom_build()
                && dep.unit.pkg.package_id() == unit.pkg.package_id()
                && !found.contains(&dep.unit)
            {
                found.push(dep.unit.clone());
            }
        }
    }
    fn to_link(graph: &UnitGraph, unit: &Unit, seen: &mut HashSet<Unit>, found: &mut Vec<Unit>) {
        if !seen.insert(unit.clone()) {
            return;
        }
        own(graph, unit, found);
        for dep in &graph[unit] {
            if !dep.unit.target.for_host() && dep.unit.target.is_linkable() {
                to_link(graph, &dep.unit, seen, found);
            }
        }
    }
    let mut found = Vec::new();
    let mut seen = HashSet::default();
    own(graph, unit, &mut found);
    for dep in &graph[unit] {
        if dep.unit.target.for_host() || dep.unit.target.is_linkable() {
            to_link(graph, &dep.unit, &mut seen, &mut found);
        }
    }
    found.sort();
    found
}

/// Trust (DC-18c): the units outside the workspace whose command takes a
/// member's build-script output: those that link, directly or through other
/// libraries, a member whose package has a build script.
fn script_dependents(graph: &UnitGraph, eligibility: &Eligibility) -> HashSet<Unit> {
    fn links(
        graph: &UnitGraph,
        eligibility: &Eligibility,
        unit: &Unit,
        memo: &mut HashMap<Unit, bool>,
    ) -> bool {
        if let Some(known) = memo.get(unit) {
            return *known;
        }
        let found = graph[unit].iter().any(|dep| {
            !dep.unit.target.for_host()
                && dep.unit.target.is_linkable()
                && ((eligibility.member(&dep.unit) && dep.unit.pkg.has_custom_build())
                    || links(graph, eligibility, &dep.unit, memo))
        });
        memo.insert(unit.clone(), found);
        found
    }
    let mut memo = HashMap::default();
    graph
        .keys()
        .filter(|unit| !eligibility.member(unit) && links(graph, eligibility, unit, &mut memo))
        .cloned()
        .collect()
}

/// The paths git reports changed in the work tree that holds `workspace`,
/// at or below it. A status git cannot give counts as the whole workspace
/// changed.
fn uncommitted_paths(workspace: &Path) -> Option<Vec<PathBuf>> {
    let repository = git2::Repository::discover(workspace).ok()?;
    let workdir = repository.workdir()?.canonicalize().ok()?;
    let Ok(workspace) = workspace.canonicalize() else {
        return Some(vec![workdir]);
    };
    let mut options = git2::StatusOptions::new();
    options
        .include_untracked(true)
        .include_ignored(false)
        .recurse_untracked_dirs(false);
    if let Ok(relative) = workspace.strip_prefix(&workdir)
        && !relative.as_os_str().is_empty()
    {
        options.pathspec(relative);
    }
    let Ok(statuses) = repository.statuses(Some(&mut options)) else {
        return Some(vec![workspace]);
    };
    Some(
        statuses
            .iter()
            .filter(|entry| {
                entry.status() != git2::Status::CURRENT
                    && !entry.status().contains(git2::Status::IGNORED)
            })
            .map(|entry| match entry.path() {
                Ok(path) => workdir.join(path),
                // A name git cannot spell here changes the whole workspace.
                Err(_) => workspace.clone(),
            })
            .collect(),
    )
}

pub(super) fn eligible_units(
    graph: &UnitGraph,
    roots: &[Unit],
    eligibility: &Eligibility,
) -> HashSet<Unit> {
    let candidates: Vec<_> = graph
        .keys()
        .filter(|unit| direct_exclusion(unit, roots, eligibility).is_none())
        .cloned()
        .collect();
    let mut selected = HashSet::default();
    loop {
        let previous = selected.len();
        for unit in &candidates {
            // Trust (DC-18c): a member's slot is named by what it is keyed
            // on; those units stay per checkout.
            if graph[unit]
                .iter()
                .all(|dep| selected.contains(&dep.unit) || eligibility.keyed(unit, &dep.unit))
            {
                selected.insert(unit.clone());
            }
        }
        if selected.len() == previous {
            return selected;
        }
    }
}

/// Use the SAME predicate for selection and diagnostic exclusion reasons.
/// The selected set still requires the dependency closure above.
pub(super) fn direct_exclusion(
    unit: &Unit,
    roots: &[Unit],
    eligibility: &Eligibility,
) -> Option<SharedDependencyExclusion> {
    use SharedDependencyExclusion::*;
    let source = unit.pkg.package_id().source_id();
    // Trust (DC-18b): a workspace member's library is a candidate too, named
    // by the build or not; whether it may be shared is decided below.
    let member = eligibility.member(unit);
    if !(member
        || source.is_registry()
        || resolved_git_commit(source).is_some()
        || (source.is_path() && !unit.pkg.root().starts_with(&eligibility.workspace)))
    {
        return Some(SourceNotShareable);
    }
    if !member
        && roots
            .iter()
            .any(|root| root.pkg.package_id() == unit.pkg.package_id())
    {
        return Some(RequestedPackage);
    }
    if !unit.target.is_lib() || unit.target.is_custom_build() {
        return Some(NonLibrary);
    }
    if unit.artifact.is_true() {
        return Some(ArtifactDependency);
    }
    if unit.target.proc_macro() {
        return Some(ProceduralMacro);
    }
    // Trust (DC-18c): a member's build script runs in each checkout, and the
    // member's slot is named by its output; any other package's stays private.
    if !member
        && unit
            .pkg
            .targets()
            .iter()
            .any(|target| target.is_custom_build())
    {
        return Some(BuildScriptPackage);
    }
    if unit.mode.is_any_test() || !(unit.mode.is_check() || unit.mode == CompileMode::Build) {
        return Some(UnsupportedMode);
    }
    if !unit
        .target
        .rustc_crate_types()
        .iter()
        .all(|kind| matches!(kind, CrateType::Lib | CrateType::Rlib))
    {
        return Some(UnsupportedCrateType);
    }
    if member {
        return eligibility.member_exclusion(unit);
    }
    if eligibility.script_dependents.contains(unit) {
        return Some(MemberScriptDependency);
    }
    None
}

/// Trust (DC-18b): a member unit's name in private records and in this
/// process's refusals: what the unit is, never where its checkout is.
pub(crate) fn member_key(unit: &Unit) -> String {
    let id = unit.pkg.package_id();
    let fields = [
        "targo-member-unit-v1".to_string(),
        id.name().to_string(),
        id.version().to_string(),
        unit.target.name().to_string(),
        format!("{:?}", unit.target.kind()),
        format!("{:?}", unit.mode),
        format!("{:?}", unit.features),
        format!("{:?}", unit.kind),
        format!("{:?}", unit.profile),
    ];
    digest_fields(&fields.iter().map(String::as_str).collect::<Vec<_>>())[..32].to_string()
}

fn digest_fields(fields: &[&str]) -> String {
    let mut hash = Sha256::new();
    for field in fields {
        hash.update(&(field.len() as u64).to_le_bytes());
        hash.update(field.as_bytes());
    }
    hash.finish_hex()
}

/// Trust (DC-18b): what a member's private record holds for.
#[derive(Clone, Debug)]
struct Bindings {
    /// The environment, the compiler, the lockfile and the member's manifest:
    /// a path-bound refusal follows what the member expands from its
    /// dependencies, which an edit of its own sources rarely changes, so an
    /// edit does not try the member again.
    stable: String,
    /// The member's sources (digested without the checkout's path), the
    /// environment and the compiler: a failed compile or a differing slot is
    /// tried again once any of them moves.
    sources: String,
}

impl Bindings {
    /// The exclusion a record's line holds for, where it still holds.
    fn reason(&self, line: &str) -> Option<SharedDependencyExclusion> {
        use SharedDependencyExclusion::*;
        let (kind, binding) = line.split_once(' ')?;
        let (reason, holds) = match kind {
            "path-bound" => (PathBound, &self.stable),
            "compile-failed" => (MemberCompileFailed, &self.sources),
            "slot-differs" => (MemberSlotDiffers, &self.sources),
            _ => return None,
        };
        (binding == holds).then_some(reason)
    }

    fn line(&self, reason: SharedDependencyExclusion) -> Option<String> {
        use SharedDependencyExclusion::*;
        match reason {
            PathBound => Some(format!("path-bound {}", self.stable)),
            MemberCompileFailed => Some(format!("compile-failed {}", self.sources)),
            MemberSlotDiffers => Some(format!("slot-differs {}", self.sources)),
            _ => None,
        }
    }
}

/// Trust (DC-18b): a member unit an attempt of this build refused to share.
/// The job queue counts it as a failure without printing it, and
/// `compile_ws` plans the build again with the unit private.
#[derive(Debug)]
pub(crate) struct MemberRefusal {
    pub(crate) package: String,
    pub(crate) reason: SharedDependencyExclusion,
    /// Trust (DC-18c): the member is planned again shared, under the slot
    /// its inputs now name, rather than private.
    pub(crate) renamed: bool,
}

impl std::fmt::Display for MemberRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.renamed {
            write!(
                f,
                "what `{}` is keyed on changed since the build was planned; planning the build again",
                self.package
            )
        } else {
            write!(
                f,
                "`{}` is compiled privately ({:?}); planning the build again",
                self.package, self.reason
            )
        }
    }
}

impl std::error::Error for MemberRefusal {}

/// Member units this process refused to share, and why: every later attempt
/// plans them private.
static PRIVATE: Mutex<BTreeMap<String, SharedDependencyExclusion>> = Mutex::new(BTreeMap::new());
/// The running attempt refused a member unit.
static REFUSED: AtomicBool = AtomicBool::new(false);
/// The running attempt failed for a reason a plan cannot change.
static FAILED: AtomicBool = AtomicBool::new(false);
/// An attempt refused nothing new: members are no longer admitted.
static WITHDRAWN: AtomicBool = AtomicBool::new(false);
/// Trust (DC-18c): member units whose keyed inputs changed after an attempt
/// of this process planned them: the next attempt names their slots from
/// the inputs as they are then, and a second change makes them private.
static RENAMED: Mutex<std::collections::BTreeSet<String>> =
    Mutex::new(std::collections::BTreeSet::new());

/// Trust (DC-18b): what a shared member's refusal records, prepared while the
/// build is planned, for a job that runs without the build context.
#[derive(Clone, Debug)]
pub(crate) struct MemberRecorder {
    path: PathBuf,
    key: String,
    package: String,
    bindings: Bindings,
}

impl MemberRecorder {
    /// Refuses the member for this process and, where the reason outlives it
    /// (a path-bound member, a failed compile, a differing slot), records it
    /// in the checkout's build directory, never in the store. A record that
    /// cannot be written leaves the refusal in this process only.
    pub(crate) fn refuse(&self, reason: SharedDependencyExclusion) -> anyhow::Error {
        self.refusal(reason, true)
    }

    /// Refuses the member for this process only: what moved (its sources
    /// during the build) is tried again by the next invocation.
    pub(crate) fn refuse_for_now(&self, reason: SharedDependencyExclusion) -> anyhow::Error {
        self.refusal(reason, false)
    }

    fn refusal(&self, reason: SharedDependencyExclusion, record: bool) -> anyhow::Error {
        if let Some(line) = self.bindings.line(reason).filter(|_| record) {
            let written = (|| -> CargoResult<()> {
                if let Some(parent) = self.path.parent() {
                    fs::create_dir_all(parent)?;
                }
                cargo_util::paths::write_atomic(&self.path, format!("{line}\n"))
            })();
            if let Err(error) = written {
                tracing::debug!(
                    "could not record why `{}` is private: {error:#}",
                    self.package
                );
            }
        }
        PRIVATE
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(self.key.clone(), reason);
        REFUSED.store(true, Ordering::SeqCst);
        anyhow::Error::new(MemberRefusal {
            package: self.package.clone(),
            reason,
            renamed: false,
        })
    }

    /// Trust (DC-18c): what the member is keyed on (a build script's output,
    /// a proc macro's library) is not what its slot was named by when the
    /// build was planned: a script or macro of this checkout ran since. The
    /// member is refused and the build planned again, which names its slot
    /// by what is there now. A member whose inputs change again after that
    /// is private for this process.
    pub(crate) fn rename(&self) -> anyhow::Error {
        let first = RENAMED
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(self.key.clone());
        if !first {
            return self.refuse_for_now(SharedDependencyExclusion::MemberInputsMoved);
        }
        REFUSED.store(true, Ordering::SeqCst);
        anyhow::Error::new(MemberRefusal {
            package: self.package.clone(),
            reason: SharedDependencyExclusion::MemberInputsMoved,
            renamed: true,
        })
    }
}

/// Trust (DC-18c): what a shared member's slot is named by beyond its
/// sources, its command and its dependencies' slots: the output of every
/// build script whose output Targo lays over its command (its own, and those
/// of what it links or loads), its own script's `OUT_DIR` tree, which its
/// compile may read, and the bytes of each proc macro it loads. These stay
/// per checkout: two checkouts whose scripts printed the same directives and
/// whose macros are the same bytes name one slot, and any difference names
/// another. Read when the build is planned, and again before the member's
/// job uses its slot: the scripts and macros have run by then.
#[derive(Debug)]
pub(crate) struct MemberInputs {
    /// Each script run's label (package and unit hash), its stdout file, and,
    /// for the member's own scripts, its `OUT_DIR`.
    scripts: Vec<(String, PathBuf, Option<PathBuf>)>,
    /// Each proc macro's label (extern name and unit hash) and the library
    /// the member's command loads.
    macros: Vec<(String, PathBuf)>,
    digest: String,
}

impl MemberInputs {
    pub(crate) fn capture(
        mut scripts: Vec<(String, PathBuf, Option<PathBuf>)>,
        mut macros: Vec<(String, PathBuf)>,
    ) -> CargoResult<Self> {
        scripts.sort();
        macros.sort();
        let mut inputs = MemberInputs {
            scripts,
            macros,
            digest: String::new(),
        };
        inputs.digest = inputs.read()?;
        Ok(inputs)
    }

    pub(crate) fn digest(&self) -> &str {
        &self.digest
    }

    /// The proc-macro libraries the member's command passes with `--extern`.
    pub(crate) fn macro_libraries(&self) -> impl Iterator<Item = &Path> {
        self.macros.iter().map(|(_, path)| path.as_path())
    }

    /// Whether every script run has printed and every proc macro is built:
    /// a slot named by an absent input could never be the one used.
    pub(crate) fn complete(&self) -> bool {
        self.scripts
            .iter()
            .map(|(_, output, _)| output)
            .chain(self.macros.iter().map(|(_, library)| library))
            .all(|path| path.is_file())
    }

    /// Whether the inputs read as they did when the slot was named.
    pub(crate) fn current(&self) -> CargoResult<bool> {
        Ok(self.read()? == self.digest)
    }

    fn read(&self) -> CargoResult<String> {
        let file = |path: &Path| -> CargoResult<String> {
            match file_digest(path) {
                Ok(digest) => Ok(format!("present:{digest}")),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    Ok("absent".to_string())
                }
                Err(error) => Err(error.into()),
            }
        };
        let mut fields = vec!["targo-member-inputs-v1".to_string()];
        for (label, output, out_dir) in &self.scripts {
            fields.push(format!("script:{label}"));
            fields.push(file(output)?);
            if let Some(out_dir) = out_dir {
                fields.push(match fs::symlink_metadata(out_dir) {
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                        "absent".to_string()
                    }
                    _ => format!(
                        "out-dir:{}",
                        SourceInputs::capture_relocatable(out_dir, out_dir)?.digest()
                    ),
                });
            }
        }
        for (label, library) in &self.macros {
            fields.push(format!("macro:{label}"));
            fields.push(file(library)?);
        }
        Ok(digest_fields(
            &fields.iter().map(String::as_str).collect::<Vec<_>>(),
        ))
    }
}

/// Trust (DC-18c): the SHA-256 of a file a member is keyed on. Every member
/// that loads one proc macro hashes its library when the build is planned and
/// again before its job, so the digest is kept for this process while the
/// file is the same file, unchanged: its device, inode, size, and its
/// modification and status-change times. A write changes the status-change
/// time; a replacement changes the inode.
fn file_digest(path: &Path) -> std::io::Result<String> {
    static DIGESTS: Mutex<BTreeMap<PathBuf, (FileIdentity, String)>> = Mutex::new(BTreeMap::new());
    let file = fs::File::open(path)?;
    let before = FileIdentity::of(&file.metadata()?);
    if let Some(before) = &before
        && let Some((known, digest)) = DIGESTS
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(path)
        && known == before
    {
        return Ok(digest.clone());
    }
    let digest = Sha256::new().update_file(&file)?.finish_hex();
    // A file that changed while it was read is not remembered.
    if let Some(before) = before
        && FileIdentity::of(&file.metadata()?).as_ref() == Some(&before)
    {
        DIGESTS
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(path.to_path_buf(), (before, digest.clone()));
    }
    Ok(digest)
}

/// Trust (DC-18c): which file a path names and whether it was written since:
/// its device, inode and size, and its modification and status-change times.
/// A host without them remembers no digest.
#[derive(Clone, Debug, PartialEq, Eq)]
struct FileIdentity([i128; 7]);

impl FileIdentity {
    #[cfg(unix)]
    fn of(metadata: &fs::Metadata) -> Option<Self> {
        use std::os::unix::fs::MetadataExt as _;
        Some(FileIdentity([
            metadata.dev().into(),
            metadata.ino().into(),
            metadata.size().into(),
            metadata.mtime().into(),
            metadata.mtime_nsec().into(),
            metadata.ctime().into(),
            metadata.ctime_nsec().into(),
        ]))
    }

    #[cfg(not(unix))]
    fn of(_: &fs::Metadata) -> Option<Self> {
        None
    }
}

/// Trust (DC-18c): the checkout's own directories, as spelled and as
/// canonical: the workspace, the member's package, and the target and build
/// directories. `-Ztrust-path-free` judges a member's metadata; code a proc
/// macro emits from an untracked read (`std::env::var("CARGO_MANIFEST_DIR")`,
/// the working directory, `Span::local_file`) reaches only the object code,
/// which no key binds. A shared member's outputs are searched for these
/// before its job ends, and one that names its checkout is path-bound.
/// The compiler's dep-info is not searched: it names each input the compile
/// read, a proc macro's library and a script's `OUT_DIR` files among them, at
/// the compiling checkout's path, and the key binds those inputs' bytes.
/// Directories every checkout of this store shares (the store, the cargo
/// home, `HOME`) bind no slot to a checkout and are not searched for: the
/// store's own path is in every slot's dep-info.
#[derive(Clone, Debug)]
pub(crate) struct CheckoutPrefixes(Vec<Vec<u8>>);

impl CheckoutPrefixes {
    pub(crate) fn new<'p>(directories: impl IntoIterator<Item = &'p Path>) -> Self {
        let mut prefixes = Vec::new();
        for directory in directories {
            let canonical = directory.canonicalize().ok();
            for spelling in std::iter::once(directory).chain(canonical.as_deref()) {
                let bytes = spelling.as_os_str().as_encoded_bytes().to_vec();
                // A root names every path; such a checkout has no spelling of
                // its own to search for.
                if bytes.len() > 1 && !prefixes.contains(&bytes) {
                    prefixes.push(bytes);
                }
            }
        }
        CheckoutPrefixes(prefixes)
    }

    /// The first regular file below `dir`, other than the compiler's
    /// `dep_info`, whose bytes name the checkout, and the directory it names.
    /// An entry that cannot be read is an error.
    pub(crate) fn named_below(
        &self,
        dir: &Path,
        dep_info: &Path,
    ) -> CargoResult<Option<(PathBuf, String)>> {
        for file in regular_files(dir)? {
            if file == dep_info {
                continue;
            }
            let bytes = fs::read(&file)?;
            for prefix in &self.0 {
                if memchr::memmem::find(&bytes, prefix).is_some() {
                    return Ok(Some((file, String::from_utf8_lossy(prefix).into_owned())));
                }
            }
        }
        Ok(None)
    }
}

/// Trust (DC-18c): removes a refused shared member's outputs from its slot.
/// Metadata that names no checkout directory stays: `-Ztrust-path-free`
/// judged it, and a dependent this attempt started on it (pipelining) may be
/// reading it. With no library and no fingerprint the slot is never fresh,
/// and the next compile into it writes every output again.
pub(crate) fn withdraw_outputs(dir: &Path, prefixes: &CheckoutPrefixes) {
    for file in regular_files(dir).unwrap_or_default() {
        let metadata = file
            .extension()
            .is_some_and(|extension| extension == "rmeta");
        if metadata
            && fs::read(&file).is_ok_and(|bytes| {
                !prefixes
                    .0
                    .iter()
                    .any(|prefix| memchr::memmem::find(&bytes, prefix).is_some())
            })
        {
            continue;
        }
        if let Err(error) = fs::remove_file(&file) {
            tracing::debug!("could not remove {}: {error}", file.display());
        }
    }
}

/// Every regular file below `dir`; a link is not followed.
pub(crate) fn regular_files(dir: &Path) -> CargoResult<Vec<PathBuf>> {
    let mut found = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(dir) = pending.pop() {
        let entries = match fs::read_dir(&dir) {
            Ok(entries) => entries,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => return Err(error.into()),
        };
        for entry in entries {
            let entry = entry?;
            let kind = entry.file_type()?;
            if kind.is_dir() {
                pending.push(entry.path());
            } else if kind.is_file() {
                found.push(entry.path());
            }
        }
    }
    found.sort();
    Ok(found)
}

/// Trust (DC-18c): the check a member keyed on per-checkout inputs runs
/// before its job uses its slot, fresh or not: a slot named by inputs that
/// have changed since is never read or written, and a waiting slot never is.
pub(crate) fn check_member_inputs(
    inputs: Option<Arc<MemberInputs>>,
    waiting: bool,
    recorder: MemberRecorder,
) -> super::job_queue::Work {
    super::job_queue::Work::new(
        move |_| match inputs.as_deref().map(MemberInputs::current) {
            _ if waiting => Err(recorder.rename()),
            None | Some(Ok(true)) => Ok(()),
            Some(Ok(false)) => Err(recorder.rename()),
            Some(Err(error)) => {
                tracing::debug!("member inputs cannot be read: {error:#}");
                Err(recorder.refuse_for_now(SharedDependencyExclusion::MemberInputsMoved))
            }
        },
    )
}

/// Trust (DC-18c): the waiting slots this process's attempt planned, which no
/// other process names and no job of it used.
static WAITING: Mutex<Vec<PathBuf>> = Mutex::new(Vec::new());

pub(crate) fn waiting_slot(dir: PathBuf) {
    WAITING
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .push(dir);
}

/// Trust (DC-18c): removes the waiting slots of the attempt that just ended.
pub(crate) fn remove_waiting_slots() {
    let slots = std::mem::take(&mut *WAITING.lock().unwrap_or_else(PoisonError::into_inner));
    for slot in slots {
        if let Err(error) = fs::remove_dir_all(&slot)
            && error.kind() != std::io::ErrorKind::NotFound
        {
            tracing::debug!("could not remove {}: {error}", slot.display());
        }
    }
}

/// Trust (DC-18b): a job's error that no plan with fewer shared members can
/// avoid. An attempt that also refused a member reports it as it is.
pub(crate) fn note_failure() {
    FAILED.store(true, Ordering::SeqCst);
}

/// Trust (DC-18b): the running attempt will be planned again: it refused a
/// member and failed for no other reason.
pub(crate) fn replan_pending() -> bool {
    REFUSED.load(Ordering::SeqCst) && !FAILED.load(Ordering::SeqCst)
}

/// Trust (DC-18b): how one attempt of `compile_ws` ended, for the next.
pub(crate) struct Attempt {
    private: usize,
}

/// Members made private, and members renamed (DC-18c), by this process:
/// each refusal adds one, and neither set loses one.
fn refusals() -> usize {
    PRIVATE.lock().unwrap_or_else(PoisonError::into_inner).len()
        + RENAMED.lock().unwrap_or_else(PoisonError::into_inner).len()
}

impl Attempt {
    pub(crate) fn begin() -> Self {
        REFUSED.store(false, Ordering::SeqCst);
        FAILED.store(false, Ordering::SeqCst);
        Attempt {
            private: refusals(),
        }
    }

    /// Whether the attempt that just ended is to be planned again. Each
    /// refusal makes one more member unit private, or renames one for the
    /// first time (DC-18c); an attempt that refused none new withdraws
    /// members altogether, so the next plan shares no member and refuses
    /// nothing: the attempts end.
    pub(crate) fn replan(self) -> bool {
        let refused = REFUSED.swap(false, Ordering::SeqCst);
        let failed = FAILED.swap(false, Ordering::SeqCst);
        if !refused || failed || WITHDRAWN.load(Ordering::SeqCst) {
            return false;
        }
        if refusals() == self.private {
            WITHDRAWN.store(true, Ordering::SeqCst);
        }
        true
    }
}

pub(super) fn log_policy(build: &super::BuildContext<'_, '_>) {
    use crate::util::log_message::{
        LogMessage, SHARED_DEPENDENCY_POLICY_VERSION, SharedDependencyDecision,
    };
    let Some(logger) = build.logger else { return };
    let enabled = build.shared_dependency_root.is_some();
    let mut members: Vec<_> = build
        .unit_to_index
        .iter()
        .filter(|(unit, _)| enabled && build.shared_eligibility.member(unit))
        .map(|(_, index)| *index)
        .collect();
    members.sort_unstable();
    // Trust (DC-18c): what a member may be keyed on instead of sharing.
    let mut keyed: Vec<_> = build
        .unit_graph
        .iter()
        .filter(|_| enabled)
        .flat_map(|(parent, deps)| {
            deps.iter()
                .filter(move |dep| build.shared_eligibility.keyed(parent, &dep.unit))
                .map(|dep| build.unit_to_index[&dep.unit])
        })
        .collect();
    keyed.sort_unstable();
    keyed.dedup();
    logger.log(LogMessage::SharedDependencyPolicy {
        version: SHARED_DEPENDENCY_POLICY_VERSION,
        enabled,
        members,
        keyed,
    });
    if !enabled {
        return;
    }
    // Stable native indices preserve duplicate package labels and edge identity.
    let mut units: Vec<_> = build.unit_to_index.iter().collect();
    units.sort_by_key(|(_, index)| **index);
    for (unit, index) in units {
        let decision = if build.shared_dependency_units.contains(unit) {
            SharedDependencyDecision::Eligible {}
        } else if let Some(reason) = direct_exclusion(unit, &build.roots, &build.shared_eligibility)
        {
            SharedDependencyDecision::Excluded { reason }
        } else {
            let mut dependencies: Vec<_> = build.unit_graph[unit]
                .iter()
                .filter(|dep| {
                    !build.shared_dependency_units.contains(&dep.unit)
                        && !build.shared_eligibility.keyed(unit, &dep.unit)
                })
                .map(|dep| build.unit_to_index[&dep.unit])
                .collect();
            dependencies.sort_unstable();
            dependencies.dedup();
            SharedDependencyDecision::DependencyBlocked { dependencies }
        };
        logger.log(LogMessage::SharedDependencyDecision {
            index: *index,
            decision,
        });
    }
}

pub(super) fn storage_root(home: &Path) -> CargoResult<PathBuf> {
    let mut root = home.canonicalize()?;
    private_parent(&root)?;
    for name in ["trust", "native-dependencies-v1"] {
        root.push(name);
        match fs::symlink_metadata(&root) {
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                let mut builder = fs::DirBuilder::new();
                #[cfg(unix)]
                {
                    use std::os::unix::fs::DirBuilderExt;
                    builder.mode(0o700);
                }
                match builder.create(&root) {
                    Ok(()) => {}
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                    Err(error) => return Err(error.into()),
                }
            }
            Err(error) => return Err(error.into()),
        }
        private_parent(&root)?;
    }
    Ok(root)
}

fn private_parent(path: &Path) -> CargoResult<()> {
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.is_dir() || metadata.file_type().is_symlink() {
        bail!(
            "shared dependency storage requires a plain directory: {}",
            path.display()
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if metadata.uid() != unsafe { libc::geteuid() } || metadata.mode() & 0o022 != 0 {
            bail!(
                "shared dependency storage must be owned by this user and not writable by other users: {}",
                path.display()
            );
        }
        crate::util::process_authority::validate_user_cache_directory(path)?;
    }
    #[cfg(target_os = "macos")]
    {
        use std::os::unix::ffi::OsStrExt;
        let path = std::ffi::CString::new(path.as_os_str().as_bytes())?;
        let mut mount = std::mem::MaybeUninit::<libc::statfs>::zeroed();
        // SAFETY: the path is NUL-terminated and statfs writes one full struct.
        if unsafe { libc::statfs(path.as_ptr(), mount.as_mut_ptr()) } != 0 {
            return Err(std::io::Error::last_os_error().into());
        }
        let mount = unsafe { mount.assume_init() };
        if mount.f_flags & libc::MNT_LOCAL as u32 == 0 {
            bail!("shared dependency storage requires a local filesystem with kernel file locks");
        }
    }
    Ok(())
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    #[test]
    fn git_identity_requires_and_binds_the_full_resolved_revision() {
        let source = SourceId::for_git(
            &"https://example.invalid/library".parse().unwrap(),
            GitReference::DefaultBranch,
        )
        .unwrap();
        assert!(git_source_identity(source).is_none());
        assert!(git_source_identity(source.with_git_precise(Some("abcdef0".into()))).is_none());
        assert!(git_source_identity(source.with_git_precise(Some("z".repeat(40)))).is_none());
        let first = source.with_git_precise(Some("1".repeat(40)));
        let second = source.with_git_precise(Some("2".repeat(40)));
        // Ordinary package/source equality deliberately cannot distinguish these.
        assert_eq!(first, second);
        assert_ne!(git_source_identity(first), git_source_identity(second));
    }

    #[test]
    fn git_identity_separates_url_query_and_reference_selector() {
        let query = SourceId::for_git(
            &"https://example.invalid/library?branch=next"
                .parse()
                .unwrap(),
            GitReference::DefaultBranch,
        )
        .unwrap()
        .with_git_precise(Some("1".repeat(40)));
        let branch = SourceId::for_git(
            &"https://example.invalid/library".parse().unwrap(),
            GitReference::Branch("next".into()),
        )
        .unwrap()
        .with_git_precise(Some("1".repeat(40)));
        assert_ne!(git_source_identity(query), git_source_identity(branch));
    }

    /// A native unverified Targo build on Apple silicon with the key set and
    /// no `-Z` flag: the lane every not-applied test departs from by one field.
    fn native_lane() -> CacheLane<'static> {
        CacheLane {
            requested: true,
            targo: true,
            verified: false,
            os: "macos",
            arch: "aarch64",
            compiler_host: "aarch64-apple-darwin",
            compiler_wrapper: false,
            new_layout: true,
            fine_grain_flag: false,
        }
    }

    /// The policy of the same build with the key unset.
    fn unset(lane: CacheLane<'_>) -> CachePolicy {
        cache_policy(CacheLane {
            requested: false,
            ..lane
        })
    }

    /// Asserts `lane` runs exactly as with the key unset, with and without
    /// `-Zfine-grain-locking`, while the native lane it departs from shares.
    fn assert_not_applied(lane: CacheLane<'_>) {
        assert_eq!(
            cache_policy(native_lane()),
            CachePolicy {
                shares: true,
                fine_grain_locking: true
            }
        );
        for fine_grain_flag in [false, true] {
            let lane = CacheLane {
                fine_grain_flag,
                ..lane
            };
            assert_eq!(cache_policy(lane), unset(lane), "{lane:?}");
            assert_eq!(
                cache_policy(lane),
                CachePolicy {
                    shares: false,
                    fine_grain_locking: fine_grain_flag
                },
                "{lane:?}"
            );
        }
    }

    #[test]
    fn the_key_turns_fine_grain_locking_on_where_it_shares() {
        let policy = cache_policy(native_lane());
        assert!(policy.shares);
        assert!(policy.fine_grain_locking, "no -Z flag was given");
        assert!(!unset(native_lane()).fine_grain_locking);
        let flagged = CacheLane {
            fine_grain_flag: true,
            ..native_lane()
        };
        assert_eq!(cache_policy(flagged), cache_policy(native_lane()));
        assert_eq!(
            cache_policy(CacheLane {
                arch: "x86_64",
                compiler_host: "x86_64-apple-darwin",
                ..native_lane()
            }),
            cache_policy(native_lane())
        );
    }

    #[test]
    fn cache_key_is_not_applied_on_a_verified_lane() {
        assert_not_applied(CacheLane {
            verified: true,
            ..native_lane()
        });
    }

    /// DC-18b: every spelling of a caller's path remap keeps members private.
    #[test]
    fn caller_path_remaps_are_recognized() {
        for flags in [
            &["--remap-path-prefix=/a=b"][..],
            &["--remap-path-prefix", "/a=b"],
            &["--remap-path-scope=all"],
            &["-Zremap-cwd-prefix=."],
            &["-Z", "remap-cwd-prefix=."],
        ] {
            assert!(remaps_paths(flags.iter().copied()), "{flags:?}");
        }
        for flags in [
            &["-Copt-level=3"][..],
            &["-Z", "share-generics"],
            &["--cfg", "remap"],
        ] {
            assert!(!remaps_paths(flags.iter().copied()), "{flags:?}");
        }
    }

    #[test]
    fn cache_key_is_not_applied_with_a_compiler_wrapper() {
        assert_not_applied(CacheLane {
            compiler_wrapper: true,
            ..native_lane()
        });
    }

    #[test]
    fn cache_key_is_not_applied_off_macos() {
        for (os, compiler_host) in [
            ("linux", "aarch64-unknown-linux-gnu"),
            ("windows", "aarch64-pc-windows-msvc"),
            ("freebsd", "aarch64-unknown-freebsd"),
            // A compiler that reports the Apple triple does not make the host macOS.
            ("linux", "aarch64-apple-darwin"),
        ] {
            assert_not_applied(CacheLane {
                os,
                compiler_host,
                ..native_lane()
            });
        }
    }

    #[test]
    fn the_key_is_not_applied_to_cargo_a_foreign_host_or_the_legacy_layout() {
        assert_not_applied(CacheLane {
            targo: false,
            ..native_lane()
        });
        for compiler_host in [
            "x86_64-apple-darwin",
            "arm64e-apple-darwin",
            "aarch64-apple-ios",
        ] {
            assert_not_applied(CacheLane {
                compiler_host,
                ..native_lane()
            });
        }
        assert_not_applied(CacheLane {
            new_layout: false,
            ..native_lane()
        });
    }

    #[test]
    fn storage_uses_one_owned_private_namespace() {
        let home = tempfile::tempdir().unwrap();
        let root = storage_root(home.path()).unwrap();
        assert_eq!(
            root,
            home.path()
                .canonicalize()
                .unwrap()
                .join("trust/native-dependencies-v1")
        );
        assert_eq!(fs::metadata(&root).unwrap().mode() & 0o077, 0);
        assert_eq!(storage_root(home.path()).unwrap(), root);
    }

    #[test]
    fn redirected_or_shared_writable_storage_is_refused() {
        let home = tempfile::tempdir().unwrap();
        let outside = tempfile::tempdir().unwrap();
        std::os::unix::fs::symlink(outside.path(), home.path().join("trust")).unwrap();
        assert!(storage_root(home.path()).is_err());
        assert!(!outside.path().join("native-dependencies-v1").exists());
        fs::remove_file(home.path().join("trust")).unwrap();
        fs::set_permissions(home.path(), fs::Permissions::from_mode(0o777)).unwrap();
        assert!(storage_root(home.path()).is_err());
    }
}
