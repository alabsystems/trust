//! See [`CompilationFiles`].

use crate::util::data_structures::{HashMap, HashSet};
use std::borrow::Borrow;
use std::cell::OnceCell;
use std::fmt;
use std::hash::{Hash, Hasher};
#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::os::unix::ffi::OsStrExt as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use tracing::debug;

use super::{BuildContext, BuildRunner, CompileKind, FileFlavor, Layout};
use crate::compiler::layout::LayoutPaths;
use crate::compiler::lto::Lto;
use crate::compiler::trim_paths;
use crate::compiler::trust_unit_id::{self, SessionInvariantLane, without_per_run_transport};
use crate::compiler::{CompileMode, CompileTarget, CrateType, FileType, Unit};
use crate::util::{self, CargoResult, OnceExt, StableHasher};
use crate::workspace::{PackageId, Target, TargetKind, Workspace};

/// This is a generic version number that can be changed to make
/// backwards-incompatible changes to any file structures in the output
/// directory. For example, the fingerprint files or the build-script
/// output files.
///
/// Normally cargo updates ship with rustc updates which will
/// cause a new hash due to the rustc version changing, but this allows
/// cargo to be extra careful to deal with different versions of cargo that
/// use the same rustc version.
const METADATA_VERSION: u8 = 2;

/// Uniquely identify a [`Unit`] under specific circumstances, see [`Metadata`] for more.
#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct UnitHash(u64);

impl fmt::Display for UnitHash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}", self.0)
    }
}

impl fmt::Debug for UnitHash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UnitHash({:016x})", self.0)
    }
}

/// [`Metadata`] tracks several [`UnitHash`]s, including
/// [`Metadata::unit_id`], [`Metadata::c_metadata`], and [`Metadata::c_extra_filename`].
///
/// We use a hash because it is an easy way to guarantee
/// that all the inputs can be converted to a valid path.
///
/// [`Metadata::unit_id`] is used to uniquely identify a unit in the build graph.
/// This serves as a similar role as [`Metadata::c_extra_filename`] in that it uniquely identifies output
/// on the filesystem except that its always present.
///
/// [`Metadata::c_extra_filename`] is needed for cases like:
/// - A project may depend on crate `A` and crate `B`, so the package name must be in the file name.
/// - Similarly a project may depend on two versions of `A`, so the version must be in the file name.
///
/// This also acts as the main layer of caching provided by Cargo
/// so this must include all things that need to be distinguished in different parts of
/// the same build. This is absolutely required or we override things before
/// we get chance to use them.
///
/// For example, we want to cache `cargo build` and `cargo doc` separately, so that running one
/// does not invalidate the artifacts for the other. We do this by including [`CompileMode`] in the
/// hash, thus the artifacts go in different folders and do not override each other.
/// If we don't add something that we should have, for this reason, we get the
/// correct output but rebuild more than is needed.
///
/// Some things that need to be tracked to ensure the correct output should definitely *not*
/// go in the `Metadata`. For example, the modification time of a file, should be tracked to make a
/// rebuild when the file changes. However, it would be wasteful to include in the `Metadata`. The
/// old artifacts are never going to be needed again. We can save space by just overwriting them.
/// If we add something that we should not have, for this reason, we get the correct output but take
/// more space than needed. This makes not including something in `Metadata`
/// a form of cache invalidation.
///
/// Note that the `Fingerprint` is in charge of tracking everything needed to determine if a
/// rebuild is needed.
///
/// [`Metadata::c_metadata`] is used for symbol mangling, because if you have two versions of
/// the same crate linked together, their symbols need to be differentiated.
///
/// You should avoid anything that would interfere with reproducible
/// builds. For example, *any* absolute path should be avoided. This is one
/// reason that `RUSTFLAGS` is not in [`Metadata::c_metadata`], because it often has
/// absolute paths (like `--remap-path-prefix` which is fundamentally used for
/// reproducible builds and has absolute paths in it). Also, in some cases the
/// mangled symbols need to be stable between different builds with different
/// settings. For example, profile-guided optimizations need to swap
/// `RUSTFLAGS` between runs, but needs to keep the same symbol names.
#[derive(Copy, Clone, Debug)]
pub struct Metadata {
    unit_id: UnitHash,
    /// Trust: shared storage alone includes flags omitted for reproducible metadata.
    shared_storage_id: UnitHash,
    c_metadata: UnitHash,
    c_extra_filename: bool,
    pkg_dir: bool,
}

impl Metadata {
    // Trust: keep ordinary short-hash fallbacks; only a shared storage variant
    // replaces the existing directory identity.
    fn shared_storage_hash(&self, ordinary: String) -> String {
        if self.shared_storage_id == self.unit_id {
            ordinary
        } else {
            self.shared_storage_id.to_string()
        }
    }

    /// A hash to identify a given [`Unit`] in the build graph
    pub fn unit_id(&self) -> UnitHash {
        self.unit_id
    }

    /// A hash to add to symbol naming through `-C metadata`
    pub fn c_metadata(&self) -> UnitHash {
        self.c_metadata
    }

    /// A hash to add to file names through `-C extra-filename`
    pub fn c_extra_filename(&self) -> Option<UnitHash> {
        self.c_extra_filename.then_some(self.unit_id)
    }

    /// A hash to add to Cargo directory names
    pub fn pkg_dir(&self) -> Option<UnitHash> {
        self.pkg_dir.then_some(self.unit_id)
    }
}

/// Trust (DC-18b): a shared workspace member's store slot.
#[derive(Clone, Debug)]
pub(crate) struct MemberSlot {
    /// `<store>/build/members/<package>/<name>`.
    pub(crate) dir: PathBuf,
    /// The relocated command digest the slot was named by; empty while the
    /// slot is planned.
    pub(crate) command: String,
    /// Trust (DC-18c): the per-checkout inputs the slot was named by (build
    /// script output, proc-macro bytes), where the member has any.
    pub(crate) inputs: Option<std::sync::Arc<crate::compiler::shared_dependencies::MemberInputs>>,
    /// Trust (DC-18c): the slot cannot be named until a build script or a
    /// proc macro it is keyed on (its own or a member dependency's) has run
    /// in this checkout; its directory is this process's, and its job is
    /// refused.
    pub(crate) waiting: bool,
}

/// Collection of information about the files emitted by the compiler, and the
/// output directory structure.
pub struct CompilationFiles<'a, 'gctx, L = Layout> {
    /// The target directory layout for the host (and target if it is the same as host).
    pub(super) host: L,
    /// The target directory layout for the target (if different from then host).
    pub(super) target: HashMap<CompileTarget, L>,
    /// Additional directory to include a copy of the outputs.
    export_dir: Option<PathBuf>,
    /// The root targets requested by the user on the command line (does not
    /// include dependencies).
    roots: Vec<Unit>,
    ws: &'a Workspace<'gctx>,
    /// Metadata hash to use for each unit.
    metas: HashMap<Unit, Metadata>,
    /// For each Unit, a list all files produced.
    outputs: HashMap<Unit, OnceCell<Arc<Vec<OutputFile>>>>,
    shared_root: Option<PathBuf>,
    shared_units: crate::util::data_structures::HashSet<Unit>,
    /// Trust (DC-18b): each shared member unit's store slot. Until
    /// `BuildRunner::plan_member_slots` names it, a planning directory beside
    /// the slots of its package.
    member_slots: HashMap<Unit, MemberSlot>,
    // Trust: native candidate-only per-unit path DATA. Actual directory
    // originals, writer exclusion and publication remain parent obligations.
    private_units: HashMap<Unit, UnitOutputNamespace>,
}

/// Shared native output layout DATA, never a directory or write capability.
/// Stable resolved identity keeps warm artifacts in the SAME namespace while
/// a different unit cannot write its predecessor's metadata or scratch files.
#[derive(Clone)]
pub(crate) struct UnitOutputNamespace {
    unit_sha256: String,
    unit_id: UnitHash,
    root: PathBuf,
    outputs: PathBuf,
    incremental: PathBuf,
}
impl UnitOutputNamespace {
    fn new(build: &Path, unit_id: UnitHash, unit_sha256: String) -> CargoResult<Self> {
        anyhow::ensure!(
            unit_sha256.len() == 64
                && unit_sha256
                    .bytes()
                    .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase()),
            "native unit output has an invalid resolved identity"
        );
        let root = build
            .join(".targo-native")
            .join("units")
            .join(format!("{unit_id}-{unit_sha256}"));
        Ok(Self {
            outputs: root.join("out"),
            incremental: root.join("incremental"),
            root,
            unit_id,
            unit_sha256,
        })
    }
    pub(crate) fn unit_sha256(&self) -> &str {
        &self.unit_sha256
    }
    pub(crate) fn unit_id(&self) -> UnitHash {
        self.unit_id
    }
    pub(crate) fn root(&self) -> &Path {
        &self.root
    }
    pub(crate) fn outputs(&self) -> &Path {
        &self.outputs
    }
    pub(crate) fn incremental(&self) -> &Path {
        &self.incremental
    }
    pub(crate) fn retained_bytes(&self) -> Option<usize> {
        self.unit_sha256
            .capacity()
            .checked_add(self.root.capacity())?
            .checked_add(self.outputs.capacity())?
            .checked_add(self.incremental.capacity())
    }
}

/// Info about a single file emitted by the compiler.
#[derive(Debug)]
pub struct OutputFile {
    /// Absolute path to the file that will be produced by the build process.
    pub path: PathBuf,
    /// If it should be linked into `target`, and what it should be called
    /// (e.g., without metadata).
    pub hardlink: Option<PathBuf>,
    /// If `--artifact-dir` is specified, the absolute path to the exported file.
    pub export_path: Option<PathBuf>,
    /// Type of the file (library / debug symbol / else).
    pub flavor: FileFlavor,
}

/// Expected output DATA from one actual resolved unit. This is neither a
/// materialization receipt nor an output-directory/read/write owner.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) struct CandidateOutput {
    pub unit_sha256: String,
    pub is_root: bool,
    pub metadata: Metadata,
    pub outputs: Arc<Vec<OutputFile>>,
    pub private: UnitOutputNamespace,
}

pub(super) fn artifact_dir_required(bcx: &BuildContext<'_, '_>) -> bool {
    artifact_dir_required_for(bcx.build_config)
}
pub(super) fn artifact_dir_required_for(config: &crate::compiler::BuildConfig) -> bool {
    use crate::compiler::UserIntent;
    match config.intent {
        UserIntent::Check { .. } => config.timing_report,
        UserIntent::Build
        | UserIntent::Test
        | UserIntent::Doc { .. }
        | UserIntent::Doctest
        | UserIntent::Bench => true,
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(in crate::compiler) fn projected_outputs<'a, 'gctx>(
    bcx: &'a BuildContext<'a, 'gctx>,
    graph: &crate::compiler::exact_unit::Graph,
    files: &CompilationFiles<'a, 'gctx, LayoutPaths>,
) -> CargoResult<Vec<CandidateOutput>> {
    // These are additional finite projection limits, not new ordinary build
    // restrictions. Check variable-size filename/path inputs before joining
    // or cloning them in the shared ordinary output calculation.
    const MAX_PATH: usize = 4096;
    const MAX_OUTPUTS: usize = 16384;
    const MAX_BYTES: usize = 16 * 1024 * 1024;
    for path in [bcx.ws.target_dir(), bcx.ws.build_dir()] {
        anyhow::ensure!(
            path.as_path_unlocked().as_os_str().as_bytes().len() <= MAX_PATH,
            "candidate output root exceeds finite path bound"
        );
    }
    anyhow::ensure!(
        bcx.profiles.get_dir_name().len() <= MAX_PATH,
        "candidate output profile exceeds finite path bound"
    );
    if let Some(root) = &bcx.shared_dependency_root {
        anyhow::ensure!(
            root.as_os_str().as_bytes().len() <= MAX_PATH,
            "candidate shared output root exceeds finite path bound"
        );
    }
    for unit in bcx.unit_graph.keys() {
        anyhow::ensure!(
            unit.target.name().len() <= MAX_PATH
                && unit.pkg.name().len() <= MAX_PATH
                && unit.target.crate_name().len() <= MAX_PATH,
            "candidate output filename input exceeds finite path bound"
        );
        if let TargetKind::Lib(types) | TargetKind::ExampleLib(types) = unit.target.kind() {
            anyhow::ensure!(
                types.len() <= 32,
                "candidate output crate type population exceeds finite bound"
            );
        }
    }
    let mut projected = Vec::with_capacity(bcx.unit_graph.len());
    let mut count = 0usize;
    let mut bytes = 0usize;
    for unit in bcx.unit_graph.keys() {
        anyhow::ensure!(
            files.metas.contains_key(unit),
            "candidate output graph contains an unreachable unit"
        );
        let outputs = files.outputs(unit, bcx)?;
        count = count
            .checked_add(outputs.len())
            .ok_or_else(|| anyhow::anyhow!("candidate output count overflow"))?;
        anyhow::ensure!(
            count <= MAX_OUTPUTS,
            "candidate output population exceeds finite bound"
        );
        for output in outputs.iter() {
            for path in std::iter::once(&output.path)
                .chain(output.hardlink.iter())
                .chain(output.export_path.iter())
            {
                bytes = bytes
                    .checked_add(path.as_os_str().as_bytes().len())
                    .ok_or_else(|| anyhow::anyhow!("candidate output byte count overflow"))?;
                anyhow::ensure!(
                    bytes <= MAX_BYTES,
                    "candidate output paths exceed finite byte bound"
                );
            }
        }
        projected.push(CandidateOutput {
            unit_sha256: graph.capture(unit)?.digest.clone(),
            is_root: bcx.roots.contains(unit),
            metadata: files.metadata(unit),
            outputs,
            private: files
                .private_unit(unit)
                .ok_or_else(|| anyhow::anyhow!("candidate output omitted private unit namespace"))?
                .clone(),
        });
    }
    // Preserve every row, including equal digest rows. A set could conceal
    // graph multiplicity; these hashes are only equality and filename data.
    projected.sort_by(|left, right| {
        (
            &left.unit_sha256,
            left.is_root,
            left.metadata.unit_id(),
            left.metadata.c_metadata(),
        )
            .cmp(&(
                &right.unit_sha256,
                right.is_root,
                right.metadata.unit_id(),
                right.metadata.c_metadata(),
            ))
    });
    Ok(projected)
}

impl OutputFile {
    /// Gets the hard link if present; otherwise, returns the path.
    pub fn bin_dst(&self) -> &PathBuf {
        match self.hardlink {
            Some(ref link_dst) => link_dst,
            None => &self.path,
        }
    }
}

impl<'a, 'gctx: 'a> CompilationFiles<'a, 'gctx> {
    pub(super) fn take_compile_leases(&mut self) -> CargoResult<Vec<crate::util::FileLock>> {
        let mut leases = self.host.take_compile_leases()?;
        for layout in self.target.values_mut() {
            leases.extend(layout.take_compile_leases()?);
        }
        Ok(leases)
    }
    /// Keep layout paths available for execution after compilation releases
    /// its directory leases. The coordinator has already joined its workers.
    pub(super) fn release_compile_leases(&mut self) {
        self.host.release_compile_leases();
        for layout in self.target.values_mut() {
            layout.release_compile_leases();
        }
    }
    /// Trust: DC-12b. The profiles' `incremental/` folders no other build
    /// can be using now: those of the layouts whose build directory lock
    /// this build took exclusively and still holds
    /// (`Layout::excludes_other_builds`).
    pub(super) fn exclusive_incremental_dirs(&self) -> Vec<PathBuf> {
        std::iter::once(&self.host)
            .chain(self.target.values())
            .filter(|layout| layout.excludes_other_builds())
            .map(|layout| layout.build_dir().incremental().to_path_buf())
            .collect()
    }

    pub(super) fn new(
        build_runner: &BuildRunner<'a, 'gctx>,
        host: Layout,
        target: HashMap<CompileTarget, Layout>,
    ) -> CargoResult<CompilationFiles<'a, 'gctx>> {
        let mut files = Self::from_parts(
            build_runner.bcx,
            &build_runner.lto,
            &build_runner.primary_packages,
            host,
            target,
        )?;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(original) =
            crate::resource_v3::current().and_then(|startup| startup.candidate.clone())
        {
            original.check()?;
            files.select_private_units(build_runner.bcx, |unit| {
                Ok(crate::compiler::exact_unit::capture(build_runner, unit)?
                    .digest
                    .clone())
            })?;
            original.check()?;
        }
        Ok(files)
    }
}

impl<'a, 'gctx: 'a> CompilationFiles<'a, 'gctx, LayoutPaths> {
    /// Pure output planning from the already resolved graph. No directory is
    /// opened or locked and no runner/resource owner is constructed.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(in crate::compiler) fn projected(
        bcx: &'a BuildContext<'a, 'gctx>,
        lto: &HashMap<Unit, Lto>,
        graph: &crate::compiler::exact_unit::Graph,
    ) -> CargoResult<Self> {
        let dest = bcx.profiles.get_dir_name();
        let artifact_dir = artifact_dir_required(bcx);
        let host = LayoutPaths::new(bcx.ws, None, &dest, artifact_dir);
        let mut target = HashMap::default();
        for kind in &bcx.all_kinds {
            if let CompileKind::Target(selected) = *kind {
                target.insert(
                    selected,
                    LayoutPaths::new(bcx.ws, Some(selected), &dest, artifact_dir),
                );
            }
        }
        let primary_packages = bcx.roots.iter().map(|unit| unit.pkg.package_id()).collect();
        let mut files = Self::from_parts(bcx, lto, &primary_packages, host, target)?;
        files.select_private_units(bcx, |unit| Ok(graph.capture(unit)?.digest.clone()))?;
        Ok(files)
    }
}

impl<'a, 'gctx: 'a, L: Borrow<LayoutPaths>> CompilationFiles<'a, 'gctx, L> {
    fn from_parts(
        bcx: &'a BuildContext<'a, 'gctx>,
        lto: &HashMap<Unit, Lto>,
        primary_packages: &HashSet<PackageId>,
        host: L,
        target: HashMap<CompileTarget, L>,
    ) -> CargoResult<Self> {
        let mut metas = HashMap::default();
        for unit in &bcx.roots {
            metadata_of(unit, bcx, lto, primary_packages, &mut metas)?;
        }
        let outputs = metas
            .keys()
            .cloned()
            .map(|unit| (unit, OnceCell::new()))
            .collect();
        let mut files = CompilationFiles {
            ws: bcx.ws,
            host,
            target,
            export_dir: bcx.build_config.export_dir.clone(),
            roots: bcx.roots.clone(),
            metas,
            outputs,
            shared_root: bcx.shared_dependency_root.clone(),
            shared_units: bcx.shared_dependency_units.clone(),
            member_slots: HashMap::default(),
            private_units: HashMap::default(),
        };
        if let Some(store) = &files.shared_root {
            let process = std::process::id();
            for unit in &bcx.shared_member_units {
                let dir = store
                    .join("build")
                    .join("members")
                    .join(unit.pkg.package_id().name().as_str())
                    .join(format!(
                        ".plan-{process}-{}",
                        crate::compiler::shared_dependencies::member_key(unit)
                    ));
                files.member_slots.insert(
                    unit.clone(),
                    MemberSlot {
                        dir,
                        command: String::new(),
                        inputs: None,
                        waiting: false,
                    },
                );
            }
        }
        Ok(files)
    }

    /// Trust (DC-18b): a shared member's slot name: a digest of what it is
    /// built from: its unit hash (package, target, features, profile, mode),
    /// its sources digested without the checkout's path, the platform its
    /// compiler sees, the compiler's content, its relocated `command` (which
    /// holds its environment and every argument, the checkout's and the
    /// slot's own paths read as tokens), and each dependency's slot, a
    /// member's by this same name. Two checkouts at one commit name one slot;
    /// a build that changes a member, anything it depends on, or how it is
    /// compiled names another, and never writes over the first. Every member
    /// dependency's slot is already named. Trust (DC-18c): and the `inputs`
    /// digest of what it is keyed on in this checkout, where it has any (its
    /// build scripts' output, the proc macros it loads), so a member whose
    /// script printed other directives, or whose macro is other bytes, names
    /// another slot.
    pub(super) fn member_slot_name(
        &self,
        unit: &Unit,
        bcx: &BuildContext<'a, 'gctx>,
        identity: (&str, &str),
        command: &str,
        inputs: Option<&str>,
    ) -> CargoResult<String> {
        let source = bcx
            .shared_eligibility
            .source(unit)
            .ok_or_else(|| anyhow::anyhow!("shared member has no source capture"))?;
        let mut dependencies = Vec::new();
        for dep in &bcx.unit_graph[unit] {
            let name = dep.extern_crate_name.to_string();
            if bcx.shared_member(&dep.unit) {
                let slot = self
                    .member_slots
                    .get(&dep.unit)
                    .filter(|slot| !slot.command.is_empty())
                    .and_then(|slot| slot.dir.file_name()?.to_str())
                    .ok_or_else(|| anyhow::anyhow!("a member dependency's slot is not named"))?;
                dependencies.push(format!("{name}:member:{slot}"));
            } else {
                let git = crate::compiler::shared_dependencies::git_source_identity(
                    dep.unit.pkg.package_id().source_id(),
                )
                .unwrap_or_default();
                dependencies.push(format!(
                    "{name}:unit:{}:{git}",
                    self.shared_storage_hash(&dep.unit)
                ));
            }
        }
        dependencies.sort();
        let (platform, compiler) = identity;
        let unit_hash = self.unit_hash(unit);
        let mut hash = cargo_util::Sha256::new();
        // A member keyed on nothing per checkout keeps its v2 name.
        let keyed = inputs.map(|inputs| ["targo-member-inputs", inputs]);
        for field in [
            "targo-member-slot-v2",
            unit_hash.as_str(),
            source.digest(),
            platform,
            compiler,
            command,
        ]
        .into_iter()
        .chain(keyed.into_iter().flatten())
        .chain(dependencies.iter().map(String::as_str))
        {
            hash.update(&(field.len() as u64).to_le_bytes());
            hash.update(field.as_bytes());
        }
        Ok(hash.finish_hex()[..32].to_string())
    }

    /// Trust (DC-18b): a shared member's slot, planned or named.
    pub(crate) fn member_slot(&self, unit: &Unit) -> Option<&MemberSlot> {
        self.member_slots.get(unit)
    }

    /// Trust (DC-18b): names a shared member's slot, and forgets the outputs
    /// computed while it was planned.
    pub(super) fn name_member_slot(&mut self, unit: &Unit, slot: MemberSlot) {
        self.member_slots.insert(unit.clone(), slot);
        if let Some(outputs) = self.outputs.get_mut(unit) {
            *outputs = OnceCell::new();
        }
    }

    // Select only before any cached output inventory is calculated. Parent
    // projection and actual candidate use their SAME already captured graph.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn select_private_units(
        &mut self,
        bcx: &BuildContext<'a, 'gctx>,
        mut identity: impl FnMut(&Unit) -> CargoResult<String>,
    ) -> CargoResult<()> {
        anyhow::ensure!(
            self.private_units.is_empty()
                && self.outputs.values().all(|outputs| outputs.get().is_none()),
            "native private output selection followed cached output calculation"
        );
        let mut occupied = HashSet::default();
        for unit in bcx.unit_graph.keys() {
            anyhow::ensure!(
                matches!(
                    unit.mode,
                    CompileMode::Build | CompileMode::Check { test: false }
                ) && unit.kind == CompileKind::Host
                    && !unit.target.is_custom_build()
                    && !unit.target.proc_macro()
                    && !unit.artifact.is_true()
                    && !unit.is_std,
                "private native output namespace exceeds the selected unit profile"
            );
            let metadata = self.metas.get(unit).ok_or_else(|| {
                anyhow::anyhow!("native output graph contains an unreachable unit")
            })?;
            let namespace = UnitOutputNamespace::new(
                self.layout(unit.kind).build_dir().root(),
                metadata.unit_id(),
                identity(unit)?,
            )?;
            anyhow::ensure!(
                occupied.insert(namespace.root.clone()),
                "distinct native units share a private writable namespace"
            );
            self.private_units.insert(unit.clone(), namespace);
        }
        Ok(())
    }
    pub(crate) fn private_unit(&self, unit: &Unit) -> Option<&UnitOutputNamespace> {
        self.private_units.get(unit)
    }

    /// Returns the appropriate directory layout for either a plugin or not.
    pub fn layout(&self, kind: CompileKind) -> &LayoutPaths {
        match kind {
            CompileKind::Host => self.host.borrow(),
            CompileKind::Target(target) => self.target[&target].borrow(),
        }
    }

    /// Gets the metadata for the given unit.
    ///
    /// See [`Metadata`] and [`fingerprint`] module for more.
    ///
    /// [`fingerprint`]: super::super::fingerprint#fingerprints-and-metadata
    pub fn metadata(&self, unit: &Unit) -> Metadata {
        self.metas[unit]
    }

    /// Gets the short hash based only on the `PackageId`.
    /// Used for the metadata when `c_extra_filename` returns `None`.
    fn target_short_hash(&self, unit: &Unit) -> String {
        let hashable = unit.pkg.package_id().stable_hash(self.ws.root());
        util::short_hash(&(METADATA_VERSION, hashable))
    }

    /// Returns the directory where the artifacts for the given unit are
    /// initially created.
    pub fn output_dir(&self, unit: &Unit) -> PathBuf {
        if let Some(private) = self.private_unit(unit) {
            return private.outputs.clone();
        }
        // Docscrape units need to have doc/ set as the out_dir so sources for reverse-dependencies
        // will be put into doc/ and not into deps/ where the *.examples files are stored.
        if unit.mode.is_doc() || unit.mode.is_doc_scrape() {
            self.layout(unit.kind)
                .artifact_dir()
                .expect("artifact-dir was not locked")
                .doc()
                .to_path_buf()
        } else if unit.mode.is_doc_test() {
            panic!("doc tests do not have an out dir");
        } else if unit.target.is_custom_build() {
            self.build_script_dir(unit)
        } else if unit.target.is_example() && !self.ws.gctx().cli_unstable().build_dir_new_layout {
            self.layout(unit.kind).build_dir().examples().to_path_buf()
        } else if unit.artifact.is_true() {
            self.artifact_dir(unit)
        } else {
            self.deps_dir(unit).to_path_buf()
        }
    }

    fn shared_unit_dir(&self, unit: &Unit) -> Option<PathBuf> {
        self.shared_units.contains(unit).then(|| {
            let root = self
                .shared_root
                .as_ref()
                .expect("shared units have a store")
                .join("build");
            if let Some(slot) = self.member_slots.get(unit) {
                return slot.dir.clone();
            }
            let source = unit.pkg.package_id().source_id();
            let root = if source.is_git() {
                let revision = crate::compiler::shared_dependencies::resolved_git_commit(source)
                    .expect("shared Git units have a full resolved commit");
                root.join("git").join(revision)
            } else {
                root
            };
            // Trust: complete omitted flags distinguish storage without entering
            // symbol metadata or artifact basenames. Dependency variants propagate.
            root.join(self.pkg_dir_with_hash(unit, self.shared_storage_hash(unit)))
        })
    }

    pub fn build_root(&self, unit: &Unit) -> PathBuf {
        if self.shared_units.contains(unit) {
            self.shared_root.clone().expect("shared units have a store")
        } else {
            self.ws.build_dir().into_path_unlocked()
        }
    }

    /// Additional export directory from `--artifact-dir`.
    pub fn export_dir(&self) -> Option<PathBuf> {
        self.export_dir.clone()
    }

    /// Directory name to use for a package in the form `{NAME}/{HASH}`.
    ///
    /// Note that some units may share the same directory, so care should be
    /// taken in those cases!
    fn pkg_dir(&self, unit: &Unit) -> String {
        self.pkg_dir_with_hash(unit, self.unit_hash(unit))
    }

    // Trust: ordinary and shared variants use the same existing layout rules.
    fn pkg_dir_with_hash(&self, unit: &Unit, hash: String) -> String {
        let name = unit.pkg.package_id().name();
        package_directory(
            name.as_str(),
            &hash,
            self.ws.gctx().cli_unstable().build_dir_new_layout,
        )
    }

    fn shared_storage_hash(&self, unit: &Unit) -> String {
        self.metas[unit].shared_storage_hash(self.unit_hash(unit))
    }

    /// The directory hash to use for a given unit
    pub fn unit_hash(&self, unit: &Unit) -> String {
        self.metas[unit]
            .pkg_dir()
            .map(|h| h.to_string())
            .unwrap_or_else(|| self.target_short_hash(unit))
    }

    /// Returns the final artifact path for the host (`/…/target/debug`)
    pub fn host_dest(&self) -> Option<&Path> {
        self.layout(CompileKind::Host)
            .artifact_dir()
            .map(|v| v.dest())
    }

    /// Returns the root of the build output tree for the host (`/…/build-dir`)
    pub fn host_build_root(&self) -> &Path {
        self.layout(CompileKind::Host).build_dir().root()
    }

    /// Returns the host `deps` directory path for a given build unit.
    pub fn host_deps(&self, unit: &Unit) -> PathBuf {
        if let Some(private) = self.private_unit(unit) {
            return private.outputs.clone();
        }
        if let Some(shared) = self.shared_unit_dir(unit) {
            return shared.join("out");
        }
        let dir = self.pkg_dir(unit);
        self.layout(CompileKind::Host).build_dir().deps(&dir)
    }

    /// Returns the directories where Rust crate dependencies are found for the
    /// specified unit.
    pub fn deps_dir(&self, unit: &Unit) -> PathBuf {
        if let Some(private) = self.private_unit(unit) {
            return private.outputs.clone();
        }
        if let Some(shared) = self.shared_unit_dir(unit) {
            return shared.join("out");
        }
        let dir = self.pkg_dir(unit);
        self.layout(unit.kind).build_dir().deps(&dir)
    }

    /// Returns the directories where Rust crate dependencies are found for the
    /// specified unit. (new layout)
    ///
    /// New features should consider using this so we can avoid their migrations.
    pub fn out_dir_new_layout(&self, unit: &Unit) -> PathBuf {
        if let Some(shared) = self.shared_unit_dir(unit) {
            return shared.join("out");
        }
        let dir = self.pkg_dir(unit);
        self.layout(unit.kind)
            .build_dir()
            .out_force_new_layout(&dir)
    }

    /// Directory where the fingerprint for the given unit should go.
    pub fn fingerprint_dir(&self, unit: &Unit) -> PathBuf {
        if let Some(shared) = self.shared_unit_dir(unit) {
            return shared.join("fingerprint");
        }
        let dir = self.pkg_dir(unit);
        self.layout(unit.kind).build_dir().fingerprint(&dir)
    }

    /// The lock location for a given build unit.
    pub fn build_unit_lock(&self, unit: &Unit) -> PathBuf {
        if let Some(shared) = self.shared_unit_dir(unit) {
            return shared.join(".lock");
        }
        let dir = self.pkg_dir(unit);
        self.layout(unit.kind)
            .build_dir()
            .build_unit(&dir)
            .join(".lock")
    }

    /// Directory where incremental output for the given unit should go.
    pub fn incremental_dir(&self, unit: &Unit) -> &Path {
        if let Some(private) = self.private_unit(unit) {
            return private.incremental();
        }
        self.layout(unit.kind).build_dir().incremental()
    }

    /// Directory where timing output should go.
    pub fn timings_dir(&self) -> Option<&Path> {
        self.layout(CompileKind::Host)
            .artifact_dir()
            .map(|v| v.timings())
    }

    /// Returns the path for a file in the fingerprint directory.
    ///
    /// The "prefix" should be something to distinguish the file from other
    /// files in the fingerprint directory.
    pub fn fingerprint_file_path(&self, unit: &Unit, prefix: &str) -> PathBuf {
        // Different targets need to be distinguished in the
        let kind = unit.target.kind().description();
        let flavor = if unit.mode.is_any_test() {
            "test-"
        } else if unit.mode.is_doc() {
            "doc-"
        } else if unit.mode.is_run_custom_build() {
            "run-"
        } else {
            ""
        };
        let name = format!("{}{}{}-{}", prefix, flavor, kind, unit.target.name());
        self.fingerprint_dir(unit).join(name)
    }

    /// Path where compiler output is cached.
    pub fn message_cache_path(&self, unit: &Unit) -> PathBuf {
        self.fingerprint_file_path(unit, "output-")
    }

    /// Returns the directory where a compiled build script is stored.
    /// `/path/to/target/{debug,release}/build/PKG-HASH`
    pub fn build_script_dir(&self, unit: &Unit) -> PathBuf {
        assert!(unit.target.is_custom_build());
        assert!(!unit.mode.is_run_custom_build());
        assert!(self.metas.contains_key(unit));
        let dir = self.pkg_dir(unit);
        self.layout(CompileKind::Host)
            .build_dir()
            .build_script(&dir)
    }

    /// Returns the directory for compiled artifacts files.
    /// `/path/to/target/{debug,release}/deps/artifact/KIND/PKG-HASH`
    fn artifact_dir(&self, unit: &Unit) -> PathBuf {
        assert!(self.metas.contains_key(unit));
        assert!(unit.artifact.is_true());
        let dir = self.pkg_dir(unit);
        let kind = match unit.target.kind() {
            TargetKind::Bin => "bin",
            TargetKind::Lib(lib_kinds) => match lib_kinds.as_slice() {
                &[CrateType::Cdylib] => "cdylib",
                &[CrateType::Staticlib] => "staticlib",
                invalid => unreachable!(
                    "BUG: unexpected artifact library type(s): {:?} - these should have been split",
                    invalid
                ),
            },
            invalid => unreachable!(
                "BUG: {:?} are not supposed to be used as artifacts",
                invalid
            ),
        };
        self.layout(unit.kind).build_dir().artifact(&dir, kind)
    }

    /// Returns the directory where information about running a build script
    /// is stored.
    /// `/path/to/target/{debug,release}/build/PKG-HASH`
    pub fn build_script_run_dir(&self, unit: &Unit) -> PathBuf {
        assert!(unit.target.is_custom_build());
        assert!(unit.mode.is_run_custom_build());
        let dir = self.pkg_dir(unit);
        self.layout(unit.kind)
            .build_dir()
            .build_script_execution(&dir)
    }

    /// Returns the "`OUT_DIR`" directory for running a build script in the
    /// old build-directory layout:
    /// `/path/to/target/{debug,release}/build/PKG-HASH/out`. Trust:
    /// `custom_build::script_out_dir` names a run's `OUT_DIR` in either layout.
    pub fn build_script_out_dir(&self, unit: &Unit) -> PathBuf {
        self.build_script_run_dir(unit).join("out")
    }

    /// Returns the path to the executable binary for the given bin target.
    ///
    /// This should only to be used when a `Unit` is not available.
    pub fn bin_link_for_target(
        &self,
        target: &Target,
        kind: CompileKind,
        bcx: &BuildContext<'_, '_>,
    ) -> CargoResult<Option<PathBuf>> {
        assert!(target.is_bin());
        let Some(dest) = self.layout(kind).artifact_dir().map(|v| v.dest()) else {
            return Ok(None);
        };
        let info = bcx.target_data.info(kind);
        let (file_types, _) = info
            .rustc_outputs(
                CompileMode::Build,
                &TargetKind::Bin,
                bcx.target_data.short_name(&kind),
            )
            .expect("target must support `bin`");

        let file_type = file_types
            .iter()
            .find(|file_type| file_type.flavor == FileFlavor::Normal)
            .expect("target must support `bin`");

        Ok(Some(dest.join(file_type.uplift_filename(target))))
    }

    /// Returns the filenames that the given unit will generate.
    ///
    /// Note: It is not guaranteed that all of the files will be generated.
    pub(in crate::compiler) fn outputs(
        &self,
        unit: &Unit,
        bcx: &BuildContext<'a, 'gctx>,
    ) -> CargoResult<Arc<Vec<OutputFile>>> {
        self.outputs[unit]
            .try_borrow_with(|| self.calc_outputs(unit, bcx))
            .map(Arc::clone)
    }

    /// Returns the path where the output for the given unit and `FileType`
    /// should be uplifted to.
    ///
    /// Returns `None` if the unit shouldn't be uplifted (for example, a
    /// dependent rlib).
    fn uplift_to(
        &self,
        unit: &Unit,
        file_type: &FileType,
        from_path: &Path,
        bcx: &BuildContext<'_, '_>,
    ) -> Option<PathBuf> {
        // Tests, check, doc, etc. should not be uplifted.
        if unit.mode != CompileMode::Build || file_type.flavor == FileFlavor::Rmeta {
            return None;
        }

        // Artifact dependencies are never uplifted.
        if unit.artifact.is_true() {
            return None;
        }

        // Build script bins are never uplifted.
        if bcx.gctx.cli_unstable().build_dir_new_layout && unit.target.is_custom_build() {
            return None;
        }

        // - Binaries: The user always wants to see these, even if they are
        //   implicitly built (for example for integration tests).
        // - dylibs: This ensures that the dynamic linker pulls in all the
        //   latest copies (even if the dylib was built from a previous cargo
        //   build). There are complex reasons for this, see #8139, #6167, #6162.
        // - Things directly requested from the command-line (the "roots").
        //   This one is a little questionable for rlibs (see #6131), but is
        //   historically how Cargo has operated. This is primarily useful to
        //   give the user access to staticlibs and cdylibs.
        if !unit.target.is_bin()
            && !unit.target.is_custom_build()
            && file_type.crate_type != Some(CrateType::Dylib)
            && !self.roots.contains(unit)
        {
            return None;
        }

        let filename = file_type.uplift_filename(&unit.target);
        let uplift_path = if unit.target.is_example() {
            // Examples live in their own little world.
            self.layout(unit.kind)
                .artifact_dir()?
                .examples()
                .join(filename)
        } else if unit.target.is_custom_build() {
            self.build_script_dir(unit).join(filename)
        } else {
            self.layout(unit.kind).artifact_dir()?.dest().join(filename)
        };
        if from_path == uplift_path {
            // This can happen with things like examples that reside in the
            // same directory, do not have a metadata hash (like on Windows),
            // and do not have hyphens.
            return None;
        }
        Some(uplift_path)
    }

    /// Calculates the filenames that the given unit will generate.
    /// Should use [`CompilationFiles::outputs`] instead
    /// as it caches the result of this function.
    fn calc_outputs(
        &self,
        unit: &Unit,
        bcx: &BuildContext<'a, 'gctx>,
    ) -> CargoResult<Arc<Vec<OutputFile>>> {
        let ret = match unit.mode {
            _ if unit.skip_non_compile_time_dep => {
                // This skips compilations so no outputs
                vec![]
            }
            CompileMode::Doc => {
                let wants_json_doc = bcx.build_config.intent.wants_doc_json_output();

                let path = if wants_json_doc {
                    // Always use 'new' layout for '--output-format=json'.
                    let crate_name = unit.target.crate_name();
                    self.out_dir_new_layout(unit)
                        .join(format!("{crate_name}.json"))
                } else {
                    self.output_dir(unit)
                        .join(unit.target.crate_name())
                        .join("index.html")
                };

                // Uplift if output is json, from 'new' layout location for backward compatibility
                // See #16773.
                let hardlink = if wants_json_doc {
                    Some(
                        self.output_dir(unit)
                            .join(format!("{}.json", unit.target.crate_name())),
                    )
                } else {
                    None
                };

                let mut outputs = vec![OutputFile {
                    path,
                    hardlink,
                    export_path: None,
                    flavor: FileFlavor::Normal,
                }];

                if bcx.gctx.cli_unstable().rustdoc_mergeable_info && !wants_json_doc {
                    // `-Zrustdoc-mergeable-info` always uses the new layout.
                    outputs.push(OutputFile {
                        path: self
                            .out_dir_new_layout(unit)
                            .join(unit.target.crate_name())
                            .with_extension("json"),
                        hardlink: None,
                        export_path: None,
                        flavor: FileFlavor::DocParts,
                    })
                }

                outputs
            }
            CompileMode::RunCustomBuild => {
                // At this time, this code path does not handle build script
                // outputs.
                vec![]
            }
            CompileMode::Doctest => {
                // Doctests are built in a temporary directory and then
                // deleted. There is the `--persist-doctests` unstable flag,
                // but Cargo does not know about that.
                vec![]
            }
            CompileMode::Docscrape => {
                // The file name needs to be stable across Cargo sessions.
                // This originally used unit.buildkey(), but that isn't stable,
                // so we use metadata instead (prefixed with name for debugging).
                let file_name = format!(
                    "{}-{}.examples",
                    unit.pkg.name(),
                    self.metadata(unit).unit_id()
                );
                let path = self.deps_dir(unit).join(file_name);
                vec![OutputFile {
                    path,
                    hardlink: None,
                    export_path: None,
                    flavor: FileFlavor::Normal,
                }]
            }
            CompileMode::Test | CompileMode::Build | CompileMode::Check { .. } => {
                let mut outputs = self.calc_outputs_rustc(unit, bcx)?;
                if bcx.build_config.sbom && bcx.gctx.cli_unstable().sbom {
                    let sbom_files: Vec<_> = outputs
                        .iter()
                        .filter(|o| matches!(o.flavor, FileFlavor::Normal | FileFlavor::Linkable))
                        .map(|output| OutputFile {
                            path: Self::append_sbom_suffix(&output.path),
                            hardlink: output.hardlink.as_ref().map(Self::append_sbom_suffix),
                            export_path: output.export_path.as_ref().map(Self::append_sbom_suffix),
                            flavor: FileFlavor::Sbom,
                        })
                        .collect();
                    outputs.extend(sbom_files.into_iter());
                }

                // Only generates unremap files for root units.
                if bcx.roots.contains(unit) && trim_paths::should_emit_unremap_file(unit) {
                    let unremap_files: Vec<_> = outputs
                        .iter()
                        .filter(|o| matches!(o.flavor, FileFlavor::Normal | FileFlavor::Linkable))
                        .map(|output| OutputFile {
                            path: trim_paths::append_unremap_suffix(&output.path),
                            hardlink: output
                                .hardlink
                                .as_ref()
                                .map(trim_paths::append_unremap_suffix),
                            export_path: output
                                .export_path
                                .as_ref()
                                .map(trim_paths::append_unremap_suffix),
                            flavor: FileFlavor::Unremap,
                        })
                        .collect();
                    outputs.extend(unremap_files.into_iter());
                }
                outputs
            }
        };
        debug!("Target filenames: {:?}", ret);

        Ok(Arc::new(ret))
    }

    /// Append the SBOM suffix to the file name.
    fn append_sbom_suffix(link: &PathBuf) -> PathBuf {
        const SBOM_FILE_EXTENSION: &str = ".cargo-sbom.json";
        let mut link_buf = link.clone().into_os_string();
        link_buf.push(SBOM_FILE_EXTENSION);
        PathBuf::from(link_buf)
    }

    /// Computes the actual, full pathnames for all the files generated by rustc.
    ///
    /// The `OutputFile` also contains the paths where those files should be
    /// "uplifted" to.
    fn calc_outputs_rustc(
        &self,
        unit: &Unit,
        bcx: &BuildContext<'a, 'gctx>,
    ) -> CargoResult<Vec<OutputFile>> {
        let out_dir = self.output_dir(unit);

        let info = bcx.target_data.info(unit.kind);
        let triple = bcx.target_data.short_name(&unit.kind);
        let (file_types, unsupported) =
            info.rustc_outputs(unit.mode, unit.target.kind(), triple)?;
        if file_types.is_empty() {
            if !unsupported.is_empty() {
                let unsupported_strs: Vec<_> = unsupported.iter().map(|ct| ct.as_str()).collect();
                anyhow::bail!(
                    "cannot produce {} for `{}` as the target `{}` \
                     does not support these crate types",
                    unsupported_strs.join(", "),
                    unit.pkg,
                    triple,
                )
            }
            anyhow::bail!(
                "cannot compile `{}` as the target `{}` does not \
                 support any of the output crate types",
                unit.pkg,
                triple,
            );
        }

        // Convert FileType to OutputFile.
        let mut outputs = Vec::new();
        for file_type in file_types {
            let meta = self.metas[unit];
            let meta_opt = meta.c_extra_filename().map(|h| h.to_string());
            let path = out_dir.join(file_type.output_filename(&unit.target, meta_opt.as_deref()));

            // If, the `different_binary_name` feature is enabled, the name of the hardlink will
            // be the name of the binary provided by the user in `Cargo.toml`.
            let hardlink = self.uplift_to(unit, &file_type, &path, bcx);
            let export_path = if unit.target.is_custom_build() {
                None
            } else {
                self.export_dir.as_ref().and_then(|export_dir| {
                    hardlink
                        .as_ref()
                        .map(|hardlink| export_dir.join(hardlink.file_name().unwrap()))
                })
            };
            outputs.push(OutputFile {
                path,
                hardlink,
                export_path,
                flavor: file_type.flavor,
            });
        }
        Ok(outputs)
    }
}

/// Gets the metadata hash for the given [`Unit`].
///
/// When a metadata hash doesn't exist for the given unit,
/// this calls itself recursively to compute metadata hashes of all its dependencies.
/// See [`compute_metadata`] for how a single metadata hash is computed.
fn metadata_of<'a>(
    unit: &Unit,
    bcx: &BuildContext<'_, '_>,
    lto: &HashMap<Unit, Lto>,
    primary_packages: &HashSet<PackageId>,
    metas: &'a mut HashMap<Unit, Metadata>,
) -> CargoResult<&'a Metadata> {
    if !metas.contains_key(unit) {
        let meta = compute_metadata(unit, bcx, lto, primary_packages, metas)?;
        metas.insert(unit.clone(), meta);
        for dep in &bcx.unit_graph[unit] {
            metadata_of(&dep.unit, bcx, lto, primary_packages, metas)?;
        }
    }
    Ok(&metas[unit])
}

/// Computes the metadata hash for the given [`Unit`].
fn compute_metadata(
    unit: &Unit,
    bcx: &BuildContext<'_, '_>,
    lto: &HashMap<Unit, Lto>,
    primary_packages: &HashSet<PackageId>,
    metas: &mut HashMap<Unit, Metadata>,
) -> CargoResult<Metadata> {
    let deps_metadata = bcx.unit_graph[unit]
        .iter()
        .map(|dep| metadata_of(&dep.unit, bcx, lto, primary_packages, metas).copied())
        .collect::<CargoResult<Vec<_>>>()?;
    let c_extra_filename = use_extra_filename(bcx, unit);
    let pkg_dir = use_pkg_dir(bcx, unit);

    let mut shared_hasher = StableHasher::new();

    METADATA_VERSION.hash(&mut shared_hasher);

    let ws_root = if unit.is_std {
        // SourceId for stdlib crates is an absolute path inside the sysroot.
        // Pass the sysroot as workspace root so that we hash a relative path.
        // This avoids the metadata hash changing depending on where the user installed rustc.
        &bcx.target_data.get_info(unit.kind).unwrap().sysroot
    } else {
        bcx.ws.root()
    };

    // Unique metadata per (name, source, version) triple. This'll allow us
    // to pull crates from anywhere without worrying about conflicts.
    unit.pkg
        .package_id()
        .stable_hash(ws_root)
        .hash(&mut shared_hasher);

    // Also mix in enabled features to our metadata. This'll ensure that
    // when changing feature sets each lib is separately cached.
    unit.features.hash(&mut shared_hasher);

    // Throw in the profile we're compiling with. This helps caching
    // `panic=abort` and `panic=unwind` artifacts, additionally with various
    // settings like debuginfo and whatnot.
    unit.profile.hash(&mut shared_hasher);
    unit.mode.hash(&mut shared_hasher);
    lto[unit].hash(&mut shared_hasher);

    // Artifacts compiled for the host should have a different
    // metadata piece than those compiled for the target, so make sure
    // we throw in the unit's `kind` as well.  Use `fingerprint_hash`
    // so that the StableHash doesn't change based on the pathnames
    // of the custom target JSON spec files.
    unit.kind.fingerprint_hash().hash(&mut shared_hasher);

    // Finally throw in the target name/kind. This ensures that concurrent
    // compiles of targets in the same crate don't collide.
    unit.target.name().hash(&mut shared_hasher);
    unit.target.kind().hash(&mut shared_hasher);

    hash_rustc_version(bcx, &mut shared_hasher, unit)?;

    if bcx.ws.is_member(&unit.pkg) {
        // This is primarily here for clippy. This ensures that the clippy
        // artifacts are separate from the `check` ones.
        if let Some(path) = &bcx.rustc().workspace_wrapper {
            path.hash(&mut shared_hasher);
        }
    }

    // Seed the contents of `__CARGO_DEFAULT_LIB_METADATA` to the hasher if present.
    // This should be the release channel, to get a different hash for each channel.
    if let Ok(ref channel) = bcx.gctx.get_env("__CARGO_DEFAULT_LIB_METADATA") {
        channel.hash(&mut shared_hasher);
    }

    // std units need to be kept separate from user dependencies. std crates
    // are differentiated in the Unit with `is_std` (for things like
    // `-Zforce-unstable-if-unmarked`), so they are always built separately.
    // This isn't strictly necessary for build dependencies which probably
    // don't need unstable support. A future experiment might be to set
    // `is_std` to false for build dependencies so that they can be shared
    // with user dependencies.
    unit.is_std.hash(&mut shared_hasher);

    // While we don't hash RUSTFLAGS because it may contain absolute paths that
    // hurts reproducibility, we track whether a unit's RUSTFLAGS is from host
    // config, so that we can generate a different metadata hash for runtime
    // and compile-time units.
    //
    // HACK: This is a temporary hack for fixing rust-lang/cargo#14253
    // Need to find a long-term solution to replace this fragile workaround.
    // See https://github.com/rust-lang/cargo/pull/14432#discussion_r1725065350
    if unit.kind.is_host() && !bcx.gctx.target_applies_to_host().unwrap_or_default() {
        let host_info = bcx.target_data.info(CompileKind::Host);
        let target_configs_are_different = unit.rustflags != host_info.rustflags
            || unit.rustdocflags != host_info.rustdocflags
            || bcx
                .target_data
                .target_config(CompileKind::Host)
                .links_overrides
                != unit.links_overrides;
        target_configs_are_different.hash(&mut shared_hasher);
    }

    let mut c_metadata_hasher = shared_hasher.clone();
    // Mix in the target-metadata of all the dependencies of this target.
    let mut dep_c_metadata_hashes = deps_metadata
        .iter()
        .map(|m| m.c_metadata)
        .collect::<Vec<_>>();
    dep_c_metadata_hashes.sort();
    dep_c_metadata_hashes.hash(&mut c_metadata_hasher);

    let mut unit_id_hasher = shared_hasher.clone();
    // Trust: distinct applied workspace path contracts need distinct artifact
    // slots, not only dirty fingerprints. Otherwise an independent tool and a
    // mixed workspace graph sharing target/ overwrite each other's same-named
    // rlibs on every invocation. Use the exact normalized rules already keyed by
    // fingerprinting; c_metadata and raw rustflag/PGO treatment stay unchanged.
    if let Some(remap) = trim_paths::workspace_remap_fingerprint_context(bcx, unit) {
        "targo-workspace-remap-unit-v1".hash(&mut unit_id_hasher);
        remap.hash(&mut unit_id_hasher);
    }
    if bcx.confines(unit) {
        "targo-confined-action-v1".hash(&mut unit_id_hasher);
    }
    if bcx.shared_dependency_units.contains(unit) && unit.pkg.package_id().source_id().is_git() {
        // Precise Git revisions are absent from ordinary PackageId hashing.
        // Bind the shared variant here so dependency unit IDs propagate a
        // changed Git input to its parents without changing symbol metadata.
        let identity = crate::compiler::shared_dependencies::git_source_identity(
            unit.pkg.package_id().source_id(),
        )
        .expect("shared Git units have a full resolved commit");
        "targo-shared-git-unit-v1".hash(&mut unit_id_hasher);
        identity.hash(&mut unit_id_hasher);
    }
    if let Some(identity) = bcx.rustc().content_variant(bcx.ws.is_member(&unit.pkg)) {
        // Separate cached compiler products, but keep installation paths and
        // executable stamps out of symbol mangling / -Cmetadata.
        "targo-compiler-content-variant-v1".hash(&mut unit_id_hasher);
        identity.hash(&mut unit_id_hasher);
    }
    // Mix in the target-metadata of all the dependencies of this target.
    let mut dep_unit_id_hashes = deps_metadata.iter().map(|m| m.unit_id).collect::<Vec<_>>();
    dep_unit_id_hashes.sort();
    dep_unit_id_hashes.hash(&mut unit_id_hasher);
    // Avoid trashing the caches on RUSTFLAGS changing via `unit_id`
    //
    // Limited to `unit_id` to help with reproducible build / PGO issues.
    let default = Vec::new();
    let extra_args = bcx.extra_args_for(unit).unwrap_or(&default);
    let flags = if unit.mode.is_doc() || unit.mode.is_doc_scrape() {
        &unit.rustdocflags
    } else {
        &unit.rustflags
    };
    // Trust: a verification-off unit of a verified run leaves the run's session
    // nonce and proof-artifact root out of its key, so an identical dependency
    // is reused across checks (`trust_unit_id`). Every other unit keeps
    // upstream's key bit for bit.
    // Keep the ordinary runner's actual primary set. The pure planner supplies
    // the same resolved root package population selected by prepare_units.
    let is_primary_package = primary_packages.contains(&unit.pkg.package_id());
    let lane = trust_unit_id::session_invariant_lane(bcx, unit, is_primary_package);
    hash_unit_id_flags(&mut unit_id_hasher, extra_args, flags, lane.as_ref());

    let c_metadata = UnitHash(Hasher::finish(&c_metadata_hasher));
    let unit_id = UnitHash(Hasher::finish(&unit_id_hasher));
    // Trust: a store exists only in the eligible unverified lane. Private and
    // verified units retain their original (including session-invariant) IDs.
    let shared_storage_id = if bcx.shared_dependency_root.is_some() {
        let dependencies = bcx.unit_graph[unit]
            .iter()
            .zip(&deps_metadata)
            .map(|(dependency, metadata)| (dependency.extern_crate_name.as_str(), *metadata))
            .collect::<Vec<_>>();
        shared_storage_id(unit_id, extra_args, flags, &dependencies)
    } else {
        unit_id
    };

    Ok(Metadata {
        unit_id,
        shared_storage_id,
        c_metadata,
        c_extra_filename,
        pkg_dir,
    })
}

/// Trust: partition only shared storage on complete flag vectors omitted from
/// reproducible unit metadata, including their transitive dependency variants.
/// Ordinary unaffected slots retain their existing identity.
fn shared_storage_id(
    unit_id: UnitHash,
    extra_args: &[String],
    flags: &[String],
    dependencies: &[(&str, Metadata)],
) -> UnitHash {
    if !has_remap_path_prefix(extra_args)
        && !has_remap_path_prefix(flags)
        && dependencies
            .iter()
            .all(|(_, dependency)| dependency.shared_storage_id == dependency.unit_id)
    {
        return unit_id;
    }
    let mut hasher = StableHasher::new();
    "targo-shared-storage-flags-v1".hash(&mut hasher);
    unit_id.hash(&mut hasher);
    extra_args.hash(&mut hasher);
    flags.hash(&mut hasher);
    let mut dependencies = dependencies
        .iter()
        .map(|(name, dependency)| (*name, dependency.shared_storage_id))
        .collect::<Vec<_>>();
    dependencies.sort();
    dependencies.hash(&mut hasher);
    UnitHash(Hasher::finish(&hasher))
}

// Trust: preserve both existing directory separators, including ordinary short hashes.
fn package_directory(name: &str, hash: &str, new_layout: bool) -> String {
    let separator = if new_layout { "/" } else { "-" };
    let mut pkg = String::with_capacity(name.len() + separator.len() + hash.len());
    pkg.push_str(name);
    pkg.push_str(separator);
    pkg.push_str(hash);
    pkg
}

/// Hashes a unit's compiler flags into its `unit_id`: `extra_args`, then
/// `flags` (rustflags, or rustdocflags for a doc unit), each skipped when it
/// may carry `--remap-path-prefix`.
///
/// Trust: with a [`SessionInvariantLane`] (a verification-off unit of a
/// verified run) the lane goes in first, and both vectors lose the run's
/// per-run transport options. Without one, or when either vector does not
/// parse, this is upstream's hashing, bit for bit.
fn hash_unit_id_flags(
    hasher: &mut StableHasher,
    extra_args: &[String],
    flags: &[String],
    lane: Option<&SessionInvariantLane<'_>>,
) {
    let projected = lane.and_then(|lane| {
        Some((
            lane,
            without_per_run_transport(extra_args)?,
            without_per_run_transport(flags)?,
        ))
    });
    let (extra_args, flags) = match &projected {
        None => (extra_args, flags),
        Some((lane, extra_args, flags)) => {
            lane.hash(hasher);
            (extra_args.as_slice(), flags.as_slice())
        }
    };
    if !has_remap_path_prefix(extra_args) {
        extra_args.hash(hasher);
    }
    if !has_remap_path_prefix(flags) {
        flags.hash(hasher);
    }
}

/// HACK: Detect the *potential* presence of `--remap-path-prefix`
///
/// As CLI parsing is contextual and dependent on the CLI definition to understand the context, we
/// can't say for sure whether `--remap-path-prefix` is present, so we guess if anything looks like
/// it.
/// If we could, we'd strip it out for hashing.
/// Instead, we use this to avoid hashing rustflags if it might be present to avoid the risk of taking
/// a flag that is trying to make things reproducible and making things less reproducible by the
/// `-Cextra-filename` showing up in the rlib, even with `split-debuginfo`.
fn has_remap_path_prefix(args: &[String]) -> bool {
    args.iter()
        .any(|s| s.starts_with("--remap-path-prefix=") || s == "--remap-path-prefix")
}

/// Hash the version of rustc being used during the build process.
fn hash_rustc_version(
    bcx: &BuildContext<'_, '_>,
    hasher: &mut StableHasher,
    unit: &Unit,
) -> CargoResult<()> {
    let observation = bcx
        .rustc()
        .version_observation(bcx.ws.is_member(&unit.pkg))?;
    let vers = observation.version;
    if vers.pre.is_empty() || bcx.gctx.cli_unstable().separate_nightlies {
        // For stable, keep the artifacts separate. This helps if someone is
        // testing multiple versions, to avoid recompiles. Note though that for
        // cross-compiled builds the `host:` line of `verbose_version` is
        // omitted since rustc should produce the same output for each target
        // regardless of the host.
        for line in observation.verbose_version.lines() {
            if unit.kind.is_host() || !line.starts_with("host: ") {
                line.hash(hasher);
            }
        }
        return Ok(());
    }
    // On "nightly"/"beta"/"dev"/etc, keep each "channel" separate. Don't hash
    // the date/git information, so that whenever someone updates "nightly",
    // they won't have a bunch of stale artifacts in the target directory.
    //
    // This assumes that the first segment is the important bit ("nightly",
    // "beta", "dev", etc.). Skip other parts like the `.3` in `-beta.3`.
    vers.pre.split('.').next().hash(hasher);
    // Keep "host" since some people switch hosts to implicitly change
    // targets, (like gnu vs musl or gnu vs msvc). In the future, we may want
    // to consider hashing `unit.kind.short_name()` instead.
    if unit.kind.is_host() {
        observation.host.hash(hasher);
    }
    // None of the other lines are important. Currently they are:
    // binary: rustc  <-- or "rustdoc"
    // commit-hash: 38114ff16e7856f98b2b4be7ab4cd29b38bed59a
    // commit-date: 2020-03-21
    // host: x86_64-apple-darwin
    // release: 1.44.0-nightly
    // LLVM version: 9.0
    //
    // The backend version ("LLVM version") might become more relevant in
    // the future when cranelift sees more use, and people want to switch
    // between different backends without recompiling.
    Ok(())
}

/// Returns whether or not this unit should use a hash in the filename to make it unique.
fn use_extra_filename(bcx: &BuildContext<'_, '_>, unit: &Unit) -> bool {
    if unit.mode.is_doc_test() || unit.mode.is_doc() {
        // Doc tests do not have metadata.
        return false;
    }
    if bcx.gctx.cli_unstable().build_dir_new_layout {
        if unit.mode.is_any_test() || unit.mode.is_check() {
            // These always use metadata.
            return true;
        }

        if unit.target.is_custom_build() {
            // Build scripts never use metadata
            return false;
        }
        // No metadata in these cases:
        //
        // - dylib, cdylib, executable: `pkg_dir` avoids collisions for us and rustc isn't
        // looking these up by `-Cextra-filename`
        //
        // The __CARGO_DEFAULT_LIB_METADATA env var is used to override this to
        // force metadata in the hash. This is only used for building libstd. For
        // example, if libstd is placed in a common location, we don't want a file
        // named /usr/lib/libstd.so which could conflict with other rustc
        // installs. In addition it prevents accidentally loading a libstd of a
        // different compiler at runtime.
        // See https://github.com/rust-lang/cargo/issues/3005
        if (unit.target.is_dylib() || unit.target.is_cdylib() || unit.target.is_executable())
            && bcx.gctx.get_env("__CARGO_DEFAULT_LIB_METADATA").is_err()
        {
            return false;
        }
    } else {
        if unit.mode.is_any_test() || unit.mode.is_check() {
            // These always use metadata.
            return true;
        }
        // No metadata in these cases:
        //
        // - dylibs:
        //   - if any dylib names are encoded in executables, so they can't be renamed.
        //   - TODO: Maybe use `-install-name` on macOS or `-soname` on other UNIX systems
        //     to specify the dylib name to be used by the linker instead of the filename.
        // - Windows MSVC executables: The path to the PDB is embedded in the
        //   executable, and we don't want the PDB path to include the hash in it.
        // - wasm32-unknown-emscripten executables: When using emscripten, the path to the
        //   .wasm file is embedded in the .js file, so we don't want the hash in there.
        //
        // This is only done for local packages, as we don't expect to export
        // dependencies.
        //
        // The __CARGO_DEFAULT_LIB_METADATA env var is used to override this to
        // force metadata in the hash. This is only used for building libstd. For
        // example, if libstd is placed in a common location, we don't want a file
        // named /usr/lib/libstd.so which could conflict with other rustc
        // installs. In addition it prevents accidentally loading a libstd of a
        // different compiler at runtime.
        // See https://github.com/rust-lang/cargo/issues/3005
        let short_name = bcx.target_data.short_name(&unit.kind);
        if (unit.target.is_dylib()
            || unit.target.is_cdylib()
            || (unit.target.is_executable() && short_name == "wasm32-unknown-emscripten")
            || (unit.target.is_executable() && short_name.contains("msvc")))
            && unit.pkg.package_id().source_id().is_path()
            && bcx.gctx.get_env("__CARGO_DEFAULT_LIB_METADATA").is_err()
        {
            return false;
        }
    }
    true
}

/// Returns whether or not this unit should use a hash in the pkg_dir to make it unique.
fn use_pkg_dir(bcx: &BuildContext<'_, '_>, unit: &Unit) -> bool {
    if unit.mode.is_doc_test() || unit.mode.is_doc() {
        // Doc tests do not have metadata.
        return false;
    }
    if bcx.gctx.cli_unstable().build_dir_new_layout {
        // These always use metadata.
        return true;
    }
    if unit.mode.is_any_test() || unit.mode.is_check() {
        // These always use metadata.
        return true;
    }
    // No metadata in these cases:
    //
    // - dylibs:
    //   - if any dylib names are encoded in executables, so they can't be renamed.
    //   - TODO: Maybe use `-install-name` on macOS or `-soname` on other UNIX systems
    //     to specify the dylib name to be used by the linker instead of the filename.
    // - Windows MSVC executables: The path to the PDB is embedded in the
    //   executable, and we don't want the PDB path to include the hash in it.
    // - wasm32-unknown-emscripten executables: When using emscripten, the path to the
    //   .wasm file is embedded in the .js file, so we don't want the hash in there.
    //
    // This is only done for local packages, as we don't expect to export
    // dependencies.
    //
    // The __CARGO_DEFAULT_LIB_METADATA env var is used to override this to
    // force metadata in the hash. This is only used for building libstd. For
    // example, if libstd is placed in a common location, we don't want a file
    // named /usr/lib/libstd.so which could conflict with other rustc
    // installs. In addition it prevents accidentally loading a libstd of a
    // different compiler at runtime.
    // See https://github.com/rust-lang/cargo/issues/3005
    let short_name = bcx.target_data.short_name(&unit.kind);
    if (unit.target.is_dylib()
        || unit.target.is_cdylib()
        || (unit.target.is_executable() && short_name == "wasm32-unknown-emscripten")
        || (unit.target.is_executable() && short_name.contains("msvc")))
        && unit.pkg.package_id().source_id().is_path()
        && bcx.gctx.get_env("__CARGO_DEFAULT_LIB_METADATA").is_err()
    {
        return false;
    }
    true
}

// Trust: the flag half of `unit_id` across two verified runs. The other half
// (package, features, profile, mode, kind, target, dependency `unit_id`s)
// carries nothing per-run, so equal flag hashes and equal dependencies give
// equal `unit_id`s; `rustflags::verified_targo_session_nonce_reruns_only_the_units_that_verify`
// checks the whole graph end to end.
#[cfg(test)]
mod native_unit_output_tests {
    use super::*;

    // Path/equality DATA only; no original directory, producer, Host scope or
    // publication acknowledgement is fabricated by these controls.
    #[test]
    fn cold_and_warm_unit_paths_are_stable_without_creating_directories() {
        let original = tempfile::tempdir().unwrap();
        let first = UnitOutputNamespace::new(original.path(), UnitHash(7), "a".repeat(64)).unwrap();
        let warm = UnitOutputNamespace::new(original.path(), UnitHash(7), "a".repeat(64)).unwrap();
        assert_eq!(first.root(), warm.root());
        assert_eq!(first.outputs(), warm.outputs());
        assert_eq!(first.incremental(), warm.incremental());
        assert!(first.outputs().starts_with(first.root()));
        assert!(first.incremental().starts_with(first.root()));
        assert_ne!(first.outputs(), first.incremental());
        assert_eq!(std::fs::read_dir(original.path()).unwrap().count(), 0);
    }

    #[test]
    fn distinct_resolved_units_and_layouts_have_disjoint_scratch_trees() {
        let base = Path::new("/selected/debug");
        let original = UnitOutputNamespace::new(base, UnitHash(7), "a".repeat(64)).unwrap();
        for changed in [
            // A short filename-hash collision cannot share a writable tree.
            UnitOutputNamespace::new(base, UnitHash(7), "b".repeat(64)).unwrap(),
            UnitOutputNamespace::new(base, UnitHash(8), "a".repeat(64)).unwrap(),
            UnitOutputNamespace::new(Path::new("/selected/release"), UnitHash(7), "a".repeat(64))
                .unwrap(),
        ] {
            assert!(!original.root().starts_with(changed.root()));
            assert!(!changed.root().starts_with(original.root()));
            for original_path in [original.outputs(), original.incremental()] {
                for changed_path in [changed.outputs(), changed.incremental()] {
                    assert!(!original_path.starts_with(changed.root()));
                    assert!(!changed_path.starts_with(original.root()));
                }
            }
        }
    }

    #[test]
    fn namespace_identity_never_becomes_a_path_component_escape() {
        for identity in [
            String::new(),
            "../source".into(),
            "a".repeat(63),
            "a".repeat(65),
            "A".repeat(64),
            format!("{}/", "a".repeat(63)),
        ] {
            assert!(
                UnitOutputNamespace::new(Path::new("/selected/debug"), UnitHash(7), identity)
                    .is_err()
            );
        }
    }
}

#[cfg(test)]
mod trust_unit_id_tests {
    use std::hash::{Hash, Hasher};

    use super::{Metadata, UnitHash, hash_unit_id_flags, package_directory, shared_storage_id};
    use crate::compiler::trust_unit_id::{SessionInvariantLane, without_per_run_transport};
    use crate::util::StableHasher;

    /// `trustc -vV` of an installed Trust seal.
    const TRUSTC_VV: &str = "rustc 1.99.0-dev (321aaeda7 2026-09-17) (trustc 0.1.0)
binary: trustc
commit-hash: 321aaeda75478038420d97830f14724c33c8dc39
commit-date: 2026-09-17
host: aarch64-apple-darwin
release: 1.99.0-dev
trust: 0.1.0
LLVM version: 22.1.2";

    fn lane(rustc_verbose_version: &str, is_host: bool) -> SessionInvariantLane<'_> {
        SessionInvariantLane {
            rustc_verbose_version,
            is_host,
        }
    }

    /// One run's graph-wide rustflags, in the shape targo-trust exports them:
    /// real flags, verifier policy, then the per-run session and artifact root.
    fn run_flags(session: &[&str], root: &[&str], extra: &[&str]) -> Vec<String> {
        [
            "-Coverflow-checks=yes",
            "-Cdebug-assertions=yes",
            "-Ztrust-verify-timeout-ms=5000",
            "-Ztrust-verify-function-budget-ms=120000",
        ]
        .iter()
        .chain(session)
        .chain(root)
        .chain(extra)
        .map(|flag| (*flag).to_string())
        .collect()
    }

    fn first_run() -> Vec<String> {
        run_flags(
            &[
                "-Ztrust-verify-session=1f0e9d8c7b6a5f4e3d2c1b0a99887766554433221100ffeeddccbbaa99887766",
            ],
            &["-Ztrust-proof-artifact-root=/private/var/folders/t/trust-proof-artifact-root-AAAA"],
            &[],
        )
    }

    fn second_run() -> Vec<String> {
        // Another nonce and root, and the split `-Z` spelling.
        run_flags(
            &[
                "-Z",
                "trust-verify-session=00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff",
            ],
            &[
                "-Z",
                "trust-proof-artifact-root=/private/var/folders/t/trust-proof-artifact-root-BBBB",
            ],
            &[],
        )
    }

    fn key(
        extra_args: &[String],
        flags: &[String],
        lane: Option<&SessionInvariantLane<'_>>,
    ) -> u64 {
        let mut hasher = StableHasher::new();
        hash_unit_id_flags(&mut hasher, extra_args, flags, lane);
        Hasher::finish(&hasher)
    }

    // Trust: remapping keeps reproducible compiler metadata while the complete
    // omitted vectors distinguish their concurrently retained shared products.
    #[test]
    fn remapped_flags_partition_storage_without_changing_unit_metadata() {
        let yes = vec![
            "--remap-path-prefix=/checkout=/src".to_owned(),
            "-Cdebug-assertions=yes".to_owned(),
        ];
        let no = vec![
            "--remap-path-prefix=/checkout=/src".to_owned(),
            "-Cdebug-assertions=no".to_owned(),
        ];
        for extra in [false, true] {
            let (extra_yes, flags_yes, extra_no, flags_no) = if extra {
                (yes.as_slice(), &[][..], no.as_slice(), &[][..])
            } else {
                (&[][..], yes.as_slice(), &[][..], no.as_slice())
            };
            let original = UnitHash(key(extra_yes, flags_yes, None));
            assert_eq!(original, UnitHash(key(extra_no, flags_no, None)));
            assert_ne!(
                shared_storage_id(original, extra_yes, flags_yes, &[]),
                shared_storage_id(original, extra_no, flags_no, &[])
            );
        }
        let flags = vec!["-Cdebuginfo=0".to_owned()];
        let original = UnitHash(key(&[], &flags, None));
        assert_eq!(shared_storage_id(original, &[], &flags, &[]), original);
    }

    // Trust: a parent with unchanged own flags must not reuse another child's
    // shared slot. Carry this distinction through another level, without changing
    // the original unit identities or depending on graph traversal order.
    #[test]
    fn shared_storage_variants_propagate_through_unchanged_parents() {
        let metadata = |unit_id, shared_storage_id| Metadata {
            unit_id,
            shared_storage_id,
            c_metadata: unit_id,
            c_extra_filename: true,
            pkg_dir: true,
        };
        let leaf = UnitHash(1);
        let normal = metadata(leaf, leaf);
        let a = metadata(leaf, UnitHash(2));
        let b = metadata(leaf, UnitHash(3));
        let parent = UnitHash(4);
        assert_eq!(
            shared_storage_id(parent, &[], &[], &[("leaf", normal)]),
            parent
        );
        let parent_a = shared_storage_id(parent, &[], &[], &[("leaf", a)]);
        let parent_b = shared_storage_id(parent, &[], &[], &[("leaf", b)]);
        assert_ne!(parent_a, parent_b);
        let grandparent = UnitHash(5);
        assert_ne!(
            shared_storage_id(
                grandparent,
                &[],
                &[],
                &[("parent", metadata(parent, parent_a))]
            ),
            shared_storage_id(
                grandparent,
                &[],
                &[],
                &[("parent", metadata(parent, parent_b))]
            )
        );
        assert_eq!(
            shared_storage_id(parent, &[], &[], &[("left", a), ("right", b)]),
            shared_storage_id(parent, &[], &[], &[("right", b), ("left", a)])
        );
        assert_ne!(
            shared_storage_id(parent, &[], &[], &[("left", a), ("right", b)]),
            shared_storage_id(parent, &[], &[], &[("left", b), ("right", a)])
        );
    }

    #[test]
    fn shared_storage_preserves_ordinary_short_hashes_and_both_layouts() {
        let ordinary = Metadata {
            unit_id: UnitHash(1),
            shared_storage_id: UnitHash(1),
            c_metadata: UnitHash(1),
            c_extra_filename: false,
            pkg_dir: false,
        };
        let variant = Metadata {
            shared_storage_id: UnitHash(2),
            ..ordinary
        };
        for (new_layout, separator) in [(false, "-"), (true, "/")] {
            assert_eq!(
                package_directory(
                    "package",
                    &ordinary.shared_storage_hash("short".into()),
                    new_layout
                ),
                format!("package{separator}short")
            );
            assert_eq!(
                package_directory(
                    "package",
                    &variant.shared_storage_hash("short".into()),
                    new_layout
                ),
                format!("package{separator}{}", UnitHash(2))
            );
        }
    }

    #[test]
    fn verification_off_unit_keeps_one_unit_id_across_sessions() {
        for is_host in [false, true] {
            let off = lane(TRUSTC_VV, is_host);
            assert_eq!(
                key(&[], &first_run(), Some(&off)),
                key(&[], &second_run(), Some(&off)),
                "a verification-off unit's key must not see the session nonce or artifact root"
            );
        }
        // The same projection applies to `targo rustc -- …` arguments.
        let off = lane(TRUSTC_VV, false);
        assert_eq!(
            key(&first_run(), &[], Some(&off)),
            key(&second_run(), &[], Some(&off)),
        );
    }

    #[test]
    fn verification_off_unit_key_keeps_every_input_but_the_per_run_transport() {
        let off = lane(TRUSTC_VV, false);
        let session = [
            "-Ztrust-verify-session=1f0e9d8c7b6a5f4e3d2c1b0a99887766554433221100ffeeddccbbaa99887766",
        ];
        let root =
            ["-Ztrust-proof-artifact-root=/private/var/folders/t/trust-proof-artifact-root-AAAA"];
        let base = key(&[], &run_flags(&session, &root, &[]), Some(&off));
        assert_eq!(base, key(&[], &first_run(), Some(&off)));
        for (changed, extra) in [
            ("a real compiler flag", &["--cfg", "probe"][..]),
            ("a codegen option", &["-Copt-level=1"][..]),
            ("the verifier policy", &["-Ztrust-policy=advisory"][..]),
            ("the verification level", &["-Ztrust-verify-level=2"][..]),
        ] {
            assert_ne!(
                key(&[], &run_flags(&session, &root, extra), Some(&off)),
                base,
                "{changed} must still separate verification-off units"
            );
        }
        // The dependency scope is fixed by the lane: with it on, every compiler
        // unit verifies and none reaches this key. Its spelling is left out,
        // as the fingerprint leaves it out.
        for spelling in [
            &["-Ztrust-verify-include-dependencies=no"][..],
            &["-Z", "trust_verify_include_dependencies=false"][..],
        ] {
            assert_eq!(
                key(&[], &run_flags(&session, &root, spelling), Some(&off)),
                base
            );
        }
        // Order is kept: rustc reads the last of two conflicting flags.
        assert_ne!(
            key(
                &[],
                &run_flags(&session, &root, &["-Copt-level=1", "-Copt-level=2"]),
                Some(&off)
            ),
            key(
                &[],
                &run_flags(&session, &root, &["-Copt-level=2", "-Copt-level=1"]),
                Some(&off)
            ),
        );

        // The toolchain: upstream's `unit_id` keeps only a `-dev` compiler's
        // channel name, so the full `rustc -vV` has to be in this key.
        let rebuilt = TRUSTC_VV.replace(
            "commit-hash: 321aaeda75478038420d97830f14724c33c8dc39",
            "commit-hash: 0123456789abcdef0123456789abcdef01234567",
        );
        assert_ne!(key(&[], &first_run(), Some(&lane(&rebuilt, false))), base);
        // A target unit's key is host-independent; a host unit's is not.
        let other_host =
            TRUSTC_VV.replace("host: aarch64-apple-darwin", "host: x86_64-apple-darwin");
        assert_eq!(
            key(&[], &first_run(), Some(&lane(&other_host, false))),
            base
        );
        assert_ne!(
            key(&[], &first_run(), Some(&lane(&other_host, true))),
            key(&[], &first_run(), Some(&lane(TRUSTC_VV, true))),
        );

        // The lane: the same flags outside the verified protocol, where Targo
        // appends none of its per-unit protocol arguments, are another unit.
        let unverified = without_per_run_transport(&first_run()).unwrap();
        assert_ne!(key(&[], &unverified, None), base);

        // Flags that do not parse get no projection: upstream's key, nonce
        // included, until the compilation reports them.
        let mut malformed = first_run();
        malformed.push("-Z".to_string());
        assert_eq!(key(&[], &malformed, Some(&off)), key(&[], &malformed, None));
    }

    #[test]
    fn verified_unit_keeps_upstreams_key_and_its_session() {
        for flags in [first_run(), second_run()] {
            let mut upstream = StableHasher::new();
            Vec::<String>::new().hash(&mut upstream);
            flags.hash(&mut upstream);
            assert_eq!(
                key(&[], &flags, None),
                Hasher::finish(&upstream),
                "a unit outside the session-invariant lane must hash exactly as upstream Cargo"
            );
        }
        assert_ne!(
            key(&[], &first_run(), None),
            key(&[], &second_run(), None),
            "a verified unit's key keeps its session, so each session's proof artifact has its own path"
        );
    }
}
