//! Retained actual dependency materializations in one original cache domain.
//! This is not native filesystem admission or a Rust metadata validity proof.
use super::build_runner::{OriginalOutputLeases, OutputFile, UnitOutputNamespace};
use super::candidate_commands::{ExpectedCommands, ExpectedUnitCommand, UnitKey};
use super::output_observation::{Observer, Seal};
use crate::ops::cargo_test::workload::Inputs as OriginalInputs;
use crate::resource_v3::workload::bank::CoordinatorLocalOperation;
use crate::resource_v3::{CoordinatorCompilerCapture, Startup};
use crate::util::CargoResult;
use anyhow::{Context as _, ensure};
use std::collections::{BTreeMap, BTreeSet};
use std::os::unix::ffi::OsStrExt as _;
use std::path::Path;
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicBool, AtomicUsize, Ordering},
};
use std::time::Instant;
use trust_resource_controller::client::{
    CoordinatorBrokerServer, workload::CompletedLocalOperation,
};
use trust_resource_controller::workload::host::coordinator::PublicationSelection;
use trust_resource_controller::workload::host::publication::{Intent, Key, Kind, Operation};
use trust_resource_controller::{
    CommandSpec,
    descriptors::{AdmittedPackageSource, AdmittedRootDirectory, AdmittedRootFile},
};
use trust_resource_provenance::program::produced::{HeldOutputRoot, HeldProducedProgram};

const MAX_PRODUCERS: usize = 4096;
const MAX_ATTEMPTS: usize = 4096;
const MAX_EPOCHS: usize = 64;
const MAX_RETAINED: usize = 128 * 1024 * 1024;

mod compiler_inputs;
pub(crate) use compiler_inputs::CompilerInputLease;

/// Actual selected original, not an FD/path/digest constructor. Its producer
/// remains separately retained by the parent ledger through comparison.
#[derive(Clone)]
pub(crate) struct DependencyFile {
    original: Arc<AdmittedRootFile>,
    producer: [u8; 16],
}
impl DependencyFile {
    pub(crate) fn original(&self) -> &Arc<AdmittedRootFile> {
        &self.original
    }
    pub(crate) fn producer_member(&self) -> [u8; 16] {
        self.producer
    }
}
struct ReadLease {
    counter: Arc<AtomicUsize>,
    active: AtomicBool,
}
impl ReadLease {
    fn retire(&self) {
        if self.active.swap(false, Ordering::AcqRel) {
            self.counter.fetch_sub(1, Ordering::AcqRel);
        }
    }
}
impl Drop for ReadLease {
    fn drop(&mut self) {
        self.retire();
    }
}
#[derive(Clone)]
struct Reader(Arc<ReadLease>);
impl Reader {
    fn new(counter: Arc<AtomicUsize>) -> Self {
        counter.fetch_add(1, Ordering::AcqRel);
        Self(Arc::new(ReadLease {
            counter,
            active: AtomicBool::new(true),
        }))
    }
    fn retire(&self) {
        self.0.retire();
    }
}
/// FD-only custody for the actual consumer. It owns neither ledger nor
/// captures: captures retain their factory owner and must never form a cycle.
#[derive(Clone)]
pub(crate) struct DependencyLease {
    files: Vec<DependencyFile>,
    _readers: Vec<Reader>,
}
impl DependencyLease {
    // Called only after SAME actual native compiler's completion barrier.
    // Capture/evidence may keep FD clones after the consumer really retires.
    fn retire(&self) {
        for reader in &self._readers {
            reader.retire();
        }
    }
    pub(crate) fn files(&self) -> &[DependencyFile] {
        &self.files
    }
    pub(crate) fn validate(&self, deadline: Instant) -> CargoResult<()> {
        for file in &self.files {
            file.original.validate(deadline)?;
        }
        Ok(())
    }
}

struct Materialization {
    key: UnitKey,
    command: CommandSpec,
    outputs: Arc<Vec<OutputFile>>,
    directory: Arc<UnitDirectories>,
    files: BTreeMap<usize, Arc<AdmittedRootFile>>,
    source: Arc<AdmittedPackageSource>,
    parents: Vec<Arc<Materialization>>,
    readers: Arc<AtomicUsize>,
    // SAME real child/guard/terminal/bytes, never reconstructed from DATA.
    native: Arc<CoordinatorCompilerCapture>,
    _coverage: Seal,
    coordinator_attempt: [u8; 16],
    issued: Instant,
    _layout: Arc<OriginalOutputLeases>,
    _selected: Arc<HeldOutputRoot>,
    _master: Arc<OriginalInputs>,
}

/// Parent-only retained publication input. The original file comes solely
/// from an actual retired Materialization; destinations remain expected DATA.
/// Do not store this in compiler factory/Inputs (capture-owner cycle). An
/// actual native publisher must still bind destinations and bookend the copy;
/// this value cannot authorize a path write or acknowledge publication.
pub(crate) struct Publication {
    producer: Arc<Materialization>,
    original: Arc<AdmittedRootFile>,
    destinations: Vec<std::path::PathBuf>,
    _reader: Reader,
    layout: Arc<OriginalOutputLeases>,
    selected: Arc<HeldOutputRoot>,
    master: Arc<OriginalInputs>,
    startup: Arc<Startup>,
    deadline: Instant,
}
impl Publication {
    pub(crate) fn original(&self) -> &Arc<AdmittedRootFile> {
        &self.original
    }
    pub(crate) fn destinations(&self) -> &[std::path::PathBuf] {
        &self.destinations
    }
    pub(crate) fn validate(&self, deadline: Instant) -> CargoResult<()> {
        let deadline = deadline.min(self.deadline);
        ensure!(
            Instant::now() < deadline,
            "retired publication input expired"
        );
        self.master.validate()?;
        self.selected.validate(deadline)?;
        self.layout.validate(self.selected.path())?;
        let mut stack = vec![self.producer.clone()];
        let mut validated = Vec::new();
        while let Some(actual) = stack.pop() {
            if validated.iter().any(|known| Arc::ptr_eq(known, &actual)) {
                continue;
            }
            actual.native.require_compiler_materialization(
                &self.startup,
                &actual.command,
                actual.coordinator_attempt,
                actual.issued,
            )?;
            actual.directory.validate(&self.selected, deadline)?;
            actual.source.validate(deadline)?;
            for file in actual.files.values() {
                file.validate(deadline)?;
            }
            stack.extend(actual.parents.iter().cloned());
            validated.push(actual);
        }
        self.original.validate(deadline)?;
        self.selected.validate(deadline)?;
        Ok(())
    }
}

/// Actual copied set awaiting SAME native one-use local return. Every source
/// is derived from a retired materialization; no raw output path can create it.
pub(crate) struct PendingPublication {
    domain: Arc<()>,
    producer: Arc<Materialization>,
    key: Key,
    selection: PublicationSelection,
    sources: Vec<Publication>,
    files: Vec<Arc<AdmittedRootFile>>,
    layout: Arc<OriginalOutputLeases>,
    selected: Arc<HeldOutputRoot>,
    master: Arc<OriginalInputs>,
    startup: Arc<Startup>,
}
/// Complete multi-file set with actual one-use native completion and retained
/// independent destination originals. This is not a verifier/proof grade.
pub(crate) struct PublishedUnit {
    pending: PendingPublication,
    native: CompletedLocalOperation,
    acknowledged: bool,
}
/// Current complete graph, checked while the actual coordinator still owns
/// its first unit and fixed inspection owns a distinct admitted second unit.
pub(crate) struct PendingGraphClosure {
    key: Key,
    member_binding: [u8; 32],
    records: Vec<Arc<Materialization>>,
    canonical: Vec<Arc<AdmittedRootFile>>,
    selections: Vec<PublicationSelection>,
    startup: Arc<Startup>,
    master: Arc<OriginalInputs>,
    selected: Arc<HeldOutputRoot>,
    layout: Arc<OriginalOutputLeases>,
    programs: Vec<PendingProgram>,
}
pub(crate) struct GraphClosure {
    pending: PendingGraphClosure,
    native: Arc<CompletedLocalOperation>,
    programs: Vec<Arc<PublishedProgram>>,
    acknowledged: bool,
}
struct PendingProgram {
    producer: Arc<Materialization>,
    original: Arc<AdmittedRootFile>,
    image: Arc<HeldProducedProgram>,
    runtime_roots: Vec<std::path::PathBuf>,
}
/// A complete published executable tied to the actual successful compiler,
/// copied canonical original, paid loader capture and one-use graph return.
/// There is no path/hash/status/JSON constructor and no NativeOutput fallback.
pub(crate) struct PublishedProgram {
    pending: PendingProgram,
    native: Arc<CompletedLocalOperation>,
    acknowledged: Arc<AtomicBool>,
    startup: Arc<Startup>,
    master: Arc<OriginalInputs>,
    selected: Arc<HeldOutputRoot>,
    layout: Arc<OriginalOutputLeases>,
    member: [u8; 16],
}
impl PublishedProgram {
    pub(crate) fn require_acknowledged(&self) -> CargoResult<()> {
        ensure!(
            self.acknowledged.load(Ordering::Acquire),
            "published program precedes actual graph acknowledgement"
        );
        self.native.require_success()?;
        Ok(())
    }
    pub(crate) fn master(&self) -> &Arc<OriginalInputs> {
        &self.master
    }
    pub(crate) fn layout(&self) -> &Arc<OriginalOutputLeases> {
        &self.layout
    }
    pub(crate) fn image(&self) -> &Arc<HeldProducedProgram> {
        &self.pending.image
    }
    pub(crate) fn runtime_roots(&self) -> &[std::path::PathBuf] {
        &self.pending.runtime_roots
    }
    pub(crate) fn producer_attempt(&self) -> [u8; 16] {
        self.member
    }
    pub(crate) fn validate(&self, deadline: Instant) -> CargoResult<()> {
        self.require_acknowledged()?;
        let producer = &self.pending.producer;
        producer.native.require_compiler_materialization(
            &self.startup,
            &producer.command,
            producer.coordinator_attempt,
            producer.issued,
        )?;
        self.master.validate()?;
        self.selected.validate(deadline)?;
        self.layout.validate(self.selected.path())?;
        self.pending.original.validate(deadline)?;
        self.pending.image.validate(deadline)?;
        Ok(())
    }
    pub(crate) fn retained_bytes(&self) -> Option<usize> {
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(2 * std::mem::size_of::<usize>())?
            .checked_add(
                self.pending
                    .runtime_roots
                    .capacity()
                    .checked_mul(std::mem::size_of::<std::path::PathBuf>())?,
            )?
            .checked_add(self.pending.image.retained_bytes()?)?
            .checked_add(self.pending.original.retained_bytes()?)?
            .checked_add(self.native.retained_bytes()?)?
            .checked_add(8 * std::mem::size_of::<usize>())?;
        for path in &self.pending.runtime_roots {
            bytes = bytes.checked_add(path.capacity())?;
        }
        Some(bytes)
    }
}
impl PendingGraphClosure {
    pub(crate) fn complete(mut self, native: CompletedLocalOperation) -> CargoResult<GraphClosure> {
        ensure!(
            native.begin().key == self.key,
            "graph return belongs to another actual inspection"
        );
        native.require_success()?;
        let native = Arc::new(native);
        let acknowledged = Arc::new(AtomicBool::new(false));
        let mut programs = Vec::new();
        programs.try_reserve_exact(self.programs.len())?;
        for pending in std::mem::take(&mut self.programs) {
            let member = pending
                .producer
                .native
                .native_status()
                .context("published program lost SAME actual native compiler status")?
                .member_attempt;
            programs.push(Arc::new(PublishedProgram {
                pending,
                native: native.clone(),
                acknowledged: acknowledged.clone(),
                startup: self.startup.clone(),
                master: self.master.clone(),
                selected: self.selected.clone(),
                layout: self.layout.clone(),
                member,
            }));
        }
        Ok(GraphClosure {
            pending: self,
            native,
            programs,
            acknowledged: false,
        })
    }
}
impl GraphClosure {
    /// Pure getter after the actual one-use graph acknowledgement. Capturing
    /// or hashing a new program after coordinator exit is not permitted here.
    pub(crate) fn programs(&self) -> CargoResult<&[Arc<PublishedProgram>]> {
        ensure!(
            self.acknowledged,
            "published programs precede actual graph acknowledgement"
        );
        for program in &self.programs {
            program.require_acknowledged()?;
        }
        Ok(&self.programs)
    }
    pub(crate) fn retained_bytes(&self) -> Option<usize> {
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(
                self.native
                    .retained_bytes()?
                    .checked_add(2 * std::mem::size_of::<usize>())?,
            )?
            .checked_add(
                self.pending
                    .records
                    .capacity()
                    .checked_mul(std::mem::size_of::<Arc<Materialization>>())?,
            )?
            .checked_add(
                self.pending
                    .canonical
                    .capacity()
                    .checked_mul(std::mem::size_of::<Arc<AdmittedRootFile>>())?,
            )?
            .checked_add(
                self.pending
                    .selections
                    .capacity()
                    .checked_mul(std::mem::size_of::<PublicationSelection>())?,
            )?;
        for selection in &self.pending.selections {
            bytes = bytes.checked_add(
                selection
                    .retained_bytes()?
                    .checked_sub(std::mem::size_of::<PublicationSelection>())?,
            )?;
        }
        // Canonical captures may outlive the publication wrappers. Include
        // their actual metadata; shared immutable compiler graph is excluded.
        for file in &self.pending.canonical {
            bytes = bytes.checked_add(file.retained_bytes()?)?;
        }
        bytes = bytes.checked_add(
            self.programs
                .capacity()
                .checked_mul(std::mem::size_of::<Arc<PublishedProgram>>())?,
        )?;
        for program in &self.programs {
            bytes = bytes.checked_add(program.retained_bytes()?)?;
        }
        Some(bytes)
    }
    /// Pure SAME-owner/member association after native retirement. All heavy
    /// validation already occurred under the retained positive IO operation;
    /// neither post-exit status nor a hash can synthesize this closure.
    pub(crate) fn require_inputs(
        &self,
        startup: &Arc<Startup>,
        master: &Arc<OriginalInputs>,
        selected: &Arc<HeldOutputRoot>,
        layout: &Arc<OriginalOutputLeases>,
        expected: &ExpectedCommands,
    ) -> CargoResult<()> {
        ensure!(
            self.acknowledged
                && Arc::ptr_eq(startup, &self.pending.startup)
                && Arc::ptr_eq(master, &self.pending.master)
                && Arc::ptr_eq(selected, &self.pending.selected)
                && Arc::ptr_eq(layout, &self.pending.layout)
                && expected.member_binding() == self.pending.member_binding
                && expected.coordinator_attempt() == self.pending.key.coordinator
                && expected.entries().len() == self.pending.records.len()
                && self.pending.selections.len() == self.pending.records.len()
                && self.pending.canonical.len()
                    == self
                        .pending
                        .selections
                        .iter()
                        .map(|selection| selection.destinations.len())
                        .sum::<usize>(),
            "completed graph belongs to another original domain/member"
        );
        self.native.require_success()?;
        Ok(())
    }
    pub(crate) fn acknowledge(
        &mut self,
        server: &mut CoordinatorBrokerServer,
        deadline: Instant,
    ) -> CargoResult<()> {
        ensure!(
            !self.acknowledged,
            "whole-graph acknowledgement already consumed"
        );
        // SAFETY: only inspect_graph constructs this complete current exact
        // population under genuine local IO, then SAME one-use native return.
        // Retain every original/capture through this final protocol barrier.
        unsafe {
            server.complete_graph(&self.native, deadline)?;
        }
        self.acknowledged = true;
        for program in &self.programs {
            program.acknowledged.store(true, Ordering::Release);
        }
        Ok(())
    }
}
impl PendingPublication {
    pub(crate) fn complete(self, native: CompletedLocalOperation) -> CargoResult<PublishedUnit> {
        ensure!(
            native.begin().key == self.key,
            "publication return belongs to another actual local operation"
        );
        native.require_success()?;
        // The fixed native local IO is now positively closed. FD retention
        // does not keep a logical compiler reader active forever.
        for source in &self.sources {
            source._reader.retire();
        }
        Ok(PublishedUnit {
            pending: self,
            native,
            acknowledged: false,
        })
    }
}
impl PublishedUnit {
    /// Conservative new owned metadata/copies only. Actual immutable graph
    /// producers, captures, sources, SDK, Layout/root and budget owners are
    /// shared and remain charged by their original graph.
    pub(crate) fn retained_bytes(&self) -> Option<usize> {
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(
                self.native
                    .retained_bytes()?
                    .checked_sub(std::mem::size_of::<CompletedLocalOperation>())?,
            )?
            .checked_add(
                self.pending
                    .selection
                    .retained_bytes()?
                    .checked_sub(std::mem::size_of::<PublicationSelection>())?,
            )?
            .checked_add(
                self.pending
                    .sources
                    .capacity()
                    .checked_mul(std::mem::size_of::<Publication>())?,
            )?
            .checked_add(
                self.pending
                    .files
                    .capacity()
                    .checked_mul(std::mem::size_of::<Arc<AdmittedRootFile>>())?,
            )?;
        for source in &self.pending.sources {
            bytes = bytes
                .checked_add(
                    source
                        .destinations
                        .capacity()
                        .checked_mul(std::mem::size_of::<std::path::PathBuf>())?,
                )?
                .checked_add(std::mem::size_of::<ReadLease>() + 2 * std::mem::size_of::<usize>())?;
            for path in &source.destinations {
                bytes = bytes.checked_add(path.capacity())?;
            }
        }
        for file in &self.pending.files {
            bytes = bytes.checked_add(file.retained_bytes()?)?;
        }
        Some(bytes)
    }
    pub(crate) fn selection(&self) -> &PublicationSelection {
        &self.pending.selection
    }
    pub(crate) fn files(&self) -> &[Arc<AdmittedRootFile>] {
        &self.pending.files
    }
    pub(crate) fn acknowledge(
        &mut self,
        server: &mut CoordinatorBrokerServer,
        deadline: Instant,
    ) -> CargoResult<()> {
        ensure!(
            !self.acknowledged,
            "publication acknowledgement was already consumed"
        );
        self.native.require_success()?;
        // SAFETY: only Ledger::publish_unit constructs this retained complete
        // set through genuine retired sources and fixed admitted IO. The
        // native return is SAME-key, one-use and successful; source/Layout/
        // selected originals and actual destination files remain retained.
        unsafe {
            server.complete_publication(&self.pending.selection, &self.native, deadline)?;
        }
        self.acknowledged = true;
        Ok(())
    }
}

/// A logical expected-unit attempt, not a CPU credit or native GO permission.
/// Losing one unresolved poisons this cache domain; native custody/Unknown is
/// still owned by the original WorkGuard and native lifetime loop.
pub(crate) struct PendingUnit {
    startup: Arc<Startup>,
    deadline: Instant,
    compiler_inputs_issued: AtomicBool,
    domain: Arc<()>,
    key: UnitKey,
    command: CommandSpec,
    outputs: Arc<Vec<OutputFile>>,
    directory: Arc<UnitDirectories>,
    source: Arc<AdmittedPackageSource>,
    parents: Vec<Arc<Materialization>>,
    dependencies: DependencyLease,
    poisoned: Arc<AtomicBool>,
    active: Arc<Mutex<BTreeSet<UnitKey>>>,
    settled: bool,
    coordinator_attempt: [u8; 16],
    issued: Instant,
    _layout: Arc<OriginalOutputLeases>,
    _selected: Arc<HeldOutputRoot>,
    _master: Arc<OriginalInputs>,
}
impl PendingUnit {
    pub(crate) fn coordinator_attempt(&self) -> [u8; 16] {
        self.coordinator_attempt
    }
    pub(crate) fn issued(&self) -> Instant {
        self.issued
    }
}

/// Prepared by the actual original parent before coordinator GO. All three
/// directories derive from the SAME selected output owner and descriptor
/// budget. Paths select DATA; these originals still supply no write grant.
struct UnitDirectories {
    namespace: UnitOutputNamespace,
    root: Arc<AdmittedRootDirectory>,
    outputs: Arc<AdmittedRootDirectory>,
    incremental: Arc<AdmittedRootDirectory>,
}
impl UnitDirectories {
    fn validate(&self, selected: &HeldOutputRoot, deadline: Instant) -> CargoResult<()> {
        for (original, path) in [
            (&self.root, self.namespace.root()),
            (&self.outputs, self.namespace.outputs()),
            (&self.incremental, self.namespace.incremental()),
        ] {
            ensure!(
                original.path() == path && original.output_root() == selected.path(),
                "private unit directory lost SAME selected root/namespace association"
            );
            original.validate(deadline)?;
        }
        selected.validate(deadline)?;
        Ok(())
    }
}
impl Drop for PendingUnit {
    fn drop(&mut self) {
        if !self.settled {
            self.poisoned.store(true, Ordering::Release);
        }
        if let Ok(mut active) = self.active.lock() {
            active.remove(&self.key);
        } else {
            self.poisoned.store(true, Ordering::Release);
        }
    }
}

/// Keep this in the parent side/cache domain and move it between coordinator
/// epochs. Fresh skips reuse only these retained genuine cold producers. A
/// missing warm owner is a refusal; this API never forces recompilation or
/// promotes a Fresh report/hash to an owner. Whole-package source bookends are
/// conservative pending finer independently checked compiler-readset reuse.
pub(crate) struct Ledger {
    domain: Arc<()>,
    records: BTreeMap<UnitKey, Arc<Materialization>>,
    history: Vec<Arc<Materialization>>,
    prepared: BTreeMap<UnitKey, Arc<UnitDirectories>>,
    attempts: BTreeMap<[u8; 32], BTreeSet<UnitKey>>,
    retired: BTreeSet<[u8; 16]>,
    failed_epochs: BTreeSet<[u8; 16]>,
    active: Arc<Mutex<BTreeSet<UnitKey>>>,
    poisoned: Arc<AtomicBool>,
    retained: usize,
    deadline: Instant,
    // Drop retained real captures/files before their original Layout/root.
    layout: Arc<OriginalOutputLeases>,
    selected: Arc<HeldOutputRoot>,
    original: Arc<OriginalInputs>,
    startup: Arc<Startup>,
}
impl Ledger {
    /// DATA manifest projected from the SAME exact expected rows. The native
    /// Host and actual original bank still decide whether any IO may occur.
    pub(crate) fn preparation_intents(expected: &ExpectedCommands) -> CargoResult<Vec<Intent>> {
        let mut intents = Vec::new();
        let mut bytes = 0usize;
        for row in expected.entries() {
            let namespace = row.private_outputs()?;
            for path in [
                namespace.root(),
                namespace.outputs(),
                namespace.incremental(),
            ] {
                push_intent(
                    &mut intents,
                    &mut bytes,
                    Intent::Directory {
                        path: path.as_os_str().as_bytes().to_vec(),
                    },
                )?;
            }
        }
        Ok(intents)
    }
    pub(crate) fn inspection_intents(&self) -> CargoResult<Vec<Intent>> {
        let mut intents = Vec::new();
        let mut bytes = 0usize;
        for directories in self.prepared.values() {
            for directory in [
                &directories.root,
                &directories.outputs,
                &directories.incremental,
            ] {
                push_intent(
                    &mut intents,
                    &mut bytes,
                    Intent::Directory {
                        path: directory.path().as_os_str().as_bytes().to_vec(),
                    },
                )?;
            }
        }
        let mut originals = Vec::new();
        for materialization in self.records.values() {
            for file in materialization.files.values() {
                if originals.iter().any(|known| Arc::ptr_eq(known, file)) {
                    continue;
                }
                originals.push(file.clone());
                push_intent(
                    &mut intents,
                    &mut bytes,
                    Intent::VerifyFile {
                        path: file.observation().path.as_os_str().as_bytes().to_vec(),
                    },
                )?;
            }
        }
        Ok(intents)
    }
    pub(crate) fn materialization_intents(
        &self,
        pending: &PendingUnit,
    ) -> CargoResult<Vec<Intent>> {
        ensure!(
            Arc::ptr_eq(&pending.domain, &self.domain),
            "materialization manifest belongs to another cache domain"
        );
        let mut intents = self.inspection_intents()?;
        let mut bytes = intents
            .iter()
            .flat_map(Intent::paths)
            .map(<[u8]>::len)
            .sum();
        for output in pending
            .outputs
            .iter()
            .filter(|output| super::output_observation::compiler_emit(&output.flavor).is_some())
        {
            push_intent(
                &mut intents,
                &mut bytes,
                Intent::CaptureFile {
                    path: output.path.as_os_str().as_bytes().to_vec(),
                },
            )?;
        }
        Ok(intents)
    }
    fn inspect_retained(&self, operation: &mut CoordinatorLocalOperation) -> CargoResult<()> {
        operation.require(&self.startup, &self.selected)?;
        for directories in self.prepared.values() {
            for directory in [
                &directories.root,
                &directories.outputs,
                &directories.incremental,
            ] {
                operation
                    .io(&self.startup, &self.selected)?
                    .verify_directory(directory)?;
            }
        }
        let mut originals = Vec::new();
        for actual in self.records.values() {
            for file in actual.files.values() {
                if originals.iter().any(|known| Arc::ptr_eq(known, file)) {
                    continue;
                }
                operation
                    .io(&self.startup, &self.selected)?
                    .verify_file(file)?;
                originals.push(file.clone());
            }
        }
        Ok(())
    }
    /// Continue only the SAME actual cache-domain owners. Equal root paths,
    /// evidence hashes or another Layout acquisition do not import a cache.
    pub(crate) fn require_inputs(
        &self,
        startup: &Arc<Startup>,
        master: &Arc<OriginalInputs>,
        selected: &Arc<HeldOutputRoot>,
        layout: &Arc<OriginalOutputLeases>,
    ) -> CargoResult<()> {
        ensure!(
            Arc::ptr_eq(&self.startup, startup)
                && Arc::ptr_eq(&self.original, master)
                && Arc::ptr_eq(&self.selected, selected)
                && Arc::ptr_eq(&self.layout, layout),
            "continued dependency ledger belongs to another original cache domain"
        );
        self.validate_domain()
    }
    pub(crate) fn new(
        startup: Arc<Startup>,
        original: Arc<OriginalInputs>,
        selected: Arc<HeldOutputRoot>,
        layout: Arc<OriginalOutputLeases>,
        expected: &ExpectedCommands,
        output_root: &Path,
        deadline: Instant,
        operation: &mut CoordinatorLocalOperation,
    ) -> CargoResult<Self> {
        operation.require(&startup, &selected)?;
        ensure!(
            selected.path() == output_root,
            "dependency custody requires the SAME selected held output root"
        );
        expected.validate()?;
        let mut ledger = Self {
            startup,
            original,
            selected,
            layout,
            domain: Arc::new(()),
            records: BTreeMap::new(),
            history: Vec::new(),
            prepared: BTreeMap::new(),
            attempts: BTreeMap::new(),
            retired: BTreeSet::new(),
            failed_epochs: BTreeSet::new(),
            active: Arc::new(Mutex::new(BTreeSet::new())),
            poisoned: Arc::new(AtomicBool::new(false)),
            retained: 0,
            deadline,
        };
        ledger.validate_domain()?;
        ledger.prepare_graph(expected, operation)?;
        Ok(ledger)
    }
    /// Actual parent-only preparation before GO, including new feature units
    /// in a later epoch. Unowned existing final directories refuse; they are
    /// never imported as a cache, retired producer or writable namespace.
    pub(crate) fn prepare_graph(
        &mut self,
        expected: &ExpectedCommands,
        operation: &mut CoordinatorLocalOperation,
    ) -> CargoResult<()> {
        operation.require(&self.startup, &self.selected)?;
        ensure!(
            matches!(&operation.request().operation, Operation::Begin(begin) if begin.kind == Kind::PrepareOutputs && operation.request().key.coordinator == expected.coordinator_attempt()),
            "private graph preparation lacks SAME native coordinator-local admission"
        );
        self.validate_domain()?;
        expected.validate()?;
        ensure!(
            expected.entries().iter().all(|row| !self
                .selected
                .path()
                .starts_with(row.package_root())
                && !row.package_root().starts_with(self.selected.path())),
            "private selected output root overlaps resolved original package source"
        );
        for row in expected.entries() {
            let namespace = row.private_outputs()?;
            ensure!(
                namespace.root().starts_with(self.selected.path())
                    && namespace.root() != self.selected.path(),
                "private namespace escapes SAME selected original output root"
            );
            if let Some(original) = self.prepared.get(row.key()) {
                ensure!(
                    original.namespace.root() == namespace.root(),
                    "prepared unit namespace differs from current exact row"
                );
                for directory in [&original.root, &original.outputs, &original.incremental] {
                    operation
                        .io(&self.startup, &self.selected)?
                        .verify_directory(directory)?;
                }
                original.validate(&self.selected, self.deadline)?;
                continue;
            }
            ensure!(
                self.prepared.len() < MAX_PRODUCERS,
                "prepared native namespace population exceeds finite bound"
            );
            let bytes = namespace
                .retained_bytes()
                .and_then(|bytes| bytes.checked_add(row.key().retained_bytes()?))
                .and_then(|bytes| bytes.checked_add(std::mem::size_of::<UnitDirectories>() + 1024))
                .context("private directory retention size overflow")?;
            ensure!(
                self.retained
                    .checked_add(bytes)
                    .is_some_and(|n| n <= MAX_RETAINED),
                "private output directory retention exceeds finite byte bound"
            );
            let root = operation
                .io(&self.startup, &self.selected)?
                .prepare_directory(namespace.root())?;
            let outputs = operation
                .io(&self.startup, &self.selected)?
                .prepare_directory(namespace.outputs())?;
            let incremental = operation
                .io(&self.startup, &self.selected)?
                .prepare_directory(namespace.incremental())?;
            let directories = Arc::new(UnitDirectories {
                namespace: namespace.clone(),
                root,
                outputs,
                incremental,
            });
            directories.validate(&self.selected, self.deadline)?;
            self.prepared.insert(row.key().clone(), directories);
            self.retained += bytes;
        }
        self.validate_domain()
    }
    fn validate_domain(&self) -> CargoResult<()> {
        ensure!(
            !self.poisoned.load(Ordering::Acquire) && Instant::now() < self.deadline,
            "dependency cache domain is poisoned or expired"
        );
        ensure!(
            self.startup.original_root
                && self.startup.candidate.is_none()
                && self.startup.workload_bank.is_some()
                && self.startup.descriptor_budget.is_some()
                && self
                    .startup
                    .workload_evidence
                    .as_ref()
                    .is_some_and(|actual| Arc::ptr_eq(actual, &self.original.evidence)),
            "dependency cache domain lost SAME original Root/evidence/budget"
        );
        self.original.validate()?;
        self.selected.validate(self.deadline)?;
        self.layout.validate(self.selected.path())
    }
    pub(crate) fn begin(
        &mut self,
        expected: &ExpectedCommands,
        command: &CommandSpec,
        sources: &[Arc<AdmittedPackageSource>],
        operation: &mut CoordinatorLocalOperation,
    ) -> CargoResult<PendingUnit> {
        self.inspect_retained(operation)?;
        self.validate_domain()?;
        let selected = expected.require(command)?;
        let key = selected.key().clone();
        let epoch = expected.member_binding();
        ensure!(
            self.attempts.contains_key(&epoch) || self.attempts.len() < MAX_EPOCHS,
            "dependency cache exceeds finite member epoch bound"
        );
        require_unattempted(&self.attempts, epoch, &key)?;
        ensure!(
            self.attempts.values().map(BTreeSet::len).sum::<usize>() < MAX_ATTEMPTS,
            "dependency domain exceeds finite actual attempt history bound"
        );
        let attempt_bytes = key
            .retained_bytes()
            .and_then(|bytes| bytes.checked_add(std::mem::size_of::<UnitKey>() + 512))
            .context("dependency attempt history size overflow")?;
        ensure!(
            self.retained
                .checked_add(attempt_bytes)
                .is_some_and(|bytes| bytes <= MAX_RETAINED),
            "dependency attempt history exceeds finite retained byte bound"
        );
        let source = selected_source(selected, sources, self.deadline)?;
        let namespace = selected.private_outputs()?;
        ensure!(
            namespace.root().starts_with(self.selected.path())
                && namespace.root() != self.selected.path()
                && sources
                    .iter()
                    .all(|source| !namespace.root().starts_with(source.path())
                        && !source.path().starts_with(namespace.root())),
            "private unit namespace overlaps original source or escapes selected output"
        );
        if let Some(previous) = self.records.get(&key) {
            ensure!(
                previous.readers.load(Ordering::Acquire) == 0,
                "cannot replace a dependency used by an actual consumer"
            );
        }
        let mut parents = Vec::new();
        let mut files = Vec::new();
        let mut readers = Vec::new();
        let mut validated = Vec::new();
        let mut leased = Vec::new();
        for predecessor in selected.predecessors() {
            let parent = self
                .records
                .get(&predecessor.key)
                .context(
                    "dependency has no retained genuine retired producer; warm owner unavailable",
                )?
                .clone();
            self.validate_record(&parent, expected, sources, &mut Vec::new(), &mut validated)?;
            for &index in &predecessor.outputs {
                retain_file(&parent, index, &mut files)?;
            }
            self.lease_closure(&parent, expected, &mut leased, &mut files, &mut readers)?;
            parents.push(parent);
        }
        let directory = self
            .prepared
            .get(&key)
            .context("actual parent did not prepare this exact private unit before GO")?
            .clone();
        ensure!(
            directory.namespace.root() == namespace.root(),
            "native unit directory differs from expected unit namespace"
        );
        directory.validate(&self.selected, self.deadline)?;
        let mut active = self
            .active
            .lock()
            .map_err(|_| anyhow::anyhow!("dependency attempt state poisoned"))?;
        ensure!(
            active.insert(key.clone()),
            "expected producer is already active"
        );
        self.attempts.entry(epoch).or_default().insert(key.clone());
        self.retained += attempt_bytes;
        Ok(PendingUnit {
            startup: self.startup.clone(),
            deadline: self.deadline,
            compiler_inputs_issued: AtomicBool::new(false),
            domain: self.domain.clone(),
            key,
            command: command.clone(),
            outputs: selected.outputs.clone(),
            directory,
            source,
            parents,
            dependencies: DependencyLease {
                files,
                _readers: readers,
            },
            poisoned: self.poisoned.clone(),
            active: self.active.clone(),
            settled: false,
            coordinator_attempt: expected.coordinator_attempt(),
            issued: Instant::now(),
            _layout: self.layout.clone(),
            _selected: self.selected.clone(),
            _master: self.original.clone(),
        })
    }
    fn lease_closure(
        &self,
        actual: &Arc<Materialization>,
        expected: &ExpectedCommands,
        leased: &mut Vec<Arc<Materialization>>,
        files: &mut Vec<DependencyFile>,
        readers: &mut Vec<Reader>,
    ) -> CargoResult<()> {
        if leased.iter().any(|known| Arc::ptr_eq(known, actual)) {
            return Ok(());
        }
        ensure!(
            leased.len() < MAX_PRODUCERS,
            "dependency closure exceeds finite producer bound"
        );
        leased.push(actual.clone());
        readers.push(Reader::new(actual.readers.clone()));
        let current = expected.entry(&actual.key)?;
        // validate_record already checked this exact predecessor population.
        for (edge, parent) in current.predecessors().iter().zip(&actual.parents) {
            for &index in &edge.outputs {
                retain_file(parent, index, files)?;
            }
            self.lease_closure(parent, expected, leased, files, readers)?;
        }
        Ok(())
    }
    fn validate_record(
        &self,
        actual: &Arc<Materialization>,
        expected: &ExpectedCommands,
        sources: &[Arc<AdmittedPackageSource>],
        visiting: &mut Vec<Arc<Materialization>>,
        validated: &mut Vec<Arc<Materialization>>,
    ) -> CargoResult<()> {
        if validated.iter().any(|known| Arc::ptr_eq(known, actual)) {
            return Ok(());
        }
        ensure!(
            !visiting.iter().any(|known| Arc::ptr_eq(known, actual)),
            "cycle in retained actual dependency closure"
        );
        ensure!(
            !self
                .active
                .lock()
                .map_err(|_| anyhow::anyhow!("dependency state poisoned"))?
                .contains(&actual.key),
            "dependency producer is still active"
        );
        visiting.push(actual.clone());
        let current = expected.entry(&actual.key)?;
        actual.directory.validate(&self.selected, self.deadline)?;
        ensure!(
            current.command() == &actual.command
                && same_outputs(&current.outputs, &actual.outputs)
                && current.private_outputs()?.root() == actual.directory.namespace.root(),
            "retained dependency command/output semantics changed"
        );
        let source = selected_source(current, sources, self.deadline)?;
        actual.source.validate(self.deadline)?;
        ensure!(
            source.content_digest() == actual.source.content_digest(),
            "retained dependency package source changed"
        );
        actual.native.require_compiler_materialization(
            &self.startup,
            &actual.command,
            actual.coordinator_attempt,
            actual.issued,
        )?;
        for file in actual.files.values() {
            file.validate(self.deadline)?;
        }
        ensure!(
            current.predecessors().len() == actual.parents.len(),
            "retained dependency closure population changed"
        );
        for (current, parent) in current.predecessors().iter().zip(&actual.parents) {
            ensure!(
                current.key == parent.key,
                "retained actual predecessor was replaced/reordered"
            );
            self.validate_record(parent, expected, sources, visiting, validated)?;
        }
        visiting.pop();
        validated.push(actual.clone());
        Ok(())
    }
    /// Validate a fully Fresh epoch without asking a compiler to run. Every
    /// current row must already have an actual retained cold producer; an
    /// unowned Fresh/cache report cannot fill a missing row or output slot.
    pub(crate) fn require_complete(
        &self,
        expected: &ExpectedCommands,
        sources: &[Arc<AdmittedPackageSource>],
        operation: &mut CoordinatorLocalOperation,
    ) -> CargoResult<()> {
        ensure!(
            !self.failed_epochs.contains(&expected.coordinator_attempt()),
            "current native coordinator epoch contains a known failed compiler"
        );
        self.inspect_retained(operation)?;
        self.validate_domain()?;
        expected.validate()?;
        let mut validated = Vec::new();
        for row in expected.entries() {
            let actual = self
                .records
                .get(row.key())
                .context("current graph has no retained genuine retired producer")?;
            self.validate_record(actual, expected, sources, &mut Vec::new(), &mut validated)?;
        }
        self.validate_domain()
    }
    fn graph_publications<'a>(
        &self,
        expected: &ExpectedCommands,
        published: &'a [PublishedUnit],
    ) -> CargoResult<Vec<&'a PublishedUnit>> {
        ensure!(
            !self.failed_epochs.contains(&expected.coordinator_attempt()),
            "failed native coordinator epoch cannot close from earlier materializations"
        );
        ensure!(
            published.len() == expected.entries().len() && published.len() <= MAX_PRODUCERS,
            "whole graph has missing/extra publication owners"
        );
        let mut current: Vec<&PublishedUnit> = Vec::new();
        current.try_reserve_exact(published.len())?;
        for row in expected.entries() {
            let selection = row.publication_selection()?;
            let mut matches = published
                .iter()
                .filter(|actual| actual.pending.selection == selection);
            let actual=matches.next().context("exact graph unit has no actual acknowledged publication (including empty canonical sets)")?;
            ensure!(
                matches.next().is_none(),
                "graph unit has duplicate publication owners"
            );
            ensure!(
                !current.iter().any(|known| std::ptr::eq(*known, actual)),
                "one publication owner cannot satisfy two graph rows"
            );
            let producer = self
                .records
                .get(row.key())
                .context("published unit lost current private producer")?;
            ensure!(
                actual.acknowledged
                    && Arc::ptr_eq(&actual.pending.domain, &self.domain)
                    && Arc::ptr_eq(&actual.pending.producer, producer)
                    && Arc::ptr_eq(&actual.pending.startup, &self.startup)
                    && Arc::ptr_eq(&actual.pending.master, &self.original)
                    && Arc::ptr_eq(&actual.pending.selected, &self.selected)
                    && Arc::ptr_eq(&actual.pending.layout, &self.layout)
                    && actual.pending.key.coordinator == expected.coordinator_attempt()
                    && actual.native.begin().key == actual.pending.key,
                "publication is unacknowledged, stale, earlier-member or from another actual producer/domain"
            );
            actual.native.require_success()?;
            ensure!(
                actual.pending.files.len() == selection.destinations.len(),
                "publication lost copied originals"
            );
            let mut paths = actual
                .pending
                .files
                .iter()
                .map(|file| file.observation().path.as_os_str().as_bytes().to_vec())
                .collect::<Vec<_>>();
            paths.sort();
            ensure!(
                paths == selection.destinations,
                "publication originals differ from complete expected canonical set"
            );
            current.push(actual);
        }
        Ok(current)
    }
    pub(crate) fn graph_intents(
        &self,
        expected: &ExpectedCommands,
        published: &[PublishedUnit],
    ) -> CargoResult<Vec<Intent>> {
        let publications = self.graph_publications(expected, published)?;
        let mut intents = self.inspection_intents()?;
        let mut bytes = intents
            .iter()
            .flat_map(Intent::paths)
            .map(<[u8]>::len)
            .sum();
        let mut unique = BTreeSet::new();
        for actual in publications {
            for file in &actual.pending.files {
                let path = file.observation().path.as_os_str().as_bytes().to_vec();
                ensure!(
                    unique.insert(path.clone()),
                    "current graph canonical originals alias another unit"
                );
                push_intent(&mut intents, &mut bytes, Intent::VerifyFile { path })?;
            }
        }
        // Loader capture uses this SAME already bounded native manifest.
        // Existing verification intents can be reused by a read-only capture.
        for program in expected.entries().iter().filter_map(|row| row.program()) {
            ensure!(intents.iter().any(|intent|matches!(intent,Intent::VerifyFile{path}if path==program.path().as_os_str().as_bytes())),
                "expected executable has no acknowledged canonical original");
            for root in program.runtime_roots() {
                if !intents.iter().any(|intent|matches!(intent,Intent::Directory{path}if path==root.as_os_str().as_bytes())) {
                    push_intent(&mut intents,&mut bytes,Intent::Directory {path:root.as_os_str().as_bytes().to_vec()})?;
                }
            }
        }
        Ok(intents)
    }
    pub(crate) fn inspect_graph(
        &self,
        expected: &ExpectedCommands,
        sources: &[Arc<AdmittedPackageSource>],
        published: &[PublishedUnit],
        operation: &mut CoordinatorLocalOperation,
    ) -> CargoResult<PendingGraphClosure> {
        operation.require(&self.startup, &self.selected)?;
        ensure!(
            operation.request().key.coordinator == expected.coordinator_attempt()
                && matches!(&operation.request().operation,Operation::Begin(begin)if begin.kind==Kind::PrepareOutputs),
            "graph closure lacks SAME live coordinator/native inspection"
        );
        self.require_complete(expected, sources, operation)?;
        let publications = self.graph_publications(expected, published)?;
        let mut canonical = Vec::new();
        let mut selections = Vec::new();
        let mut unique = BTreeSet::new();
        selections.try_reserve_exact(publications.len())?;
        for publication in publications {
            for file in &publication.pending.files {
                ensure!(
                    unique.insert(file.observation().path.clone()),
                    "graph copied canonical destinations overlap"
                );
                operation
                    .io(&self.startup, &self.selected)?
                    .verify_file(file)?;
                canonical.try_reserve(1)?;
                canonical.push(file.clone());
            }
            selections.push(publication.pending.selection.clone());
        }
        ensure!(
            self.active
                .lock()
                .map_err(|_| anyhow::anyhow!("dependency state poisoned"))?
                .is_empty(),
            "graph closure has an unresolved logical compiler attempt"
        );
        let mut records = Vec::new();
        records.try_reserve_exact(expected.entries().len())?;
        for row in expected.entries() {
            records.push(
                self.records
                    .get(row.key())
                    .context("graph closure lost current actual producer")?
                    .clone(),
            );
        }
        let mut programs = Vec::new();
        for row in expected.entries() {
            let Some(program) = row.program() else {
                continue;
            };
            let selection = row.publication_selection()?;
            let publication = published
                .iter()
                .find(|publication| publication.selection() == &selection)
                .context("published executable has no SAME actual unit publication")?;
            let producer = self
                .records
                .get(row.key())
                .context("published executable lost actual compiler materialization")?;
            ensure!(
                Arc::ptr_eq(producer, &publication.pending.producer),
                "published executable grafted another producer"
            );
            let mut files = publication
                .files()
                .iter()
                .filter(|file| file.observation().path == program.path());
            let original = files
                .next()
                .context("expected executable omitted its canonical copied original")?
                .clone();
            ensure!(
                files.next().is_none(),
                "published executable has ambiguous canonical originals"
            );
            let image = operation
                .io(&self.startup, &self.selected)?
                .capture_program(
                    self.original.sdk().clone(),
                    &original,
                    program.runtime_roots(),
                )?;
            programs.push(PendingProgram {
                producer: producer.clone(),
                original,
                image,
                runtime_roots: program.runtime_roots().to_vec(),
            });
        }
        Ok(PendingGraphClosure {
            key: operation.request().key,
            member_binding: expected.member_binding(),
            records,
            canonical,
            selections,
            startup: self.startup.clone(),
            master: self.original.clone(),
            selected: self.selected.clone(),
            layout: self.layout.clone(),
            programs,
        })
    }
    fn collect_publications<'a>(
        &self,
        rows: impl Iterator<Item = &'a ExpectedUnitCommand>,
    ) -> CargoResult<Vec<Publication>> {
        let mut publications = Vec::new();
        let mut destinations = BTreeSet::new();
        for row in rows {
            let producer = self
                .records
                .get(row.key())
                .context("publication lacks SAME actual retired producer")?;
            for (index, output) in row.outputs.iter().enumerate() {
                let paths = output
                    .hardlink
                    .iter()
                    .chain(output.export_path.iter())
                    .cloned()
                    .collect::<Vec<_>>();
                if paths.is_empty() {
                    continue;
                }
                ensure!(
                    publications.len() < MAX_PRODUCERS,
                    "native publication input population exceeds finite bound"
                );
                for path in &paths {
                    ensure!(
                        path.starts_with(self.selected.path())
                            && path != self.selected.path()
                            && !path.starts_with(producer.directory.namespace.root())
                            && destinations.insert(path.clone()),
                        "native publication destination escapes selected root or aliases another slot"
                    );
                }
                let original = producer.files.get(&index)
                    .context("publication slot has no actual retired compiler file (bundle publication unsupported)")?.clone();
                let publication = Publication {
                    producer: producer.clone(),
                    original,
                    destinations: paths,
                    _reader: Reader::new(producer.readers.clone()),
                    layout: self.layout.clone(),
                    selected: self.selected.clone(),
                    master: self.original.clone(),
                    startup: self.startup.clone(),
                    deadline: self.deadline,
                };
                publication.validate(self.deadline)?;
                publications.push(publication);
            }
        }
        self.validate_domain()?;
        Ok(publications)
    }
    pub(crate) fn publication_intents(
        &self,
        expected: &ExpectedCommands,
        selection: &PublicationSelection,
    ) -> CargoResult<Vec<Intent>> {
        let row = expected.require_publication(selection)?;
        let mut intents = self.inspection_intents()?;
        let mut bytes = intents
            .iter()
            .flat_map(Intent::paths)
            .map(<[u8]>::len)
            .sum();
        for output in row.outputs.iter() {
            for destination in output.hardlink.iter().chain(output.export_path.iter()) {
                push_intent(
                    &mut intents,
                    &mut bytes,
                    Intent::PublishFile {
                        source: output.path.as_os_str().as_bytes().to_vec(),
                        destination: destination.as_os_str().as_bytes().to_vec(),
                    },
                )?;
            }
        }
        Ok(intents)
    }
    /// Publish exactly one requested Unit, including a genuine Fresh reuse.
    /// All current predecessor/native/source semantics are rechecked under
    /// the actual second-unit operation before any original-FD copy.
    pub(crate) fn publish_unit(
        &self,
        expected: &ExpectedCommands,
        selection: &PublicationSelection,
        sources: &[Arc<AdmittedPackageSource>],
        operation: &mut CoordinatorLocalOperation,
    ) -> CargoResult<PendingPublication> {
        operation.require(&self.startup, &self.selected)?;
        ensure!(
            operation.request().key.coordinator == expected.coordinator_attempt()
                && matches!(&operation.request().operation,Operation::Begin(begin)if matches!(begin.kind,Kind::PublishFresh|Kind::MaterializeAndPublish)),
            "publication lacks SAME current native coordinator/local operation"
        );
        self.inspect_retained(operation)?;
        self.validate_domain()?;
        let row = expected.require_publication(selection)?;
        let producer = self
            .records
            .get(row.key())
            .context("publication has no retained genuine retired unit")?;
        self.validate_record(
            producer,
            expected,
            sources,
            &mut Vec::new(),
            &mut Vec::new(),
        )?;
        let publications = self.collect_publications(std::iter::once(row))?;
        let mut files = Vec::new();
        for publication in &publications {
            publication.validate(self.deadline)?;
            for destination in publication.destinations() {
                let copied = operation
                    .io(&self.startup, &self.selected)?
                    .publish_file(publication.original(), destination)?;
                ensure!(
                    copied.observation().path == *destination
                        && copied.observation().sha256
                            == publication.original().observation().sha256
                        && copied.observation().bytes == publication.original().observation().bytes
                        && (copied.observation().device, copied.observation().inode)
                            != (
                                publication.original().observation().device,
                                publication.original().observation().inode
                            ),
                    "publication did not retain an independent exact copy"
                );
                ensure!(
                    files.len() < MAX_PRODUCERS,
                    "publication copied set exceeds finite bound"
                );
                files.push(copied);
            }
        }
        let mut actual = files
            .iter()
            .map(|file| file.observation().path.as_os_str().as_bytes().to_vec())
            .collect::<Vec<_>>();
        actual.sort();
        ensure!(
            actual == selection.destinations,
            "publication multi-file set is incomplete or reordered"
        );
        for file in &files {
            file.validate(self.deadline)?;
        }
        for source in &publications {
            source.validate(self.deadline)?;
        }
        self.validate_domain()?;
        operation.require(&self.startup, &self.selected)?;
        Ok(PendingPublication {
            domain: self.domain.clone(),
            producer: producer.clone(),
            key: operation.request().key,
            selection: selection.clone(),
            sources: publications,
            files,
            layout: self.layout.clone(),
            selected: self.selected.clone(),
            master: self.original.clone(),
            startup: self.startup.clone(),
        })
    }
    pub(crate) fn finish(
        &mut self,
        mut pending: PendingUnit,
        native: Arc<CoordinatorCompilerCapture>,
        operation: &mut CoordinatorLocalOperation,
    ) -> CargoResult<()> {
        operation.require(&self.startup, &self.selected)?;
        ensure!(
            matches!(&operation.request().operation, Operation::Begin(begin) if begin.kind == Kind::MaterializeAndPublish && begin.producer == native.native_status().map(|status|status.member_attempt) && operation.request().key.coordinator == pending.coordinator_attempt),
            "materialization lacks SAME native producer/local operation"
        );
        self.inspect_retained(operation)?;
        ensure!(
            Arc::ptr_eq(&pending.domain, &self.domain),
            "producer belongs to another cache domain"
        );
        // A known failed/BeforeRequest capture settles only this logical
        // attempt. It cannot seed a materialization or settle a native loan.
        pending.settled = true;
        self.validate_domain()?;
        native.require_compiler_read_retirement(
            &self.startup,
            &pending.command,
            pending.coordinator_attempt,
            pending.issued,
        )?;
        let retired = native
            .native_status()
            .context("read-retired compiler lost SAME actual native terminal")?
            .member_attempt;
        ensure!(
            self.retired.len() < MAX_ATTEMPTS && self.retired.insert(retired),
            "actual native producer was already retired/consumed by this ledger"
        );
        pending.dependencies.retire();
        native.require_compiler_materialization(
            &self.startup,
            &pending.command,
            pending.coordinator_attempt,
            pending.issued,
        )?;
        pending.directory.validate(&self.selected, self.deadline)?;
        let coverage =
            observed_outputs(&pending.outputs, &pending.command, &native.capture().stderr)?;
        pending.source.validate(self.deadline)?;
        pending.dependencies.validate(self.deadline)?;
        ensure!(
            self.history.len() + self.records.len() < MAX_PRODUCERS,
            "dependency domain exceeds finite retained producer bound"
        );
        let bytes = native
            .retained_bytes()
            .context("retained dependency capture size overflow")?
            .checked_add(super::candidate_runner::command_demand(&pending.command)?)
            .and_then(|bytes| bytes.checked_add(coverage.retained_bytes()?))
            .and_then(|bytes| {
                bytes.checked_add(output_bytes(&pending.outputs, pending.outputs.capacity())?)
            })
            .and_then(|bytes| bytes.checked_add(pending.key.retained_bytes()?.checked_mul(2)?))
            .and_then(|bytes| bytes.checked_add(std::mem::size_of::<Materialization>() + 1024))
            .and_then(|bytes| bytes.checked_add(pending.parents.len().checked_mul(64)?))
            .context("retained dependency materialization size overflow")?;
        ensure!(
            self.retained
                .checked_add(bytes)
                .is_some_and(|n| n <= MAX_RETAINED),
            "dependency domain exceeds finite retained capture bound"
        );
        let mut files = BTreeMap::new();
        for (index, output) in pending.outputs.iter().enumerate() {
            if super::output_observation::compiler_emit(&output.flavor).is_some() {
                let original = operation
                    .io(&self.startup, &self.selected)?
                    .capture_file(&output.path)?;
                files.insert(index, original);
            }
        }
        pending.source.validate(self.deadline)?;
        for file in files.values() {
            file.validate(self.deadline)?;
        }
        let mut validated = Vec::new();
        for parent in &pending.parents {
            self.validate_held(parent, &mut validated)?;
        }
        self.validate_domain()?;
        pending.directory.validate(&self.selected, self.deadline)?;
        let materialization = Arc::new(Materialization {
            key: pending.key.clone(),
            command: pending.command.clone(),
            outputs: pending.outputs.clone(),
            directory: pending.directory.clone(),
            files,
            source: pending.source.clone(),
            parents: pending.parents.clone(),
            readers: Arc::new(AtomicUsize::new(0)),
            native,
            _coverage: coverage,
            coordinator_attempt: pending.coordinator_attempt,
            issued: pending.issued,
            _layout: pending._layout.clone(),
            _selected: pending._selected.clone(),
            _master: pending._master.clone(),
        });
        if let Some(previous) = self.records.insert(pending.key.clone(), materialization) {
            self.history.push(previous);
        }
        self.retained += bytes;
        Ok(())
    }
    /// A genuine failed compiler has stopped reading even when it cannot
    /// materialize an output. Preserve unrelated actual producers for a new
    /// admitted epoch; THIS epoch can never close from stale earlier records.
    pub(crate) fn retire_failed(
        &mut self,
        mut pending: PendingUnit,
        native: &Arc<CoordinatorCompilerCapture>,
    ) -> CargoResult<()> {
        ensure!(
            Arc::ptr_eq(&pending.domain, &self.domain),
            "failed producer belongs to another cache domain"
        );
        native.require_compiler_read_retirement(
            &self.startup,
            &pending.command,
            pending.coordinator_attempt,
            pending.issued,
        )?;
        let frame = native
            .native_status()
            .context("read-retired failed compiler lost native terminal")?;
        ensure!(
            !matches!(
                frame.status,
                trust_resource_controller::Status::Finished {
                    outcome: trust_resource_controller::Outcome::Exit(0),
                    cause: trust_resource_controller::CompletionCause::Exited,
                    ..
                }
            ),
            "successful compiler cannot become a failed epoch marker"
        );
        pending.dependencies.retire();
        pending.settled = true;
        let result = (|| -> CargoResult<()> {
            ensure!(
                self.retired.len() < MAX_ATTEMPTS && self.retired.insert(frame.member_attempt),
                "failed native attempt was already consumed or exceeds finite history"
            );
            if !self.failed_epochs.contains(&pending.coordinator_attempt) {
                ensure!(
                    self.failed_epochs.len() < MAX_EPOCHS,
                    "failed native epoch history exceeds finite bound"
                );
                let bytes = 16usize
                    .checked_mul(11)
                    .and_then(|n| n.checked_add(128))
                    .context("failed epoch retention overflow")?;
                ensure!(
                    self.retained
                        .checked_add(bytes)
                        .is_some_and(|n| n <= MAX_RETAINED),
                    "failed epoch exceeds retained domain quota"
                );
                self.failed_epochs.insert(pending.coordinator_attempt);
                self.retained += bytes;
            }
            Ok(())
        })();
        if result.is_err() {
            self.poisoned.store(true, Ordering::Release);
        }
        result
    }
    fn validate_held(
        &self,
        actual: &Arc<Materialization>,
        validated: &mut Vec<Arc<Materialization>>,
    ) -> CargoResult<()> {
        if validated.iter().any(|known| Arc::ptr_eq(known, actual)) {
            return Ok(());
        }
        actual.native.require_compiler_materialization(
            &self.startup,
            &actual.command,
            actual.coordinator_attempt,
            actual.issued,
        )?;
        actual.source.validate(self.deadline)?;
        actual.directory.validate(&self.selected, self.deadline)?;
        for file in actual.files.values() {
            file.validate(self.deadline)?;
        }
        for parent in &actual.parents {
            self.validate_held(parent, validated)?;
        }
        validated.push(actual.clone());
        Ok(())
    }
}
fn push_intent(intents: &mut Vec<Intent>, bytes: &mut usize, intent: Intent) -> CargoResult<()> {
    ensure!(
        intents.len() < trust_resource_controller::workload::host::publication::MAX_INTENTS,
        "local IO manifest exceeds finite population"
    );
    let added = intent.paths().map(<[u8]>::len).sum::<usize>();
    ensure!(
        bytes.checked_add(added).is_some_and(
            |n| n <= trust_resource_controller::workload::host::publication::MAX_INTENT_BYTES
        ),
        "local IO manifest exceeds finite byte bound"
    );
    intents.try_reserve(1)?;
    *bytes = bytes
        .checked_add(added)
        .context("local IO manifest byte count overflow")?;
    intents.push(intent);
    Ok(())
}
fn retain_file(
    producer: &Arc<Materialization>,
    index: usize,
    files: &mut Vec<DependencyFile>,
) -> CargoResult<()> {
    let original = producer
        .files
        .get(&index)
        .context("actual predecessor did not materialize selected extern OutputFile")?;
    if !files
        .iter()
        .any(|known| Arc::ptr_eq(&known.original, original))
    {
        ensure!(
            files.len() < MAX_PRODUCERS,
            "dependency closure exceeds finite selected file bound"
        );
        files.push(DependencyFile {
            original: original.clone(),
            producer: producer
                .native
                .native_status()
                .context("retained producer lost actual native terminal")?
                .member_attempt,
        });
    }
    Ok(())
}
// DATA coverage only, used by finish solely after SAME actual native success.
// --version/redirected emits cannot materialize stale files left at plan paths.
fn observed_outputs(
    outputs: &[OutputFile],
    command: &CommandSpec,
    stderr: &[u8],
) -> CargoResult<Seal> {
    let mut observer = Observer::new(
        super::output_observation::expected_outputs(outputs),
        Path::new(std::ffi::OsStr::from_bytes(&command.cwd)).to_path_buf(),
    );
    for line in std::str::from_utf8(stderr)?
        .lines()
        .filter(|line| !line.is_empty())
    {
        observer.observe(line);
    }
    observer
        .finish()
        .context("actual compiler did not report complete expected output inventory")
}
fn output_bytes(outputs: &[OutputFile], capacity: usize) -> Option<usize> {
    let mut bytes = capacity.checked_mul(std::mem::size_of::<OutputFile>() + 64)?;
    for output in outputs {
        for path in std::iter::once(&output.path)
            .chain(output.hardlink.iter())
            .chain(output.export_path.iter())
        {
            bytes = bytes.checked_add(path.capacity())?;
        }
    }
    Some(bytes)
}
fn require_unattempted(
    attempts: &BTreeMap<[u8; 32], BTreeSet<UnitKey>>,
    epoch: [u8; 32],
    key: &UnitKey,
) -> CargoResult<()> {
    ensure!(
        !attempts
            .get(&epoch)
            .is_some_and(|attempted| attempted.contains(key)),
        "duplicate expected producer in SAME coordinator member"
    );
    Ok(())
}
fn selected_source(
    expected: &ExpectedUnitCommand,
    sources: &[Arc<AdmittedPackageSource>],
    deadline: Instant,
) -> CargoResult<Arc<AdmittedPackageSource>> {
    let mut selected = sources
        .iter()
        .filter(|source| source.path() == expected.package_root());
    let source = selected
        .next()
        .context("expected unit has no actual original package source")?;
    ensure!(
        selected.next().is_none(),
        "expected unit has ambiguous actual source owners"
    );
    source.validate(deadline)?;
    Ok(source.clone())
}
fn same_outputs(left: &[OutputFile], right: &[OutputFile]) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(a, b)| {
            a.path == b.path
                && a.hardlink == b.hardlink
                && a.export_path == b.export_path
                && a.flavor == b.flavor
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    // Equality/path observations only, never a materialization, NativeCapture,
    // source/SDK/CPU owner, or valid-rmeta assertion.
    #[test]
    fn retired_consumer_does_not_stay_active_through_retained_reader_copies() {
        // Logical bookkeeping DATA only. In production only finish's SAME
        // native materialization barrier can retire these shared readers.
        let count = Arc::new(AtomicUsize::new(0));
        let original = Reader::new(count.clone());
        let retained = original.clone();
        assert_eq!(count.load(Ordering::Acquire), 1);
        original.retire();
        assert_eq!(count.load(Ordering::Acquire), 0);
        retained.retire();
        drop(original);
        drop(retained);
        assert_eq!(count.load(Ordering::Acquire), 0);
        let unresolved = Reader::new(count.clone());
        let last = unresolved.clone();
        drop(unresolved);
        assert_eq!(count.load(Ordering::Acquire), 1);
        drop(last);
        assert_eq!(count.load(Ordering::Acquire), 0);
    }
    #[test]
    fn completed_attempt_history_cannot_be_reset_by_another_attempt() {
        let key = super::super::candidate_commands::test_unit_key("equality-data");
        let mut attempts = BTreeMap::new();
        assert!(require_unattempted(&attempts, [1; 32], &key).is_ok());
        attempts
            .entry([1; 32])
            .or_insert_with(BTreeSet::new)
            .insert(key.clone());
        assert!(require_unattempted(&attempts, [1; 32], &key).is_err());
        assert!(require_unattempted(&attempts, [2; 32], &key).is_ok());
        attempts
            .entry([2; 32])
            .or_insert_with(BTreeSet::new)
            .insert(key.clone());
        assert!(require_unattempted(&attempts, [1; 32], &key).is_err());
    }
    #[test]
    fn output_relation_does_not_collapse_flavors_hardlinks_or_exports() {
        let output = || OutputFile {
            path: "/output/lib.rmeta".into(),
            hardlink: Some("/output/published.rmeta".into()),
            export_path: None,
            flavor: super::super::FileFlavor::Rmeta,
        };
        for alteration in 0..4 {
            let original = output();
            let mut changed = output();
            match alteration {
                0 => changed.path = "/another/lib.rmeta".into(),
                1 => changed.hardlink = None,
                2 => changed.export_path = Some("/export/lib.rmeta".into()),
                3 => changed.flavor = super::super::FileFlavor::Normal,
                _ => unreachable!(),
            }
            assert!(
                !same_outputs(&[original], &[changed]),
                "alteration {alteration}"
            );
        }
    }
    #[test]
    fn output_coverage_cannot_be_seeded_by_stale_paths_or_partial_reports() {
        let output = |name: &str, flavor| OutputFile {
            path: Path::new("/output").join(name),
            hardlink: Some(Path::new("/output/published").join(name)),
            export_path: None,
            flavor,
        };
        let outputs = [
            output("lib.rmeta", super::super::FileFlavor::Rmeta),
            output("lib.rlib", super::super::FileFlavor::Linkable),
            output("bin", super::super::FileFlavor::Normal),
            output("debug", super::super::FileFlavor::DebugInfo),
        ];
        let command = CommandSpec {
            program: b"/compiler".to_vec(),
            arg0: None,
            args: Vec::new(),
            cwd: b"/package".to_vec(),
            environment: Vec::new(),
        };
        let report = |path: &str, emit: &str| {
            serde_json::json!({
                "$message_type": "artifact", "artifact": path, "emit": emit
            })
            .to_string()
        };
        let metadata = report("/output/lib.rmeta", "metadata");
        let library = report("/output/lib.rlib", "link");
        let binary = report("/output/bin", "link");
        let complete = format!("{metadata}\n{library}\n{binary}\n");
        assert_eq!(
            super::super::output_observation::expected_outputs(&outputs).len(),
            3
        );
        assert!(observed_outputs(&outputs, &command, complete.as_bytes()).is_ok());
        for rejected in [
            String::new(),
            "compiler version 1.0\n".into(),
            format!("{metadata}\n{library}\n"),
            format!("{metadata}\n{library}\n{library}\n"),
            format!(
                "{metadata}\n{library}\n{}\n",
                report("/output/published/bin", "link")
            ),
            format!(
                "{metadata}\n{library}\n{}\n",
                report("/output/bin", "metadata")
            ),
            format!("{complete}{{malformed\n"),
        ] {
            assert!(
                observed_outputs(&outputs, &command, rejected.as_bytes()).is_err(),
                "{rejected}"
            );
        }
        assert!(observed_outputs(&outputs, &command, &[0xff]).is_err());
        // A complete DATA inventory alone never constructs Ledger,
        // Materialization, NativeCapture, or a valid-rmeta owner.
    }
}
