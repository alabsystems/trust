//! One fixed trusted Root-local IO scope from actual native admission.
//! No constructor decodes an observation into CPU/writer/SDK authority.
use std::os::unix::ffi::OsStrExt as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use std::time::Duration;

use trust_resource_provenance::program::produced::{HeldOutputRoot, PublicationExclusions};

use super::*;
use crate::descriptors::{
    AdmittedRootDirectory, AdmittedRootFile, DescriptorBudget, OriginalInputPermit,
};
use crate::workload::host::publication as wire;

pub(super) struct Life {
    request: Arc<wire::Request>,
    stage: AtomicU8,
}
/// Actual pre-request refusal or authenticated positive no-admission. It can
/// retire only the matching offered local reservation; it grants no capacity.
pub struct LocalNotAdmitted {
    request: Arc<wire::Request>,
    reason: String,
    busy: bool,
}
impl LocalNotAdmitted {
    pub fn request(&self) -> &wire::Request {
        &self.request
    }
    pub fn reason(&self) -> &str {
        &self.reason
    }
    pub fn busy(&self) -> bool {
        self.busy
    }
}
pub enum LocalAdmission {
    Ready(LocalIoScope),
    NotAdmitted(LocalNotAdmitted),
}

/// Only closed original-FD IO primitives are exposed. There is no arbitrary
/// callback, hosted Child/Status, public Boolean completion or FD extractor.
/// All writer/staging handles are lexical inside each primitive and close
/// before it returns. Returned originals are read-only DATA custody.
pub struct LocalIoScope {
    life: Arc<Life>,
    host: Arc<trust_resource_provenance::PinnedHelper>,
    selected: Arc<HeldOutputRoot>,
    budget: Arc<DescriptorBudget>,
    deadline: Instant,
    cancellation: Arc<AtomicBool>,
    used: Vec<bool>,
    bytes: u64,
    failure: Option<String>,
    finished: bool,
    exclusions: PublicationExclusions,
    _descriptors: Arc<OriginalInputPermit>,
}
pub struct LocalCompletion {
    life: Arc<Life>,
    selected: Arc<HeldOutputRoot>,
    budget: Arc<DescriptorBudget>,
    outcome: wire::Outcome,
    _descriptors: Arc<OriginalInputPermit>,
}
/// One-use native local return, NOT hosted subtree retirement or verifier
/// evidence. This cannot be cloned or reconstructed from its wire projection.
pub struct CompletedLocalOperation {
    begin: Arc<wire::Request>,
    reply: wire::Reply,
    _selected: Arc<HeldOutputRoot>,
    _budget: Arc<DescriptorBudget>,
}
impl CompletedLocalOperation {
    /// Owned native request/reply metadata only. The selected-root/budget
    /// graph is shared original custody and is not charged a second time.
    pub fn retained_bytes(&self) -> Option<usize> {
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(self.begin.retained_bytes()?)?
            .checked_add(2 * std::mem::size_of::<usize>())?;
        match &self.reply.decision {
            wire::Decision::Completed { outcome: wire::Outcome::Failed { reason } }
            | wire::Decision::Refused { reason } => bytes = bytes.checked_add(reason.capacity())?,
            wire::Decision::Ready { exclusions, .. } => {
                for values in [&exclusions.files, &exclusions.directories, &exclusions.trees] {
                    bytes = bytes.checked_add(
                        values.capacity().checked_mul(std::mem::size_of::<crate::FileIdentity>())?,
                    )?;
                }
            }
            _ => {}
        }
        Some(bytes)
    }
    pub fn begin(&self) -> &wire::Request {
        &self.begin
    }
    pub fn observation(&self) -> &wire::Reply {
        &self.reply
    }
    pub fn require_success(&self) -> io::Result<()> {
        match &self.reply.decision {
            wire::Decision::Completed { outcome: wire::Outcome::Succeeded { .. } } => Ok(()),
            wire::Decision::Completed { outcome: wire::Outcome::Failed { reason } } => {
                Err(io::Error::other(reason.clone()))
            }
            _ => Err(refused()),
        }
    }
}
fn bounded_reason(error: impl std::fmt::Display) -> String {
    let mut text = error.to_string();
    if text.len() > 4096 {
        let mut end = 4096;
        while !text.is_char_boundary(end) {
            end -= 1
        }
        text.truncate(end)
    }
    text = text.replace('\0', "?");
    if text.is_empty() {
        text.push_str("native local IO failed")
    }
    text
}
fn current_owner() -> io::Result<crate::Identity> {
    let actual = trust_resource_provenance::process::read_identity(std::process::id())?;
    #[cfg(target_os = "macos")]
    let birth_kind = crate::BirthKind::MacosWallMicroseconds;
    #[cfg(target_os = "linux")]
    let birth_kind = crate::BirthKind::LinuxStartTicks;
    Ok(crate::Identity { pid: actual.pid, birth: actual.birth, birth_kind })
}
impl LocalIoScope {
    /// Recheck the opaque native admission and its SAME actual owners. This
    /// is not a constructor and cannot promote a saved request to a scope.
    pub fn require_live(&self) -> io::Result<()> {
        self.live()
    }
    pub fn request(&self) -> &wire::Request {
        &self.life.request
    }
    pub fn output_root(&self) -> &Arc<HeldOutputRoot> {
        &self.selected
    }
    pub fn descriptor_budget(&self) -> &Arc<DescriptorBudget> {
        &self.budget
    }
    pub fn deadline(&self) -> Instant {
        self.deadline
    }
    fn begin(&self) -> io::Result<&wire::Begin> {
        let wire::Operation::Begin(begin) = &self.life.request.operation else {
            return Err(refused());
        };
        Ok(begin)
    }
    fn live(&self) -> io::Result<()> {
        if self.life.stage.load(Ordering::Acquire) != 0 || self.cancellation.load(Ordering::Acquire)
        {
            return Err(io::ErrorKind::Interrupted.into());
        }
        if Instant::now() >= self.deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        if current_owner()? != self.begin()?.owner {
            return Err(refused());
        }
        self.host.validate(self.deadline)?;
        self.selected.require_disjoint_trees(&self.exclusions, self.deadline)
    }
    fn select(&self, predicate: impl Fn(&wire::Intent) -> bool) -> io::Result<usize> {
        self.live()?;
        self.begin()?
            .intents
            .iter()
            .enumerate()
            .find(|(index, intent)| !self.used[*index] && predicate(intent))
            .map(|(index, _)| index)
            .ok_or_else(refused)
    }
    fn verification(&self, predicate: impl Fn(&wire::Intent) -> bool) -> io::Result<usize> {
        self.live()?;
        self.begin()?.intents.iter().position(predicate).ok_or_else(refused)
    }
    fn record<T>(&mut self, index: usize, result: io::Result<T>) -> io::Result<T> {
        if result.is_ok() {
            self.used[index] = true
        } else if let Err(error) = &result {
            self.fail(error)
        }
        result
    }
    pub fn fail(&mut self, error: impl std::fmt::Display) {
        if self.failure.is_none() {
            self.failure = Some(bounded_reason(error))
        }
    }
    pub fn prepare_directory(&mut self, path: &Path) -> io::Result<Arc<AdmittedRootDirectory>> {
        if self.begin()?.kind == wire::Kind::PublishFresh {
            return Err(refused());
        }
        let index=self.select(|intent|matches!(intent,wire::Intent::Directory{path:expected}if expected==path.as_os_str().as_bytes()))?;
        let result = self.budget.prepare_local_directory(
            &self.selected,
            path,
            &self.exclusions,
            self.deadline,
        );
        self.record(index, result)
    }
    pub fn verify_directory(&mut self, original: &Arc<AdmittedRootDirectory>) -> io::Result<()> {
        let index=self.verification(|intent|matches!(intent,wire::Intent::Directory{path}if path==original.path().as_os_str().as_bytes()))?;
        let result = self.budget.verify_local_directory(&self.selected, original, self.deadline);
        self.record(index, result)
    }
    pub fn capture_file(&mut self, path: &Path) -> io::Result<Arc<AdmittedRootFile>> {
        let index=self.select(|intent|matches!(intent,wire::Intent::CaptureFile{path:expected}if expected==path.as_os_str().as_bytes()))?;
        let result = self.budget.capture_output_file(&self.selected, path, self.deadline);
        self.record(index, result)
    }
    pub fn verify_file(&mut self, original: &Arc<AdmittedRootFile>) -> io::Result<()> {
        let index=self.verification(|intent|matches!(intent,wire::Intent::VerifyFile{path}if path==original.observation().path.as_os_str().as_bytes()))?;
        let result = self.budget.verify_local_file(&self.selected, original, self.deadline);
        self.record(index, result)
    }
    /// Read-only supported runtime capture under this SAME live fixed local
    /// admission. The executable must be a retained original in this output
    /// and budget; every additional runtime root must be in the original
    /// finite Directory manifest. No raw path or digest creates a producer.
    pub fn capture_program(
        &mut self,
        sdk: Arc<trust_resource_provenance::program::HeldProgram>,
        original: &Arc<AdmittedRootFile>,
        runtime_roots: &[PathBuf],
    ) -> io::Result<Arc<trust_resource_provenance::program::produced::HeldProducedProgram>> {
        if runtime_roots.len() > wire::MAX_INTENTS {
            return Err(refused());
        }
        let index=self.verification(|intent|matches!(intent,wire::Intent::VerifyFile{path}if path==original.observation().path.as_os_str().as_bytes()))?;
        let result = (|| {
            let mut directories = Vec::new();
            directories.try_reserve_exact(runtime_roots.len()).map_err(io::Error::other)?;
            for path in runtime_roots {
                directories.push(self.verification(|intent|matches!(intent,wire::Intent::Directory{path:expected}if expected==path.as_os_str().as_bytes()))?);
            }
            // Reserve BEFORE SDK validation, executable or loader capture can
            // open anything. The image retains this permit after scope return.
            let permit = Arc::new(self.budget.reserve_original_inputs(
                trust_resource_provenance::program::HeldProgram::capture_descriptor_bound()?,
            )?);
            self.budget.verify_local_file(&self.selected, original, self.deadline)?;
            let expected = hex_digest(&original.observation().sha256)?;
            let image = self.selected.program(
                sdk,
                &original.observation().path,
                &expected,
                runtime_roots,
                self.deadline,
            )?;
            let observed = &image.observation().executable;
            if observed != original.observation() {
                return Err(refused());
            }
            self.budget.verify_local_file(&self.selected, original, self.deadline)?;
            self.live()?;
            let image = Arc::new(image.retain_descriptor_guard(permit)?);
            for directory in directories {
                self.used[directory] = true;
            }
            Ok(image)
        })();
        self.record(index, result)
    }
    pub fn publish_file(
        &mut self,
        source: &Arc<AdmittedRootFile>,
        destination: &Path,
    ) -> io::Result<Arc<AdmittedRootFile>> {
        let index=self.select(|intent|matches!(intent,wire::Intent::PublishFile{source:expected,destination:target}if expected==source.observation().path.as_os_str().as_bytes()&&target==destination.as_os_str().as_bytes()))?;
        let bytes = self
            .bytes
            .checked_add(source.observation().bytes)
            .filter(|bytes| *bytes <= wire::MAX_TOTAL_BYTES)
            .ok_or_else(refused)?;
        // SAFETY: this opaque scope exists solely after native actual second
        // original/Root SDK/output/exclusion admission. Its owners outlive the
        // synchronous primitive; no writable handle escapes before return.
        let result = unsafe {
            self.budget.publish_local_file(
                &self.selected,
                source,
                destination,
                (self.life.request.key.operation, index as u64),
                &self.exclusions,
                self.deadline,
            )
        };
        if result.is_ok() {
            self.bytes = bytes
        }
        self.record(index, result)
    }
    /// Closed primitives have returned and retain no writer/staging handles.
    /// Failure/timeout/cancellation retires IO without asserting eligibility.
    pub fn finish(mut self) -> LocalCompletion {
        if self.failure.is_none() && self.used.iter().any(|used| !*used) {
            self.fail("native local IO inventory is incomplete")
        }
        if self.failure.is_none()
            && (self.cancellation.load(Ordering::Acquire) || Instant::now() >= self.deadline)
        {
            self.fail("native local IO cancelled or expired")
        }
        let outcome = match self.failure.take() {
            Some(reason) => wire::Outcome::Failed { reason },
            None => {
                wire::Outcome::Succeeded { operations: self.used.len() as u64, bytes: self.bytes }
            }
        };
        self.finished = true;
        self.life.stage.store(1, Ordering::Release);
        LocalCompletion {
            life: self.life.clone(),
            selected: self.selected.clone(),
            budget: self.budget.clone(),
            outcome,
            _descriptors: self._descriptors.clone(),
        }
    }
}
fn hex_digest(value: &str) -> io::Result<[u8; 32]> {
    if value.len() != 64 {
        return Err(refused());
    }
    let mut result = [0; 32];
    for (output, pair) in result.iter_mut().zip(value.as_bytes().as_chunks::<2>().0) {
        let digit = |value: u8| match value {
            b'0'..=b'9' => Some(value - b'0'),
            b'a'..=b'f' => Some(value - b'a' + 10),
            _ => None,
        };
        *output =
            (digit(pair[0]).ok_or_else(refused)? << 4) | digit(pair[1]).ok_or_else(refused)?;
    }
    Ok(result)
}
impl Drop for LocalIoScope {
    fn drop(&mut self) {
        if !self.finished {
            self.life.stage.store(3, Ordering::Release)
        }
    }
}

impl WorkloadControl {
    pub fn next_local_sequence(&self) -> io::Result<u64> {
        if self.failed || self.drained || self.pending.is_some() {
            return Err(refused());
        }
        self.last_local_sequence.checked_add(1).ok_or_else(refused)
    }
    pub fn begin_local(
        &mut self,
        request: wire::Request,
        selected: Arc<HeldOutputRoot>,
        budget: Arc<DescriptorBudget>,
        cancellation: Arc<AtomicBool>,
        deadline: Instant,
    ) -> Result<LocalAdmission, WorkloadControlError> {
        let entered = Instant::now();
        let request = Arc::new(request);
        let before = (|| -> io::Result<_> {
            // Admit validation scratch BEFORE host/root/process bookends can
            // open any descriptions. This reservation is not CPU admission.
            let descriptors = Arc::new(budget.reserve_original_inputs(8)?);
            let bytes = request.encode()?;
            let wire::Operation::Begin(begin) = &request.operation else {
                return Err(refused());
            };
            if self.failed
                || self.drained
                || self.pending.is_some()
                || self.local_active.is_some()
                || self.output_locks.is_none()
                || request.key.root_attempt != self.root_attempt
                || request.key.invocation_sha256 != self.invocation_sha256
                || request.key.sequence != self.next_local_sequence()?
                || self.active_phase != Some((request.key.phase, request.key.ordinal))
                || begin.owner != current_owner()?
                || begin.output_root != selected.path().as_os_str().as_bytes()
            {
                return Err(refused());
            }
            let limit = deadline.min(
                entered.checked_add(Duration::from_nanos(begin.timeout_ns)).ok_or_else(refused)?,
            );
            self.host.validate(limit)?;
            selected.validate(limit)?;
            let mut used = Vec::new();
            used.try_reserve_exact(begin.intents.len()).map_err(io::Error::other)?;
            used.resize(begin.intents.len(), false);
            Ok((bytes, limit, used, descriptors))
        })();
        let (bytes, limit, used, descriptors) = match before {
            Ok(value) => value,
            Err(error) => {
                return Ok(LocalAdmission::NotAdmitted(LocalNotAdmitted {
                    request,
                    reason: bounded_reason(error),
                    busy: false,
                }));
            }
        };
        let received = (|| -> io::Result<_> {
            self.channel.send(&bytes, limit)?;
            let reply = wire::Reply::decode(&self.channel.receive(limit)?, &request)?;
            self.host.validate(limit)?;
            selected.validate(limit)?;
            Ok(reply)
        })();
        let reply = match received {
            Ok(value) => value,
            Err(error) => {
                self.failed = true;
                return Err(WorkloadControlError::Unknown(error));
            }
        };
        self.last_local_sequence = request.key.sequence;
        match reply.decision {
            wire::Decision::Ready { exclusions, .. } => {
                let life = Arc::new(Life { request, stage: AtomicU8::new(0) });
                self.local_active = Some(life.clone());
                Ok(LocalAdmission::Ready(LocalIoScope {
                    life,
                    host: self.host.clone(),
                    selected,
                    budget,
                    deadline: limit,
                    cancellation,
                    used,
                    bytes: 0,
                    failure: None,
                    finished: false,
                    exclusions: PublicationExclusions {
                        files: exclusions.files.iter().map(|id| (id.device, id.inode)).collect(),
                        directories: exclusions
                            .directories
                            .iter()
                            .map(|id| (id.device, id.inode))
                            .collect(),
                        trees: exclusions.trees.iter().map(|id| (id.device, id.inode)).collect(),
                    },
                    _descriptors: descriptors,
                }))
            }
            wire::Decision::Busy => Ok(LocalAdmission::NotAdmitted(LocalNotAdmitted {
                request,
                reason: "native local operation is busy".into(),
                busy: true,
            })),
            wire::Decision::Refused { reason } => {
                Ok(LocalAdmission::NotAdmitted(LocalNotAdmitted { request, reason, busy: false }))
            }
            _ => {
                self.failed = true;
                Err(WorkloadControlError::Unknown(refused()))
            }
        }
    }
    pub fn complete_local(
        &mut self,
        completion: LocalCompletion,
        deadline: Instant,
    ) -> Result<CompletedLocalOperation, WorkloadControlError> {
        let result = (|| -> io::Result<_> {
            if self.failed
                || self.drained
                || self.pending.is_some()
                || !self
                    .local_active
                    .as_ref()
                    .is_some_and(|active| Arc::ptr_eq(active, &completion.life))
                || completion.life.stage.load(Ordering::Acquire) != 1
            {
                return Err(refused());
            }
            let mut key = completion.life.request.key;
            key.sequence = self.next_local_sequence()?;
            let request = wire::Request {
                key,
                operation: wire::Operation::Complete {
                    begun_sequence: completion.life.request.key.sequence,
                    outcome: completion.outcome.clone(),
                },
            };
            let bytes = request.encode()?;
            self.host.validate(deadline)?;
            self.channel.send(&bytes, deadline)?;
            let reply = wire::Reply::decode(&self.channel.receive(deadline)?, &request)?;
            self.host.validate(deadline)?;
            self.last_local_sequence = request.key.sequence;
            completion.life.stage.store(2, Ordering::Release);
            self.local_active = None;
            Ok(CompletedLocalOperation {
                begin: completion.life.request.clone(),
                reply,
                _selected: completion.selected,
                _budget: completion.budget,
            })
        })();
        result.map_err(|error| {
            self.failed = true;
            WorkloadControlError::Unknown(error)
        })
    }
}
