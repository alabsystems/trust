//! Incremental raw failure evidence under the SAME original output capsule.
//! Files and these records grant no execution, completion or retirement.

use portable_atomic::AtomicU64;
use std::ffi::OsStr;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, OnceLock, TryLockError};
use std::time::{Duration, Instant};

use trust_resource_provenance::program::{
    HeldProgram,
    produced::{BoundedEvidenceFile, HeldEvidenceRoot},
};

const MAX_ACTIONS: u64 = 1024;
const HEADER: &[u8] = b"trust.workload.failed-evidence.v1\0";
static ABORT_EVIDENCE: OnceLock<Arc<Evidence>> = OnceLock::new();
static ABORT_DEADLINE: OnceLock<Instant> = OnceLock::new();
static ABORT_STARTED: AtomicBool = AtomicBool::new(false);
static ABORT_SYNCED: AtomicBool = AtomicBool::new(false);
static ABORT_SYNC_SUCCEEDED: AtomicBool = AtomicBool::new(false);

fn incomplete(reason: &'static str) -> io::Error {
    io::Error::other(reason)
}

fn lock_until<T>(mutex: &Mutex<T>, deadline: Instant) -> io::Result<std::sync::MutexGuard<'_, T>> {
    loop {
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        match mutex.try_lock() {
            Ok(guard) => return Ok(guard),
            Err(TryLockError::Poisoned(_)) => {
                return Err(incomplete("original evidence owner poisoned"));
            }
            Err(TryLockError::WouldBlock) => std::thread::sleep(Duration::from_millis(1)),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Kind {
    Compile,
    CompilerQuery,
    BuildScript,
    Inventory,
    Sample,
    Diagnostic,
}
impl Kind {
    fn code(self) -> u8 {
        match self {
            Self::Compile => 1,
            Self::CompilerQuery => 2,
            Self::BuildScript => 3,
            Self::Inventory => 4,
            Self::Sample => 5,
            Self::Diagnostic => 6,
        }
    }
}

/// Equality binding supplied by the actual action owner BEFORE delivery. The
/// description digest binds its observed argv/cwd/environment projection; it
/// must omit the private job locator/capability, never relabel semantic argv.
pub(crate) struct Binding {
    pub(crate) member: [u8; 16],
    pub(crate) kind: Kind,
    pub(crate) description_sha256: [u8; 32],
}

pub(crate) fn command_description(command: &trust_resource_controller::CommandSpec) -> [u8; 32] {
    fn part(hash: &mut cargo_util::Sha256, bytes: &[u8]) {
        hash.update(&(bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    }
    let mut hash = cargo_util::Sha256::new();
    part(&mut hash, b"observed-process-builder-command-projection-v1");
    part(&mut hash, &command.program);
    hash.update(&[u8::from(command.arg0.is_some())]);
    if let Some(arg0) = &command.arg0 {
        part(&mut hash, arg0);
    }
    part(&mut hash, &command.cwd);
    hash.update(&(command.args.len() as u64).to_le_bytes());
    for arg in &command.args {
        part(&mut hash, arg);
    }
    hash.update(&(command.environment.len() as u64).to_le_bytes());
    for (name, value) in &command.environment {
        part(&mut hash, name);
        if matches!(
            name.as_slice(),
            b"ATERM_RESOURCE_JOB_V3"
                | b"TRUST_CPU_HANDOFF"
                | b"CARGO_JOBSERVER_HANDOFF"
                | b"TRUST_JOBSERVER_HANDOFF"
        ) {
            part(&mut hash, b"<private-native-binding-omitted>");
        } else {
            part(&mut hash, value);
        }
    }
    hash.finish()
}
pub(crate) struct Evidence {
    writer: Mutex<HeldEvidenceRoot>,
    sdk: Arc<HeldProgram>,
    root_attempt: [u8; 16],
    invocation_sha256: [u8; 32],
    path: PathBuf,
    deadline: Instant,
    next: AtomicU64,
    failed: Arc<AtomicBool>,
    sealed: Arc<AtomicBool>,
    actions: Mutex<Vec<Arc<ActionEvidence>>>,
    // The default Unknown binding is synchronized BEFORE any target delivery.
    // It never needs append/budget locking on an abort path.
    _unknown: BoundedEvidenceFile,
}

pub(crate) struct ActionEvidence {
    member: [u8; 16],
    kind: Kind,
    description_sha256: [u8; 32],
    pub(crate) stdout: RawStream,
    pub(crate) stderr: RawStream,
    // Original create-only action/invocation binding, already synchronized.
    _binding: BoundedEvidenceFile,
}
impl ActionEvidence {
    pub(crate) fn member_attempt(&self) -> [u8; 16] {
        self.member
    }
    /// Synchronize only this actual action's original prefixes. Ordinary graph
    /// checkpoints must not seal the whole root's writer (abort does that).
    /// No FD/writer export, new budget or later deadline is created here.
    pub(crate) fn sync_prefix(&self, deadline: Instant) -> io::Result<()> {
        let deadline = deadline.min(self.stdout.deadline).min(self.stderr.deadline);
        let stdout = self.stdout.synchronize(deadline);
        let stderr = self.stderr.synchronize(deadline);
        match (stdout, stderr) {
            (Ok(()), Ok(())) => Ok(()),
            (first, second) => {
                self.stdout.failed.store(true, Ordering::Release);
                Err(io::Error::other(format!(
                    "original action prefix synchronization incomplete: stdout={:?}; stderr={:?}",
                    first.err(),
                    second.err(),
                )))
            }
        }
    }
}

pub(crate) struct RawStream {
    file: Mutex<BoundedEvidenceFile>,
    failed: Arc<AtomicBool>,
    sealed: Arc<AtomicBool>,
    deadline: Instant,
    seen: AtomicU64,
    persisted: AtomicU64,
}

impl Evidence {
    /// Actual native target request DATA, durably synchronized BEFORE its
    /// delivery starts. No claim of execution, kernel environment, completion,
    /// source authentication or proof authority can be read from this record.
    pub(crate) fn publish_action_command(
        &self,
        action: &Arc<ActionEvidence>,
        command: &trust_resource_controller::CommandSpec,
    ) -> io::Result<()> {
        let deadline = self.deadline.min(Instant::now() + Duration::from_secs(2));
        let result = (|| {
            if self.failed()
                || self.sealed.load(Ordering::Acquire)
                || !matches!(action.kind, Kind::Compile)
                || action.description_sha256 != command_description(command)
                || !lock_until(&self.actions, deadline)?
                    .iter()
                    .any(|original| Arc::ptr_eq(original, action))
            {
                return Err(incomplete(
                    "command observation does not bind its original registered native action",
                ));
            }
            let environment=command.environment.iter().map(|(name,value)| {
                let private=trust_resource_controller::resolver::private_environment_channel(name)
                    ||matches!(name.as_slice(),b"TRUST_CPU_HANDOFF"|b"CARGO_JOBSERVER_HANDOFF"|b"ATERM_WORKLOAD_CPU_FDS_V1"|b"ATERM_WORKLOAD_HOST_STORE_FD_V1"|b"ATERM_SDK_LEASE_V3"|b"ATERM_RESOURCE_INSPECTOR");
                serde_json::json!({"name_hex":hex::encode(name),"value_hex":if private{None}else{Some(hex::encode(value))},"private_transport_omitted":private})
            }).collect::<Vec<_>>();
            let bytes=serde_json::to_vec(&serde_json::json!({
                "schema":"trust.native-member-command-observation.v1",
                "scope":"observed ProcessBuilder target request before delivery; no kernel environment attestation, execution, retirement, source authentication or proof authority",
                "root_attempt":hex::encode(self.root_attempt),"invocation_sha256":hex::encode(self.invocation_sha256),
                "member_attempt":hex::encode(action.member),"command_description_sha256":hex::encode(action.description_sha256),
                "program_hex":hex::encode(&command.program),"arg0_hex":command.arg0.as_ref().map(hex::encode),
                "cwd_hex":hex::encode(&command.cwd),"args_hex":command.args.iter().map(hex::encode).collect::<Vec<_>>(),"environment":environment,
            })).map_err(io::Error::other)?;
            if bytes.len() > 4 * 1024 * 1024 {
                return Err(incomplete(
                    "native command observation exceeds its durable bound",
                ));
            }
            let mut writer = lock_until(&self.writer, deadline)?;
            let mut file = writer.create(
                OsStr::new(&format!(
                    "member-{}.command.v1.json",
                    hex::encode(action.member)
                )),
                4 * 1024 * 1024,
                deadline,
            )?;
            let append = append_exact(&mut file, &bytes, deadline);
            let sync = file.sync_prefix(deadline);
            append.and(sync)
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }
    /// Publish original pre-resource-injection command DATA before the compiler
    /// can be delivered. It survives WorkGuard's non-unwinding Unknown abort;
    /// it contains no materialization, native member, proof or execution grant.
    pub(crate) fn publish_original_command(
        &self,
        root: [u8; 16],
        invocation: [u8; 32],
        unit: u64,
        digest: &str,
        bytes: &[u8],
    ) -> io::Result<()> {
        let deadline = self.deadline.min(Instant::now() + Duration::from_secs(2));
        let result = (|| {
            if self.sealed.load(Ordering::Acquire)
                || root != self.root_attempt
                || invocation != self.invocation_sha256
                || digest.len() != 64
                || !digest
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
                || bytes.len() > 4 * 1024 * 1024
            {
                return Err(incomplete(
                    "original command data lost its root/bounds binding",
                ));
            }
            let mut writer = lock_until(&self.writer, deadline)?;
            let mut file = writer.create(
                OsStr::new(&format!("unit-{unit}-{digest}.original-command.v1.json")),
                4 * 1024 * 1024,
                deadline,
            )?;
            let append = append_exact(&mut file, bytes, deadline);
            // Synchronize the actual prefix even after short write/quota/IO
            // failure. This publication is never deferred to a destructor.
            let sync = file.sync_prefix(deadline);
            append.and(sync)
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }
    pub(crate) fn publish_service_input(
        &self,
        observation: Result<(Vec<u8>, u64, Option<String>, bool), String>,
    ) -> io::Result<()> {
        let deadline = self
            .deadline
            .min(Instant::now() + Duration::from_millis(250));
        let result = (|| {
            if self.sealed.load(Ordering::Acquire) {
                return Err(incomplete(
                    "original service input evidence is already sealed",
                ));
            }
            let observation = match observation {
                Ok((prefix, seen, failure, stopped)) => {
                    if prefix.len() > 64 * 1024 || seen < prefix.len() as u64 {
                        return Err(incomplete("invalid original service input prefix bounds"));
                    }
                    serde_json::json!({"prefix_hex":hex::encode(prefix),"bytes_seen":seen,"failure":failure,"stopped":stopped})
                }
                Err(failure) => {
                    serde_json::json!({"prefix_hex":null,"bytes_seen":null,"failure":failure,"stopped":null})
                }
            };
            let bytes=serde_json::to_vec(&serde_json::json!({"schema":"trust.workload.service-input-observation.v1","root_attempt":hex::encode(self.root_attempt),"invocation_sha256":hex::encode(self.invocation_sha256),"observation":observation})).map_err(io::Error::other)?;
            let mut writer = lock_until(&self.writer, deadline)?;
            let mut file =
                writer.create(OsStr::new("service-input.v1.json"), 256 * 1024, deadline)?;
            append_exact(&mut file, &bytes, deadline)?;
            file.sync_prefix(deadline)
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }
    /// Original local helper observations stay separate from its hosted
    /// target. Root owning-wait CPU includes helpers it actually waited for;
    /// never add these as an invented tree metric or infer a missing outcome.
    pub(crate) fn publish_helper(
        &self,
        member: [u8; 16],
        helper: Option<trust_resource_controller::client::HelperObservation>,
    ) -> io::Result<()> {
        let deadline = self
            .deadline
            .min(Instant::now() + Duration::from_millis(250));
        let result = (|| {
            if self.sealed.load(Ordering::Acquire)
                || !lock_until(&self.actions, deadline)?
                    .iter()
                    .any(|action| action.member == member)
            {
                return Err(incomplete(
                    "helper observation lacks its original native action binding",
                ));
            }
            let observed=helper.map(|helper| serde_json::json!({
                "identity":{"pid":helper.identity.pid,"birth":helper.identity.birth,"birth_kind":match helper.identity.birth_kind {
                    trust_resource_controller::BirthKind::MacosWallMicroseconds=>"macos-wall-microseconds",trust_resource_controller::BirthKind::LinuxStartTicks=>"linux-start-ticks",
                }},
                "outcome":helper.outcome.map(|outcome|match outcome {trust_resource_controller::Outcome::Exit(code)=>serde_json::json!({"exit":code}),trust_resource_controller::Outcome::Signal(signal)=>serde_json::json!({"signal":signal})}),
            }));
            let bytes=serde_json::to_vec(&serde_json::json!({"schema":"trust.workload.local-helper-observation.v1", "root_attempt":hex::encode(self.root_attempt),"invocation_sha256":hex::encode(self.invocation_sha256),"target_member_attempt":hex::encode(member),"helper":observed,"metric_relation":"root-owning-wait-includes-local-helper-only-if-waited","cpu_times":null})).map_err(io::Error::other)?;
            let mut writer = lock_until(&self.writer, deadline)?;
            let name = format!("member-{}.local-helper.v1.json", hex::encode(member));
            let mut file = writer.create(OsStr::new(&name), 4096, deadline)?;
            append_exact(&mut file, &bytes, deadline)?;
            file.sync_prefix(deadline)
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }
    /// Role7's stream bodies can be64MiB each and already reach the original
    /// raw files incrementally. Retain their actual lengths/end facts and the
    /// original event prefix separately, without pretending empty bodies are
    /// a complete metadata64KiB capture or granting a successful terminal.
    pub(crate) fn publish_produced_failure(
        &self,
        observation: &trust_resource_controller::client::ProducedFailureObservation,
    ) -> io::Result<()> {
        let deadline = self
            .deadline
            .min(Instant::now() + Duration::from_millis(250));
        let result = (|| {
            if self.sealed.load(Ordering::Acquire)
                || observation.key.root_attempt != self.root_attempt
                || observation.key.invocation_sha256 != self.invocation_sha256
                || !lock_until(&self.actions, deadline)?
                    .iter()
                    .any(|action| action.member == observation.member_attempt)
            {
                return Err(incomplete(
                    "produced failure lacks its original registered action",
                ));
            }
            let mut bytes = b"trust.workload.produced-failure.v1\0".to_vec();
            bytes.extend(observation.key.root_attempt);
            bytes.extend(observation.key.invocation_sha256);
            bytes.extend(observation.member_attempt);
            bytes.extend(observation.key.phase);
            bytes.extend(observation.key.ordinal.to_be_bytes());
            bytes.extend(observation.key.output);
            bytes.extend((observation.stdout.len() as u64).to_be_bytes());
            bytes.extend((observation.stderr.len() as u64).to_be_bytes());
            bytes.extend([
                u8::from(observation.stdout_eof),
                u8::from(observation.stderr_eof),
                u8::from(observation.output_limit_exceeded),
            ]);
            bytes.extend(observation.event_bytes_seen.to_be_bytes());
            let mut part = |value: &[u8]| -> io::Result<()> {
                if bytes
                    .len()
                    .checked_add(8)
                    .and_then(|n| n.checked_add(value.len()))
                    .is_none_or(|n| n > 4 * trust_resource_controller::MAX_PAYLOAD)
                {
                    return Err(incomplete(
                        "produced failure annex exceeds its original finite bound",
                    ));
                }
                bytes
                    .try_reserve(value.len() + 8)
                    .map_err(io::Error::other)?;
                bytes.extend((value.len() as u64).to_be_bytes());
                bytes.extend(value);
                Ok(())
            };
            part(&observation.event_prefix)?;
            part(
                observation
                    .capture_error
                    .as_deref()
                    .unwrap_or("")
                    .as_bytes(),
            )?;
            part(
                &observation
                    .prepared
                    .as_ref()
                    .map(|value| value.encode())
                    .transpose()?
                    .unwrap_or_default(),
            )?;
            part(
                &observation
                    .observed_completion
                    .as_ref()
                    .map(|value| value.encode())
                    .transpose()?
                    .unwrap_or_default(),
            )?;
            part(
                &observation
                    .observed_started
                    .map(|started| {
                        trust_resource_controller::StatusFrame {
                            root_attempt: observation.key.root_attempt,
                            member_attempt: observation.member_attempt,
                            status: trust_resource_controller::Status::Started(started),
                        }
                        .encode()
                    })
                    .transpose()?
                    .unwrap_or_default(),
            )?;
            let mut writer = lock_until(&self.writer, deadline)?;
            let name = format!(
                "member-{}.produced-failure.v1",
                hex::encode(observation.member_attempt)
            );
            let mut file = writer.create(
                OsStr::new(&name),
                (4 * trust_resource_controller::MAX_PAYLOAD) as u64,
                deadline,
            )?;
            append_exact(&mut file, &bytes, deadline)?;
            file.sync_prefix(deadline)
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }
    /// Publish the actual native failure/event prefix before Unknown abort.
    /// This is a bounded diagnostic annex, never a terminal or resource grant.
    /// The original action/SDK/output writer must already exist; no path or
    /// saved observation can construct another sink or execution continuation.
    pub(crate) fn publish_failure(
        &self,
        observation: &trust_resource_controller::MetadataFailureObservation,
    ) -> io::Result<()> {
        let deadline = self
            .deadline
            .min(Instant::now() + Duration::from_millis(250));
        let result = (|| {
            if self.sealed.load(Ordering::Acquire)
                || observation.root_attempt != self.root_attempt
                || !lock_until(&self.actions, deadline)?
                    .iter()
                    .any(|action| action.member == observation.member_attempt)
            {
                return Err(incomplete(
                    "failure does not bind an original registered native action",
                ));
            }
            let bytes = observation.encode()?;
            let mut writer = lock_until(&self.writer, deadline)?;
            let name = format!(
                "member-{}.failure.v1",
                hex::encode(observation.member_attempt)
            );
            let mut file = writer.create(
                OsStr::new(&name),
                trust_resource_controller::MAX_PAYLOAD as u64,
                deadline,
            )?;
            append_exact(&mut file, &bytes, deadline)?;
            file.sync_prefix(deadline)
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }
    /// Consume the actual writer opened before compilation with the REAL
    /// original SDK owner and actual root attempt. No path/JSON constructor.
    pub(crate) fn new(
        mut writer: HeldEvidenceRoot,
        sdk: Arc<HeldProgram>,
        root_attempt: [u8; 16],
        invocation_sha256: [u8; 32],
        deadline: Instant,
    ) -> io::Result<Arc<Self>> {
        if root_attempt == [0; 16] || Instant::now() >= deadline {
            return Err(incomplete("invalid original evidence binding/deadline"));
        }
        sdk.validate(deadline)?;
        let path = writer.path().to_owned();
        if path.starts_with(sdk.root()) || sdk.root().starts_with(&path) {
            return Err(incomplete("workload evidence overlaps the original SDK"));
        }
        let mut unknown = writer.create(OsStr::new("attempt-unknown.v1"), 256, deadline)?;
        let mut header = HEADER.to_vec();
        header.extend(root_attempt);
        header.extend(invocation_sha256);
        header.push(0); // Explicit Unknown, never inferred success/no-execution.
        append_exact(&mut unknown, &header, deadline)?;
        unknown.sync_prefix(deadline)?;
        sdk.validate(deadline)?;
        Ok(Arc::new(Self {
            writer: Mutex::new(writer),
            sdk,
            root_attempt,
            invocation_sha256,
            path,
            deadline,
            next: AtomicU64::new(0),
            failed: Arc::new(AtomicBool::new(false)),
            sealed: Arc::new(AtomicBool::new(false)),
            actions: Mutex::new(Vec::new()),
            _unknown: unknown,
        }))
    }

    pub(crate) fn path(&self) -> &Path {
        &self.path
    }
    pub(crate) fn deadline(&self) -> Instant {
        self.deadline
    }
    pub(crate) fn sdk_matches(&self, sdk: &Arc<HeldProgram>) -> bool {
        Arc::ptr_eq(&self.sdk, sdk)
    }
    pub(crate) fn invocation_sha256(&self) -> [u8; 32] {
        self.invocation_sha256
    }
    pub(crate) fn root_attempt(&self) -> [u8; 16] {
        self.root_attempt
    }
    pub(crate) fn failed(&self) -> bool {
        self.failed.load(Ordering::Acquire)
    }

    /// Register all original stream descriptions before delivery. Exhaustion,
    /// replacement, IO and short writes fail explicitly, without a second sink.
    pub(crate) fn action(
        &self,
        binding: Binding,
        stdout_cap: u64,
        stderr_cap: u64,
    ) -> io::Result<Arc<ActionEvidence>> {
        let result = (|| {
            if Instant::now() >= self.deadline
                || self.failed()
                || self.sealed.load(Ordering::Acquire)
                || binding.member == [0; 16]
            {
                return Err(incomplete(
                    "original workload evidence is incomplete or expired",
                ));
            }
            let sequence = self
                .next
                .fetch_update(Ordering::AcqRel, Ordering::Acquire, |next| {
                    (next < MAX_ACTIONS).then_some(next + 1)
                })
                .map_err(|_| incomplete("original workload evidence action bound exhausted"))?;
            let name = format!("action-{sequence:04}-{}", hex::encode(binding.member));
            let mut writer = lock_until(&self.writer, self.deadline)?;
            let mut record = writer.create(
                OsStr::new(&format!("{name}.binding.v1")),
                256,
                self.deadline,
            )?;
            let mut header = HEADER.to_vec();
            header.extend(self.root_attempt);
            header.extend(self.invocation_sha256);
            header.extend(sequence.to_be_bytes());
            header.extend(binding.member);
            header.push(binding.kind.code());
            header.extend(binding.description_sha256);
            append_exact(&mut record, &header, self.deadline)?;
            record.sync_prefix(self.deadline)?;
            let stdout = writer.create(
                OsStr::new(&format!("{name}.stdout.bin")),
                stdout_cap,
                self.deadline,
            )?;
            let stderr = writer.create(
                OsStr::new(&format!("{name}.stderr.bin")),
                stderr_cap,
                self.deadline,
            )?;
            drop(writer);
            let action = Arc::new(ActionEvidence {
                member: binding.member,
                kind: binding.kind,
                description_sha256: binding.description_sha256,
                stdout: RawStream::new(
                    stdout,
                    self.failed.clone(),
                    self.sealed.clone(),
                    self.deadline,
                ),
                stderr: RawStream::new(
                    stderr,
                    self.failed.clone(),
                    self.sealed.clone(),
                    self.deadline,
                ),
                _binding: record,
            });
            lock_until(&self.actions, self.deadline)?.push(action.clone());
            Ok(action)
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }

    /// Actual write prefixes only. Never append diagnostics or take the writer
    /// budget mutex here: a different writer may hold it during an IO failure.
    pub(crate) fn synchronize(&self, deadline: Instant) -> io::Result<()> {
        // No writer may append after its prefix was synchronized. A writer
        // already inside IO is observed as unavailable/incomplete via try_lock.
        self.sealed.store(true, Ordering::Release);
        let actions = self.actions.try_lock().map_err(|_| {
            self.failed.store(true, Ordering::Release);
            incomplete("original evidence registry unavailable during abort")
        })?;
        let mut complete = true;
        for action in actions.iter() {
            for stream in [&action.stdout, &action.stderr] {
                if Instant::now() >= deadline || stream.synchronize(deadline).is_err() {
                    complete = false;
                }
            }
        }
        if complete {
            Ok(())
        } else {
            self.failed.store(true, Ordering::Release);
            Err(incomplete(
                "some original workload prefixes could not be synchronized",
            ))
        }
    }
}

fn append_exact(file: &mut BoundedEvidenceFile, bytes: &[u8], deadline: Instant) -> io::Result<()> {
    if file.append(bytes, deadline)? != bytes.len() {
        return Err(incomplete("original evidence received a short write"));
    }
    Ok(())
}

impl RawStream {
    fn new(
        file: BoundedEvidenceFile,
        failed: Arc<AtomicBool>,
        sealed: Arc<AtomicBool>,
        deadline: Instant,
    ) -> Self {
        Self {
            file: Mutex::new(file),
            failed,
            sealed,
            deadline,
            seen: AtomicU64::new(0),
            persisted: AtomicU64::new(0),
        }
    }

    /// Write actual read bytes immediately, before a parser/callback can fail.
    /// There is no sole memory Vec to dump at a terminal or destructor.
    pub(crate) fn append(&self, bytes: &[u8]) -> io::Result<()> {
        let result = (|| {
            self.seen
                .fetch_update(Ordering::AcqRel, Ordering::Acquire, |seen| {
                    seen.checked_add(bytes.len() as u64)
                })
                .map_err(|_| incomplete("original received-byte count overflow"))?;
            let mut file = self
                .file
                .try_lock()
                .map_err(|_| incomplete("original stream writer busy/poisoned"))?;
            if self.sealed.load(Ordering::Acquire) {
                return Err(incomplete(
                    "original abort prefix is sealed; later read remains incomplete",
                ));
            }
            let written = file.append(bytes, self.deadline)?;
            self.persisted
                .store(file.bytes_written(), Ordering::Release);
            if written != bytes.len() {
                return Err(incomplete("original raw stream prefix was truncated"));
            }
            Ok(())
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }

    #[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn received(&self) -> u64 {
        self.seen.load(Ordering::Acquire)
    }
    #[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn persisted(&self) -> u64 {
        self.persisted.load(Ordering::Acquire)
    }

    fn synchronize(&self, deadline: Instant) -> io::Result<()> {
        match self.file.try_lock() {
            Ok(file) => file.sync_prefix(deadline),
            Err(TryLockError::WouldBlock | TryLockError::Poisoned(_)) => Err(incomplete(
                "original stream unavailable during abort; prefix remains incomplete",
            )),
        }
    }
}

/// Install only for the SAME actual workload owner before monitor/threads or
/// project code. The observer retains data/writer custody, never an execution
/// or release capability; there is no reset or second provider fallback.
pub(crate) fn install_abort_evidence(evidence: Arc<Evidence>) -> io::Result<()> {
    ABORT_EVIDENCE
        .set(evidence)
        .map_err(|_| incomplete("original workload abort evidence already installed"))
}

pub(crate) fn is_installed(evidence: &Arc<Evidence>) -> bool {
    ABORT_EVIDENCE
        .get()
        .is_some_and(|original| Arc::ptr_eq(original, evidence))
}

/// Called by ALL original workload abort paths. Concurrent/reentrant aborts
/// share one deadline and never wait on the append/budget/stream mutexes.
pub(crate) fn synchronize_abort(requested_deadline: Instant) -> io::Result<()> {
    let Some(evidence) = ABORT_EVIDENCE.get() else {
        return Ok(());
    };
    let deadline = *ABORT_DEADLINE.get_or_init(|| requested_deadline.min(evidence.deadline));
    if ABORT_STARTED
        .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
        .is_ok()
    {
        let result = evidence.synchronize(deadline);
        ABORT_SYNC_SUCCEEDED.store(result.is_ok(), Ordering::Release);
        ABORT_SYNCED.store(true, Ordering::Release);
        result
    } else {
        while !ABORT_SYNCED.load(Ordering::Acquire) && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(1));
        }
        if ABORT_SYNCED.load(Ordering::Acquire) && ABORT_SYNC_SUCCEEDED.load(Ordering::Acquire) {
            Ok(())
        } else {
            Err(incomplete(
                "concurrent original workload prefix synchronization incomplete/expired",
            ))
        }
    }
}

#[cfg(test)]
pub(crate) mod tests;
