//! Finite input/output data for the native metadata service. These records
//! carry no root capability, resource grant or admission authority. Only the
//! funded service can construct member requests from its actual live context.

use std::collections::BTreeSet;

use super::*;
use crate::{Started, Status, StatusFrame};

pub const MAX_PROBES: usize = 6;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MetadataProbeCommand {
    VerboseVersion,
    Sysroot,
    UnverifiedVersion,
}
impl MetadataProbeCommand {
    pub fn arguments(self) -> Vec<Vec<u8>> {
        match self {
            Self::VerboseVersion => vec![b"-vV".to_vec()],
            Self::Sysroot => vec![b"--print".to_vec(), b"sysroot".to_vec()],
            Self::UnverifiedVersion => vec![b"--unverified".to_vec(), b"--version".to_vec()],
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetadataProbe {
    pub root: Vec<u8>,
    pub program: Vec<u8>,
    pub program_sha256: [u8; 32],
    pub command: MetadataProbeCommand,
    pub cwd: Vec<u8>,
}
impl MetadataProbe {
    pub fn validate(&self) -> io::Result<()> {
        if [&self.root, &self.program, &self.cwd]
            .into_iter()
            .any(|p| p.len() > 4096 || !canonical_absolute(p))
            || !self.program.starts_with(&self.root)
            || self.program.get(self.root.len()) != Some(&b'/')
            || self.cwd != self.root
        {
            return Err(invalid());
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetadataBatch {
    /// Optional explicit original native-host discovery store. Data only;
    /// account discovery is default, and an explicit failure has no fallback.
    pub host_store: Option<Vec<u8>>,
    pub service_program: Vec<u8>,
    pub service_sha256: [u8; 32],
    pub probes: Vec<MetadataProbe>,
}
impl MetadataBatch {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.probes.is_empty() || self.probes.len() > MAX_PROBES {
            return Err(invalid());
        }
        let mut e = Encoder::new(15);
        if !canonical_absolute(&self.service_program) || self.service_program.len() > 4096 {
            return Err(invalid());
        }
        e.bytes(&self.service_program)?;
        e.0.extend(self.service_sha256);
        match &self.host_store {
            None => e.number(0),
            Some(path) => {
                if path.len() > 4096 || !canonical_absolute(path) {
                    return Err(invalid());
                }
                e.number(1);
                e.bytes(path)?;
            }
        }
        e.number(self.probes.len() as u64);
        for probe in &self.probes {
            probe.validate()?;
            e.bytes(&probe.root)?;
            e.bytes(&probe.program)?;
            e.0.extend(probe.program_sha256);
            e.number(match probe.command {
                MetadataProbeCommand::VerboseVersion => 0,
                MetadataProbeCommand::Sysroot => 1,
                MetadataProbeCommand::UnverifiedVersion => 2,
            });
            e.bytes(&probe.cwd)?;
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 15)?;
        let service_program = d.bytes()?;
        let service_sha256 = d.array()?;
        let host_store = match d.number()? {
            0 => None,
            1 => Some(d.bytes()?),
            _ => return Err(invalid()),
        };
        let mut probes = Vec::new();
        for _ in 0..d.count(MAX_PROBES)? {
            probes.push(MetadataProbe {
                root: d.bytes()?,
                program: d.bytes()?,
                program_sha256: d.array()?,
                command: match d.number()? {
                    0 => MetadataProbeCommand::VerboseVersion,
                    1 => MetadataProbeCommand::Sysroot,
                    2 => MetadataProbeCommand::UnverifiedVersion,
                    _ => return Err(invalid()),
                },
                cwd: d.bytes()?,
            });
        }
        d.done()?;
        let batch = Self { host_store, service_program, service_sha256, probes };
        batch.encode()?;
        Ok(batch)
    }
}

/// Actual member observations from the native authenticated client, or saved
/// data after decoding. Decoding never establishes producer/process authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetadataResult {
    pub prepared: MetadataPrepared,
    pub started: Started,
    pub completion: MetadataCompletion,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub output_limit_exceeded: bool,
}

/// Observations inside the already-funded service, rather than a pre-GO event
/// or SDK/resource grant. The actual host retains the original service SDK.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetadataRunnerObservation {
    pub root: Vec<u8>,
    pub executable: MetadataFile,
    pub runtime: Vec<MetadataFile>,
    pub loader_paths: Vec<Vec<u8>>,
    pub system_dependencies: Vec<String>,
    pub policy: String,
    pub scope: String,
    pub identity: crate::Identity,
    /// Exact authenticated ContextReply; no capability or closure right.
    pub context_frame: Vec<u8>,
}
impl MetadataRunnerObservation {
    fn validate(&self, batch: &MetadataBatch) -> io::Result<()> {
        self.validate_program(&batch.service_program, &batch.service_sha256)
    }
    pub(crate) fn validate_program(&self, program: &[u8], sha256: &[u8; 32]) -> io::Result<()> {
        if !canonical_absolute(&self.root)
            || self.executable.path != program
            || &self.executable.sha256 != sha256
            || self.runtime.len() > 128
            || self.loader_paths.len() > 2
            || self.system_dependencies.len() > 128
            || self.scope.is_empty()
            || self.scope.len() > 4096
            || self.policy.is_empty()
            || self.policy.len() > 256
            || self.identity.pid <= 1
            || self.identity.birth == 0
            || self.context_frame.is_empty()
            || self.context_frame.len() > MAX_FIELD
        {
            return Err(invalid());
        }
        let context = crate::ContextReply::decode_observation(&self.context_frame)?.context;
        if context.original_root != self.identity
            || context.subject != (crate::Subject::Root { identity: self.identity })
            || !matches!(context.cpu, crate::Cpu::RetainedFixed { units: 1, .. })
            || context.sdk.as_ref().is_none_or(|sdk| sdk.execution != self.root)
        {
            return Err(invalid());
        }
        let mut paths = BTreeSet::new();
        let mut bytes = 0u64;
        for file in std::iter::once(&self.executable).chain(&self.runtime) {
            file.validate(&self.root)?;
            bytes = bytes.checked_add(file.bytes).ok_or_else(invalid)?;
            if !paths.insert(&file.path) || bytes > 4 * 1024 * 1024 * 1024 {
                return Err(invalid());
            }
        }
        for path in &self.loader_paths {
            if path.len() > 4096
                || !canonical_absolute(path)
                || !path.starts_with(&self.root)
                || path.get(self.root.len()) != Some(&b'/')
            {
                return Err(invalid());
            }
        }
        for path in &self.system_dependencies {
            if path.len() > 4096 || !canonical_absolute(path.as_bytes()) {
                return Err(invalid());
            }
        }
        Ok(())
    }
    pub(crate) fn encode(&self, e: &mut Encoder) -> io::Result<()> {
        e.bytes(&self.root)?;
        self.executable.encode(e)?;
        e.number(self.runtime.len() as u64);
        for file in &self.runtime {
            file.encode(e)?;
        }
        e.number(self.loader_paths.len() as u64);
        for path in &self.loader_paths {
            e.bytes(path)?;
        }
        e.number(self.system_dependencies.len() as u64);
        for path in &self.system_dependencies {
            e.bytes(path.as_bytes())?;
        }
        e.bytes(self.policy.as_bytes())?;
        e.bytes(self.scope.as_bytes())?;
        e.number(self.identity.pid.into());
        e.number(self.identity.birth);
        e.number(match self.identity.birth_kind {
            crate::BirthKind::MacosWallMicroseconds => 0,
            crate::BirthKind::LinuxStartTicks => 1,
        });
        e.bytes(&self.context_frame)
    }
    pub(crate) fn decode(d: &mut crate::wire::Decoder<'_>) -> io::Result<Self> {
        let root = d.bytes()?;
        let executable = MetadataFile::decode(d)?;
        let mut runtime = Vec::new();
        for _ in 0..d.count(128)? {
            runtime.push(MetadataFile::decode(d)?);
        }
        let mut loader_paths = Vec::new();
        for _ in 0..d.count(2)? {
            loader_paths.push(d.bytes()?);
        }
        let mut system_dependencies = Vec::new();
        for _ in 0..d.count(128)? {
            system_dependencies.push(d.text()?);
        }
        let policy = d.text()?;
        let scope = d.text()?;
        let pid = d.narrow()?;
        let birth = d.number()?;
        let birth_kind = match d.number()? {
            0 => crate::BirthKind::MacosWallMicroseconds,
            1 => crate::BirthKind::LinuxStartTicks,
            _ => return Err(invalid()),
        };
        let context_frame = d.bytes()?;
        Ok(Self {
            root,
            executable,
            runtime,
            loader_paths,
            system_dependencies,
            policy,
            scope,
            identity: crate::Identity { pid, birth, birth_kind },
            context_frame,
        })
    }
}

/// A failure stops the finite batch; records retain all actual completed
/// outcomes before it. Failure text has no classification/proof authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetadataBatchReport {
    pub runner: Option<MetadataRunnerObservation>,
    pub records: Vec<MetadataResult>,
    pub failure: Option<String>,
    /// Available actual start of the one failed, incomplete member. This is
    /// retained observation, never a fabricated exit or release receipt.
    pub failure_started: Option<StatusFrame>,
    /// Original bounded bytes from an incomplete/failed exchange. This never
    /// supplies a terminal process outcome or resource-retirement receipt.
    pub failure_observation: Option<MetadataFailureObservation>,
}
impl MetadataBatchReport {
    pub fn validate_for(&self, batch: &MetadataBatch) -> io::Result<()> {
        batch.encode()?;
        if self.records.len() > batch.probes.len()
            || (self.failure.is_none() && self.records.len() != batch.probes.len())
            || self.failure.as_ref().is_some_and(|reason| reason.is_empty() || reason.len() > 4096)
        {
            return Err(invalid());
        }
        let mut attempts = BTreeSet::new();
        if let Some(runner) = &self.runner {
            runner.validate(batch)?;
        } else if self.failure.is_none() || !self.records.is_empty() {
            return Err(invalid());
        }
        let mut root = None;
        let runner_root = self
            .runner
            .as_ref()
            .map(|runner| {
                crate::ContextReply::decode_observation(&runner.context_frame)
                    .map(|reply| reply.context.root_attempt)
            })
            .transpose()?;
        for (record, probe) in self.records.iter().zip(&batch.probes) {
            let prepared = &record.prepared;
            if prepared.root != probe.root
                || prepared.executable.path != probe.program
                || prepared.executable.sha256 != probe.program_sha256
                || record
                    .stdout
                    .len()
                    .checked_add(record.stderr.len())
                    .is_none_or(|n| n > METADATA_MAX_OUTPUT)
                || !attempts.insert(prepared.member_attempt)
                || root.is_some_and(|expected| expected != prepared.root_attempt)
                || runner_root.is_some_and(|expected| expected != prepared.root_attempt)
                || record.completion.finished.root_attempt != prepared.root_attempt
                || record.completion.finished.member_attempt != prepared.member_attempt
            {
                return Err(invalid());
            }
            root = Some(prepared.root_attempt);
            prepared.encode()?;
            record.completion.encode()?;
        }
        if let Some(frame) = &self.failure_started {
            frame.encode()?;
            if self.failure.is_none()
                || !matches!(frame.status, Status::Started(_))
                || root.is_some_and(|expected| expected != frame.root_attempt)
                || runner_root.is_some_and(|expected| expected != frame.root_attempt)
                || attempts.contains(&frame.member_attempt)
            {
                return Err(invalid());
            }
        }
        if let Some(observation) = &self.failure_observation {
            observation.validate()?;
            if self.failure.is_none()
                || self.records.len() >= batch.probes.len()
                || runner_root != Some(observation.root_attempt)
                || attempts.contains(&observation.member_attempt)
                || self.failure_started.as_ref().is_some_and(|frame| {
                    frame.root_attempt != observation.root_attempt
                        || frame.member_attempt != observation.member_attempt
                })
            {
                return Err(invalid());
            }
        }
        Ok(())
    }
    pub fn encode(&self, batch: &MetadataBatch) -> io::Result<Vec<u8>> {
        self.validate_for(batch)?;
        let mut e = Encoder::metadata_report();
        match &self.runner {
            None => e.number(0),
            Some(runner) => {
                e.number(1);
                runner.encode(&mut e)?;
            }
        }
        e.number(self.records.len() as u64);
        for record in &self.records {
            let prepared = &record.prepared;
            e.0.extend(prepared.root_attempt);
            e.0.extend(prepared.member_attempt);
            e.frame_bytes(&prepared.encode()?)?;
            let start = StatusFrame {
                root_attempt: prepared.root_attempt,
                member_attempt: prepared.member_attempt,
                status: Status::Started(record.started),
            };
            e.bytes(&start.encode()?)?;
            e.bytes(&record.completion.encode()?)?;
            e.bytes(&record.stdout)?;
            e.bytes(&record.stderr)?;
            e.number(u64::from(record.output_limit_exceeded));
        }
        match &self.failure {
            None => e.number(0),
            Some(reason) => {
                e.number(1);
                e.bytes(reason.as_bytes())?;
            }
        }
        match &self.failure_started {
            None => e.number(0),
            Some(frame) => {
                e.number(1);
                e.0.extend(frame.root_attempt);
                e.0.extend(frame.member_attempt);
                e.bytes(&frame.encode()?)?;
            }
        }
        // Absence emits exactly the original Report16 bytes. A present kind17
        // version1 annex is strictly report data, never a native lifecycle event.
        if let Some(observation) = &self.failure_observation {
            e.0.extend(observation.encode()?);
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], batch: &MetadataBatch) -> io::Result<Self> {
        let mut d = crate::wire::metadata_report_header(bytes)?;
        let runner = match d.number()? {
            0 => None,
            1 => Some(MetadataRunnerObservation::decode(&mut d)?),
            _ => return Err(invalid()),
        };
        let mut records = Vec::new();
        for _ in 0..d.count(MAX_PROBES)? {
            let root = d.array()?;
            let member = d.array()?;
            let prepared = MetadataPrepared::decode(&d.frame_bytes()?, root, member)?;
            let start = StatusFrame::decode(&d.bytes()?, root, member)?;
            let Status::Started(started) = start.status else {
                return Err(invalid());
            };
            let completion = MetadataCompletion::decode(&d.bytes()?, root, member)?;
            let stdout = d.bytes()?;
            let stderr = d.bytes()?;
            let output_limit_exceeded = match d.number()? {
                0 => false,
                1 => true,
                _ => return Err(invalid()),
            };
            records.push(MetadataResult {
                prepared,
                started,
                completion,
                stdout,
                stderr,
                output_limit_exceeded,
            });
        }
        let failure = match d.number()? {
            0 => None,
            1 => Some(d.text()?),
            _ => return Err(invalid()),
        };
        let failure_started = match d.number()? {
            0 => None,
            1 => {
                let root = d.array()?;
                let member = d.array()?;
                Some(StatusFrame::decode(&d.bytes()?, root, member)?)
            }
            _ => return Err(invalid()),
        };
        let failure_observation = if d.remaining().is_empty() {
            None
        } else {
            let value = MetadataFailureObservation::decode(d.remaining())?;
            d.take(d.remaining().len())?;
            Some(value)
        };
        d.done()?;
        let report = Self { runner, records, failure, failure_started, failure_observation };
        report.validate_for(batch)?;
        Ok(report)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Codec fixtures are data only. They never create a Client, host pin,
    // process, resource owner, keeper or admission capability.
    fn failed_report() -> (MetadataBatch, MetadataBatchReport) {
        use crate::{
            BirthKind, Context, ContextReply, Cpu, FileIdentity, Identity, Memory, SdkCustody,
            Subject,
        };
        let identity =
            Identity { pid: 42, birth: 123, birth_kind: BirthKind::MacosWallMicroseconds };
        let context = ContextReply {
            call_attempt: [9; 16],
            context: Context {
                session: "s-ab".into(),
                root_attempt: [1; 16],
                host: "host".into(),
                boot: "abcdef".into(),
                original_root: identity,
                subject: Subject::Root { identity },
                cpu: Cpu::RetainedFixed {
                    units: 1,
                    native_manifest: FileIdentity { device: 1, inode: 2 },
                },
                memory: Memory {
                    bytes: 1,
                    namespace: [2; 16],
                    marker: "1-2-3".into(),
                    epoch: [3; 16],
                    guard: FileIdentity { device: 1, inode: 4 },
                },
                sdk: Some(SdkCustody {
                    execution: b"/current".to_vec(),
                    build: 42,
                    lease_path: b"/current/in-use".to_vec(),
                    lease: FileIdentity { device: 1, inode: 5 },
                    inherited_fd: 5,
                }),
            },
        };
        let batch = MetadataBatch {
            host_store: None,
            service_program: b"/current/bin/targo".to_vec(),
            service_sha256: [8; 32],
            probes: vec![MetadataProbe {
                root: b"/sealed".to_vec(),
                program: b"/sealed/bin/program".to_vec(),
                program_sha256: [7; 32],
                command: MetadataProbeCommand::Sysroot,
                cwd: b"/sealed".to_vec(),
            }],
        };
        let report = MetadataBatchReport {
            runner: Some(MetadataRunnerObservation {
                root: b"/current".to_vec(),
                executable: MetadataFile {
                    path: batch.service_program.clone(),
                    sha256: batch.service_sha256,
                    bytes: 100,
                    device: 1,
                    inode: 2,
                },
                runtime: vec![],
                loader_paths: vec![],
                system_dependencies: vec![],
                policy: "observed-policy".into(),
                scope: "observed-scope".into(),
                identity,
                context_frame: context.encode().unwrap(),
            }),
            records: vec![],
            failure: Some("event stream closed before retirement".into()),
            failure_started: None,
            failure_observation: Some(MetadataFailureObservation {
                root_attempt: [1; 16],
                member_attempt: [3; 16],
                stdout: b"original\0bytes".to_vec(),
                stderr: vec![0xff],
                stdout_eof: true,
                stderr_eof: false,
                output_limit_exceeded: false,
                event_prefix: vec![0, 0, 0, 8, b'x', b'y'],
                event_bytes_seen: 6,
                capture_error: None,
            }),
        };
        (batch, report)
    }

    #[test]
    fn incomplete_report_annex_preserves_bytes_and_refuses_foreign_or_terminal_claims() {
        let (batch, report) = failed_report();
        let encoded = report.encode(&batch).unwrap();
        assert_eq!(MetadataBatchReport::decode(&encoded, &batch).unwrap(), report);
        assert!(SealedMetadataRequest::decode(&encoded).is_err());
        let mut old = report.clone();
        old.failure_observation = None;
        let old_bytes = old.encode(&batch).unwrap();
        assert_eq!(&encoded[..old_bytes.len()], old_bytes);
        assert_eq!(MetadataBatchReport::decode(&old_bytes, &batch).unwrap(), old);
        for change in 0..5 {
            let mut invalid = report.clone();
            match change {
                0 => invalid.failure = None,
                1 => invalid.failure_observation.as_mut().unwrap().root_attempt = [4; 16],
                2 => invalid.runner = None,
                3 => {
                    invalid.failure_started = Some(StatusFrame {
                        root_attempt: [1; 16],
                        member_attempt: [4; 16],
                        status: Status::Started(crate::Started {
                            identity: report.runner.as_ref().unwrap().identity,
                            monotonic_ns: 1,
                            unix_ns: 1,
                        }),
                    })
                }
                _ => {
                    invalid.failure_started = Some(StatusFrame {
                        root_attempt: [1; 16],
                        member_attempt: [3; 16],
                        status: Status::Attached,
                    })
                }
            }
            assert!(invalid.encode(&batch).is_err(), "accepted alteration {change}");
        }
        let mut duplicate = encoded.clone();
        duplicate.extend(report.failure_observation.as_ref().unwrap().encode().unwrap());
        assert!(MetadataBatchReport::decode(&duplicate, &batch).is_err());
        let mut trailing = encoded;
        trailing.push(0);
        assert!(MetadataBatchReport::decode(&trailing, &batch).is_err());
    }

    #[test]
    fn finite_aggregate_report_does_not_weaken_native_frame_bounds() {
        let (mut batch, mut report) = failed_report();
        let mut records = Vec::new();
        let probe = batch.probes[0].clone();
        batch.probes = vec![probe.clone(); MAX_PROBES];
        for index in 0..MAX_PROBES {
            let member = [index as u8 + 3; 16];
            let prepared = MetadataPrepared {
                root_attempt: [1; 16],
                member_attempt: member,
                root: probe.root.clone(),
                policy: "observed-policy".into(),
                scope: "observed-scope".into(),
                executable: MetadataFile {
                    path: probe.program.clone(),
                    sha256: probe.program_sha256,
                    bytes: 100,
                    device: 1,
                    inode: 2,
                },
                runtime: (0..128)
                    .map(|n| MetadataFile {
                        path: format!("/sealed/lib/{n:03}{}", "x".repeat(3900)).into_bytes(),
                        sha256: [5; 32],
                        bytes: 1,
                        device: 1,
                        inode: n + 10,
                    })
                    .collect(),
                loader_paths: vec![],
                system_dependencies: vec![],
                host: "host".into(),
                boot: "abcdef".into(),
            };
            let prepared_bytes = prepared.encode().unwrap();
            assert!(prepared_bytes.len() > MAX_FIELD && prepared_bytes.len() < MAX_PAYLOAD);
            records.push(MetadataResult {
                prepared,
                started: crate::Started {
                    identity: report.runner.as_ref().unwrap().identity,
                    monotonic_ns: 1,
                    unix_ns: 1,
                },
                completion: MetadataCompletion {
                    finished: StatusFrame {
                        root_attempt: [1; 16],
                        member_attempt: member,
                        status: Status::Finished {
                            outcome: crate::Outcome::Exit(0),
                            cause: crate::CompletionCause::Exited,
                            runtime_ns: 1,
                        },
                    },
                    inputs_unchanged: Ok(()),
                },
                stdout: vec![],
                stderr: vec![],
                output_limit_exceeded: false,
            });
        }
        report.records = records;
        report.failure = None;
        report.failure_observation = None;
        let bytes = report.encode(&batch).unwrap();
        assert!(bytes.len() > MAX_PAYLOAD && bytes.len() < METADATA_REPORT_MAX_BYTES);
        assert_eq!(MetadataBatchReport::decode(&bytes, &batch).unwrap(), report);
        assert!(
            crate::wire::header(&bytes, 16).is_err(),
            "ordinary native frame bound must stay unchanged"
        );
        let mut oversized = bytes;
        oversized.resize(METADATA_REPORT_MAX_BYTES + 1, 0);
        assert!(MetadataBatchReport::decode(&oversized, &batch).is_err());
    }
    #[test]
    fn batch_is_finite_lossless_closed_and_distinct_from_member_authority() {
        let probe = MetadataProbe {
            root: b"/sealed-\xff".to_vec(),
            program: b"/sealed-\xff/bin/program".to_vec(),
            program_sha256: [7; 32],
            command: MetadataProbeCommand::Sysroot,
            cwd: b"/sealed-\xff".to_vec(),
        };
        let batch = MetadataBatch {
            host_store: None,
            service_program: b"/current/bin/targo".to_vec(),
            service_sha256: [8; 32],
            probes: vec![probe.clone(); MAX_PROBES],
        };
        let bytes = batch.encode().unwrap();
        assert_eq!(MetadataBatch::decode(&bytes).unwrap(), batch);
        assert!(SealedMetadataRequest::decode(&bytes).is_err());
        for length in 0..bytes.len() {
            assert!(MetadataBatch::decode(&bytes[..length]).is_err());
        }
        let mut extra = bytes;
        extra.push(0);
        assert!(MetadataBatch::decode(&extra).is_err());
        assert!(MetadataBatch { probes: vec![], ..batch.clone() }.encode().is_err());
        assert!(
            MetadataBatch { probes: vec![probe; MAX_PROBES + 1], ..batch.clone() }
                .encode()
                .is_err()
        );
        assert!(
            MetadataBatchReport {
                runner: None,
                records: vec![],
                failure: None,
                failure_started: None,
                failure_observation: None
            }
            .encode(&batch)
            .is_err()
        );
        let report = MetadataBatchReport {
            runner: None,
            records: vec![],
            failure: Some("host refused before attachment".into()),
            failure_started: None,
            failure_observation: None,
        };
        assert_eq!(
            MetadataBatchReport::decode(&report.encode(&batch).unwrap(), &batch).unwrap(),
            report
        );
    }
}
