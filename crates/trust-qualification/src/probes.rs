//! Actual compiler metadata is diagnostic consistency, not build/source/proof
//! authentication. This stage retains and rebinds the original input owner.

use std::path::Path;

use serde_json::{Value, json};
use trust_resource_controller::{
    CompletionCause, MetadataBatch, MetadataBatchReport, MetadataProbe, MetadataProbeCommand,
    MetadataResult, Outcome, Status,
};

use crate::pair::{FileIdentity, Snapshot};
use crate::receipts::ReceiptCheckedPair;
use crate::{Git, Result, canonical_hex, refusal, tree};

pub const PENDING_STAGES: &[&str] = crate::pair::PENDING_STAGES.split_at(2).1;

/// The concrete frontend owns native program/admission/process custody. Saved
/// reports and a test implementor cannot construct a resource grant here.
pub trait MetadataRunner {
    fn service_image(&self) -> Result<FileIdentity>;
    fn collect(&mut self, batch: &MetadataBatch) -> Result<MetadataBatchReport>;
    fn execution_observation(&self) -> Option<Value> {
        None
    }
}

/// Retains the same owner on success AND failure, including failed partial
/// native observations. There is no constructor/deserializer from a report.
pub struct ProbeAttempt {
    pair: ReceiptCheckedPair,
    service: Option<FileIdentity>,
    batch: Option<MetadataBatch>,
    observations: Option<MetadataBatchReport>,
    errors: Vec<String>,
    execution: Option<Value>,
}

fn sha_bytes(text: &str) -> Result<[u8; 32]> {
    if !canonical_hex(text, 64) {
        return Err(refusal("noncanonical expected executable SHA256"));
    }
    let mut bytes = [0; 32];
    for (index, pair) in text.as_bytes().as_chunks::<2>().0.iter().enumerate() {
        let digit = |b: u8| if b <= b'9' { b - b'0' } else { b - b'a' + 10 };
        bytes[index] = digit(pair[0]) * 16 + digit(pair[1]);
    }
    Ok(bytes)
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn frame_observation(frame: std::io::Result<Vec<u8>>) -> Value {
    match frame {
        Ok(bytes) => json!({"hex":hex(&bytes),"sha256":tree::hash_bytes(&bytes)}),
        Err(error) => json!({"encoding_refused":error.to_string()}),
    }
}

pub fn batch(snapshot: &Snapshot, service: &FileIdentity) -> Result<MetadataBatch> {
    let mut probes = Vec::new();
    for toolchain in [&snapshot.control, &snapshot.candidate] {
        for (tool, command) in [
            ("trustc", MetadataProbeCommand::VerboseVersion),
            ("trustc", MetadataProbeCommand::Sysroot),
            ("targo", MetadataProbeCommand::UnverifiedVersion),
        ] {
            let image = toolchain
                .executables
                .get(tool)
                .ok_or_else(|| refusal("sealed tool executable absent"))?;
            probes.push(MetadataProbe {
                root: tree::path_bytes(&toolchain.path),
                program: tree::path_bytes(&image.path),
                program_sha256: sha_bytes(&image.sha256)?,
                command,
                cwd: tree::path_bytes(&toolchain.path),
            });
        }
    }
    let batch = MetadataBatch {
        host_store: None,
        service_program: tree::path_bytes(&service.resolved_path),
        service_sha256: sha_bytes(&service.sha256)?,
        probes,
    };
    batch.encode()?;
    Ok(batch)
}

fn compiler_version(bytes: &[u8], commit: &str) -> Result<()> {
    let text =
        std::str::from_utf8(bytes).map_err(|_| refusal("compiler version output is not UTF8"))?;
    let commits =
        text.lines().filter_map(|line| line.strip_prefix("commit-hash: ")).collect::<Vec<_>>();
    if commits != [commit] || !text.contains("trust:") {
        return Err(refusal("compiler does not report exactly the sealed Trust commit"));
    }
    Ok(())
}
fn sysroot(bytes: &[u8], expected: &Path) -> Result<()> {
    let text = std::str::from_utf8(bytes)
        .map_err(|_| refusal("compiler sysroot output is not UTF8"))?
        .trim();
    let path = Path::new(text);
    if !path.is_absolute() || std::fs::canonicalize(path)? != expected {
        return Err(refusal("compiler resolves a different sysroot"));
    }
    Ok(())
}
fn genuine_targo(bytes: &[u8]) -> Result<()> {
    let text =
        std::str::from_utf8(bytes).map_err(|_| refusal("native Targo version is not UTF8"))?;
    if !text.starts_with("targo ") {
        return Err(refusal("sealed targo did not report native Targo after --unverified"));
    }
    Ok(())
}

fn validate_record(
    record: &MetadataResult,
    command: MetadataProbeCommand,
    expected_commit: &str,
    expected_root: &Path,
) -> Result<()> {
    if record.output_limit_exceeded
        || record.completion.inputs_unchanged.is_err()
        || !matches!(
            record.completion.finished.status,
            Status::Finished { outcome: Outcome::Exit(0), cause: CompletionCause::Exited, .. }
        )
    {
        return Err(refusal("native metadata probe did not complete unchanged within its limits"));
    }
    match command {
        MetadataProbeCommand::VerboseVersion => compiler_version(&record.stdout, expected_commit),
        MetadataProbeCommand::Sysroot => sysroot(&record.stdout, expected_root),
        MetadataProbeCommand::UnverifiedVersion => genuine_targo(&record.stdout),
    }
}

fn validate_observations(
    snapshot: &Snapshot,
    batch: &MetadataBatch,
    report: &MetadataBatchReport,
) -> Result<()> {
    report.validate_for(batch)?;
    if let Some(failure) = &report.failure {
        return Err(refusal(format!("native metadata service refused: {failure}")));
    }
    for (index, record) in report.records.iter().enumerate() {
        let toolchain = if index < 3 { &snapshot.control } else { &snapshot.candidate };
        validate_record(
            record,
            batch.probes[index].command,
            &toolchain.reported_commit,
            &toolchain.path,
        )?;
    }
    Ok(())
}

impl ReceiptCheckedPair {
    /// Rebind before any probe AND after every outcome, including refusal or
    /// unknown transport. The execution owner never comes from saved bytes.
    pub fn probe_compilers(self, git: &impl Git, runner: &mut impl MetadataRunner) -> ProbeAttempt {
        let mut attempt = ProbeAttempt {
            pair: self,
            service: None,
            batch: None,
            observations: None,
            errors: Vec::new(),
            execution: None,
        };
        let run = (|| -> Result<()> {
            attempt.pair.check_unchanged(git)?;
            let service = runner.service_image()?;
            let batch = batch(attempt.pair.snapshot(), &service)?;
            attempt.service = Some(service.clone());
            attempt.batch = Some(batch.clone());
            let observations = runner.collect(&batch);
            attempt.execution = runner.execution_observation();
            let after_service = runner.service_image();
            if let Err(error) = &after_service {
                attempt.errors.push(format!("service image after probes: {error}"));
            }
            if after_service.as_ref().is_ok_and(|after| after != &service) {
                attempt.errors.push("native metadata service image changed during probes".into());
            }
            // Save the actual native result before any consistency/drift check.
            attempt.observations = Some(observations?);
            validate_observations(
                attempt.pair.snapshot(),
                &batch,
                attempt
                    .observations
                    .as_ref()
                    .ok_or_else(|| refusal("native metadata observations absent"))?,
            )
        })();
        if let Err(error) = run {
            attempt.errors.push(error.to_string());
        }
        if let Err(error) = attempt.pair.check_unchanged(git) {
            attempt.errors.push(format!("original inputs after metadata probes: {error}"));
        }
        attempt
    }
}

impl ProbeAttempt {
    /// Preserve the original pair and complete compiler observations across the
    /// next native stage. A failed compiler probe never calls a resolver.
    pub fn resolve_dependencies(
        self,
        git: &impl Git,
        runner: &mut impl crate::dependencies::DependencyResolver,
    ) -> crate::dependencies::DependencyAttempt {
        let report = self.report();
        let consistent = self.consistent();
        crate::dependencies::DependencyAttempt::run(self.pair, report, consistent, git, runner)
    }

    pub fn consistent(&self) -> bool {
        self.errors.is_empty()
    }
    pub fn report(&self) -> Value {
        let metadata=self.observations.as_ref().map(|report| {
            let runner=report.runner.as_ref().map(|runner|json!({
                "program":runner.executable.path,"sha256":hex(&runner.executable.sha256),"device":runner.executable.device,"inode":runner.executable.inode,
                "runtime_files":runner.runtime.iter().map(|file|json!({"path":file.path,"sha256":hex(&file.sha256),"bytes":file.bytes,"device":file.device,"inode":file.inode})).collect::<Vec<_>>(),
                "scope":runner.scope,"policy":runner.policy,"loader_paths":runner.loader_paths,"system_dependencies":runner.system_dependencies,
                "pid":runner.identity.pid,"birth":runner.identity.birth,"context_frame_hex":hex(&runner.context_frame),"context_frame_sha256":tree::hash_bytes(&runner.context_frame)}));
            let records=report.records.iter().map(|record|json!({
                "prepared_frame":frame_observation(record.prepared.encode()),
                "pid":record.started.identity.pid,"birth":record.started.identity.birth,
                "started_monotonic_ns":record.started.monotonic_ns,"started_unix_ns":record.started.unix_ns,
                "completion_frame":frame_observation(record.completion.encode()),
                "stdout_hex":hex(&record.stdout),"stdout_sha256":tree::hash_bytes(&record.stdout),
                "stderr_hex":hex(&record.stderr),"stderr_sha256":tree::hash_bytes(&record.stderr),
                "output_limit_exceeded":record.output_limit_exceeded})).collect::<Vec<_>>();
            let incomplete=report.failure_observation.as_ref().map(|observation|json!({
                "scope":"bounded original failed-exchange stream observations; no terminal, exit, retirement or proof authority",
                "root_attempt":hex(&observation.root_attempt),"member_attempt":hex(&observation.member_attempt),
                "stdout_hex":hex(&observation.stdout),"stderr_hex":hex(&observation.stderr),
                "stdout_eof":observation.stdout_eof,"stderr_eof":observation.stderr_eof,
                "output_limit_exceeded":observation.output_limit_exceeded,
                "native_event_prefix_hex":hex(&observation.event_prefix),
                "native_event_bytes_seen":observation.event_bytes_seen,
                "native_event_prefix_truncated":observation.event_prefix_truncated(),
                "capture_error":observation.capture_error}));
            json!({"runner":runner,"records":records,"failure":report.failure,
                "incomplete_member_observation":incomplete,
                "incomplete_member_started_frame":report.failure_started.as_ref().map(|frame|frame_observation(frame.encode()))})
        });
        json!({"schema":"trust.paired-qualification.v1","stage":"compiler-metadata-probes",
            "status":if self.consistent() {"compiler-metadata-checked"} else {"refused"},
            "claim_scope":"diagnostic compiler metadata consistency and held input observations only; actual execution facts are recorded separately when present; no source/build authentication, proof, workload qualification or publication authority; frontend Git preparation is outside probe admission",
            "pending_stages":if self.consistent(){PENDING_STAGES}else{crate::receipts::PENDING_STAGES},"receipts":self.pair.report(),"service_image_observation":self.service,
            "batch_frame_sha256":self.batch.as_ref().and_then(|batch|batch.encode().ok()).map(|bytes|tree::hash_bytes(&bytes)),
            "metadata":metadata,"execution":self.execution,"errors":self.errors})
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The actual host fixture supplies immutable original request/report bytes.
    /// This replays the diagnostic consumer only: saved data supplies no live
    /// host, resource owner, completed pair or proof authority.
    #[cfg(unix)]
    #[test]
    #[ignore = "requires an explicitly selected genuine native host capture and SDK commit"]
    fn actual_captured_metadata_uses_production_consistency_policy() {
        use std::io::Read as _;
        use std::os::unix::ffi::OsStringExt as _;

        let read_path = |path: &Path, limit: usize| {
            let mut bytes = Vec::new();
            std::fs::File::open(path)
                .unwrap()
                .take(limit as u64 + 1)
                .read_to_end(&mut bytes)
                .unwrap();
            assert!(bytes.len() <= limit);
            bytes
        };
        let request_path = std::env::var_os("TRUST_METADATA_CAPTURE_REQUEST")
            .expect("explicit original request file");
        let output_path = std::env::var_os("TRUST_METADATA_CAPTURE_REPORT")
            .expect("explicit original report file");
        let capture = Path::new(&output_path).parent().unwrap();
        let request = read_path(Path::new(&request_path), trust_resource_controller::MAX_PAYLOAD);
        let output = read_path(
            Path::new(&output_path),
            trust_resource_controller::METADATA_REPORT_MAX_BYTES,
        );
        let commit = std::env::var("TRUST_METADATA_CAPTURE_EXPECTED_COMMIT")
            .expect("independently selected SDK source commit");
        assert!(canonical_hex(&commit, 40));
        let batch = MetadataBatch::decode(&request).unwrap();
        let report = MetadataBatchReport::decode(&output, &batch).unwrap();
        assert_eq!(
            report.encode(&batch).unwrap(),
            output,
            "original successful Report16 bytes must remain unchanged"
        );
        assert!(report.failure.is_none(), "{:?}", report.failure);
        assert!(report.runner.is_some());
        assert_eq!(batch.probes.len(), 3);
        assert_eq!(report.records.len(), 3);
        for (index, command) in [
            MetadataProbeCommand::VerboseVersion,
            MetadataProbeCommand::Sysroot,
            MetadataProbeCommand::UnverifiedVersion,
        ]
        .into_iter()
        .enumerate()
        {
            assert_eq!(batch.probes[index].command, command);
            assert_eq!(batch.probes[index].root, batch.probes[0].root);
        }
        let root =
            std::path::PathBuf::from(std::ffi::OsString::from_vec(batch.probes[0].root.clone()));
        assert_eq!(root.canonicalize().unwrap(), root);
        for (probe, record) in batch.probes.iter().zip(&report.records) {
            validate_record(record, probe.command, &commit, &root).unwrap();
            use trust_resource_controller::{MetadataEvent, SealedMetadataRequest, StatusFrame};
            let stem = format!("member-{}", hex(&record.prepared.member_attempt));
            let original_request = read_path(
                &capture.join(format!("{stem}.request12")),
                trust_resource_controller::MAX_PAYLOAD,
            );
            let member = SealedMetadataRequest::decode(&original_request).unwrap();
            assert_eq!(member.member.command.args, probe.command.arguments());
            record.prepared.validate_for(&member).unwrap();
            let events = read_path(
                &capture.join(format!("{stem}.events")),
                4 * (trust_resource_controller::MAX_PAYLOAD + 4),
            );
            let mut remaining = events.as_slice();
            let mut decoded = Vec::new();
            while !remaining.is_empty() {
                assert!(decoded.len() < 4, "extra original host event");
                let length =
                    u32::from_be_bytes(remaining.get(..4).unwrap().try_into().unwrap()) as usize;
                assert!(length <= trust_resource_controller::MAX_PAYLOAD);
                let body = remaining.get(4..4 + length).unwrap();
                decoded.push(
                    MetadataEvent::decode(
                        body,
                        record.prepared.root_attempt,
                        record.prepared.member_attempt,
                    )
                    .unwrap(),
                );
                remaining = &remaining[4 + length..];
            }
            let status = |status| StatusFrame {
                root_attempt: record.prepared.root_attempt,
                member_attempt: record.prepared.member_attempt,
                status,
            };
            assert_eq!(
                decoded,
                [
                    MetadataEvent::Status(status(Status::Attached)),
                    MetadataEvent::Prepared(record.prepared.clone()),
                    MetadataEvent::Status(status(Status::Started(record.started))),
                    MetadataEvent::Completed(record.completion.clone()),
                ]
            );
        }

        let mut different_commit = commit.clone();
        different_commit.replace_range(..1, if commit.starts_with('0') { "1" } else { "0" });
        assert!(
            validate_record(
                &report.records[0],
                MetadataProbeCommand::VerboseVersion,
                &different_commit,
                &root,
            )
            .unwrap_err()
            .to_string()
            .contains("sealed Trust commit")
        );
        let foreign = tempfile::tempdir().unwrap();
        assert!(
            validate_record(
                &report.records[1],
                MetadataProbeCommand::Sysroot,
                &commit,
                &foreign.path().canonicalize().unwrap(),
            )
            .unwrap_err()
            .to_string()
            .contains("different sysroot")
        );
        // Real compiler output cannot be relabeled as native Targo output.
        assert!(
            validate_record(
                &report.records[0],
                MetadataProbeCommand::UnverifiedVersion,
                &commit,
                &root,
            )
            .unwrap_err()
            .to_string()
            .contains("native Targo")
        );

        for cause in
            [CompletionCause::Timeout, CompletionCause::Cancelled, CompletionCause::ResourceLimit, CompletionCause::HostFault]
        {
            let mut altered = report.records[0].clone();
            let Status::Finished { cause: actual, .. } = &mut altered.completion.finished.status
            else {
                panic!("actual native capture lacks its Finished outcome")
            };
            *actual = cause;
            assert!(
                validate_record(&altered, MetadataProbeCommand::VerboseVersion, &commit, &root,)
                    .is_err()
            );
        }
        for drift in [false, true] {
            let mut altered = report.records[0].clone();
            if drift {
                altered.completion.inputs_unchanged = Err("negative input drift".into());
            } else {
                altered.output_limit_exceeded = true;
            }
            assert!(
                validate_record(&altered, MetadataProbeCommand::VerboseVersion, &commit, &root,)
                    .is_err()
            );
        }
        eprintln!(
            "actual metadata consumer request_sha256={} report_sha256={} expected_commit={} root={} baseline_records=3 original_member_requests=3 original_host_events=12 negative_controls=8; saved-data consistency only",
            tree::hash_bytes(&request),
            tree::hash_bytes(&output),
            commit,
            root.display()
        );
    }

    #[test]
    fn compiler_commit_label_requires_one_exact_trust_commit() {
        let commit = "a".repeat(40);
        let valid = format!("trust: 1.99\ncommit-hash: {commit}\n");
        compiler_version(valid.as_bytes(), &commit).unwrap();
        for invalid in [
            format!("rustc: 1.99\ncommit-hash: {commit}\n"),
            format!("{valid}commit-hash: {commit}\n"),
            format!("trust: 1.99\ncommit-hash: {}\n", "b".repeat(40)),
        ] {
            assert!(compiler_version(invalid.as_bytes(), &commit).is_err());
        }
        assert!(compiler_version(&[0xff], &commit).is_err());
    }
    #[test]
    fn sysroot_and_native_targo_controls_refuse_empty_relative_and_foreign_output() {
        let root = tempfile::tempdir().unwrap();
        let root = root.path().canonicalize().unwrap();
        sysroot(root.as_os_str().as_encoded_bytes(), &root).unwrap();
        for invalid in [b"".as_slice(), b".", b"/", b"\xff"] {
            assert!(sysroot(invalid, &root).is_err());
        }
        genuine_targo(b"targo 1.99.0 (native)\n").unwrap();
        for invalid in [b"cargo 1.99".as_slice(), b"", b"\xff"] {
            assert!(genuine_targo(invalid).is_err());
        }
    }
}
