//! Trust: native bounded metadata service under an actual retained host root. This
//! owns no new pool or memory grant; the host retains the original capacity.

use std::ffi::OsString;
use std::fs::File;
use std::io::{Read as _, Write as _};
use std::os::fd::{AsFd as _, AsRawFd as _, BorrowedFd, FromRawFd as _, OwnedFd};
use std::os::unix::ffi::OsStringExt as _;
use std::os::unix::fs::MetadataExt as _;
use std::time::{Duration, Instant};

use anyhow::{Context as _, bail};
pub use trust_resource_controller::client::sdk::{capture_sdk_lease, snapshot_sdk_lease};
use trust_resource_controller::client::{Client, MetadataError, MetadataIo};
use trust_resource_controller::{
    BirthKind, CommandSpec, Context, ContextQuery, Cpu, Delegations, Descriptor, GnuTransport,
    Identity, JobBinding, METADATA_CAPABILITIES_JSON, METADATA_STARTUP_ARGUMENT, MetadataBatch,
    MetadataBatchReport, MetadataCpu, Request, Role, SealedMetadataRequest, Status, StatusFrame,
    Subject,
};

use crate::util::CargoResult;

const ROOT_LIFETIME: Duration = Duration::from_secs(600);
const MEMBER_LIFETIME: Duration = Duration::from_secs(120);
const HANDOFF: Duration = Duration::from_secs(20);

pub fn capabilities() -> &'static str {
    if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        METADATA_CAPABILITIES_JSON
    } else {
        r#"{"version":3,"sealed_metadata":null}"#
    }
}
pub fn requested(args: &[OsString]) -> bool {
    args.first()
        .is_some_and(|arg| arg == METADATA_STARTUP_ARGUMENT)
}

fn nonce() -> std::io::Result<[u8; 16]> {
    let mut bytes = [0; 16];
    // SAFETY: one bounded initialized writable buffer; the native entropy API
    // returns a real error instead of synthesizing an attempt on failure.
    if unsafe { libc::getentropy(bytes.as_mut_ptr().cast(), bytes.len()) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    if bytes == [0; 16] {
        return Err(std::io::Error::other("empty metadata attempt"));
    }
    Ok(bytes)
}
fn duplicate(source: BorrowedFd<'_>) -> std::io::Result<OwnedFd> {
    // SAFETY: new owned CLOEXEC description of the SAME original grant. Never
    // opens a resource path, creates credits, locks or changes the source.
    let raw = unsafe { libc::fcntl(source.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 5) };
    if raw < 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(unsafe { OwnedFd::from_raw_fd(raw) })
}
fn actual_producer() -> std::io::Result<Identity> {
    let actual = trust_resource_provenance::process::read_identity(std::process::id())?;
    Ok(Identity {
        pid: actual.pid,
        birth: actual.birth,
        birth_kind: if cfg!(target_os = "macos") {
            BirthKind::MacosWallMicroseconds
        } else {
            BirthKind::LinuxStartTicks
        },
    })
}
fn validate_root(context: &Context, producer: Identity) -> CargoResult<()> {
    if context.original_root != producer
        || context.subject != (Subject::Root { identity: producer })
        || !matches!(context.cpu, Cpu::RetainedFixed { units: 1, .. })
    {
        bail!(
            "metadata service requires its actual original retained fixed-one root; ancestor borrowing is unsupported, never replaced"
        );
    }
    trust_resource_controller::client::sdk::validate_sdk_keeper(context)
        .context("metadata service requires its actual original inherited SDK keeper")?;
    let sdk = context
        .sdk
        .as_ref()
        .context("native metadata service SDK context absent")?;
    let executable = std::env::current_exe()?.canonicalize()?;
    let sdk_root = std::path::PathBuf::from(OsString::from_vec(sdk.execution.clone()));
    if executable.parent().and_then(|bin| bin.parent()) != Some(sdk_root.as_path()) {
        bail!("metadata service executable differs from the actually inherited SDK root");
    }
    Ok(())
}

/// Actual service entry, before project/user configuration or ordinary lane
/// dispatch. Input is one finite regular file, never an unbounded pipe/prompt.
pub fn run(args: &[OsString]) -> CargoResult<()> {
    if args.len() != 1
        || !requested(args)
        || !cfg!(all(target_os = "macos", target_arch = "aarch64"))
    {
        bail!("unsupported native metadata service invocation or platform");
    }
    let until = Instant::now() + ROOT_LIFETIME;
    let mut input = File::from(std::io::stdin().as_fd().try_clone_to_owned()?);
    let before = input.metadata()?;
    if !before.is_file() || before.len() > trust_resource_controller::MAX_PAYLOAD as u64 {
        bail!("native metadata service requires a finite bounded regular input file");
    }
    let mut bytes = Vec::new();
    (&mut input)
        .take(trust_resource_controller::MAX_PAYLOAD as u64 + 1)
        .read_to_end(&mut bytes)?;
    let after = input.metadata()?;
    if bytes.len() as u64 != before.len()
        || before.dev() != after.dev()
        || before.ino() != after.ino()
        || before.len() != after.len()
        || before.mtime() != after.mtime()
        || before.mtime_nsec() != after.mtime_nsec()
        || before.ctime() != after.ctime()
        || before.ctime_nsec() != after.ctime_nsec()
    {
        bail!("native metadata batch input changed while reading");
    }
    let batch = MetadataBatch::decode(&bytes).context("invalid finite native metadata batch")?;
    let discovery_until = (Instant::now() + HANDOFF).min(until);
    let client = match &batch.host_store {
        None => Client::discover(discovery_until),
        Some(path) => Client::discover_at(&std::path::PathBuf::from(OsString::from_vec(path.clone())),discovery_until),
    }.context("native metadata service cannot authenticate its explicitly selected original host; no fallback")?;
    let report = execute(client, &batch, until)?;
    let output = report.encode(&batch)?;
    std::io::stdout().lock().write_all(&output)?;
    std::io::stdout().lock().flush()?;
    if report.failure.is_some() {
        bail!("native metadata batch refused; retained report includes completed observations");
    }
    Ok(())
}

/// Shared real execution path for the CLI and actual host-owned private-store
/// qualification. A supplied Client still authenticates native peer/ancestry;
/// no decoded Context or caller-supplied CPU count can construct this owner.
#[expect(
    clippy::disallowed_methods,
    reason = "read the actual inherited native root locator before Targo configuration exists"
)]
pub fn execute(
    client: Client,
    batch: &MetadataBatch,
    until: Instant,
) -> CargoResult<MetadataBatchReport> {
    batch.encode()?;
    let binding = JobBinding::from_locator(
        &std::env::var("ATERM_RESOURCE_JOB_V3")
            .context("native metadata service has no original root locator")?,
    )?;
    let query = ContextQuery {
        binding: binding.clone(),
        call_attempt: nonce()?,
    };
    let reply = client
        .metadata_context(&query, (Instant::now() + HANDOFF).min(until))
        .context("native metadata SDK context negotiation refused; no fallback")?;
    let context = &reply.context;
    validate_root(context, actual_producer()?)?;
    let sdk = context
        .sdk
        .as_ref()
        .context("metadata service SDK absent")?;
    let program = std::path::PathBuf::from(OsString::from_vec(batch.service_program.clone()));
    if program != std::env::current_exe()?.canonicalize()? {
        bail!("metadata batch selected a different service executable");
    }
    let held = trust_resource_provenance::program::HeldProgram::open(
        &std::path::PathBuf::from(OsString::from_vec(sdk.execution.clone())),
        &program,
        &batch.service_sha256,
        until,
    )?;
    held.validate_loaded(
        trust_resource_provenance::process::read_identity(std::process::id())?,
        until,
    )?;
    fn file_observation(
        file: &trust_resource_provenance::program::FileObservation,
    ) -> CargoResult<trust_resource_controller::MetadataFile> {
        let mut sha256 = [0; 32];
        hex::decode_to_slice(&file.sha256, &mut sha256)?;
        Ok(trust_resource_controller::MetadataFile {
            path: file.path.as_os_str().as_encoded_bytes().to_vec(),
            sha256,
            bytes: file.bytes,
            device: file.device,
            inode: file.inode,
        })
    }
    let input = held.observation();
    let runner = trust_resource_controller::MetadataRunnerObservation {
        root: held.root().as_os_str().as_encoded_bytes().to_vec(),
        executable: file_observation(&input.executable)?,
        runtime: input
            .runtime
            .iter()
            .map(file_observation)
            .collect::<CargoResult<Vec<_>>>()?,
        loader_paths: input
            .loader_paths
            .iter()
            .map(|p| p.as_os_str().as_encoded_bytes().to_vec())
            .collect(),
        system_dependencies: input.system_dependencies.clone(),
        policy: input.policy.into(),
        scope: input.scope.into(),
        identity: actual_producer()?,
        context_frame: reply.encode()?,
    };
    let jobserver = crate::context::inherited_metadata_jobserver()?;
    let pipe = jobserver
        .pipe_descriptors()
        .context("metadata service lacks original numeric GNU descriptions")?;
    // This live owner and authenticated context remain in this stack through
    // all members, cancellations and actual drain. The host checks the real
    // pipe backing against its own original owner, not these descriptor IDs.
    let mut report = MetadataBatchReport {
        runner: Some(runner),
        records: Vec::new(),
        failure: None,
        failure_started: None,
        failure_observation: None,
    };
    for probe in &batch.probes {
        let prepared = (|| -> CargoResult<_> {
            let descriptions = vec![duplicate(pipe[0].as_fd())?, duplicate(pipe[1].as_fd())?];
            let read = Descriptor {
                source: descriptions[0].as_raw_fd() as u32,
                target: 3,
            };
            let write = Descriptor {
                source: descriptions[1].as_raw_fd() as u32,
                target: 4,
            };
            let request = SealedMetadataRequest {
                member: Request {
                    binding: binding.clone(),
                    member_attempt: nonce()?,
                    role: Role::SealedMetadata,
                    command: CommandSpec {
                        program: probe.program.clone(),
                        arg0: None,
                        args: probe.command.arguments(),
                        environment: vec![
                            (b"LANG".to_vec(), b"C".to_vec()),
                            (b"LC_ALL".to_vec(), b"C".to_vec()),
                        ],
                        cwd: probe.cwd.clone(),
                    },
                    delegations: Delegations {
                        cpu: None,
                        gnu: GnuTransport::NumericPipe { read, write },
                        fences: vec![],
                    },
                    timeout_ns: Some(trust_resource_controller::METADATA_MAX_TIMEOUT_NS),
                },
                cpu: MetadataCpu::FixedBorrow,
                root: probe.root.clone(),
                program_sha256: probe.program_sha256,
            };
            request.encode()?;
            Ok((descriptions, request))
        })();
        let (descriptions, request) = match prepared {
            Ok(prepared) => prepared,
            Err(error) => {
                report.failure = Some(format!(
                    "metadata request preparation failed before delivery: {error}"
                ));
                break;
            }
        };
        let member_until = (Instant::now() + MEMBER_LIFETIME).min(until);
        let mut member = match client.metadata(
            &request,
            MetadataIo { descriptions },
            (Instant::now() + HANDOFF).min(member_until),
        ) {
            Ok(member) => member,
            Err(MetadataError::Unknown { mut member, error }) => {
                let _ = member.cancel((Instant::now() + Duration::from_secs(1)).min(until));
                report.failure = Some(format!(
                    "unknown native metadata attachment; never retry: {error}"
                ));
                report.failure_started = member.started().map(|started| StatusFrame {
                    root_attempt: binding.root_attempt,
                    member_attempt: request.member.member_attempt,
                    status: Status::Started(started),
                });
                report.failure_observation = member.take_failure_observation();
                break;
            }
            Err(error) => {
                report.failure = Some(error.to_string());
                break;
            }
        };
        loop {
            match member.poll(member_until) {
                Ok(Some(result)) => {
                    let invalid = result.output_limit_exceeded
                        || result.completion.inputs_unchanged.is_err()
                        || !matches!(
                            result.completion.finished.status,
                            Status::Finished {
                                outcome: trust_resource_controller::Outcome::Exit(0),
                                cause: trust_resource_controller::CompletionCause::Exited,
                                ..
                            }
                        );
                    report.records.push(result);
                    if invalid {
                        report.failure=Some("native metadata exited unsuccessfully, exceeded output bound or changed its original inputs".into());
                    }
                    break;
                }
                Ok(None) => std::thread::sleep(Duration::from_millis(5)),
                Err(error) => {
                    let _ = member.cancel((Instant::now() + Duration::from_secs(1)).min(until));
                    report.failure = Some(format!(
                        "native metadata lifecycle unavailable; never retry: {error}"
                    ));
                    report.failure_started = member.started().map(|started| StatusFrame {
                        root_attempt: binding.root_attempt,
                        member_attempt: request.member.member_attempt,
                        status: Status::Started(started),
                    });
                    report.failure_observation = member.take_failure_observation();
                    break;
                }
            }
        }
        if report.failure.is_some() {
            break;
        }
    }
    // Refuse persistent SDK-context drift before returning even
    // observational output. No source identity or release claim is inferred.
    if let Err(error) = trust_resource_controller::client::sdk::validate_sdk_keeper(context)
        .and_then(|()| held.validate(until))
    {
        report.failure = Some(format!(
            "{}; final inherited SDK keeper check failed: {error}",
            report
                .failure
                .as_deref()
                .unwrap_or("metadata observations collected")
        ));
    }
    report.validate_for(batch)?;
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_resource_controller::{FileIdentity, Memory, SdkCustody};

    #[test]
    fn decoded_counts_and_sdk_observations_cannot_create_a_funded_root() {
        let producer = actual_producer().unwrap();
        let (host, boot) = trust_resource_provenance::process::host_boot().unwrap();
        let context = Context {
            session: "s-ab".into(),
            root_attempt: [1; 16],
            host,
            boot,
            original_root: producer,
            subject: Subject::Root { identity: producer },
            cpu: Cpu::RetainedFixed {
                units: 1,
                native_manifest: FileIdentity {
                    device: 1,
                    inode: 2,
                },
            },
            memory: Memory {
                bytes: 1024 * 1024 * 1024,
                namespace: [2; 16],
                marker: "1-2-3".into(),
                epoch: [3; 16],
                guard: FileIdentity {
                    device: 1,
                    inode: 4,
                },
            },
            sdk: Some(SdkCustody {
                execution: b"/invented-sdk".to_vec(),
                build: 42,
                lease_path: b"/invented-lease".to_vec(),
                lease: FileIdentity {
                    device: 1,
                    inode: 5,
                },
                inherited_fd: 5,
            }),
        };
        assert!(
            validate_root(&context, producer)
                .unwrap_err()
                .to_string()
                .contains("actual original inherited SDK keeper")
        );
        for change in 0..4 {
            let mut changed = context.clone();
            match change {
                0 => {
                    changed.cpu = Cpu::CooperativeShared {
                        ceiling: 7,
                        native_manifest: FileIdentity {
                            device: 1,
                            inode: 2,
                        },
                    }
                }
                1 => {
                    changed.cpu = Cpu::RetainedFixed {
                        units: 7,
                        native_manifest: FileIdentity {
                            device: 1,
                            inode: 2,
                        },
                    }
                }
                2 => {
                    changed.subject = Subject::RegisteredMember {
                        identity: producer,
                        attempt: [9; 16],
                    }
                }
                3 => changed.original_root.pid += 1,
                _ => unreachable!(),
            }
            assert!(
                validate_root(&changed, producer)
                    .unwrap_err()
                    .to_string()
                    .contains("original retained fixed-one root")
            );
        }
    }

    #[test]
    fn duplicate_retains_the_original_pipe_and_never_mutates_source_inheritance() {
        let (reader, writer) = std::io::pipe().unwrap();
        let flags = unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_GETFD) };
        let retained = duplicate(writer.as_fd()).unwrap();
        assert_eq!(
            unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_GETFD) },
            flags
        );
        assert_ne!(
            unsafe { libc::fcntl(retained.as_raw_fd(), libc::F_GETFD) } & libc::FD_CLOEXEC,
            0
        );
        drop(writer);
        let mut poll = libc::pollfd {
            fd: reader.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        assert_eq!(
            unsafe { libc::poll(&mut poll, 1, 0) },
            0,
            "copied original writer must remain live"
        );
        drop(retained);
        assert_eq!(unsafe { libc::poll(&mut poll, 1, 0) }, 1);
        assert_ne!(poll.revents & libc::POLLHUP, 0);
    }
}
