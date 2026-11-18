//! One original root/SDK/GNU owner, installed before configuration. Only
//! separately admitted closed non-producing compiler queries may execute.
use crate::util::{CargoResult, GlobalContext};
use anyhow::{Context as _, bail};
use cargo_util::{ExecStats, ProcessBuilder, ProcessExecutor, StreamingOutputLimits};
use std::ffi::OsString;
use std::fs::File;
use std::io::{self, Read as _, Write as _};
use std::os::fd::{AsFd as _, AsRawFd as _, BorrowedFd, FromRawFd as _, OwnedFd};
use std::os::unix::{
    ffi::{OsStrExt as _, OsStringExt as _},
    fs::MetadataExt as _,
    process::ExitStatusExt as _,
};
use std::path::PathBuf;
use std::process::{ExitStatus, Output};
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicBool, Ordering},
};
use std::time::{Duration, Instant};
use trust_resource_controller::{
    BirthKind, CommandSpec, CompletionCause, Context, ContextQuery, Cpu, Delegations, Descriptor,
    GnuTransport, Identity, JobBinding, MetadataFile, MetadataResult, MetadataRunnerObservation,
    Outcome, Request, Role, Status, StatusFrame, Subject,
    client::{Client, MetadataError, MetadataIo, MetadataMember},
    resolver::*,
};
use trust_resource_provenance::program::HeldProgram;
const ROOT_LIFETIME: Duration = Duration::from_secs(600);
const HANDOFF: Duration = Duration::from_secs(20);
const MEMBER_LIFETIME: Duration = Duration::from_secs(90);
fn bounded_reason(message: impl Into<String>) -> String {
    let mut value = message.into();
    if value.len() > 4000 {
        let mut end = 3900;
        while !value.is_char_boundary(end) {
            end -= 1;
        }
        value.truncate(end);
        value.push_str(" [reason truncated; original process bytes remain separately retained]");
    }
    value
}
fn error(message: impl Into<String>) -> io::Error {
    io::Error::other(message.into())
}
fn nonce() -> io::Result<[u8; 16]> {
    let mut out = [0; 16];
    // SAFETY: the kernel writes exactly this initialized bounded array.
    if unsafe { libc::getentropy(out.as_mut_ptr().cast(), out.len()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    if out == [0; 16] {
        return Err(error("native resolver has no real attempt nonce"));
    }
    Ok(out)
}
fn duplicate(source: BorrowedFd<'_>) -> io::Result<OwnedFd> {
    // SAFETY: duplicate ownership of this SAME live original description only.
    let raw = unsafe { libc::fcntl(source.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 5) };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { OwnedFd::from_raw_fd(raw) })
}
fn actual_producer() -> io::Result<Identity> {
    let id = trust_resource_provenance::process::read_identity(std::process::id())?;
    Ok(Identity {
        pid: id.pid,
        birth: id.birth,
        birth_kind: if cfg!(target_os = "macos") {
            BirthKind::MacosWallMicroseconds
        } else {
            BirthKind::LinuxStartTicks
        },
    })
}
pub fn requested(args: &[OsString]) -> bool {
    args.first().is_some_and(|a| a == RESOLVER_STARTUP_ARGUMENT)
}
fn path(bytes: &[u8]) -> PathBuf {
    PathBuf::from(OsString::from_vec(bytes.to_vec()))
}
#[expect(
    clippy::disallowed_methods,
    reason = "validate the actual inherited request-bound environment before configuration overlays"
)]
fn root_environment(inv: &ResolverInvocation) -> CargoResult<()> {
    for (name, value) in [
        ("CARGO_HOME", inv.cargo_home.as_slice()),
        ("CARGO", inv.program.as_slice()),
        ("RUSTC", inv.compiler.as_slice()),
        ("CARGO_CACHE_RUSTC_INFO", b"0"),
    ] {
        if std::env::var_os(name).as_deref().map(|v| v.as_bytes()) != Some(value) {
            bail!("native resolver lacks exact request-bound {name}");
        }
    }
    if std::env::current_dir()?
        .canonicalize()?
        .as_os_str()
        .as_bytes()
        != inv.cwd
    {
        bail!("native resolver root cwd differs from invocation");
    }
    Ok(())
}
fn validate_root(
    context: &Context,
    producer: Identity,
    inv: &ResolverInvocation,
) -> CargoResult<()> {
    if context.original_root != producer
        || context.subject != (Subject::Root { identity: producer })
        || !matches!(context.cpu, Cpu::RetainedFixed { units: 1, .. })
    {
        bail!("resolver requires its actual original retained fixed-one root");
    }
    trust_resource_controller::client::sdk::validate_sdk_keeper(context)
        .context("resolver requires original target SDK keeper")?;
    if context
        .sdk
        .as_ref()
        .is_none_or(|sdk| sdk.execution != inv.root)
        || std::env::current_exe()?.canonicalize()? != path(&inv.program)
    {
        bail!("resolver cannot substitute service SDK or a different Targo executable");
    }
    Ok(())
}
fn observed_file(
    file: &trust_resource_provenance::program::FileObservation,
) -> CargoResult<MetadataFile> {
    let mut sha256 = [0; 32];
    hex::decode_to_slice(&file.sha256, &mut sha256)?;
    Ok(MetadataFile {
        path: file.path.as_os_str().as_bytes().to_vec(),
        sha256,
        bytes: file.bytes,
        device: file.device,
        inode: file.inode,
    })
}
struct State {
    queries: Vec<ResolverQueryObservation>,
    pending: Vec<MetadataMember>,
    failure: Option<String>,
}
struct Owner {
    invocation: ResolverInvocation,
    client: Client,
    binding: JobBinding,
    context: Context,
    targo: HeldProgram,
    compiler: HeldProgram,
    jobserver: cargo_util::Jobserver,
    runner: MetadataRunnerObservation,
    until: Instant,
    poisoned: AtomicBool,
    state: Mutex<State>,
}
impl Owner {
    #[expect(
        clippy::disallowed_methods,
        reason = "authenticate the actual inherited resolver root locator before configuration"
    )]
    fn prepare(
        invocation: ResolverInvocation,
        client: Client,
        until: Instant,
    ) -> CargoResult<Arc<Self>> {
        invocation.validate()?;
        root_environment(&invocation)?;
        let binding = JobBinding::from_locator(
            &std::env::var("ATERM_RESOURCE_JOB_V3")
                .context("resolver has no original root locator")?,
        )?;
        let reply = client.resolver_context(
            &ContextQuery {
                binding: binding.clone(),
                call_attempt: nonce()?,
            },
            (Instant::now() + HANDOFF).min(until),
        )?;
        validate_root(&reply.context, actual_producer()?, &invocation)?;
        let targo = HeldProgram::open(
            &path(&invocation.root),
            &path(&invocation.program),
            &invocation.program_sha256,
            until,
        )?;
        targo.require_resolver_protocol_marker(&RESOLVER_PROTOCOL_MARKER, until)?;
        targo.validate_loaded(
            trust_resource_provenance::process::read_identity(std::process::id())?,
            until,
        )?;
        let compiler = HeldProgram::open(
            &path(&invocation.root),
            &path(&invocation.compiler),
            &invocation.compiler_sha256,
            until,
        )?;
        let input = targo.observation();
        let runner = MetadataRunnerObservation {
            root: invocation.root.clone(),
            executable: observed_file(&input.executable)?,
            runtime: input
                .runtime
                .iter()
                .map(observed_file)
                .collect::<CargoResult<_>>()?,
            loader_paths: input
                .loader_paths
                .iter()
                .map(|p| p.as_os_str().as_bytes().to_vec())
                .collect(),
            system_dependencies: input.system_dependencies.clone(),
            policy: input.policy.into(),
            scope: input.scope.into(),
            identity: actual_producer()?,
            context_frame: reply.encode()?,
        };
        let jobserver = crate::context::inherited_metadata_jobserver()?;
        jobserver
            .pipe_descriptors()
            .context("resolver requires actual original GNU pipe")?;
        Ok(Arc::new(Self {
            invocation,
            client,
            binding,
            context: reply.context,
            targo,
            compiler,
            jobserver,
            runner,
            until,
            poisoned: AtomicBool::new(false),
            state: Mutex::new(State {
                queries: Vec::new(),
                pending: Vec::new(),
                failure: None,
            }),
        }))
    }
    fn revalidate(&self) -> io::Result<()> {
        trust_resource_controller::client::sdk::validate_sdk_keeper(&self.context)?;
        self.targo.validate(self.until)?;
        self.compiler.validate(self.until)
    }
    fn fail(&self, reason: impl Into<String>) -> io::Error {
        let reason = bounded_reason(reason);
        self.poisoned.store(true, Ordering::Release);
        if let Ok(mut state) = self.state.try_lock() {
            state.failure.get_or_insert(reason.clone());
        }
        error(reason)
    }
    fn command(
        &self,
        process: &ProcessBuilder,
    ) -> io::Result<(CommandSpec, Vec<(Vec<u8>, Vec<u8>)>, Vec<Vec<u8>>)> {
        let actual = process.build_command();
        let mut observed = Vec::new();
        let mut omitted = Vec::new();
        for (name, value) in process.get_effective_envs()? {
            let name = name.as_os_str().as_bytes().to_vec();
            if private_environment_channel(&name) {
                omitted.push(name);
            } else {
                observed.push((name, value.as_os_str().as_bytes().to_vec()));
            }
        }
        let command = CommandSpec {
            program: actual.get_program().as_bytes().to_vec(),
            arg0: process.get_arg0().map(|s| s.as_bytes().to_vec()),
            args: actual.get_args().map(|a| a.as_bytes().to_vec()).collect(),
            environment: vec![
                (b"LANG".to_vec(), b"C".to_vec()),
                (b"LC_ALL".to_vec(), b"C".to_vec()),
                (b"CARGO".to_vec(), self.invocation.program.clone()),
                (b"RUSTC".to_vec(), self.invocation.compiler.clone()),
                (b"CARGO_HOME".to_vec(), self.invocation.cargo_home.clone()),
                (b"CARGO_CACHE_RUSTC_INFO".to_vec(), b"0".to_vec()),
            ],
            cwd: process
                .get_cwd()
                .unwrap_or(&path(&self.invocation.cwd))
                .as_os_str()
                .as_bytes()
                .to_vec(),
        };
        Ok((command, observed, omitted))
    }
    fn validate_process(&self, process: &ProcessBuilder, command: &CommandSpec) -> io::Result<()> {
        validate_process_profile(&self.invocation, process, command)?;
        let environment = process
            .get_effective_envs()?
            .into_iter()
            .filter_map(|(name, value)| {
                (!private_environment_channel(name.as_os_str().as_bytes())).then(|| {
                    (
                        name.as_os_str().as_bytes().to_vec(),
                        value.as_os_str().as_bytes().to_vec(),
                    )
                })
            })
            .collect::<Vec<_>>();
        validate_effective_environment(
            &self.invocation,
            &environment,
            &self.compiler.runtime_environment()?,
        )?;
        self.revalidate()
    }
    fn execute(&self, process: &ProcessBuilder) -> io::Result<Output> {
        if self.poisoned.load(Ordering::Acquire) {
            return Err(error("resolver is poisoned; no further dispatch"));
        }
        let mut state = self
            .state
            .try_lock()
            .map_err(|_| self.fail("resolver fixed-one root cannot dispatch concurrent queries"))?;
        if state.queries.len() >= RESOLVER_MAX_QUERIES {
            return Err(self.fail("resolver exceeds finite query population"));
        }
        let (command, observed_environment, omitted_environment) = match self.command(process) {
            Ok(v) => v,
            Err(e) => {
                self.poisoned.store(true, Ordering::Release);
                state.failure = Some(e.to_string());
                return Err(e);
            }
        };
        let mut observation = ResolverQueryObservation {
            command,
            observed_environment,
            omitted_environment,
            member_attempt: nonce()?,
            result: None,
            failure_started: None,
            failure_observation: None,
            failure: None,
        };
        let outcome = (|| -> io::Result<Output> {
            self.validate_process(process, &observation.command)?;
            let pipe = self
                .jobserver
                .pipe_descriptors()
                .ok_or_else(|| error("original GNU pipe unavailable"))?;
            let descriptions = vec![duplicate(pipe[0].as_fd())?, duplicate(pipe[1].as_fd())?];
            let request = SealedResolverQueryRequest {
                member: Request {
                    binding: self.binding.clone(),
                    member_attempt: observation.member_attempt,
                    role: Role::ResolverQuery,
                    command: observation.command.clone(),
                    delegations: Delegations {
                        cpu: None,
                        fences: vec![],
                        gnu: GnuTransport::NumericPipe {
                            read: Descriptor {
                                source: descriptions[0].as_raw_fd() as u32,
                                target: 3,
                            },
                            write: Descriptor {
                                source: descriptions[1].as_raw_fd() as u32,
                                target: 4,
                            },
                        },
                    },
                    timeout_ns: Some(RESOLVER_MAX_QUERY_NS),
                },
                root: self.invocation.root.clone(),
                program_sha256: self.invocation.compiler_sha256,
            };
            request.validate()?;
            let until = (Instant::now() + MEMBER_LIFETIME).min(self.until);
            if self.poisoned.load(Ordering::Acquire) {
                return Err(error("resolver poisoned before delivery"));
            }
            let mut member = match self.client.resolver_query(
                &request,
                MetadataIo { descriptions },
                (Instant::now() + HANDOFF).min(until),
            ) {
                Ok(member) => member,
                Err(MetadataError::Unknown { mut member, error }) => {
                    let _ =
                        member.cancel((Instant::now() + Duration::from_secs(1)).min(self.until));
                    observation.failure_started = member.started().map(|started| StatusFrame {
                        root_attempt: self.binding.root_attempt,
                        member_attempt: observation.member_attempt,
                        status: Status::Started(started),
                    });
                    observation.failure_observation = member.take_failure_observation();
                    state.pending.push(*member);
                    return Err(error);
                }
                Err(error) => return Err(io::Error::other(error.to_string())),
            };
            loop {
                match member.poll(until) {
                    Ok(Some(result)) => {
                        let actual = actual_output(&result);
                        observation.result = Some(result);
                        self.revalidate()?;
                        return actual;
                    }
                    Ok(None) => {
                        if process
                            .execution_cancellation()
                            .as_ref()
                            .is_some_and(|cancel| cancel.load(Ordering::Acquire))
                        {
                            let _ = member
                                .cancel((Instant::now() + Duration::from_secs(1)).min(self.until));
                        }
                        std::thread::sleep(Duration::from_millis(5));
                    }
                    Err(error) => {
                        let _ = member
                            .cancel((Instant::now() + Duration::from_secs(1)).min(self.until));
                        observation.failure_started = member.started().map(|started| StatusFrame {
                            root_attempt: self.binding.root_attempt,
                            member_attempt: observation.member_attempt,
                            status: Status::Started(started),
                        });
                        observation.failure_observation = member.take_failure_observation();
                        state.pending.push(member);
                        return Err(error);
                    }
                }
            }
        })();
        let outcome = match (outcome, self.revalidate()) {
            (outcome, Ok(())) => outcome,
            (_, Err(error)) => Err(error),
        };
        if let Err(error) = &outcome {
            observation.failure = Some(bounded_reason(error.to_string()));
            self.poisoned.store(true, Ordering::Release);
            state
                .failure
                .get_or_insert(bounded_reason(error.to_string()));
        }
        if outcome
            .as_ref()
            .is_ok_and(|output| !output.status.success())
        {
            let reason = "actual resolver query exited unsuccessfully".to_owned();
            observation.failure = Some(reason.clone());
            self.poisoned.store(true, Ordering::Release);
            state.failure.get_or_insert(reason);
        }
        state.queries.push(observation);
        outcome
    }
    fn report(
        &self,
        metadata: Option<Vec<u8>>,
        failure: Option<String>,
    ) -> CargoResult<ResolverReport> {
        let check = self
            .revalidate()
            .err()
            .map(|e| format!("original resolver SDK/program input changed: {e}"));
        let mut state = self
            .state
            .lock()
            .map_err(|_| error("resolver observation owner poisoned"))?;
        let mut failures = Vec::new();
        if let Some(check) = check {
            failures.push(bounded_reason(check));
        }
        if let Some(failure) = failure {
            failures.push(bounded_reason(failure));
        }
        if let Some(failure) = &state.failure {
            failures.push(bounded_reason(failure.clone()));
        }
        if self.poisoned.load(Ordering::Acquire) {
            failures
                .push("resolver query lifecycle poisoned; captured bytes are ineligible".into());
        }
        let failure = if failures.is_empty() {
            None
        } else {
            Some(bounded_reason(failures.join("; ")))
        };
        let report = ResolverReport {
            invocation: self.invocation.clone(),
            runner: Some(self.runner.clone()),
            queries: std::mem::take(&mut state.queries),
            metadata,
            failure,
        };
        report.validate_for(&self.invocation)?;
        Ok(report)
    }
}
fn validate_process_profile(
    invocation: &ResolverInvocation,
    process: &ProcessBuilder,
    command: &CommandSpec,
) -> io::Result<()> {
    crate::native_query_profile::validate_process_profile(
        &crate::native_query_profile::Profile::resolver(invocation),
        process,
        command,
    )
}
fn validate_effective_environment(
    invocation: &ResolverInvocation,
    environment: &[(Vec<u8>, Vec<u8>)],
    runtime: &[(OsString, OsString)],
) -> io::Result<()> {
    crate::native_query_profile::validate_effective_environment(
        &crate::native_query_profile::Profile::resolver(invocation),
        environment,
        runtime,
    )
}
#[cfg(test)]
fn darwin_default_encoding(value: &[u8], uid: u32, euid: u32, darwin: bool) -> bool {
    crate::native_query_profile::darwin_default_encoding(value, uid, euid, darwin)
}
fn actual_output(result: &MetadataResult) -> io::Result<Output> {
    if result.output_limit_exceeded || result.completion.inputs_unchanged.is_err() {
        return Err(error(
            "resolver query exceeded bound or changed original inputs",
        ));
    }
    let Status::Finished {
        outcome,
        cause: CompletionCause::Exited,
        ..
    } = result.completion.finished.status
    else {
        return Err(error(
            "resolver query has no normal positively retired exit",
        ));
    };
    let status = match outcome {
        Outcome::Exit(code) => ExitStatus::from_raw(
            code.checked_mul(256)
                .ok_or_else(|| error("invalid native resolver exit"))?,
        ),
        Outcome::Signal(signal) => ExitStatus::from_raw(signal),
    };
    Ok(Output {
        status,
        stdout: result.stdout.clone(),
        stderr: result.stderr.clone(),
    })
}
impl ProcessExecutor for Owner {
    fn output(&self, p: &ProcessBuilder) -> io::Result<Output> {
        self.execute(p)
    }
    fn status(&self, p: &ProcessBuilder) -> io::Result<ExitStatus> {
        self.execute(p)
            .and_then(|output| p.report_captured_status(output))
    }
    fn streaming(
        &self,
        _p: &ProcessBuilder,
        _stdout: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        _stderr: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        _capture: bool,
        _limits: Option<StreamingOutputLimits>,
        _rusage: bool,
    ) -> (ExecStats, anyhow::Result<Output>) {
        (
            ExecStats::default(),
            Err(self
                .fail("resolver refuses streaming/configured external execution")
                .into()),
        )
    }
}
fn metadata() -> CargoResult<Vec<u8>> {
    let mut gctx = GlobalContext::default()?;
    gctx.configure(0, false, None, false, true, true, &None, &[], &[])?;
    let manifest = crate::util::important_paths::find_root_manifest_for_wd(gctx.cwd())?;
    let ws = crate::workspace::Workspace::new(&manifest, &gctx)?;
    let options = crate::ops::OutputMetadataOptions {
        cli_features: crate::resolver::CliFeatures::from_command_line(&[], false, true)?,
        no_deps: false,
        version: 1,
        filter_platforms: vec![],
    };
    let output = crate::ops::output_metadata(&ws, &options)?;
    // Same compact serde JSON plus newline as normal Shell::print_json.
    let mut bytes = serde_json::to_vec(&output)?;
    bytes.push(b'\n');
    if bytes.len() > RESOLVER_MAX_METADATA {
        bail!("normal full metadata exceeds resolver output bound");
    }
    Ok(bytes)
}
/// The lane callback is the CLI's canonical normal metadata initialization. It
/// runs exactly once after mandatory execution ownership is installed.
pub fn run(
    args: &[OsString],
    initialize_metadata_lane: fn() -> CargoResult<()>,
) -> CargoResult<()> {
    if args.len() != 1
        || !requested(args)
        || !cfg!(all(target_os = "macos", target_arch = "aarch64"))
    {
        bail!("unsupported native resolver entry or runtime profile");
    }
    let until = Instant::now() + ROOT_LIFETIME;
    let mut input = File::from(std::io::stdin().as_fd().try_clone_to_owned()?);
    let before = input.metadata()?;
    if !before.is_file() || before.len() > trust_resource_controller::MAX_PAYLOAD as u64 {
        bail!("resolver requires finite regular invocation data");
    }
    let mut bytes = Vec::new();
    (&mut input)
        .take(trust_resource_controller::MAX_PAYLOAD as u64 + 1)
        .read_to_end(&mut bytes)?;
    let after = input.metadata()?;
    if before.dev() != after.dev()
        || before.ino() != after.ino()
        || before.len() != after.len()
        || before.len() != bytes.len() as u64
        || before.mtime() != after.mtime()
        || before.mtime_nsec() != after.mtime_nsec()
        || before.ctime() != after.ctime()
        || before.ctime_nsec() != after.ctime_nsec()
    {
        bail!("original resolver invocation input changed");
    }
    let invocation = ResolverInvocation::decode(&bytes)?;
    root_environment(&invocation)?;
    let client = match &invocation.host_store {
        None => Client::discover((Instant::now() + HANDOFF).min(until)),
        Some(store) => Client::discover_at(&path(store), (Instant::now() + HANDOFF).min(until)),
    }?;
    let owner = Owner::prepare(invocation, client, until)?;
    cargo_util::install_process_executor(owner.clone())?;
    let outcome = initialize_metadata_lane().and_then(|()| metadata());
    let (metadata, failure) = match outcome {
        Ok(bytes) => (Some(bytes), None),
        Err(error) => (
            None,
            Some(format!("normal full metadata failed: {error:#}")),
        ),
    };
    let report = owner.report(metadata, failure)?;
    let output = report.encode()?;
    std::io::stdout().lock().write_all(&output)?;
    std::io::stdout().lock().flush()?;
    if report.failure.is_some() {
        bail!("native resolver failed; original observations remain in its report");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normal_query_owner_keeps_original_scheduler_and_executor_refusal() {
        use std::ffi::OsStr;
        use std::sync::atomic::AtomicUsize;

        struct Refuse {
            calls: AtomicUsize,
            original_makeflags: OsString,
        }
        impl ProcessExecutor for Refuse {
            fn status(&self, _: &ProcessBuilder) -> io::Result<std::process::ExitStatus> {
                panic!("compiler query must use captured output")
            }
            fn output(&self, process: &ProcessBuilder) -> io::Result<Output> {
                self.calls.fetch_add(1, Ordering::SeqCst);
                assert!(process.has_jobserver());
                assert_eq!(
                    process
                        .get_effective_envs()?
                        .get(OsStr::new("CARGO_MAKEFLAGS")),
                    Some(&self.original_makeflags)
                );
                Err(io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    "retained resolver fixture refused delivery",
                ))
            }
            fn streaming(
                &self,
                _: &ProcessBuilder,
                _: &mut dyn FnMut(&str) -> CargoResult<()>,
                _: &mut dyn FnMut(&str) -> CargoResult<()>,
                _: bool,
                _: Option<StreamingOutputLimits>,
                _: bool,
            ) -> (ExecStats, CargoResult<Output>) {
                panic!("compiler query must use captured output")
            }
        }

        let directory = tempfile::tempdir().unwrap();
        let fallback = directory.path().join("local-spawned");
        let original = cargo_util::Jobserver::new(2).unwrap();
        let held = original.client().acquire().unwrap();
        let mut command = ProcessBuilder::new("/bin/sh");
        command
            .args(&["-c", "touch \"$1\"", "sh"])
            .arg(&fallback)
            .inherit_jobserver(&original);
        let original_makeflags = command
            .get_effective_envs()
            .unwrap()
            .get(OsStr::new("CARGO_MAKEFLAGS"))
            .unwrap()
            .clone();
        let executor = Arc::new(Refuse {
            calls: AtomicUsize::new(0),
            original_makeflags,
        });
        command.process_executor(executor.clone());
        let failure = crate::context::compiler_query::output(&command).unwrap_err();
        assert!(format!("{failure:#}").contains("retained resolver fixture refused delivery"));
        assert_eq!(executor.calls.load(Ordering::SeqCst), 1);
        assert!(
            !fallback.exists(),
            "a refused hosted query must never spawn locally"
        );
        assert_eq!(original.client().available().unwrap(), 1);
        drop(held);
        assert_eq!(original.client().available().unwrap(), 2);
    }

    fn invocation() -> ResolverInvocation {
        ResolverInvocation {
            host_store: None,
            root: b"/sealed".to_vec(),
            program: b"/sealed/bin/targo".to_vec(),
            program_sha256: [1; 32],
            compiler: b"/sealed/bin/trustc".to_vec(),
            compiler_sha256: [2; 32],
            cwd: b"/source".to_vec(),
            cargo_home: b"/cargo".to_vec(),
        }
    }
    fn process() -> ProcessBuilder {
        let mut value = ProcessBuilder::new("/sealed/bin/trustc");
        value
            .arg("--print=sysroot")
            .cwd("/source")
            .env("CARGO", "/sealed/bin/targo");
        value
    }
    fn observed(process: &ProcessBuilder) -> CommandSpec {
        let command = process.build_command();
        CommandSpec {
            program: command.get_program().as_bytes().to_vec(),
            args: command.get_args().map(|a| a.as_bytes().to_vec()).collect(),
            arg0: process.get_arg0().map(|a| a.as_bytes().to_vec()),
            environment: vec![],
            cwd: process.get_cwd().unwrap().as_os_str().as_bytes().to_vec(),
        }
    }
    #[test]
    fn actual_process_builder_profile_refuses_wrappers_backend_config_environment_and_producing_stdin()
     {
        let inv = invocation();
        assert!(validate_process_profile(&inv, &process(), &observed(&process())).is_ok());
        for change in 0..7 {
            let mut p = process();
            match change {
                0 => {
                    p.arg("--emit=link");
                }
                1 => {
                    p.arg("-Zcodegen-backend=/foreign");
                }
                2 => {
                    p.env("DYLD_INSERT_LIBRARIES", "/foreign");
                }
                3 => {
                    p.arg0("wrapper");
                }
                4 => {
                    p.cwd("/other-source");
                }
                5 => {
                    p.stdin(b"producing Rust source".to_vec());
                }
                _ => {
                    p = p.wrapped(Some(std::path::Path::new("/external/wrapper")));
                }
            }
            assert!(
                validate_process_profile(&inv, &p, &observed(&p)).is_err(),
                "change {change}"
            );
        }
    }
    #[test]
    fn private_entry_is_exact_and_invocation_marker_never_selects_a_legacy_role() {
        assert!(requested(&[RESOLVER_STARTUP_ARGUMENT.into()]));
        assert!(!requested(&[
            trust_resource_controller::METADATA_STARTUP_ARGUMENT.into()
        ]));
        assert!(!requested(&["metadata".into()]));
        assert!(!requested(&[]));
        assert_eq!(RESOLVER_REQUEST_ROLE, 5);
        assert_eq!(trust_resource_controller::METADATA_REQUEST_ROLE, 3);
        assert_eq!(trust_resource_controller::MACHO_LINKER_REQUEST_ROLE, 4);
    }
    #[test]
    fn inherited_managed_semantics_are_refused_and_fixed_root_inputs_are_forwarded_exactly() {
        let inv = invocation();
        let mut environment = vec![
            (b"LANG".to_vec(), b"C".to_vec()),
            (b"LC_ALL".to_vec(), b"C".to_vec()),
            (b"CARGO".to_vec(), inv.program.clone()),
            (b"RUSTC".to_vec(), inv.compiler.clone()),
            (b"CARGO_HOME".to_vec(), inv.cargo_home.clone()),
            (b"CARGO_CACHE_RUSTC_INFO".to_vec(), b"0".to_vec()),
        ];
        assert!(validate_effective_environment(&inv, &environment, &[]).is_ok());
        environment.push((
            b"RUSTUP_TOOLCHAIN".to_vec(),
            b"different compiler semantics".to_vec(),
        ));
        assert!(validate_effective_environment(&inv, &environment, &[]).is_err());
        environment.pop();
        environment[3].1 = b"/different/bin/trustc".to_vec();
        assert!(validate_effective_environment(&inv, &environment, &[]).is_err());
        environment[3].1 = inv.compiler.clone();
        environment[5].1 = b"1".to_vec();
        assert!(validate_effective_environment(&inv, &environment, &[]).is_err());
        environment[5].1 = b"0".to_vec();
        environment.push((b"DYLD_LIBRARY_PATH".to_vec(), b"/sealed/lib".to_vec()));
        let runtime = vec![(
            OsString::from("DYLD_LIBRARY_PATH"),
            OsString::from("/sealed/lib"),
        )];
        assert!(validate_effective_environment(&inv, &environment, &runtime).is_ok());
        environment.last_mut().unwrap().1 = b"/foreign/lib".to_vec();
        assert!(validate_effective_environment(&inv, &environment, &runtime).is_err());
        assert!(RESOLVER_CAPABILITIES_JSON.contains(RESOLVER_QUERY_ENVIRONMENT));
    }
    #[test]
    fn darwin_encoding_is_exact_uid_bound_zero_default_and_other_cf_semantics_refuse() {
        assert!(darwin_default_encoding(b"0x1F5:0x0:0x0", 501, 501, true));
        assert!(darwin_default_encoding(b"0x1F5:0:0", 501, 501, true));
        for value in [
            b"0x1F6:0x0:0x0".as_slice(),
            b"0x1F5:0x1:0x0",
            b"0x1F5:0x0:0x1",
            b"0x1f5:0x0:0x0",
            b"0x1F5:0x0:0x0\n",
            b"0x1F5:0x0:0x0:0",
            b"0x1F5:0x0:0x0\0",
        ] {
            assert!(!darwin_default_encoding(value, 501, 501, true));
        }
        assert!(!darwin_default_encoding(b"0x1F5:0x0:0x0", 501, 502, true));
        assert!(!darwin_default_encoding(b"0x1F5:0x0:0x0", 501, 501, false));
        let inv = invocation();
        let mut environment = vec![
            (b"LANG".to_vec(), b"C".to_vec()),
            (b"LC_ALL".to_vec(), b"C".to_vec()),
            (b"CARGO".to_vec(), inv.program.clone()),
            (b"RUSTC".to_vec(), inv.compiler.clone()),
            (b"CARGO_HOME".to_vec(), inv.cargo_home.clone()),
            (b"CARGO_CACHE_RUSTC_INFO".to_vec(), b"0".to_vec()),
        ];
        environment.push((b"__CF_ARBITRARY_SEMANTICS".to_vec(), b"0".to_vec()));
        assert!(validate_effective_environment(&inv, &environment, &[]).is_err());
    }
    #[cfg(target_os = "macos")]
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "test actor observes its real inherited selector and the native CoreFoundation environment"
    )]
    fn darwin_encoding_runtime_actor() {
        if std::env::var_os("TRUST_RESOLVER_CF_RUNTIME_ACTOR").as_deref()
            != Some(std::ffi::OsStr::new("1"))
        {
            return;
        }
        #[link(name = "CoreFoundation", kind = "framework")]
        unsafe extern "C" {
            fn CFStringGetSystemEncoding() -> u32;
        }
        // SAFETY: read-only system CoreFoundation API; ensures the same runtime
        // framework constructor is linked into this test-only native actor.
        let system = unsafe { CFStringGetSystemEncoding() };
        let value = std::env::var_os("__CF_USER_TEXT_ENCODING")
            .expect("clean CF runtime should publish its encoding");
        let uid = unsafe { libc::getuid() };
        let euid = unsafe { libc::geteuid() };
        assert!(darwin_default_encoding(
            value.as_os_str().as_bytes(),
            uid,
            euid,
            true
        ));
        println!(
            "actual-darwin-runtime uid={uid} euid={euid} system={system} encoding={}",
            value.to_string_lossy()
        );
    }
    #[cfg(target_os = "macos")]
    #[test]
    fn actual_clean_native_framework_recreates_only_supported_default_encoding() {
        #[allow(
            clippy::disallowed_types,
            reason = "actual native runtime actor; not production execution or admission"
        )]
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "resolver_service::supported::tests::darwin_encoding_runtime_actor",
                "--nocapture",
            ])
            .env_clear()
            .env("LANG", "C")
            .env("LC_ALL", "C")
            .env("TRUST_RESOLVER_CF_RUNTIME_ACTOR", "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "native CF actor failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("actual-darwin-runtime uid="));
        print!("{}", String::from_utf8_lossy(&output.stdout));
    }
}
