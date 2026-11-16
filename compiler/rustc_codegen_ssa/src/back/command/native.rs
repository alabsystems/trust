//! Direct hosted linker ownership; no helper process is spawned by the compiler.
use std::collections::BTreeMap;
use std::io::{self, Read};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::process::ExitStatusExt;
use std::process::{ExitStatus, Output};
use std::sync::Arc;
use std::time::{Duration, Instant};

use rustc_data_structures::jobserver::{CompilerPause, NativeV3};
use rustc_target::spec::LldFlavor;
use trust_resource_controller::client::{LinkerError, LinkerMember, LinkerOutcome, MetadataIo};
use trust_resource_controller::{
    CommandSpec, CompletionCause, Delegations, Descriptor, GnuTransport, Loan, Outcome, Request,
    Role, Status, Subject,
};

use super::{Command, Program};

struct Delivery(bool);
impl Drop for Delivery {
    fn drop(&mut self) {
        if self.0 {
            lost();
        }
    }
}
fn lost() -> ! {
    // SAFETY: terminate this process without unwinding or reusing a borrowed
    // implicit unit whose target retirement is not positively established.
    unsafe { libc::_exit(75) }
}
fn refused(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, message.into())
}
fn attempt() -> io::Result<[u8; 16]> {
    let mut value = [0; 16];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut value)?;
    if value == [0; 16] {
        return Err(refused("native linker attempt generation failed"));
    }
    Ok(value)
}
fn primary(pause: &CompilerPause) -> io::Result<OwnedFd> {
    // SAFETY: pause retains this live original lease. Duplicate into a fresh
    // CLOEXEC slot >=5, never replace a parent descriptor or reconstruct a lock.
    let fd = unsafe { libc::fcntl(pause.cpu().as_raw_fd(), libc::F_DUPFD_CLOEXEC, 5) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful fcntl returned a new descriptor owned only here.
    Ok(unsafe { OwnedFd::from_raw_fd(fd) })
}
pub(super) fn command_spec(command: &Command) -> io::Result<CommandSpec> {
    if !matches!(command.program, Program::Lld(_, LldFlavor::Ld64)) || command.resources.is_some() {
        return Err(refused("native linking requires the paired Darwin LLD phase"));
    }
    let native = command.command();
    let mut environment =
        if command.env_clear { BTreeMap::new() } else { std::env::vars_os().collect() };
    for (name, value) in native.get_envs() {
        if let Some(value) = value {
            environment.insert(name.to_owned(), value.to_owned());
        } else {
            environment.remove(name);
        }
    }
    let mut args: Vec<Vec<u8>> = native.get_args().map(|value| value.as_bytes().to_vec()).collect();
    // Trust: final cap strings alone do not prove effective worker limits:
    // a preceding option can consume them. The private paired image must run
    // its maintained MachOOptTable guard before creating workers or inputs.
    args.extend([
        b"--threads=1".to_vec(),
        b"--thinlto-jobs=1".to_vec(),
        b"--read-workers=0".to_vec(),
    ]);
    Ok(CommandSpec {
        program: native.get_program().as_bytes().to_vec(),
        arg0: None,
        args,
        environment: environment
            .into_iter()
            .map(|(key, value)| (key.into_vec(), value.into_vec()))
            .collect(),
        cwd: std::env::current_dir()?.into_os_string().into_vec(),
    })
}
fn pause(context: &Arc<NativeV3>) -> io::Result<CompilerPause> {
    // The caller is the built-in backend's post-join linker path. This retry
    // only drains transient unpublished offers, never substitutes for that join.
    let deadline = Instant::now() + Duration::from_secs(8);
    loop {
        if let Some(pause) = context.try_pause()? {
            return Ok(pause);
        }
        if Instant::now() >= deadline {
            return Err(refused("native compiler work did not become quiescent before linking"));
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

pub(crate) struct Child {
    // FIRST: unresolved delivery exits before the pause/original backing drops.
    delivery: Delivery,
    pause: Option<CompilerPause>,
    member: LinkerMember,
}
impl Child {
    pub(super) fn spawn(command: &Command, context: Arc<NativeV3>) -> io::Result<Self> {
        let Subject::RegisteredMember { attempt: parent_attempt, .. } = context.context().subject
        else {
            return Err(refused("only a registered compiler member may lend a linker unit"));
        };
        let command = command_spec(command)?;
        let sdk = context
            .context()
            .sdk
            .as_ref()
            .ok_or_else(|| refused("native linker original SDK is unavailable"))?;
        // Observation only. The host independently retains and validates the
        // SAME original SDK; this pathname cannot construct that authority.
        let root = std::path::Path::new(std::ffi::OsStr::from_bytes(&sdk.execution))
            .canonicalize()?
            .into_os_string()
            .into_vec();
        let member_attempt = attempt()?;
        let nonce = attempt()?;
        let pause = pause(&context)?;
        let source = match primary(&pause) {
            Ok(source) => source,
            Err(error) => {
                pause.resume()?;
                return Err(error);
            }
        };
        let request = Request {
            binding: context.binding().clone(),
            member_attempt,
            role: Role::MachOLinker(Loan { parent_attempt, nonce, cpu_slot: pause.cpu().slot() }),
            command,
            delegations: Delegations {
                cpu: Some(Descriptor { source: source.as_raw_fd() as u32, target: 5 }),
                gnu: GnuTransport::None,
                fences: vec![],
            },
            timeout_ns: None,
        };
        let request = trust_resource_controller::linker::Request { member: request, root };
        let io = MetadataIo { descriptions: vec![source] };
        let mut delivery = Delivery(true);
        // SAFETY: this is the built-in backend's post-join path. The original
        // pause retains the exact authenticated primary and excludes all
        // workers until positive host retirement. Unknown terminates before
        // that custody drops; no local helper/fork or execution retry exists.
        match unsafe {
            context.controller().linker_loan(&request, io, Instant::now() + Duration::from_secs(8))
        } {
            Ok(member) => Ok(Self { delivery, pause: Some(pause), member }),
            Err(LinkerError::BeforeRequest(error)) => {
                delivery.0 = false;
                pause.resume()?;
                // Never turn a transport's E2BIG into opaque linker-argument replay.
                Err(refused(format!("native linker was not offered: {error}")))
            }
            Err(LinkerError::Refused) => {
                delivery.0 = false;
                pause.resume()?;
                Err(refused("native linker host declined before execution"))
            }
            Err(LinkerError::Unknown { member, .. }) => {
                std::mem::forget(member);
                lost()
            }
        }
    }
    pub(super) fn output(mut self) -> io::Result<Output> {
        loop {
            match self.member.poll(Instant::now() + Duration::from_millis(250)) {
                Ok(None) => {}
                Ok(Some(outcome)) => {
                    // The same native owner checked exact loan, actual owning
                    // wait, both output EOFs and original host before return.
                    self.delivery.0 = false;
                    let pause =
                        self.pause.take().ok_or_else(|| refused("native linker pause missing"))?;
                    pause.resume()?;
                    return match outcome {
                        LinkerOutcome::Refused(reason) => Err(refused(reason)),
                        LinkerOutcome::Completed(result) => {
                            if result.output_limit_exceeded {
                                return Err(refused("native linker output exceeded its bound"));
                            }
                            if let Err(reason) = result.completion.completed.inputs_unchanged {
                                return Err(refused(format!(
                                    "native linker inputs changed: {reason}"
                                )));
                            }
                            Ok(Output {
                                status: exit_status(result.completion.completed.finished.status)?,
                                stdout: result.stdout,
                                stderr: result.stderr,
                            })
                        }
                    };
                }
                Err(_) => {
                    let _ = self.member.cancel(Instant::now() + Duration::from_secs(1));
                    let _ = self.member.take_failure_observation();
                    lost()
                }
            }
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}
pub(super) fn exit_status(status: Status) -> io::Result<ExitStatus> {
    match status {
        Status::Finished {
            outcome: Outcome::Exit(code), cause: CompletionCause::Exited, ..
        } if (0..=255).contains(&code) => Ok(ExitStatus::from_raw(code << 8)),
        Status::Finished {
            outcome: Outcome::Signal(signal),
            cause: CompletionCause::Exited,
            ..
        } if (1..=127).contains(&signal) => Ok(ExitStatus::from_raw(signal)),
        Status::Finished { cause, .. } => Err(refused(format!("native linker ended: {cause:?}"))),
        Status::Refused { reason } => Err(refused(reason)),
        _ => lost(),
    }
}
