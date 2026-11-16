//! Direct native compiler members using the ordinary queue's SAME credit.
//! No local child/helper, second GNU read or status-to-credit conversion.
use super::*;
use cargo_util::{Read2Action, Read2Control};
use std::fs::File;
use std::os::fd::OwnedFd;
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::process::ExitStatusExt as _;
use trust_resource_controller::bootstrap_graph::compilation::{
    MAX_MEMBER_NS, MAX_MEMBERS, MemberRequest, ProgramRole,
};
use trust_resource_controller::{CommandSpec, CompletionCause, Outcome, Status};

pub(crate) struct QueuedExecutor {
    permit: Mutex<QueuePermit>,
    target_limit: Option<Duration>,
}
impl QueuedExecutor {
    pub(crate) fn new(permit: QueuePermit) -> Arc<Self> {
        Arc::new(Self {
            permit: Mutex::new(permit),
            target_limit: None,
        })
    }
    pub(super) fn for_query(permit: QueuePermit) -> Arc<Self> {
        Arc::new(Self {
            permit: Mutex::new(permit),
            target_limit: Some(Duration::from_secs(30)),
        })
    }

    fn run(
        &self,
        process: &ProcessBuilder,
        on_stdout: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        on_stderr: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        capture: bool,
        limits: Option<StreamingOutputLimits>,
        text_lines: bool,
    ) -> io::Result<Output> {
        let mut permit = self
            .permit
            .lock()
            .map_err(|_| io::Error::other("Full queue execution owner poisoned"))?;
        let full = Arc::clone(permit.owner());
        full.check_current()?;
        if process.has_action_sandbox() || process.get_stdin().is_some() {
            return Err(io::Error::other(
                "Full compiler cannot reinterpret confined or stdin execution",
            ));
        }
        let Some(actual) = process.get_jobserver() else {
            return Err(io::Error::other(
                "Full compiler lost its actual queued GNU scheduler",
            ));
        };
        super::super::dependency_inputs::same_scheduler(actual, &full.owner.data().gnu)?;
        if process.get_program().as_encoded_bytes() != full.owner.data().seed.compiler.path {
            return Err(io::Error::other(
                "Full produced program has no actual native-issued runtime owner",
            ));
        }
        let environment = process.get_effective_envs()?;
        if environment
            .get(std::ffi::OsStr::new("CARGO_HOME"))
            .map(|value| value.as_os_str())
            != Some(full.cargo_home.as_os_str())
        {
            return Err(io::Error::other(
                "Full compiler changed its actual guarded Cargo home",
            ));
        }
        let command = CommandSpec {
            program: process.get_program().as_encoded_bytes().to_vec(),
            arg0: process.get_arg0().map(|value| value.as_bytes().to_vec()),
            args: process
                .get_args()
                .map(|value| value.as_encoded_bytes().to_vec())
                .collect(),
            cwd: process
                .get_cwd()
                .ok_or_else(|| io::Error::other("Full compiler requires its actual explicit cwd"))?
                .as_os_str()
                .as_bytes()
                .to_vec(),
            environment: environment
                .into_iter()
                .map(|(key, value)| {
                    (
                        key.as_encoded_bytes().to_vec(),
                        value.as_encoded_bytes().to_vec(),
                    )
                })
                .collect(),
        };
        let original_deadline = full.owner.original_deadline();
        let execution_deadline = target_deadline(original_deadline, self.target_limit)?;
        let timeout_ns = execution_deadline
            .saturating_duration_since(Instant::now())
            .as_nanos()
            .min(u128::from(MAX_MEMBER_NS)) as u64;
        if timeout_ns == 0 {
            return Err(io::ErrorKind::TimedOut.into());
        }
        let (stdout, stdout_writer) = std::io::pipe()?;
        let (stderr, stderr_writer) = std::io::pipe()?;
        let stdin: OwnedFd = File::open("/dev/null")?.into();
        let (read, write) = match full.scheduler.client().transport_witnesses()? {
            jobserver::TransportWitnesses::NumericPipe { read, write }
            | jobserver::TransportWitnesses::NamedFifo { read, write, .. } => (read, write),
        };
        // Serialize only offer delivery, so strictly increasing reservations
        // cannot arrive out of order. Actual compiler execution is concurrent
        // in the existing JobQueue after attachment; retirement is separate.
        let mut delivery = Some(
            full.delivery
                .lock()
                .map_err(|_| io::Error::other("Full offer owner poisoned"))?,
        );
        let sequence = full.sequence.fetch_add(1, Ordering::AcqRel);
        if !(1..=MAX_MEMBERS).contains(&sequence) {
            return Err(io::Error::other("Full compiler member census is exhausted"));
        }
        let request = MemberRequest {
            key: full.owner.data().key.clone(),
            sequence,
            member: crate::resource_v3::call_attempt(
                full.owner
                    .data()
                    .key
                    .attempt
                    .key
                    .graph
                    .query
                    .binding
                    .root_attempt,
            )?,
            program: ProgramRole::SeedCompiler,
            command,
            gnu: full.owner.data().gnu.clone(),
            fixed_units: 1,
            timeout_ns,
        };
        let offer_deadline = full.observation_deadline()?;
        permit.begin_delivery(&request)?;
        let descriptions = [
            stdin,
            stdout_writer.into(),
            stderr_writer.into(),
            read,
            write,
        ];
        let member = match full.owner.member(request, descriptions, offer_deadline) {
            Ok(member) => member,
            Err(failure) => {
                drop(delivery.take());
                if permit.failed(&failure).is_ok() {
                    return Err(io::Error::other(failure));
                }
                // Unknown may only consume SAME Retire; never retry Member.
                match failure.into_member() {
                    Ok(member) => member,
                    Err(failure) => return Err(io::Error::other(failure)),
                }
            }
        };
        // No local copy of the transferred stream writers remains here.
        drop(delivery.take());
        let limits = limits
            .unwrap_or_else(|| StreamingOutputLimits::new(128 * 1024 * 1024, 512 * 1024 * 1024));
        let mut output = [Vec::new(), Vec::new()];
        let mut lengths = [0usize; 2];
        let mut stream_error = None;
        let streams = cargo_util::read2_controlled(
            std::process::ChildStdout::from(OwnedFd::from(stdout)),
            std::process::ChildStderr::from(OwnedFd::from(stderr)),
            Some(execution_deadline),
            &mut |is_stdout, bytes, eof| {
                let index = usize::from(!is_stdout);
                if lengths[index].saturating_add(bytes.len()) > limits.stream_bytes() {
                    stream_error = Some(io::Error::other(
                        "Full compiler output exceeds its finite stream bound",
                    ));
                    return Read2Action::Stop;
                }
                let result = (|| -> io::Result<()> {
                    if !text_lines {
                        if capture {
                            output[index]
                                .try_reserve(bytes.len())
                                .map_err(io::Error::other)?;
                            output[index].extend_from_slice(bytes);
                        }
                        lengths[index] =
                            lengths[index].checked_add(bytes.len()).ok_or_else(|| {
                                io::Error::other("Full compiler output length overflow")
                            })?;
                        bytes.clear();
                        return Ok(());
                    }
                    let mut consumed = 0;
                    while consumed < bytes.len() {
                        let tail = &bytes[consumed..];
                        let length = match tail.iter().position(|value| *value == b'\n') {
                            Some(index) => index + 1,
                            None if eof => tail.len(),
                            None => break,
                        };
                        if length > limits.line_bytes() {
                            return Err(io::Error::other(
                                "Full compiler output exceeds its finite line bound",
                            ));
                        }
                        let line = &tail[..length];
                        let line_text = std::str::from_utf8(line)
                            .map_err(io::Error::other)?
                            .trim_end_matches('\n')
                            .trim_end_matches('\r');
                        if is_stdout {
                            on_stdout(line_text)
                        } else {
                            on_stderr(line_text)
                        }
                        .map_err(io::Error::other)?;
                        if capture {
                            output[index]
                                .try_reserve(line.len())
                                .map_err(io::Error::other)?;
                            output[index].extend_from_slice(line);
                        }
                        consumed += length;
                    }
                    lengths[index] = lengths[index]
                        .checked_add(consumed)
                        .ok_or_else(|| io::Error::other("Full compiler output length overflow"))?;
                    bytes.drain(..consumed);
                    if bytes.len() > limits.line_bytes() {
                        return Err(io::Error::other(
                            "Full compiler partial line exceeds its finite bound",
                        ));
                    }
                    Ok(())
                })();
                match result {
                    Ok(()) => Read2Action::Continue,
                    Err(error) => {
                        stream_error = Some(error);
                        Read2Action::Stop
                    }
                }
            },
            &mut || {
                if Instant::now() >= execution_deadline {
                    return Err(io::ErrorKind::TimedOut.into());
                }
                Ok(Read2Control::Continue)
            },
        );
        // Actual native owning closure is mandatory even after stream failure.
        // Source/artifact validity is a different postcheck, never a CPU refund.
        // A query's target timeout never shortens the original owning cleanup
        // bound. Its SAME credit stays held until actual native retirement.
        let retired = match member.retire(original_deadline) {
            Ok(retired) => retired,
            Err(failure) => {
                permit.failed(&failure)?;
                return Err(io::Error::other(failure));
            }
        };
        permit.retired(&retired)?;
        streams?;
        if let Some(error) = stream_error {
            return Err(error);
        }
        full.check_current()?;
        let status = match retired.native_retirement().status() {
            Status::Finished {
                outcome,
                cause: CompletionCause::Exited,
                ..
            } => match outcome {
                Outcome::Exit(code) => ExitStatus::from_raw(*code << 8),
                Outcome::Signal(signal) => ExitStatus::from_raw(*signal),
            },
            Status::Refused { reason } => {
                return Err(io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    reason.clone(),
                ));
            }
            _ => {
                return Err(io::Error::other(
                    "Full compiler ended without a successful owning exit",
                ));
            }
        };
        let [stdout, stderr] = output;
        Ok(Output {
            status,
            stdout,
            stderr,
        })
    }
}

fn target_deadline(original: Instant, limit: Option<Duration>) -> io::Result<Instant> {
    let now = Instant::now();
    if now >= original {
        return Err(io::ErrorKind::TimedOut.into());
    }
    match limit {
        None => Ok(original),
        Some(limit) => Ok(now
            .checked_add(limit)
            .ok_or_else(|| io::Error::other("Full target deadline overflow"))?
            .min(original)),
    }
}
impl ProcessExecutor for QueuedExecutor {
    fn output(&self, process: &ProcessBuilder) -> io::Result<Output> {
        self.run(process, &mut |_| Ok(()), &mut |_| Ok(()), true, None, false)
    }
    fn status(&self, _: &ProcessBuilder) -> io::Result<ExitStatus> {
        Err(io::Error::other(
            "Full queued compiler requires physical output ownership",
        ))
    }
    fn streaming(
        &self,
        process: &ProcessBuilder,
        on_stdout: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        on_stderr: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        capture: bool,
        limits: Option<StreamingOutputLimits>,
        capture_rusage: bool,
    ) -> (ExecStats, anyhow::Result<Output>) {
        if capture_rusage {
            return (
                ExecStats::default(),
                Err(anyhow::anyhow!(
                    "Full member has no issued per-target resource accounting"
                )),
            );
        }
        let result = self
            .run(process, on_stdout, on_stderr, capture, limits, true)
            .map_err(anyhow::Error::from)
            .and_then(|output| completed_stream(process, output));
        (ExecStats::default(), result)
    }
}

// Regular output judgment only, after the actual opaque retirement above.
// This function cannot construct a native witness or return a queue credit.
fn completed_stream(process: &ProcessBuilder, output: Output) -> anyhow::Result<Output> {
    if output.status.success() {
        Ok(output)
    } else {
        Err(cargo_util::ProcessError::new(
            &format!("process didn't exit successfully: {process}"),
            Some(output.status),
            Some(&output),
        )
        .into())
    }
}

#[cfg(test)]
mod tests;
