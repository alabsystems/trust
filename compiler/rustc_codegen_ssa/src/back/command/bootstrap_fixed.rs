//! Trust: direct paired LLD using the actual private Fixed compiler's primary.
//! No local process, cooperative Lease or new GNU acquisition is created here.
use std::fs::File;
use std::io::{self, Read};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::process::Output;
use std::sync::Arc;
use std::time::{Duration, Instant};

use rustc_data_structures::jobserver::{BootstrapCompilerPause, BootstrapFixed};
use trust_resource_controller::bootstrap_graph::compilation::compiler::PairedLinkerRequest;
use trust_resource_controller::client::bootstrap_graph::PairedLinkerLoan;

use super::Command;

const OUTPUT_LIMIT: usize = 32 * 1024 * 1024;
fn refused(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, message.into())
}
fn lost() -> ! {
    // SAFETY: unresolved native execution must not unwind/reuse its original
    // paused primary. The native owner still owns the actual child and cohort.
    unsafe { libc::_exit(75) }
}
struct Delivery(bool);
impl Drop for Delivery {
    fn drop(&mut self) {
        if self.0 {
            lost();
        }
    }
}
fn attempt() -> io::Result<[u8; 16]> {
    let mut value = [0; 16];
    File::open("/dev/urandom")?.read_exact(&mut value)?;
    if value == [0; 16] {
        return Err(refused("private linker nonce unavailable"));
    }
    Ok(value)
}
fn pipe() -> io::Result<(File, OwnedFd)> {
    let mut pair = [-1; 2];
    // SAFETY: pair has exactly two writable slots; successful descriptors are
    // immediately uniquely owned. Only our new reader becomes nonblocking.
    if unsafe { libc::pipe(pair.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let read = unsafe { OwnedFd::from_raw_fd(pair[0]) };
    let write = unsafe { OwnedFd::from_raw_fd(pair[1]) };
    for fd in [&read, &write] {
        if unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC) } != 0 {
            return Err(io::Error::last_os_error());
        }
    }
    let flags = unsafe { libc::fcntl(read.as_raw_fd(), libc::F_GETFL) };
    if flags < 0
        || unsafe { libc::fcntl(read.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) } != 0
    {
        return Err(io::Error::last_os_error());
    }
    Ok((File::from(read), write))
}
fn pause(context: &Arc<BootstrapFixed>) -> io::Result<BootstrapCompilerPause> {
    let deadline =
        context.member().original_deadline()?.min(Instant::now() + Duration::from_secs(8));
    context.member().check_current(deadline)?;
    loop {
        if let Some(pause) = context.try_pause()? {
            return Ok(pause);
        }
        if Instant::now() >= deadline {
            return Err(refused("private compiler work did not become quiescent before linking"));
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

pub(crate) struct Child {
    // FIRST: an unresolved delivery exits before pause/original custody drops.
    delivery: Delivery,
    pause: Option<BootstrapCompilerPause>,
    member: Option<PairedLinkerLoan>,
    stdout: File,
    stderr: File,
    deadline: Instant,
}
impl Child {
    pub(super) fn spawn(command: &Command, context: Arc<BootstrapFixed>) -> io::Result<Self> {
        // Reuse the exact ordinary native Darwin recipe construction; private
        // selection additionally binds the actual held private seed/issued pair.
        let command = super::native::command_spec(command)?;
        if command.program != context.member().data().inputs.paired_linker.path {
            return Err(refused("private linker differs from the actual adopted paired image"));
        }
        let nonce = attempt()?;
        let input = File::open("/dev/null")?;
        let (stdout, output) = pipe()?;
        let (stderr, error) = pipe()?;
        let pause = pause(&context)?;
        let deadline = context.member().original_deadline()?;
        let request = PairedLinkerRequest {
            adopted: context.member().data().clone(),
            generation: pause.generation(),
            member: nonce,
            command,
            timeout_ns: deadline
                .saturating_duration_since(Instant::now())
                .as_nanos()
                .try_into()
                .map_err(|_| refused("private linker deadline exceeds protocol bound"))?,
        };
        let mut delivery = Delivery(true);
        // SAFETY: this is only called by spawn_linker_inner after the built-in
        // backend joined codegen. Actual registry/all GNU helpers are paused;
        // exact native closure or its private never-offered token alone resumes.
        match unsafe {
            context.member().paired_linker(
                request,
                [input.into(), output, error],
                deadline.min(Instant::now() + Duration::from_secs(8)),
            )
        } {
            Ok(member) => Ok(Self {
                delivery,
                pause: Some(pause),
                member: Some(member),
                stdout,
                stderr,
                deadline,
            }),
            Err(failure) => {
                let message = failure.to_string();
                match failure.into_unoffered(context.member(), pause.generation()) {
                    Ok(unlent) => {
                        pause.cancel_unoffered(unlent)?;
                        delivery.0 = false;
                        Err(refused(format!("private linker was not offered: {message}")))
                    }
                    Err(failure) => {
                        // No status/EOF/ambiguous transport can release primary.
                        std::mem::forget(failure);
                        lost()
                    }
                }
            }
        }
    }
    pub(super) fn output(mut self) -> io::Result<Output> {
        // Drain both actual pipes without a helper/process or unbounded output
        // allocation. Continue draining after the cap so native wait can settle.
        let mut bytes = [Vec::new(), Vec::new()];
        let mut eof = [false, false];
        let mut exceeded = false;
        while !eof.iter().all(|value| *value) {
            if Instant::now() >= self.deadline {
                lost();
            }
            for (index, reader) in [&mut self.stdout, &mut self.stderr].into_iter().enumerate() {
                if eof[index] {
                    continue;
                }
                let mut buffer = [0u8; 8192];
                loop {
                    if Instant::now() >= self.deadline {
                        lost();
                    }
                    match reader.read(&mut buffer) {
                        Ok(0) => {
                            eof[index] = true;
                            break;
                        }
                        Ok(count) => {
                            let keep = count.min(OUTPUT_LIMIT.saturating_sub(bytes[index].len()));
                            bytes[index].extend_from_slice(&buffer[..keep]);
                            exceeded |= keep != count;
                        }
                        Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
                        Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                        Err(_) => lost(),
                    }
                }
            }
            if !eof.iter().all(|value| *value) {
                std::thread::sleep(Duration::from_millis(10));
            }
        }
        let member = self.member.take().unwrap_or_else(|| lost());
        let closed = match member.retire(self.deadline) {
            Ok(closed) => closed,
            Err(failure) => {
                std::mem::forget(failure);
                lost()
            }
        };
        let pause = self.pause.take().unwrap_or_else(|| lost());
        let status = pause.resume(closed).unwrap_or_else(|_| lost());
        self.delivery.0 = false;
        if exceeded {
            return Err(refused("private linker output exceeded its bound"));
        }
        let [stdout, stderr] = bytes;
        Ok(Output { status: super::native::exit_status(status)?, stdout, stderr })
    }
}
