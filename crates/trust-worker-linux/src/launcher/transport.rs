use std::fs::File;
use std::io::Read;
use std::os::fd::{AsRawFd, FromRawFd};
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};
use trust_process_isolation::{
    Admission, Binding, Budget, Call, Charge, FrameDecoder, Handle, Session, Value,
};

use super::{InputClosureIdentity, LaunchLimits, OwnedWorker, checked, contract, snapshot};
use crate::native::NativeInputReceipt;
use crate::{Error, system};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    Finished,
    Refused,
    WorkerFailure,
    SetupFailure { stage: u32, errno: i32 },
    AbnormalExit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InputIdentity {
    pub sha256: [u8; 32],
    pub size: u64,
    pub executable: bool,
}

/// Local structural diagnostic only: no Trust seal or semantic/proof authority.
#[derive(Debug)]
pub struct Receipt {
    pub binding: Binding,
    pub limits: LaunchLimits,
    pub input_bytes: u64,
    pub input_identity: InputClosureIdentity,
    pub worker: InputIdentity,
    pub inputs: [Option<InputIdentity>; 27],
    pub native: Option<NativeInputReceipt>,
    pub elapsed_after_prepare: Duration,
    pub deadline: Instant,
    pub outcome: Outcome,
    pub refusal: Option<Error>,
    pub worker_failure: Option<String>,
    pub output: Option<Handle>,
    pub raw_status: i32,
    pub reaped: bool,
    pub used_pidfd: bool,
    /// Leader only. Trusted startup must not create threads/descendants before
    /// B2; B2 independently denies process creation afterward. Not a tree RSS.
    pub sampled_leader_rss_peak_bytes: u64,
    pub rss_sample_interval: Duration,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub stdout_sha256: [u8; 32],
    pub stderr_sha256: [u8; 32],
}

pub(crate) struct Capture {
    bytes: Vec<u8>,
    digest: Sha256,
    closed: bool,
}
impl Capture {
    pub(crate) fn new(cap: usize, b: &Budget) -> Result<Self, Error> {
        let size = cap.checked_add(1).ok_or_else(|| contract("capture overflow"))?;
        b.charge(Charge { allocation_bytes: size as u64, work: 64, ..Charge::default() })
            .map_err(Error::Budget)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(size)
            .map_err(|_| Error::Budget(b.refuse(trust_process_isolation::Error::Allocation)))?;
        b.charge(Charge {
            allocation_bytes: bytes.capacity().saturating_sub(size) as u64,
            ..Charge::default()
        })
        .map_err(Error::Budget)?;
        Ok(Self { bytes, digest: Sha256::new(), closed: false })
    }
    pub(crate) fn read(&mut self, fd: &mut File, cap: usize, b: &Budget) -> Result<(), Error> {
        if self.closed {
            return Ok(());
        }
        let mut buffer = [0; 1024];
        let count = buffer.len().min(cap + 1 - self.bytes.len());
        if count == 0 {
            return Err(contract("output bytes"));
        }
        b.charge(Charge { work: 3 * count as u64, ..Charge::default() }).map_err(Error::Budget)?;
        match fd.read(&mut buffer[..count]) {
            Ok(0) => self.closed = true,
            Ok(n) => {
                self.digest.update(&buffer[..n]);
                self.bytes.extend_from_slice(&buffer[..n]);
                if self.bytes.len() > cap {
                    return Err(contract("output bytes"));
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
            Err(e) => return Err(Error::System("worker capture", e)),
        }
        checked(b)
    }
    pub(crate) fn bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub(crate) fn closed(&self) -> bool {
        self.closed
    }
}

fn sample_rss(pid: u32, b: &Budget) -> Result<u64, Error> {
    b.charge(Charge { work: 8 * 512, ..Charge::default() }).map_err(Error::Budget)?;
    let path = snapshot::proc_path(b"", pid, b"/statm")?;
    // SAFETY: path is a fixed terminated owned-child observation path; no
    // worker-supplied pathname is opened by this diagnostic memory sampler.
    let fd = unsafe { libc::open(path.as_ptr().cast(), libc::O_RDONLY | libc::O_CLOEXEC) };
    if fd < 0 {
        return Err(system("worker statm"));
    }
    // SAFETY: successful open produced a new uniquely owned read descriptor.
    let mut file = unsafe { File::from_raw_fd(fd) };
    let mut buffer = [0; 512];
    let count = file.read(&mut buffer).map_err(|e| Error::System("worker statm read", e))?;
    if count == buffer.len() {
        return Err(contract("statm bytes"));
    }
    let text = std::str::from_utf8(&buffer[..count]).map_err(|_| contract("statm encoding"))?;
    let pages = text
        .split_whitespace()
        .nth(1)
        .ok_or_else(|| contract("statm resident"))?
        .parse::<u64>()
        .map_err(|_| contract("statm resident"))?;
    // SAFETY: sysconf returns a scalar page-size observation; nonpositive is
    // refused, never cast into an apparent positive memory measurement.
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    if page <= 0 {
        return Err(contract("native page size"));
    }
    checked(b)?;
    pages.checked_mul(page as u64).ok_or_else(|| contract("RSS overflow"))
}

impl OwnedWorker {
    /// Callbacks remain owner code. They must debit bounded semantic traversal
    /// and handle payloads; an opaque callback is not preemptible by this driver.
    /// Err/unwind aborts the shared invocation and kill/reaps its owned process.
    pub fn run(
        mut self,
        mut callback: impl FnMut(Call, &mut Session) -> Result<Value, Error>,
    ) -> Result<Receipt, Error> {
        let budget = self.prepared.budget.clone();
        let mut stdout = Capture::new(self.prepared.limits.output_bytes_per_stream, &budget)?;
        let mut stderr = Capture::new(self.prepared.limits.output_bytes_per_stream, &budget)?;
        let mut decoder = FrameDecoder::new(budget.clone());
        let mut sent = 0usize;
        let mut partial = false;
        let mut ipc_closed = false;
        let mut exec_record = [0u8; 9];
        let mut exec_bytes = 0usize;
        let mut exec_closed = false;
        let mut finish = false;
        let mut output = None;
        let mut failure = None;
        let mut peak = 0u64;
        let interval = Duration::from_millis(5);
        let mut next_sample = Instant::now();
        let result = (|| -> Result<Outcome, Error> {
            loop {
                checked(&budget)?;
                if Instant::now() >= next_sample {
                    peak = peak.max(sample_rss(self.pid(), &budget)?);
                    if peak > self.prepared.limits.sampled_leader_rss_bytes {
                        return Err(contract("sampled leader RSS threshold"));
                    }
                    next_sample = Instant::now()
                        .checked_add(interval)
                        .ok_or_else(|| contract("sample interval overflow"))?;
                }
                stdout.read(
                    &mut self.stdout,
                    self.prepared.limits.output_bytes_per_stream,
                    &budget,
                )?;
                stderr.read(
                    &mut self.stderr,
                    self.prepared.limits.output_bytes_per_stream,
                    &budget,
                )?;
                if !exec_closed {
                    budget
                        .charge(Charge { work: 9, ..Charge::default() })
                        .map_err(Error::Budget)?;
                    match self.status.read(&mut exec_record[exec_bytes..]) {
                        Ok(0) => exec_closed = true,
                        Ok(n) => {
                            exec_bytes += n;
                            if exec_bytes > 8 {
                                return Err(contract("exec status bytes"));
                            }
                        }
                        Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
                        Err(e) => return Err(Error::System("exec status read", e)),
                    }
                    if exec_closed && exec_bytes != 0 {
                        if exec_bytes != 8 {
                            return Err(contract("exec status truncated"));
                        }
                        let stage = u32::from_le_bytes(
                            exec_record[..4].try_into().map_err(|_| contract("exec stage"))?,
                        );
                        let errno = i32::from_le_bytes(
                            exec_record[4..8].try_into().map_err(|_| contract("exec errno"))?,
                        );
                        return Ok(Outcome::SetupFailure { stage, errno });
                    }
                }
                if sent < self.outbound.len() {
                    let count = (self.outbound.len() - sent).min(4096);
                    budget
                        .charge(Charge { work: count as u64, ..Charge::default() })
                        .map_err(Error::Budget)?;
                    // SAFETY: a live bounded initialized slice goes to the
                    // parent-owned control FD; NOSIGNAL prevents pipe death.
                    let n = unsafe {
                        libc::send(
                            self.control.as_raw_fd(),
                            self.outbound[sent..sent + count].as_ptr().cast(),
                            count,
                            libc::MSG_NOSIGNAL,
                        )
                    };
                    if n >= 0 {
                        sent += n as usize;
                    } else {
                        let e = std::io::Error::last_os_error();
                        if e.kind() != std::io::ErrorKind::WouldBlock {
                            return Err(Error::System("worker control send", e));
                        }
                    }
                }
                if !ipc_closed {
                    let mut bytes = [0u8; 1024];
                    let count = if finish { 1 } else { decoder.needed().min(bytes.len()) };
                    budget
                        .charge(Charge { work: count as u64, ..Charge::default() })
                        .map_err(Error::Budget)?;
                    match self.control.read(&mut bytes[..count]) {
                        Ok(0) => {
                            ipc_closed = true;
                            if partial {
                                return Err(contract("truncated worker frame"));
                            }
                        }
                        Ok(n) => {
                            if finish {
                                return Err(contract("post-finish bytes"));
                            }
                            partial = true;
                            if let Some(envelope) =
                                decoder.push(&bytes[..n]).map_err(Error::Budget)?
                            {
                                if sent != self.outbound.len() {
                                    return Err(contract("reply not delivered"));
                                }
                                partial = false;
                                match self.session.receive(envelope).map_err(Error::Budget)? {
                                    Admission::Ready => {}
                                    Admission::Call(call) => {
                                        checked(&budget)?;
                                        let id = call.id;
                                        let value = callback(call, &mut self.session)?;
                                        checked(&budget)?;
                                        // The callback borrows the real Session, so it can
                                        // replace that value. Matching metadata and a valid
                                        // replayed pending call still cannot replace the
                                        // original conversation owner after dispatch.
                                        if !self.prepared.session_owner.matches(&self.session) {
                                            return Err(Error::Budget(budget.refuse(
                                                trust_process_isolation::Error::Identity,
                                            )));
                                        }
                                        let reply =
                                            self.session.reply(id, value).map_err(Error::Budget)?;
                                        self.outbound =
                                            trust_process_isolation::encode(&reply, &budget)
                                                .map_err(Error::Budget)?;
                                        sent = 0;
                                    }
                                    Admission::Finished(handle) => {
                                        finish = true;
                                        output = handle;
                                    }
                                    Admission::Failed(reason) => {
                                        failure = Some(reason);
                                        return Ok(Outcome::WorkerFailure);
                                    }
                                }
                                decoder = FrameDecoder::new(budget.clone());
                            }
                        }
                        Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
                        Err(e) => return Err(Error::System("worker control read", e)),
                    }
                }
                if self.child.exited()?
                    && stdout.closed
                    && stderr.closed
                    && ipc_closed
                    && exec_closed
                {
                    if !finish || sent != self.outbound.len() {
                        return Err(contract("missing worker completion"));
                    }
                    return Ok(Outcome::Finished);
                }
                let left = budget.deadline().saturating_duration_since(Instant::now());
                let timeout = left.min(Duration::from_millis(1)).as_millis() as i32;
                let mut fds = [
                    libc::pollfd {
                        fd: if ipc_closed { -1 } else { self.control.as_raw_fd() },
                        events: libc::POLLIN
                            | if sent < self.outbound.len() { libc::POLLOUT } else { 0 },
                        revents: 0,
                    },
                    libc::pollfd {
                        fd: if stdout.closed { -1 } else { self.stdout.as_raw_fd() },
                        events: if stdout.closed { 0 } else { libc::POLLIN },
                        revents: 0,
                    },
                    libc::pollfd {
                        fd: if stderr.closed { -1 } else { self.stderr.as_raw_fd() },
                        events: if stderr.closed { 0 } else { libc::POLLIN },
                        revents: 0,
                    },
                    libc::pollfd {
                        fd: if exec_closed { -1 } else { self.status.as_raw_fd() },
                        events: if exec_closed { 0 } else { libc::POLLIN },
                        revents: 0,
                    },
                ];
                budget.charge(Charge { work: 4, ..Charge::default() }).map_err(Error::Budget)?;
                // SAFETY: poll receives a complete writable fixed descriptor
                // array and a nonnegative deadline-bounded millisecond wait.
                if unsafe { libc::poll(fds.as_mut_ptr(), fds.len() as libc::nfds_t, timeout) } < 0
                    && std::io::Error::last_os_error().raw_os_error() != Some(libc::EINTR)
                {
                    return Err(system("worker poll"));
                }
            }
        })();
        let (mut outcome, mut refusal) = match result {
            Ok(o) => (o, None),
            Err(e) => (Outcome::Refused, Some(e)),
        };
        if outcome != Outcome::Finished {
            budget.refuse(trust_process_isolation::Error::Phase);
        }
        let status = self.child.stop_and_reap()?;
        if outcome == Outcome::Finished {
            if !libc::WIFEXITED(status) || libc::WEXITSTATUS(status) != 0 {
                outcome = Outcome::AbnormalExit;
                budget.refuse(trust_process_isolation::Error::Phase);
            }
        }
        let identity = |s: &snapshot::Snapshot| InputIdentity {
            sha256: s.sha256,
            size: s.size,
            executable: s.executable,
        };
        let worker = identity(&self.prepared.worker);
        let inputs = std::array::from_fn(|at| self.prepared.inputs[at].as_ref().map(identity));
        let binding = self.prepared.binding.clone();
        let limits = self.prepared.limits;
        let input_bytes = self.prepared.input_bytes;
        let input_identity = self.prepared.input_identity;
        let native = self.prepared.native.take().map(|native| native.into_receipt());
        let prepared_at = self.prepared.prepared_at;
        let reaped = self.child.reaped();
        let used_pidfd = self.child.used_pidfd();
        // Teardown is explicit: no worker/channel/decoder/memfd ownership is
        // hidden after the final deadline check. Retained output data transfers
        // to the receipt under its previously reserved bounded allocation.
        drop(decoder);
        drop(self);
        let stdout_sha256 = stdout.digest.finalize().into();
        let stderr_sha256 = stderr.digest.finalize().into();
        if outcome == Outcome::Finished {
            if let Err(e) = checked(&budget) {
                outcome = Outcome::Refused;
                refusal = Some(e);
            }
        }
        if outcome != Outcome::Finished {
            output = None;
        }
        Ok(Receipt {
            binding,
            limits,
            input_bytes,
            input_identity,
            worker,
            inputs,
            native,
            elapsed_after_prepare: prepared_at.elapsed(),
            deadline: budget.deadline(),
            outcome,
            refusal,
            worker_failure: failure,
            output,
            raw_status: status,
            reaped,
            used_pidfd,
            sampled_leader_rss_peak_bytes: peak,
            rss_sample_interval: interval,
            stdout_sha256,
            stderr_sha256,
            stdout: stdout.bytes,
            stderr: stderr.bytes,
        })
    }
}
