// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded, cached observations from an explicitly selected aterm executable.
//! This transport observes raw memory availability, not reservation entitlement.

use std::io::{self, Read};
use std::os::fd::AsRawFd;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use crate::{Observation, invalid};

const MAX_BYTES: usize = 65_536;
const POLL: Duration = Duration::from_millis(10);

#[derive(Default)]
struct State {
    stop: bool,
    latest: Option<(Observation, u64)>,
    unavailable: Option<String>,
    observed: bool,
}

#[derive(Default)]
struct Shared {
    state: Mutex<State>,
    wake: Condvar,
}

impl Shared {
    fn stopped(&self) -> bool {
        self.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner).stop
    }

    fn pause(&self, duration: Duration) {
        let state = self.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        if !state.stop {
            drop(self.wake.wait_timeout_while(state, duration, |state| !state.stop));
        }
    }
}

/// One asynchronous sampler. Cache reads never launch a process or refresh age.
///
/// Each round executes at most two probes sequentially. Dropping the sampler
/// cancels its current probe, reaps that owned child and joins the sampler.
pub struct Monitor {
    shared: Arc<Shared>,
    thread: Option<JoinHandle<()>>,
}

impl Monitor {
    /// Poll an absolute executable directly, without invoking a shell.
    ///
    /// Cadence is the minimum delay after a completed pair of probes. Both it
    /// and the per-probe timeout must be positive. A failed round
    /// clears the cache; absent aterm never becomes an invented resource grant.
    pub fn spawn(program: PathBuf, cadence: Duration, timeout: Duration) -> io::Result<Self> {
        let origin = Instant::now();
        Self::spawn_with(program, cadence, timeout, move || origin.elapsed())
    }

    // Only the per-probe timeout reads `probe_time`, a monotonic duration.
    // Tests pass a clock they move, so a probe ends by what the test means
    // (its output, its bound or its time), never by a slow start.
    pub(crate) fn spawn_with(
        program: PathBuf,
        cadence: Duration,
        timeout: Duration,
        probe_time: impl Fn() -> Duration + Send + 'static,
    ) -> io::Result<Self> {
        if !program.is_absolute()
            || cadence.is_zero()
            || timeout.is_zero()
            || Instant::now().checked_add(cadence).is_none()
            || Instant::now().checked_add(timeout).is_none()
        {
            return Err(invalid("monitor needs an absolute executable and positive durations"));
        }
        let shared = Arc::new(Shared::default());
        let worker = Arc::clone(&shared);
        let thread =
            thread::Builder::new().name("trust-host-observation".into()).spawn(move || {
                while !worker.stopped() {
                    let result = observe(&program, timeout, &worker, &probe_time);
                    let mut state =
                        worker.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
                    if state.stop {
                        break;
                    }
                    match result {
                        Ok(value) => {
                            state.observed = true;
                            state.latest = Some(value);
                            state.unavailable = None;
                        }
                        Err(error) => {
                            state.latest = None;
                            state.unavailable = Some(error.to_string());
                        }
                    }
                    drop(state);
                    worker.pause(cadence);
                }
            })?;
        Ok(Self { shared, thread: Some(thread) })
    }

    /// Clone the last successful round, preserving its original receipt time.
    /// The caller still checks observation age before making a decision.
    pub fn latest(&self) -> Option<(Observation, u64)> {
        self.shared.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner).latest.clone()
    }

    /// Why the last completed round was unavailable; none before its first result.
    pub fn unavailable(&self) -> Option<String> {
        self.shared
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .unavailable
            .clone()
    }

    /// Whether this monitor ever received a valid complete round. Losing an
    /// established monitor differs from a machine with no monitor capability.
    pub fn ever_observed(&self) -> bool {
        self.shared.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner).observed
    }
}

impl Drop for Monitor {
    fn drop(&mut self) {
        self.shared.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner).stop = true;
        self.shared.wake.notify_all();
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn observe(
    program: &Path,
    timeout: Duration,
    shared: &Shared,
    probe_time: &dyn Fn() -> Duration,
) -> io::Result<(Observation, u64)> {
    let bytes = probe(program, &["ctl", "@self", "sys", "--json"], timeout, shared, probe_time)?;
    let observed = Observation::from_aterm_sys(&bytes, Instant::now())?;
    let bytes = probe(program, &["pkg", "capacity", "--json"], timeout, shared, probe_time)?;
    let value: serde_json::Value =
        serde_json::from_slice(&bytes).map_err(|_| invalid("aterm capacity is not JSON"))?;
    let available = value["available"]
        .as_u64()
        .ok_or_else(|| invalid("aterm claimable memory is unavailable"))?;
    Ok((observed, available))
}

/// Every error path closes the pipe and terminates/reaps only this child.
struct OwnedProbe(Child);

impl Drop for OwnedProbe {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn probe(
    program: &Path,
    args: &[&str],
    timeout: Duration,
    shared: &Shared,
    probe_time: &dyn Fn() -> Duration,
) -> io::Result<Vec<u8>> {
    let began = probe_time();
    let elapsed = || probe_time().saturating_sub(began);
    if shared.stopped() {
        return Err(io::Error::new(io::ErrorKind::Interrupted, "monitor cancelled"));
    }
    let mut child = OwnedProbe(
        Command::new(program)
            .args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?,
    );
    let mut stdout = child.0.stdout.take().ok_or_else(|| invalid("probe has no stdout"))?;
    let fd = stdout.as_raw_fd();
    // SAFETY: stdout owns this live pipe throughout both fcntl calls. Only its
    // file-status flags change; no descriptor ownership or process identity does.
    let nonblocking = unsafe {
        let flags = libc::fcntl(fd, libc::F_GETFL);
        flags >= 0 && libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) >= 0
    };
    if !nonblocking {
        return Err(io::Error::last_os_error());
    }
    let mut bytes = Vec::new();
    loop {
        if shared.stopped() {
            return Err(io::Error::new(io::ErrorKind::Interrupted, "monitor cancelled"));
        }
        if elapsed() >= timeout {
            return Err(io::Error::new(io::ErrorKind::TimedOut, "aterm probe timed out"));
        }
        let mut chunk = [0; 4096];
        loop {
            match stdout.read(&mut chunk) {
                Ok(0) => break,
                Ok(count) => {
                    if bytes.len().saturating_add(count) > MAX_BYTES {
                        return Err(invalid("aterm probe output exceeds its size bound"));
                    }
                    bytes.extend_from_slice(&chunk[..count]);
                }
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
                Err(error) => return Err(error),
            }
        }
        if let Some(status) = child.0.try_wait()? {
            if !status.success() {
                return Err(io::Error::other("aterm probe exited unsuccessfully"));
            }
            // The exited child may have written between the drain and wait.
            loop {
                match stdout.read(&mut chunk) {
                    Ok(0) => break,
                    Ok(count) => {
                        if bytes.len().saturating_add(count) > MAX_BYTES {
                            return Err(invalid("aterm probe output exceeds its size bound"));
                        }
                        bytes.extend_from_slice(&chunk[..count]);
                    }
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
                    Err(error) => return Err(error),
                }
            }
            return Ok(bytes);
        }
        shared.pause(POLL.min(timeout.saturating_sub(elapsed())));
    }
}

#[cfg(test)]
#[path = "monitor/tests.rs"]
mod tests;
