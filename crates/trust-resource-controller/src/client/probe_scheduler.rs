// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Early GNU/SDK custody for fixed trusted synchronous compiler queries.
//! No admission or extra credit is created. The callback must retire its child
//! before returning, including capture-error paths; its serial guard stays live.
use std::io::{self, Read, Seek};
use std::os::fd::AsRawFd;
use std::process::{Child, Command, Output, Stdio};
use std::sync::Mutex;

use jobserver_utils::Jobserver;

use super::sdk;

pub struct ProbeScheduler {
    server: Mutex<Option<Jobserver>>,
    original_transport_present: bool,
    inherited_server_present: bool,
    interrupted: std::sync::atomic::AtomicBool,
    #[cfg(test)]
    lock_rendezvous: Option<std::sync::Arc<dyn Fn() + Send + Sync>>,
    sdk_present: bool,
}
impl ProbeScheduler {
    /// Capture before any descriptor-opening operation or arbitrary callback.
    /// # Safety
    /// Only the SDK snapshot and fixed GNU importer may precede SDK capture.
    pub unsafe fn capture_at_entry() -> io::Result<Self> {
        let sdk_advertised = std::env::var_os(sdk::SDK_LEASE_ENV).is_some();
        let required_handoff = [
            jobserver_utils::DESCENDANT_HANDOFF_ENV,
            jobserver_utils::CPU_HANDOFF_ENV,
            jobserver_utils::FIXED_CLAIM_HANDOFF_ENV,
            "BUILD_SLOT_CPU_PROTOCOL",
        ]
        .iter()
        .any(|key| std::env::var_os(key).is_some());
        let pending = sdk::snapshot_sdk_lease()?;
        // SAFETY: our caller guarantees genuine native entry and original FDs.
        let server = unsafe { Jobserver::from_env_with_handoff_checked() }?;
        // SAFETY: only the fixed scheduler importer followed the snapshot.
        unsafe { sdk::capture_sdk_lease(pending) }?;
        if server.is_none() && std::env::var_os(jobserver_utils::DESCENDANT_HANDOFF_ENV).is_some() {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "advertised probe scheduler has no inherited transport",
            ));
        }
        let inherited_server_present = server.is_some();
        let original_transport_present =
            inherited_server_present || sdk_advertised || required_handoff;
        Ok(Self {
            server: Mutex::new(server),
            original_transport_present,
            inherited_server_present,
            interrupted: std::sync::atomic::AtomicBool::new(false),
            #[cfg(test)]
            lock_rendezvous: None,
            sdk_present: sdk_advertised,
        })
    }

    /// Configure only the caller's fixed trusted compiler query. GNU variables
    /// describe our real owned transport. No jobs/environment integer is credit.
    /// The original SDK/CPU descriptors are passed through without reopening or
    /// reconstructing a lease. A locator still confers no authentication.
    pub fn with_command<T>(
        &self,
        command: &mut Command,
        run: impl FnOnce(&mut Command) -> T,
    ) -> io::Result<T> {
        self.check_interrupted()?;
        self.before_lock();
        let mut guard =
            self.server.lock().map_err(|_| io::Error::other("poisoned serial probe owner"))?;
        // A queued caller may have passed the first check before the previous
        // borrower was interrupted. No transport or launch precedes this check.
        self.check_interrupted()?;
        if !cfg!(trust_std) {
            // Stock std cannot explicitly transfer original descriptions. Only
            // a genuinely transport-free stock query retains its ordinary path.
            if self.original_transport_present {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "advertised probe transport requires Trust std descriptor inheritance",
                ));
            }
            return Ok(run(command));
        }
        if guard.is_none() {
            // ZERO extras; the synchronous child borrows this owner's implicit execution.
            *guard = Some(Jobserver::new(0)?);
        }
        let server = guard.as_mut().expect("initialized above");
        server.enable_descendant_handoff()?;
        server.configure_make(command);
        let descriptions =
            server.pipe_descriptors().map(|pipe| [pipe[0].as_raw_fd(), pipe[1].as_raw_fd()]);
        if let Some(descriptions) = descriptions {
            super::member::inherit_descriptions(command, &descriptions)?;
        }
        if self.sdk_present {
            sdk::inherit_original_lease(command)?;
        }
        // Guard and real scheduler survive the complete existing capture/reap.
        Ok(run(command))
    }

    /// Run one producing child using ONLY transport captured at native entry.
    /// The caller must already own the enclosing execution. This serializes
    /// with fixed queries and creates no token, CPU, memory or SDK admission.
    /// Unlike a fixed query, a producing child cannot use a lazily created
    /// empty query pipe when the original transport was absent.
    ///
    /// The callback cannot take ownership of the child. Its private guard
    /// stops its owned process group and reaps it, including callback errors
    /// and unwinding, before unlocking the original scheduler. Detached sessions
    /// are outside this local API's contract; this is not a containment API.
    pub fn run_inherited_child<T>(
        &self,
        command: &mut Command,
        run: impl FnOnce(&mut InheritedChild) -> io::Result<T>,
    ) -> io::Result<T> {
        self.check_interrupted()?;
        self.before_lock();
        let guard =
            self.server.lock().map_err(|_| io::Error::other("poisoned serial probe owner"))?;
        // A queued caller may have passed the first check before the previous
        // borrower was interrupted. No transport or launch precedes this check.
        self.check_interrupted()?;
        if self.original_transport_present {
            if !cfg!(trust_std) {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "inherited command transport requires Trust std descriptor inheritance",
                ));
            }
            if !self.inherited_server_present {
                return Err(io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    "producing child has no original inherited GNU scheduler",
                ));
            }
            let server = guard.as_ref().ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    "producing child has no original inherited GNU scheduler",
                )
            })?;
            server.configure_make(command);
            if let Some(pipe) = server.pipe_descriptors() {
                super::member::inherit_descriptions(
                    command,
                    &[pipe[0].as_raw_fd(), pipe[1].as_raw_fd()],
                )?;
            }
            if self.sdk_present {
                sdk::inherit_original_lease(command)?;
            }
        }
        // Ordinary transport-free callers retain their former local path.
        // A pipe created for an earlier query never becomes producing custody.
        let mut child = InheritedChild::spawn(command)?;
        let consumed = run(&mut child);
        let result = child.finish_callback().and(consumed);
        if result.as_ref().is_err_and(|error| error.kind() == io::ErrorKind::Interrupted) {
            self.interrupted.store(true, std::sync::atomic::Ordering::Release);
        }
        drop(child); // terminal custody BEFORE the serial guard can unlock
        result
    }

    fn before_lock(&self) {
        #[cfg(test)]
        if let Some(rendezvous) = &self.lock_rendezvous {
            rendezvous();
        }
    }

    fn check_interrupted(&self) -> io::Result<()> {
        if self.interrupted.load(std::sync::atomic::Ordering::Acquire) {
            Err(io::Error::new(io::ErrorKind::Interrupted, "original scheduler was interrupted"))
        } else {
            Ok(())
        }
    }

    /// Capture a fixed synchronous query while retaining its exact child through
    /// terminal status, capture errors and unwinding. No output/error is a grant.
    pub fn output(&self, command: &mut Command) -> io::Result<Output> {
        self.with_command(command, |command| {
            // These fixed metadata queries previously used Command::output,
            // whose default stdin is null rather than inherited terminal input.
            command.stdin(Stdio::null());
            let mut stdout = tempfile::tempfile()?;
            let mut stderr = tempfile::tempfile()?;
            command.stdout(Stdio::from(stdout.try_clone()?));
            command.stderr(Stdio::from(stderr.try_clone()?));
            let mut child = QueryChild(command.spawn()?);
            drop(child.0.stdin.take());
            let status = child.0.wait()?;
            stdout.rewind()?;
            stderr.rewind()?;
            let mut out = Vec::new();
            let mut err = Vec::new();
            stdout.read_to_end(&mut out)?;
            stderr.read_to_end(&mut err)?;
            Ok(Output { status, stdout: out, stderr: err })
        })?
    }
}

#[path = "probe_scheduler/inherited_child.rs"]
mod inherited_child;
pub use inherited_child::InheritedChild;

struct QueryChild(Child);
impl Drop for QueryChild {
    fn drop(&mut self) {
        if !matches!(self.0.try_wait(), Ok(Some(_))) {
            let _ = self.0.kill();
            if self.0.wait().is_err() {
                // Releasing the serial guard without terminal custody would
                // permit a second borrower while the original may still run.
                std::process::abort();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn absent_owner() -> ProbeScheduler {
        // Explicit synthetic absence; no inherited transport or SDK admission.
        ProbeScheduler {
            server: Mutex::new(None),
            original_transport_present: false,
            inherited_server_present: false,
            interrupted: std::sync::atomic::AtomicBool::new(false),
            #[cfg(test)]
            lock_rendezvous: None,
            sdk_present: false,
        }
    }

    #[test]
    fn fixed_query_output_retains_exact_bytes_exit_and_null_stdin() {
        let owner = absent_owner();
        let mut print = Command::new("/usr/bin/printf");
        print.args(["%s", "query ü\n"]);
        let output = owner.output(&mut print).unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, "query ü\n".as_bytes());
        assert!(output.stderr.is_empty());
        let output = owner.output(&mut Command::new("/bin/cat")).unwrap();
        assert!(output.status.success());
        assert!(output.stdout.is_empty());
        let output = owner.output(&mut Command::new("/usr/bin/false")).unwrap();
        assert_eq!(output.status.code(), Some(1));
        assert!(owner.output(&mut Command::new("/no/such/fixed-query")).is_err());
        assert!(owner.output(&mut Command::new("/usr/bin/true")).unwrap().status.success());
    }

    #[cfg(not(trust_std))]
    #[test]
    fn stock_cannot_execute_an_original_transport_borrower() {
        let owner = ProbeScheduler {
            server: Mutex::new(None),
            original_transport_present: true,
            inherited_server_present: false,
            interrupted: std::sync::atomic::AtomicBool::new(false),
            #[cfg(test)]
            lock_rendezvous: None,
            sdk_present: false,
        };
        let error = owner.output(&mut Command::new("/no/such/query-must-not-launch")).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::Unsupported);
    }
}

#[cfg(test)]
#[path = "probe_scheduler/tests.rs"]
mod inherited_tests;
