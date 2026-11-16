//! Trust: owned GNU transport for Bootstrap queries and embedded producers.
//!
//! This creates no CPU/memory admission or extra GNU credit. A GNU-free owner
//! lends its existing implicit execution through an EMPTY pipe, just as Targo's
//! external serial phase does. One mutex covers the complete child lifecycle.
//! Compiler argv, SDK capture and resource/proof refusals remain unchanged.
//! Embedded producers borrow this SAME mutex/server through their actual child
//! and original readers. A typed exact-child join is required to return that
//! implicit borrower; unresolved ownership permanently refuses later dispatch.

use std::fs::File;
use std::io::{self, Read, Seek};
use std::process::{Child, Command, Output, Stdio};
use std::sync::{Arc, Mutex, OnceLock};

use jobserver_utils::Jobserver;

#[cfg(any(target_os = "macos", target_os = "linux"))]
mod producer;
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) use producer::{ProducerBorrow, prepare_producer};

static CAPTURED: OnceLock<Result<Arc<Scheduler>, String>> = OnceLock::new();

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) mod host_graph;

pub(crate) fn hosted_graph_active() -> bool {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        host_graph::installed()
    }
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    {
        false
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
mod native_work;
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) use native_work::run_native_worker;

/// Install the SAME already captured scheduler from the enclosing Targo.
/// No environment import, pipe creation, token acquisition or replenishment.
pub(crate) fn install_original(server: Jobserver) -> Result<(), String> {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    let sdk_present = trust_resource_controller::client::sdk::original_lease_present()
        .map_err(|error| error.to_string())?;
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    let sdk_present = false;
    CAPTURED
        .set(Ok(Arc::new(Scheduler {
            state: Mutex::new(State {
                server: Some(server),
                embedded_original: true,
                producer_failed: false,
                original_transport_present: true,
                sdk_present,
            }),
        })))
        .map_err(|_| "bootstrap scheduler was already captured or installed".to_owned())
}

/// Synthetic test owners explicitly have no SDK transport; they confer no SDK
/// admission. Real native-entry/embedding paths above never use this installer.
#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
pub(crate) fn install_test_original(server: Jobserver) -> Result<(), String> {
    let sdk = &trust_resource_controller::client::sdk::original_lease_present;
    if sdk().is_err() {
        assert!(
            std::env::var_os("ATERM_SDK_LEASE_V3").is_none(),
            "synthetic owner cannot capture an advertised SDK lease late"
        );
        let pending = trust_resource_controller::client::sdk::snapshot_sdk_lease()
            .map_err(|error| error.to_string())?;
        // SAFETY: this synthetic test has proven no advertised SDK description;
        // the absent snapshot neither opens nor imports any descriptor.
        unsafe { trust_resource_controller::client::sdk::capture_sdk_lease(pending) }
            .map_err(|error| error.to_string())?;
    }
    install_original(server)
}

struct State {
    server: Option<Jobserver>,
    embedded_original: bool,
    // An abandoned producing borrower never becomes another implicit slot.
    // The same captured server remains retained; every later dispatch refuses.
    producer_failed: bool,
    original_transport_present: bool,
    sdk_present: bool,
}

/// A chosen scheduler and one exclusively borrowed implicit execution. The
/// empty scheduler is born only when an actual synchronous query is dispatched.
pub(crate) struct Scheduler {
    state: Mutex<State>,
}

/// Capture only at genuine native entry, before any descriptor-opening work.
/// Invalid advertised transport cannot become a serial fallback.
///
/// # Safety
/// No file open or arbitrary callback may precede this call. Bootstrap's native
/// main calls it first; embeddings must meet the same precondition themselves.
pub unsafe fn capture_at_entry() -> Result<(), String> {
    if CAPTURED.get().is_some() {
        return Err("bootstrap scheduler was already captured".into());
    }
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    let original_sdk = trust_resource_controller::client::sdk::snapshot_sdk_lease()
        .map_err(|error| error.to_string())?;
    let required_handoff = [
        jobserver_utils::CPU_HANDOFF_ENV,
        jobserver_utils::FIXED_CLAIM_HANDOFF_ENV,
        "BUILD_SLOT_CPU_PROTOCOL",
    ]
    .iter()
    .any(|key| std::env::var_os(key).is_some());
    let sdk_advertised = std::env::var_os("ATERM_SDK_LEASE_V3").is_some();
    let handoff_advertised = std::env::var_os(jobserver_utils::DESCENDANT_HANDOFF_ENV).is_some();
    // SAFETY: the caller guarantees the original descriptor identity at entry.
    let captured = unsafe { Jobserver::from_env_with_handoff_checked() }
        .map_err(|error| error.to_string())
        .and_then(|server| {
            if handoff_advertised && server.is_none() {
                Err("advertised bootstrap scheduler has no valid inherited transport".into())
            } else {
                Ok(Arc::new(Scheduler {
                    state: Mutex::new(State {
                        original_transport_present: server.is_some()
                            || sdk_advertised
                            || handoff_advertised
                            || required_handoff,
                        sdk_present: sdk_advertised,
                        server,
                        embedded_original: false,
                        producer_failed: false,
                    }),
                }))
            }
        });
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    // SAFETY: only the fixed original GNU importer followed the SDK snapshot.
    unsafe { trust_resource_controller::client::sdk::capture_sdk_lease(original_sdk) }
        .map_err(|error| error.to_string())?;
    CAPTURED.set(captured).map_err(|_| "bootstrap scheduler capture raced".to_owned())?;
    selected().map(|_| ()).map_err(|error| error.to_string())
}

/// Trust: explicit absent-transport owner for isolated synthetic controls only.
/// Genuine library entry captures the actual owner before libtest. Session never
/// installs this fallback, and the uncaptured fixture mode confers no authority.
#[cfg(test)]
pub(crate) fn install_test_owner() {
    CAPTURED.get_or_init(|| {
        Ok(Arc::new(Scheduler {
            state: Mutex::new(State {
                server: None,
                embedded_original: false,
                producer_failed: false,
                original_transport_present: false,
                sdk_present: false,
            }),
        }))
    });
}

fn selected() -> io::Result<&'static Arc<Scheduler>> {
    CAPTURED
        .get()
        .ok_or_else(|| {
            io::Error::other("bootstrap metadata requires native early scheduler capture")
        })?
        .as_ref()
        .map_err(|error| io::Error::other(error.clone()))
}

pub(crate) fn output(command: &mut Command, stdout: bool, stderr: bool) -> io::Result<Output> {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if let Some(actual) = host_graph::output(command, stdout, stderr) {
        return actual;
    }
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    if let Some(scope) = super::exec::protected_scope()? {
        let actual = protected_output(command, &scope, stdout, stderr)?;
        return Err(io::Error::other(format!(
            "actual child {}; {}",
            actual.output.status, actual.reason
        )));
    }
    selected()?.output(command, stdout, stderr)
}

/// Trust: only the maintained command wrapper knows whether its environment
/// was cleared and whether stdin is inherited. Raw Command callers retain
/// ordinary behavior; they cannot impersonate a projected Full command.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn projected_output(
    command: &mut Command,
    stdout: bool,
    stderr: bool,
    inputs: super::exec::OriginalCommandInputs,
) -> io::Result<Output> {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if let Some(actual) = host_graph::projected_output(command, stdout, stderr, inputs) {
        return actual;
    }
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    let _ = (inputs.environment_cleared, inputs.inherited_stdin);
    output(command, stdout, stderr)
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod bounded;

/// Only the completed source-built compiler constructor selects this route.
/// A hosted/protected query needs its own typed bounded transport; never fall
/// back to a standalone child outside that owner.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) fn bounded_output(
    command: &mut Command,
    deadline: std::time::Instant,
    bytes: u64,
) -> io::Result<Output> {
    if hosted_graph_active() || super::exec::protected_scope()?.is_some() {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "bounded compiler discovery requires a qualified owner transport",
        ));
    }
    selected()?.bounded_output(command, deadline, bytes)
}

// Trust: after installation ALL query dispatch uses the same bounded original
// producer borrower. Calling the old unbounded metadata mutex while streaming
// must not create a reentrant implicit execution or block forever.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn protected_output(
    command: &mut Command,
    scope: &build_helper::trust_repo_lock::management::ScopeDispatch,
    stdout: bool,
    stderr: bool,
) -> io::Result<super::exec::UnresolvedOutput> {
    let registration = scope.register_launch()?;
    // Preserve the normal synchronous query's seekable captures. The SAME
    // original capture Files enter the registry BEFORE actual child delivery.
    let out =
        capture(command, stdout, true)?.map(|file| registration.capture_file(file)).transpose()?;
    let err =
        capture(command, stderr, false)?.map(|file| registration.capture_file(file)).transpose()?;
    let producer = prepare_producer(command, &registration, scope.deadline())?;
    let mut child = registration.spawn(command)?;
    let status = child.wait()?;
    let stdout = out.map(|capture| capture.read_after_wait()).transpose()?.unwrap_or_default();
    let stderr = err.map(|capture| capture.read_after_wait()).transpose()?.unwrap_or_default();
    Ok(super::exec::UnresolvedOutput::after_join(
        Output { status, stdout, stderr },
        producer,
        child.joined(),
    ))
}

/// Retains the actual Child until terminal, even when waiting/capturing errors
/// or unwinding. It drops BEFORE the scheduler's exclusive borrower is released.
struct Running(Child);
impl Drop for Running {
    fn drop(&mut self) {
        // A reaped child returns its saved status; a still-live owned child is
        // killed and waited. Never release the implicit borrower while it runs.
        if !matches!(self.0.try_wait(), Ok(Some(_))) {
            let _ = self.0.kill();
            if self.0.wait().is_err() {
                // No next implicit borrower may run if terminal custody cannot
                // be established. Aborting the owner cannot publish success.
                std::process::abort();
            }
        }
    }
}

impl Scheduler {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    fn bounded_output(
        &self,
        command: &mut Command,
        deadline: std::time::Instant,
        bytes: u64,
    ) -> io::Result<Output> {
        let mut state = loop {
            if std::time::Instant::now() >= deadline {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "compiler discovery borrower deadline",
                ));
            }
            match self.state.try_lock() {
                Ok(state) => break state,
                Err(std::sync::TryLockError::Poisoned(_)) => {
                    return Err(io::Error::other("poisoned metadata borrower"));
                }
                Err(std::sync::TryLockError::WouldBlock) => {
                    std::thread::sleep(std::time::Duration::from_millis(5));
                }
            }
        };
        prepare_original(&mut state, command)?;
        // Retain SAME implicit execution and SDK/GNU originals through reap.
        bounded::run(command, deadline, bytes)
    }

    fn output(&self, command: &mut Command, stdout: bool, stderr: bool) -> io::Result<Output> {
        let mut state =
            self.state.lock().map_err(|_| io::Error::other("poisoned metadata borrower"))?;
        prepare_original(&mut state, command)?;
        // Seekable private captures let us retain Child through every wait and
        // output error without pipe deadlock or detached reader/worker threads.
        let mut out = capture(command, stdout, true)?;
        let mut err = capture(command, stderr, false)?;
        let mut running = Running(command.spawn()?);
        drop(running.0.stdin.take());
        let status = running.0.wait()?;
        let stdout = contents(&mut out)?;
        let stderr = contents(&mut err)?;
        drop(running); // terminal before the exclusive state guard can drop
        Ok(Output { status, stdout, stderr })
    }
}

fn prepare_original(state: &mut State, command: &mut Command) -> io::Result<()> {
    if state.producer_failed {
        return Err(io::Error::other("original producing borrower is unresolved"));
    }
    if !scheduler_transport_supported() && state.original_transport_present {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "original metadata transport requires Trust std descriptor inheritance",
        ));
    }
    if scheduler_transport_supported() && state.server.is_none() {
        // ZERO extras: one child borrows this owner's existing implicit
        // execution. No jobs/environment integer is used as authority.
        state.server = Some(Jobserver::new(0)?);
    }
    if scheduler_transport_supported() {
        configure_original_transport(
            state
                .server
                .as_ref()
                .ok_or_else(|| io::Error::other("metadata scheduler was not retained"))?,
            command,
            state.sdk_present,
        )?;
    }
    Ok(())
}

fn capture(command: &mut Command, enabled: bool, stdout: bool) -> io::Result<Option<File>> {
    let file = enabled.then(tempfile::tempfile).transpose()?;
    let stdio = match &file {
        Some(file) => Stdio::from(file.try_clone()?),
        None => Stdio::inherit(),
    };
    if stdout {
        command.stdout(stdio);
    } else {
        command.stderr(stdio);
    }
    Ok(file)
}

fn contents(file: &mut Option<File>) -> io::Result<Vec<u8>> {
    let mut result = Vec::new();
    if let Some(file) = file {
        file.rewind()?;
        file.read_to_end(&mut result)?;
    }
    Ok(result)
}

#[cfg(all(test, unix))]
mod tests;

/// Forward actual retained descriptions; advertisements alone are not transport.
fn configure_original_transport(
    server: &Jobserver,
    command: &mut Command,
    sdk_present: bool,
) -> io::Result<()> {
    server.configure_make(command);
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    if scheduler_transport_supported() {
        use std::os::fd::AsRawFd;
        if let Some(pipe) = server.pipe_descriptors() {
            trust_resource_controller::client::inherit_descriptions(
                command,
                &[pipe[0].as_raw_fd(), pipe[1].as_raw_fd()],
            )?;
        }
        if sdk_present {
            trust_resource_controller::client::sdk::inherit_original_lease(command)?;
        }
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    let _ = sdk_present;
    Ok(())
}

// Trust: only native Unix descriptions need the Trust std export capability.
// Other platforms retain jobserver's supported transport (including named Windows semaphores).
fn scheduler_transport_supported() -> bool {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        trust_resource_controller::client::explicit_inheritance_supported()
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        true
    }
}

/// The ordinary compiletest root borrows this same owner until its exact child
/// retires. This is transport custody only, never parallel-case admission.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) struct StreamingBorrow {
    child: Child,
    state: std::sync::MutexGuard<'static, State>,
    child_reaped: bool,
}
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn stream_original(command: &mut Command) -> io::Result<StreamingBorrow> {
    let mut state = selected()?
        .state
        .lock()
        .map_err(|_| io::Error::other("poisoned original streaming borrower"))?;
    if state.producer_failed {
        return Err(io::Error::other("original producing borrower is unresolved"));
    }
    if !scheduler_transport_supported() && state.original_transport_present {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "original streaming transport requires Trust std",
        ));
    }
    if scheduler_transport_supported() {
        if state.server.is_none() {
            state.server = Some(Jobserver::new(0)?);
        }
        configure_original_transport(state.server.as_ref().unwrap(), command, state.sdk_present)?;
    }
    let child = command.spawn()?;
    Ok(StreamingBorrow { child, state, child_reaped: false })
}
#[cfg(any(target_os = "macos", target_os = "linux"))]
impl StreamingBorrow {
    pub(crate) fn take_stdout(&mut self) -> Option<std::process::ChildStdout> {
        self.child.stdout.take()
    }
    pub(crate) fn take_stderr(&mut self) -> Option<std::process::ChildStderr> {
        self.child.stderr.take()
    }
    pub(crate) fn wait(mut self) -> io::Result<std::process::ExitStatus> {
        let status = self.child.wait()?;
        self.child_reaped = true;
        Ok(status)
    }
}
#[cfg(any(target_os = "macos", target_os = "linux"))]
impl Drop for StreamingBorrow {
    fn drop(&mut self) {
        if !self.child_reaped {
            // Errors/unwind cannot return a reusable implicit borrower.
            self.state.producer_failed = true;
            if !matches!(self.child.try_wait(), Ok(Some(_))) {
                let _ = self.child.kill();
                if self.child.wait().is_err() {
                    std::process::abort();
                }
            }
        }
    }
}
