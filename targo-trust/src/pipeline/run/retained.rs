//! Own the original compiler child across finite evidence and qualified tests.

#[cfg(unix)]
use trust_test_execution::retained::{GrantedSession, RuntimeOutput, SessionOwner};

use super::*;

/// A checkpoint is deliberately not an ExitStatus. Only an observed process
/// exit can populate Exited or the final execution status.
pub(super) enum CompileCompletion {
    Exited(ExitStatus),
    Checkpoint(trust_test_execution::PreparedTestsReceipt),
}

impl CompileCompletion {
    pub(super) fn success(&self) -> bool {
        match self {
            Self::Exited(status) => status.success(),
            Self::Checkpoint(_) => true,
        }
    }

    pub(super) fn code(&self) -> i32 {
        match self {
            Self::Exited(status) => child_status_code(status),
            Self::Checkpoint(_) => 0,
        }
    }

    pub(super) fn signal_exit(&self) -> Option<u8> {
        match self {
            Self::Exited(status) => child_signal_exit_code(status),
            Self::Checkpoint(_) => None,
        }
    }

    pub(super) fn is_checkpoint(&self) -> bool {
        matches!(self, Self::Checkpoint(_))
    }

    pub(super) fn require_receipt(
        &self,
        parsed: Option<&trust_test_execution::PreparedTestsReceipt>,
    ) -> Result<(), String> {
        let Self::Checkpoint(actual) = self else { return Ok(()) };
        let parsed = parsed.ok_or("retained compilation omitted its prepared-plan receipt")?;
        if actual.schema != parsed.schema
            || actual.session != parsed.session
            || actual.path != parsed.path
            || actual.sha256 != parsed.sha256
        {
            return Err(
                "retained checkpoint and compiler evidence bind different test plans".into()
            );
        }
        Ok(())
    }
}

/// One owner and one watchdog persist through compilation, qualification and
/// execution. Every early return stops/reaps an unreaped child.
pub(super) struct RunChild {
    child: std::process::Child,
    guard: Option<CompilerProcessGuard>,
    reaped: Option<ExitStatus>,
    retained_session: Option<String>,
    #[cfg(unix)]
    session: Option<SessionOwner>,
    #[cfg(unix)]
    granted: Option<GrantedSession>,
    #[cfg(unix)]
    runtime: Vec<RuntimeDrain>,
}

impl RunChild {
    pub(super) fn spawn(
        command: &mut Command,
        retained_session: Option<&str>,
        bounds: CompilerProcessBounds,
    ) -> Result<Self, ChildSetupError> {
        CompilerProcessGuard::configure(command);
        #[cfg(unix)]
        let (child, session, output) = if let Some(session) = retained_session {
            let deadline = Instant::now()
                .checked_add(bounds.absolute)
                .ok_or_else(|| "retained compiler deadline is not representable".to_owned())?;
            let (child, owner, output) = SessionOwner::spawn(command, session, deadline)
                .map_err(|error| format!("could not start retained compiler session: {error}"))?;
            (child, Some(owner), Some(output))
        } else {
            (
                command.spawn().map_err(|error| format!("could not spawn compiler: {error}"))?,
                None,
                None,
            )
        };
        #[cfg(not(unix))]
        let child = {
            if retained_session.is_some() {
                return Err("retained verified execution requires a Unix native companion"
                    .to_owned()
                    .into());
            }
            command.spawn().map_err(|error| format!("could not spawn compiler: {error}"))?
        };
        let guard = CompilerProcessGuard::start(child.id(), bounds);
        let mut owned = Self {
            child,
            guard: Some(guard),
            reaped: None,
            retained_session: retained_session.map(str::to_owned),
            #[cfg(unix)]
            session,
            #[cfg(unix)]
            granted: None,
            #[cfg(unix)]
            runtime: Vec::new(),
        };
        #[cfg(unix)]
        if let Some(output) = output {
            // Runtime data can never enter a compiler/proof parser or extend
            // the compiler watchdog's progress clock.
            owned.runtime = RuntimeDrain::start(output)
                .map_err(|error| format!("could not drain retained runtime output: {error}"))?;
        }
        Ok(owned)
    }

    pub(super) fn child_mut(&mut self) -> &mut std::process::Child {
        &mut self.child
    }

    pub(super) fn progress(&self) -> Arc<CompilerProgress> {
        self.guard.as_ref().expect("live process guard").progress()
    }

    pub(super) fn execution_started(&self) -> bool {
        #[cfg(unix)]
        {
            self.granted.is_some()
        }
        #[cfg(not(unix))]
        {
            false
        }
    }

    pub(super) fn compile_completion(&mut self) -> Result<CompileCompletion, ChildSetupError> {
        #[cfg(unix)]
        if self.session.is_some() {
            loop {
                let guard = self.guard.as_ref().expect("live compile guard");
                if guard.state.timed_out() {
                    return Err(ChildSetupError::CouldNotRun(guard.state.timeout_message()));
                }
                let deadline = guard.state.absolute_deadline();
                let ready = self.session.as_mut().unwrap().poll_ready(deadline);
                match ready {
                    Ok(Some(ready)) if ready.is_success() => {
                        let receipt =
                            ready.receipt().expect("successful checkpoint receipt").clone();
                        if crate::bounded_process::exited_without_reaping(&mut self.child)
                            .map_err(|error| error.to_string())?
                        {
                            return Err("retained compiler exited before qualification"
                                .to_owned()
                                .into());
                        }
                        guard.state.enter_qualification()?;
                        return Ok(CompileCompletion::Checkpoint(receipt));
                    }
                    Ok(Some(_failed)) => {
                        // Failure is data until the real child exit is observed.
                        // It can never stand in for a successful checkpoint.
                        return self.wait_actual_exit().map(CompileCompletion::Exited);
                    }
                    Ok(None) => {}
                    Err(error) => {
                        if crate::bounded_process::exited_without_reaping(&mut self.child)
                            .map_err(|error| error.to_string())?
                        {
                            let status = self.wait_actual_exit()?;
                            if !status.success() {
                                return Ok(CompileCompletion::Exited(status));
                            }
                        }
                        return Err(format!("retained compiler checkpoint failed: {error}").into());
                    }
                }
                if crate::bounded_process::exited_without_reaping(&mut self.child)
                    .map_err(|error| error.to_string())?
                {
                    let status = self.wait_actual_exit()?;
                    if status.success() {
                        return Err("native companion exited without its retained checkpoint"
                            .to_owned()
                            .into());
                    }
                    return Ok(CompileCompletion::Exited(status));
                }
                thread::sleep(Duration::from_millis(10));
            }
        }
        self.wait_actual_exit().map(CompileCompletion::Exited)
    }

    pub(super) fn grant_and_wait(
        &mut self,
        qualified: &QualifiedTestExecution,
        session: &str,
        authority: &TestExecutionAuthority,
    ) -> Result<ExitStatus, ChildSetupError> {
        qualified.require_session(session)?;
        if self.retained_session.as_deref() != Some(session) {
            return Err("qualification belongs to a different original compiler child"
                .to_owned()
                .into());
        }
        #[cfg(unix)]
        {
            let guard =
                self.guard.as_ref().ok_or_else(|| "retained child already exited".to_owned())?;
            guard
                .state
                .enter_execution(COMPILER_PROCESS_TIMEOUT)
                .map_err(ChildSetupError::CouldNotRun)?;
            let deadline = guard.state.absolute_deadline();
            let owner = self
                .session
                .take()
                .ok_or_else(|| "original retained session is absent".to_owned())?;
            self.granted =
                Some(owner.grant(&authority.path, &authority.inventory_sha256, deadline).map_err(
                    |error| format!("could not grant the retained test inventory: {error}"),
                )?);
            self.wait_actual_exit()
        }
        #[cfg(not(unix))]
        {
            let _ = authority;
            Err("retained verified execution requires a Unix native companion".to_owned().into())
        }
    }

    fn wait_actual_exit(&mut self) -> Result<ExitStatus, ChildSetupError> {
        let guard =
            self.guard.as_mut().ok_or_else(|| "compiler child was already reaped".to_owned())?;
        #[cfg(unix)]
        let outcome = if let Some(session) = self.granted.as_mut() {
            wait_for_retained_exit(&mut self.child, guard, session)
        } else {
            wait_for_compiler_process(&mut self.child, guard)
        };
        #[cfg(not(unix))]
        let outcome = wait_for_compiler_process(&mut self.child, guard);
        let status = match outcome {
            Ok(status) => status,
            Err(error) => {
                // Settle ownership before publishing an orchestration error.
                // The unreaped leader still reserves its PID during cleanup.
                guard.abort_before_reap(&mut self.child);
                self.reaped = self.child.wait().ok();
                let timed_out =
                    guard.state.timed_out() || error.kind() == std::io::ErrorKind::TimedOut;
                self.guard.take();
                let message = format!("could not wait for original compiler child: {error}");
                return Err(if timed_out {
                    ChildSetupError::CouldNotRun(message)
                } else {
                    ChildSetupError::Setup(message)
                });
            }
        };
        self.reaped = Some(status);
        self.guard.take().unwrap().finish().map_err(ChildSetupError::CouldNotRun)?;
        #[cfg(unix)]
        for drain in self.runtime.drain(..) {
            drain.finish().map_err(ChildSetupError::Setup)?;
        }
        #[cfg(unix)]
        if status.success() && self.granted.as_ref().is_some_and(|session| !session.drained()) {
            return Err("retained child exited successfully without draining its original queue"
                .to_owned()
                .into());
        }
        Ok(status)
    }
}

#[cfg(unix)]
fn wait_for_retained_exit(
    child: &mut std::process::Child,
    guard: &mut CompilerProcessGuard,
    session: &mut GrantedSession,
) -> std::io::Result<ExitStatus> {
    loop {
        // A native drained event is neither a child exit nor a proof result.
        // It only permits normal endpoint teardown while the original owner
        // still waits for the actual exit under its unchanged watchdog.
        let connected = session.check_connected(guard.state.absolute_deadline());
        let exited = crate::bounded_process::exited_without_reaping(child)?;
        if let Err(error) = connected {
            if error.kind() == std::io::ErrorKind::UnexpectedEof && exited {
                // A real unsuccessful exit keeps its actual failure status.
                // The owner separately refuses exit0 without DrainComplete.
                return wait_for_compiler_process(child, guard);
            }
            return Err(error);
        }
        if exited {
            // Inspect queued control bytes even if exit won the previous race.
            // Extra/replayed frames cannot hide behind a successful process.
            if let Err(error) = session.check_connected(guard.state.absolute_deadline()) {
                if error.kind() != std::io::ErrorKind::UnexpectedEof {
                    return Err(error);
                }
            }
            return wait_for_compiler_process(child, guard);
        }
        thread::sleep(Duration::from_millis(10));
    }
}

impl Drop for RunChild {
    fn drop(&mut self) {
        #[cfg(unix)]
        {
            // Closing the original controller also cancels the child's queue.
            self.granted.take();
            self.session.take();
        }
        if self.reaped.is_none() {
            if let Some(guard) = &mut self.guard {
                guard.abort_before_reap(&mut self.child);
            }
            let _ = self.child.wait();
        }
    }
}

#[cfg(unix)]
struct RuntimeDrain {
    output: Option<CompilerOutputChannel<()>>,
    interrupt: std::os::unix::net::UnixStream,
}

#[cfg(unix)]
impl RuntimeDrain {
    fn start(output: RuntimeOutput) -> std::io::Result<Vec<Self>> {
        let mut drains = Vec::new();
        for (stream, stderr) in [(output.stdout, false), (output.stderr, true)] {
            let interrupt = stream.try_clone()?;
            let output =
                spawn_pipe_parser(stream, Arc::new(CompilerProgress::new()), move |mut source| {
                    let mut buffer = [0u8; 16 * 1024];
                    loop {
                        // Compiler/qualification diagnostics still use the same
                        // console. Never hold that console lock across the idle
                        // runtime stream's blocking read before a grant.
                        let read = source
                            .read(&mut buffer)
                            .map_err(|error| format!("runtime output drain failed: {error}"))?;
                        if read == 0 {
                            return Ok(());
                        }
                        let written = if stderr {
                            std::io::stderr().lock().write_all(&buffer[..read])
                        } else {
                            std::io::stdout().lock().write_all(&buffer[..read])
                        };
                        written.map_err(|error| format!("runtime output echo failed: {error}"))?;
                    }
                });
            drains.push(Self { output: Some(output), interrupt });
        }
        Ok(drains)
    }

    fn finish(mut self) -> Result<(), String> {
        receive_compiler_output(self.output.take().unwrap(), "untrusted retained runtime output")
    }
}

#[cfg(unix)]
impl Drop for RuntimeDrain {
    fn drop(&mut self) {
        let _ = self.interrupt.shutdown(std::net::Shutdown::Read);
    }
}

#[cfg(all(test, unix))]
mod tests {
    use trust_test_execution::retained::RetainedChild;

    use super::*;

    const SESSION: &str = "a7427213850878f98b2f7159bebc9ade72864e33d57c091dbb5b76ad4b201b72";
    const ACTOR: &str = "pipeline::run::retained::tests::retained_frontend_actor";

    #[test]
    #[ignore = "entered only as an owned retained-session child"]
    fn retained_frontend_actor() {
        let mode = std::env::var("CARGO_RETAINED_FRONTEND_ACTOR").unwrap();
        let mut injected = if mode == "extra" {
            use std::os::fd::BorrowedFd;
            // SAFETY: this test actor's original stdin is the private socket;
            // the owned duplicate is used solely to inject malformed traffic.
            Some(std::os::unix::net::UnixStream::from(unsafe {
                BorrowedFd::borrow_raw(0).try_clone_to_owned().unwrap()
            }))
        } else {
            None
        };
        let mut endpoint =
            RetainedChild::capture_stdin(Instant::now() + Duration::from_secs(10)).unwrap();
        let deadline = endpoint.deadline();
        if mode == "missing" {
            std::process::exit(0);
        }
        if mode == "failed" {
            endpoint.publish_compile_failed("actual compiler rejection", deadline).unwrap();
            std::process::exit(101);
        }
        println!("finite compiler evidence");
        let receipt = trust_test_execution::PreparedTestsReceipt {
            schema: trust_test_execution::RECEIPT_SCHEMA.into(),
            session: SESSION.into(),
            path: std::env::var("CARGO_RETAINED_PLAN").unwrap(),
            sha256: "b".repeat(64),
        };
        endpoint.publish_ready(&receipt, deadline).unwrap();
        loop {
            match endpoint.poll_grant(deadline) {
                Ok(Some(grant)) => {
                    assert_eq!(grant.session(), SESSION);
                    assert_eq!(grant.plan_sha256(), receipt.sha256);
                    if mode == "close" {
                        drop(endpoint);
                        thread::sleep(Duration::from_secs(2));
                        std::fs::write(
                            std::env::var_os("CARGO_RETAINED_MARKER").unwrap(),
                            b"escaped",
                        )
                        .unwrap();
                        std::process::exit(0);
                    }
                    if let Some(mut socket) = injected.take() {
                        socket.write_all(&[0xff; 4]).unwrap();
                        thread::sleep(Duration::from_secs(2));
                        std::fs::write(
                            std::env::var_os("CARGO_RETAINED_MARKER").unwrap(),
                            b"escaped",
                        )
                        .unwrap();
                        std::process::exit(0);
                    }
                    std::fs::write(std::env::var_os("CARGO_RETAINED_MARKER").unwrap(), b"ran")
                        .unwrap();
                    println!("untrusted runtime output after the grant");
                    std::io::stdout().flush().unwrap();
                    endpoint.publish_drained(deadline).unwrap();
                    std::process::exit(0);
                }
                Ok(None) => thread::sleep(Duration::from_millis(5)),
                Err(_) => return,
            }
        }
    }

    fn actor(mode: &str, root: &Path) -> RunChild {
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args(["--ignored", "--exact", ACTOR, "--nocapture"])
            .env("CARGO_RETAINED_FRONTEND_ACTOR", mode)
            .env("CARGO_RETAINED_PLAN", root.join("plan.json"))
            .env("CARGO_RETAINED_MARKER", root.join("ran"))
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        RunChild::spawn(
            &mut command,
            Some(SESSION),
            CompilerProcessBounds::flat(Duration::from_secs(10)),
        )
        .unwrap()
    }

    #[test]
    fn original_child_survives_finite_evidence_until_grant_without_respawning() {
        let root = tempfile::tempdir().unwrap();
        let mut process = actor("ready", root.path());
        let progress = process.progress();
        let mut stdout = process.child_mut().stdout.take().unwrap();
        let mut stderr = process.child_mut().stderr.take().unwrap();
        let checkpoint = process.compile_completion().unwrap();
        assert!(checkpoint.is_checkpoint());
        assert!(process.child_mut().try_wait().unwrap().is_none());
        let mut evidence = String::new();
        stdout.read_to_string(&mut evidence).unwrap();
        stderr.read_to_string(&mut String::new()).unwrap();
        assert!(evidence.contains("finite compiler evidence"));
        assert!(!root.path().join("ran").exists());
        assert!(process.child_mut().try_wait().unwrap().is_none());
        // This actor tests process/session ownership. The production manifest
        // and proof gates have their own native authenticated-image controls.
        let qualified = QualifiedTestExecution::for_authority_writer_test(SESSION);
        let authority = TestExecutionAuthority {
            path: root.path().join("authority.json"),
            target_directory: root.path().display().to_string(),
            executables: Vec::new(),
            inventory_sha256: "c".repeat(64),
            plan: None,
        };
        assert!(process.grant_and_wait(&qualified, SESSION, &authority).unwrap().success());
        assert!(process.execution_started());
        assert_eq!(std::fs::read(root.path().join("ran")).unwrap(), b"ran");
        assert_eq!(
            progress.last_progress(),
            None,
            "untrusted runtime output cannot update the compiler progress clock"
        );
    }

    #[test]
    fn checkpoint_receipt_mismatch_missing_checkpoint_and_real_compile_failure_refuse() {
        let root = tempfile::tempdir().unwrap();
        let mut process = actor("ready", root.path());
        let checkpoint = process.compile_completion().unwrap();
        let CompileCompletion::Checkpoint(receipt) = &checkpoint else { panic!("checkpoint") };
        assert!(checkpoint.require_receipt(Some(receipt)).is_ok());
        let mut changed = receipt.clone();
        changed.sha256 = "d".repeat(64);
        assert!(checkpoint.require_receipt(Some(&changed)).is_err());
        assert!(checkpoint.require_receipt(None).is_err());
        let foreign = "e".repeat(64);
        let qualified = QualifiedTestExecution::for_authority_writer_test(&foreign);
        let authority = TestExecutionAuthority {
            path: root.path().join("foreign-authority.json"),
            target_directory: root.path().display().to_string(),
            executables: Vec::new(),
            inventory_sha256: "c".repeat(64),
            plan: None,
        };
        assert!(process.grant_and_wait(&qualified, &foreign, &authority).is_err());
        assert!(!process.execution_started());
        drop(process);
        assert!(!root.path().join("ran").exists());

        let mut process = actor("missing", root.path());
        assert!(process.compile_completion().is_err());
        assert!(!process.execution_started());
        drop(process);
        let mut process = actor("failed", root.path());
        let failed = process.compile_completion().unwrap();
        assert!(!failed.is_checkpoint());
        assert_eq!(failed.code(), 101);
        assert!(!failed.success());
        assert!(!root.path().join("ran").exists());
    }

    #[test]
    fn retained_phases_keep_original_ceiling_and_runtime_progress_cannot_extend_the_cap() {
        let bounds = CompilerProcessBounds {
            silent: Duration::ZERO,
            idle: Duration::ZERO,
            absolute: Duration::from_secs(2),
        };
        let state = CompilerTimeoutState::new(std::process::id(), bounds);
        let original = state.absolute_deadline();
        state.enter_qualification().unwrap();
        assert!(state.poll().is_ok(), "qualification is expected to be silent");
        assert!(state.enter_qualification().is_err());
        state.enter_execution(Duration::from_millis(15)).unwrap();
        assert_eq!(state.absolute_deadline(), original);
        thread::sleep(Duration::from_millis(25));
        state.progress.record();
        let detail = state.poll().expect_err("runtime output must not buy a fresh interval");
        assert_eq!(detail.bound, CompilerTimeoutBound::Absolute);
        assert!(state.enter_execution(Duration::from_secs(30)).is_err());
    }

    #[test]
    fn post_grant_custody_loss_and_malformed_traffic_stop_and_reap_the_original_child() {
        for mode in ["close", "extra"] {
            let root = tempfile::tempdir().unwrap();
            let mut process = actor(mode, root.path());
            assert!(process.compile_completion().unwrap().is_checkpoint());
            let qualified = QualifiedTestExecution::for_authority_writer_test(SESSION);
            let authority = TestExecutionAuthority {
                path: root.path().join("authority.json"),
                target_directory: root.path().display().to_string(),
                executables: Vec::new(),
                inventory_sha256: "c".repeat(64),
                plan: None,
            };
            let error = process
                .grant_and_wait(&qualified, SESSION, &authority)
                .expect_err("a private control failure cannot become a successful child exit");
            assert!(error.to_string().contains("original compiler child"), "{error}");
            assert!(process.child_mut().try_wait().unwrap().is_some(), "child was not reaped");
            assert!(!root.path().join("ran").exists(), "control failure did not stop child");
        }
    }
}
