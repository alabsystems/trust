//! See [`JobState`].

use std::{
    cell::{Cell, RefCell},
    marker,
    sync::Arc,
};

use cargo_util::ProcessBuilder;

use crate::compiler::future_incompat::FutureBreakageItem;
use crate::compiler::locking::LockKey;
use crate::compiler::timings::SectionTiming;
use crate::context::WarningHandling;
use crate::util::Queue;
use crate::util::interning::InternedString;
use crate::util::log_message::LogMessage;
use crate::{CargoResult, compiler::locking::LockManager};

use super::{Artifact, DiagDedupe, Job, JobId, Message};

/// A `JobState` is constructed by `JobQueue::run` and passed to `Job::run`. It includes everything
/// necessary to communicate between the main thread and the execution of the job.
///
/// The job may execute on either a dedicated thread or the main thread. If the job executes on the
/// main thread, the `output` field must be set to prevent a deadlock.
pub struct JobState<'a, 'gctx> {
    /// Channel back to the main thread to coordinate messages and such.
    ///
    /// When the `output` field is `Some`, care must be taken to avoid calling `push_bounded` on
    /// the message queue to prevent a deadlock.
    messages: Arc<Queue<Message>>,

    /// Normally output is sent to the job queue with backpressure. When the job is fresh
    /// however we need to immediately display the output to prevent a deadlock as the
    /// output messages are processed on the same thread as they are sent from. `output`
    /// defines where to output in this case.
    ///
    /// Currently the [`Shell`] inside [`GlobalContext`] is wrapped in a `RefCell` and thus can't
    /// be passed between threads. This means that it isn't possible for multiple output messages
    /// to be interleaved. In the future, it may be wrapped in a `Mutex` instead. In this case
    /// interleaving is still prevented as the lock would be held for the whole printing of an
    /// output message.
    ///
    /// [`Shell`]: cargo_util_terminal::Shell
    /// [`GlobalContext`]: crate::GlobalContext
    output: Option<&'a DiagDedupe<'gctx>>,

    /// The job id that this state is associated with, used when sending
    /// messages back to the main thread.
    id: JobId,

    /// Whether or not we're expected to have a call to `rmeta_produced`. Once
    /// that method is called this is dynamically set to `false` to prevent
    /// sending a double message later on.
    rmeta_required: Cell<bool>,

    /// Manages locks for build units when fine grain locking is enabled.
    lock_manager: Arc<LockManager>,

    warning_handling: WarningHandling,
    // Actual branch, updated only by the ordinary under-lock recheck. A
    // planned dirty job that became fresh must not invent a compiler attempt.
    current_warm: Cell<bool>,
    record_workload_output: bool,
    original_command: RefCell<
        Option<(
            Arc<crate::compiler::qualification_command::Capture>,
            crate::compiler::qualification_command::PendingCommand,
        )>,
    >,

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    resources: Option<Arc<crate::compiler::resource_runtime::RootContext>>,
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    bootstrap_execution: Option<Arc<crate::context::bootstrap_full::QueuedExecutor>>,

    // Historical versions of Cargo made use of the `'a` argument here, so to
    // leave the door open to future refactorings keep it here.
    _marker: marker::PhantomData<&'a ()>,
}

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod original_command_tests {
    use super::*;
    use crate::compiler::job_queue::{Artifact, Freshness, Work};
    use crate::compiler::qualification_command::{
        self, FailedCommand, Observer, OriginalUnitCommand,
    };
    use std::sync::Mutex;
    #[derive(Default)]
    struct Recorded(
        Mutex<Vec<Result<Arc<OriginalUnitCommand>, String>>>,
        Mutex<Option<std::ffi::OsString>>,
    );
    impl Observer for Recorded {
        fn completed(&self, command: Arc<OriginalUnitCommand>) -> CargoResult<()> {
            self.0.lock().unwrap().push(Ok(command));
            Ok(())
        }
        fn failed(&self, command: FailedCommand) -> CargoResult<()> {
            assert_eq!(command.unit().index, crate::compiler::UnitIndex(3));
            assert_eq!(
                command.original().get_program(),
                self.1.lock().unwrap().as_ref().unwrap().as_os_str()
            );
            self.0
                .lock()
                .unwrap()
                .push(Err(command.reason().to_owned()));
            Ok(())
        }
    }
    #[test]
    fn original_warm_job_captures_without_running_or_recompiling_and_failed_inputs_stay_failed() {
        // Run the actual JobState completion protocol with held native INPUT
        // and actual Layout guards. No compiler or Host admission is fabricated.
        for (warm, fail, drift, panic) in [
            (true, false, false, false),
            (true, true, false, false),
            (true, false, true, false),
            (false, false, false, false),
            (true, false, false, true),
        ] {
            let root = tempfile::tempdir().unwrap();
            let observer = Arc::new(Recorded::default());
            let (capture, command, source) =
                qualification_command::command_fixture(root.path(), observer.clone());
            *observer.1.lock().unwrap() = Some(command.get_program().to_owned());
            let command_display = command.to_string();
            let messages = Arc::new(Queue::new(100));
            let state = JobState::new(
                JobId(1),
                messages.clone(),
                None,
                false,
                Arc::new(LockManager::new()),
                WarningHandling::Warn,
                warm,
                true,
                None,
            );
            let mut job = Job::new_fresh();
            assert!(matches!(job.freshness(), Freshness::Fresh));
            job.before(Work::new(move |state| {
                state.retain_original_command(capture.clone(), &command)?;
                assert!(!panic, "controlled undelivered input-only worker unwind");
                if drift {
                    std::fs::write(source, "pub fn changed() {}\n")?;
                }
                if fail {
                    anyhow::bail!("original actual unit bookkeeping failed");
                }
                Ok(())
            }));
            let result =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| state.run_to_finish(job)));
            assert_eq!(result.is_err(), panic);
            let mut finished = None;
            let mut observed = 0;
            for message in messages.try_pop_all() {
                match message {
                    Message::Run(_, _) => {
                        panic!("warm capture reported a primary compiler process")
                    }
                    Message::OriginalCommand(command) => {
                        observed += 1;
                        command.notify().unwrap();
                    }
                    Message::Finish(_, Artifact::All, result) => {
                        assert_eq!(
                            observed, 1,
                            "unit removed before original attempted command publication"
                        );
                        finished = Some(result.is_ok());
                    }
                    _ => {}
                }
            }
            assert_eq!(observed, 1);
            let success = warm && !fail && !drift && !panic;
            assert_eq!(finished, Some(success));
            let observations = observer.0.lock().unwrap();
            assert_eq!(observations.len(), 1);
            if success {
                let command = observations[0].as_ref().unwrap();
                assert_eq!(command.unit().index, crate::compiler::UnitIndex(3));
                assert_eq!(command.unit().root_attempt, [1; 16]);
                assert_eq!(command.command_digest().len(), 64);
                assert_eq!(command.original().to_string(), command_display);
                assert_eq!(
                    command.producer_attempt(),
                    None,
                    "warm data invented a cold compiler"
                );
                command.validate().unwrap();
            } else {
                assert!(observations[0].is_err());
            }
        }
    }
}

impl<'a, 'gctx> JobState<'a, 'gctx> {
    pub(super) fn new(
        id: JobId,
        messages: Arc<Queue<Message>>,
        output: Option<&'a DiagDedupe<'gctx>>,
        rmeta_required: bool,
        lock_manager: Arc<LockManager>,
        warning_handling: WarningHandling,
        current_warm: bool,
        record_workload_output: bool,
        #[cfg(any(target_os = "linux", target_os = "macos"))] resources: Option<
            Arc<crate::compiler::resource_runtime::RootContext>,
        >,
    ) -> Self {
        Self {
            id,
            messages,
            output,
            rmeta_required: Cell::new(rmeta_required),
            lock_manager,
            warning_handling,
            current_warm: Cell::new(current_warm),
            record_workload_output,
            original_command: RefCell::new(None),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            resources,
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            bootstrap_execution: None,
            _marker: marker::PhantomData,
        }
    }

    pub(in crate::compiler) fn configure_resources(
        &self,
        command: &mut ProcessBuilder,
        compiler: bool,
    ) -> CargoResult<()> {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if let Some(executor) = &self.bootstrap_execution {
            anyhow::ensure!(
                self.resources.is_none(),
                "Full queue cannot borrow a cooperative member"
            );
            command.process_executor(executor.clone());
            return Ok(());
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(resources) = &self.resources {
            resources.configure(command, compiler)?;
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        let _ = (command, compiler);
        Ok(())
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(super) fn with_bootstrap_permit(
        mut self,
        permit: Option<crate::context::bootstrap_full::QueuePermit>,
    ) -> Self {
        self.bootstrap_execution = permit.map(crate::context::bootstrap_full::QueuedExecutor::new);
        self
    }

    pub fn running(&self, cmd: &ProcessBuilder) {
        self.messages.push(Message::Run(self.id, cmd.to_string()));
    }

    pub(in crate::compiler) fn retain_original_command(
        &self,
        capture: Arc<crate::compiler::qualification_command::Capture>,
        command: &ProcessBuilder,
    ) -> CargoResult<()> {
        let mut original = self.original_command.borrow_mut();
        anyhow::ensure!(original.is_none(), "original unit command captured twice");
        *original = Some((capture.clone(), capture.pending(command)?));
        Ok(())
    }

    /// Trust: return input-capture diagnostics without sharing the logger or
    /// using bounded output queues that can block a main-thread job.
    pub(in crate::compiler) fn input_work(&self, message: LogMessage) {
        self.messages.push(Message::InputWork(message));
    }

    pub fn stdout(&self, stdout: String) -> CargoResult<()> {
        if let Some(dedupe) = self.output {
            writeln!(dedupe.gctx.shell().out(), "{}", stdout)?;
        } else {
            self.messages.push_bounded(Message::Stdout(stdout));
        }
        Ok(())
    }

    pub fn stderr(&self, stderr: String) -> CargoResult<()> {
        if let Some(dedupe) = self.output {
            let mut shell = dedupe.gctx.shell();
            shell.print_ansi_stderr(stderr.as_bytes())?;
            shell.err().write_all(b"\n")?;
        } else {
            self.messages.push_bounded(Message::Stderr(stderr));
        }
        Ok(())
    }

    /// See [`Message::Diagnostic`] and [`Message::WarningCount`].
    pub fn emit_diag(
        &self,
        level: &str,
        diag: String,
        lint: bool,
        fixable: bool,
    ) -> CargoResult<()> {
        if level == "warning" && lint && self.warning_handling == WarningHandling::Allow {
            tracing::warn!("{diag}");
        } else if let Some(dedupe) = self.output {
            let emitted = dedupe.emit_diag(&diag)?;
            if level == "warning" {
                self.messages.push(Message::WarningCount {
                    id: self.id,
                    lint,
                    emitted,
                    fixable,
                });
            }
        } else {
            self.messages.push_bounded(Message::Diagnostic {
                id: self.id,
                level: level.to_string(),
                diag,
                lint,
                fixable,
            });
        }
        Ok(())
    }

    /// Trust: JSON diagnostics are emitted without the rendered-diagnostic
    /// channel, but must still reach the coordinator's warning policy.
    pub fn count_json_warning(&self, lint: bool, fixable: bool) {
        self.messages.push(Message::WarningCount {
            id: self.id,
            lint,
            emitted: true,
            fixable,
        });
    }

    /// See [`Message::Warning`].
    pub fn warning(&self, warning: String) {
        self.messages.push_bounded(Message::Warning {
            id: self.id,
            warning,
        });
    }

    /// A method used to signal to the coordinator thread that the rmeta file
    /// for an rlib has been produced. This is only called for some rmeta
    /// builds when required, and can be called at any time before a job ends.
    /// This should only be called once because a metadata file can only be
    /// produced once!
    pub fn rmeta_produced(&self) {
        self.rmeta_required.set(false);
        self.messages
            .push(Message::Finish(self.id, Artifact::Metadata, Ok(())));
    }

    pub fn lock_exclusive(&self, lock: &LockKey) -> CargoResult<()> {
        self.lock_manager.lock(lock)
    }

    /// The coordinator owns BuildRunner and its non-Send configuration. Ask
    /// it to repeat the ordinary freshness check while we hold the unit lock.
    /// Trust (DC-24a): a miss of a shared unit carries its key where the build
    /// names a unit source. `staged` asks for the check of a unit a source
    /// staged and the worker placed (`fingerprint::recheck_after_lock`).
    pub(crate) fn recheck_freshness(
        &self,
        force: bool,
        staged: bool,
    ) -> CargoResult<crate::compiler::unit_source::Recheck> {
        let (reply, result) = std::sync::mpsc::channel();
        self.messages.push(Message::RecheckFreshness {
            id: self.id,
            force,
            staged,
            reply,
        });
        let recheck = result
            .recv()
            .map_err(|_| anyhow::anyhow!("build coordinator closed the freshness reply"))??;
        self.current_warm.set(recheck.fresh);
        Ok(recheck)
    }

    pub fn downgrade_to_shared(&self, lock: &LockKey) -> CargoResult<()> {
        self.lock_manager.downgrade_to_shared(lock)
    }

    pub fn on_section_timing_emitted(&self, section: SectionTiming) {
        self.messages.push(Message::SectionTiming(self.id, section));
    }

    /// Reports the peak resident set size (in bytes) of this unit's process,
    /// for the `--timings` report.
    pub fn peak_memory(&self, bytes: u64) {
        self.messages.push(Message::PeakMemory(self.id, bytes));
    }

    /// Retain CPU from the same owning wait, including failed compiler executions.
    pub fn cpu_times(&self, times: cargo_util::CpuTimes) {
        self.messages.push(Message::CpuTimes(self.id, times));
    }

    /// Drives a [`Job`] to finish. This ensures that a [`Message::Finish`] is
    /// sent even if our job panics.
    pub(super) fn run_to_finish(self, job: Job) {
        let mut sender = FinishOnDrop {
            messages: &self.messages,
            id: self.id,
            result: None,
        };
        // Declared AFTER FinishOnDrop: retain attempted command data before
        // the queue can remove this unit, including ordinary worker unwinding.
        // Actual delivered WorkGuard Unknown still follows its existing abort.
        struct OriginalOnDrop<'a> {
            original: &'a RefCell<
                Option<(
                    Arc<crate::compiler::qualification_command::Capture>,
                    crate::compiler::qualification_command::PendingCommand,
                )>,
            >,
            messages: &'a Queue<Message>,
        }
        impl Drop for OriginalOnDrop<'_> {
            fn drop(&mut self) {
                if let Ok(mut original) = self.original.try_borrow_mut()
                    && let Some((capture, pending)) = original.take()
                {
                    self.messages.push(Message::OriginalCommand(
                        crate::compiler::qualification_command::Observation::incomplete(
                            capture, pending,
                        ),
                    ));
                }
            }
        }
        let _original = OriginalOnDrop {
            original: &self.original_command,
            messages: &self.messages,
        };
        sender.result = Some(job.run(&self));
        let mut materialization = None;
        if self.record_workload_output && sender.result.as_ref().is_some_and(Result::is_ok) {
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            let compiler = self
                .resources
                .as_ref()
                .map(|owner| owner.completed_workload_compiler())
                .transpose()
                .map(Option::flatten);
            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
            let compiler: CargoResult<Option<[u8; 16]>> = Ok(None);
            match compiler.and_then(|compiler| {
                crate::ops::cargo_test::workload::Materialization::completed(
                    self.current_warm.get(),
                    compiler,
                )
            }) {
                Ok(observed) => {
                    materialization = Some(observed);
                    self.messages
                        .push(Message::WorkloadMaterialized(self.id, observed));
                }
                Err(error) => sender.result = Some(Err(error)),
            }
        }

        if let Some((capture, pending)) = self.original_command.borrow_mut().take() {
            let outcome = match sender.result.as_ref().expect("original unit outcome") {
                Ok(()) => materialization.ok_or_else(|| {
                    "successful original command has no native warm/cold materialization".to_owned()
                }),
                Err(error) => Err(format!("original unit failed: {error:#}")),
            };
            let observed = crate::compiler::qualification_command::Observation::finish(
                capture, pending, outcome,
            );
            if sender.result.as_ref().is_some_and(Result::is_ok)
                && let Some(reason) = observed.failure_reason()
            {
                sender.result = Some(Err(anyhow::anyhow!(reason.to_owned())));
            }
            self.messages.push(Message::OriginalCommand(observed));
        }

        // If the `rmeta_required` wasn't consumed but it was set
        // previously, then we either have:
        //
        // 1. The `job` didn't do anything because it was "fresh".
        // 2. The `job` returned an error and didn't reach the point where
        //    it called `rmeta_produced`.
        // 3. We forgot to call `rmeta_produced` and there's a bug in Cargo.
        //
        // Ruling out the third, the other two are pretty common for 2
        // we'll just naturally abort the compilation operation but for 1
        // we need to make sure that the metadata is flagged as produced so
        // send a synthetic message here.
        if self.rmeta_required.get() && sender.result.as_ref().unwrap().is_ok() {
            self.messages
                .push(Message::Finish(self.id, Artifact::Metadata, Ok(())));
        }

        // Use a helper struct with a `Drop` implementation to guarantee
        // that a `Finish` message is sent even if our job panics. We
        // shouldn't panic unless there's a bug in Cargo, so we just need
        // to make sure nothing hangs by accident.
        struct FinishOnDrop<'a> {
            messages: &'a Queue<Message>,
            id: JobId,
            result: Option<CargoResult<()>>,
        }

        impl Drop for FinishOnDrop<'_> {
            fn drop(&mut self) {
                let result = self
                    .result
                    .take()
                    .unwrap_or_else(|| Err(anyhow::format_err!("worker panicked")));
                self.messages
                    .push(Message::Finish(self.id, Artifact::All, result));
            }
        }
    }

    pub fn future_incompat_report(&self, report: Vec<FutureBreakageItem>) {
        self.messages
            .push(Message::FutureIncompatReport(self.id, report));
    }

    /// The rustc emitted the list of unused `--extern` args.
    ///
    /// This is useful for checking unused dependencies.
    /// Should only be called once, as the compiler only emits it once per compilation.
    pub fn unused_externs(&self, unused_externs: std::collections::BTreeSet<InternedString>) {
        self.messages
            .push(Message::UnusedExterns(self.id, unused_externs));
    }
}
