//! Real verification dependents in the existing admitted native queue. The
//! actions never complete or time the selected compile UnitIndex a second time.
use super::*;
use crate::compiler::qualification::{self, Action, Completion, Options, VerificationIndex};
use crate::compiler::qualification_command::{OriginalUnitCommand, UnitIdentity};
use crate::ops::cargo_test::workload::CapturedAction;
use cargo_util::{CapturedProcess, ExecStats, StreamingProcessScope};
use std::collections::BTreeSet;

pub(super) struct State {
    pub options: Arc<Options>,
    pub active: BTreeSet<VerificationIndex>,
    pub stopped: bool,
    remaining: BTreeSet<VerificationIndex>,
    expected: UnitIdentity,
    pub(super) signals: Arc<StreamingProcessScope>,
    run: qualification::Run,
}
impl State {
    pub(super) fn compiler_retired(
        &mut self,
        compilation: &crate::compiler::Compilation<'_>,
        succeeded: bool,
    ) -> CargoResult<()> {
        if let Err(error) = test_action::observe_report(|| {
            self.options
                .observer
                .compiler_retired(compilation, succeeded)
        }) {
            self.run
                .fatal_failure
                .get_or_insert_with(|| format!("{error:#}"));
            self.run
                .reporting_failure
                .get_or_insert_with(|| format!("{error:#}"));
            self.stopped = true;
            self.signals.cancel();
            return Err(error);
        }
        Ok(())
    }
    fn action(&self, index: VerificationIndex) -> CargoResult<Action> {
        Action::ALL
            .into_iter()
            .find(|action| action.index == index)
            .context("unknown verification node")
    }
    fn command(
        &self,
        action: Action,
    ) -> CargoResult<(cargo_util::ProcessBuilder, Arc<OriginalUnitCommand>)> {
        let original = self.options.original()?;
        anyhow::ensure!(
            original.unit() == &self.expected,
            "verification node received another original compile unit"
        );
        Ok((self.options.command(action)?, original))
    }
}
impl JobQueue<'_> {
    pub(super) fn enqueue_verifications(
        &mut self,
        build: &BuildRunner<'_, '_>,
        options: Arc<Options>,
    ) -> CargoResult<State> {
        options.validate_workspace(build)?;
        let unit = build
            .bcx
            .roots
            .iter()
            .find(|unit| options.selects(unit))
            .context("missing selected AY root")?;
        let expected = crate::compiler::qualification_command::unit_identity(build, unit)?;
        let mut previous = None;
        for action in Action::ALL {
            // All current compilation prerequisites close before verification.
            // A failed prerequisite blocks an explicitly retained node; no
            // absent function/obligation population becomes an empty success.
            let mut deps = self
                .queued_units
                .iter()
                .cloned()
                .map(|unit| (QueueNode::Compile(unit), Artifact::All))
                .collect::<Vec<_>>();
            if let Some(previous) = previous {
                deps.push((QueueNode::Verification(previous), Artifact::All));
            }
            test_action::observe_report(|| options.observer.registered(action, &expected))?;
            self.queue.queue(
                QueueNode::Verification(action.index),
                QueueWork::Verification(action),
                deps,
                100,
            );
            previous = Some(action.index);
        }
        let outputs = build.workload_output_leases()?;
        Ok(State {
            options,
            active: BTreeSet::new(),
            stopped: false,
            remaining: Action::ALL.into_iter().map(|a| a.index).collect(),
            expected,
            signals: Arc::new(StreamingProcessScope::new()?),
            run: qualification::Run {
                outputs: Some(outputs),
                ..qualification::Run::default()
            },
        })
    }
}
impl DrainState<'_> {
    pub(super) fn workload_inputs(&self) -> Option<Arc<crate::ops::cargo_test::workload::Inputs>> {
        self.tests
            .as_ref()
            .and_then(|tests| tests.options.workload.as_ref())
            .map(|workload| workload.inputs.clone())
            .or_else(|| {
                self.verification
                    .as_ref()
                    .map(|state| state.options.inputs.clone())
            })
            .or_else(||self.native_inputs.clone())
    }
    pub(super) fn verification_active(&self) -> usize {
        self.verification
            .as_ref()
            .map_or(0, |state| state.active.len())
    }
    pub(super) fn verification_signals(&self) -> Option<Arc<StreamingProcessScope>> {
        self.verification
            .as_ref()
            .map(|state| state.signals.clone())
    }
    pub(super) fn run_verification<'s>(
        &mut self,
        action: Action,
        _build: &BuildRunner<'_, '_>,
        scope: &'s Scope<'s, '_>,
        workers: &mut Vec<thread::ScopedJoinHandle<'s, ()>>,
        token: Option<Acquired>,
        resources: Option<Arc<crate::compiler::resource_runtime::RootContext>>,
    ) -> CargoResult<()> {
        anyhow::ensure!(
            self.active.is_empty() && self.verification_active() == 0 && self.compiler_finalized,
            "verification requires closed compilation and its own current node"
        );
        // A Finish message precedes some final drops. Join the original current
        // workers before borrowing inputs or dispatching the next policy.
        anyhow::ensure!(
            workload_script::join_current_workers(workers) == 0,
            "original worker panicked before verifier admission"
        );
        let state = self
            .verification
            .as_mut()
            .context("missing verification population")?;
        anyhow::ensure!(
            state.remaining.contains(&action.index) && !state.active.contains(&action.index),
            "verification node dispatched twice"
        );
        let (mut command, original) = state.command(action)?;
        let resources =
            resources.context("verification has no actual original compiler admission")?;
        resources.configure(&mut command, true)?;
        test_action::observe_report(|| state.options.observer.scheduled(action))?;
        anyhow::ensure!(
            state.active.insert(action.index),
            "verification node became active twice"
        );
        let signals = state.signals.clone();
        let inputs = state.options.inputs.clone();
        let timeout = Duration::from_nanos(state.options.invocation.consumer.timeout_ns);
        let messages = self.messages.clone();
        let started = Instant::now();
        workers.push(scope.spawn(move || {
            let _local_token = token;
            let _resources = resources;
            struct Finished {
                messages: Arc<Queue<Message>>,
                completion: Option<Completion>,
                action: Action,
                started: Instant,
            }
            impl Drop for Finished {
                fn drop(&mut self) {
                    let completion = self.completion.take().unwrap_or_else(|| Completion {
                        action: self.action,
                        elapsed: self.started.elapsed(),
                        capture: CapturedAction {
                            capture: CapturedProcess {
                                failure: Some(anyhow::anyhow!(
                                    "verification worker ended without an owned terminal"
                                )),
                                ..CapturedProcess::default()
                            },
                            stats: ExecStats::default(),
                        },
                        input_failure: Some("worker outcome/input revalidation unknown".into()),
                    });
                    self.messages
                        .push(Message::VerificationFinished(completion));
                }
            }
            let mut finished = Finished {
                messages,
                completion: None,
                action,
                started,
            };
            let capture = qualification::execute(&command, &signals, timeout);
            let input_failure = match (original.validate(), inputs.validate()) {
                (Ok(()), Ok(())) => None,
                (Err(error), Ok(())) | (Ok(()), Err(error)) => Some(format!("{error:#}")),
                (Err(error), Err(second)) => Some(format!(
                    "{error:#}; original inputs also changed: {second:#}"
                )),
            };
            drop(command);
            finished.completion = Some(Completion {
                action,
                capture,
                elapsed: started.elapsed(),
                input_failure,
            });
        }));
        Ok(())
    }
    pub(super) fn finish_verification(&mut self, completion: Completion) -> CargoResult<()> {
        let state = self
            .verification
            .as_mut()
            .context("verification terminal without population")?;
        let action = state.action(completion.action.index)?;
        anyhow::ensure!(
            action == completion.action
                && state.active.remove(&action.index)
                && state.remaining.remove(&action.index),
            "verification terminal is missing, duplicate or misbound"
        );
        let complete = completion.complete_observation();
        if let Some(failure) = &completion.input_failure {
            state
                .run
                .fatal_failure
                .get_or_insert_with(|| failure.clone());
        }
        // Retain the actual outcome/raw bytes BEFORE any report observer fails.
        state.run.completed.push(completion);
        if let Err(error) = test_action::observe_report(|| {
            state
                .options
                .observer
                .completed(state.run.completed.last().expect("just retained"))
        }) {
            state.stopped = true;
            state
                .run
                .reporting_failure
                .get_or_insert_with(|| format!("{error:#}"));
            state
                .run
                .fatal_failure
                .get_or_insert_with(|| format!("{error:#}"));
            state.signals.cancel();
            return Err(error);
        }
        if complete {
            // Complete independent nonzero observations may release strict and
            // later consumer coverage. They do not become compile successes.
            self.queue
                .finish(&QueueNode::Verification(action.index), &Artifact::All);
        } else {
            state.stopped = true;
            state.signals.cancel();
            state
                .run
                .reporting_failure
                .get_or_insert("verification lacked complete original terminal/input facts".into());
        }
        Ok(())
    }
    pub(super) fn finish_verification_graph(&mut self, build: &mut BuildRunner<'_, '_>) {
        let Some(mut state) = self.verification.take() else {
            return;
        };
        for index in std::mem::take(&mut state.remaining) {
            let action = state.action(index).expect("original declared action");
            let reason =
                "original prerequisite/admission/verification observation did not complete";
            if let Err(error) =
                test_action::observe_report(|| state.options.observer.blocked(action, reason))
            {
                state
                    .run
                    .reporting_failure
                    .get_or_insert_with(|| format!("{error:#}"));
                state
                    .run
                    .fatal_failure
                    .get_or_insert_with(|| format!("{error:#}"));
            }
            state.run.blocked.push((action, reason.into()));
        }
        match state.options.original() {
            Ok(original) => state.run.original = Some(original),
            Err(error) => state.run.original_failure = Some(format!("{error:#}")),
        }
        match state.options.failed_original() {
            Ok(failed) => state.run.failed_original = failed,
            Err(error) => {
                state
                    .run
                    .reporting_failure
                    .get_or_insert_with(|| format!("{error:#}"));
                state
                    .run
                    .fatal_failure
                    .get_or_insert_with(|| format!("{error:#}"));
            }
        }
        build.compilation.qualification = Some(state.run);
    }
}
