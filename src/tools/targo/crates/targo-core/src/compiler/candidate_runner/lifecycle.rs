//! Parent-owned prepared/GO/relay/retirement loop. Public reports and exit-zero
//! projections cannot construct its actual member, original loan or artifact.
use super::*;
use crate::resource_v3::workload::bank::{PrimaryLoan, broker::RegisteredArtifact};
use trust_resource_controller::client::{
    ContainedProducedMember, ProducedFailureObservation, ProducedResult,
    SuccessfulProducedCompletion,
};
use trust_resource_controller::{Status, StatusFrame};

/// Actual observed native outcome. This is not independent behavior/proof
/// validation, producer eligibility or permission to land a candidate.
pub(crate) enum NativeOutcome {
    Finished {
        // Retain the SAME actual native outcome owner through comparison.
        _result: Box<ProducedResult>,
    },
    Refused {
        _frame: StatusFrame,
        _observation: Option<Box<ProducedFailureObservation>>,
    },
}

/// Keep original member/captures and all input owners through comparison,
/// including known failed and refused attempts. There is no DATA constructor.
pub(crate) struct Attempt {
    // These retain the complete known outcome, including failed/refused custody.
    pub(crate) _outcome: NativeOutcome,
    pub(crate) _failures: Vec<String>,
    pub(crate) relay: CompilerRelay,
    _original: Original,
}

struct Original {
    member: ContainedProducedMember,
    request_plan: Plan,
    artifact: Arc<RegisteredArtifact>,
    primary: Arc<PrimaryLoan>,
    settled: bool,
    success: Option<SuccessfulProducedCompletion>,
}
impl Attempt {
    fn require_successful_retirement(&self) -> CargoResult<()> {
        ensure!(
            self._original.settled,
            "produced coordinator has not retired"
        );
        let success = self
            ._original
            .success
            .as_ref()
            .context("produced coordinator has no validated native success owner")?;
        ensure!(
            success.matches_registration(self._original.artifact.registered()),
            "native success belongs to another original produced coordinator"
        );
        self.relay.require_dependencies()
    }
    pub(crate) fn require_frontend(
        &self,
        original: &Arc<crate::ops::cargo_test::workload::NativeOutput>,
    ) -> CargoResult<()> {
        self.require_successful_retirement()?;
        ensure!(
            std::ptr::eq(self._original.artifact.original(), original.as_ref()),
            "coordinator did not execute the requested original produced frontend"
        );
        Ok(())
    }
    /// SAME original request, independently selected plan and private native
    /// retirement owner. Equality is DATA, never a substitute for retirement.
    pub(crate) fn require_plan(&self, plan: &Plan) -> CargoResult<()> {
        self.require_successful_retirement()?;
        ensure!(
            self._original.request_plan == *plan,
            "retired coordinator executed another selected plan"
        );
        Ok(())
    }
    pub(in crate::compiler) fn require_retired_originals(
        &self,
        primary: &Arc<PrimaryLoan>,
        artifact: &Arc<RegisteredArtifact>,
    ) -> CargoResult<()> {
        ensure!(
            self._original.settled
                && Arc::ptr_eq(primary, &self._original.primary)
                && Arc::ptr_eq(artifact, &self._original.artifact),
            "coordinator phase cannot leave before SAME native member retirement"
        );
        Ok(())
    }
    pub(crate) fn published_programs(&self) -> CargoResult<&[Arc<PublishedProgram>]> {
        self.require_successful_retirement()?;
        self.relay.published_programs()
    }
}
impl Drop for Original {
    fn drop(&mut self) {
        // A caught callback panic cannot free the offered original while the
        // native target or helper might still execute. No Drop invents return.
        if !self.settled {
            crate::resource_v3::workload::abort_unknown();
        }
    }
}
impl Original {
    fn retire(&mut self, frame: &StatusFrame) {
        if frame.member_attempt != self.primary.coordinator_attempt().unwrap_or([0; 16])
            || frame.root_attempt != self.artifact.registered().registration().key.root_attempt
            || !matches!(
                frame.status,
                Status::Finished { .. } | Status::Refused { .. }
            )
            || self.primary.retired().is_err()
        {
            crate::resource_v3::workload::abort_unknown();
        }
        if matches!(frame.status, Status::Finished { .. })
            && self
                .primary
                .record_coordinator_terminal(&frame.status)
                .is_err()
        {
            crate::resource_v3::workload::abort_unknown();
        }
        self.settled = true;
    }
}

fn note(failures: &mut Vec<String>, error: impl std::fmt::Display) {
    // Each transition is recorded once, not on every polling iteration.
    if failures.len() < 64 {
        failures.push(bounded_reason(&error.to_string()));
    }
}

fn refused(
    mut original: Original,
    mut relay: CompilerRelay,
    mut failures: Vec<String>,
    error: String,
    frame: StatusFrame,
) -> Attempt {
    if let Err(error) = relay.stop() {
        note(&mut failures, error);
    }
    let observation = original.member.take_failure_observation().map(Box::new);
    original.retire(&frame);
    note(&mut failures, error);
    if let Some(observation) = &observation {
        if let Some(sink) = &relay.inputs.startup.workload_evidence {
            if let Err(error) = sink.publish_produced_failure(observation) {
                note(&mut failures, error);
            }
        }
    }
    Attempt {
        _outcome: NativeOutcome::Refused {
            _frame: frame,
            _observation: observation,
        },
        _failures: failures,
        relay,
        _original: original,
    }
}

/// Drive an ALREADY admitted actual member. The caller owns admission and
/// begins the actual coordinator primary before offering it to the Host.
/// Preparation uses the existing resolver and the SAME original GNU owner;
/// the resulting semantic binding itself remains DATA only.
/// The native Host continues to require its own source/output/SDK confinement.
pub(crate) fn run(
    member: ContainedProducedMember,
    mut relay: CompilerRelay,
    primary: Arc<PrimaryLoan>,
    artifact: Arc<RegisteredArtifact>,
    jobserver: cargo_util::Jobserver,
) -> Attempt {
    // Capture equality DATA from the SAME admitted member before compaction
    // closes its transfer descriptions and removes the live request view.
    let request_plan = match member.coordinator_request() {
        Ok(request) => request.plan.clone(),
        Err(_) => crate::resource_v3::workload::abort_unknown(),
    };
    let mut original = Original {
        member,
        request_plan,
        artifact,
        primary,
        settled: false,
        success: None,
    };
    let root = relay.inputs.startup.query.binding.root_attempt;
    let request = match original.member.coordinator_request() {
        Ok(request) => request,
        Err(_) => crate::resource_v3::workload::abort_unknown(),
    };
    let registered = original.artifact.registered().registration();
    if relay
        .factory
        .require_coordinator(
            &relay.inputs.startup,
            &original.primary,
            request.contained.produced.member.member_attempt,
        )
        .is_err()
    {
        crate::resource_v3::workload::abort_unknown();
    }
    if request.contained.produced.key != registered.key
        || request.contained.produced.member.binding.root_attempt != root
        || Some(request.contained.produced.member.member_attempt)
            != original.primary.coordinator_attempt()
        || request.plan != relay.inputs.plan
        || request.contained.gnu != original.artifact.phase().gnu
        || relay
            .inputs
            .startup
            .workload_bank
            .as_ref()
            .is_none_or(|bank| !original.primary.belongs_to(bank))
    {
        crate::resource_v3::workload::abort_unknown();
    }
    let deadline = relay.inputs.deadline;
    let mut failures = Vec::new();
    let mut bound = false;
    let mut stopping = false;
    let mut cancel_sent = false;
    let mut refusing: Option<String> = None;
    loop {
        if Instant::now() >= deadline {
            relay.cancel();
            let _ = original
                .member
                .cancel(Instant::now() + Duration::from_millis(100));
            // The original absolute deadline never becomes a new grace grant
            // or a claim that the native target stopped. Keep Unknown strict.
            crate::resource_v3::workload::abort_unknown();
        }
        let until = deadline.min(Instant::now() + Duration::from_millis(100));
        if let Some(error) = &refusing {
            // Known no-start event/output closure is distinct from actual
            // control EOF. Wait on the same connection; do not replay poll
            // after its one-use refused result or send another cancellation.
            match original.member.coordinator_refusal(until) {
                Ok(Some(frame)) => {
                    let frame = frame.clone();
                    let error = error.clone();
                    return refused(original, relay, failures, error, frame);
                }
                Ok(None) => {
                    std::thread::sleep(Duration::from_millis(1));
                    continue;
                }
                Err(_) => crate::resource_v3::workload::abort_unknown(),
            }
        }
        if !stopping {
            let check = relay
                .inputs
                .validate()
                .and_then(|()| original.artifact.validate(deadline));
            if let Err(error) = check {
                note(&mut failures, error);
                stopping = true;
            }
        }
        if stopping && !cancel_sent {
            relay.cancel();
            // One cancellation delivery only; it cannot be replayed on an
            // ambiguous send. Continue polling the SAME native member below.
            cancel_sent = true;
            if original.member.cancel(until).is_err() {
                crate::resource_v3::workload::abort_unknown();
            }
        }
        match original.member.poll(until) {
            Ok(Some(mut operation)) => {
                if !relay.is_idle() {
                    note(
                        &mut failures,
                        "coordinator completed while its compiler worker was active",
                    );
                }
                if let Err(error) = relay.stop() {
                    note(&mut failures, error);
                }
                if !operation.matches_registration(original.artifact.registered()) {
                    crate::resource_v3::workload::abort_unknown();
                }
                // Issue from the private native observation BEFORE exposing
                // mutable reporting DATA. Failed exits and truncated captures
                // never create this owner.
                let success = operation.successful_completion().ok();
                let result = match operation.take_observation() {
                    Some(result) => result,
                    None => crate::resource_v3::workload::abort_unknown(),
                };
                let frame = result.completion.completed.finished.clone();
                if matches!(
                    frame.status,
                    Status::Finished {
                        outcome: trust_resource_controller::Outcome::Exit(0),
                        cause: trust_resource_controller::CompletionCause::Exited,
                        ..
                    }
                ) {
                    // Includes a fully Fresh epoch: every current row still
                    // needs its SAME genuine retired producer/file closure.
                    if let Err(error) = relay.require_dependencies() {
                        note(&mut failures, error);
                    }
                }
                // Actual native completion and physical EOF precede local
                // loan retirement. Failed input bookends do not undo CPU
                // retirement and cannot convert this result into success.
                original.retire(&frame);
                if let Err(error) = original.artifact.retain_completed(operation) {
                    note(&mut failures, error);
                }
                if let Err(error) = relay.inputs.validate() {
                    note(&mut failures, error);
                }
                if let Err(error) = original.artifact.validate(deadline) {
                    note(&mut failures, error);
                }
                // Only this private branch installs the actual success owner
                // after native retirement and all original input bookends.
                // Editing public outcome/failure DATA cannot mint it later.
                if failures.is_empty() {
                    original.success = success;
                }
                return Attempt {
                    _outcome: NativeOutcome::Finished {
                        _result: Box::new(result),
                    },
                    _failures: failures,
                    relay,
                    _original: original,
                };
            }
            Ok(None) => {}
            Err(error) => {
                match original.member.workload_refusal(until) {
                    Ok(Some(_)) => {
                        refusing = Some(bounded_reason(&error.to_string()));
                        if let Err(error) = relay.stop() {
                            note(&mut failures, error);
                        }
                        continue;
                    }
                    Ok(None) | Err(_) => {
                        // Preserve any native raw prefix before the original
                        // Unknown abort; neither an error nor EOF is a loan.
                        if let Some(observation) = original.member.take_failure_observation() {
                            if let Some(sink) = &relay.inputs.startup.workload_evidence {
                                let _ = sink.publish_produced_failure(&observation);
                            }
                        }
                        relay.cancel();
                        crate::resource_v3::workload::abort_unknown();
                    }
                }
            }
        }
        if !stopping && !bound {
            match original.member.coordinator_prepared(until) {
                Ok(Some(_)) => {
                    match relay
                        .server
                        .bind_publication_member(&mut original.member, until)
                    {
                        Ok(Some(())) => {}
                        Ok(None) => continue,
                        Err(error) => {
                            note(&mut failures, error);
                            stopping = true;
                            continue;
                        }
                    }
                    let selection =
                        relay.prepare(&mut original.member, original.artifact.clone(), &jobserver);
                    let binding = selection.and_then(|selection| {
                        relay.inputs.validate()?;
                        relay.inputs.require_commands(&mut original.member)?;
                        original.artifact.validate(deadline)?;
                        original.member.bind_coordinator(&selection, deadline)?;
                        Ok(())
                    });
                    match binding {
                        Ok(()) => bound = true,
                        Err(error) => {
                            note(&mut failures, error);
                            stopping = true;
                        }
                    }
                }
                Ok(None) => {}
                Err(error) => {
                    note(&mut failures, error);
                    stopping = true;
                }
            }
        }
        if bound && !stopping {
            if let Err(error) = relay.poll() {
                note(&mut failures, error);
                stopping = true;
            }
        }
        std::thread::sleep(Duration::from_millis(1));
    }
}
