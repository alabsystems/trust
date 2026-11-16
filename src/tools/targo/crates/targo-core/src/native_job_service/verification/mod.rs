//! An actual native Verify node, continuing the original compile graph.
//!
//! Captured rows and stored hints are DATA. Favorable current proof credit
//! additionally requires this node's native compiler/session/input owners and
//! the nonClone proof values returned by the maintained kernel in this call.
use super::context::{NodeContext, RootPreparation};
use crate::compiler::{
    build_runner::OriginalOutputLeases,
    native_job::{
        NativeLocalPreparation, NativeOperationGraph, NativeRetainedGraph,
        NativeVerificationContext,
    },
    qualification_command::{NativePolicy, OriginalUnitCommand},
};
use crate::ops::cargo_test::workload::Inputs;
use crate::resource_v3::{NativeVerificationCapture, Startup};
use crate::util::CargoResult;
use anyhow::{Context as _, ensure};
use cargo_util::{ProcessBuilder, StreamingOutputLimits};
use std::sync::{Arc, atomic::Ordering};
use std::time::{Duration, Instant};
use trust_proof_session::{MetadataDirectory, VerificationSession};
use trust_resource_controller::{
    descriptors::OriginalInputPermit,
    native_job::{Artifact as DeclaredArtifact, Kind, NodeId, ProofPolicy},
};

mod census;
mod kernel;

/// A NEW actual local reservation after positive native verifier retirement.
/// It does not revive the compiler's retired lease or create another bank.
struct KernelPreparation {
    original: NativeLocalPreparation,
    startup: Arc<Startup>,
    deadline: Instant,
}
impl KernelPreparation {
    fn require_current(&self) -> CargoResult<()> {
        self.original.require(&self.startup)?;
        require_live(&self.startup, self.deadline)
    }
}

struct PolicySession {
    session: VerificationSession,
    metadata: MetadataDirectory,
    startup: Arc<Startup>,
    inputs: Arc<Inputs>,
    outputs: Arc<OriginalOutputLeases>,
    command: Arc<OriginalUnitCommand>,
    policy: ProofPolicy,
    deadline: Instant,
    // All actual originals above close FIRST, this SAME capacity LAST.
    _descriptors: OriginalInputPermit,
}
#[derive(Clone, Copy)]
enum InputPhase {
    Execution,
    Retained,
}
impl PolicySession {
    fn create(
        context: &NativeVerificationContext,
        node: &NodeContext<'_>,
        artifact: &crate::compiler::native_job::Artifact,
        policy: ProofPolicy,
        deadline: Instant,
    ) -> CargoResult<Self> {
        // Preparation is actual read-only SAME loan/lease/Startup validation,
        // BEFORE hint-store/hash/create/open/duplicate I/O of any kind.
        let startup = context.preparation()?;
        ensure!(
            Arc::ptr_eq(&startup, node.startup()),
            "verification substituted its original prepared Root"
        );
        require_live(&startup, deadline)?;
        const SESSION_FD_ENVELOPE: usize = 16;
        let descriptors = startup
            .descriptor_budget
            .as_ref()
            .context("verification has no original descriptor budget")?
            .reserve_original_inputs(SESSION_FD_ENVELOPE)?;
        let inputs = artifact.inputs().clone();
        let outputs = artifact.output_leases().clone();
        artifact.validate()?;
        let command = artifact.original_command()?;
        let output = inputs.held_output_root();
        let session = VerificationSession::create_at(output.descriptor(deadline)?, output.path())?
            .with_proof_store(Some(command.cargo_home()));
        let metadata = session.prepare_metadata()?;
        let original = Self {
            session,
            metadata,
            startup,
            inputs,
            outputs,
            command,
            policy,
            deadline,
            _descriptors: descriptors,
        };
        original.require_current()?;
        Ok(original)
    }
    fn require_current(&self) -> CargoResult<()> {
        self.require_inputs(InputPhase::Execution)
    }
    fn require_retained_current(&self) -> CargoResult<()> {
        self.require_inputs(InputPhase::Retained)
    }
    fn require_inputs(&self, phase: InputPhase) -> CargoResult<()> {
        require_live_in(&self.startup, self.deadline, phase)?;
        let plan = self
            .inputs
            .native_plan()
            .context("verification lost its actual native plan")?;
        let actual = crate::resource_v3::native_job::require(plan)?;
        ensure!(
            Arc::ptr_eq(&actual, &self.startup),
            "verification substituted original Root Startup"
        );
        self.inputs.validate()?;
        self.outputs
            .validate(self.inputs.held_output_root().path())?;
        self.command.validate()?;
        self.session.check_current()?;
        self.metadata.check_current()?;
        Ok(())
    }
    fn command(&self) -> CargoResult<ProcessBuilder> {
        self.require_current()?;
        let policy = match self.policy {
            ProofPolicy::Advisory => NativePolicy::Advisory,
            ProofPolicy::Certify => NativePolicy::Certify,
        };
        let command = self
            .command
            .native_policy_command(policy, &self.metadata, &self.session)?;
        self.require_current()?;
        Ok(command)
    }
}

fn require_live(startup: &Startup, deadline: Instant) -> CargoResult<()> {
    require_live_in(startup, deadline, InputPhase::Execution)
}
fn require_live_in(startup: &Startup, deadline: Instant, phase: InputPhase) -> CargoResult<()> {
    let process = startup
        .workload_process
        .as_ref()
        .context("verification lost original native process owner")?;
    require_window(Instant::now(), deadline, process.deadline, phase)?;
    ensure!(
        !process.cancelled.load(Ordering::Acquire) && !process.poisoned.load(Ordering::Acquire),
        "original native verification Root cancelled or poisoned"
    );
    Ok(())
}
/// Time selection DATA only. A retained phase is reachable only from the
/// actual completed native/proof owner under a NEW paid consumer preparation.
/// It cannot resume GO/search, renew the old budget or extend the original Root.
fn require_window(
    now: Instant,
    execution: Instant,
    root: Instant,
    phase: InputPhase,
) -> CargoResult<()> {
    let until = match phase {
        InputPhase::Execution => execution,
        InputPhase::Retained => root,
    };
    ensure!(
        execution <= root && now < until,
        "original native verification/input deadline expired or was extended"
    );
    Ok(())
}

struct State {
    node: NodeId,
    artifact: Option<DeclaredArtifact>,
    operation: Option<NativeOperationGraph>,
    context: Option<NativeVerificationContext>,
    session: Option<PolicySession>,
    capture: Option<NativeVerificationCapture>,
    census: Option<census::Census>,
    checked: Option<kernel::CheckedRows>,
    failures: Vec<anyhow::Error>,
    continuation: Option<NativeRetainedGraph>,
}

/// This actual run retains all known outcomes separately from continuation and
/// favorable proof eligibility. No report/Boolean can construct this owner.
pub(super) struct VerificationAttempt {
    state: Option<Box<State>>,
}
impl VerificationAttempt {
    /// A real parent reporting/control failure vetoes eligibility but never
    /// discards the original native outcome, current proofs or input owners.
    pub(super) fn reporting_failed(&mut self, error: anyhow::Error) {
        self.state
            .as_mut()
            .expect("owned native verification attempt")
            .failures
            .push(error);
    }
    pub(super) fn compiler_executions(&self) -> Option<u64> {
        let state = self.state.as_ref()?;
        let capture = state.capture.as_ref()?;
        if capture.capture().started {
            return Some(1);
        }
        // Only this SAME native owning capture followed by positive graph
        // closure can observe a pre-GO refusal. False Started alone is Unknown.
        (state.context.is_none()
            && state.operation.is_none()
            && capture.native_status().is_some_and(|status| {
                matches!(
                    status.status,
                    trust_resource_controller::Status::Refused { .. }
                )
            }))
        .then_some(0)
    }
    pub(super) fn result(&self) -> CargoResult<()> {
        let state = self
            .state
            .as_ref()
            .expect("owned native verification attempt");
        ensure!(
            state.failures.is_empty(),
            "native Verify node failed: {}",
            state
                .failures
                .iter()
                .map(bounded_reason)
                .collect::<Vec<_>>()
                .join("; ")
        );
        ensure!(
            state.operation.is_none() && state.context.is_none() && state.capture.is_some(),
            "native Verify node has unresolved actual graph/native owners"
        );
        state
            .session
            .as_ref()
            .context("native Verify omitted its actual session")?;
        state
            .census
            .as_ref()
            .context("native Verify omitted its full current census")?;
        state
            .checked
            .as_ref()
            .context("native Verify omitted actual kernel work")?;
        // This is only a projection of the actual completed run. All heavy
        // Certify final gates ran under its real local preparation before
        // suspension; never decode/hash current VCs against a parked bank.
        Ok(())
    }
    pub(super) fn has_retained_continuation(&self) -> bool {
        self.state
            .as_ref()
            .is_some_and(|state| state.continuation.is_some())
    }
    pub(super) fn take_continuation(&mut self) -> Option<NativeRetainedGraph> {
        self.state.as_mut()?.continuation.take()
    }
    pub(super) fn require_current(
        &self,
        context: &NodeContext<'_>,
        artifact: &DeclaredArtifact,
        preparation: &RootPreparation,
    ) -> CargoResult<()> {
        preparation.require(context.startup())?;
        let state = self
            .state
            .as_ref()
            .context("native Verify lost its actual outcome owner")?;
        ensure!(
            state.failures.is_empty() && state.artifact.as_ref() == Some(artifact),
            "native verification does not cover the requested actual producer"
        );
        // CompletedNode owns this result after its continuation moves to the
        // next node. Its real native closure remains in the opaque capture.
        let session = state
            .session
            .as_ref()
            .context("native Verify lost its actual session")?;
        ensure!(
            Arc::ptr_eq(context.startup(), &session.startup),
            "native proof outcome belongs to another Root"
        );
        let actual = context.artifact(artifact)?.original_command()?;
        ensure!(
            Arc::ptr_eq(&actual, &session.command),
            "native proof outcome belongs to another original compiler command"
        );
        ensure!(
            state.context.is_none() && state.operation.is_none() && state.capture.is_some(),
            "native proof outcome has unresolved native owners"
        );
        session.require_retained_current()?;
        state
            .checked
            .as_ref()
            .context("native Verify has no current kernel proof owners")?
            .require_complete(
                state
                    .census
                    .as_ref()
                    .context("native Verify has no whole-unit census")?,
            )?;
        session.require_retained_current()?;
        preparation.require(context.startup())?;
        Ok(())
    }
}
impl Drop for VerificationAttempt {
    fn drop(&mut self) {
        if self
            .state
            .as_ref()
            .is_some_and(|state| state.context.is_some() || state.operation.is_some())
        {
            // Unknown native owners are not a no-launch/ClosedRoot receipt.
            // Keep the whole original, including raw capture and paid FD
            // envelope; dropping an attempt cannot return an uncertain unit.
            if let Some(state) = self.state.take() {
                std::mem::forget(state);
            }
        }
    }
}

pub(super) fn run(
    node: &NodeContext<'_>,
    operation: NativeOperationGraph,
    deadline: Instant,
) -> VerificationAttempt {
    let mut attempt = VerificationAttempt {
        state: Some(Box::new(State {
            node: node.node(),
            artifact: None,
            operation: Some(operation),
            context: None,
            session: None,
            capture: None,
            census: None,
            checked: None,
            failures: vec![],
            continuation: None,
        })),
    };
    // Install whole-owner retention before the first fallible preparation or
    // native call, including an unwind before a result can be returned.
    let state = attempt.state.as_mut().unwrap();
    if let Err(error) = execute(node, state, deadline) {
        state.failures.push(error);
    }
    // Only the actual graph owner's positive suspension returns a continuation.
    // Native Unknown/return errors retain the original context AND operation.
    if state.context.is_none() {
        if let Some(operation) = state.operation.take() {
            match operation.try_suspend() {
                Ok(continuation) => state.continuation = Some(continuation),
                Err((error, operation)) => {
                    state.operation = Some(operation);
                    state
                        .failures
                        .push(error.context("native Verify graph suspension failed"));
                }
            }
        }
    }
    attempt
}

fn bounded_reason(error: &anyhow::Error) -> String {
    let mut reason = format!("{error:#}");
    if reason.len() > 4096 {
        let mut end = 4096;
        while !reason.is_char_boundary(end) {
            end -= 1;
        }
        reason.truncate(end);
        reason.push_str(" [original error retained]");
    }
    reason
}

fn execute(node: &NodeContext<'_>, state: &mut State, deadline: Instant) -> CargoResult<()> {
    let Kind::Verify {
        artifact: declared,
        policy,
    } = &node.plan().nodes[state.node.0 as usize].kind
    else {
        anyhow::bail!("native verification provider received another node kind")
    };
    state.artifact = Some(declared.clone());
    let process = node
        .startup()
        .workload_process
        .as_ref()
        .context("native Verify has no original process budget")?;
    let deadline = deadline.min(process.deadline);
    require_live(node.startup(), deadline)?;
    let artifact = node.artifact(declared)?;
    {
        let operation = state
            .operation
            .as_ref()
            .context("native Verify lost its original graph")?;
        operation.select_artifact(artifact)?;
        state.context = Some(
            operation
                .try_verification()?
                .context("native Verify has no available original bank unit")?,
        );
    }
    let prepared = (|| -> CargoResult<_> {
        state.session = Some(PolicySession::create(
            state.context.as_ref().unwrap(),
            node,
            artifact,
            *policy,
            deadline,
        )?);
        let command = state.session.as_ref().unwrap().command()?;
        let timeout = deadline
            .checked_duration_since(Instant::now())
            .context("native Verify expired before actual compiler dispatch")?;
        let limits =
            StreamingOutputLimits::new(64 * 1024 * 1024, 64 * 1024 * 1024).with_timeout(timeout);
        Ok((command, limits))
    })();
    let (command, limits) = match prepared {
        Ok(prepared) => prepared,
        Err(error) => {
            // No native capture call has occurred on this path. Even here,
            // only the SAME actual positively unbound preparation may close.
            if let Err((failure, original)) = state.context.take().unwrap().cancel_preparation() {
                state.context = Some(original);
                return Err(
                    error.context(format!("unbound native preparation refused: {failure:#}"))
                );
            }
            return Err(error);
        }
    };
    let session = state.session.as_ref().unwrap();
    // Capture internally finalizes SAME native originals/GNU exactly once.
    // Save the actual result before any report/input post-bookend can fail.
    state.capture = Some(state.context.as_ref().unwrap().capture(command, limits)?);
    let capture = state.capture.as_ref().unwrap();
    let mut context = state.context.take().unwrap();
    loop {
        match context.try_retire(capture) {
            Ok(()) => break,
            Err((error, original)) => {
                context = original;
                if Instant::now() < deadline
                    && error
                        .downcast_ref::<std::io::Error>()
                        .is_some_and(|cause| cause.kind() == std::io::ErrorKind::WouldBlock)
                {
                    std::thread::sleep(Duration::from_millis(2));
                    continue;
                }
                state.context = Some(context);
                return Err(error.context("native verifier retirement is unresolved"));
            }
        }
    }
    // Current kernel math and all report/input IO use a fresh real loan from
    // the SAME bank, never the compiler lease just positively retired above.
    let preparation = KernelPreparation {
        original: state
            .operation
            .as_ref()
            .context("native kernel lost its original graph")?
            .prepare_local()?
            .context("native kernel replay has no available actual local unit")?,
        startup: node.startup().clone(),
        deadline,
    };
    preparation.require_current()?;
    session.require_current()?;
    let scope = session.command.scope();
    state.census = Some(census::parse(
        &capture.capture().stderr,
        &census::Scope {
            package: &scope.package_name,
            krate: &scope.crate_name,
            primary: scope.primary_package,
            session: session.session.id(),
        },
    )?);
    state.checked = Some(kernel::check(
        state.census.as_ref().unwrap(),
        &session.session,
        &preparation,
        deadline,
    )?);
    preparation.require_current()?;
    // Publish mathematical hint bytes only, under this actual local unit.
    // Unknown/failed rows still cannot satisfy any current-proof consumer.
    session.session.publish_proof_hints();
    // Preserve actual proof/stop/error owners before this fallible bookend.
    session.require_current()?;
    preparation.require_current()?;
    // Advisory may retain unknowns, but Certify must complete the entire
    // current scope WHILE this actual local CPU reservation still exists.
    if session.policy == ProofPolicy::Certify {
        state
            .checked
            .as_ref()
            .unwrap()
            .require_complete(state.census.as_ref().unwrap())?;
        session.require_current()?;
    }
    preparation.require_current()?;
    ensure!(
        capture.capture().succeeded(),
        "native verifier failed/cancelled or did not retain complete physical output"
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn retained_input_recheck_uses_current_root_without_renewing_execution_budget() {
        let origin = Instant::now();
        let producer = origin + Duration::from_secs(10);
        let root = origin + Duration::from_secs(100);
        let later_consumer = origin + Duration::from_secs(40);
        // Deterministic timeline DATA; this creates no Root/SDK/session/proof
        // owner. The actual retained-owner path separately requires paid prep.
        assert!(require_window(later_consumer, producer, root, InputPhase::Execution).is_err());
        require_window(later_consumer, producer, root, InputPhase::Retained).unwrap();
        assert!(require_window(root, producer, root, InputPhase::Retained).is_err());
        assert!(
            require_window(
                origin,
                root + Duration::from_secs(1),
                root,
                InputPhase::Execution
            )
            .is_err()
        );
        assert!(
            require_window(
                origin,
                root + Duration::from_secs(1),
                root,
                InputPhase::Retained
            )
            .is_err()
        );
    }
}
