//! Read-only native scheduler context. No decoded record can construct a
//! completed node, actual artifact or original resource preparation owner.
use crate::compiler::native_job::{Artifact, Attempt};
use crate::ops::cargo_test::workload::Inputs;
use crate::resource_v3::{Startup, native_job::outputs::Outputs};
use crate::util::CargoResult;
use anyhow::Context as _;
use std::sync::Arc;
use std::time::{Duration, Instant};
use trust_resource_controller::descriptors::AdmittedPackageSource;
use trust_resource_controller::native_job::{Kind, NodeId, Plan};

/// This interval is measured around the original parent's actual node call.
/// It is metric DATA; it grants neither native retirement nor a proof grade.
pub(super) struct ParentActionInterval {
    entered: Instant,
    returned: Instant,
}
impl ParentActionInterval {
    pub(super) fn elapsed(&self) -> Duration {
        self.returned.duration_since(self.entered)
    }
}
pub(super) struct CompletedNode {
    id: NodeId,
    interval: ParentActionInterval,
    compile: Option<Attempt>,
    comparison: Option<super::comparison_attempt::Attempt>,
    land: Option<super::land_attempt::Attempt>,
    verification: Option<super::verification::VerificationAttempt>,
    failure: Option<String>,
    // Observed solely while the actual returned continuation still existed.
    // Later moving that original to the next node does not erase this fact.
    retired: bool,
}
impl CompletedNode {
    pub(super) fn compiler_executions(&self) -> Option<u64> {
        if let Some(attempt) = self.verification() {
            return attempt.compiler_executions();
        }
        if let Some(attempt) = self.compile() {
            return (self.retired && attempt.result().is_ok())
                .then(|| attempt.compiler_executions() as u64);
        }
        (self.comparison.is_some() || self.land.is_some()).then_some(0)
    }
    pub(super) fn reused_units(&self) -> Option<u64> {
        if let Some(attempt) = self.compile() {
            return (self.retired && attempt.result().is_ok()).then(|| attempt.warm_units() as u64);
        }
        (self.verification.is_some() || self.comparison.is_some() || self.land.is_some())
            .then_some(0)
    }
    pub(super) fn verification(&self) -> Option<&super::verification::VerificationAttempt> {
        self.verification.as_ref()
    }
    pub(super) fn verified(
        id: NodeId,
        entered: Instant,
        returned: Instant,
        attempt: super::verification::VerificationAttempt,
    ) -> Self {
        let failure = attempt.result().err().map(|error| format!("{error:#}"));
        let retired = attempt.has_retained_continuation();
        Self {
            id,
            interval: ParentActionInterval { entered, returned },
            compile: None,
            comparison: None,
            land: None,
            verification: Some(attempt),
            failure,
            retired,
        }
    }
    pub(super) fn comparison(&self) -> Option<&super::comparison::ComparedNode> {
        self.comparison
            .as_ref()
            .and_then(super::comparison_attempt::Attempt::comparison)
    }
    pub(super) fn compared(
        id: NodeId,
        entered: Instant,
        returned: Instant,
        attempt: super::comparison_attempt::Attempt,
    ) -> Self {
        let failure = attempt.failure();
        let retired = attempt.retired();
        Self {
            id,
            interval: ParentActionInterval { entered, returned },
            compile: None,
            comparison: Some(attempt),
            land: None,
            verification: None,
            failure,
            retired,
        }
    }
    pub(super) fn land(
        id: NodeId,
        entered: Instant,
        returned: Instant,
        attempt: super::land_attempt::Attempt,
    ) -> Self {
        let failure = Some(attempt.failure());
        let retired = attempt.retired();
        Self {
            id,
            interval: ParentActionInterval { entered, returned },
            compile: None,
            comparison: None,
            land: Some(attempt),
            verification: None,
            failure,
            retired,
        }
    }
    pub(super) fn require_frontend(
        &self,
        original: &Arc<crate::ops::cargo_test::workload::NativeOutput>,
    ) -> CargoResult<()> {
        let attempt = self
            .compile
            .as_ref()
            .context("comparison action has no actual compiler attempt owner")?;
        attempt.require_frontend(original)
    }
    pub(super) fn require_native_validation(
        &self,
        context: &NodeContext<'_>,
        preparation: &RootPreparation,
    ) -> CargoResult<()> {
        preparation.require(context.startup())?;
        anyhow::ensure!(
            self.succeeded(),
            "native comparison node has no successful retained completion owner"
        );
        if let Some(attempt) = self.verification.as_ref() {
            attempt.result()?;
            let Kind::Verify { artifact, policy } = &context.plan().nodes[self.id.0 as usize].kind
            else {
                anyhow::bail!("verification completion differs from its actual native role")
            };
            if *policy == trust_resource_controller::native_job::ProofPolicy::Certify {
                attempt.require_current(context, artifact, preparation)?;
            }
            return preparation.require(context.startup());
        }
        let attempt = self
            .compile
            .as_ref()
            .context("native comparison node has no current typed consumer owner")?;
        attempt.result()?;
        let artifact = attempt
            .artifact()
            .context("native comparison compiler omitted actual output owner")?;
        artifact.validate()?;
        let Kind::Compile { .. } = &context.plan().nodes[self.id.0 as usize].kind else {
            anyhow::bail!("native comparison node lacks its own native role provider")
        };
        // Compilation claims actual native compile/output closure only. A
        // requested Verify/Run/Tests node supplies its own proof/behavior owner.
        preparation.require(context.startup())
    }
    pub(super) fn compiler(
        id: NodeId,
        entered: Instant,
        returned: Instant,
        attempt: Attempt,
    ) -> Self {
        let failure = attempt
            .result()
            .err()
            .map(|error| format!("{error:#}"))
            .or_else(|| attempt.continuation_failure().map(str::to_owned));
        let retired = attempt.has_retained_continuation();
        Self {
            id,
            interval: ParentActionInterval { entered, returned },
            compile: Some(attempt),
            comparison: None,
            land: None,
            verification: None,
            failure,
            retired,
        }
    }
    pub(super) fn refused(
        id: NodeId,
        entered: Instant,
        returned: Instant,
        error: anyhow::Error,
    ) -> Self {
        Self {
            id,
            interval: ParentActionInterval { entered, returned },
            compile: None,
            comparison: None,
            land: None,
            verification: None,
            failure: Some(format!("{error:#}")),
            retired: false,
        }
    }
    pub(super) fn id(&self) -> NodeId {
        self.id
    }
    pub(super) fn interval(&self) -> &ParentActionInterval {
        &self.interval
    }
    pub(super) fn compile(&self) -> Option<&Attempt> {
        self.compile.as_ref()
    }
    pub(super) fn failure(&self) -> Option<&str> {
        self.failure.as_deref()
    }
    pub(super) fn retired(&self) -> bool {
        self.retired
    }
    pub(super) fn succeeded(&self) -> bool {
        self.retired
            && self.failure.is_none()
            && (self
                .compile
                .as_ref()
                .is_some_and(|attempt| attempt.artifact().is_some())
                || self.comparison().is_some()
                || self.verification.is_some())
    }
    pub(super) fn take_continuation(
        &mut self,
    ) -> Option<crate::compiler::native_job::NativeRetainedGraph> {
        self.compile
            .as_mut()
            .and_then(Attempt::take_continuation)
            .or_else(|| {
                self.comparison
                    .as_mut()
                    .and_then(super::comparison_attempt::Attempt::take_continuation)
            })
            .or_else(|| {
                self.verification
                    .as_mut()
                    .and_then(super::verification::VerificationAttempt::take_continuation)
            })
            .or_else(|| {
                self.land
                    .as_mut()
                    .and_then(super::land_attempt::Attempt::take_continuation)
            })
    }
}

pub(super) struct NodeContext<'a> {
    node: NodeId,
    startup: &'a Arc<Startup>,
    plan: &'a Arc<Plan>,
    inputs: &'a Arc<Inputs>,
    outputs: &'a Arc<Outputs>,
    completed: &'a [CompletedNode],
}
impl<'a> NodeContext<'a> {
    pub(super) fn require_development_qualification(
        &self,
        _prepared: &super::comparison::PreparedLand,
        _affected: &super::comparison::AffectedSource,
        preparation: &RootPreparation,
    ) -> CargoResult<()> {
        preparation.require(self.startup)?;
        anyhow::bail!(
            "native source-main publication lacks the actual applicable source-delta qualification owner; repository/plan/timing DATA cannot replace ordinary development gates"
        )
    }
    pub(super) fn require_comparison_configuration(
        &self,
        _baseline: &trust_resource_controller::native_job::Artifact,
        _candidate: &trust_resource_controller::native_job::Artifact,
        _selection: &trust_resource_controller::native_job::comparison::Selection,
    ) -> CargoResult<()> {
        anyhow::bail!(
            "native comparison has no independently preselected full-configuration/controlled-factor owner; whole-plan hash is DATA only"
        )
    }
    pub(super) fn new(
        node: NodeId,
        startup: &'a Arc<Startup>,
        plan: &'a Arc<Plan>,
        inputs: &'a Arc<Inputs>,
        outputs: &'a Arc<Outputs>,
        completed: &'a [CompletedNode],
    ) -> CargoResult<Self> {
        let actual = crate::resource_v3::native_job::require(plan)?;
        anyhow::ensure!(
            Arc::ptr_eq(startup, &actual)
                && Arc::ptr_eq(plan, outputs.plan())
                && Arc::ptr_eq(inputs, outputs.master())
                && inputs
                    .native_plan()
                    .is_some_and(|original| Arc::ptr_eq(original, plan)),
            "native node context replaced original Startup/Plan/input/output registry"
        );
        let selected = plan
            .nodes
            .get(node.0 as usize)
            .context("native selected node is outside the complete plan")?;
        for dependency in &selected.dependencies {
            let previous = completed
                .iter()
                .find(|record| record.id() == dependency.node)
                .context("native node lacks an actual prerequisite record")?;
            anyhow::ensure!(
                match dependency.condition {
                    trust_resource_controller::native_job::EdgeCondition::Retired =>
                        previous.retired(),
                    trust_resource_controller::native_job::EdgeCondition::Succeeded =>
                        previous.succeeded(),
                },
                "native prerequisite has no required actual retirement/success owner"
            );
        }
        Ok(Self {
            node,
            startup,
            plan,
            inputs,
            outputs,
            completed,
        })
    }
    pub(super) fn node(&self) -> NodeId {
        self.node
    }
    pub(super) fn plan(&self) -> &Arc<Plan> {
        self.plan
    }
    pub(super) fn startup(&self) -> &Arc<Startup> {
        self.startup
    }
    pub(super) fn inputs(&self) -> &Arc<Inputs> {
        self.inputs
    }
    pub(super) fn outputs(&self) -> &Arc<Outputs> {
        self.outputs
    }
    pub(super) fn source(&self, index: u32) -> CargoResult<&Arc<AdmittedPackageSource>> {
        self.inputs.native_source(index as usize)
    }
    pub(super) fn completed(&self, id: NodeId) -> CargoResult<&CompletedNode> {
        self.completed
            .iter()
            .find(|record| record.id() == id)
            .context("native node was not actually completed in this original job")
    }
    pub(super) fn artifact(
        &self,
        declared: &trust_resource_controller::native_job::Artifact,
    ) -> CargoResult<&Artifact> {
        let record = self.completed(declared.producer)?;
        anyhow::ensure!(
            record.succeeded(),
            "native artifact producer has no actual successful retained completion"
        );
        let artifact = record
            .compile()
            .and_then(Attempt::artifact)
            .context("native artifact lacks its original compiler output owner")?;
        artifact.require(declared)?;
        Ok(artifact)
    }
    /// A current proof-kernel owner must be provided by the native Verify
    /// consumer. Neither a compiler return nor an interval supplies it.
    pub(super) fn require_current_verification(
        &self,
        artifact: &trust_resource_controller::native_job::Artifact,
        preparation: &RootPreparation,
    ) -> CargoResult<()> {
        preparation.require(self.startup)?;
        let mut failures = Vec::new();
        for record in self.completed {
            if !record.succeeded() {
                continue;
            }
            let Some(attempt) = record.verification() else {
                continue;
            };
            let Kind::Verify {
                artifact: covered, ..
            } = &self.plan.nodes[record.id().0 as usize].kind
            else {
                continue;
            };
            if covered != artifact {
                continue;
            }
            match attempt.require_current(self, artifact, preparation) {
                Ok(()) => return Ok(()),
                Err(error) => failures.push(format!("{error:#}")),
            }
        }
        anyhow::bail!(
            "native artifact has no required complete current-kernel owner: {}",
            failures.join("; ")
        )
    }
    pub(super) fn prepare(&self) -> CargoResult<RootPreparation> {
        let actual = crate::resource_v3::native_job::require(self.plan)?;
        anyhow::ensure!(
            Arc::ptr_eq(&actual, self.startup),
            "native preparation replaced actual Startup"
        );
        let bank = self
            .startup
            .workload_bank
            .as_ref()
            .context("native preparation lost original bank")?;
        let loan = bank
            .try_primary()?
            .context("native preparation lacks a real available original unit")?;
        let lease = loan.lease();
        loan.require_preparation(&lease)?;
        let preparation = RootPreparation {
            startup: self.startup.clone(),
            loan,
            lease,
        };
        preparation.require(self.startup)?;
        self.inputs.validate()?;
        preparation.require(self.startup)?;
        Ok(preparation)
    }
}
/// A live unbound SAME-bank reservation for fixed trusted Root preparation.
/// No public callback, command, status or Boolean can construct this value.
pub(super) struct RootPreparation {
    startup: Arc<Startup>,
    loan: Arc<crate::resource_v3::workload::bank::PrimaryLoan>,
    lease: Arc<trust_build_cpu::Lease>,
}
impl RootPreparation {
    pub(super) fn require(&self, startup: &Arc<Startup>) -> CargoResult<()> {
        let plan = startup
            .native_job_plan
            .as_ref()
            .context("native preparation lost its actual whole plan")?;
        let actual = crate::resource_v3::native_job::require(plan)?;
        anyhow::ensure!(
            Arc::ptr_eq(startup, &self.startup) && Arc::ptr_eq(startup, &actual),
            "native preparation replaced actual Startup"
        );
        Ok(self.loan.require_preparation(&self.lease)?)
    }
}
