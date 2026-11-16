//! Parent-owned comparison of the complete selected native job population.
//! Public interval/assessment values remain DATA. Only the original scheduler
//! can call this consumer; all source/program/SDK and execution owners remain
//! required when a later native Land operation consumes its opaque result.
use std::sync::Arc;
use std::time::Instant;

use anyhow::{Context as _, ensure};
use cargo_util::Sha256;
use trust_qualification::improvement::comparison::{
    ActionObservation, Assessment, ComparisonSpec, Direction, IntervalScope, Outcome,
    ProgramIdentity, RunObservations, WorkloadIdentity,
};
use trust_resource_controller::descriptors::AdmittedPackageSource;
use trust_resource_controller::native_job::{
    Artifact, Kind, NodeId, Plan, ProofPolicy, comparison::Selection,
};

use super::context::{NodeContext, RootPreparation};
use crate::ops::cargo_test::workload::{Inputs, NativeOutput};
use crate::resource_v3::Startup;
use crate::util::CargoResult;

mod publication;
pub(super) use publication::{AffectedSource, PreparedLand, prepare_land};

/// No public constructor, deserializer, status setter or qualifier. The actual
/// scheduler retains its original completed nodes while this result is used.
/// Keeping the whole registry here would create registry/capture cycles.
pub(super) struct ComparedNode {
    original: Original,
    selection: Selection,
    baseline: Artifact,
    candidate: Artifact,
    // Preserve both original observation records beside their assessment.
    _observations: [RunObservations; 2],
    assessment: Assessment,
    missing: Vec<String>,
}

struct Original {
    startup: Arc<Startup>,
    plan: Arc<Plan>,
    inputs: Arc<Inputs>,
    sources: Vec<Arc<AdmittedPackageSource>>,
    programs: [Arc<NativeOutput>; 2],
    node: NodeId,
}
impl Original {
    fn validate(&self, context: &NodeContext<'_>) -> CargoResult<()> {
        ensure!(
            Arc::ptr_eq(&self.startup, context.startup())
                && Arc::ptr_eq(&self.plan, context.plan())
                && Arc::ptr_eq(&self.inputs, context.inputs()),
            "native comparison replaced its original Root/plan/input owner"
        );
        self.inputs.validate()?;
        let process = self
            .startup
            .workload_process
            .as_ref()
            .context("native comparison lost its retained compiler/SDK owners")?;
        ensure!(
            Instant::now() < process.deadline,
            "native comparison deadline expired"
        );
        process.compiler.validate(process.deadline)?;
        process.sysroot.validate(process.deadline)?;
        for source in &self.sources {
            source.validate(process.deadline)?;
        }
        for program in &self.programs {
            program.validate(process.deadline)?;
        }
        Ok(())
    }
}
impl ComparedNode {
    pub(super) fn node(&self) -> NodeId {
        self.original.node
    }

    /// Recheck the SAME original graph and current verifier, never a prior
    /// assessment/receipt/JSON. An observed lower interval alone cannot land.
    pub(super) fn require_for_land(
        &self,
        context: &NodeContext<'_>,
        source: u32,
        preparation: &RootPreparation,
    ) -> CargoResult<()> {
        preparation.require(context.startup())?;
        self.original.validate(context)?;
        ensure!(
            self.original.node.0 < context.node().0,
            "native landing precedes comparison"
        );
        ensure!(
            source == program_source(&self.original.plan, &self.candidate)?,
            "native landing source is not the actually built candidate"
        );
        self.require_complete(context, preparation)?;
        // Timing-pair membership is not the landing gate's denominator. Every
        // requested preceding operation must still have its own actual native
        // completion/validation owner, including unrelated obligations.
        for index in 0..context.node().0 {
            let id = NodeId(index);
            let record = context.completed(id)?;
            match &context.plan().nodes[index as usize].kind {
                Kind::Compare { .. } => record
                    .comparison()
                    .context("native landing omitted a requested comparison owner")?
                    .require_complete(context, preparation)?,
                Kind::Land { .. } => {
                    anyhow::bail!("one native Land profile cannot replay a prior publication")
                }
                _ => record.require_native_validation(context, preparation)?,
            }
        }
        self.original.validate(context)?;
        preparation.require(context.startup())
    }

    /// The scheduler may observe completion only through this live bookend.
    /// The read-only assessment and elapsed values never imply it.
    pub(super) fn require_complete(
        &self,
        context: &NodeContext<'_>,
        preparation: &RootPreparation,
    ) -> CargoResult<()> {
        preparation.require(context.startup())?;
        self.original.validate(context)?;
        self.selection.validate(
            &self.original.plan,
            &self.baseline,
            &self.candidate,
            self.original.node,
        )?;
        ensure!(
            self.missing.is_empty(),
            "native comparison has unavailable required owners: {:?}",
            self.missing
        );
        context.require_comparison_configuration(
            &self.baseline,
            &self.candidate,
            &self.selection,
        )?;
        // Only the actual requested applicable proof scopes are judged here.
        // Structural/unverified source qualification does not imply whole-tool
        // formal correctness and never upgrades a proof grade.
        for pair in &self.selection.pairs {
            for node in [pair.baseline, pair.candidate] {
                context
                    .completed(node)?
                    .require_native_validation(context, preparation)?;
                if let Kind::Verify {
                    artifact,
                    policy: ProofPolicy::Certify,
                } = &context.plan().nodes[node.0 as usize].kind
                {
                    context.require_current_verification(artifact, preparation)?;
                }
            }
        }
        let Assessment::Comparable { focus, actions } = &self.assessment else {
            anyhow::bail!("native comparison is incomplete or has a required regression");
        };
        ensure!(
            actions
                .iter()
                .any(|action| &action.action == focus && action.direction == Direction::Lower),
            "native comparison did not observe a lower preselected focus interval"
        );
        self.original.validate(context)?;
        preparation.require(context.startup())
    }
}

fn program_source(plan: &Plan, artifact: &Artifact) -> CargoResult<u32> {
    match &plan
        .nodes
        .get(artifact.producer.0 as usize)
        .context("native program producer omitted")?
        .kind
    {
        Kind::Compile { source, unit, .. } if unit == &artifact.unit => Ok(*source),
        _ => anyhow::bail!("native comparison program is not its selected actual compiler product"),
    }
}
fn add_reason(reasons: &mut Vec<String>, error: impl std::fmt::Display) {
    // Original full errors/captures remain in completed-node owners. Bound only
    // this duplicate diagnostic summary; do not use its text to grade a row.
    if reasons.len() < 256 {
        reasons.push(error.to_string().chars().take(1024).collect());
    }
}
fn hash(domain: &[u8], pieces: impl IntoIterator<Item = Vec<u8>>) -> String {
    let mut hash = Sha256::new();
    hash.update(domain);
    for piece in pieces {
        hash.update(&(piece.len() as u64).to_be_bytes());
        hash.update(&piece);
    }
    hash.finish_hex()
}

/// Consume actual scheduler outcomes. No node is removed from the denominator
/// when admission, behavior/current proof, retirement or capture was unavailable.
pub(super) fn compare(
    context: &NodeContext<'_>,
    baseline: &Artifact,
    candidate: &Artifact,
    selection: &Selection,
) -> CargoResult<ComparedNode> {
    selection.validate(context.plan(), baseline, candidate, context.node())?;
    let paid = context.prepare()?;
    paid.require(context.startup())?;
    let before = context.artifact(baseline)?;
    before.validate()?;
    let after = context.artifact(candidate)?;
    after.validate()?;
    let programs = [before.program()?, after.program()?];
    let mut sources = Vec::new();
    for index in 0..context.plan().sources.len() {
        sources.push(context.source(index as u32)?.clone());
    }
    let original = Original {
        startup: context.startup().clone(),
        plan: context.plan().clone(),
        inputs: context.inputs().clone(),
        sources,
        programs,
        node: context.node(),
    };
    original.validate(context)?;
    let identity = |artifact: &Artifact, program: &NativeOutput| -> CargoResult<ProgramIdentity> {
        let source = context.source(program_source(context.plan(), artifact)?)?;
        Ok(ProgramIdentity {
            build_source_sha256: hex::encode(source.content_digest()),
            program_sha256: program.image().observation().executable.sha256.clone(),
        })
    };
    let identities = [
        identity(baseline, &original.programs[0])?,
        identity(candidate, &original.programs[1])?,
    ];
    // These are DATA fingerprints beneath the original-owner checks, not a
    // substitute for complete effective-configuration/behavior validation.
    let source_identity = hash(
        b"trust.native-comparison.workload-sources.v1\0",
        selection
            .workload_sources
            .iter()
            .map(|index| {
                context
                    .source(*index)
                    .map(|source| source.content_digest().to_vec())
            })
            .collect::<CargoResult<Vec<_>>>()?,
    );
    let plan_bytes = context.plan().encode()?;
    let workload = WorkloadIdentity {
        source_sha256: source_identity,
        configuration_sha256: hash(
            b"trust.native-comparison.preselected-plan.v1\0",
            [plan_bytes],
        ),
        coverage_sha256: hash(
            b"trust.native-comparison.population.v1\0",
            selection.pairs.iter().map(|pair| {
                format!(
                    "{}\0{}\0{}\0{}",
                    pair.action, pair.repetition, pair.baseline.0, pair.candidate.0
                )
                .into_bytes()
            }),
        ),
    };
    let process = original
        .startup
        .workload_process
        .as_ref()
        .context("native SDK owner omitted")?;
    let sdk = hash(
        b"trust.native-comparison.retained-sdk.v1\0",
        std::iter::once(
            process
                .compiler
                .observation()
                .executable
                .sha256
                .as_bytes()
                .to_vec(),
        )
        .chain(
            process
                .compiler
                .observation()
                .runtime
                .iter()
                .map(|file| file.sha256.as_bytes().to_vec()),
        )
        .chain(
            process
                .sysroot
                .file_observations()
                .map(|file| file.sha256.as_bytes().to_vec()),
        ),
    );
    let parent = trust_resource_provenance::process::read_identity(std::process::id())?;
    let mut missing = Vec::new();
    let mut actions: [Vec<ActionObservation>; 2] = [Vec::new(), Vec::new()];
    if let Err(error) = context.require_comparison_configuration(baseline, candidate, selection) {
        add_reason(&mut missing, error);
    }
    let mut behavior = false;
    for pair in &selection.pairs {
        for (side, node) in [pair.baseline, pair.candidate].into_iter().enumerate() {
            let mut outcome = Outcome::CouldNotRun;
            let mut interval = None;
            match context.completed(node) {
                Ok(record) => {
                    interval = u64::try_from(record.interval().elapsed().as_nanos()).ok();
                    let checked = (|| -> CargoResult<()> {
                        record.require_native_validation(context, &paid)?;
                        match &context.plan().nodes[node.0 as usize].kind {
                            Kind::Compile { .. } => {
                                record.require_frontend(&original.programs[side])?
                            }
                            Kind::Verify { artifact, policy } => {
                                // Advisory still needs its actual session/census
                                // and native closure above. It never becomes a
                                // Certified grade because comparison completed.
                                if *policy == ProofPolicy::Certify {
                                    context.require_current_verification(artifact, &paid)?;
                                }
                            }
                            Kind::Run { .. } | Kind::Tests { .. } => {
                                behavior = true;
                            }
                            _ => anyhow::bail!("unselected native comparison action kind"),
                        }
                        Ok(())
                    })();
                    match checked {
                        Ok(()) => outcome = Outcome::Succeeded,
                        Err(error) => add_reason(&mut missing, error),
                    }
                }
                Err(error) => add_reason(&mut missing, error),
            }
            actions[side].push(ActionObservation {
                action: pair.action.clone(),
                repetition: pair.repetition,
                outcome,
                elapsed_ns: interval,
                scope: IntervalScope::ParentActionIntervalV1,
            });
        }
    }
    if !behavior {
        add_reason(
            &mut missing,
            "no independently validated test/application provider in the required population",
        );
    }
    let observations = std::array::from_fn(|side| RunObservations {
        run_sha256: hash(
            b"trust.native-comparison.original-run.v1\0",
            [
                context.startup().query.binding.root_attempt.to_vec(),
                format!(
                    "{}:{}:{}:{}",
                    parent.pid, parent.birth, parent.unique_id, parent.exec_version
                )
                .into_bytes(),
                selection
                    .pairs
                    .iter()
                    .map(|pair| {
                        if side == 0 {
                            pair.baseline.0
                        } else {
                            pair.candidate.0
                        }
                    })
                    .flat_map(u32::to_be_bytes)
                    .collect(),
            ],
        ),
        program: identities[side].clone(),
        workload: workload.clone(),
        sdk_sha256: sdk.clone(),
        actions: std::mem::take(&mut actions[side]),
    });
    let names = selection
        .pairs
        .iter()
        .map(|pair| pair.action.clone())
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    let spec = ComparisonSpec::new(
        identities[0].clone(),
        identities[1].clone(),
        workload,
        sdk,
        names,
        selection.repetitions,
        selection.focus.clone(),
    )?;
    let assessment = spec.assess(&observations[0], &observations[1]);
    original.validate(context)?;
    ensure!(
        trust_resource_provenance::process::read_identity(parent.pid)? == parent,
        "native comparison process image changed"
    );
    paid.require(context.startup())?;
    Ok(ComparedNode {
        original,
        selection: selection.clone(),
        baseline: baseline.clone(),
        candidate: candidate.clone(),
        _observations: observations,
        assessment,
        missing,
    })
}
