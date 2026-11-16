//! Real source/repository preparation for the native Land node. This owner
//! cannot publish a ref or stand in for the still-required native Agh/Git
//! operation, current verification and independent behavior owners.
use super::*;
use std::path::PathBuf;
use trust_qualification::repository_source::RepositorySources;
use trust_resource_controller::native_job::comparison::{LandSelection, SourcePair};

/// Actual originals retained while the native publication product is prepared.
/// No public constructor, deserializer, success flag or saved receipt exists.
pub(in crate::native_job_service) struct PreparedLand {
    startup: Arc<Startup>,
    plan: Arc<Plan>,
    inputs: Arc<Inputs>,
    before: RepositorySources,
    after: RepositorySources,
    // Retain the complete source delta beside the original repository owners.
    _changed: Vec<PathBuf>,
    selection: LandSelection,
    affected: Vec<AffectedSource>,
    source: u32,
    node: NodeId,
    comparison: NodeId,
}
/// The complete native commit delta for one exact pair of actual originals.
/// It does not assert that this owner's applicable checks passed.
pub(in crate::native_job_service) struct AffectedSource {
    // Keep each original source pair and its complete changed-path DATA.
    _pair: SourcePair,
    _paths: Vec<PathBuf>,
}
impl PreparedLand {
    /// Source correspondence alone cannot replace the ordinary development
    /// gate's actual selected checks. In particular Agh's native API does not
    /// implicitly run a local Git pre-push hook.
    pub(in crate::native_job_service) fn require_publication(
        &self,
        context: &NodeContext<'_>,
        preparation: &RootPreparation,
    ) -> CargoResult<()> {
        self.require(context, preparation)?;
        ensure!(
            !self.affected.is_empty(),
            "native Land omitted every changed owner"
        );
        for affected in &self.affected {
            context.require_development_qualification(self, affected, preparation)?;
        }
        self.require(context, preparation)
    }
    pub(in crate::native_job_service) fn require(
        &self,
        context: &NodeContext<'_>,
        preparation: &RootPreparation,
    ) -> CargoResult<()> {
        preparation.require(context.startup())?;
        ensure!(
            self.node == context.node()
                && Arc::ptr_eq(&self.startup, context.startup())
                && Arc::ptr_eq(&self.plan, context.plan())
                && Arc::ptr_eq(&self.inputs, context.inputs()),
            "native Land preparation replaced its original Root/plan/inputs/node"
        );
        let compared = context
            .completed(self.comparison)?
            .comparison()
            .context("native Land lost its actual comparison owner")?;
        compared.require_for_land(context, self.source, preparation)?;
        self.selection
            .validate(context.plan(), self.source, self.comparison)?;
        let trust_resource_controller::native_job::Kind::Land {
            source,
            comparison,
            selection,
        } = &context.plan().nodes[self.node.0 as usize].kind
        else {
            anyhow::bail!("native Land preparation was grafted onto a different node family")
        };
        ensure!(
            *source == self.source
                && *comparison == self.comparison
                && selection == &self.selection,
            "native Land changed its independently selected source population"
        );
        ensure!(
            self.before.sources().len() == self.selection.sources.len()
                && self.after.sources().len() == self.selection.sources.len(),
            "native Land lost its complete source population"
        );
        for ((pair, before), after) in self
            .selection
            .sources
            .iter()
            .zip(self.before.sources())
            .zip(self.after.sources())
        {
            ensure!(
                Arc::ptr_eq(before, context.source(pair.baseline)?)
                    && Arc::ptr_eq(after, context.source(pair.candidate)?),
                "native Land changed an originally validated source owner"
            );
            ensure!(
                before.path().strip_prefix(self.before.repository_root())?
                    == after.path().strip_prefix(self.after.repository_root())?,
                "native Land paired different selected packages"
            );
        }
        self.before.validate(self.deadline()?)?;
        self.after.validate(self.deadline()?)?;
        preparation.require(context.startup())
    }
    fn deadline(&self) -> CargoResult<Instant> {
        let deadline = self
            .startup
            .workload_process
            .as_ref()
            .context("native Land lost original process/SDK owner")?
            .deadline;
        ensure!(
            Instant::now() < deadline,
            "native Land original deadline expired"
        );
        Ok(deadline)
    }
}

/// The scheduler calls this actual consumer for Kind::Land. Complete current
/// native validation must precede repository work, and the SAME original unit
/// pays for both Git/source matching and all bookends. Returning this owner is
/// not publication or a successful Land node.
pub(in crate::native_job_service) fn prepare_land(
    context: &NodeContext<'_>,
    source: u32,
    comparison: NodeId,
    selection: &LandSelection,
) -> CargoResult<PreparedLand> {
    let preparation = context.prepare()?;
    preparation.require(context.startup())?;
    let compared = context
        .completed(comparison)?
        .comparison()
        .context("native Land has no original completed comparison")?;
    ensure!(
        compared.node() == comparison,
        "native Land grafted another comparison node"
    );
    compared.require_for_land(context, source, &preparation)?;
    selection.validate(context.plan(), source, comparison)?;
    let process = context
        .startup()
        .workload_process
        .as_ref()
        .context("native Land lost actual process/SDK owner")?;
    let budget = context
        .startup()
        .descriptor_budget
        .as_ref()
        .context("native Land lost SAME descriptor admission")?;
    let before = RepositorySources::capture(
        selection
            .sources
            .iter()
            .map(|pair| context.source(pair.baseline).cloned())
            .collect::<CargoResult<Vec<_>>>()?,
        budget.clone(),
        process.deadline,
    )?;
    let after = RepositorySources::capture(
        selection
            .sources
            .iter()
            .map(|pair| context.source(pair.candidate).cloned())
            .collect::<CargoResult<Vec<_>>>()?,
        budget.clone(),
        process.deadline,
    )?;
    let delta = after.require_candidate_of(&before, process.deadline)?;
    let mut affected = Vec::with_capacity(delta.affected.len());
    for changed in delta.affected {
        ensure!(
            changed.baseline == changed.candidate,
            "native Land crossed independently selected baseline/candidate package pairs"
        );
        affected.push(AffectedSource {
            _pair: selection.sources[changed.candidate].clone(),
            _paths: changed.paths,
        });
    }
    let original = PreparedLand {
        startup: context.startup().clone(),
        plan: context.plan().clone(),
        inputs: context.inputs().clone(),
        before,
        after,
        _changed: delta.paths,
        selection: selection.clone(),
        affected,
        source,
        node: context.node(),
        comparison,
    };
    original.require(context, &preparation)?;
    Ok(original)
}
