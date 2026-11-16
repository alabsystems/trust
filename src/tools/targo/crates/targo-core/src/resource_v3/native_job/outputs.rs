//! Actual per-output-root custody for ONE original general job. Paths select
//! equality rows; only the original FD-derived root and Layout OFDs live here.
use crate::compiler::build_runner::OriginalOutputLeases;
use crate::ops::cargo_test::workload::Inputs;
use crate::resource_v3::Startup;
use crate::util::CargoResult;
use anyhow::Context as _;
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt as _;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use trust_resource_controller::descriptors::AdmittedOutputRoot;
use trust_resource_controller::native_job::{Kind, NodeId, Plan};
fn path(bytes: &[u8]) -> PathBuf {
    PathBuf::from(OsString::from_vec(bytes.to_vec()))
}
pub(crate) struct Outputs {
    plan: Arc<Plan>,
    master: Arc<Inputs>,
    selected: Vec<Arc<AdmittedOutputRoot>>,
    leases: Mutex<BTreeMap<u32, Arc<OriginalOutputLeases>>>,
}
/// Retired compiler/capture owners live outside Startup. A native capture
/// retains Startup itself, so placing this cache in Startup's output registry
/// would create an ownership cycle and keep originals alive forever.
pub(crate) struct Artifacts {
    outputs: Arc<Outputs>,
    entries: Mutex<BTreeMap<(u32, String), Arc<crate::compiler::native_job::RetiredArtifact>>>,
    ledgers: Mutex<BTreeMap<u32, crate::compiler::candidate_dependencies::Ledger>>,
}
impl Outputs {
    pub(crate) fn prepare(startup: &Arc<Startup>, master: Arc<Inputs>) -> CargoResult<Arc<Self>> {
        let plan = master
            .native_plan()
            .context("native output registry requires original general-job inputs")?
            .clone();
        let actual = super::require(&plan)?;
        anyhow::ensure!(
            Arc::ptr_eq(startup, &actual),
            "output registry replaced actual Startup"
        );
        let bank = startup
            .workload_bank
            .as_ref()
            .context("output registry lost original bank")?;
        let loan = bank
            .try_primary()?
            .context("native output preparation primary unavailable")?;
        loan.require_preparation(&loan.lease())?;
        let deadline = startup
            .workload_process
            .as_ref()
            .context("native output registry lost original process")?
            .deadline;
        master.validate()?;
        let mut exclusions = master.sdk().publication_exclusions(deadline)?;
        for index in 0..plan.sources.len() {
            let identity = master
                .native_source(index)?
                .original_root_identity(deadline)?;
            exclusions.trees.push((identity.device, identity.inode));
        }
        let budget = startup
            .descriptor_budget
            .as_ref()
            .context("output registry lost SAME native descriptor budget")?;
        let mut selected = Vec::new();
        for output in &plan.outputs {
            // Only a positively absent master-relative lookup can choose
            // create-new. EEXIST/races/other failures never trigger fallback.
            let owner = match budget.capture_output_root(
                master.held_output_root(),
                &path(&output.root),
                deadline,
            ) {
                Ok(owner) => owner,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => budget
                    .prepare_output_root(
                        master.held_output_root(),
                        &path(&output.root),
                        &exclusions,
                        deadline,
                    )?,
                Err(error) => return Err(error.into()),
            };
            owner
                .original()
                .require_disjoint_trees(&exclusions, deadline)?;
            exclusions
                .trees
                .push(owner.original().original_identity(deadline)?);
            selected.push(owner);
        }
        master.validate()?;
        drop(loan); // Unbound lexical preparation only; no Host delivery.
        Ok(Arc::new(Self {
            plan,
            master,
            selected,
            leases: Mutex::new(BTreeMap::new()),
        }))
    }
    pub(crate) fn plan(&self) -> &Arc<Plan> {
        &self.plan
    }
    pub(crate) fn master(&self) -> &Arc<Inputs> {
        &self.master
    }
    pub(crate) fn inputs(&self, node: NodeId) -> CargoResult<Arc<Inputs>> {
        let Some(Kind::Compile { output, .. }) =
            self.plan.nodes.get(node.0 as usize).map(|node| &node.kind)
        else {
            anyhow::bail!("native output inputs require a declared compile node")
        };
        self.master
            .native_compile_inputs(self.selected[*output as usize].clone(), node)
    }
    fn require_inputs(&self, inputs: &Arc<Inputs>) -> CargoResult<u32> {
        super::require(&self.plan)?;
        let node = inputs
            .native_compile_node()
            .context("output custody lacks original compile selection")?;
        let Some(Kind::Compile { output, .. }) =
            self.plan.nodes.get(node.0 as usize).map(|node| &node.kind)
        else {
            anyhow::bail!("output custody selected another node kind")
        };
        anyhow::ensure!(
            inputs
                .native_plan()
                .is_some_and(|plan| Arc::ptr_eq(plan, &self.plan))
                && inputs
                    .native_master()
                    .is_some_and(|master| Arc::ptr_eq(master, &self.master))
                && inputs
                    .native_selected_root()
                    .is_some_and(|root| Arc::ptr_eq(root, &self.selected[*output as usize])),
            "output custody replaced original plan/master/selected root"
        );
        inputs.validate()?;
        Ok(*output)
    }
    pub(crate) fn retain_leases(
        &self,
        inputs: &Arc<Inputs>,
        leases: Arc<OriginalOutputLeases>,
    ) -> CargoResult<()> {
        let output = self.require_inputs(inputs)?;
        leases.validate(self.selected[output as usize].original().path())?;
        let mut held = self
            .leases
            .lock()
            .map_err(|_| anyhow::anyhow!("native original Layout registry poisoned"))?;
        if let Some(original) = held.get(&output) {
            anyhow::ensure!(
                Arc::ptr_eq(original, &leases),
                "native graph replaced original Layout OFDs"
            );
        } else {
            held.insert(output, leases);
        }
        Ok(())
    }
    pub(crate) fn leases(
        &self,
        inputs: &Arc<Inputs>,
    ) -> CargoResult<Option<Arc<OriginalOutputLeases>>> {
        let output = self.require_inputs(inputs)?;
        let held = self
            .leases
            .lock()
            .map_err(|_| anyhow::anyhow!("native original Layout registry poisoned"))?;
        let original = held.get(&output).cloned();
        if let Some(original) = &original {
            original.validate(self.selected[output as usize].original().path())?;
        }
        Ok(original)
    }
    pub(crate) fn artifacts(self: &Arc<Self>) -> Arc<Artifacts> {
        Arc::new(Artifacts {
            outputs: self.clone(),
            entries: Mutex::new(BTreeMap::new()),
            ledgers: Mutex::new(BTreeMap::new()),
        })
    }
    pub(crate) fn require_registered(
        &self,
        root: &std::path::Path,
        leases: &Arc<OriginalOutputLeases>,
    ) -> CargoResult<()> {
        super::require(&self.plan)?;
        let index = self
            .selected
            .iter()
            .position(|owner| owner.original().path() == root)
            .context("Layout root is outside the actual selected population")?
            as u32;
        let held = self
            .leases
            .lock()
            .map_err(|_| anyhow::anyhow!("native original Layout registry poisoned"))?;
        anyhow::ensure!(
            held.get(&index)
                .is_some_and(|original| Arc::ptr_eq(original, leases)),
            "Layout is not the actual registered original capsule"
        );
        self.selected[index as usize].validate(self.master.evidence.deadline())?;
        leases.validate(root)
    }
}
impl Artifacts {
    /// Only the actual retained domain can cross sequential coordinator epochs.
    pub(crate) fn take_ledger(
        &self,
        inputs: &Arc<Inputs>,
    ) -> CargoResult<Option<crate::compiler::candidate_dependencies::Ledger>> {
        let output = self.outputs.require_inputs(inputs)?;
        Ok(self
            .ledgers
            .lock()
            .map_err(|_| anyhow::anyhow!("native dependency cache poisoned"))?
            .remove(&output))
    }
    pub(crate) fn retain_ledger(
        &self,
        inputs: &Arc<Inputs>,
        ledger: crate::compiler::candidate_dependencies::Ledger,
    ) -> CargoResult<()> {
        let output = match self.outputs.require_inputs(inputs) {
            Ok(output) => output,
            Err(error) => {
                std::mem::forget(ledger);
                return Err(error);
            }
        };
        let mut owners = match self.ledgers.lock() {
            Ok(owners) => owners,
            Err(poisoned) => {
                // Preserve the full native capture domain on poisoning.
                std::mem::forget(ledger);
                drop(poisoned);
                anyhow::bail!("native dependency cache poisoned");
            }
        };
        if owners.contains_key(&output) {
            std::mem::forget(ledger);
            anyhow::bail!("native output domain already has an owned dependency epoch");
        }
        owners.insert(output, ledger);
        Ok(())
    }

    pub(crate) fn cached(
        &self,
        inputs: &Arc<Inputs>,
        key: &str,
    ) -> CargoResult<Option<Arc<crate::compiler::native_job::RetiredArtifact>>> {
        let output = self.outputs.require_inputs(inputs)?;
        Ok(self
            .entries
            .lock()
            .map_err(|_| anyhow::anyhow!("native retired-output registry poisoned"))?
            .get(&(output, key.to_owned()))
            .cloned())
    }
    pub(crate) fn retain(
        &self,
        inputs: &Arc<Inputs>,
        artifact: Arc<crate::compiler::native_job::RetiredArtifact>,
    ) -> CargoResult<()> {
        let output = self.outputs.require_inputs(inputs)?;
        let mut artifacts = self
            .entries
            .lock()
            .map_err(|_| anyhow::anyhow!("native retired-output registry poisoned"))?;
        anyhow::ensure!(
            artifacts.len() < 4096,
            "native retained artifact population exceeds bound"
        );
        artifacts.insert((output, artifact.key().to_owned()), artifact);
        Ok(())
    }
    pub(crate) fn require_outputs(&self, outputs: &Arc<Outputs>) -> CargoResult<()> {
        anyhow::ensure!(
            Arc::ptr_eq(outputs, &self.outputs),
            "retired artifact cache replaced its actual output domain"
        );
        Ok(())
    }
}
