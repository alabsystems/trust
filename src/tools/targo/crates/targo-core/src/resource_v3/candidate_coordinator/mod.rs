//! A produced coordinator continues one actual parent-bank primary. It owns
//! neither a root bank nor permission to acquire an additional native unit.
use crate::compiler::build_runner::OriginalOutputLeases;
use crate::util::CargoResult;
use anyhow::Context as _;
use std::io;
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};
use std::time::Instant;
use trust_resource_controller::client::{CoordinatorBroker, CoordinatorOriginals};
use trust_resource_controller::descriptors::{AdmittedPackageSource, AdmittedTargetSysroot};
use trust_resource_provenance::program::HeldProgram;

pub(super) mod executor;
pub(crate) mod startup;

/// The original receiver remains intact even after Layout and CPU adoption.
/// Its descriptions are close-only and outlive all per-command copies.
pub(crate) struct Original {
    pub(crate) broker: std::sync::Mutex<CoordinatorBroker>,
    pub(crate) originals: Arc<CoordinatorOriginals>,
    pub(crate) compiler: Arc<HeldProgram>,
    pub(crate) sysroot: Arc<AdmittedTargetSysroot>,
    pub(crate) sources: Vec<Arc<AdmittedPackageSource>>,
    pub(crate) outputs: Arc<OriginalOutputLeases>,
    // Actual descriptions and per-command duplicates close before this charge.
    _input_permit: Arc<trust_resource_controller::descriptors::OriginalInputPermit>,
    pub(crate) deadline: Instant,
    pub(crate) busy: Arc<AtomicBool>,
    failed: AtomicBool,
}
impl Original {
    pub(crate) fn check(&self) -> io::Result<()> {
        let result = (|| {
            if self.failed.load(Ordering::Acquire) || Instant::now() >= self.deadline {
                return Err(io::Error::other("original candidate failed or expired"));
            }
            self.originals.validate(self.deadline)?;
            self.sysroot.validate(self.deadline)?;
            for source in &self.sources {
                source.validate(self.deadline)?;
            }
            let root = startup::path(&self.originals.observation().plan.output_root);
            self.outputs.validate(&root).map_err(io::Error::other)?;
            self.originals.validate(self.deadline)
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }
    pub(crate) fn poison(&self) {
        self.failed.store(true, Ordering::Release);
    }
    pub(crate) fn validate_command(
        &self,
        command: &trust_resource_controller::CommandSpec,
    ) -> io::Result<()> {
        self.check()?;
        self.sysroot.validate_invocation(
            &self.compiler,
            &command.program,
            command.arg0.as_deref(),
            &command.args,
            &command.environment,
            self.deadline,
        )
    }
    pub(crate) fn publish(
        &self,
        selection: trust_resource_controller::workload::host::coordinator::PublicationSelection,
    ) -> io::Result<trust_resource_controller::client::PublicationAcknowledgement> {
        self.check()?;
        if self
            .busy
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return Err(io::Error::other(
                "candidate has an active compiler/publication continuation",
            ));
        }
        let result = (|| {
            let mut broker = self
                .broker
                .lock()
                .map_err(|_| io::Error::other("candidate original broker poisoned"))?;
            let ack = broker.publish(selection, self.deadline)?;
            self.check()?;
            Ok(ack)
        })();
        if result.is_err() {
            self.poison();
        }
        self.busy.store(false, Ordering::Release);
        result
    }
    pub(crate) fn finish(&self) -> CargoResult<()> {
        self.check()?;
        anyhow::ensure!(
            self.busy
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_ok(),
            "candidate still owns an outgoing compiler/publication continuation"
        );
        let result = (|| {
            let mut broker = self
                .broker
                .lock()
                .map_err(|_| io::Error::other("candidate original broker poisoned"))?;
            let _ack = broker.finish_graph(self.deadline)?;
            self.check()?;
            Ok(())
        })();
        if result.is_err() {
            self.poison();
        }
        self.busy.store(false, Ordering::Release);
        result
    }
}

/// Called before normal Layout acquisition, never inferred from a decoded
/// plan. Complete-population Layout validation remains in prepare_units.
pub(crate) fn outputs(root: &std::path::Path) -> CargoResult<Option<Arc<OriginalOutputLeases>>> {
    let Some(original) = super::current().and_then(|startup| startup.candidate.clone()) else {
        return Ok(None);
    };
    original.check()?;
    anyhow::ensure!(
        root == startup::path(&original.originals.observation().plan.output_root),
        "candidate attempted a different output namespace"
    );
    original
        .outputs
        .validate(root)
        .context("candidate original output guards changed")?;
    Ok(Some(original.outputs.clone()))
}

/// Publication can be acknowledged only through the actual original parent
/// endpoint. Neither Fresh nor compiler exit status substitutes for it.
pub(crate) fn publish(
    selection: trust_resource_controller::workload::host::coordinator::PublicationSelection,
) -> CargoResult<trust_resource_controller::client::PublicationAcknowledgement> {
    let startup =
        super::current().context("private publication has no actual candidate startup")?;
    let original = startup
        .candidate
        .as_ref()
        .context("private publication has no original parent capsule")?;
    Ok(original.publish(selection)?)
}
