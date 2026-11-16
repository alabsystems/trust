//! FD-only continuation from the parent's actual selected, live unit attempt.
//! This retains no producer capture/ledger and cannot create a writer or GO.
use super::*;
use std::io;

pub(crate) struct CompilerInputLease {
    startup: Arc<Startup>,
    command: CommandSpec,
    coordinator: [u8; 16],
    directory: Arc<UnitDirectories>,
    dependencies: DependencyLease,
    source: Arc<AdmittedPackageSource>,
    poisoned: Arc<AtomicBool>,
    layout: Arc<OriginalOutputLeases>,
    selected: Arc<HeldOutputRoot>,
    master: Arc<OriginalInputs>,
    deadline: Instant,
}
impl PendingUnit {
    /// Only this SAME live ledger attempt can issue the native FD capsule.
    /// The second CPU original and Host admission remain independent owners.
    pub(crate) fn compiler_inputs(
        &self,
        startup: &Arc<Startup>,
        coordinator: [u8; 16],
        deadline: Instant,
    ) -> io::Result<Arc<CompilerInputLease>> {
        let result = (|| -> CargoResult<_> {
            ensure!(
                Arc::ptr_eq(&self.startup, startup)
                    && self.coordinator_attempt == coordinator
                    && !self.settled
                    && !self.poisoned.load(Ordering::Acquire)
                    && self
                        .active
                        .lock()
                        .map_err(|_| anyhow::anyhow!("pending compiler attempt state poisoned"))?
                        .contains(&self.key),
                "compiler inputs require SAME live pending unit/Root/coordinator"
            );
            ensure!(
                !self.compiler_inputs_issued.swap(true, Ordering::AcqRel),
                "pending compiler inputs were already issued; no retry/replayed producer"
            );
            let original = Arc::new(CompilerInputLease {
                startup: self.startup.clone(),
                command: self.command.clone(),
                coordinator,
                directory: self.directory.clone(),
                dependencies: self.dependencies.clone(),
                source: self.source.clone(),
                poisoned: self.poisoned.clone(),
                layout: self._layout.clone(),
                selected: self._selected.clone(),
                master: self._master.clone(),
                deadline: deadline.min(self.deadline),
            });
            original.validate(deadline)?;
            Ok(original)
        })();
        if result.is_err() {
            self.poisoned.store(true, Ordering::Release);
        }
        result.map_err(io::Error::other)
    }
}
impl CompilerInputLease {
    fn poison(&self) {
        self.poisoned.store(true, Ordering::Release);
        if let Some(process) = &self.startup.workload_process {
            process.poisoned.store(true, Ordering::Release);
        }
    }
    /// Current originals and namespace bookends only, never compiler success,
    /// output inventory/validity, SDK readiness, or formal verification.
    pub(crate) fn validate(&self, deadline: Instant) -> io::Result<()> {
        let result = (|| -> CargoResult<()> {
            let deadline = deadline.min(self.deadline);
            ensure!(
                !self.poisoned.load(Ordering::Acquire)
                    && self.startup.original_root
                    && self.startup.candidate.is_none()
                    && Instant::now() < deadline,
                "original compiler inputs are poisoned, foreign or expired"
            );
            self.master.validate()?;
            self.selected.validate(deadline)?;
            self.layout.validate(self.selected.path())?;
            self.source.validate(deadline)?;
            self.directory.validate(&self.selected, deadline)?;
            self.dependencies.validate(deadline)?;
            let process = self
                .startup
                .workload_process
                .as_ref()
                .context("compiler inputs lost their original SDK")?;
            ensure!(
                !process.cancelled.load(Ordering::Acquire)
                    && !process.poisoned.load(Ordering::Acquire),
                "original compiler workload stopped or lost an input"
            );
            process.sysroot.validate(deadline.min(process.deadline))?;
            ensure!(
                Instant::now() < deadline,
                "compiler input postcheck deadline expired"
            );
            Ok(())
        })();
        if result.is_err() {
            self.poison();
        }
        result.map_err(io::Error::other)
    }
    pub(crate) fn require_command(
        &self,
        startup: &Arc<Startup>,
        coordinator: [u8; 16],
        command: &CommandSpec,
        deadline: Instant,
    ) -> io::Result<()> {
        self.require_factory(startup, coordinator, deadline)?;
        if command != &self.command {
            self.poison();
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "compiler command/Root/coordinator differs from SAME pending unit",
            ));
        }
        self.validate(deadline)
    }
    pub(crate) fn require_factory(
        &self,
        startup: &Arc<Startup>,
        coordinator: [u8; 16],
        deadline: Instant,
    ) -> io::Result<()> {
        if !Arc::ptr_eq(startup, &self.startup) || coordinator != self.coordinator {
            self.poison();
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "compiler inputs belong to another actual Root/coordinator",
            ));
        }
        self.validate(deadline)
    }
    pub(crate) fn output_directory(&self) -> &Arc<AdmittedRootDirectory> {
        &self.directory.root
    }
    pub(crate) fn dependencies(&self) -> &DependencyLease {
        &self.dependencies
    }
    pub(crate) fn retained_bytes(&self) -> Option<usize> {
        std::mem::size_of::<Self>()
            .checked_add(self.command.retained_bytes()?)?
            .checked_add(
                self.dependencies
                    .files
                    .capacity()
                    .checked_mul(std::mem::size_of::<DependencyFile>())?,
            )?
            .checked_add(
                self.dependencies
                    ._readers
                    .capacity()
                    .checked_mul(std::mem::size_of::<Reader>())?,
            )
    }
}
