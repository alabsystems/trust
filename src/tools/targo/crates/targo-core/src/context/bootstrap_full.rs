//! Trust: the SAME original input session advances into the maintained engine.
//! Neither a phase observation nor configuration DATA constructs this owner.
use bootstrap::engine::OriginalBootstrapCompilation;
use cargo_util::{
    EnvironmentInputs, ExecStats, Jobserver, ProcessBuilder, ProcessExecutor, StreamingOutputLimits,
};
use std::io;
use std::path::PathBuf;
use std::process::ExitStatus;
use std::process::Output;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Weak};
use std::time::{Duration, Instant};

pub(super) struct AdvanceFailure {
    pub(super) _owner: Arc<BootstrapFull>,
}
impl std::fmt::Debug for AdvanceFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RefusedFullAdvance").finish_non_exhaustive()
    }
}
impl std::fmt::Display for AdvanceFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("the original input executor already has a Full continuation")
    }
}
impl std::error::Error for AdvanceFailure {}

/// Constructed only by consuming actual finished input work and the original
/// Bootstrap source/output owner through the native Advance exchange. The
/// existing mandatory executor keeps a weak reference, so closing this owner
/// permanently refuses later helpers rather than restoring local execution.
#[must_use]
pub struct BootstrapFull {
    pub(super) original_self: Weak<Self>,
    pub(super) owner: Arc<OriginalBootstrapCompilation>,
    pub(super) scheduler: Jobserver,
    pub(super) implicit_borrowed: AtomicBool,
    pub(super) cargo_home: PathBuf,
    pub(super) environment: EnvironmentInputs,
    pub(super) sequence: AtomicU64,
    pub(super) delivery: Mutex<()>,
}
impl std::fmt::Debug for BootstrapFull {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OriginalBootstrapFull")
            .finish_non_exhaustive()
    }
}

mod queue;
pub(crate) use queue::QueuePermit;
mod executor;
pub(crate) use executor::QueuedExecutor;
impl BootstrapFull {
    pub fn original(&self) -> &Arc<OriginalBootstrapCompilation> {
        &self.owner
    }
    pub fn check_current(&self) -> io::Result<()> {
        self.owner.check_current()?;
        super::dependency_inputs::same_scheduler(&self.scheduler, &self.owner.data().gnu)
    }
    /// Parse regular Cargo configuration under the SAME original protected
    /// source and native cache owner. Environment and program spellings are
    /// selection DATA only; this actual Full owner remains in the context.
    pub fn context(
        self: &Arc<Self>,
        shell: cargo_util_terminal::Shell,
        environment: EnvironmentInputs,
    ) -> crate::CargoResult<super::GlobalContext> {
        self.check_current()?;
        for name in [
            "BUILD_SLOT_HELD",
            "TRUST_BUILD_LOCK_TOKEN",
            "TRUST_CPU_HANDOFF",
            "TRUST_CPU_IMPLICIT_FD",
            jobserver_utils::FIXED_CLAIM_HANDOFF_ENV,
            trust_build_tree::admission::FIXED_HANDOFF_ENV,
        ] {
            anyhow::ensure!(
                !environment
                    .iter()
                    .any(|(key, _)| key == std::ffi::OsStr::new(name)),
                "original Full context cannot reimport {name}"
            );
        }
        anyhow::ensure!(
            environment.iter().any(|(key, value)| {
                key == std::ffi::OsStr::new("CARGO_HOME") && value == self.cargo_home.as_os_str()
            }),
            "Full context changed its actual admission-owned Cargo home"
        );
        let source = self.owner.original_source()?.path().to_owned();
        let program = self.owner.control_targo()?;
        let mut context = super::GlobalContext::for_coordinator_queries(
            shell,
            source,
            self.cargo_home.clone(),
            program,
            environment,
            self.scheduler.clone(),
            self.clone(),
        )?;
        // These are NEW compiler requests under this Full owner's actual
        // execution loan. Input-phase captured answers cannot describe the
        // control Targo/CARGO environment or later metadata queries.
        context.coordinator_queries = context
            .coordinator_queries
            .take()
            .map(|scope| scope.preserve_explicit_inputs());
        context.bootstrap_full = Some(Arc::clone(self));
        self.check_current()?;
        Ok(context)
    }
    pub fn environment(&self) -> &EnvironmentInputs {
        &self.environment
    }
    /// Equality with the actual consuming transition's context, never a
    /// constructor from a directory, environment or observed native key.
    pub fn owns_context(self: &Arc<Self>, context: &super::GlobalContext) -> bool {
        context
            .bootstrap_full
            .as_ref()
            .is_some_and(|actual| Arc::ptr_eq(actual, self))
    }
    /// Apply the canonical parser's directory selection only to its context.
    /// The original source/cache/GNU owners remain held and independently judge
    /// every native command; the process cwd and environment are unchanged.
    pub fn reload_context_directory(
        self: &Arc<Self>,
        context: &mut super::GlobalContext,
        selected: &std::path::Path,
    ) -> crate::CargoResult<()> {
        self.check_current()?;
        anyhow::ensure!(
            self.owns_context(context),
            "Full directory belongs to another context"
        );
        let selected = if selected.is_absolute() {
            selected.to_owned()
        } else {
            context.cwd().join(selected)
        };
        context.reload_directory(selected)?;
        self.check_current()?;
        Ok(())
    }
    pub(crate) fn ceiling(&self) -> io::Result<u32> {
        self.owner.cpu_ceiling().map(std::num::NonZeroU32::get)
    }
    pub(super) fn compiler_output(&self, command: &ProcessBuilder) -> io::Result<Output> {
        let original = self.original_self.upgrade().ok_or_else(|| {
            io::Error::other("original Full compiler-query execution owner is closed")
        })?;
        let permit = original.try_implicit()?.ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::WouldBlock,
                "Full metadata query cannot borrow an already queued implicit execution",
            )
        })?;
        // The ordinary member executor retains this SAME actual loan through
        // physical output and opaque native owning retirement, including errors.
        QueuedExecutor::for_query(permit).output(command)
    }
    pub(crate) fn observation_deadline(&self) -> io::Result<Instant> {
        let now = Instant::now();
        if now >= self.owner.original_deadline() {
            return Err(io::ErrorKind::TimedOut.into());
        }
        Ok(now
            .checked_add(Duration::from_secs(8))
            .ok_or_else(|| io::Error::other("Full observation deadline overflow"))?
            .min(self.owner.original_deadline()))
    }
}

impl super::GlobalContext {
    pub(crate) fn original_bootstrap_full(&self) -> Option<&Arc<BootstrapFull>> {
        self.bootstrap_full.as_ref()
    }
}

impl ProcessExecutor for BootstrapFull {
    fn output(&self, command: &ProcessBuilder) -> io::Result<Output> {
        self.compiler_output(command)
    }
    fn status(&self, _: &ProcessBuilder) -> io::Result<ExitStatus> {
        Err(io::Error::other(
            "Full commands require an actual queued native execution owner",
        ))
    }
    fn streaming(
        &self,
        _: &ProcessBuilder,
        _: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        _: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        _: bool,
        _: Option<StreamingOutputLimits>,
        _: bool,
    ) -> (ExecStats, anyhow::Result<Output>) {
        (
            ExecStats::default(),
            Err(anyhow::anyhow!(
                "Full commands require an actual queued native execution owner"
            )),
        )
    }
}
