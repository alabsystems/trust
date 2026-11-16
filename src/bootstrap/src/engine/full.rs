//! Trust: the normal Step graph borrows the SAME actual advanced Root. No
//! standalone continuation, second lease/scope or status-built owner exists.
use std::io;
use std::process::{Command, Output};
use std::sync::{OnceLock, Weak};

use super::*;

mod command;
pub use command::OriginalCommand;
mod completed;
pub(crate) use completed::{CompletedCommand, CompletedReader};

/// The maintained Targo command parser/library supplies regular command I/O.
/// It must retain this SAME actual original Full owner; no callback or returned
/// Output can issue a member, an artifact, a GNU credit or native retirement.
/// Every command must still use its own actual native/queue execution issuer.
pub trait OriginalCommandExecutor: Send + Sync {
    fn original(&self) -> &Arc<OriginalBootstrapCompilation>;
    fn output(
        &self,
        command: &OriginalCommand<'_>,
        stdout: bool,
        stderr: bool,
    ) -> io::Result<Output>;
}

// Permanent restriction only. A weak reference cannot keep a closed engine
// alive, and absent/expired dispatch never restores SDK queries or local spawn.
static COMMANDS: OnceLock<Weak<dyn OriginalCommandExecutor>> = OnceLock::new();

pub(crate) fn command_output(
    graph: &crate::utils::metadata_scheduler::host_graph::OriginalHostGraph,
    command: &Command,
    inputs: crate::utils::exec::OriginalCommandInputs,
    stdout: bool,
    stderr: bool,
) -> io::Result<Output> {
    command_completed(graph, command, inputs, stdout, stderr).map(CompletedCommand::into_output)
}

/// A regular library command completes synchronously under its SAME actual
/// producer. Readers retain that owner; no Child or native retirement is made
/// from the returned status or output bytes.
pub(crate) fn command_completed(
    graph: &crate::utils::metadata_scheduler::host_graph::OriginalHostGraph,
    command: &Command,
    inputs: crate::utils::exec::OriginalCommandInputs,
    stdout: bool,
    stderr: bool,
) -> io::Result<CompletedCommand> {
    let executor = COMMANDS.get().and_then(Weak::upgrade).ok_or_else(|| {
        io::Error::other("original Full command execution owner is absent or closed")
    })?;
    if !executor.original().same_graph(graph) {
        return Err(io::Error::other(
            "Full command execution belongs to a different original graph",
        ));
    }
    executor.original().check_current()?;
    let projection = OriginalCommand::capture(command, inputs)?;
    let result = executor.output(&projection, stdout, stderr);
    // A successful command result never outruns its actual producer guards.
    executor.original().check_current()?;
    result.map(|output| CompletedCommand::new(Arc::clone(executor.original()), output))
}

/// Failed configuration/execution retains the actual original source/output,
/// native enrollment and complete Root lifetime. It grants no release/SDK.
#[must_use]
pub struct OriginalCompilationFailure {
    error: String,
    _owner: Arc<OriginalBootstrapCompilation>,
    _executor: Arc<dyn OriginalCommandExecutor>,
}
impl std::fmt::Debug for OriginalCompilationFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OriginalCompilationFailure").field("error", &self.error).finish()
    }
}
impl std::fmt::Display for OriginalCompilationFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}
impl std::error::Error for OriginalCompilationFailure {}
impl OriginalCompilationFailure {
    /// Recover the SAME actual owner, including its failed native/source
    /// state. This does not clear failure or grant a successful completion.
    pub fn into_owner(self) -> Arc<OriginalBootstrapCompilation> {
        self._owner
    }
}

/// Execute the maintained Session/Step body while retaining the actual Full
/// owner. The managed command executor must already be installed by the same
/// original Targo entry. Unsupported commands still refuse through that owner;
/// paths, returned statuses and this result cannot supply an execution issuer.
/// The caller must finish the SAME owner after all actual native/local work.
pub fn run_original_compilation(
    owner: Arc<OriginalBootstrapCompilation>,
    bootstrap_shims: PathBuf,
    executor: Arc<dyn OriginalCommandExecutor>,
) -> Result<Arc<OriginalBootstrapCompilation>, OriginalCompilationFailure> {
    let result = (|| -> Result<(), String> {
        owner.check_current().map_err(|error| error.to_string())?;
        if !Arc::ptr_eq(&owner, executor.original()) {
            return Err(
                "Full command executor belongs to different actual original producers".into()
            );
        }
        COMMANDS
            .set(Arc::downgrade(&executor))
            .map_err(|_| "original Full command executor is already installed".to_owned())?;
        owner.install_execution_scope().map_err(|error| error.to_string())?;
        let shims = selected_shims(&bootstrap_shims)?;
        let configured = owner.configure().map_err(|error| error.to_string())?;
        owner
            .scoped_work(|| {
                let mut session =
                    crate::core::session::Session::new_with_original(configured, shims)
                        .map_err(std::io::Error::other)?;
                crate::cli_main::run_session_steps(
                    &mut session,
                    crate::cli_main::StepOwners::Original(&owner),
                )
                .map_err(std::io::Error::other)
            })
            .map_err(|error| error.to_string())?;
        owner.check_current().map_err(|error| error.to_string())
    })();
    match result {
        Ok(()) => Ok(owner),
        Err(error) => Err(OriginalCompilationFailure { error, _owner: owner, _executor: executor }),
    }
}
