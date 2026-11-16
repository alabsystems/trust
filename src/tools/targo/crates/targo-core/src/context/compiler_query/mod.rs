//! One synchronous compiler-query borrower, independent of the build pool.
//! Zero extra GNU credits expose the parent's existing implicit execution only.
use super::GLOBAL_JOBSERVER;
use crate::util::CargoResult;
use cargo_util::{EnvironmentInputs, Jobserver, ProcessBuilder, ProcessError, ProcessExecutor};
use std::process::Output;
use std::sync::{Arc, Mutex};

/// Scoped execution selected by the actual parent of a prepared coordinator.
/// Environment bytes are data. The executor must retain that parent's real
/// coordinator and allocate each query's distinct original second unit. This
/// never installs a global executor or creates a scheduler/CPU pool.
#[derive(Clone)]
pub(crate) struct Scoped {
    environment: EnvironmentInputs,
    cwd: std::path::PathBuf,
    scheduler: Jobserver,
    executor: Arc<dyn ProcessExecutor>,
    // Exact per-query environment DATA from an actual native issued projection.
    // Selection grants no execution or completion; the executor checks it.
    issued: Vec<(
        std::ffi::OsString,
        Vec<std::ffi::OsString>,
        EnvironmentInputs,
    )>,
    preserve_explicit: bool,
}
impl std::fmt::Debug for Scoped {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ScopedNativeCompilerQueries")
            .finish_non_exhaustive()
    }
}
impl Scoped {
    pub(super) fn new(
        environment: EnvironmentInputs,
        scheduler: Jobserver,
        executor: Arc<dyn ProcessExecutor>,
        cwd: std::path::PathBuf,
    ) -> Self {
        Self {
            environment,
            scheduler,
            executor,
            cwd,
            issued: Vec::new(),
            preserve_explicit: false,
        }
    }
    pub(crate) fn with_issued_environments(
        mut self,
        issued: Vec<(
            std::ffi::OsString,
            Vec<std::ffi::OsString>,
            EnvironmentInputs,
        )>,
    ) -> Self {
        self.issued = issued;
        self.preserve_explicit = true;
        self
    }
    /// Restriction only: fresh requests still execute through the actual
    /// owner's executor, without normalizing explicit foreign selections.
    pub(crate) fn preserve_explicit_inputs(mut self) -> Self {
        self.preserve_explicit = true;
        self
    }
    pub(super) fn with_directory(mut self, cwd: std::path::PathBuf) -> Self {
        self.cwd = cwd;
        self
    }
    pub(crate) fn configure(&self, command: &mut ProcessBuilder) {
        let environment = self
            .issued
            .iter()
            .find(|(program, args, _)| {
                command.get_program() == program && command.get_args().eq(args.iter())
            })
            .map(|(_, _, environment)| environment)
            .unwrap_or(&self.environment);
        if !self.preserve_explicit || !command.has_environment_snapshot() {
            command.environment_snapshot(environment.clone());
        }
        // Retained and fresh original-owner requests preserve selections for
        // their actual executor to judge; ordinary coordinators stay unchanged.
        if !self.preserve_explicit || command.get_cwd().is_none() {
            command.cwd(&self.cwd);
        }
        if !self.preserve_explicit || !command.has_jobserver() {
            command.inherit_jobserver(&self.scheduler);
        }
        command.process_executor(self.executor.clone());
    }
}

// One process-wide owner also covers multiple Rustc/GlobalContext objects.
// Normal compilation units never enter this owner or inherit its empty pool.
struct QueryOwner(Mutex<Option<Jobserver>>);
static QUERY: QueryOwner = QueryOwner(Mutex::new(None));
pub(crate) const TRANSPORT_POLICY: &str = "owned-compiler-query-complete-native-environment-v2";

pub(crate) fn output(command: &ProcessBuilder) -> CargoResult<Output> {
    // Resolve the original early checked capture before creating any fallback.
    let inherited = GLOBAL_JOBSERVER
        .as_ref()
        .map_err(|error| anyhow::anyhow!("{error}"))?;
    QUERY.output(command, inherited.as_ref())
}

impl QueryOwner {
    fn output(
        &self,
        command: &ProcessBuilder,
        inherited: Option<&Jobserver>,
    ) -> CargoResult<Output> {
        let mut owner = self
            .0
            .lock()
            .map_err(|_| anyhow::anyhow!("poisoned compiler-query borrower"))?;
        let mut command = command.clone();
        if !command.has_jobserver() {
            if let Some(inherited) = inherited {
                command.inherit_jobserver(inherited);
            } else {
                if owner.is_none() {
                    let mut server = Jobserver::new(0)?;
                    server.enable_descendant_handoff()?;
                    *owner = Some(server);
                }
                command.inherit_jobserver(owner.as_ref().expect("query scheduler retained"));
            }
        }
        // The exclusive guard and retained scheduler outlive terminal custody.
        command.output_owned()
    }
}

pub(crate) fn exec(command: &ProcessBuilder) -> CargoResult<Output> {
    let output = output(command)?;
    if output.status.success() {
        Ok(output)
    } else {
        Err(ProcessError::new(
            &format!("process didn't exit successfully: {command}"),
            Some(output.status),
            Some(&output),
        )
        .into())
    }
}

#[cfg(all(test, unix))]
mod tests;
