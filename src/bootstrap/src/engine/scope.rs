//! Original command custody for the embedded graph. No data constructor or
//! Host/release conversion exists. Only Preparation can mint ExecutionScope.

use std::marker::PhantomData;
use std::sync::Arc;
use std::time::Instant;

#[cfg(any(target_os = "macos", target_os = "linux"))]
use build_helper::trust_repo_lock::management::{
    LocalJoinedScope, OriginalSourceRoot, ProtectedWorkScope,
};

use super::{CompletedRuntime, Plan};
#[cfg(any(target_os = "macos", target_os = "linux"))]
use crate::core::build_steps::frontend_runtime::{BuildOwnership, CommandOwnership};

#[cfg(any(target_os = "macos", target_os = "linux"))]
type CommandOwner = Arc<CommandOwnership>;
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
type CommandOwner = Arc<()>;

/// A transient borrow of this invocation's actual acquired command owner.
/// It cannot be cloned or constructed from Plan, tokens, paths or observations.
pub struct Preparation<'a> {
    plan: Plan,
    command: Option<&'a CommandOwner>,
    _lifetime: PhantomData<&'a ()>,
}

impl<'a> Preparation<'a> {
    pub fn plan(&self) -> &Plan {
        &self.plan
    }

    pub(crate) fn new(plan: Plan, command: Option<&'a CommandOwner>) -> Self {
        Self { plan, command, _lifetime: PhantomData }
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(super) fn bind_original_host(
        self,
        graph: Arc<super::OriginalHostGraph>,
        before_steps: impl FnOnce(Preparation<'a>) -> Result<ExecutionScope, String>,
    ) -> Result<ExecutionScope, String> {
        // Preserve the actual invocation's original Arc across the consuming
        // callback, so a foreign prepared scope refuses BEFORE enrollment.
        let actual = self.command.cloned();
        let mut scope = before_steps(self)?;
        scope.check_original_command(actual.as_ref())?;
        scope.enroll_original_host(graph)?;
        Ok(scope)
    }

    /// Consume only this actual owned lease into durable exclusion and bind
    /// one protected scope to the SAME guard. This grants no Host admission,
    /// SDK, GNU credits, child launch or release authority.
    pub fn protect(self, original_deadline: Instant) -> Result<ExecutionScope, String> {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            if Instant::now() >= original_deadline {
                return Err("protected work deadline already expired".into());
            }
            let command = self.command.ok_or("protected work needs the actual command owner")?;
            command.check_original_source(&self.plan.source)?;
            if Instant::now() >= original_deadline {
                return Err("original source binding crossed the protected work deadline".into());
            }
            let original = command.withhold_original()?;
            let scope = ProtectedWorkScope::new(original, original_deadline)
                .map_err(|error| error.to_string())?;
            let source_root = Arc::new(
                scope.original_source(&self.plan.source).map_err(|error| error.to_string())?,
            );
            Ok(ExecutionScope {
                scope: Some(scope),
                source_root: Some(source_root),
                command: Some(Arc::clone(command)),
                ownership: None,
                completed: None,
                #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
                source: self.plan.source,
                #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
                output: self.plan.output,
                #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
                host_graph: None,
                _private: (),
            })
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            let _ = original_deadline;
            Err("protected work ownership is unsupported on this platform".into())
        }
    }
}

/// Nonconstructible original scope, minted only by consuming Preparation.
/// No returned foreign scope or generic completion boolean can supply it.
#[must_use]
pub struct ExecutionScope {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    scope: Option<ProtectedWorkScope>,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    source_root: Option<Arc<OriginalSourceRoot>>,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    command: Option<CommandOwner>,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    ownership: Option<Arc<BuildOwnership>>,
    completed: Option<Arc<CompletedRuntime>>,
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    source: std::path::PathBuf,
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    output: std::path::PathBuf,
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    host_graph: Option<Arc<super::OriginalHostGraph>>,
    _private: (),
}

impl ExecutionScope {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn original_source_root(&self) -> Result<&Arc<OriginalSourceRoot>, String> {
        self.check_current()?;
        self.source_root.as_ref().ok_or_else(|| "original source custody is absent".into())
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn weak_dispatch(
        &self,
    ) -> Result<build_helper::trust_repo_lock::management::WeakScopeDispatch, String> {
        self.check_current()?;
        Ok(self.scope.as_ref().ok_or("original scope is absent")?.dispatcher().downgrade())
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(super) fn enroll_original_host(
        &mut self,
        graph: Arc<super::OriginalHostGraph>,
    ) -> Result<(), String> {
        if self.host_graph.is_some() {
            return Err("original Host graph is already bound".into());
        }
        // Retain the actual graph before any enrollment request can be exposed.
        self.host_graph = Some(Arc::clone(&graph));
        let result = graph.enroll(self, &self.source, &self.output);
        if let Err(error) = &result {
            if let Some(scope) = &self.scope {
                scope.dispatcher().record_failure(error);
            }
        }
        result
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn run_native_object(
        &self,
    ) -> Result<crate::utils::metadata_scheduler::host_graph::object::NativeObjectObservation, String>
    {
        self.check_current()?;
        let graph = self.host_graph.as_ref().ok_or("actual original Host graph absent")?;
        let result = graph.run_native_object_node().map_err(|error| error.to_string())?;
        self.check_current()?;
        Ok(result)
    }

    pub(super) fn native_graph_owner(&self) -> Result<NativeGraphOwner<'_>, String> {
        self.check_current()?;
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            let ownership = self.ownership.as_ref().ok_or("original output custody is absent")?;
            ownership.check()?;
            Ok(NativeGraphOwner {
                scope: self.scope.as_ref().ok_or("original scope is absent")?,
                ownership,
                source_root: self
                    .source_root
                    .as_ref()
                    .ok_or("original source custody is absent")?,
            })
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        Err("native graph custody is unsupported on this platform".into())
    }
    pub(crate) fn check_current(&self) -> Result<(), String> {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            self.scope
                .as_ref()
                .ok_or("protected scope was already consumed")?
                .check_current()
                .map_err(|error| error.to_string())?;
            self.source_root
                .as_ref()
                .ok_or("original source custody is absent")?
                .check_current()
                .map_err(|error| error.to_string())
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        Err("protected work ownership is unsupported on this platform".into())
    }

    pub(crate) fn install(&self, actual: Option<&CommandOwner>) -> Result<(), String> {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            self.check_original_command(actual)?;
            let scope = self.scope.as_ref().ok_or("protected work scope was already consumed")?;
            scope.check_current().map_err(|error| error.to_string())?;
            crate::utils::exec::install_protected_scope(scope.dispatcher())
                .map_err(|error| error.to_string())?;
            scope.check_current().map_err(|error| error.to_string())
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            let _ = actual;
            Err("protected work ownership is unsupported on this platform".into())
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn check_original_command(&self, actual: Option<&CommandOwner>) -> Result<(), String> {
        let actual = actual.ok_or("protected scope has no actual command owner")?;
        let original = self.command.as_ref().ok_or("protected command owner is absent")?;
        if !Arc::ptr_eq(actual, original) {
            return Err("protected scope belongs to another actual command owner".into());
        }
        self.check_current()
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    pub(crate) fn retain_build_ownership(
        &mut self,
        original: Arc<BuildOwnership>,
    ) -> Result<(), String> {
        assert!(self.ownership.is_none(), "cannot replace original build/output ownership");
        self.ownership = Some(original);
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if let Some(graph) = &self.host_graph {
            let result = (|| {
                self.check_current()?;
                let original =
                    self.ownership.as_ref().ok_or("original build ownership is absent")?;
                // SAFETY: this scope retained the actual same command/close-only
                // OutputLock owners before any offer, and the original pinned
                // Host stores close-only duplicates through native settlement.
                let descriptions = unsafe {
                    original.original_output(
                        self.command.as_ref().ok_or("original command owner is absent")?,
                        &self.output,
                    )
                }?;
                graph.attach_output(
                    &descriptions,
                    Arc::clone(original),
                    Arc::clone(self.command.as_ref().ok_or("original command owner is absent")?),
                )?;
                // SAFETY: same unchanged close-only recipient and owners; the
                // second borrow is a nonblocking ownership/identity bookend.
                unsafe {
                    original.original_output(
                        self.command.as_ref().ok_or("original command owner is absent")?,
                        &self.output,
                    )
                }?;
                self.check_current()
            })();
            if let Err(error) = &result {
                if let Some(scope) = &self.scope {
                    scope.dispatcher().record_failure(error);
                }
            }
            result?;
        }
        Ok(())
    }

    pub(crate) fn retain_completed(&mut self, completed: Option<Arc<CompletedRuntime>>) {
        assert!(self.completed.is_none(), "cannot replace original completed runtime");
        self.completed = completed;
    }

    pub(crate) fn seal_graph(mut self) -> Result<JoinedOutcome, UnresolvedOutcome> {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            let Some(scope) = self.scope.take() else {
                return Err(UnresolvedOutcome::retaining(
                    self,
                    "protected scope was already consumed".into(),
                    None,
                    None,
                ));
            };
            let joined = match scope.seal().join() {
                Ok(joined) => joined,
                Err(failure) => {
                    let error = failure.error().to_string();
                    return Err(UnresolvedOutcome::retaining(self, error, Some(failure), None));
                }
            };
            if let Err(error) = joined.check_current() {
                return Err(UnresolvedOutcome::retaining(
                    self,
                    error.to_string(),
                    None,
                    Some(joined),
                ));
            }
            Ok(JoinedOutcome {
                completed: self.completed.take(),
                protected: Some(CompletedScope {
                    joined,
                    _source_root: self.source_root.take(),
                    _command: self.command.take().expect("same original command owner"),
                    _ownership: self.ownership.take(),
                    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
                    _host_graph: self.host_graph.take(),
                    _private: (),
                }),
            })
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        Err(UnresolvedOutcome::absent())
    }
}

/// A private borrow, never an exported dispatcher or a replacement owner.
pub(super) struct NativeGraphOwner<'a> {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    scope: &'a ProtectedWorkScope,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    ownership: &'a Arc<BuildOwnership>,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    source_root: &'a Arc<OriginalSourceRoot>,
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    _lifetime: PhantomData<&'a ()>,
}

impl NativeGraphOwner<'_> {
    pub(super) fn check(&self) -> Result<(), String> {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            self.scope.check_current().map_err(|error| error.to_string())?;
            self.source_root.check_current().map_err(|error| error.to_string())?;
            self.ownership.check()
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        Err("native graph custody is unsupported on this platform".into())
    }
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    pub(super) fn source_root(&self) -> &Arc<OriginalSourceRoot> {
        self.source_root
    }
    // Trust: additional negative restriction on the original output owner;
    // observations never replace either guard or authorize source mutation.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    pub(super) fn source_directory_disjoint(
        &self,
        subtree: &std::path::Path,
        directory: (u64, u64),
    ) -> Result<(), String> {
        self.check()?;
        self.ownership.source_directory_disjoint(subtree, directory)
    }
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    pub(super) fn identity(&self) -> &build_helper::trust_repo_lock::management::ScopeIdentity {
        self.scope.identity()
    }
    #[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
    pub(super) fn same_original_directory(&self, file: &std::fs::File) -> std::io::Result<bool> {
        self.scope.same_original_directory(file)
    }
}

impl Drop for ExecutionScope {
    fn drop(&mut self) {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        if let Some(scope) = self.scope.take() {
            // Abandonment irrevocably invalidates every previously cloned
            // dispatcher BEFORE retaining any unresolved original inputs.
            drop(scope.seal());
        }
        // Failed/unknown scope closure cannot close the only original runtime
        // or output descriptions. Retain the actual owners until process death;
        // durable WITHHELD independently continues to prohibit ordinary release.
        if let Some(completed) = self.completed.take() {
            std::mem::forget(completed);
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if let Some(graph) = self.host_graph.take() {
            // Same accepted graph, query census and failure owners survive an
            // unresolved scope. A weak installed sentinel never restores spawn.
            std::mem::forget(graph);
        }
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            if let Some(source) = self.source_root.take() {
                std::mem::forget(source);
            }
            if let Some(owner) = self.ownership.take() {
                std::mem::forget(owner);
            }
            if let Some(command) = self.command.take() {
                std::mem::forget(command);
            }
        }
    }
}

/// Owns actual local joins and the SAME build/output/command guards. This is
/// deliberately private and supplies no Host closure or release operation.
struct CompletedScope {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    joined: LocalJoinedScope,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    _source_root: Option<Arc<OriginalSourceRoot>>,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    _command: CommandOwner,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    _ownership: Option<Arc<BuildOwnership>>,
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    _host_graph: Option<Arc<super::OriginalHostGraph>>,
    _private: (),
}

impl CompletedScope {
    fn check_current(&self) -> Result<(), String> {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            self.joined.check_current().map_err(|error| error.to_string())
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        Err("protected work ownership is unsupported on this platform".into())
    }
}

/// Actual local closure with the SAME runtime/build inputs still retained.
/// It is not original Host/member/loan closure and has no release operation.
#[must_use]
pub struct JoinedOutcome {
    completed: Option<Arc<CompletedRuntime>>,
    protected: Option<CompletedScope>,
}

impl JoinedOutcome {
    pub fn has_completed_runtime(&self) -> bool {
        self.completed.is_some()
    }

    pub fn check_work_scope(&self) -> Result<(), String> {
        self.protected.as_ref().ok_or("joined original scope is absent")?.check_current()
    }
}

impl Drop for JoinedOutcome {
    fn drop(&mut self) {
        // Local joins alone cannot close input/output custody while genuine
        // Host member/loan/foreign closure is still unavailable.
        if let Some(completed) = self.completed.take() {
            std::mem::forget(completed);
        }
        if let Some(protected) = self.protected.take() {
            std::mem::forget(protected);
        }
    }
}

/// Failure retains the actual unresolved owners; its diagnostic is data only.
#[must_use]
pub struct UnresolvedOutcome {
    error: String,
    _scope: Option<ExecutionScope>,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    _failure: Option<build_helper::trust_repo_lock::management::ScopeFailure>,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    _joined: Option<LocalJoinedScope>,
}

impl UnresolvedOutcome {
    pub fn error(&self) -> &str {
        &self.error
    }

    pub(super) fn absent() -> Self {
        Self {
            error: "this invocation has no original protected scope".into(),
            _scope: None,
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            _failure: None,
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            _joined: None,
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn retaining(
        scope: ExecutionScope,
        error: String,
        failure: Option<build_helper::trust_repo_lock::management::ScopeFailure>,
        joined: Option<LocalJoinedScope>,
    ) -> Self {
        Self { error, _scope: Some(scope), _failure: failure, _joined: joined }
    }
}

impl std::fmt::Debug for UnresolvedOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("UnresolvedOutcome").field(&self.error).finish()
    }
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
mod tests;
