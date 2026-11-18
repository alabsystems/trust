//! Trust: original completed native runtime ownership for frontend iteration.
//!
//! Only this Step constructs `CompletedRuntime`, after normal compiler, std,
//! docs, Targo, frontend, daemon and AY Steps return successfully. No record,
//! directory name, version response or digest constructs completion. The owner
//! retains the SAME original build/output guards and read-only runtime inputs.
//! This is not a published SDK, a resource grant, ABI compatibility, or proof.
//! Cross-origin frontend execution is deliberately unavailable until its live
//! authenticated consumer is implemented; ordinary identity gates are unchanged.

use std::sync::Arc;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use crate::core::build_steps::repo;
use crate::core::build_steps::tool;
use crate::core::builder::{Builder, CommandLineStep, Kind, RunConfig, ShouldRun};
use crate::core::config::{Config, TargetSelection};
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use crate::utils::{exec::ExecutionContext, trust_source_identity};

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) struct BuildOwnership {
    // Keep the actual guards, not re-opened lock names or recreated holders.
    output: Arc<build_helper::trust_output_lock::OutputLock>,
    command: Arc<CommandOwnership>,
}

/// One actual acquired/borrowed native guard, shared through this container.
/// A future consuming handoff can move that value exactly once; Arc clones
/// never create another guard or reconstruct one from a record or token.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) struct CommandOwnership {
    lease: std::sync::Mutex<CommandState>,
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
enum CommandState {
    Original(build_helper::trust_repo_lock::management::Lease),
    Withheld {
        lease: Arc<build_helper::trust_repo_lock::management::WithheldLease>,
        #[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
        retention: Option<RetentionBinding>,
        #[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
        offered: bool,
    },
    Failed(build_helper::trust_repo_lock::management::WithholdFailure),
    Unresolved,
}

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
struct RetentionBinding {
    context: trust_resource_controller::Context,
    binding: trust_resource_controller::JobBinding,
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
impl CommandOwnership {
    pub(crate) fn new(original: build_helper::trust_repo_lock::management::Lease) -> Self {
        Self { lease: std::sync::Mutex::new(CommandState::Original(original)) }
    }

    // Trust: check the actual still-unused source owner BEFORE withholding.
    // A mismatched Plan must not change or replace the original owned lease.
    pub(crate) fn check_original_source(&self, source: &std::path::Path) -> Result<(), String> {
        let original =
            self.lease.try_lock().map_err(|_| "native command ownership is busy or poisoned")?;
        let CommandState::Original(lease) = &*original else {
            return Err("source binding requires the unused original manager lease".into());
        };
        if lease.is_borrowed() {
            return Err("source binding cannot promote borrowed manager custody".into());
        }
        lease.check_root(source).map_err(|error| error.to_string())
    }

    /// Consume the actual owned original once into durable exclusion only.
    /// The engine still needs its real resource/Host Preparation before work;
    /// this value alone cannot dispatch, send runtime inputs or release.
    pub(crate) fn withhold_original(
        &self,
    ) -> Result<Arc<build_helper::trust_repo_lock::management::WithheldLease>, String> {
        let mut original = self.lease.lock().map_err(|_| "native command ownership is poisoned")?;
        Self::withhold_original_locked(&mut original)
    }

    fn withhold_original_locked(
        original: &mut CommandState,
    ) -> Result<Arc<build_helper::trust_repo_lock::management::WithheldLease>, String> {
        match original {
            CommandState::Original(lease) if !lease.is_borrowed() => {
                lease.check_current().map_err(|e| e.to_string())?;
            }
            _ => return Err("withholding requires the unused original owned manager lease".into()),
        }
        let CommandState::Original(lease) = std::mem::replace(original, CommandState::Unresolved)
        else {
            unreachable!()
        };
        // The primitive disables ordinary release BEFORE fallible publication.
        // Keep every actual failed transition, even after poisoning/unwind.
        match lease.into_withheld() {
            Ok(lease) => {
                let lease = Arc::new(lease);
                *original = CommandState::Withheld {
                    lease: Arc::clone(&lease),
                    #[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
                    retention: None,
                    #[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
                    offered: false,
                };
                Ok(lease)
            }
            Err(failed) => {
                let error = failed.to_string();
                *original = CommandState::Failed(failed);
                Err(error)
            }
        }
    }

    fn check(&self) -> Result<(), String> {
        let original = self.lease.lock().map_err(|_| "native command ownership is poisoned")?;
        match &*original {
            CommandState::Original(lease) => lease.check_current().map_err(|e| e.to_string()),
            CommandState::Withheld { lease, .. } => {
                lease.check_current().map_err(|e| e.to_string())
            }
            CommandState::Failed(failure) => Err(format!(
                "native command withholding failed; original custody retained: {failure}"
            )),
            CommandState::Unresolved => {
                Err("native command ownership transition is unresolved".into())
            }
        }
    }

    /// Run local cleanup only under the same still-original command lease.
    /// Keep the state mutex through the operation: withheld execution may
    /// still have consumers, even when its retained holder is unchanged.
    pub(crate) fn with_pruning_lease<T>(
        &self,
        root: &std::path::Path,
        prune: impl FnOnce() -> Result<T, String>,
    ) -> Result<T, String> {
        let original = self.lease.lock().map_err(|_| "native command ownership is poisoned")?;
        let CommandState::Original(lease) = &*original else {
            return Err("pruning requires the original unwithheld command lease".into());
        };
        lease.check_root(root).map_err(|error| error.to_string())?;
        let result = prune()?;
        lease.check_root(root).map_err(|error| error.to_string())?;
        Ok(result)
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
impl BuildOwnership {
    /// # Safety
    /// Only the same original protected graph may offer these actual acquired
    /// descriptions. The recipient must be close-only and retain them through
    /// genuine native settlement; no DATA/ACK may release the original guard.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) unsafe fn original_output(
        &self,
        command: &Arc<CommandOwnership>,
        output: &std::path::Path,
    ) -> Result<build_helper::trust_output_lock::OriginalOutputDescriptions<'_>, String> {
        if !Arc::ptr_eq(&self.command, command) {
            return Err("output belongs to another original protected command".into());
        }
        self.output.check_current().map_err(|error| error.to_string())?;
        {
            let state = self
                .command
                .lease
                .try_lock()
                .map_err(|_| "original command ownership is busy or poisoned")?;
            let CommandState::Withheld { lease, .. } = &*state else {
                return Err("graph output requires its original durably withheld command".into());
            };
            lease.check_current().map_err(|error| error.to_string())?;
        }
        self.output.check_root(output).map_err(|error| error.to_string())?;
        // SAFETY: caller upholds the same original close-only graph contract.
        unsafe { self.output.original_descriptions() }.map_err(|error| error.to_string())
    }

    pub(crate) fn new(
        output: Arc<build_helper::trust_output_lock::OutputLock>,
        command: Arc<CommandOwnership>,
    ) -> Result<Self, String> {
        let original = Self { output, command };
        original.check()?;
        Ok(original)
    }

    pub(crate) fn check(&self) -> Result<(), String> {
        self.output.check_current().map_err(|error| error.to_string())?;
        self.command.check()
    }

    // Trust: consuming split of the SAME real guards after native input close
    // and local join. The caller retains output exclusion through exact source
    // retirement while the actual original command lease moves via its joined
    // source/offer owner; no pathname or status constructs either guard.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn into_resident_output(
        self,
    ) -> (Arc<build_helper::trust_output_lock::OutputLock>, Arc<CommandOwnership>) {
        (self.output, self.command)
    }

    // Trust: a negative source/output restriction observed from the SAME held
    // output guard. Neither these path/inode observations nor success here
    // constructs an output, source, SDK or completion owner.
    pub(crate) fn source_directory_disjoint(
        &self,
        subtree: &std::path::Path,
        directory: (u64, u64),
    ) -> Result<(), String> {
        use std::os::fd::AsRawFd as _;
        self.check()?;
        let output = self.output.original_root().map_err(|error| error.to_string())?;
        let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: observes the actual still-held output directory, not a reopen.
        if unsafe {
            libc::fstat(
                self.output.original_directory().map_err(|error| error.to_string())?.as_raw_fd(),
                stat.as_mut_ptr(),
            )
        } != 0
        {
            return Err(std::io::Error::last_os_error().to_string());
        }
        let stat = unsafe { stat.assume_init() };
        #[allow(
            clippy::unnecessary_cast,
            reason = "Trust: libc dev_t/ino_t widths vary across macOS and Linux ABIs; preserve the existing u64 identity and signed-device cast semantics"
        )]
        let output_identity = (stat.st_dev as u64, stat.st_ino as u64);
        if output.starts_with(subtree)
            || subtree.starts_with(output)
            || directory == output_identity
        {
            return Err("native source subtree and original output must be disjoint".into());
        }
        self.check()
    }
}

/// Non-cloneable completed native producer. An Arc can extend the SAME owner;
/// no public field, deserializer or saved observation can reconstruct one.
pub(crate) struct CompletedRuntime {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    state: NativeRuntime,
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
struct NativeRuntime {
    // Runtime descriptions close before the original output/build guards.
    inputs: crate::utils::retained_compiler_fixture::HeldRuntimeInputs,
    source_inputs: crate::utils::trust_repo_cache::InputSnapshot,
    ownership: Arc<BuildOwnership>,
    producer_source: String,
    nonfrontend_source: String,
    construction_inputs: String,
    producer_commit: String,
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) struct OriginalCompletedInputs<'a> {
    pub(crate) runtime: crate::utils::retained_compiler_fixture::OriginalRuntimeDescriptions<'a>,
    pub(crate) output: build_helper::trust_output_lock::OriginalOutputDescriptions<'a>,
    _completed: &'a CompletedRuntime,
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
impl OriginalCompletedInputs<'_> {
    fn count(&self) -> usize {
        self.runtime.count() + 2
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct FrontendRuntime {
    target: TargetSelection,
}

impl CommandLineStep for FrontendRuntime {
    type Output = Option<Arc<CompletedRuntime>>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("frontend-runtime-owner")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        false
    }

    fn make_run(run: RunConfig<'_>) {
        // Trust: retain the exact normal Step result without bypassing host
        // dispatch or constructing a second Builder/producer graph.
        let builder = run.builder;
        assert!(
            builder.sess.completed_runtime.borrow().is_none(),
            "one invocation cannot run another producer after runtime completion"
        );
        if let Some(completed) = builder.ensure(Self { target: run.target }) {
            let mut retained = builder.sess.completed_runtime.borrow_mut();
            assert!(retained.is_none(), "one invocation cannot replace runtime ownership");
            *retained = Some(completed);
        }
    }

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        validate_request(builder, self.target)
            .unwrap_or_else(|error| panic!("completed frontend runtime: {error}"));
        // Dry runs plan ordinary producers, but never construct completion.
        if builder.config.dry_run() {
            produce(builder, self.target);
            return None;
        }
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        panic!("completed frontend runtime is unsupported on this platform");
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        {
            let ownership =
                Arc::clone(builder.sess.runtime_build_ownership.as_ref().expect(
                    "completed runtime requires original native build and output ownership",
                ));
            // Trust: ignored child-exit success cannot hide unresolved native
            // execution ownership or manufacture a completed producer.
            drop(crate::utils::exec::protected_scope().unwrap_or_else(|error| {
                panic!("completed runtime has no current execution scope: {error}")
            }));
            ownership.check().unwrap();
            let before = repo::completed_frontend_runtime_inputs(builder).unwrap_or_else(|error| {
                panic!("cannot bind original runtime recipe inputs: {error}")
            });
            let (producer_source, nonfrontend_source) = sources(builder);
            let members = produce(builder, self.target);
            drop(crate::utils::exec::protected_scope().unwrap_or_else(|error| {
                panic!("runtime producer execution did not finish: {error}")
            }));
            assert!(
                !builder.config.exec_ctx().has_delayed_failures(),
                "failed normal producer cannot create completed runtime ownership"
            );
            let compiler = builder.compiler(1, self.target);
            let inputs = crate::utils::retained_compiler_fixture::HeldRuntimeInputs::capture(
                &std::fs::canonicalize(builder.sysroot(compiler)).unwrap(),
                &self.target.triple,
            )
            .unwrap_or_else(|error| panic!("cannot hold original completed runtime: {error}"));
            inputs.require_executables(&members).unwrap();
            let after = repo::completed_frontend_runtime_inputs(builder).unwrap();
            drop(crate::utils::exec::protected_scope().unwrap_or_else(|error| {
                panic!("runtime completion lost execution ownership: {error}")
            }));
            assert_eq!(before, after, "runtime construction inputs moved; no completion owner");
            assert_eq!(
                (producer_source.clone(), nonfrontend_source.clone()),
                sources(builder),
                "runtime source bookends moved; no completion owner"
            );
            let completed = CompletedRuntime {
                state: NativeRuntime {
                    inputs,
                    source_inputs: before.0,
                    ownership,
                    producer_source,
                    nonfrontend_source,
                    construction_inputs: before.1,
                    producer_commit: builder
                        .version_info()
                        .sha()
                        .expect("completed runtime requires original source identity")
                        .to_owned(),
                },
            };
            completed.check().unwrap();
            let offered_count = completed.original_input_descriptions().unwrap().count();
            builder.info(&format!(
                "Live completed native runtime: {} (original producer {}; sources {}; nonfrontend sources {}; observed input snapshot {}; construction inputs {}; original runtime/output descriptions {}). Original guards retained; no persistent receipt, cross-origin execution, SDK, ABI, resource or proof qualification.",
                completed.state.inputs.root().display(), completed.state.producer_commit,
                completed.state.producer_source, completed.state.nonfrontend_source,
                completed.state.source_inputs.digest(),
                completed.state.construction_inputs,
                offered_count,
            ));
            Some(Arc::new(completed))
        }
    }
}

fn validate_request(builder: &Builder<'_>, target: TargetSelection) -> Result<(), String> {
    validate_config(&builder.config)?;
    if builder.kind != Kind::Build
        || builder.paths.as_slice() != [std::path::PathBuf::from("frontend-runtime-owner")]
        || target != builder.host_target
        || builder.hosts.as_slice() != [builder.host_target]
        || builder.top_stage != 1
        || builder.download_rustc()
    {
        return Err(
            "completed runtime Step differs from its validated native stage1 selection".into()
        );
    }
    Ok(())
}

/// Reject an unsupported parsed request BEFORE taking command/output guards or
/// consuming Preparation. This inspects configuration only, without a Builder,
/// compiler download, producer invocation or reconstructed completion owner.
pub(crate) fn validate_config(config: &Config) -> Result<(), String> {
    if config.cmd.kind() != Kind::Build
        || config.paths.as_slice() != [std::path::PathBuf::from("frontend-runtime-owner")]
        || config.include_default_paths
        || config.hosts.as_slice() != [config.host_target]
        || config.stage != 1
        // Calling download_rustc() can start a download. A declared download
        // route is ineligible without invoking that effectful lazy accessor.
        || config.download_rustc_commit.is_some()
        || config.bypass_bootstrap_lock
        || !config.keep_stage.is_empty()
        || !config.keep_stage_std.is_empty()
        || !config.skip.is_empty()
        || config.compiler_test_fixture.is_some()
        || !config.free_args.is_empty()
        || config.omit_git_hash
    {
        return Err("requires the sole explicit frontend-runtime-owner selection, native stage1 normal producers, original locks and source identity; no defaults, downloaded, kept, skipped, test-fixture or extra-argument routes".into());
    }
    if !config.dry_run()
        && (!cfg!(all(target_os = "macos", target_arch = "aarch64"))
            || config.host_target.triple != "aarch64-apple-darwin")
    {
        return Err("completed runtime currently supports only native arm64 macOS".into());
    }
    Ok(())
}

/// Paths come from the successful original Steps, never a runtime record.
fn produce(builder: &Builder<'_>, target: TargetSelection) -> Vec<std::path::PathBuf> {
    let build_compiler = builder.compiler(0, target);
    for configured in &builder.targets {
        builder.std(build_compiler, *configured);
    }
    let compiler = builder.compiler(1, target);
    let docs = builder.rustdoc_for_compiler(compiler);
    let targo = builder.ensure(tool::Cargo::from_build_compiler(build_compiler, target));
    let frontend = builder.ensure(tool::TCargoTrust::from_build_compiler(build_compiler, target));
    let daemon = builder.ensure(tool::Trustd::from_build_compiler(build_compiler, target));
    let root = builder.sysroot(compiler);
    let ay = tool::ensure_sysroot_ay(builder, compiler, &root)
        .expect("completed runtime requires the actual source-backed AY producer");
    vec![builder.rustc(compiler), docs, targo.tool_path, frontend.tool_path, daemon.tool_path, ay]
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn sources(builder: &Builder<'_>) -> (String, String) {
    let fresh = ExecutionContext::new(builder.config.exec_ctx().verbosity, false);
    let config =
        trust_source_identity::config_digest(builder.config.config.as_deref(), &builder.src);
    let head = builder.rust_info().info().expect("completed runtime requires Git-backed source");
    let full = trust_source_identity::of_sources(&fresh, &builder.src, &config, head).unwrap();
    let nonfrontend =
        trust_source_identity::frontend_runtime_sources(&fresh, &builder.src, &config, head)
            .unwrap();
    (full.info.sha, nonfrontend)
}

impl CompletedRuntime {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn original_input_descriptions(
        &self,
    ) -> Result<OriginalCompletedInputs<'_>, String> {
        self.state.ownership.check()?;
        let runtime = self.state.inputs.original_descriptions()?;
        // SAFETY: this method only lends originals from the SAME live owner.
        // No release/unlock/flag/cursor operation occurs, and the returned
        // lifetime retains this completed owner and its original close-only
        // OutputLock. The eventual authenticated sender must preserve custody.
        let output = unsafe { self.state.ownership.output.original_descriptions() }
            .map_err(|error| error.to_string())?;
        let complete = OriginalCompletedInputs { runtime, output, _completed: self };
        if complete.count() > 4096 {
            return Err("complete runtime/output descriptor census exceeds bound".into());
        }
        use std::os::fd::AsRawFd as _;
        let mut descriptors =
            std::collections::BTreeSet::from([complete.runtime.root_descriptor.as_raw_fd()]);
        for entry in &complete.runtime.entries {
            descriptors.insert(entry.descriptor.as_raw_fd());
        }
        if !complete.output.root().is_absolute()
            || !descriptors.insert(complete.output.directory().as_raw_fd())
            || !descriptors.insert(complete.output.lock().as_raw_fd())
            || descriptors.len() != complete.count()
        {
            return Err("original runtime/output descriptions are incomplete or alias".into());
        }
        self.state.ownership.check()?;
        Ok(complete)
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn check(&self) -> Result<(), String> {
        self.state.ownership.check()?;
        self.state.inputs.check()?;
        self.state.ownership.check()
    }
}

#[cfg(test)]
mod tests;

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod retention;
