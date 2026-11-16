//! Trust: explicit first producing node of the original Host Bootstrap graph.
//! This object is unverified engineering output, not a runtime or SDK result.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use std::os::unix::ffi::OsStrExt as _;

use crate::core::builder::{Builder, CommandLineStep, Kind, RunConfig, ShouldRun};
use crate::core::config::{Config, TargetSelection};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct NativeObject {
    target: TargetSelection,
}
impl CommandLineStep for NativeObject {
    type Output = ();
    const IS_HOST: bool = true;
    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("native-object-leaf")
    }
    fn is_default_step(_builder: &Builder<'_>) -> bool {
        false
    }
    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Self { target: run.target });
    }
    fn run(self, builder: &Builder<'_>) {
        assert!(
            builder.kind == Kind::Build
                && builder.paths.as_slice() == [std::path::PathBuf::from("native-object-leaf")]
                && self.target == builder.host_target
                && builder.hosts.as_slice() == [builder.host_target]
                && builder.top_stage == 1,
            "native object requires one explicit original host build node"
        );
        if builder.config.dry_run() {
            builder.info(
                "Plan original-source NativeLeafV1 object; no dispatch or artifact owner created",
            );
            return;
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        {
            let observation = crate::utils::metadata_scheduler::host_graph::produce_native_object(
                b"trust_bootstrap_native_object.o",
            )
            .unwrap_or_else(|error| panic!("actual native object node failed: {error}"));
            builder.info(&format!("Original source-task predecessor read {} bytes from {} before this object operation.", observation.source.bytes,
                std::path::Path::new(std::ffi::OsStr::from_bytes(&observation.source.path)).display()));
            builder.info(&format!("Native object produced at {} ({} bytes; SHA256 {}). Original source/output/Host operation retained; no SDK, runtime, proof or whole-graph completion.",
                observation.path.display(),observation.bytes,observation.sha256.iter().map(|byte|format!("{byte:02x}")).collect::<String>()));
        }
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        panic!("native object operation is unsupported on this platform");
    }
}

/// Parsed selection DATA only. It precedes command/output acquisition and does
/// not create an original source, Host operation, scope, SDK or CPU owner.
pub(crate) fn validate_config(config: &Config) -> Result<(), String> {
    if config.cmd.kind() != Kind::Build
        || config.paths.as_slice() != [std::path::PathBuf::from("native-object-leaf")]
        || config.include_default_paths
        || config.hosts.as_slice() != [config.host_target]
        || config.targets.as_slice() != [config.host_target]
        || config.stage != 1
        || config.host_target.file.is_some()
        || config.host_target.synthetic
        || config.download_rustc_commit.is_some()
        || config.bypass_bootstrap_lock
        || !config.keep_stage.is_empty()
        || !config.keep_stage_std.is_empty()
        || !config.skip.is_empty()
        || config.compiler_test_fixture.is_some()
        || !config.free_args.is_empty()
        || config.omit_git_hash
    {
        return Err("requires the sole explicit native-object-leaf build, native stage1 host/target, original locks and source identity; no defaults, downloads, kept/skipped/test-fixture or extra-argument routes".into());
    }
    if !config.dry_run() && (config.external_rustc.is_none() || config.external_cargo.is_none()) {
        return Err(
            "native object needs explicit configured original SDK compiler and Targo inputs".into(),
        );
    }
    if !config.dry_run()
        && (!cfg!(all(target_os = "macos", target_arch = "aarch64"))
            || config.host_target.triple != "aarch64-apple-darwin")
    {
        return Err("native object production supports only native arm64 macOS".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests;

/// Run this one native node from the real prepared engine scope. It requires
/// no C compiler, Cargo dependency graph or runtime assembly Session. Those
/// remain prerequisites of their own ordinary Step graphs, unchanged.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) fn execute_original(
    config: &Config,
    scope: &crate::engine::ExecutionScope,
) -> Result<(), String> {
    validate_config(config)?;
    if config.dry_run() {
        return Err("native object production needs a real protected scope".into());
    }
    let observation = scope.run_native_object()?;
    println!(
        "Original source-task predecessor read {} bytes from {} before this object operation.",
        observation.source.bytes,
        std::path::Path::new(std::ffi::OsStr::from_bytes(&observation.source.path)).display()
    );
    println!(
        "Native object produced at {} ({} bytes; SHA256 {}). Original owners retained; no runtime, SDK, proof or whole-graph completion.",
        observation.path.display(),
        observation.bytes,
        observation.sha256.iter().map(|byte| format!("{byte:02x}")).collect::<String>()
    );
    Ok(())
}
