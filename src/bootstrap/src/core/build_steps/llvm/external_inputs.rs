//! Observed declared inputs of one prepared external-LLVM CMake request.
//! These are local cache facts, never provider readiness or hermetic execution.

use std::collections::BTreeSet;
use std::fs;
#[cfg(target_os = "macos")]
use std::path::Path;
use std::path::PathBuf;

use sha2::{Digest as _, Sha256};

use super::{LlvmKind, LlvmOutput};
use crate::core::config::TargetSelection;
use crate::utils::{trust_repo_cache as cache, trust_repo_tools as tools};

pub(super) struct ExternalInputs {
    paths: Vec<PathBuf>,
}

impl ExternalInputs {
    pub(super) fn from_prepared(prepared: &cmake::Prepared) -> Option<Self> {
        // Requested strings and cleanup namespaces alone are not byte evidence.
        prepared.cache_inputs()?;
        let paths = prepared.cleanup_inputs()?;
        if paths.is_empty() || paths.iter().any(|path| !path.is_absolute()) {
            return None;
        }
        Some(Self { paths: paths.iter().cloned().collect::<BTreeSet<_>>().into_iter().collect() })
    }

    pub(super) fn key(&self, llvm: &LlvmOutput, target: TargetSelection) -> Option<String> {
        if !cfg!(any(target_os = "macos", target_os = "linux"))
            || llvm.kind() != LlvmKind::External
            || self.paths.is_empty()
            || self.paths.iter().any(|path| !path.is_absolute())
            || !llvm.root_dir().is_dir()
            || !llvm.llvm_config().is_file()
            || !llvm.cmake_dir().join("LLVMConfig.cmake").is_file()
            || !llvm.cmake_dir().join("LLVMExports.cmake").is_file()
        {
            return None;
        }
        self.key_with_context(llvm, target, &native_context().ok()?)
    }

    fn key_with_context(
        &self,
        llvm: &LlvmOutput,
        target: TargetSelection,
        context: &str,
    ) -> Option<String> {
        if llvm.kind() != LlvmKind::External || context.is_empty() || self.paths.is_empty() {
            return None;
        }
        let selected = llvm.root_dir();
        let selected_before = fs::symlink_metadata(selected).ok()?;
        let root = fs::canonicalize(selected).ok()?;
        let root_before = fs::symlink_metadata(&root).ok()?;
        if !root_before.is_dir() {
            return None;
        }
        // A package namespace can record unused missing links, but the selected
        // executable and CMake exports must actually be available. Their paths
        // do not become SourceReady or an SDK through this observation.
        for file in [
            llvm.llvm_config().to_owned(),
            llvm.cmake_dir().join("LLVMConfig.cmake"),
            llvm.cmake_dir().join("LLVMExports.cmake"),
        ] {
            if !fs::metadata(file).ok()?.is_file() {
                return None;
            }
        }
        let mut hash = Sha256::new();
        cache::add(&mut hash, b"trust.prepared-external-llvm-inputs/v1");
        cache::add(&mut hash, selected.as_os_str().as_encoded_bytes());
        cache::add(&mut hash, root.as_os_str().as_encoded_bytes());
        cache::add(&mut hash, target.triple.as_bytes());
        cache::add(&mut hash, [u8::from(llvm.link_shared())]);
        cache::add(&mut hash, context);
        cache::add(
            &mut hash,
            tools::selected_tool_installation_digest(&root, llvm.llvm_config()).ok()?,
        );
        for path in &self.paths {
            if !path.is_absolute() {
                return None;
            }
            cache::add(&mut hash, path.as_os_str().as_encoded_bytes());
            // Required native paths keep their stronger absence policy. In
            // particular an unused installation link is not tool availability.
            let digest =
                if path.is_dir() { cache::tree_digest(path) } else { tools::tool_digest(path) };
            cache::add(&mut hash, digest.ok()?);
        }
        if fs::canonicalize(selected).ok()? != root
            || !cache::same_snapshot(&selected_before, &fs::symlink_metadata(selected).ok()?)
            || !cache::same_snapshot(&root_before, &fs::symlink_metadata(&root).ok()?)
        {
            return None;
        }
        Some(cache::finish(hash))
    }
}

// Reuse the native tool/install/loader contract used by repository inputs.
// In particular tree_digest's sealed-system links require this actual OS build;
// a version string supplied by a caller or a cache record cannot replace it.
fn native_context() -> Result<String, String> {
    let mut hash = Sha256::new();
    cache::add(&mut hash, b"trust.prepared-native-context/v1");
    cache::add(&mut hash, std::env::consts::OS);
    cache::add(&mut hash, std::env::consts::ARCH);
    for name in ["DYLD_LIBRARY_PATH", "DYLD_FALLBACK_LIBRARY_PATH", "LD_LIBRARY_PATH"] {
        let value = std::env::var_os(name);
        cache::add(&mut hash, name);
        cache::add(&mut hash, [u8::from(value.is_some())]);
        if let Some(value) = value {
            cache::add(&mut hash, value.as_encoded_bytes());
            for directory in std::env::split_paths(&value) {
                if !directory.is_absolute() {
                    return Err("relative native loader override is not reusable".into());
                }
                cache::add(&mut hash, cache::tree_digest(&directory)?);
            }
        }
    }
    #[cfg(target_os = "macos")]
    {
        let build = tools::query(Path::new("/usr/bin/sw_vers"), &["-buildVersion"])?;
        if build.is_empty() {
            return Err("sealed OS build is unavailable".into());
        }
        cache::add(&mut hash, &build);
        let sdk = match std::env::var_os("SDKROOT") {
            Some(path) => PathBuf::from(path),
            None => PathBuf::from(tools::query(Path::new("/usr/bin/xcrun"), &["--show-sdk-path"])?),
        };
        if !sdk.is_absolute() {
            return Err("selected native SDK is not absolute".into());
        }
        cache::add(&mut hash, cache::tree_digest(&sdk)?);
        let clang = tools::query(Path::new("/usr/bin/xcrun"), &["--find", "clang"])?;
        let directory = Path::new(&clang)
            .parent()
            .and_then(Path::parent)
            .ok_or("selected developer compiler has no installation")?;
        cache::add(
            &mut hash,
            tools::selected_tool_installation_digest(directory, Path::new(&clang))?,
        );
        if tools::query(Path::new("/usr/bin/sw_vers"), &["-buildVersion"])? != build {
            return Err("sealed OS build changed during native observation".into());
        }
    }
    Ok(cache::finish(hash))
}

#[cfg(test)]
#[path = "tests/external_inputs_tests.rs"]
mod tests;
