//! Bind LLD's CMake dependency to the same declared zstd metadata as rustc_llvm.

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::utils::llvm_native_link::{StaticZstd, static_zstd_in};

fn query(provider: &Path, directory: &Path, arguments: &[&str]) -> Result<String, String> {
    let mut selected = OsString::from("--with-path=");
    selected.push(directory);
    let output = Command::new(provider)
        .arg(selected)
        .args(arguments)
        .output()
        .map_err(|error| format!("could not query declared LLD zstd metadata: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "declared LLD zstd metadata query failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8(output.stdout).map_err(|error| error.to_string())
}

fn include_directory(value: &str) -> Result<PathBuf, String> {
    let value = value.trim();
    if value.is_empty() || value.chars().any(char::is_control) {
        return Err("declared LLD zstd include directory is malformed".into());
    }
    let directory = Path::new(value);
    if !directory.is_absolute() {
        return Err("declared LLD zstd include directory must be absolute".into());
    }
    let physical = directory.canonicalize().map_err(|error| error.to_string())?;
    if !physical.is_dir() || !physical.join("zstd.h").is_file() {
        return Err("declared LLD zstd include directory has no zstd.h".into());
    }
    // Keep the declared namespace in the CMake request, including any alias.
    // Canonicalizing the operand would lose a later retarget of that alias.
    Ok(directory.to_owned())
}

/// This is a dependency selection, not a CMake search hint: an installed package
/// outside the declared directory must not silently replace the selected input.
pub(super) fn bind_declared(
    config: &mut cmake::Config,
    provider: &Path,
    target: &str,
    directory: &Path,
) -> Result<(), String> {
    let selected = static_zstd_in(provider, target, directory)?;
    let before = fs::read(&selected.metadata).map_err(|error| error.to_string())?;
    let provider_before = fs::read(&selected.provider).map_err(|error| error.to_string())?;
    let include = include_directory(&query(
        &selected.provider,
        directory,
        &["--variable=includedir", "libzstd"],
    )?)?;
    // Re-resolve the original selector: its alias or PATH lookup can change
    // while the old physical executable remains intact and answers queries.
    let repeated = static_zstd_in(provider, target, directory)?;
    if selected.provider != repeated.provider
        || selected.watch_paths != repeated.watch_paths
        || selected.metadata != repeated.metadata
        || selected.library != repeated.library
        || selected.version != repeated.version
        || before != fs::read(&selected.metadata).map_err(|error| error.to_string())?
        || provider_before != fs::read(&selected.provider).map_err(|error| error.to_string())?
    {
        return Err("declared LLD zstd input changed while resolving its headers".into());
    }
    bind_paths(config, directory, &selected, &include);
    Ok(())
}

fn bind_paths(config: &mut cmake::Config, directory: &Path, selected: &StaticZstd, include: &Path) {
    config
        .input_path(directory)
        .input_path(&selected.provider)
        .input_path(&selected.metadata)
        .define_input_path("zstd_INCLUDE_DIR", include)
        .define_input_path("zstd_LIBRARY", &selected.library.path)
        .define_input_path("zstd_STATIC_LIBRARY", &selected.library.path);
    for path in &selected.watch_paths {
        config.input_path(path);
    }
}

#[cfg(test)]
#[path = "tests/lld_zstd_tests.rs"]
mod tests;
