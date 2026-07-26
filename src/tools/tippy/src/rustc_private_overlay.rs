//! Narrow rustc-private search-path support for branded Tippy invocations.
//!
//! The public frontend accepts a prepared bootstrap overlay only when both
//! directories belong to the selected Trust build tree, name the selected
//! compiler commit, and carry its exact `rustc_public`/`rustc_driver`
//! artifacts. The driver applies the overlay only to the fixed Trust-MC leaf
//! allowlist.

// This module is compiled independently into the frontend and driver binary;
// each binary intentionally uses only its half of the shared policy.
#![allow(dead_code)]

use std::ffi::{OsStr, OsString};
use std::fs;
use std::io::{BufReader, Read as _};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

pub(crate) const HOST_DIR_ENV: &str = "TRUST_TIPPY_RUSTC_PRIVATE_HOST_DIR";
pub(crate) const TARGET_DIR_ENV: &str = "TRUST_TIPPY_RUSTC_PRIVATE_TARGET_DIR";

const PREPARED_ROOT_DIR: &str = "rustc-private-sysroots";
const FILTERED_DEPS_DIR: &str = ".trust-tippy-rustc-private-filtered-deps";
const PREPARED_MARKER: &str = ".rustc-commit-hash";
const MAX_PREPARED_MARKER_BYTES: u64 = 128;
const MAX_COMPILER_VERBOSE_VERSION_BYTES: u64 = 64 * 1024;
const LINKED_RUSTC_COMMIT_PREFIX_LEN: usize = 9;
const RUSTC_PRIVATE_CRATES: [&str; 5] = [
    "trust_mc_codegen_shared",
    "trust_mc_codegen_types",
    "trust_mc_kani_types",
    "trust_mc_compiler",
    "scanner",
];
const BOUND_ARTIFACT_PREFIXES: [&str; 2] = ["librustc_public-", "librustc_driver-"];
const LIBRARY_EXTENSIONS: [&str; 7] = ["rlib", "rmeta", "dylib", "so", "dll", "lib", "a"];

static NEXT_FILTER_DIR: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct OverlayEnvironment {
    host_dir: Option<OsString>,
    target_dir: Option<OsString>,
}

impl OverlayEnvironment {
    pub(crate) fn capture() -> Self {
        Self {
            host_dir: std::env::var_os(HOST_DIR_ENV),
            target_dir: std::env::var_os(TARGET_DIR_ENV),
        }
    }

    pub(crate) fn is_configured(&self) -> bool {
        self.host_dir.is_some() || self.target_dir.is_some()
    }

    #[cfg(test)]
    fn new(host_dir: Option<PathBuf>, target_dir: Option<PathBuf>) -> Self {
        Self {
            host_dir: host_dir.map(PathBuf::into_os_string),
            target_dir: target_dir.map(PathBuf::into_os_string),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConfiguredOverlay {
    host_dir: PathBuf,
    target_dir: PathBuf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MarkerExpectation<'a> {
    Exact(&'a str),
    ExactWithCompatiblePrefix { exact: &'a str, compatible_prefix: &'a str },
}

impl ConfiguredOverlay {
    pub(crate) fn for_frontend(
        compiler: Option<&Path>,
        compiler_commit_hash: Option<&str>,
        environment: OverlayEnvironment,
    ) -> Result<Option<Self>, String> {
        match compiler {
            Some(compiler) => Self::for_compiler(compiler, compiler_commit_hash, environment),
            None if environment.is_configured() => Err(format!(
                "{HOST_DIR_ENV}/{TARGET_DIR_ENV} require an authenticated branded Tippy frontend"
            )),
            None => Ok(None),
        }
    }

    pub(crate) fn for_driver(
        sysroot: Option<&Path>,
        compiler_commit_hash: Option<&str>,
        linked_rustc_version: Option<&str>,
        environment: OverlayEnvironment,
    ) -> Result<Option<Self>, String> {
        if !environment.is_configured() {
            return Ok(None);
        }
        match sysroot {
            Some(sysroot) => {
                let exact = compiler_commit_hash.ok_or_else(|| {
                    "configured rustc-private overlay is missing the authenticated sibling `trustc` compiler identity"
                        .to_owned()
                })?;
                let compatible_prefix = linked_rustc_version
                    .ok_or_else(|| {
                        "configured rustc-private overlay is missing the linked rustc compiler identity".to_owned()
                    })
                    .and_then(linked_rustc_commit_prefix)?;
                Self::for_sysroot(
                    sysroot,
                    Some(MarkerExpectation::ExactWithCompatiblePrefix {
                        exact,
                        compatible_prefix,
                    }),
                    environment,
                )
            },
            None if environment.is_configured() => Err(format!(
                "{HOST_DIR_ENV}/{TARGET_DIR_ENV} require an authenticated branded Tippy driver"
            )),
            None => Ok(None),
        }
    }

    pub(crate) fn for_compiler(
        compiler: &Path,
        compiler_commit_hash: Option<&str>,
        environment: OverlayEnvironment,
    ) -> Result<Option<Self>, String> {
        let bin = compiler
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .ok_or_else(|| {
                format!(
                    "cannot derive the selected Trust sysroot from compiler `{}`",
                    compiler.display()
                )
            })?;
        let sysroot = bin
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .ok_or_else(|| {
                format!(
                    "cannot derive the selected Trust sysroot from compiler `{}`",
                    compiler.display()
                )
            })?;
        Self::for_sysroot(sysroot, compiler_commit_hash.map(MarkerExpectation::Exact), environment)
    }

    fn for_sysroot(
        sysroot: &Path,
        marker_expectation: Option<MarkerExpectation<'_>>,
        environment: OverlayEnvironment,
    ) -> Result<Option<Self>, String> {
        let (host_dir, target_dir) = match (environment.host_dir, environment.target_dir) {
            (None, None) => return Ok(None),
            (Some(_), None) | (None, Some(_)) => {
                return Err(format!(
                    "{HOST_DIR_ENV} and {TARGET_DIR_ENV} must be configured together"
                ));
            },
            (Some(host_dir), Some(target_dir)) => (PathBuf::from(host_dir), PathBuf::from(target_dir)),
        };

        let sysroot = canonical_directory(sysroot, "selected Trust sysroot")?;
        let build_host = sysroot.parent().ok_or_else(|| {
            format!(
                "selected Trust sysroot `{}` has no build-host parent",
                sysroot.display()
            )
        })?;
        let host_triple = build_host.file_name().ok_or_else(|| {
            format!(
                "selected Trust build directory `{}` has no host name",
                build_host.display()
            )
        })?;
        let prepared_root = canonical_directory(
            &build_host.join(PREPARED_ROOT_DIR),
            "selected Trust rustc-private prepared-root directory",
        )?;
        let host_dir = canonical_directory(&host_dir, HOST_DIR_ENV)?;
        let target_dir = canonical_directory(&target_dir, TARGET_DIR_ENV)?;

        if host_dir.file_name() != Some(OsStr::new("host")) {
            return Err(format!(
                "{HOST_DIR_ENV} `{}` must name the prepared `host` directory",
                host_dir.display()
            ));
        }
        if target_dir.file_name() != Some(host_triple) {
            return Err(format!(
                "{TARGET_DIR_ENV} `{}` must name the selected compiler host `{}`",
                target_dir.display(),
                host_triple.to_string_lossy()
            ));
        }
        let host_parent = host_dir.parent();
        let target_parent = target_dir.parent();
        if host_parent != target_parent {
            return Err(format!(
                "{HOST_DIR_ENV} and {TARGET_DIR_ENV} must share one prepared rustc-private root"
            ));
        }
        let prepared = host_parent.ok_or_else(|| {
            format!(
                "canonical {HOST_DIR_ENV} directory `{}` has no prepared parent",
                host_dir.display()
            )
        })?;
        if prepared.parent() != Some(prepared_root.as_path()) {
            return Err(format!(
                "configured rustc-private overlay `{}` is outside selected Trust prepared root `{}`",
                prepared.display(),
                prepared_root.display()
            ));
        }
        let marker_expectation = marker_expectation.ok_or_else(|| {
            "configured rustc-private overlay is missing authenticated compiler version identity".to_owned()
        })?;
        validate_prepared_marker(prepared, marker_expectation)?;
        validate_bound_artifacts(&sysroot, &target_dir, host_triple)?;

        Ok(Some(Self { host_dir, target_dir }))
    }

    pub(crate) fn configure_command(&self, command: &mut Command) {
        command
            .env(HOST_DIR_ENV, &self.host_dir)
            .env(TARGET_DIR_ENV, &self.target_dir);
    }

    pub(crate) fn prepare_compiler_args(
        &self,
        crate_name: Option<&str>,
        args: &[String],
    ) -> Result<Option<PreparedCompilerArgs>, String> {
        let Some(crate_name) = crate_name.filter(|name| crate_uses_overlay(name)) else {
            return Ok(None);
        };

        let mut prepared = PreparedCompilerArgs {
            args: Vec::with_capacity(args.len() + 4),
            filtered_dirs: FilteredDependencyDirs::default(),
        };
        let program_count = usize::from(!args.is_empty());
        prepared.args.extend_from_slice(&args[..program_count]);
        prepared.args.extend([
            "-L".to_owned(),
            format!("dependency={}", self.target_dir.display()),
            "-L".to_owned(),
            format!("dependency={}", self.host_dir.display()),
        ]);

        let mut index = program_count;
        while index < args.len() {
            if args[index] == "-L" && index + 1 < args.len() {
                let payload = &args[index + 1];
                if let Some(path) = payload.strip_prefix("dependency=") {
                    self.rewrite_dependency_path(crate_name, path, &mut prepared)?;
                } else {
                    prepared.args.extend([args[index].clone(), payload.clone()]);
                }
                index += 2;
                continue;
            }
            if let Some(payload) = args[index].strip_prefix("-Ldependency=") {
                self.rewrite_dependency_path(crate_name, payload, &mut prepared)?;
                index += 1;
                continue;
            }
            prepared.args.push(args[index].clone());
            index += 1;
        }

        Ok(Some(prepared))
    }

    fn rewrite_dependency_path(
        &self,
        crate_name: &str,
        path: &str,
        prepared: &mut PreparedCompilerArgs,
    ) -> Result<(), String> {
        let dependency_dir = canonical_directory(Path::new(path), "Cargo dependency search directory")?;
        if dependency_dir == self.host_dir || dependency_dir == self.target_dir {
            return Ok(());
        }
        let filtered = create_filtered_dependency_dir(&dependency_dir, crate_name)?;
        prepared
            .args
            .extend(["-L".to_owned(), format!("dependency={}", filtered.display())]);
        prepared.filtered_dirs.paths.push(filtered);
        Ok(())
    }
}

pub(crate) fn clear_overlay_command_environment(command: &mut Command) {
    command.env_remove(HOST_DIR_ENV).env_remove(TARGET_DIR_ENV);
}

pub(crate) fn crate_uses_overlay(crate_name: &str) -> bool {
    let normalized = crate_name.replace('-', "_");
    RUSTC_PRIVATE_CRATES.contains(&normalized.as_str())
}

/// Query the selected compiler's complete metadata identity.
///
/// The caller must authenticate and revalidate `compiler` around this query.
/// This helper bounds captured output and rejects every non-canonical version
/// response; it does not establish executable pathname authority by itself.
pub(crate) fn query_compiler_commit_hash(compiler: &Path) -> Result<String, String> {
    let mut command = Command::new(compiler);
    clear_overlay_command_environment(&mut command);
    command
        .arg("-vV")
        .env_remove("RUSTC_FORCE_RUSTC_VERSION")
        .env_remove("RUSTC_OVERRIDE_VERSION_STRING")
        .stdout(Stdio::piped())
        .stderr(Stdio::null());

    let mut child = command.spawn().map_err(|error| {
        format!(
            "cannot launch selected compiler `{}` for metadata identity: {error}",
            compiler.display()
        )
    })?;
    let stdout = match child.stdout.take() {
        Some(stdout) => stdout,
        None => {
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!(
                "selected compiler `{}` did not expose its captured version output",
                compiler.display()
            ));
        },
    };
    let mut bytes = Vec::new();
    let read_result = stdout
        .take(MAX_COMPILER_VERBOSE_VERSION_BYTES + 1)
        .read_to_end(&mut bytes);
    if let Err(error) = read_result {
        let _ = child.kill();
        let _ = child.wait();
        return Err(format!(
            "cannot read selected compiler `{}` version output: {error}",
            compiler.display()
        ));
    }
    if bytes.len() as u64 > MAX_COMPILER_VERBOSE_VERSION_BYTES {
        let _ = child.kill();
        let _ = child.wait();
        return Err(format!(
            "selected compiler `{}` version output exceeds the {MAX_COMPILER_VERBOSE_VERSION_BYTES}-byte limit",
            compiler.display()
        ));
    }
    let status = child.wait().map_err(|error| {
        format!(
            "cannot wait for selected compiler `{}` version query: {error}",
            compiler.display()
        )
    })?;
    if !status.success() {
        return Err(format!(
            "selected compiler `{}` version query failed with {status}",
            compiler.display()
        ));
    }
    let verbose_version = std::str::from_utf8(&bytes).map_err(|error| {
        format!(
            "selected compiler `{}` version output is not UTF-8: {error}",
            compiler.display()
        )
    })?;
    compiler_commit_hash_from_verbose_version(verbose_version)
}

fn compiler_commit_hash_from_verbose_version(verbose_version: &str) -> Result<String, String> {
    if verbose_version.len() as u64 > MAX_COMPILER_VERBOSE_VERSION_BYTES {
        return Err(format!(
            "selected compiler version output exceeds the {MAX_COMPILER_VERBOSE_VERSION_BYTES}-byte limit"
        ));
    }
    let mut hashes = verbose_version
        .lines()
        .filter_map(|line| line.strip_prefix("commit-hash: "));
    let hash = hashes
        .next()
        .ok_or_else(|| "selected compiler version output omitted `commit-hash`".to_owned())?;
    if hashes.next().is_some() {
        return Err("selected compiler version output contains multiple `commit-hash` fields".to_owned());
    }
    validate_full_commit_hash(hash, "selected compiler version output")?;
    Ok(hash.to_owned())
}

fn linked_rustc_commit_prefix(version: &str) -> Result<&str, String> {
    let (_, suffix) = version
        .rsplit_once(" (")
        .ok_or_else(|| format!("linked rustc version `{version}` omitted its compiler commit prefix"))?;
    let prefix = suffix
        .split_ascii_whitespace()
        .next()
        .ok_or_else(|| format!("linked rustc version `{version}` omitted its compiler commit prefix"))?;
    if prefix.len() != LINKED_RUSTC_COMMIT_PREFIX_LEN || !prefix.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(format!(
            "linked rustc version `{version}` has a malformed compiler commit prefix"
        ));
    }
    Ok(prefix)
}

fn validate_full_commit_hash(hash: &str, subject: &str) -> Result<(), String> {
    if hash.len() != 40 || !hash.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(format!("{subject} does not contain one 40-digit compiler commit"));
    }
    Ok(())
}

#[derive(Debug)]
pub(crate) struct PreparedCompilerArgs {
    args: Vec<String>,
    filtered_dirs: FilteredDependencyDirs,
}

impl PreparedCompilerArgs {
    pub(crate) fn args(&self) -> &[String] {
        &self.args
    }
}

#[derive(Debug, Default)]
struct FilteredDependencyDirs {
    paths: Vec<PathBuf>,
}

impl Drop for FilteredDependencyDirs {
    fn drop(&mut self) {
        for path in self.paths.iter().rev() {
            let _ = fs::remove_dir_all(path);
            if let Some(parent) = path.parent() {
                let _ = fs::remove_dir(parent);
            }
        }
    }
}

fn canonical_directory(path: &Path, subject: &str) -> Result<PathBuf, String> {
    if path.as_os_str().is_empty() {
        return Err(format!("{subject} is empty"));
    }
    let canonical = path
        .canonicalize()
        .map_err(|error| format!("cannot canonicalize {subject} `{}`: {error}", path.display()))?;
    let metadata = fs::symlink_metadata(&canonical)
        .map_err(|error| format!("cannot inspect {subject} `{}`: {error}", canonical.display()))?;
    if !metadata.file_type().is_dir() {
        return Err(format!("{subject} `{}` is not a directory", canonical.display()));
    }
    Ok(canonical)
}

fn validate_prepared_marker(prepared: &Path, expectation: MarkerExpectation<'_>) -> Result<(), String> {
    let marker = prepared.join(PREPARED_MARKER);
    let metadata = fs::symlink_metadata(&marker).map_err(|error| {
        format!(
            "configured rustc-private overlay `{}` is not a prepared Trust sysroot: missing {PREPARED_MARKER}: {error}",
            prepared.display()
        )
    })?;
    if !metadata.file_type().is_file() {
        return Err(format!(
            "configured rustc-private marker `{}` is not a plain file",
            marker.display()
        ));
    }
    if metadata.len() > MAX_PREPARED_MARKER_BYTES {
        return Err(format!(
            "configured rustc-private marker `{}` exceeds the {MAX_PREPARED_MARKER_BYTES}-byte limit",
            marker.display()
        ));
    }
    let file = fs::File::open(&marker).map_err(|error| {
        format!(
            "cannot open prepared rustc-private marker `{}`: {error}",
            marker.display()
        )
    })?;
    let opened_metadata = file.metadata().map_err(|error| {
        format!(
            "cannot inspect opened rustc-private marker `{}`: {error}",
            marker.display()
        )
    })?;
    if !opened_metadata.file_type().is_file() {
        return Err(format!(
            "opened rustc-private marker `{}` is not a plain file",
            marker.display()
        ));
    }
    if opened_metadata.len() > MAX_PREPARED_MARKER_BYTES {
        return Err(format!(
            "opened rustc-private marker `{}` exceeds the {MAX_PREPARED_MARKER_BYTES}-byte limit",
            marker.display()
        ));
    }
    let mut bytes = Vec::with_capacity(opened_metadata.len() as usize);
    file.take(MAX_PREPARED_MARKER_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| {
            format!(
                "cannot read prepared rustc-private marker `{}`: {error}",
                marker.display()
            )
        })?;
    if bytes.len() as u64 > MAX_PREPARED_MARKER_BYTES {
        return Err(format!(
            "configured rustc-private marker `{}` exceeds the {MAX_PREPARED_MARKER_BYTES}-byte limit",
            marker.display()
        ));
    }
    let marker_text = std::str::from_utf8(&bytes).map_err(|error| {
        format!(
            "configured rustc-private marker `{}` is not UTF-8: {error}",
            marker.display()
        )
    })?;
    let commit = marker_text.strip_suffix('\n').unwrap_or(marker_text);
    let commit = commit.strip_suffix('\r').unwrap_or(commit);
    validate_full_commit_hash(
        commit,
        &format!("configured rustc-private marker `{}`", marker.display()),
    )?;
    match expectation {
        MarkerExpectation::Exact(expected) => {
            validate_full_commit_hash(expected, "authenticated selected compiler identity")?;
            if commit != expected {
                return Err(format!(
                    "configured rustc-private marker `{}` names compiler commit `{commit}`, not authenticated selected compiler commit `{expected}`",
                    marker.display()
                ));
            }
        },
        MarkerExpectation::ExactWithCompatiblePrefix {
            exact,
            compatible_prefix,
        } => {
            validate_full_commit_hash(exact, "authenticated sibling `trustc` compiler identity")?;
            if commit != exact {
                return Err(format!(
                    "configured rustc-private marker `{}` names compiler commit `{commit}`, not authenticated sibling `trustc` compiler commit `{exact}`",
                    marker.display()
                ));
            }
            if !commit.starts_with(compatible_prefix) {
                return Err(format!(
                    "configured rustc-private marker `{}` names compiler commit `{commit}`, incompatible with linked rustc commit prefix `{compatible_prefix}`",
                    marker.display()
                ));
            }
        },
    }
    Ok(())
}

fn validate_bound_artifacts(sysroot: &Path, target_dir: &Path, host_triple: &OsStr) -> Result<(), String> {
    let installed = canonical_directory(
        &sysroot.join("lib").join("rustlib").join(host_triple).join("lib"),
        "selected Trust compiler library directory",
    )?;
    for prefix in BOUND_ARTIFACT_PREFIXES {
        let prepared = unique_artifact(target_dir, prefix)?;
        let file_name = prepared.file_name().ok_or_else(|| {
            format!(
                "prepared rustc-private artifact `{}` has no file name",
                prepared.display()
            )
        })?;
        let selected = installed.join(file_name);
        if !plain_files_have_identical_bytes(&prepared, &selected)? {
            return Err(format!(
                "prepared rustc-private artifact `{}` does not exactly match selected compiler artifact `{}`",
                prepared.display(),
                selected.display()
            ));
        }
    }
    Ok(())
}

fn unique_artifact(directory: &Path, prefix: &str) -> Result<PathBuf, String> {
    let mut matches = Vec::new();
    for entry in fs::read_dir(directory)
        .map_err(|error| format!("cannot inspect prepared directory `{}`: {error}", directory.display()))?
    {
        let entry = entry.map_err(|error| {
            format!(
                "cannot read an entry in prepared directory `{}`: {error}",
                directory.display()
            )
        })?;
        let path = entry.path();
        if path
            .file_name()
            .and_then(OsStr::to_str)
            .is_some_and(|name| name.starts_with(prefix) && has_library_extension(Path::new(name)))
        {
            matches.push(path);
        }
    }
    let artifact = matches.first().cloned().ok_or_else(|| {
        format!(
            "prepared rustc-private directory `{}` has no `{prefix}*` artifact",
            directory.display()
        )
    })?;
    if matches.len() != 1 {
        return Err(format!(
            "prepared rustc-private directory `{}` has multiple `{prefix}*` artifacts",
            directory.display()
        ));
    }
    Ok(artifact)
}

fn has_library_extension(path: &Path) -> bool {
    path.extension()
        .and_then(OsStr::to_str)
        .is_some_and(|extension| LIBRARY_EXTENSIONS.contains(&extension))
}

fn plain_files_have_identical_bytes(left: &Path, right: &Path) -> Result<bool, String> {
    let left_metadata = plain_file_metadata(left, "prepared rustc-private artifact")?;
    let right_metadata = plain_file_metadata(right, "selected compiler artifact")?;
    if left_metadata.len() != right_metadata.len() {
        return Ok(false);
    }

    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;

        if left_metadata.dev() == right_metadata.dev() && left_metadata.ino() == right_metadata.ino() {
            return Ok(true);
        }
    }

    let left_path = left.to_owned();
    let right_path = right.to_owned();
    let left_file = fs::File::open(&left_path)
        .map_err(|error| format!("cannot open artifact `{}` for comparison: {error}", left_path.display()))?;
    let right_file = fs::File::open(&right_path).map_err(|error| {
        format!(
            "cannot open artifact `{}` for comparison: {error}",
            right_path.display()
        )
    })?;
    let mut left = BufReader::new(left_file);
    let mut right = BufReader::new(right_file);
    let mut left_buffer = [0_u8; 64 * 1024];
    let mut right_buffer = [0_u8; 64 * 1024];
    loop {
        let left_read = left
            .read(&mut left_buffer)
            .map_err(|error| format!("cannot read `{}` for comparison: {error}", left_path.display()))?;
        let right_read = right
            .read(&mut right_buffer)
            .map_err(|error| format!("cannot read `{}` for comparison: {error}", right_path.display()))?;
        if left_read != right_read || left_buffer[..left_read] != right_buffer[..right_read] {
            return Ok(false);
        }
        if left_read == 0 {
            return Ok(true);
        }
    }
}

fn plain_file_metadata(path: &Path, subject: &str) -> Result<fs::Metadata, String> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {subject} `{}`: {error}", path.display()))?;
    if !metadata.file_type().is_file() {
        return Err(format!("{subject} `{}` is not a plain file", path.display()));
    }
    Ok(metadata)
}

fn create_filtered_dependency_dir(dependency_dir: &Path, crate_name: &str) -> Result<PathBuf, String> {
    let parent = dependency_dir.parent().ok_or_else(|| {
        format!(
            "Cargo dependency search directory `{}` has no parent",
            dependency_dir.display()
        )
    })?;
    let base = parent.join(FILTERED_DEPS_DIR);
    fs::create_dir_all(&base)
        .map_err(|error| format!("cannot create filtered dependency root `{}`: {error}", base.display()))?;
    let base_metadata = fs::symlink_metadata(&base)
        .map_err(|error| format!("cannot inspect filtered dependency root `{}`: {error}", base.display()))?;
    if !base_metadata.file_type().is_dir() {
        return Err(format!(
            "filtered dependency root `{}` is not a plain directory",
            base.display()
        ));
    }
    let canonical_base = canonical_directory(&base, "filtered dependency root")?;
    if canonical_base.parent() != Some(parent) {
        return Err(format!(
            "filtered dependency root `{}` escaped Cargo target directory `{}`",
            canonical_base.display(),
            parent.display()
        ));
    }

    let sequence = NEXT_FILTER_DIR.fetch_add(1, Ordering::Relaxed);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| format!("system clock is before Unix epoch: {error}"))?
        .as_nanos();
    let filtered = canonical_base.join(format!("{crate_name}-{}-{nanos}-{sequence}", std::process::id()));
    fs::create_dir(&filtered).map_err(|error| {
        format!(
            "cannot create filtered dependency directory `{}`: {error}",
            filtered.display()
        )
    })?;

    let result = populate_filtered_dependency_dir(dependency_dir, &filtered);
    if let Err(error) = result {
        let _ = fs::remove_dir_all(&filtered);
        return Err(error);
    }
    Ok(filtered)
}

fn populate_filtered_dependency_dir(dependency_dir: &Path, filtered: &Path) -> Result<(), String> {
    for entry in fs::read_dir(dependency_dir).map_err(|error| {
        format!(
            "cannot read Cargo dependency directory `{}`: {error}",
            dependency_dir.display()
        )
    })? {
        let entry = entry.map_err(|error| {
            format!(
                "cannot read an entry in Cargo dependency directory `{}`: {error}",
                dependency_dir.display()
            )
        })?;
        let source = entry.path();
        let name = entry.file_name();
        if is_filtered_hashbrown_artifact(&name) {
            continue;
        }
        let metadata = fs::symlink_metadata(&source)
            .map_err(|error| format!("cannot inspect Cargo dependency `{}`: {error}", source.display()))?;
        if !metadata.file_type().is_file() {
            continue;
        }
        let destination = filtered.join(&name);
        fs::hard_link(&source, &destination).map_err(|error| {
            format!(
                "cannot link Cargo dependency `{}` into filtered directory `{}`: {error}",
                source.display(),
                filtered.display()
            )
        })?;
    }
    Ok(())
}

fn is_filtered_hashbrown_artifact(name: &OsStr) -> bool {
    let Some(name) = name.to_str() else {
        return false;
    };
    let Some(suffix) = name.strip_prefix("libhashbrown") else {
        return false;
    };
    (suffix.starts_with('-') || suffix.starts_with('.')) && has_library_extension(Path::new(name))
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::{
        ConfiguredOverlay, HOST_DIR_ENV, MAX_COMPILER_VERBOSE_VERSION_BYTES, MAX_PREPARED_MARKER_BYTES,
        OverlayEnvironment, TARGET_DIR_ENV, compiler_commit_hash_from_verbose_version, crate_uses_overlay,
        is_filtered_hashbrown_artifact, linked_rustc_commit_prefix,
    };

    const FIXTURE_COMMIT: &str = "0123456789abcdef0123456789abcdef01234567";
    const FIXTURE_LINKED_RUSTC_VERSION: &str = "1.99.0-dev (012345678 2026-07-22)";

    struct Fixture {
        root: PathBuf,
        sysroot: PathBuf,
        host_dir: PathBuf,
        target_dir: PathBuf,
    }

    impl Fixture {
        fn new(label: &str) -> Self {
            let nanos = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("clock after Unix epoch")
                .as_nanos();
            let root = std::env::temp_dir().join(format!("tippy-rustc-private-{label}-{}-{nanos}", std::process::id()));
            let build_host = root.join("build/test-host");
            let sysroot = build_host.join("stage2");
            let installed = sysroot.join("lib/rustlib/test-host/lib");
            let prepared = build_host
                .join("rustc-private-sysroots")
                .join("rustc-private-tool-stage1-test-host-fixture");
            let host_dir = prepared.join("host");
            let target_dir = prepared.join("test-host");
            fs::create_dir_all(&installed).expect("create selected sysroot fixture");
            fs::create_dir_all(&host_dir).expect("create prepared host fixture");
            fs::create_dir_all(&target_dir).expect("create prepared target fixture");
            fs::write(prepared.join(".rustc-commit-hash"), format!("{FIXTURE_COMMIT}\n"))
                .expect("write prepared marker");
            for (name, bytes) in [
                ("librustc_public-fixture.rlib", b"public".as_slice()),
                ("librustc_driver-fixture.so", b"driver".as_slice()),
            ] {
                fs::write(installed.join(name), bytes).expect("write installed artifact");
                fs::write(target_dir.join(name), bytes).expect("write prepared artifact");
            }
            Self {
                root,
                sysroot,
                host_dir,
                target_dir,
            }
        }

        fn environment(&self) -> OverlayEnvironment {
            OverlayEnvironment::new(Some(self.host_dir.clone()), Some(self.target_dir.clone()))
        }

        fn marker(&self) -> PathBuf {
            self.host_dir
                .parent()
                .expect("fixture host directory has a prepared parent")
                .join(".rustc-commit-hash")
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    #[test]
    fn fixed_allowlist_accepts_only_trust_mc_rustc_private_leaves() {
        for allowed in [
            "trust_mc_codegen_shared",
            "trust-mc-codegen-types",
            "trust_mc_kani_types",
            "trust_mc_compiler",
            "scanner",
        ] {
            assert!(crate_uses_overlay(allowed), "{allowed}");
        }
        for rejected in ["trust_mc", "trust_bmc", "hashbrown", "build_script_build", "rustc"] {
            assert!(!crate_uses_overlay(rejected), "{rejected}");
        }
    }

    #[test]
    fn compiler_version_parser_requires_one_complete_commit_hash() {
        let valid = format!("rustc 1.99.0-dev\ncommit-hash: {FIXTURE_COMMIT}\nhost: test-host\n");
        assert_eq!(
            compiler_commit_hash_from_verbose_version(&valid),
            Ok(FIXTURE_COMMIT.to_owned())
        );

        for invalid in [
            "rustc 1.99.0-dev\nhost: test-host\n".to_owned(),
            format!("commit-hash: {FIXTURE_COMMIT}\ncommit-hash: {FIXTURE_COMMIT}\n"),
            format!("commit-hash: {}\n", "a".repeat(39)),
            format!("commit-hash: {}\n", "a".repeat(41)),
            format!("commit-hash: {}g\n", "a".repeat(39)),
        ] {
            assert!(
                compiler_commit_hash_from_verbose_version(&invalid).is_err(),
                "accepted malformed compiler version output: {invalid:?}"
            );
        }

        let oversized = "x".repeat(MAX_COMPILER_VERBOSE_VERSION_BYTES as usize + 1);
        assert!(
            compiler_commit_hash_from_verbose_version(&oversized)
                .expect_err("oversized compiler output must fail")
                .contains("byte limit")
        );
    }

    #[test]
    fn linked_rustc_version_exposes_only_the_canonical_commit_prefix() {
        assert_eq!(
            linked_rustc_commit_prefix(FIXTURE_LINKED_RUSTC_VERSION),
            Ok(&FIXTURE_COMMIT[..9])
        );
        for invalid in [
            "1.99.0-dev",
            "1.99.0-dev (01234567 2026-07-22)",
            "1.99.0-dev (01234567g 2026-07-22)",
        ] {
            assert!(linked_rustc_commit_prefix(invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn exact_marker_rejects_a_stale_commit_with_the_same_linked_prefix() {
        let fixture = Fixture::new("same-prefix-stale");
        let compiler = fixture.sysroot.join("bin/rustc");
        let stale_commit = format!("{}{}", &FIXTURE_COMMIT[..9], "f".repeat(31));
        assert_ne!(stale_commit, FIXTURE_COMMIT);
        fs::write(fixture.marker(), format!("{stale_commit}\n")).expect("write stale prepared marker");

        let error = ConfiguredOverlay::for_frontend(Some(&compiler), Some(FIXTURE_COMMIT), fixture.environment())
            .expect_err("full compiler identity must reject a stale same-prefix marker");
        assert!(error.contains("not authenticated selected compiler commit"), "{error}");
    }

    #[test]
    fn driver_rejects_a_marker_incompatible_with_its_linked_rustc_prefix() {
        let fixture = Fixture::new("driver-prefix-mismatch");
        let error = ConfiguredOverlay::for_driver(
            Some(&fixture.sysroot),
            Some(FIXTURE_COMMIT),
            Some("1.99.0-dev (abcdef012 2026-07-22)"),
            fixture.environment(),
        )
        .expect_err("driver must reject a prepared marker from another linked compiler");
        assert!(
            error.contains("incompatible with linked rustc commit prefix"),
            "{error}"
        );
    }

    #[test]
    fn direct_driver_rejects_a_stale_marker_with_the_same_linked_prefix() {
        let fixture = Fixture::new("direct-driver-same-prefix-stale");
        let stale_commit = format!("{}{}", &FIXTURE_COMMIT[..9], "f".repeat(31));
        assert_ne!(stale_commit, FIXTURE_COMMIT);
        fs::write(fixture.marker(), format!("{stale_commit}\n")).expect("write stale prepared marker");

        let error = ConfiguredOverlay::for_driver(
            Some(&fixture.sysroot),
            Some(FIXTURE_COMMIT),
            Some(FIXTURE_LINKED_RUSTC_VERSION),
            fixture.environment(),
        )
        .expect_err("direct driver must require the authenticated sibling compiler's complete identity");
        assert!(
            error.contains("not authenticated sibling `trustc` compiler commit"),
            "{error}"
        );
    }

    #[test]
    fn direct_driver_requires_both_full_and_linked_compiler_identities() {
        let fixture = Fixture::new("direct-driver-missing-identities");
        for (full_commit, linked_version, expected) in [
            (
                None,
                Some(FIXTURE_LINKED_RUSTC_VERSION),
                "sibling `trustc` compiler identity",
            ),
            (Some(FIXTURE_COMMIT), None, "linked rustc compiler identity"),
        ] {
            let error = ConfiguredOverlay::for_driver(
                Some(&fixture.sysroot),
                full_commit,
                linked_version,
                fixture.environment(),
            )
            .expect_err("direct driver must reject an incomplete compiler identity");
            assert!(error.contains(expected), "{error}");
        }
    }

    #[test]
    fn prepared_marker_read_is_size_bounded() {
        let fixture = Fixture::new("oversized-marker");
        let compiler = fixture.sysroot.join("bin/rustc");
        fs::write(fixture.marker(), vec![b'a'; MAX_PREPARED_MARKER_BYTES as usize + 1])
            .expect("write oversized prepared marker");

        let error = ConfiguredOverlay::for_frontend(Some(&compiler), Some(FIXTURE_COMMIT), fixture.environment())
            .expect_err("oversized prepared marker must fail");
        assert!(error.contains("byte limit"), "{error}");
    }

    #[test]
    fn configured_overlay_is_bound_to_selected_toolchain_artifacts() {
        let fixture = Fixture::new("accepted");
        let compiler = fixture.sysroot.join("bin/rustc");
        let overlay = ConfiguredOverlay::for_frontend(Some(&compiler), Some(FIXTURE_COMMIT), fixture.environment())
            .expect("valid prepared overlay")
            .expect("configured overlay");
        let mut command = std::process::Command::new("targo");
        super::clear_overlay_command_environment(&mut command);
        overlay.configure_command(&mut command);
        let envs = command.get_envs().collect::<Vec<_>>();
        assert_eq!(
            envs.iter()
                .find(|(name, _)| *name == HOST_DIR_ENV)
                .and_then(|(_, value)| *value),
            Some(fixture.host_dir.canonicalize().unwrap().as_os_str())
        );
        assert_eq!(
            envs.iter()
                .find(|(name, _)| *name == TARGET_DIR_ENV)
                .and_then(|(_, value)| *value),
            Some(fixture.target_dir.canonicalize().unwrap().as_os_str())
        );
    }

    #[test]
    fn unbranded_frontend_rejects_configured_overlay_authority() {
        let fixture = Fixture::new("unbranded");
        assert!(
            ConfiguredOverlay::for_frontend(None, None, fixture.environment())
                .expect_err("unbranded frontend must reject overlay configuration")
                .contains("authenticated branded Tippy frontend")
        );
        assert_eq!(
            ConfiguredOverlay::for_frontend(None, None, OverlayEnvironment::default()),
            Ok(None)
        );
        assert!(
            ConfiguredOverlay::for_driver(None, None, None, fixture.environment())
                .expect_err("unbranded driver must reject overlay configuration")
                .contains("authenticated branded Tippy driver")
        );
        assert_eq!(
            ConfiguredOverlay::for_driver(None, None, None, OverlayEnvironment::default()),
            Ok(None)
        );
    }

    #[test]
    fn missing_outside_mixed_or_stale_prepared_directories_fail_closed() {
        let fixture = Fixture::new("rejected");
        let compiler = fixture.sysroot.join("bin/rustc");
        let missing_pair = OverlayEnvironment::new(Some(fixture.host_dir.clone()), None);
        assert!(
            ConfiguredOverlay::for_frontend(Some(&compiler), Some(FIXTURE_COMMIT), missing_pair)
                .expect_err("one configured directory must fail")
                .contains("configured together")
        );

        let missing = fixture.root.join("missing");
        let missing_dir = OverlayEnvironment::new(Some(fixture.host_dir.clone()), Some(missing));
        assert!(
            ConfiguredOverlay::for_frontend(Some(&compiler), Some(FIXTURE_COMMIT), missing_dir)
                .expect_err("missing target directory must fail")
                .contains("cannot canonicalize")
        );

        let outside_root = fixture.root.join("outside");
        let outside_host = outside_root.join("host");
        let outside_target = outside_root.join("test-host");
        fs::create_dir_all(&outside_host).expect("create outside host");
        fs::create_dir_all(&outside_target).expect("create outside target");
        let outside = OverlayEnvironment::new(Some(outside_host), Some(outside_target));
        assert!(
            ConfiguredOverlay::for_frontend(Some(&compiler), Some(FIXTURE_COMMIT), outside)
                .expect_err("outside overlay must fail")
                .contains("outside selected Trust prepared root")
        );

        let second_prepared = fixture.root.join("build/test-host/rustc-private-sysroots/second");
        let second_target = second_prepared.join("test-host");
        fs::create_dir_all(&second_target).expect("create mixed-root target");
        let mixed = OverlayEnvironment::new(Some(fixture.host_dir.clone()), Some(second_target));
        assert!(
            ConfiguredOverlay::for_frontend(Some(&compiler), Some(FIXTURE_COMMIT), mixed)
                .expect_err("mixed prepared roots must fail")
                .contains("share one prepared")
        );

        fs::write(fixture.target_dir.join("librustc_public-fixture.rlib"), b"stale!")
            .expect("replace prepared artifact");
        assert!(
            ConfiguredOverlay::for_frontend(Some(&compiler), Some(FIXTURE_COMMIT), fixture.environment())
                .expect_err("stale prepared artifact must fail")
                .contains("does not exactly match")
        );
    }

    #[test]
    fn allowed_crate_gets_prepared_paths_then_hashbrown_filtered_local_deps() {
        let fixture = Fixture::new("rewrite");
        let overlay = ConfiguredOverlay::for_driver(
            Some(&fixture.sysroot),
            Some(FIXTURE_COMMIT),
            Some(FIXTURE_LINKED_RUSTC_VERSION),
            fixture.environment(),
        )
        .unwrap()
        .unwrap();
        let deps = fixture.root.join("target/debug/deps");
        fs::create_dir_all(&deps).expect("create local deps");
        fs::write(deps.join("libhashbrown-local.rmeta"), b"wrong hashbrown").unwrap();
        fs::write(deps.join("libserde-local.rlib"), b"serde").unwrap();
        fs::write(deps.join("metadata.d"), b"metadata").unwrap();
        let args = vec![
            "rustc".to_owned(),
            "--crate-name".to_owned(),
            "trust_mc_compiler".to_owned(),
            "-L".to_owned(),
            format!("dependency={}", deps.display()),
            "-Cdebuginfo=1".to_owned(),
        ];
        let prepared = overlay
            .prepare_compiler_args(Some("trust_mc_compiler"), &args)
            .unwrap()
            .expect("allowlisted crate uses overlay");
        let rewritten = prepared.args();
        assert_eq!(rewritten[0], "rustc");
        assert_eq!(rewritten[1], "-L");
        assert_eq!(
            rewritten[2],
            format!("dependency={}", fixture.target_dir.canonicalize().unwrap().display())
        );
        assert_eq!(rewritten[3], "-L");
        assert_eq!(
            rewritten[4],
            format!("dependency={}", fixture.host_dir.canonicalize().unwrap().display())
        );
        let mirror = rewritten
            .windows(2)
            .filter_map(|pair| {
                (pair[0] == "-L")
                    .then(|| pair[1].strip_prefix("dependency="))
                    .flatten()
                    .map(PathBuf::from)
            })
            .find(|path| path.to_string_lossy().contains("filtered-deps"))
            .expect("filtered local dependency mirror");
        assert!(!mirror.join("libhashbrown-local.rmeta").exists());
        assert!(mirror.join("libserde-local.rlib").is_file());
        assert!(mirror.join("metadata.d").is_file());
        assert_eq!(rewritten.last().map(String::as_str), Some("-Cdebuginfo=1"));
    }

    #[test]
    fn non_allowlisted_crate_keeps_original_compiler_arguments() {
        let fixture = Fixture::new("non-allowlisted");
        let overlay = ConfiguredOverlay::for_driver(
            Some(&fixture.sysroot),
            Some(FIXTURE_COMMIT),
            Some(FIXTURE_LINKED_RUSTC_VERSION),
            fixture.environment(),
        )
        .unwrap()
        .unwrap();
        let args = ["rustc", "--crate-name", "ordinary", "-Ldependency=/tmp/deps"].map(String::from);
        assert!(
            overlay
                .prepare_compiler_args(Some("ordinary"), &args)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn only_hashbrown_library_artifacts_are_filtered() {
        for name in ["libhashbrown-local.rlib", "libhashbrown-local.rmeta", "libhashbrown.so"] {
            assert!(is_filtered_hashbrown_artifact(Path::new(name).as_os_str()));
        }
        for name in [
            "libhashbrown-local.d",
            "hashbrown-local.rlib",
            "libhashbrownish-local.rlib",
            "libserde-local.rlib",
        ] {
            assert!(!is_filtered_hashbrown_artifact(Path::new(name).as_os_str()));
        }
    }
}
