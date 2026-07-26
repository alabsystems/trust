// Native compile probe and runtime library path management for the discovered trustc.
//
// Runs a tiny test crate through the candidate compiler to detect whether the trust
// verification driver is available and whether it speaks the JSON transport. Also
// sets the dynamic-loader search paths the in-tree compiler needs for non-installed
// builds (build/host/stage{1,2,3}).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::env;
use std::ffi::OsString;
use std::io::{self, Cursor, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::Duration;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_buildcache::BuildCache;

use super::discovery::{NativeRustcCapabilities, canonicalize_or_self};
use super::process_environment::scrub_proof_compiler_authority_env;
use super::transport::parse_compiler_stderr;
use crate::{bounded_process, input_limits};

// v7 requires the exact versioned coverage/function identity reconciliation;
// v6 accepted and cached nonce-bound count-only rows as authenticated coverage.
// Persisted positives require both generic JSON compatibility and the exact
// inventory; partial/negative observations remain invocation-local because
// loader/resource failures must not become sticky capability verdicts.
const CAPABILITY_PROBE_CACHE_SCHEMA_VERSION: u32 = 7;
const CAPABILITY_PROBE_CACHE_KEY_DOMAIN: &[u8] = b"targo-trust/native-capability-probe-cache/v7\n";
const CAPABILITY_PROBE_CRATE: &str = "trust_verify_probe";
const CAPABILITY_PROBE_MAX_STREAM_BYTES: usize = 64 * 1024 * 1024;
const CAPABILITY_PROBE_TIMEOUT: Duration = Duration::from_secs(5 * 60);

pub(crate) const TRUSTD_RUNTIME_CLOSURE_SCHEMA: &str = "trust.trustd-runtime-closure.v2";
const TRUSTD_RUNTIME_CLOSURE_DOMAIN: &[u8] =
    b"trust/trustd-runtime-closure/v2\0system-default-only\0none\0";
const TRUSTD_RUNTIME_INSPECTOR_MAX_STREAM_BYTES: usize = 4 * 1024 * 1024;
const TRUSTD_RUNTIME_INSPECTOR_TIMEOUT: Duration = Duration::from_secs(10);
const TRUSTD_RUNTIME_MAX_DEPENDENCIES: usize = 256;
const TRUSTD_RUNTIME_MAX_DEPENDENCY_BYTES: usize = 4 * 1024;

/// Exact runtime authority admitted for release-candidate `trustd` launches.
///
/// Unlike compiler tools, `trustd` has no release requirement for an in-tree
/// rustc-driver search path. Its candidate is therefore launched with a fully
/// cleared environment and the platform loader's system defaults only. The
/// empty path and entry lists are security-significant: a repo-local dylib,
/// symlink, or mutable build directory can never enter this closure. The
/// candidate's native load commands are inspected separately and bound here;
/// on macOS only a thin Mach-O with absolute SIP/system dependencies and the
/// system dyld is admissible. The candidate and its complete root-to-leaf path
/// must also be immutable to group/other users, symlink-free, and owned by an
/// immutable root prefix followed by the effective user. Path-based `exec`
/// still cannot atomically bind an open file descriptor against that same
/// effective user, so the evidence states the release-ceremony requirement
/// that no other same-UID writer runs concurrently.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct TrustdRuntimeClosure {
    pub(crate) schema_version: String,
    pub(crate) policy: String,
    pub(crate) loader_environment: String,
    pub(crate) loader_variable: Option<String>,
    pub(crate) search_paths: Vec<String>,
    pub(crate) directory_entries: Vec<String>,
    pub(crate) concurrent_writer_policy: String,
    pub(crate) native_format: String,
    pub(crate) inspector_path: String,
    pub(crate) inspector_sha256: String,
    pub(crate) system_dependencies: Vec<String>,
    pub(crate) closure_sha256: String,
}

impl TrustdRuntimeClosure {
    fn from_macho_observation(
        inspector_path: String,
        inspector_sha256: String,
        system_dependencies: Vec<String>,
    ) -> Result<Self, String> {
        let closure_sha256 = trustd_runtime_closure_sha256(
            "mach-o-thin",
            "exclusive-same-uid-release-host",
            &inspector_path,
            &inspector_sha256,
            &system_dependencies,
        );
        let closure = Self {
            schema_version: TRUSTD_RUNTIME_CLOSURE_SCHEMA.to_string(),
            policy: "system-default-only".to_string(),
            loader_environment: "none".to_string(),
            loader_variable: None,
            search_paths: Vec::new(),
            directory_entries: Vec::new(),
            concurrent_writer_policy: "exclusive-same-uid-release-host".to_string(),
            native_format: "mach-o-thin".to_string(),
            inspector_path,
            inspector_sha256,
            system_dependencies,
            closure_sha256,
        };
        closure.validate()?;
        Ok(closure)
    }

    pub(crate) fn validate(&self) -> Result<(), String> {
        if self.schema_version != TRUSTD_RUNTIME_CLOSURE_SCHEMA
            || self.policy != "system-default-only"
            || self.loader_environment != "none"
            || self.loader_variable.is_some()
            || !self.search_paths.is_empty()
            || !self.directory_entries.is_empty()
            || self.concurrent_writer_policy != "exclusive-same-uid-release-host"
            || self.native_format != "mach-o-thin"
            || !trusted_macho_inspector_path(Path::new(&self.inspector_path))
            || !trust_types::digest::is_stable_sha256_hex(&self.inspector_sha256)
            || self.system_dependencies.len() > TRUSTD_RUNTIME_MAX_DEPENDENCIES
        {
            return Err(
                "trustd runtime closure must be the canonical empty loader environment with a bound native system dependency set"
                    .to_string(),
            );
        }
        for (index, dependency) in self.system_dependencies.iter().enumerate() {
            validate_macho_system_path(dependency, "dependency")?;
            if self.system_dependencies[..index].contains(dependency) {
                return Err("trustd runtime closure contains a duplicate system dependency".into());
            }
        }
        let expected_sha256 = trustd_runtime_closure_sha256(
            &self.native_format,
            &self.concurrent_writer_policy,
            &self.inspector_path,
            &self.inspector_sha256,
            &self.system_dependencies,
        );
        if self.closure_sha256 != expected_sha256 {
            return Err(
                "trustd runtime closure digest does not bind its inspector and ordered dependency set"
                    .into(),
            );
        }
        Ok(())
    }

    pub(crate) fn validate_for_candidate(&self, candidate: &Path) -> Result<(), String> {
        self.validate()?;
        let observed = inspect_trustd_runtime_closure(candidate)?;
        if &observed != self {
            return Err(
                "trustd native load commands do not exactly match the admitted runtime closure"
                    .to_string(),
            );
        }
        Ok(())
    }
}

/// Configure a candidate `trustd` launch with no ambient process or loader
/// authority. The executable path must be absolute and hash-bound by the
/// caller; no PATH lookup is available after this call.
pub(crate) fn apply_trustd_runtime_closure(
    command: &mut Command,
    candidate: &Path,
    closure: &TrustdRuntimeClosure,
) -> Result<(), String> {
    closure.validate_for_candidate(candidate)?;
    command.env_clear();
    Ok(())
}


fn hash_runtime_closure_field(hasher: &mut Sha256, value: &str) {
    hasher.update((value.len() as u64).to_le_bytes());
    hasher.update(value.as_bytes());
}

fn trustd_runtime_closure_sha256(
    native_format: &str,
    concurrent_writer_policy: &str,
    inspector_path: &str,
    inspector_sha256: &str,
    dependencies: &[String],
) -> String {
    let mut hasher = Sha256::new();
    hasher.update(TRUSTD_RUNTIME_CLOSURE_DOMAIN);
    hash_runtime_closure_field(&mut hasher, native_format);
    hash_runtime_closure_field(&mut hasher, concurrent_writer_policy);
    hash_runtime_closure_field(&mut hasher, inspector_path);
    hash_runtime_closure_field(&mut hasher, inspector_sha256);
    hasher.update((dependencies.len() as u64).to_le_bytes());
    for dependency in dependencies {
        hash_runtime_closure_field(&mut hasher, dependency);
    }
    format!("{:x}", hasher.finalize())
}

fn trusted_macho_inspector_path(path: &Path) -> bool {
    matches!(
        path.to_str(),
        Some("/Library/Developer/CommandLineTools/usr/bin/llvm-otool")
            | Some(
                "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/llvm-otool"
            )
            | Some(
                "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/otool"
            )
    )
}

fn validate_macho_system_path(path: &str, label: &str) -> Result<(), String> {
    if path.is_empty()
        || path.len() > TRUSTD_RUNTIME_MAX_DEPENDENCY_BYTES
        || path.chars().any(char::is_control)
        || path.contains("//")
        || !path.starts_with('/')
        || path
            .split('/')
            .skip(1)
            .any(|component| component.is_empty() || component == "." || component == "..")
        || !(path.starts_with("/usr/lib/") || path.starts_with("/System/Library/"))
    {
        return Err(format!(
            "trustd Mach-O {label} must be an absolute normalized system-library path"
        ));
    }
    Ok(())
}

#[cfg(target_os = "macos")]
fn exact_file_sha256(path: &Path) -> Result<String, String> {
    let mut file = std::fs::File::open(path)
        .map_err(|error| format!("could not open native inspector {}: {error}", path.display()))?;
    let metadata = file.metadata().map_err(|error| {
        format!("could not inspect native inspector {}: {error}", path.display())
    })?;
    if !metadata.file_type().is_file() {
        return Err(format!("native inspector {} is not an exact regular file", path.display()));
    }
    let mut hasher = Sha256::new();
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = file.read(&mut buffer).map_err(|error| {
            format!("could not hash native inspector {}: {error}", path.display())
        })?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

#[cfg(target_os = "macos")]
fn trusted_macho_inspector() -> Result<(PathBuf, String), String> {
    const CANDIDATES: &[&str] = &[
        "/Library/Developer/CommandLineTools/usr/bin/otool",
        "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/otool",
    ];
    for candidate in CANDIDATES {
        let Ok(path) = std::fs::canonicalize(candidate) else {
            continue;
        };
        if !trusted_macho_inspector_path(&path) {
            continue;
        }
        if validate_root_owned_inspector_chain(&path).is_err() {
            continue;
        }
        let sha256 = exact_file_sha256(&path)?;
        return Ok((path, sha256));
    }
    Err(
        "no fixed, canonical, root-owned llvm-otool inspector is available; /usr/bin/otool and PATH lookup are not release authority"
            .to_string(),
    )
}

#[cfg(target_os = "macos")]
fn validate_root_owned_inspector_chain(path: &Path) -> Result<(), String> {
    use std::os::unix::fs::MetadataExt as _;
    use std::path::Component;

    if !path.is_absolute() {
        return Err("native inspector path is not absolute".to_string());
    }
    let mut current = PathBuf::from("/");
    let root_metadata = std::fs::symlink_metadata(&current)
        .map_err(|error| format!("could not inspect native inspector authority /: {error}"))?;
    if !root_metadata.file_type().is_dir()
        || root_metadata.uid() != 0
        || root_metadata.mode() & 0o022 != 0
    {
        return Err(
            "native inspector root authority is not a root-owned immutable directory".to_string()
        );
    }
    let components = path.components().collect::<Vec<_>>();
    for (index, component) in components.iter().enumerate() {
        match component {
            Component::RootDir => continue,
            Component::Normal(component) => current.push(component),
            _ => return Err("native inspector path is not normalized".to_string()),
        }
        let metadata = std::fs::symlink_metadata(&current).map_err(|error| {
            format!("could not inspect native inspector authority {}: {error}", current.display())
        })?;
        let is_leaf = index + 1 == components.len();
        if metadata.uid() != 0 || metadata.mode() & 0o022 != 0 {
            return Err(format!(
                "native inspector authority {} is not root-owned and immutable",
                current.display()
            ));
        }
        if is_leaf {
            if !metadata.file_type().is_file() || metadata.mode() & 0o111 == 0 {
                return Err(format!(
                    "native inspector {} is not an exact executable file",
                    current.display()
                ));
            }
        } else if !metadata.file_type().is_dir() {
            return Err(format!(
                "native inspector ancestor {} is not an exact directory",
                current.display()
            ));
        }
    }
    Ok(())
}

#[cfg(target_os = "macos")]
fn validate_trustd_candidate_owner(
    path: &Path,
    owner_uid: u32,
    effective_uid: u32,
    effective_user_prefix_started: &mut bool,
) -> Result<(), String> {
    if owner_uid == effective_uid {
        *effective_user_prefix_started = true;
        return Ok(());
    }
    if owner_uid == 0 && !*effective_user_prefix_started {
        return Ok(());
    }
    Err(format!(
        "candidate trustd authority {} is owned by uid {owner_uid}; expected an immutable root prefix followed by effective uid {effective_uid}",
        path.display()
    ))
}

/// Validate the filesystem authority used by path-based candidate execution.
///
/// A root-owned immutable prefix (for example `/` and `/Users`) may precede
/// the effective user's non-group/world-writable tree. Once an
/// effective-user-owned component is reached, a different owner is rejected.
/// This removes ordinary POSIX group/other mode-bit authority. Root, host ACL
/// policy, and other privileged mutation mechanisms remain part of the host
/// TCB; concurrent effective-user mutation is the separately disclosed
/// release-ceremony exclusion.
#[cfg(target_os = "macos")]
fn validate_trustd_candidate_authority(candidate: &Path) -> Result<PathBuf, String> {
    use std::os::unix::fs::MetadataExt as _;
    use std::path::Component;

    if !candidate.is_absolute() {
        return Err("candidate trustd path must be absolute".to_string());
    }
    let components = candidate.components().collect::<Vec<_>>();
    if !matches!(components.first(), Some(Component::RootDir))
        || components.len() < 2
        || components[1..].iter().any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err("candidate trustd path must be absolute and normalized".to_string());
    }
    let canonical = std::fs::canonicalize(candidate).map_err(|error| {
        format!("could not canonicalize candidate trustd {}: {error}", candidate.display())
    })?;
    if canonical != candidate {
        return Err(
            "candidate trustd path must be canonical and contain no symlink components".to_string()
        );
    }

    // SAFETY: geteuid has no preconditions and only observes process identity.
    let effective_uid = unsafe { libc::geteuid() };
    let mut effective_user_prefix_started = false;
    let mut current = PathBuf::from("/");
    let root_metadata = std::fs::symlink_metadata(&current)
        .map_err(|error| format!("could not inspect candidate trustd authority /: {error}"))?;
    if !root_metadata.file_type().is_dir()
        || root_metadata.file_type().is_symlink()
        || root_metadata.mode() & 0o022 != 0
    {
        return Err(
            "candidate trustd root authority is not an exact immutable directory".to_string()
        );
    }
    validate_trustd_candidate_owner(
        &current,
        root_metadata.uid(),
        effective_uid,
        &mut effective_user_prefix_started,
    )?;

    let normal_components = &components[1..];
    for (index, component) in normal_components.iter().enumerate() {
        let Component::Normal(component) = component else {
            unreachable!("candidate components were normalized above");
        };
        current.push(component);
        let metadata = std::fs::symlink_metadata(&current).map_err(|error| {
            format!("could not inspect candidate trustd authority {}: {error}", current.display())
        })?;
        let is_leaf = index + 1 == normal_components.len();
        if metadata.file_type().is_symlink() {
            return Err(format!("candidate trustd authority {} is a symlink", current.display()));
        }
        if metadata.mode() & 0o022 != 0 {
            return Err(format!(
                "candidate trustd authority {} is writable by group or other users (mode {:o})",
                current.display(),
                metadata.mode() & 0o777
            ));
        }
        validate_trustd_candidate_owner(
            &current,
            metadata.uid(),
            effective_uid,
            &mut effective_user_prefix_started,
        )?;
        if is_leaf {
            if !metadata.file_type().is_file() || metadata.mode() & 0o111 == 0 {
                return Err(format!(
                    "candidate trustd {} is not an exact executable regular file",
                    current.display()
                ));
            }
        } else if !metadata.file_type().is_dir() {
            return Err(format!(
                "candidate trustd ancestor {} is not an exact directory",
                current.display()
            ));
        }
    }

    let canonical_after = std::fs::canonicalize(candidate).map_err(|error| {
        format!(
            "could not re-canonicalize candidate trustd {} after authority validation: {error}",
            candidate.display()
        )
    })?;
    if canonical_after != canonical {
        return Err("candidate trustd path changed during authority validation".to_string());
    }
    Ok(canonical)
}

#[cfg(target_os = "macos")]
fn run_macho_inspector(
    inspector: &Path,
    inspector_sha256: &str,
    flag: &str,
    candidate: &Path,
) -> Result<String, String> {
    if exact_file_sha256(inspector)?.as_str() != inspector_sha256 {
        return Err("native inspector changed before execution".to_string());
    }
    let mut command = Command::new(inspector);
    command.arg(flag).arg(candidate).env_clear().current_dir("/").stdin(Stdio::null());
    let output = bounded_process::output(
        &mut command,
        "canonical trustd Mach-O inspection",
        TRUSTD_RUNTIME_INSPECTOR_MAX_STREAM_BYTES,
        TRUSTD_RUNTIME_INSPECTOR_TIMEOUT,
    )?;
    if !output.status.success() {
        return Err(format!("canonical native inspector {flag} exited {}", output.status));
    }
    if !output.stderr.is_empty() {
        return Err(format!("canonical native inspector {flag} wrote to stderr"));
    }
    if exact_file_sha256(inspector)?.as_str() != inspector_sha256 {
        return Err("native inspector changed during execution".to_string());
    }
    String::from_utf8(output.stdout)
        .map_err(|_| format!("canonical native inspector {flag} output was not UTF-8"))
}

#[cfg(target_os = "macos")]
fn parse_macho_dependencies(output: &str, candidate: &Path) -> Result<Vec<String>, String> {
    let candidate =
        candidate.to_str().ok_or_else(|| "candidate trustd path is not UTF-8".to_string())?;
    let mut lines = output.lines();
    if lines.next() != Some(format!("{candidate}:").as_str()) {
        return Err(
            "native dependency inspection did not identify exactly one thin candidate slice"
                .to_string(),
        );
    }
    let mut dependencies = Vec::new();
    for line in lines {
        let Some(line) = line.strip_prefix('\t') else {
            return Err("native dependency inspection had a non-canonical record".to_string());
        };
        let Some((dependency, versions)) = line.split_once(" (compatibility version ") else {
            return Err("native dependency inspection omitted compatibility metadata".to_string());
        };
        if !versions.ends_with(')') || !versions.contains(", current version ") {
            return Err("native dependency inspection had malformed version metadata".to_string());
        }
        validate_macho_system_path(dependency, "dependency")?;
        if dependencies.iter().any(|existing| existing == dependency) {
            return Err("candidate trustd contains a duplicate native dependency".to_string());
        }
        if dependencies.len() == TRUSTD_RUNTIME_MAX_DEPENDENCIES {
            return Err("candidate trustd native dependency count exceeds the bound".to_string());
        }
        dependencies.push(dependency.to_string());
    }
    Ok(dependencies)
}

#[cfg(target_os = "macos")]
fn parse_macho_load_commands(
    output: &str,
    candidate: &Path,
    expected_dependencies: &[String],
) -> Result<(), String> {
    let candidate =
        candidate.to_str().ok_or_else(|| "candidate trustd path is not UTF-8".to_string())?;
    let mut lines = output.lines();
    if lines.next() != Some(format!("{candidate}:").as_str()) {
        return Err(
            "native load-command inspection did not identify exactly one thin candidate slice"
                .to_string(),
        );
    }
    let mut pending_path_command: Option<&str> = None;
    let mut dependencies = Vec::new();
    let mut dylinkers = Vec::new();
    for line in lines {
        let line = line.trim();
        if let Some(command) = line.strip_prefix("cmd ") {
            if pending_path_command.is_some() {
                return Err("native load command omitted its bound path".to_string());
            }
            match command {
                "LC_RPATH" => {
                    return Err("candidate trustd contains a forbidden LC_RPATH".to_string());
                }
                "LC_DYLD_ENVIRONMENT" => {
                    return Err(
                        "candidate trustd contains a forbidden LC_DYLD_ENVIRONMENT".to_string()
                    );
                }
                "LC_LOAD_DYLIB"
                | "LC_LOAD_WEAK_DYLIB"
                | "LC_REEXPORT_DYLIB"
                | "LC_LOAD_UPWARD_DYLIB"
                | "LC_LAZY_LOAD_DYLIB" => {
                    pending_path_command = Some("dependency");
                }
                "LC_LOAD_DYLINKER" => pending_path_command = Some("dynamic linker"),
                other
                    if other.contains("DYLIB")
                        || (other.contains("DYLINKER") && other != "LC_LOAD_DYLINKER") =>
                {
                    return Err(format!(
                        "candidate trustd contains unsupported loader command {other}"
                    ));
                }
                _ => {}
            }
            continue;
        }
        let Some(label) = pending_path_command else {
            continue;
        };
        let Some(name) = line.strip_prefix("name ") else {
            continue;
        };
        let Some((path, offset)) = name.rsplit_once(" (offset ") else {
            return Err(format!("native {label} load command has malformed path metadata"));
        };
        if !offset.ends_with(')') {
            return Err(format!("native {label} load command has malformed offset metadata"));
        }
        match label {
            "dependency" => {
                validate_macho_system_path(path, label)?;
                dependencies.push(path.to_string());
            }
            "dynamic linker" if path == "/usr/lib/dyld" => dylinkers.push(path.to_string()),
            "dynamic linker" => {
                return Err(
                    "candidate trustd dynamic linker must be exactly /usr/lib/dyld".to_string()
                );
            }
            _ => unreachable!("closed native path command labels"),
        }
        pending_path_command = None;
    }
    if pending_path_command.is_some() {
        return Err("native load command omitted its bound path".to_string());
    }
    if dylinkers != ["/usr/lib/dyld"] {
        return Err("candidate trustd must bind exactly one system dynamic linker".to_string());
    }
    if dependencies != expected_dependencies {
        return Err(
            "native dependency summary does not exactly match ordered Mach-O load commands"
                .to_string(),
        );
    }
    Ok(())
}

#[cfg(target_os = "macos")]
pub(crate) fn inspect_trustd_runtime_closure(
    candidate: &Path,
) -> Result<TrustdRuntimeClosure, String> {
    let candidate = validate_trustd_candidate_authority(candidate)?;
    let (inspector, inspector_sha256) = trusted_macho_inspector()?;
    let dependencies_output = run_macho_inspector(&inspector, &inspector_sha256, "-L", &candidate)?;
    let dependencies = parse_macho_dependencies(&dependencies_output, &candidate)?;
    let commands_output = run_macho_inspector(&inspector, &inspector_sha256, "-l", &candidate)?;
    parse_macho_load_commands(&commands_output, &candidate, &dependencies)?;
    TrustdRuntimeClosure::from_macho_observation(
        inspector
            .to_str()
            .ok_or_else(|| "canonical native inspector path is not UTF-8".to_string())?
            .to_string(),
        inspector_sha256,
        dependencies,
    )
}

#[cfg(not(target_os = "macos"))]
pub(crate) fn inspect_trustd_runtime_closure(
    _candidate: &Path,
) -> Result<TrustdRuntimeClosure, String> {
    Err("trustd runtime-closure inspection is unsupported on this host and fails closed"
        .to_string())
}

const TRUST_VERIFY_PROBE_SOURCE: &str = r#"
// Probe body must be VERIFIABLE under strict batteries-on verification with
// whole-crate coverage: `a + b` was refutable (usize overflow) and only passed
// while dead pub fns were never demanded (the demand-truncation defect). The
// wrapping form is total, so the probe proves cleanly while still exercising
// the arithmetic lowering + JSON transport.
pub fn trust_verify_probe(a: usize, b: usize) -> usize {
    a.wrapping_add(b)
}
fn main() {}
"#;

#[derive(Debug, Clone, Copy, Deserialize, Serialize)]
struct NativeCapabilityProbeCacheEntry {
    schema_version: u32,
    trust_verify: bool,
    json_transport: bool,
    authenticated_coverage: bool,
}

fn push_unique_existing_dir(paths: &mut Vec<PathBuf>, candidate: PathBuf) {
    let candidate = canonicalize_or_self(candidate);
    if candidate.is_dir() && !paths.iter().any(|path| path == &candidate) {
        paths.push(candidate);
    }
}

fn push_sorted_unique_existing_dirs(
    paths: &mut Vec<PathBuf>,
    candidates: impl IntoIterator<Item = PathBuf>,
) {
    let mut candidates = candidates
        .into_iter()
        .map(canonicalize_or_self)
        .filter(|path| path.is_dir())
        .collect::<Vec<_>>();
    candidates.sort();
    candidates.dedup();
    for candidate in candidates {
        if !paths.iter().any(|path| path == &candidate) {
            paths.push(candidate);
        }
    }
}

pub(super) fn native_runtime_library_paths(rustc: &Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    let Some(bin_dir) = rustc.parent() else {
        return paths;
    };
    let Some(sysroot) = bin_dir.parent() else {
        return paths;
    };

    push_unique_existing_dir(&mut paths, sysroot.join("lib"));

    let rustlib_root = sysroot.join("lib").join("rustlib");
    if let Ok(entries) = std::fs::read_dir(&rustlib_root) {
        push_sorted_unique_existing_dirs(
            &mut paths,
            entries.flatten().map(|entry| entry.path().join("lib")),
        );
    }

    if let (Some(build_dir), Some(stage_name)) =
        (sysroot.parent(), sysroot.file_name().and_then(|name| name.to_str()))
    {
        let rustc_deps_root = build_dir.join(format!("{stage_name}-rustc"));
        if let Ok(entries) = std::fs::read_dir(&rustc_deps_root) {
            push_sorted_unique_existing_dirs(
                &mut paths,
                entries.flatten().map(|entry| entry.path().join("release").join("deps")),
            );
        }
    }

    // Preserve semantic loader precedence between tiers: the sysroot's direct
    // libraries, then target rustlibs, then compiler-build dependency outputs.
    // Directory enumeration is sorted *within* each tier above so independent
    // reconstructors still produce one canonical value.
    paths
}

pub(super) fn trusted_runtime_search_path_value(paths: Vec<PathBuf>) -> Option<OsString> {
    if paths.is_empty() { None } else { env::join_paths(paths).ok() }
}

fn runtime_library_path_var() -> Option<&'static str> {
    if cfg!(windows) {
        None
    } else if cfg!(target_os = "macos") {
        Some("DYLD_LIBRARY_PATH")
    } else if cfg!(target_os = "aix") {
        Some("LIBPATH")
    } else {
        Some("LD_LIBRARY_PATH")
    }
}

/// Return the complete loader environment reconstructed from the selected
/// stage toolchain. Callers that clear their environment must use this exact
/// value before launching verified Targo or one of its sibling tools.
pub(crate) fn native_runtime_environment(rustc: &Path) -> Option<(&'static str, OsString)> {
    let variable = runtime_library_path_var()?;
    let value = trusted_runtime_search_path_value(native_runtime_library_paths(rustc))?;
    Some((variable, value))
}

fn is_dynamic_loader_authority_env(variable: &OsString) -> bool {
    let Some(variable) = variable.to_str() else {
        return false;
    };
    let variable = variable.to_ascii_uppercase();
    variable.starts_with("LD_")
        || variable.starts_with("DYLD_")
        || variable.starts_with("LDR_")
        || variable.starts_with("_RLD")
        || matches!(variable.as_str(), "LIBPATH" | "SHLIB_PATH")
}

pub(crate) fn apply_native_runtime_env(cmd: &mut Command, rustc: &Path) {
    // CFG_RELEASE/CFG_VERSION are rustc *build-time* inputs, not runtime loader
    // controls. Injecting a frozen value here leaked stale release identity
    // into every user build script and made proof builds semantically differ
    // from the corresponding Targo build. The selected compiler already has
    // its release identity compiled in; only its dynamic-library search path
    // belongs in this runtime helper.
    // Dynamic-loader variables are code-injection channels into the hashed
    // compiler process. Clear the complete platform namespaces and rebuild the
    // one required search path solely from the selected toolchain.
    for variable in [
        "LD_AUDIT",
        "LD_LIBRARY_PATH",
        "LD_PRELOAD",
        "DYLD_FALLBACK_FRAMEWORK_PATH",
        "DYLD_FALLBACK_LIBRARY_PATH",
        "DYLD_FRAMEWORK_PATH",
        "DYLD_INSERT_LIBRARIES",
        "DYLD_LIBRARY_PATH",
        "LIBPATH",
        "SHLIB_PATH",
        "LDR_PRELOAD",
        "LDR_AUDIT",
        "_RLD_LIST",
        "_RLDN32_LIST",
        "_RLD64_LIST",
    ] {
        cmd.env_remove(variable);
    }
    for (variable, _) in env::vars_os() {
        if is_dynamic_loader_authority_env(&variable) {
            cmd.env_remove(variable);
        }
    }

    if let Some((variable, value)) = native_runtime_environment(rustc) {
        cmd.env(variable, value);
    }
}

fn output_contains_json_transport(output: &Output) -> bool {
    std::str::from_utf8(&output.stderr).is_ok_and(stderr_contains_json_transport)
}

fn stderr_contains_json_transport(stderr: &str) -> bool {
    stderr.lines().any(|line| trust_types::parse_transport_line(line).is_some())
}

fn stderr_contains_authenticated_json_transport(stderr: &str, expected_session: &str) -> bool {
    let Ok(parsed) = parse_compiler_stderr(Cursor::new(stderr), false)
        .require_raw_coverage_authentication(expected_session, true)
    else {
        return false;
    };
    let coverage = parsed.coverage_rows;
    matches!(
        coverage.as_slice(),
        [summary]
            if summary.crate_name == CAPABILITY_PROBE_CRATE
                && summary.package_name.is_empty()
                && !summary.primary_package
                && summary.verification_session == expected_session
                && summary.is_complete()
    )
}

fn output_contains_native_verification_signal(output: &Output) -> bool {
    std::str::from_utf8(&output.stderr).is_ok_and(|stderr| {
        stderr.contains(trust_types::TRANSPORT_PREFIX)
            || stderr.contains("=== Trust Verification Report ===")
            || stderr.contains("note: Trust [")
            || stderr.contains("Trust [")
    })
}

fn native_capability_probe_cache_dir() -> PathBuf {
    BuildCache::default_root().join("native-capability-probes").join("v7")
}

fn native_capability_probe_cache_path(cache_key: &str) -> PathBuf {
    native_capability_probe_cache_dir().join(format!("{cache_key}.json"))
}

fn is_dynamic_library_name(name: &str) -> bool {
    name.ends_with(".dylib")
        || name.ends_with(".dll")
        || name.ends_with(".so")
        || name.contains(".so.")
}

fn is_rust_metadata_or_library_name(name: &str) -> bool {
    is_dynamic_library_name(name) || name.ends_with(".rlib") || name.ends_with(".rmeta")
}

fn is_native_capability_driver_artifact(path: &Path) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    let name = name.to_ascii_lowercase();

    // The launched trustc can be a thin executable whose -Z support lives in
    // rustc_driver. Trust dynamic libraries are included when split out, while
    // static Trust crates are covered by either the driver dylib or rustc bytes.
    ((name.starts_with("librustc_driver") || name.starts_with("rustc_driver"))
        && is_rust_metadata_or_library_name(&name))
        || ((name.starts_with("libtrust_") || name.starts_with("trust_"))
            && is_dynamic_library_name(&name))
}

fn native_capability_driver_artifacts(rustc: &Path) -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    if let Some(bin_dir) = rustc.parent() {
        push_unique_existing_dir(&mut dirs, bin_dir.to_path_buf());
    }
    for dir in native_runtime_library_paths(rustc) {
        push_unique_existing_dir(&mut dirs, dir);
    }

    let mut artifacts = Vec::new();
    for dir in dirs {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_file() && is_native_capability_driver_artifact(&path) {
                artifacts.push(canonicalize_or_self(path));
            }
        }
    }
    artifacts.sort();
    artifacts.dedup();
    artifacts
}

fn hash_file_component(hasher: &mut Sha256, label: &[u8], path: &Path) -> io::Result<()> {
    let path = canonicalize_or_self(path.to_path_buf());
    let path_bytes = path.as_os_str().as_encoded_bytes();
    hasher.update(label);
    hasher.update(b":path:");
    hasher.update((path_bytes.len() as u64).to_le_bytes());
    hasher.update(path_bytes);

    let mut file = std::fs::File::open(&path)?;
    let file_len = file.metadata()?.len();
    hasher.update(b":bytes:");
    hasher.update(file_len.to_le_bytes());

    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    hasher.update(b"\n");
    Ok(())
}

fn native_capability_probe_cache_key(rustc: &Path) -> io::Result<String> {
    let mut hasher = Sha256::new();
    hasher.update(CAPABILITY_PROBE_CACHE_KEY_DOMAIN);
    hash_file_component(&mut hasher, b"rustc", rustc)?;
    for artifact in native_capability_driver_artifacts(rustc) {
        hash_file_component(&mut hasher, b"driver", &artifact)?;
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn read_cached_native_capabilities(cache_key: &str) -> Option<NativeRustcCapabilities> {
    let bytes = input_limits::read_bounded_file(
        &native_capability_probe_cache_path(cache_key),
        input_limits::MAX_RELEASE_METADATA_BYTES,
    )
    .ok()?;
    let entry: NativeCapabilityProbeCacheEntry = serde_json::from_slice(&bytes).ok()?;
    // A successful JSON probe is positive evidence about this exact compiler
    // artifact. A negative or partial row is only absence of a success signal:
    // the child may instead have hit a transient loader, filesystem, resource,
    // or execution failure. Never turn that absence into a sticky capability
    // verdict. This also ignores negative, partial, and pre-v7 rows written by
    // older Targo builds.
    if entry.schema_version != CAPABILITY_PROBE_CACHE_SCHEMA_VERSION
        || !entry.trust_verify
        || !entry.json_transport
        || !entry.authenticated_coverage
    {
        return None;
    }
    Some(NativeRustcCapabilities {
        trust_verify: true,
        json_transport: true,
        authenticated_coverage: true,
    })
}

fn write_cached_native_capabilities(
    cache_key: &str,
    capabilities: NativeRustcCapabilities,
) -> io::Result<()> {
    let path = native_capability_probe_cache_path(cache_key);
    let parent = path.parent().ok_or_else(|| {
        io::Error::new(io::ErrorKind::InvalidInput, "capability probe cache path has no parent")
    })?;
    std::fs::create_dir_all(parent)?;

    let entry = NativeCapabilityProbeCacheEntry {
        schema_version: CAPABILITY_PROBE_CACHE_SCHEMA_VERSION,
        trust_verify: capabilities.trust_verify,
        json_transport: capabilities.trust_verify && capabilities.json_transport,
        authenticated_coverage: capabilities.trust_verify
            && capabilities.json_transport
            && capabilities.authenticated_coverage,
    };
    let mut temp_file = tempfile::NamedTempFile::new_in(parent)?;
    serde_json::to_writer(&mut temp_file, &entry).map_err(io::Error::other)?;
    temp_file.write_all(b"\n")?;
    temp_file.persist(&path).map_err(|error| error.error)?;
    Ok(())
}

fn cache_native_capabilities(cache_key: Option<&str>, capabilities: NativeRustcCapabilities) {
    // Persist only a fully positive probe. The current probe protocol has no
    // typed "unsupported option" response that can distinguish unsupported
    // functionality from an arbitrary nonzero compiler exit.
    if capabilities.trust_verify
        && capabilities.json_transport
        && capabilities.authenticated_coverage
    {
        if let Some(cache_key) = cache_key {
            let _ = write_cached_native_capabilities(cache_key, capabilities);
        }
    }
}

struct NativeCompileProbe {
    output: Output,
    verification_session: Option<String>,
}

fn run_native_compile_probe(rustc: &Path, json_transport: bool) -> io::Result<NativeCompileProbe> {
    let probe_dir = tempfile::Builder::new().prefix("targo-trust-probe-").tempdir()?;
    harden_probe_dir_permissions(&probe_dir)?;
    let verification_session = json_transport
        .then(|| {
            probe_dir
                .path()
                .file_name()
                .and_then(|name| name.to_str())
                .filter(|name| !name.is_empty())
                .map(str::to_string)
                .ok_or_else(|| io::Error::other("capability probe session token is not UTF-8"))
        })
        .transpose()?;
    let src = probe_dir.path().join("probe.rs");
    let out = probe_dir.path().join("probe.rmeta");
    std::fs::write(&src, TRUST_VERIFY_PROBE_SOURCE)?;

    let mut cmd = Command::new(rustc);
    cmd.stdin(Stdio::null());
    scrub_proof_compiler_authority_env(&mut cmd);
    apply_native_runtime_env(&mut cmd, rustc);
    if let Some(sysroot) = rustc.parent().and_then(|p| p.parent()) {
        cmd.arg("--sysroot").arg(sysroot);
    }
    // Verification is batteries-on. A direct compiler invocation uses the
    // default `unscoped` role, which is deliberately in scope. The probe must
    // not impersonate Cargo-owned role/package metadata.
    // The capability probe's argv is fixed: it authenticates with its OWN
    // probe-scoped session below and deliberately receives no TRUSTFLAGS
    // overrides — user policy (budgets, levels, profiles) cannot change what
    // the compiler is capable of, and forwarding it would let one invocation's
    // policy contaminate a cached cross-invocation capability verdict.
    cmd.arg("--edition")
        .arg("2021")
        .arg("--crate-name")
        .arg(CAPABILITY_PROBE_CRATE)
        // A capability probe needs the verifier and frontend, not a linked
        // executable. Metadata-only compilation avoids linker/toolchain false
        // negatives and needless code generation.
        .arg("--crate-type=lib")
        .arg("--emit=metadata")
        .arg("-o")
        .arg(&out);
    if json_transport {
        cmd.arg("-Z").arg("trust-verify-output=json").arg("-Z").arg(format!(
            "trust-verify-session={}",
            verification_session.as_deref().expect("JSON probe has a session")
        ));
    }
    cmd.arg(&src);

    let output = bounded_process::output(
        &mut cmd,
        "native trustc capability probe",
        CAPABILITY_PROBE_MAX_STREAM_BYTES,
        CAPABILITY_PROBE_TIMEOUT,
    )
    .map_err(io::Error::other)?;
    Ok(NativeCompileProbe { output, verification_session })
}

#[cfg(unix)]
fn harden_probe_dir_permissions(dir: &tempfile::TempDir) -> io::Result<()> {
    use std::os::unix::fs::PermissionsExt;

    std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o700))
}

#[cfg(not(unix))]
fn harden_probe_dir_permissions(_dir: &tempfile::TempDir) -> io::Result<()> {
    Ok(())
}

pub(crate) fn detect_native_rustc_capabilities(rustc: &Path) -> NativeRustcCapabilities {
    let cache_key = native_capability_probe_cache_key(rustc).ok();
    if let Some(capabilities) = cache_key.as_deref().and_then(read_cached_native_capabilities) {
        return capabilities;
    }

    let mut completed_all_probes = true;
    if let Ok(probe) = run_native_compile_probe(rustc, true) {
        if probe.output.status.success() && output_contains_json_transport(&probe.output) {
            let authenticated_coverage =
                probe.verification_session.as_deref().is_some_and(|session| {
                    std::str::from_utf8(&probe.output.stderr).is_ok_and(|stderr| {
                        stderr_contains_authenticated_json_transport(stderr, session)
                    })
                });
            let capabilities = NativeRustcCapabilities {
                trust_verify: true,
                json_transport: true,
                authenticated_coverage,
            };
            cache_native_capabilities(cache_key.as_deref(), capabilities);
            return capabilities;
        }
    } else {
        completed_all_probes = false;
    }

    if let Ok(probe) = run_native_compile_probe(rustc, false) {
        if probe.output.status.success()
            && output_contains_native_verification_signal(&probe.output)
        {
            let capabilities = NativeRustcCapabilities {
                trust_verify: true,
                json_transport: false,
                authenticated_coverage: false,
            };
            cache_native_capabilities(cache_key.as_deref(), capabilities);
            return capabilities;
        }
    } else {
        completed_all_probes = false;
    }

    let capabilities = NativeRustcCapabilities::default();
    if completed_all_probes {
        cache_native_capabilities(cache_key.as_deref(), capabilities);
    }
    capabilities
}

#[cfg(test)]
mod tests {
    use super::*;

    struct EnvVarGuard {
        key: &'static str,
        old: Option<OsString>,
    }

    impl EnvVarGuard {
        #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
        fn set(key: &'static str, value: &Path) -> Self {
            let old = env::var_os(key);
            env::set_var(key, value);
            Self { key, old }
        }
    }

    impl Drop for EnvVarGuard {
        #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
        fn drop(&mut self) {
            if let Some(old) = self.old.take() {
                env::set_var(self.key, old);
            } else {
                env::remove_var(self.key);
            }
        }
    }

    fn read_probe_count(path: &Path) -> u32 {
        std::fs::read_to_string(path)
            .ok()
            .and_then(|text| text.trim().parse::<u32>().ok())
            .unwrap_or(0)
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn trustd_runtime_closure_macho_parser_binds_exact_system_dependencies_and_order() {
        let candidate = Path::new("/private/tmp/candidate-trustd");
        let dependencies = parse_macho_dependencies(
            "/private/tmp/candidate-trustd:\n\t/usr/lib/libiconv.2.dylib (compatibility version 7.0.0, current version 7.0.0)\n\t/usr/lib/libSystem.B.dylib (compatibility version 1.0.0, current version 1356.0.0)\n",
            candidate,
        )
        .expect("parse canonical dependency summary");
        assert_eq!(dependencies, ["/usr/lib/libiconv.2.dylib", "/usr/lib/libSystem.B.dylib"]);
        let commands = "/private/tmp/candidate-trustd:\nLoad command 0\n          cmd LC_LOAD_DYLINKER\n      cmdsize 28\n         name /usr/lib/dyld (offset 12)\nLoad command 1\n          cmd LC_LOAD_DYLIB\n      cmdsize 56\n         name /usr/lib/libiconv.2.dylib (offset 24)\nLoad command 2\n          cmd LC_LOAD_DYLIB\n      cmdsize 56\n         name /usr/lib/libSystem.B.dylib (offset 24)\n";
        parse_macho_load_commands(commands, candidate, &dependencies)
            .expect("load commands must match the ordered dependency summary");

        let mut reordered = dependencies.clone();
        reordered.swap(0, 1);
        assert!(
            parse_macho_load_commands(commands, candidate, &reordered).is_err(),
            "dependency reordering changed loader precedence"
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn trustd_runtime_closure_macho_parser_rejects_embedded_loader_authority() {
        let candidate = Path::new("/private/tmp/candidate-trustd");
        for dependency in [
            "@rpath/libattacker.dylib",
            "@loader_path/libattacker.dylib",
            "@executable_path/libattacker.dylib",
            "relative/libattacker.dylib",
            "/tmp/libattacker.dylib",
            "/usr/lib/../local/libattacker.dylib",
            "/usr/lib//libattacker.dylib",
            "/usr/lib/lib\tattacker.dylib",
        ] {
            let output = format!(
                "/private/tmp/candidate-trustd:\n\t{dependency} (compatibility version 1.0.0, current version 1.0.0)\n"
            );
            assert!(
                parse_macho_dependencies(&output, candidate).is_err(),
                "admitted mutable or tokenized dependency {dependency}"
            );
        }

        for (label, command) in [
            (
                "rpath",
                "/private/tmp/candidate-trustd:\n          cmd LC_RPATH\n      cmdsize 32\n         path /tmp/ignored (offset 12)\n",
            ),
            (
                "embedded environment",
                "/private/tmp/candidate-trustd:\n          cmd LC_DYLD_ENVIRONMENT\n      cmdsize 48\n         name DYLD_LIBRARY_PATH=/tmp/ignored (offset 12)\n",
            ),
            (
                "mutable dynamic linker",
                "/private/tmp/candidate-trustd:\n          cmd LC_LOAD_DYLINKER\n      cmdsize 32\n         name /tmp/dyld (offset 12)\n",
            ),
        ] {
            assert!(
                parse_macho_load_commands(command, candidate, &[]).is_err(),
                "admitted hostile {label} load command"
            );
        }
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn trustd_runtime_closure_inspection_ignores_path_shims_and_developer_dir() {
        let _guard = crate::TEST_ENV_LOCK.lock().expect("environment lock");
        let fake_root = tempfile::Builder::new()
            .prefix("trustd-fake-otool-")
            .tempdir()
            .expect("fake inspector directory");
        let fake_otool = fake_root.path().join("otool");
        write_executable(&fake_otool, "#!/bin/sh\nprintf '%s\\n' 'attacker-controlled otool'\n");
        let _path = EnvVarGuard::set("PATH", fake_root.path());
        let _developer_dir = EnvVarGuard::set("DEVELOPER_DIR", fake_root.path());

        let closure = inspect_trustd_runtime_closure(
            &std::env::current_exe().expect("current test executable"),
        )
        .expect("fixed native inspector must ignore ambient lookup authority");
        assert_ne!(closure.inspector_path, fake_otool.display().to_string());
        assert_ne!(closure.inspector_path, "/usr/bin/otool");
        assert!(closure.inspector_path.ends_with("/llvm-otool"));
        assert!(closure.system_dependencies.iter().all(|dependency| {
            dependency.starts_with("/usr/lib/") || dependency.starts_with("/System/Library/")
        }));
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn trustd_runtime_closure_inspector_requires_immutable_root_owned_ancestor_chain() {
        let (trusted, _) = trusted_macho_inspector().expect("fixed native inspector");
        validate_root_owned_inspector_chain(&trusted)
            .expect("fixed inspector authority chain must be established");

        let writable_root = tempfile::Builder::new()
            .prefix("trustd-writable-inspector-")
            .tempdir()
            .expect("writable inspector root");
        let fake = writable_root.path().join("nested/llvm-otool");
        std::fs::create_dir_all(fake.parent().expect("fake inspector parent"))
            .expect("create fake inspector parent");
        write_executable(&fake, "#!/bin/sh\nexit 0\n");
        let fake = std::fs::canonicalize(&fake).expect("canonical fake inspector");
        assert!(
            validate_root_owned_inspector_chain(&fake).is_err(),
            "a user-owned or writable inspector ancestor was accepted"
        );

        let redirected = writable_root.path().join("redirected-inspector");
        std::os::unix::fs::symlink(fake.parent().expect("fake inspector parent"), &redirected)
            .expect("create redirected inspector ancestor");
        let redirected_leaf = redirected.join("llvm-otool");
        assert!(
            validate_root_owned_inspector_chain(&redirected_leaf).is_err(),
            "a symlink inspector ancestor was accepted"
        );
        let redirected_target =
            std::fs::canonicalize(&redirected_leaf).expect("canonical redirected inspector");
        assert!(
            validate_root_owned_inspector_chain(&redirected_target).is_err(),
            "canonicalization hid a user-controlled inspector authority chain"
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn trustd_runtime_closure_candidate_authority_rejects_writable_leaf_ancestor_and_symlink() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let current_exe = std::env::current_exe().expect("current test executable");
        validate_trustd_candidate_authority(&current_exe)
            .expect("test executable must begin under an admissible candidate authority chain");
        let fixture = tempfile::Builder::new()
            .prefix("trustd-candidate-authority-")
            .tempdir_in(current_exe.parent().expect("test executable parent"))
            .expect("candidate authority fixture");
        std::fs::set_permissions(fixture.path(), std::fs::Permissions::from_mode(0o700))
            .expect("harden fixture root");
        let trusted_dir = fixture.path().join("trusted");
        std::fs::create_dir(&trusted_dir).expect("create trusted candidate directory");
        std::fs::set_permissions(&trusted_dir, std::fs::Permissions::from_mode(0o700))
            .expect("harden trusted candidate directory");
        let candidate = trusted_dir.join("trustd");
        write_executable(&candidate, "#!/bin/sh\nexit 0\n");
        let candidate = std::fs::canonicalize(&candidate).expect("canonical candidate fixture");
        validate_trustd_candidate_authority(&candidate)
            .expect("owner-private exact candidate chain must be admitted");

        std::fs::set_permissions(&candidate, std::fs::Permissions::from_mode(0o770))
            .expect("make candidate group-writable");
        let writable_leaf = validate_trustd_candidate_authority(&candidate)
            .expect_err("group-writable candidate leaf must be rejected");
        assert!(
            writable_leaf.contains(candidate.to_string_lossy().as_ref())
                && writable_leaf.contains("writable by group or other users"),
            "unexpected writable-leaf diagnostic: {writable_leaf}"
        );
        std::fs::set_permissions(&candidate, std::fs::Permissions::from_mode(0o700))
            .expect("restore candidate permissions");

        std::fs::set_permissions(&trusted_dir, std::fs::Permissions::from_mode(0o707))
            .expect("make candidate ancestor other-writable");
        let writable_ancestor = validate_trustd_candidate_authority(&candidate)
            .expect_err("other-writable candidate ancestor must be rejected");
        assert!(
            writable_ancestor.contains(trusted_dir.to_string_lossy().as_ref())
                && writable_ancestor.contains("writable by group or other users"),
            "unexpected writable-ancestor diagnostic: {writable_ancestor}"
        );
        std::fs::set_permissions(&trusted_dir, std::fs::Permissions::from_mode(0o700))
            .expect("restore candidate ancestor permissions");

        let redirected = fixture.path().join("redirected");
        symlink(&trusted_dir, &redirected).expect("create redirected candidate ancestor");
        let redirected_candidate = redirected.join("trustd");
        let redirected_error = validate_trustd_candidate_authority(&redirected_candidate)
            .expect_err("symlinked candidate ancestor must be rejected");
        assert!(
            redirected_error.contains("canonical")
                && redirected_error.contains("no symlink components"),
            "unexpected redirected-candidate diagnostic: {redirected_error}"
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn trustd_runtime_closure_candidate_authority_rejects_foreign_owner() {
        // SAFETY: geteuid has no preconditions and only observes process identity.
        let effective_uid = unsafe { libc::geteuid() };
        let foreign_uid = if effective_uid == 1 { 2 } else { 1 };
        let mut effective_user_prefix_started = false;
        let error = validate_trustd_candidate_owner(
            Path::new("/foreign-candidate"),
            foreign_uid,
            effective_uid,
            &mut effective_user_prefix_started,
        )
        .expect_err("foreign-owned candidate authority must be rejected");
        assert!(error.contains("owned by uid"), "unexpected foreign-owner diagnostic: {error}");

        if effective_uid != 0 {
            validate_trustd_candidate_owner(
                Path::new("/"),
                0,
                effective_uid,
                &mut effective_user_prefix_started,
            )
            .expect("immutable root prefix must be admitted before the user tree");
            validate_trustd_candidate_owner(
                Path::new("/user"),
                effective_uid,
                effective_uid,
                &mut effective_user_prefix_started,
            )
            .expect("effective-user tree must be admitted");
            assert!(
                validate_trustd_candidate_owner(
                    Path::new("/user/root-owned-after-user"),
                    0,
                    effective_uid,
                    &mut effective_user_prefix_started,
                )
                .is_err(),
                "root ownership after the effective-user prefix must not widen authority"
            );
        }
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn trustd_runtime_closure_reinspection_rejects_rehashed_addition_and_ordering() {
        let candidate = std::env::current_exe().expect("current test executable");
        let canonical = inspect_trustd_runtime_closure(&candidate)
            .expect("inspect current test executable runtime closure");

        let mut added_dependencies = canonical.system_dependencies.clone();
        added_dependencies.push("/usr/lib/libClosureAddition.dylib".to_string());
        let added = TrustdRuntimeClosure::from_macho_observation(
            canonical.inspector_path.clone(),
            canonical.inspector_sha256.clone(),
            added_dependencies,
        )
        .expect("construct internally consistent added dependency closure");
        assert!(
            added.validate_for_candidate(&candidate).is_err(),
            "a rehashed dependency addition was not checked against the candidate"
        );

        if canonical.system_dependencies.len() >= 2 {
            let mut reordered_dependencies = canonical.system_dependencies.clone();
            reordered_dependencies.swap(0, 1);
            let reordered = TrustdRuntimeClosure::from_macho_observation(
                canonical.inspector_path.clone(),
                canonical.inspector_sha256.clone(),
                reordered_dependencies,
            )
            .expect("construct internally consistent reordered dependency closure");
            assert!(
                reordered.validate_for_candidate(&candidate).is_err(),
                "a rehashed dependency ordering change was not checked against the candidate"
            );
        }
    }

    #[test]
    fn capability_probe_requires_current_session_bound_coverage() {
        const EXPECTED_SESSION: &str = "fresh-session";
        fn transport_line(message: &trust_types::TransportMessage) -> String {
            format!(
                "{}{}",
                trust_types::TRANSPORT_PREFIX,
                serde_json::to_string(message).expect("serialize probe transport")
            )
        }

        let legacy = format!(
            "{}{{\"type\":\"coverage_summary\",\"crate_name\":\"trust_verify_probe\",\"eligible\":1,\"processed\":1}}",
            trust_types::TRANSPORT_PREFIX
        );
        assert!(stderr_contains_json_transport(&legacy));
        assert!(!stderr_contains_authenticated_json_transport(&legacy, EXPECTED_SESSION));

        let wrong_session = format!(
            "{}{{\"type\":\"coverage_summary\",\"crate_name\":\"trust_verify_probe\",\"package_name\":\"\",\"primary_package\":false,\"verification_session\":\"stale\",\"eligible\":1,\"processed\":1}}",
            trust_types::TRANSPORT_PREFIX
        );
        assert!(!stderr_contains_authenticated_json_transport(&wrong_session, EXPECTED_SESSION));

        let current = format!(
            "{}{{\"type\":\"coverage_summary\",\"crate_name\":\"trust_verify_probe\",\"package_name\":\"\",\"primary_package\":false,\"verification_session\":\"{}\",\"eligible\":1,\"processed\":1}}",
            trust_types::TRANSPORT_PREFIX,
            EXPECTED_SESSION
        );
        assert!(
            !stderr_contains_authenticated_json_transport(&current, EXPECTED_SESSION),
            "nonce-bound count-only coverage is not exact authenticated coverage"
        );

        let function =
            trust_types::TransportMessage::FunctionResult(trust_types::FunctionTransportResult {
                function: "trust_verify_probe::trust_verify_probe".to_string(),
                package_name: None,
                crate_name: Some(CAPABILITY_PROBE_CRATE.to_string()),
                primary_package: false,
                verification_session: EXPECTED_SESSION.to_string(),
                results: Vec::new(),
                proved: 0,
                failed: 0,
                unknown: 0,
                timed_out: 0,
                skipped: 0,
                runtime_checked: 0,
                cached: 0,
                total: 0,
            });
        let coverage =
            trust_types::TransportMessage::CoverageSummary(trust_types::CoverageTransportSummary {
                crate_name: CAPABILITY_PROBE_CRATE.to_string(),
                package_name: String::new(),
                primary_package: false,
                verification_session: EXPECTED_SESSION.to_string(),
                eligible: 1,
                processed: 1,
                function_identities: Some(trust_types::CoverageFunctionIdentityInventory {
                    schema: trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1.to_string(),
                    eligible_functions: vec!["trust_verify_probe::trust_verify_probe".to_string()],
                    processed_functions: vec!["trust_verify_probe::trust_verify_probe".to_string()],
                }),
            });
        let exact = format!("{}\n{}", transport_line(&function), transport_line(&coverage));
        assert!(stderr_contains_authenticated_json_transport(&exact, EXPECTED_SESSION));

        let wrong_crate = exact.replace("trust_verify_probe", "lookalike_probe");
        assert!(!stderr_contains_authenticated_json_transport(&wrong_crate, EXPECTED_SESSION));

        let duplicate = format!("{exact}\n{exact}");
        assert!(!stderr_contains_authenticated_json_transport(&duplicate, EXPECTED_SESSION));
    }

    #[cfg(unix)]
    fn write_executable(path: &Path, script: &str) {
        use std::os::unix::fs::PermissionsExt;

        std::fs::write(path, script).expect("should write fake rustc");
        let mut permissions =
            std::fs::metadata(path).expect("fake rustc should exist").permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(path, permissions).expect("should chmod fake rustc");
    }

    #[cfg(unix)]
    fn exact_probe_transport_shell() -> String {
        format!(
            r#"printf '%s{{"type":"function_result","function":"trust_verify_probe::trust_verify_probe","package_name":null,"crate_name":"trust_verify_probe","primary_package":false,"verification_session":"%s","results":[],"proved":0,"failed":0,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":0,"cached":0,"total":0}}\n' '{prefix}' "$verification_session" >&2
printf '%s{{"type":"coverage_summary","crate_name":"trust_verify_probe","package_name":"","primary_package":false,"verification_session":"%s","eligible":1,"processed":1,"function_identities":{{"schema":"{schema}","eligible_functions":["trust_verify_probe::trust_verify_probe"],"processed_functions":["trust_verify_probe::trust_verify_probe"]}}}}\n' '{prefix}' "$verification_session" >&2"#,
            prefix = trust_types::TRANSPORT_PREFIX,
            schema = trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1,
        )
    }

    #[test]
    fn native_capability_probe_cache_key_changes_with_driver_artifact_bytes() {
        let harness = tempfile::Builder::new()
            .prefix("targo-trust-probe-cache-key-")
            .tempdir()
            .expect("should create probe harness tempdir");
        let rustc = harness.path().join("stage2").join("bin").join("trustc");
        let driver = harness.path().join("stage2").join("lib").join("librustc_driver-test.dylib");
        std::fs::create_dir_all(rustc.parent().expect("rustc parent")).expect("create bin");
        std::fs::create_dir_all(driver.parent().expect("driver parent")).expect("create lib");
        std::fs::write(&rustc, b"fake-rustc").expect("write fake rustc");
        std::fs::write(&driver, b"driver-v1").expect("write fake driver");

        let v1 = native_capability_probe_cache_key(&rustc).expect("key v1");
        std::fs::write(&driver, b"driver-v2").expect("write updated fake driver");
        let v2 = native_capability_probe_cache_key(&rustc).expect("key v2");

        assert_ne!(v1, v2, "driver artifact bytes must invalidate cached capabilities");
    }

    #[cfg(unix)]
    #[test]
    fn native_compile_probe_reuses_positive_persistent_cache() {
        let _guard = crate::TEST_ENV_LOCK.lock().expect("env lock");
        let harness = tempfile::Builder::new()
            .prefix("targo-trust-probe-cache-hit-")
            .tempdir()
            .expect("should create probe harness tempdir");
        let cache_dir = harness.path().join("cache");
        let _cache_guard = EnvVarGuard::set("TRUST_CACHE_DIR", &cache_dir);
        let rustc = harness.path().join("fake-rustc");
        let counter = harness.path().join("count.txt");
        let mode = harness.path().join("mode.txt");
        std::fs::write(&mode, "ok\n").expect("write mode");
        let script = format!(
            r#"#!/bin/sh
counter='{}'
mode='{}'
count=0
if [ -f "$counter" ]; then
    count="$(cat "$counter")"
fi
count=$((count + 1))
printf '%s\n' "$count" > "$counter"
if [ "$(cat "$mode")" != "ok" ]; then
    echo "probe should have used cache" >&2
    exit 64
fi
verification_session=
for arg in "$@"; do
    case "$arg" in
        trust-verify-session=*) verification_session="${{arg#trust-verify-session=}}" ;;
    esac
done
{}
exit 0
"#,
            counter.display(),
            mode.display(),
            exact_probe_transport_shell(),
        );
        write_executable(&rustc, &script);

        let first = detect_native_rustc_capabilities(&rustc);
        assert!(first.trust_verify);
        assert!(first.json_transport);
        assert!(first.authenticated_coverage);
        assert_eq!(read_probe_count(&counter), 1);
        let key = native_capability_probe_cache_key(&rustc).expect("cache key");
        assert!(
            native_capability_probe_cache_path(&key).is_file(),
            "positive capability probe should be persisted under the trust buildcache root"
        );

        std::fs::write(&mode, "fail\n").expect("write fail mode");
        let second = detect_native_rustc_capabilities(&rustc);
        assert!(second.trust_verify);
        assert!(second.json_transport);
        assert!(second.authenticated_coverage);
        assert_eq!(
            read_probe_count(&counter),
            1,
            "second detection should be served from cache without compiling the probe"
        );
    }

    #[cfg(unix)]
    #[test]
    fn native_compile_probe_does_not_persist_or_reuse_negative_results() {
        let _guard = crate::TEST_ENV_LOCK.lock().expect("env lock");
        let harness = tempfile::Builder::new()
            .prefix("targo-trust-probe-cache-negative-")
            .tempdir()
            .expect("should create probe harness tempdir");
        let cache_dir = harness.path().join("cache");
        let _cache_guard = EnvVarGuard::set("TRUST_CACHE_DIR", &cache_dir);
        let rustc = harness.path().join("fake-rustc");
        let counter = harness.path().join("count.txt");
        let mode = harness.path().join("mode.txt");
        std::fs::write(&mode, "unsupported\n").expect("write mode");
        let script = format!(
            r#"#!/bin/sh
counter='{}'
mode='{}'
count=0
if [ -f "$counter" ]; then
    count="$(cat "$counter")"
fi
count=$((count + 1))
printf '%s\n' "$count" > "$counter"
verification_session=
for arg in "$@"; do
    case "$arg" in
        trust-verify-session=*) verification_session="${{arg#trust-verify-session=}}" ;;
    esac
done
case "$(cat "$mode")" in
    unsupported)
        echo "trust-verify unsupported" >&2
        exit 1
        ;;
    json)
        {}
        exit 0
        ;;
    *)
        echo "unexpected mode" >&2
        exit 65
        ;;
esac
"#,
            counter.display(),
            mode.display(),
            exact_probe_transport_shell(),
        );
        write_executable(&rustc, &script);

        let first = detect_native_rustc_capabilities(&rustc);
        assert!(!first.trust_verify);
        assert!(!first.json_transport);
        assert!(!first.authenticated_coverage);
        assert_eq!(read_probe_count(&counter), 2);
        let key = native_capability_probe_cache_key(&rustc).expect("cache key");
        let cache_path = native_capability_probe_cache_path(&key);
        assert!(
            !cache_path.exists(),
            "a nonzero probe exit is not evidence that can be persisted as unsupported"
        );

        // Simulate a negative row left by an older Targo. New readers must
        // ignore it rather than preserving the stale false-negative forever.
        write_cached_native_capabilities(&key, NativeRustcCapabilities::default())
            .expect("write legacy negative row");
        assert!(cache_path.is_file());

        std::fs::write(&mode, "json\n").expect("write json mode");
        let second = detect_native_rustc_capabilities(&rustc);
        assert!(second.trust_verify);
        assert!(second.json_transport);
        assert!(second.authenticated_coverage);
        assert_eq!(
            read_probe_count(&counter),
            3,
            "a prior negative row must not suppress a later successful JSON probe"
        );

        let entry: NativeCapabilityProbeCacheEntry =
            serde_json::from_slice(&std::fs::read(&cache_path).expect("read positive cache entry"))
                .expect("parse positive cache entry");
        assert!(entry.trust_verify);
        assert!(entry.json_transport);
        assert!(entry.authenticated_coverage);
    }

    #[cfg(unix)]
    #[test]
    fn native_compile_probe_does_not_persist_partial_results() {
        let _guard = crate::TEST_ENV_LOCK.lock().expect("env lock");
        let harness = tempfile::Builder::new()
            .prefix("targo-trust-probe-cache-partial-")
            .tempdir()
            .expect("should create probe harness tempdir");
        let cache_dir = harness.path().join("cache");
        let _cache_guard = EnvVarGuard::set("TRUST_CACHE_DIR", &cache_dir);
        let rustc = harness.path().join("fake-rustc");
        let counter = harness.path().join("count.txt");
        let mode = harness.path().join("mode.txt");
        std::fs::write(&mode, "partial\n").expect("write mode");
        let script = format!(
            r#"#!/bin/sh
counter='{}'
mode='{}'
count=0
if [ -f "$counter" ]; then
    count="$(cat "$counter")"
fi
count=$((count + 1))
printf '%s\n' "$count" > "$counter"
mode_value="$(cat "$mode")"
json=0
verification_session=
for arg in "$@"; do
    if [ "$arg" = "trust-verify-output=json" ]; then
        json=1
    fi
    case "$arg" in
        trust-verify-session=*) verification_session="${{arg#trust-verify-session=}}" ;;
    esac
done
case "$mode_value" in
    partial)
        if [ "$json" = 1 ]; then
            echo "json transport unavailable this time" >&2
            exit 1
        fi
        echo "=== Trust Verification Report ===" >&2
        exit 0
        ;;
    json)
        {}
        exit 0
        ;;
    *)
        echo "unexpected mode" >&2
        exit 64
        ;;
esac
"#,
            counter.display(),
            mode.display(),
            exact_probe_transport_shell(),
        );
        write_executable(&rustc, &script);

        let first = detect_native_rustc_capabilities(&rustc);
        assert!(first.trust_verify);
        assert!(!first.json_transport);
        assert!(!first.authenticated_coverage);
        assert_eq!(read_probe_count(&counter), 2);
        let key = native_capability_probe_cache_key(&rustc).expect("cache key");
        let cache_path = native_capability_probe_cache_path(&key);
        assert!(
            !cache_path.exists(),
            "a failed JSON probe must not make a partial capability result sticky"
        );

        std::fs::write(&mode, "json\n").expect("write json mode");
        let second = detect_native_rustc_capabilities(&rustc);
        assert!(second.trust_verify);
        assert!(second.json_transport);
        assert!(second.authenticated_coverage);
        assert_eq!(
            read_probe_count(&counter),
            3,
            "an earlier partial result must be probed again and allowed to recover"
        );
        assert!(cache_path.is_file(), "the recovered fully positive result should be cached");

        std::fs::write(&mode, "fail\n").expect("write fail mode");
        let third = detect_native_rustc_capabilities(&rustc);
        assert!(third.trust_verify);
        assert!(third.json_transport);
        assert!(third.authenticated_coverage);
        assert_eq!(read_probe_count(&counter), 3, "fully positive evidence should be reused");
    }

    #[cfg(unix)]
    #[test]
    fn native_compile_probe_recovers_after_driver_artifact_changes() {
        let _guard = crate::TEST_ENV_LOCK.lock().expect("env lock");
        let harness = tempfile::Builder::new()
            .prefix("targo-trust-probe-cache-stale-")
            .tempdir()
            .expect("should create probe harness tempdir");
        let cache_dir = harness.path().join("cache");
        let _cache_guard = EnvVarGuard::set("TRUST_CACHE_DIR", &cache_dir);
        let rustc = harness.path().join("stage2").join("bin").join("trustc");
        let driver = harness.path().join("stage2").join("lib").join("librustc_driver-test.dylib");
        std::fs::create_dir_all(rustc.parent().expect("rustc parent")).expect("create bin");
        std::fs::create_dir_all(driver.parent().expect("driver parent")).expect("create lib");
        std::fs::write(&driver, "unsupported\n").expect("write fake driver");
        let counter = harness.path().join("count.txt");
        let script = format!(
            r#"#!/bin/sh
counter='{}'
driver='{}'
count=0
if [ -f "$counter" ]; then
    count="$(cat "$counter")"
fi
count=$((count + 1))
printf '%s\n' "$count" > "$counter"
verification_session=
for arg in "$@"; do
    case "$arg" in
        trust-verify-session=*) verification_session="${{arg#trust-verify-session=}}" ;;
    esac
done
case "$(cat "$driver")" in
    unsupported)
        echo "trust-verify unsupported" >&2
        exit 1
        ;;
    json)
        {}
        exit 0
        ;;
    *)
        echo "unexpected driver mode" >&2
        exit 65
        ;;
esac
"#,
            counter.display(),
            driver.display(),
            exact_probe_transport_shell(),
        );
        write_executable(&rustc, &script);

        let first = detect_native_rustc_capabilities(&rustc);
        assert!(!first.trust_verify);
        assert!(!first.json_transport);
        assert!(!first.authenticated_coverage);
        assert_eq!(read_probe_count(&counter), 2);
        let unsupported_key = native_capability_probe_cache_key(&rustc).expect("unsupported key");
        assert!(
            !native_capability_probe_cache_path(&unsupported_key).exists(),
            "unsupported-looking results must not be cached"
        );

        std::fs::write(&driver, "json\n").expect("write updated fake driver");
        let json_key = native_capability_probe_cache_key(&rustc).expect("json key");
        assert_ne!(
            unsupported_key, json_key,
            "driver artifact bytes must invalidate cached capabilities"
        );
        let second = detect_native_rustc_capabilities(&rustc);
        assert!(second.trust_verify);
        assert!(second.json_transport);
        assert!(second.authenticated_coverage);
        assert_eq!(
            read_probe_count(&counter),
            3,
            "changed driver artifact hash should force a fresh JSON probe"
        );
        assert!(
            native_capability_probe_cache_path(&json_key).is_file(),
            "refreshed positive compiler result should be cached under the new key"
        );
    }

    #[cfg(unix)]
    #[test]
    fn native_compile_probe_uses_owned_temp_dir_and_removes_it() {
        let harness = tempfile::Builder::new()
            .prefix("targo-trust-probe-harness-")
            .tempdir()
            .expect("should create probe harness tempdir");
        let rustc = harness.path().join("fake-rustc");
        let marker = harness.path().join("probe-dir.txt");
        let script = format!(
            r#"#!/bin/sh
marker='{}'
if read line; then
    exit 46
fi
last=
prev=
out=
metadata_emit=
lib_crate_type=
while [ "$#" -gt 0 ]; do
    case "$1" in
        trust-verify|trust-verify=*|trust-verify-full|trust-verify-full=*|trust-verify-target=*)
            echo "capability probe passed a retired verifier activation/scope option" >&2
            exit 47
            ;;
        --emit=metadata) metadata_emit=1 ;;
        --crate-type=lib) lib_crate_type=1 ;;
        --emit=*|--crate-type=*)
            echo "capability probe requested unexpected output mode: $1" >&2
            exit 48
            ;;
    esac
    if [ "$prev" = "-o" ]; then
        out="$1"
    fi
    prev="$1"
    last="$1"
    shift
done
if [ "$metadata_emit" != 1 ] || [ "$lib_crate_type" != 1 ]; then
    echo "capability probe must compile a metadata-only library" >&2
    exit 49
fi
src="$last"
src_dir="$(dirname "$src")"
out_dir="$(dirname "$out")"
if [ ! -f "$src" ]; then
    echo "missing source: $src" >&2
    exit 42
fi
if [ "$src_dir" != "$out_dir" ]; then
    echo "source/output dirs differ: src_dir=$src_dir out_dir=$out_dir out=$out" >&2
    exit 43
fi
case "$(basename "$src_dir")" in
    targo-trust-probe-*) ;;
    *)
        echo "unexpected probe dir basename: $(basename "$src_dir")" >&2
        exit 44
        ;;
esac
mode="$(stat -f '%Lp' "$src_dir" 2>/dev/null || stat -c '%a' "$src_dir" 2>/dev/null || true)"
case "$mode" in
    *[2367])
        echo "probe dir is world-writable: mode=$mode" >&2
        exit 45
        ;;
esac
if [ -z "$mode" ]; then
    echo "could not inspect probe dir mode" >&2
    exit 45
fi
printf '%s\n' "$src_dir" > "$marker"
exit 0
"#,
            marker.display()
        );
        write_executable(&rustc, &script);

        let probe = run_native_compile_probe(&rustc, false).expect("probe should run fake rustc");
        let output = probe.output;
        assert!(
            output.status.success(),
            "fake rustc should accept probe arguments: status={} stdout={} stderr={}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let probe_dir =
            std::fs::read_to_string(&marker).expect("fake rustc should record probe dir");
        assert!(
            !Path::new(probe_dir.trim()).exists(),
            "probe tempdir should be removed after compile probe returns"
        );
    }
}
