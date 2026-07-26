// Native rustc discovery: locating trustc next to targo-trust or in the repo build dirs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::env;
use std::io::Read;
use std::path::{Path, PathBuf};

use serde::Serialize;

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct NativeRustcCapabilities {
    pub(crate) trust_verify: bool,
    pub(crate) json_transport: bool,
    /// The compiler echoed a fresh invocation nonce in exactly one complete,
    /// unscoped coverage row for the expected probe crate.
    pub(crate) authenticated_coverage: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum NativeRustcDiscoverySource {
    #[serde(rename = "sibling_trustc")]
    SiblingTCargoTrust,
    RepoLocalStage2,
    RepoLocalStage3,
}

impl NativeRustcDiscoverySource {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::SiblingTCargoTrust => "sibling trustc next to `targo-trust`",
            Self::RepoLocalStage2 => "repo-local stage2 canonical trustc",
            Self::RepoLocalStage3 => "repo-local stage3 canonical trustc",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct NativeRustcDiscovery {
    pub(crate) rustc: PathBuf,
    pub(crate) source: NativeRustcDiscoverySource,
}

pub(super) fn canonicalize_or_self(path: PathBuf) -> PathBuf {
    std::fs::canonicalize(&path).unwrap_or(path)
}

pub(super) fn trust_compiler_names() -> [&'static str; 1] {
    if cfg!(windows) { ["trustc.exe"] } else { ["trustc"] }
}

pub(super) fn is_trustc_path(path: &Path) -> bool {
    path.file_name().is_some_and(|name| name == "trustc" || name == "trustc.exe")
}

pub(super) fn sibling_rustc_path(executable: &Path) -> Option<PathBuf> {
    // The running evidence frontend itself must be a regular executable. A
    // symlinked `targo-trust` would otherwise let its containing directory
    // relocate compiler authority before any capability check runs.
    if !path_is_executable_file(executable) {
        return None;
    }
    let bin_dir = executable.parent()?;
    trust_compiler_names()
        .into_iter()
        .map(|name| bin_dir.join(name))
        .find(|candidate| path_is_executable_file(candidate))
        .map(canonicalize_or_self)
}

pub(super) fn current_exe_sibling_rustc() -> Option<PathBuf> {
    env::current_exe().ok().and_then(|path| sibling_rustc_path(&path))
}

pub(super) fn host_executable_name(tool: &str) -> String {
    if cfg!(windows) { format!("{tool}.exe") } else { tool.to_string() }
}

fn trust_cargo_name() -> &'static str {
    // Trust: toolchain produces canonical `targo` (Rust-compat `cargo` is a symlink onto it).
    if cfg!(windows) { "targo.exe" } else { "targo" }
}

pub(crate) fn native_trust_cargo_path(rustc: &Path) -> Result<PathBuf, String> {
    if !is_trustc_path(rustc) || !path_is_executable_file(rustc) {
        return Err(format!(
            "selected Trust compiler is not a canonical regular executable: {}",
            rustc.display()
        ));
    }
    let bin_dir = rustc
        .parent()
        .ok_or_else(|| format!("Trust compiler `{}` has no bin directory", rustc.display()))?;
    let candidate = bin_dir.join(trust_cargo_name());
    if path_is_executable_file(&candidate) {
        // Deliberately NOT canonicalized: the sibling `targo` may be a
        // symlink, and resolving it could rename the spawned program (e.g. to
        // `cargo`), making the downstream `is_cargo_program` check fail and
        // silently skipping the cargo-mode RUSTFLAGS injection and the Gap-4
        // per-package clean. // Trust: produced frontend is `targo`.
        return Ok(candidate);
    }
    Err(format!(
        "linked Trust Cargo frontend is missing or not executable: {}; crate-mode verification requires sibling `{}` next to {} and will not use PATH fallback",
        candidate.display(),
        trust_cargo_name(),
        rustc.display()
    ))
}

pub(crate) fn is_cargo_program(program: &str) -> bool {
    Path::new(program).file_name().is_some_and(|name| name == "targo" || name == "targo.exe")
}

pub(super) fn repo_local_rustc_candidates(trust_root: &Path) -> Vec<NativeRustcDiscovery> {
    repo_local_stage_dirs(trust_root)
        .into_iter()
        .flat_map(|(dir, source)| {
            trust_compiler_names().into_iter().map(move |name| (dir.join(name), source))
        })
        .filter_map(|(candidate, source)| {
            path_is_executable_file(&candidate)
                .then(|| NativeRustcDiscovery { rustc: canonicalize_or_self(candidate), source })
        })
        .collect()
}

fn repo_local_stage_dirs(trust_root: &Path) -> Vec<(PathBuf, NativeRustcDiscoverySource)> {
    let build_dir = trust_root.join("build");
    let mut seen = BTreeSet::new();
    let mut dirs = Vec::new();

    push_repo_local_stage_dir(
        &mut dirs,
        &mut seen,
        build_dir.join("host").join("stage2").join("bin"),
        NativeRustcDiscoverySource::RepoLocalStage2,
    );

    let hosts = repo_local_build_hosts(&build_dir);
    for host_dir in &hosts {
        push_repo_local_stage_dir(
            &mut dirs,
            &mut seen,
            host_dir.join("stage2").join("bin"),
            NativeRustcDiscoverySource::RepoLocalStage2,
        );
    }

    push_repo_local_stage_dir(
        &mut dirs,
        &mut seen,
        build_dir.join("host").join("stage3").join("bin"),
        NativeRustcDiscoverySource::RepoLocalStage3,
    );

    for host_dir in &hosts {
        push_repo_local_stage_dir(
            &mut dirs,
            &mut seen,
            host_dir.join("stage3").join("bin"),
            NativeRustcDiscoverySource::RepoLocalStage3,
        );
    }

    dirs
}

fn repo_local_build_hosts(build_dir: &Path) -> Vec<PathBuf> {
    if let Ok(entries) = std::fs::read_dir(build_dir) {
        let mut hosts = entries
            .flatten()
            .map(|entry| entry.path())
            .filter(|path| path.is_dir())
            .collect::<Vec<_>>();
        hosts.sort();
        hosts
    } else {
        Vec::new()
    }
}

fn push_repo_local_stage_dir(
    dirs: &mut Vec<(PathBuf, NativeRustcDiscoverySource)>,
    seen: &mut BTreeSet<PathBuf>,
    path: PathBuf,
    source: NativeRustcDiscoverySource,
) {
    if seen.insert(path.clone()) {
        dirs.push((path, source));
    }
}

pub(crate) fn select_native_rustc_discovery(
    sibling_rustc: Option<PathBuf>,
    repo_candidates: Vec<NativeRustcDiscovery>,
) -> Option<NativeRustcDiscovery> {
    if let Some(rustc) = sibling_rustc
        .clone()
        .filter(|rustc| is_trustc_path(rustc) && path_is_executable_file(rustc))
    {
        return Some(NativeRustcDiscovery {
            rustc,
            source: NativeRustcDiscoverySource::SiblingTCargoTrust,
        });
    }

    if let Some(rustc) = repo_candidates.iter().find(|candidate| {
        is_trustc_path(&candidate.rustc) && path_is_executable_file(&candidate.rustc)
    }) {
        return Some(rustc.clone());
    }

    None
}

pub(super) fn path_is_executable_file(path: &Path) -> bool {
    let Ok(metadata) = path.symlink_metadata() else {
        return false;
    };
    if !metadata.file_type().is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

/// Compatibility aliases are deliberately symlinks onto canonical Trust
/// executables. Callers using this helper must separately prove the resolved
/// target stays in the selected toolchain directory.
pub(super) fn path_is_executable_target(path: &Path) -> bool {
    let Ok(metadata) = path.metadata() else {
        return false;
    };
    if !metadata.file_type().is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

/// Accept an intentional compatibility entrypoint only when it resolves to the
/// canonical tool itself or has byte-for-byte identical contents. Merely
/// sharing a bin directory is not an executable identity proof.
pub(super) fn same_file_or_exact_contents(left: &Path, right: &Path) -> bool {
    if left
        .canonicalize()
        .ok()
        .zip(right.canonicalize().ok())
        .is_some_and(|(left, right)| left == right)
    {
        return true;
    }
    let Ok(left_before) = std::fs::metadata(left) else {
        return false;
    };
    let Ok(right_before) = std::fs::metadata(right) else {
        return false;
    };
    if !left_before.is_file() || !right_before.is_file() || left_before.len() != right_before.len()
    {
        return false;
    }
    let Ok(mut left_file) = std::fs::File::open(left) else {
        return false;
    };
    let Ok(mut right_file) = std::fs::File::open(right) else {
        return false;
    };
    let Ok(left_opened) = left_file.metadata() else {
        return false;
    };
    let Ok(right_opened) = right_file.metadata() else {
        return false;
    };
    if !same_file_identity(&left_before, &left_opened)
        || !same_file_identity(&right_before, &right_opened)
    {
        return false;
    }

    let mut left_chunk = [0_u8; 64 * 1024];
    let mut right_chunk = [0_u8; 64 * 1024];
    loop {
        let Ok(left_read) = left_file.read(&mut left_chunk) else {
            return false;
        };
        let Ok(right_read) = right_file.read(&mut right_chunk) else {
            return false;
        };
        if left_read != right_read || left_chunk[..left_read] != right_chunk[..right_read] {
            return false;
        }
        if left_read == 0 {
            break;
        }
    }

    std::fs::metadata(left).ok().zip(std::fs::metadata(right).ok()).is_some_and(
        |(left_after, right_after)| {
            same_file_identity(&left_before, &left_after)
                && same_file_identity(&right_before, &right_after)
        },
    )
}

#[cfg(unix)]
fn same_file_identity(left: &std::fs::Metadata, right: &std::fs::Metadata) -> bool {
    use std::os::unix::fs::MetadataExt;

    left.dev() == right.dev() && left.ino() == right.ino()
}

#[cfg(not(unix))]
fn same_file_identity(left: &std::fs::Metadata, right: &std::fs::Metadata) -> bool {
    left.is_file() && right.is_file() && left.len() == right.len()
}

pub(crate) fn discover_native_rustc_checked() -> Option<NativeRustcDiscovery> {
    let trust_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    select_native_rustc_discovery(
        current_exe_sibling_rustc(),
        repo_local_rustc_candidates(&trust_root),
    )
}

/// Resolve the canonical Targo frontend bound to the same Trust root as the
/// selected compiler. Internal subcommands must not fall back to a bare
/// `cargo` from PATH: doing so can mix an upstream frontend into otherwise
/// same-sysroot Trust evidence.
pub(crate) fn discover_native_trust_cargo_checked() -> Result<PathBuf, String> {
    let discovery = discover_native_rustc_checked().ok_or_else(|| {
        "no canonical Trust compiler is available to anchor the sibling targo frontend".to_string()
    })?;
    native_trust_cargo_path(&discovery.rustc)
}
