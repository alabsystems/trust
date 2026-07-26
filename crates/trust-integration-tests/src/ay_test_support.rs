//! ay discovery helpers for integration tests.
//!
//! Real-solver tests use the standalone Trust toolchain layout first and then
//! PATH or repo-local build outputs.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use trust_router::IncrementalAYSession;

/// Return a usable ay binary path.
///
/// Discovery order:
/// - sibling `ay` next to the running test binary
/// - repo-local `build/*/stage{2,3}/bin/ay`
/// - `PATH`
/// - repo-local `first-party/ay/target/{debug,release}/ay`
#[must_use]
pub fn ay_solver_path() -> Option<PathBuf> {
    static AY_SOLVER_PATH: OnceLock<Option<PathBuf>> = OnceLock::new();
    AY_SOLVER_PATH
        .get_or_init(|| {
            ay_candidates()
                .into_iter()
                .find(|path| ay_version(path).is_some())
                .or_else(build_repo_ay_solver)
        })
        .clone()
}

/// True when a usable ay binary can be discovered by the test harness.
#[must_use]
pub fn ay_available() -> bool {
    ay_solver_path().is_some()
}

/// Build an incremental ay session or panic with the searched conventions.
///
/// Integration tests use this instead of `Command::new("ay")` so the same
/// standalone stage2 layout used by the toolchain is exercised in tests.
#[must_use]
pub fn require_ay() -> IncrementalAYSession {
    let path = ay_solver_path().unwrap_or_else(|| {
        panic!(
            "ay not found; build the standalone Trust toolchain, add ay to PATH, or build first-party/ay"
        )
    });
    let version = ay_version(&path).unwrap_or_else(|| "unknown version".to_string());
    eprintln!("ay detected: {} at {}", version.trim(), path.display());
    IncrementalAYSession::with_solver_path(path.to_string_lossy().into_owned())
}

fn ay_candidates() -> Vec<PathBuf> {
    let mut candidates = Vec::new();

    if let Ok(current) = env::current_exe() {
        if let Some(dir) = current.parent() {
            push_candidate(&mut candidates, dir.join(ay_exe_name()));
        }
    }

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    if let Some(repo_root) = manifest_dir.parent().and_then(Path::parent) {
        let build_root = repo_root.join("build");
        if let Ok(entries) = std::fs::read_dir(&build_root) {
            let mut stage_dirs = entries
                .flatten()
                .filter_map(|entry| {
                    let file_type = entry.file_type().ok()?;
                    file_type.is_dir().then_some(entry.path())
                })
                .flat_map(|slot| [slot.join("stage2/bin"), slot.join("stage3/bin")])
                .collect::<Vec<_>>();
            stage_dirs.sort();
            for dir in stage_dirs {
                push_candidate(&mut candidates, dir.join(ay_exe_name()));
            }
        }
    }

    if let Some(path_var) = env::var_os("PATH") {
        for dir in env::split_paths(&path_var) {
            push_candidate(&mut candidates, dir.join(ay_exe_name()));
        }
    }

    if let Some(repo_root) = manifest_dir.parent().and_then(Path::parent) {
        push_ay_root_candidates(&mut candidates, &repo_root.join("first-party/ay"));
    }

    candidates
}

fn push_ay_root_candidates(candidates: &mut Vec<PathBuf>, root: &Path) {
    for profile in ["debug", "release"] {
        push_candidate(candidates, root.join("target").join(profile).join(ay_exe_name()));
    }
}

fn build_repo_ay_solver() -> Option<PathBuf> {
    if env::var_os("TRUST_TEST_NO_BUILD_AY").is_some() {
        return None;
    }

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir.parent().and_then(Path::parent)?;
    let ay_root = repo_root.join("first-party/ay");
    let manifest = ay_root.join("Cargo.toml");
    if !manifest.is_file() {
        return None;
    }

    eprintln!("ay not found; building repo-owned first-party/ay binary for integration tests");
    let status = Command::new("cargo")
        .arg("build")
        .arg("--manifest-path")
        .arg(&manifest)
        .arg("-p")
        .arg("ay")
        .arg("--bin")
        .arg("ay")
        .arg("--features")
        .arg("cli")
        .status()
        .ok()?;
    if !status.success() {
        eprintln!("building first-party/ay failed with status {status}");
        return None;
    }

    ay_candidates().into_iter().find(|path| ay_version(path).is_some())
}

fn push_candidate(candidates: &mut Vec<PathBuf>, path: PathBuf) {
    if !candidates.iter().any(|candidate| candidate == &path) {
        candidates.push(path);
    }
}

fn ay_exe_name() -> &'static str {
    if cfg!(windows) { "ay.exe" } else { "ay" }
}

fn ay_version(path: &Path) -> Option<String> {
    if !path.is_file() {
        return None;
    }

    let output = Command::new(path).arg("--version").output().ok()?;
    if !output.status.success() {
        return None;
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let version = stdout.lines().next()?.trim();
    if version.is_empty() { None } else { Some(version.to_string()) }
}
