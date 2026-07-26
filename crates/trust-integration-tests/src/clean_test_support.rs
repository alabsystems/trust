//! clean (CIC kernel / proof checker) discovery helpers for integration tests.
//!
//! Mirrors [`crate::ay_test_support`]: locates a `clean` executable so a gate
//! can cross-check it against the proof corpora.
//!
//! What a binary found here measures is THE BINARY. Discovery reaches `PATH`
//! and other locations outside this checkout, so the executable may be older
//! than the pinned `first-party/clean` source and disagree with it. The
//! corpora's own authority therefore does not live here: `clean-parser`,
//! `clean-elab`, and `clean-kernel` are workspace dependencies of
//! `trust-certify`, so `lean_front_door_gate` kernel-checks the same files in
//! process, at the pinned revision, with nothing to discover and no way to
//! skip.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

/// Return a usable `clean` checker binary path, or `None` if none is discoverable.
///
/// Discovery order:
/// - sibling `clean` next to the running test binary
/// - repo-local `build/*/stage{2,3}/bin/clean`
/// - repo-local `first-party/clean/target/{debug,release}/clean`
///
/// `PATH` is deliberately NOT searched. An installed `clean` is not an artifact
/// of this tree: it can predate the `first-party/clean` pin by any amount, and
/// when it does, it disagrees with the pinned source about proofs that are
/// perfectly good — a red gate carrying no information about the repository.
/// Every candidate above is something a build in THIS checkout produced, so a
/// disagreement is a fact about the tree and worth failing on.
#[must_use]
pub fn clean_checker_path() -> Option<PathBuf> {
    static CLEAN_CHECKER_PATH: OnceLock<Option<PathBuf>> = OnceLock::new();
    CLEAN_CHECKER_PATH
        .get_or_init(|| clean_candidates().into_iter().find(|path| clean_usable(path)))
        .clone()
}

/// True when a usable `clean` checker can be discovered by the test harness.
#[must_use]
pub fn clean_available() -> bool {
    clean_checker_path().is_some()
}

fn clean_exe_name() -> &'static str {
    if cfg!(windows) { "clean.exe" } else { "clean" }
}

/// A binary is "usable" if it exists and responds to a trivial `--help`/`check`
/// invocation without an exec error (we don't pin a version string — the gate's
/// per-file `check` is the real test).
fn clean_usable(path: &Path) -> bool {
    path.is_file()
        && Command::new(path)
            .arg("--help")
            .output()
            .map(|o| o.status.success() || !o.stdout.is_empty() || !o.stderr.is_empty())
            .unwrap_or(false)
}

fn push_candidate(candidates: &mut Vec<PathBuf>, candidate: PathBuf) {
    if !candidates.contains(&candidate) {
        candidates.push(candidate);
    }
}

fn clean_candidates() -> Vec<PathBuf> {
    let mut candidates = Vec::new();

    if let Ok(current) = env::current_exe() {
        if let Some(dir) = current.parent() {
            push_candidate(&mut candidates, dir.join(clean_exe_name()));
        }
    }

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir.parent().and_then(Path::parent);

    if let Some(repo_root) = repo_root {
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
                push_candidate(&mut candidates, dir.join(clean_exe_name()));
            }
        }
    }

    if let Some(repo_root) = repo_root {
        let clean_target = repo_root.join("first-party/clean/target");
        push_candidate(&mut candidates, clean_target.join("debug").join(clean_exe_name()));
        push_candidate(&mut candidates, clean_target.join("release").join(clean_exe_name()));
    }

    candidates
}
