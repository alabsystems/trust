// Solver detection and status reporting for solver tool binaries
//
// Searches PATH and common installation locations for each solver
// binary, parses version output, and reports availability.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use serde::Serialize;

use crate::bounded_process;

// Identity probes run while Cargo and verifier workers may be saturating a CI
// host. Keep them strictly bounded, but allow enough scheduling headroom that
// an already-running, trivial solver cannot be rejected solely due to load.
// Trust: raised 15s -> 60s. Under the `full_verifier_flag` integration suite at
// default (num-CPU) test parallelism, ~26 concurrent `targo-trust check` flows —
// several themselves running compile probes — oversubscribe the scheduler enough
// that even a trivial `ay --version` shim cannot be dispatched within 15s wall
// clock, so the probe timed out and the check reported the solver "unavailable"
// (the observed `-j9`/default-threads flake). A genuinely missing solver still
// fails at spawn (not via this timeout), and a hung solver is still detected well
// within 60s, so the wider headroom costs nothing in production.
const SOLVER_IDENTITY_PROBE_TIMEOUT: Duration = Duration::from_secs(60);

/// Known solver tools and the proof levels they support.
const KNOWN_SOLVERS: &[SolverSpec] = &[
    SolverSpec {
        name: "ay",
        binary: "ay",
        description: "Primary SMT solver for supported L0 obligations (coverage is corpus-dependent)",
        proof_levels: &["L0"],
    },
    SolverSpec {
        name: "trust-mc",
        binary: "trust-mc",
        description: "Bounded model checking, counterexamples",
        proof_levels: &["L0"],
    },
    SolverSpec {
        name: "trust-vc",
        binary: "trust-vc",
        description: "Ownership-aware verification",
        proof_levels: &["L0"],
    },
    SolverSpec {
        name: "trust-wp",
        binary: "trust-wp",
        description: "Deductive verification, strongest postconditions",
        proof_levels: &["L1"],
    },
    SolverSpec {
        name: "ty",
        binary: "ty",
        description: "Temporal logic for distributed protocols",
        proof_levels: &["L2"],
    },
    SolverSpec {
        name: "clean",
        binary: "clean",
        description: "Higher-order prover, induction",
        proof_levels: &["L2"],
    },
];

/// Static specification of a known solver.
struct SolverSpec {
    name: &'static str,
    binary: &'static str,
    description: &'static str,
    proof_levels: &'static [&'static str],
}

/// Information about a detected (or missing) solver.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct SolverInfo {
    pub(crate) name: String,
    pub(crate) description: String,
    pub(crate) proof_levels: Vec<String>,
    pub(crate) available: bool,
    pub(crate) path: Option<PathBuf>,
    pub(crate) version: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) diagnostic: Option<String>,
}

/// Common installation directories to search beyond PATH.
fn common_search_dirs() -> Vec<PathBuf> {
    let mut dirs = Vec::new();

    // Cargo bin directory
    if let Some(home) = home_dir() {
        dirs.push(home.join(".cargo/bin"));
    }

    // Homebrew paths
    dirs.push(PathBuf::from("/opt/homebrew/bin"));
    dirs.push(PathBuf::from("/usr/local/bin"));

    // solver-specific install locations
    if let Some(home) = home_dir() {
        dirs.push(home.join(".dmath/bin"));
        dirs.push(home.join("dmath/bin"));
    }

    dirs
}

/// Get the user's home directory.
fn home_dir() -> Option<PathBuf> {
    std::env::var("HOME").ok().map(PathBuf::from)
}

#[derive(Debug)]
enum BinaryResolution {
    Found { path: PathBuf, version: String },
    Missing,
    InvalidExplicit { path: PathBuf, diagnostic: String },
}

fn explicit_solver_path(name: &str) -> Option<(String, OsString)> {
    let variables: &[&str] = match name {
        "ay" => &["AY_PATH"],
        "trust-mc" => &["TRUST_MC_PATH"],
        "trust-wp" => &["TRUST_WP_PATH"],
        "ty" => &["TRUST_TY_PATH", "TY_PATH"],
        _ => &[],
    };
    variables.iter().find_map(|variable| {
        std::env::var_os(variable).map(|value| ((*variable).to_string(), value))
    })
}

/// Search for a binary with explicit configuration taking strict precedence.
/// A configured-but-invalid path is an error and never falls through to a
/// different sibling/PATH executable.
fn find_binary(name: &str) -> BinaryResolution {
    let explicit = explicit_solver_path(name);
    let mut candidates = sibling_binary(name).into_iter().collect::<Vec<_>>();
    if let Some(path) = std::env::var_os("PATH") {
        candidates.extend(
            std::env::split_paths(&path).map(|directory| directory.join(executable_name(name))),
        );
    }
    candidates.extend(
        common_search_dirs().into_iter().map(|directory| directory.join(executable_name(name))),
    );
    select_binary_candidate(name, explicit, candidates)
}

fn select_binary_candidate(
    name: &str,
    explicit: Option<(String, OsString)>,
    candidates: impl IntoIterator<Item = PathBuf>,
) -> BinaryResolution {
    if let Some((variable, value)) = explicit {
        let path = PathBuf::from(value);
        return match validate_candidate(&path, name, matches!(name, "ay" | "ty")) {
            Ok((path, version)) => BinaryResolution::Found { path, version },
            Err(diagnostic) => BinaryResolution::InvalidExplicit {
                path,
                diagnostic: format!("{variable} is invalid: {diagnostic}"),
            },
        };
    }

    for candidate in candidates {
        if !candidate.is_file() {
            continue;
        }
        if let Ok((path, version)) =
            validate_candidate(&candidate, name, matches!(name, "ay" | "ty"))
        {
            return BinaryResolution::Found { path, version };
        }
    }
    BinaryResolution::Missing
}

fn sibling_binary(name: &str) -> Option<PathBuf> {
    let current = std::env::current_exe().ok()?;
    let bindir = current.parent()?;
    let candidate = bindir.join(executable_name(name));
    candidate.is_file().then_some(candidate)
}

#[cfg(windows)]
fn executable_name(name: &str) -> PathBuf {
    PathBuf::from(format!("{name}.exe"))
}

#[cfg(not(windows))]
fn executable_name(name: &str) -> PathBuf {
    PathBuf::from(name)
}

fn validate_candidate(
    binary_path: &Path,
    expected_name: &str,
    require_identity: bool,
) -> Result<(PathBuf, String), String> {
    if !solver_path_is_executable(binary_path) {
        return Err(format!("{} is not an executable file", binary_path.display()));
    }
    let canonical = binary_path
        .canonicalize()
        .map_err(|error| format!("could not canonicalize {}: {error}", binary_path.display()))?;
    let mut command = Command::new(&canonical);
    command.arg("--version");
    let output = bounded_process::output(
        &mut command,
        &format!("solver identity probe for {}", canonical.display()),
        64 * 1024,
        SOLVER_IDENTITY_PROBE_TIMEOUT,
    )
    .map_err(|error| format!("could not run {} --version: {error}", canonical.display()))?;
    if !output.status.success() {
        return Err(format!("{} --version exited with {}", canonical.display(), output.status));
    }
    let text = if output.stdout.iter().any(|byte| !byte.is_ascii_whitespace()) {
        String::from_utf8_lossy(&output.stdout)
    } else {
        String::from_utf8_lossy(&output.stderr)
    };
    let version = text
        .lines()
        .find(|line| !line.trim().is_empty())
        .map(str::trim)
        .ok_or_else(|| format!("{} --version produced no identity", canonical.display()))?
        .to_string();
    if require_identity && !version_identifies(&version, expected_name) {
        return Err(format!(
            "{} --version did not identify `{expected_name}` (reported `{version}`)",
            canonical.display()
        ));
    }
    Ok((canonical, version))
}

fn version_identifies(version: &str, expected_name: &str) -> bool {
    let expected = expected_name.replace(['-', '_'], "").to_ascii_lowercase();
    version
        .split(|character: char| {
            !character.is_ascii_alphanumeric() && character != '-' && character != '_'
        })
        .map(|token| token.replace(['-', '_'], "").to_ascii_lowercase())
        .any(|token| token == expected || (expected == "ty" && token == "tla"))
}

fn solver_path_is_executable(path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        path.metadata().is_ok_and(|metadata| metadata.permissions().mode() & 0o111 != 0)
    }
    #[cfg(not(unix))]
    {
        true
    }
}

/// Detect a single solver by name.
///
/// Returns `SolverInfo` with `available: true` if found, `false` otherwise.
pub(crate) fn detect_solver(name: &str) -> SolverInfo {
    let spec = KNOWN_SOLVERS.iter().find(|s| s.name == name);

    let (description, proof_levels) = match spec {
        Some(s) => {
            (s.description.to_string(), s.proof_levels.iter().map(|l| l.to_string()).collect())
        }
        None => (format!("Unknown solver: {name}"), vec![]),
    };

    let binary_name = spec.map_or(name, |s| s.binary);

    match find_binary(binary_name) {
        BinaryResolution::Found { path, version } => SolverInfo {
            name: name.to_string(),
            description,
            proof_levels,
            available: true,
            path: Some(path),
            version: Some(version),
            diagnostic: None,
        },
        BinaryResolution::InvalidExplicit { path, diagnostic } => SolverInfo {
            name: name.to_string(),
            description,
            proof_levels,
            available: false,
            path: Some(path),
            version: None,
            diagnostic: Some(diagnostic),
        },
        BinaryResolution::Missing => SolverInfo {
            name: name.to_string(),
            description,
            proof_levels,
            available: false,
            path: None,
            version: None,
            diagnostic: None,
        },
    }
}

/// Detect all known solvers and return their status.
pub(crate) fn detect_all_solvers() -> Vec<SolverInfo> {
    KNOWN_SOLVERS.iter().map(|spec| detect_solver(spec.name)).collect()
}

/// Validate that a solver name is known.
pub(crate) fn is_known_solver(name: &str) -> bool {
    KNOWN_SOLVERS.iter().any(|s| s.name == name)
}

/// Get the list of known solver names.
pub(crate) fn known_solver_names() -> Vec<&'static str> {
    KNOWN_SOLVERS.iter().map(|s| s.name).collect()
}

pub(crate) fn terminal_safe(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_control() || ('\u{7f}'..='\u{9f}').contains(&character) {
                '\u{fffd}'
            } else {
                character
            }
        })
        .collect()
}

/// Render solver status to terminal.
pub(crate) fn render_solvers_terminal(solvers: &[SolverInfo]) {
    eprintln!();
    eprintln!("=== Trust Solver Status ===");
    eprintln!();

    let mut available_count = 0;
    let total = solvers.len();

    for solver in solvers {
        let status = if solver.available {
            available_count += 1;
            "FOUND"
        } else {
            "MISSING"
        };

        let version_str = solver
            .version
            .as_deref()
            .map(|version| format!(" ({})", terminal_safe(version)))
            .unwrap_or_default();

        let path_str = solver
            .path
            .as_deref()
            .map(|path| format!(" at {}", terminal_safe(&path.display().to_string())))
            .unwrap_or_default();

        let levels = if solver.proof_levels.is_empty() {
            String::new()
        } else {
            format!(" [{}]", solver.proof_levels.join(", "))
        };

        eprintln!(
            "  [{status:>7}] {:<10} {}{levels}{version_str}{path_str}",
            terminal_safe(&solver.name),
            terminal_safe(&solver.description)
        );
        if let Some(diagnostic) = &solver.diagnostic {
            eprintln!("             ERROR: {}", terminal_safe(diagnostic));
        }
    }

    eprintln!();
    eprintln!("Summary: {available_count}/{total} solvers available");

    if available_count == 0 {
        eprintln!();
        eprintln!("No solvers found. Verification will produce only Unknown results.");
        eprintln!(
            "Install solvers from their solver repos (see targo-trust/README.md for install notes)."
        );
        eprintln!();
        eprintln!("Solver requirements by proof level:");
        eprintln!("  L0 (basic):    ay + trust_mc + trust-vc");
        eprintln!("  L1 (moderate): L0 + trust-wp");
        eprintln!("  L2 (full):     L1 + ty + clean");
    } else if available_count < total {
        eprintln!();
        eprintln!("Some solvers are missing. Full verification requires all solvers.");
    }

    eprintln!("===========================");
}

/// Render solver status as JSON.
pub(crate) fn render_solvers_json(solvers: &[SolverInfo]) {
    #[derive(Serialize)]
    struct SolverReport {
        solvers: Vec<SolverInfo>,
        available: usize,
        total: usize,
    }

    let available = solvers.iter().filter(|s| s.available).count();
    let report = SolverReport { solvers: solvers.to_vec(), available, total: solvers.len() };

    match serde_json::to_string_pretty(&report) {
        Ok(json) => println!("{json}"),
        Err(e) => eprintln!("targo trust: failed to serialize solver report: {e}"),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    fn fake_solver(directory: &Path, name: &str, version: &str) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;

        let path = directory.join(name);
        std::fs::write(&path, format!("#!/bin/sh\nprintf '%s\\n' '{version}'\n"))
            .expect("write fake solver");
        let mut permissions = std::fs::metadata(&path).expect("fake solver metadata").permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&path, permissions).expect("make fake solver executable");
        path
    }

    #[test]
    fn test_known_solver_names() {
        let names = known_solver_names();
        assert!(names.contains(&"ay"));
        assert!(names.contains(&"trust-mc"));
        assert!(names.contains(&"trust-wp"));
        assert!(names.contains(&"trust-vc"));
        assert!(names.contains(&"ty"));
        assert!(names.contains(&"clean"));
        assert_eq!(names.len(), 6);
    }

    #[test]
    fn test_is_known_solver() {
        assert!(is_known_solver("ay"));
        assert!(is_known_solver("clean"));
        assert!(!is_known_solver("nonexistent"));
        assert!(!is_known_solver(""));
    }

    #[test]
    fn test_detect_unknown_solver() {
        let info = detect_solver("definitely_not_a_real_solver_xyz");
        assert!(!info.available);
        assert!(info.path.is_none());
        assert!(info.version.is_none());
        assert_eq!(info.name, "definitely_not_a_real_solver_xyz");
    }

    #[cfg(unix)]
    #[test]
    fn explicit_ay_path_precedes_fallback_and_is_identity_probed() {
        let temp = tempfile::tempdir().expect("create solver fixture");
        let explicit = fake_solver(temp.path(), "explicit-ay", "ay 9.1 explicit");
        let fallback = fake_solver(temp.path(), "fallback-ay", "ay 8.0 fallback");
        let resolution = select_binary_candidate(
            "ay",
            Some(("AY_PATH".to_string(), explicit.clone().into_os_string())),
            [fallback],
        );
        match resolution {
            BinaryResolution::Found { path, version } => {
                assert_eq!(path, explicit.canonicalize().unwrap());
                assert_eq!(version, "ay 9.1 explicit");
            }
            other => panic!("expected explicit ay, got {other:?}"),
        }
    }

    #[cfg(unix)]
    #[test]
    fn invalid_explicit_ay_never_falls_back_to_another_solver() {
        let temp = tempfile::tempdir().expect("create solver fixture");
        let wrong = fake_solver(temp.path(), "wrong", "not-ay-compatible 1.0");
        let fallback = fake_solver(temp.path(), "fallback", "ay 8.0 fallback");
        let resolution = select_binary_candidate(
            "ay",
            Some(("AY_PATH".to_string(), wrong.clone().into_os_string())),
            [fallback],
        );
        match resolution {
            BinaryResolution::InvalidExplicit { path, diagnostic } => {
                assert_eq!(path, wrong);
                assert!(diagnostic.contains("AY_PATH"));
                assert!(diagnostic.contains("did not identify `ay`"));
            }
            other => panic!("invalid explicit path must fail closed, got {other:?}"),
        }
    }

    #[test]
    fn test_detect_all_solvers_returns_all() {
        let solvers = detect_all_solvers();
        assert_eq!(solvers.len(), 6);
        // All should have names matching known solvers
        let names: Vec<&str> = solvers.iter().map(|s| s.name.as_str()).collect();
        assert!(names.contains(&"ay"));
        assert!(names.contains(&"clean"));
    }

    #[test]
    fn test_solver_info_serialization() {
        let info = SolverInfo {
            name: "ay".to_string(),
            description: "SMT solver".to_string(),
            proof_levels: vec!["L0".to_string()],
            available: true,
            path: Some(PathBuf::from("/usr/local/bin/ay")),
            version: Some("ay 4.13.0".to_string()),
            diagnostic: None,
        };
        let json = serde_json::to_string(&info).expect("should serialize");
        assert!(json.contains("\"available\":true"));
        assert!(json.contains("\"name\":\"ay\""));
    }

    #[test]
    fn test_common_search_dirs_non_empty() {
        let dirs = common_search_dirs();
        // Should always include at least the homebrew paths
        assert!(!dirs.is_empty());
    }

    #[test]
    fn terminal_rendering_neutralizes_solver_control_sequences() {
        assert_eq!(terminal_safe("ay\u{1b}[31m\nforged"), "ay�[31m�forged");
    }
}
