// Unified Trust CLI adapters for repository maintenance scripts.
//
// These commands keep `targo trust` as the public control surface while the
// existing Python implementations are migrated into Rust library code.

use sha2::{Digest, Sha256};
use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Output};
use std::time::Duration;
use std::{env, fs, io};

#[cfg(test)]
use std::time::Instant;

use crate::bounded_process;
use crate::stage2_tools::{discover_unique_repo_stage2_tool, validate_repo_stage2_tool};

const SCRIPT_MAX_STREAM_BYTES: usize = 64 * 1024 * 1024;
const SCRIPT_TIMEOUT: Duration = Duration::from_secs(12 * 60 * 60);
const CERTIFIED_MONITOR_RELEASE_SCRIPT: &str = "scripts/stage2_certified_monitor_e2e.sh";
const CERTIFIED_MONITOR_RELEASE_PATH: &str = "/usr/bin:/bin";
const CERTIFIED_MONITOR_CACHE_HOME_ENV: &str = "TRUST_CERTIFIED_MONITOR_E2E_CACHE_HOME";
const CERTIFIED_MONITOR_EXPECTED_HEAD_ENV: &str = "TRUST_CERTIFIED_MONITOR_EXPECTED_HEAD";
const TEMPORAL_FABRIC_MANIFEST: &str = "targo-trust/tests/fixtures/fabric/Cargo.toml";
const TEMPORAL_FABRIC_LOCK: &str = "targo-trust/tests/fixtures/fabric/Cargo.lock";

#[cfg(unix)]
const TRUSTED_BASH: &str = "/bin/bash";
#[cfg(not(unix))]
const TRUSTED_BASH: &str = "bash";

struct ScriptSpec {
    names: &'static [&'static str],
    script: &'static str,
    summary: &'static str,
    runner: MaintenanceRunner,
    /// Arguments enforced by this public command before caller-supplied
    /// arguments. Release adapters use this to make evidence-strengthening
    /// policy non-optional.
    fixed_args: &'static [&'static str],
}

struct MaintenanceSpec {
    names: &'static [&'static str],
    script: &'static str,
    summary: &'static str,
    runner: MaintenanceRunner,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MaintenanceRunner {
    Python,
    Shell,
}

impl ScriptSpec {
    fn canonical_name(&self) -> &'static str {
        self.names[0]
    }

    fn matches(&self, value: &str) -> bool {
        self.names.contains(&value)
    }
}

impl MaintenanceSpec {
    fn canonical_name(&self) -> &'static str {
        self.names[0]
    }

    fn matches(&self, value: &str) -> bool {
        self.names.contains(&value)
    }
}

const VERIFY_USAGE: &str = "\
Usage: targo trust verify <command> [args...]

Commands:
  examples              Check examples/verify*.rs Expected headers and verifier output
  cargo-cache           Materialize a dedicated registry-only Cargo seed cache for release full-verify
  repo-gate             Run the repository verification gate without shell orchestration
  solvers               Run solver detection through the canonical Trust CLI surface
  self                  Run the Rust-native Trust self-verification harness

Removed verify aliases reject when invoked. Use cargo-cache, repo-gate,
verify self --full-verifier, and release check for release evidence.

Examples:
  targo trust verify examples --metadata-only
  targo trust verify examples --trustc build/host/stage2/bin/trustc --json-output target/trust/gates/verify-examples.json
  targo trust verify cargo-cache --repo-root . --cargo-home build/full-verify/cargo-seed-home --json-output build/full-verify/cargo-cache-materialization.json
  targo trust verify repo-gate --quick
  targo trust verify solvers --json
";

const RUST_NATIVE_RELEASE_GATE_ADVICE: &str = "targo trust verify cargo-cache, targo trust verify repo-gate, targo trust verify self --full-verifier, and targo trust release check";

const DEPS_USAGE: &str = "\
Usage: targo trust deps <command> [args...]

Commands:
  status        Report Trust-owned dependency alignment state
  diff          Classify dependency drift from the Rust alignment report
  upstream-plan Produce a dependency upstreaming/import action plan
  export        Plan or write a deterministic dependency export
  import        Plan or apply a deterministic dependency import
  lock          Plan trust-engines.lock updates for imported dependencies
  validate      Gate Trust-owned dependency alignment state
  upstream-test-inventory  Produce upstream Trust test inventory

Examples:
  targo trust deps status --json
  targo trust deps status --dependency ty --json
  targo trust deps status --fetch --view refresh-plan
  targo trust deps status --fetch --gate snapshot-integrity
  targo trust deps upstream-plan --fetch
  targo trust deps validate --fetch
  targo trust deps validate --source git-index --json
  targo trust deps validate --production --source git-index --json-output reports/full-verify/owned-dependency-release-readiness.report.json
";

const RELEASE_VALIDATE_USAGE: &str = "\
Usage: targo trust release validate <command> [args...]

Commands:
  conformance                  Run Trust conformance checks
  ledger-expirations           Fail on expired upstream-parity ledger entries
  seed-freshness               Require a current seed and all digest-bound payloads
  certified-monitors           Run real-Targo monitor E2Es (Linux/macOS x86_64/aarch64)
";

const GATE_USAGE: &str = "\
Usage: targo trust gate <command> [args...]

Commands:
  check-all       Run repository compile and stage2 verifier gates
  scripts         Run script syntax and verifier example metadata gates only
  verify-examples Check examples/verify*.rs Expected headers against trustc output
  coherence       Check the recorded first-party submodule SHAs type-check together

Examples:
  targo trust gate check-all --repo-root .
  targo trust gate scripts --repo-root .
  targo trust gate coherence --repo-root .
  targo trust gate verify-examples --trustc build/host/stage2/bin/trustc --json-output target/trust/gates/verify-examples.json
";

const REPO_USAGE: &str = "\
Usage: targo trust repo <command> [args...]

Commands:
  check                         Run the repository compilation/test sanity gate
  scripts                       Run script syntax and verifier example metadata gates
  verify-examples               Check examples/verify*.rs Expected headers/output
  ledger-expirations            Fail on expired upstream-parity ledger entries
  submodule-reachability        Check parent-pinned submodule commit remote reachability
  mir-extract                   Check rustc_private Trust MIR extraction path
  upstream-toolchain            Preflight upstream Rust test toolchain state
  compat                        Run compatibility harness against crate list
  build                         Run the Trust build orchestrator
  dev-build                     Run fast development build helper
  dev-test                      Run fast development test helper
  generate-mir-fixtures         Regenerate MIR JSON fixtures
  test-after-build              Run tiered tests after a completed Trust build
  stage2-noverify-mir-test      Run focused no-verification MIR-transform test
  stage2-noverify-self-build    Run bounded no-verification stage2 self-build gate
  stage2-verify-self-build      Run bounded verification-on stage2 self-build gate
  showcase-demo                 Run internal model-check showcase demo
  concurrency-cap               Run cargo under the host concurrency limiter
  memory-monitor                Monitor RSS for a build process

Examples:
  targo trust repo check
  targo trust repo scripts
  targo trust repo verify-examples --trustc build/host/stage2/bin/trustc --json-output target/trust/gates/verify-examples.json
  targo trust repo submodule-reachability --json
  targo trust repo dev-test trust-vcgen
  targo trust repo build stage1
";

const BOOTSTRAP_USAGE: &str = "\
Usage: targo trust bootstrap <command> [args...]

Trust stage0 maintenance scripts. These commands operate on bootstrap/trust-stage0
artifacts; they do not configure the targo frontend.

Commands:
  recreate              Recreate local bootstrap artifacts from system Rust
  create-local-genesis  Create an explicit local genesis stage0 adapter
  discover-stage0       Discover materialized Trust-owned stage0 payload roots
  fetch-stage0          Fetch declared checksum-pinned Trust stage0 payloads
  check-seed-freshness  Validate seed/source version cadence and optional payloads
  seed-stage0           Re-seed bootstrap/trust-stage0 after successful tests
  rustup-link           Register the stage1/stage2 Trust toolchain with rustup

Examples:
  targo trust bootstrap recreate --check
  targo trust bootstrap recreate --stage 1
  targo trust bootstrap fetch-stage0
  targo trust bootstrap rustup-link stage2
";

static VERIFY_SPECS: &[ScriptSpec] = &[];

static DEPS_SPECS: &[ScriptSpec] = &[ScriptSpec {
    names: &["upstream-test-inventory"],
    script: "scripts/trust_upstream_test_inventory.py",
    summary: "Produce upstream Trust test inventory",
    runner: MaintenanceRunner::Python,
    fixed_args: &[],
}];

static RELEASE_VALIDATE_SPECS: &[ScriptSpec] = &[
    ScriptSpec {
        names: &["conformance"],
        script: "scripts/run_trust_conformance.py",
        summary: "Run Trust conformance checks",
        runner: MaintenanceRunner::Python,
        fixed_args: &[],
    },
    ScriptSpec {
        names: &["ledger-expirations"],
        script: "scripts/check_ledger_expirations.py",
        summary: "Fail on expired upstream-parity ledger entries",
        runner: MaintenanceRunner::Python,
        fixed_args: &[],
    },
    ScriptSpec {
        names: &["seed-freshness"],
        script: "scripts/check_seed_freshness.py",
        summary: "Validate Trust stage0 seed cadence and release payload binding",
        runner: MaintenanceRunner::Python,
        fixed_args: &["--require-payloads"],
    },
    ScriptSpec {
        names: &["certified-monitors"],
        script: CERTIFIED_MONITOR_RELEASE_SCRIPT,
        summary: "Run the Linux/macOS stage2 certified-monitor release E2E gate",
        runner: MaintenanceRunner::Shell,
        fixed_args: &[],
    },
];

static REPO_SPECS: &[MaintenanceSpec] = &[
    MaintenanceSpec {
        names: &["ledger-expirations"],
        script: "scripts/check_ledger_expirations.py",
        summary: "Fail on expired upstream-parity ledger entries",
        runner: MaintenanceRunner::Python,
    },
    MaintenanceSpec {
        names: &["submodule-reachability"],
        script: "scripts/check_submodule_remote_reachability.py",
        summary: "Check parent-pinned submodule commit remote reachability",
        runner: MaintenanceRunner::Python,
    },
    MaintenanceSpec {
        names: &["seed-freshness"],
        script: "scripts/check_seed_freshness.py",
        summary: "Validate Trust stage0 seed/source version cadence",
        runner: MaintenanceRunner::Python,
    },
    MaintenanceSpec {
        names: &["mir-extract"],
        script: "scripts/check_trust_mir_extract.sh",
        summary: "Check rustc_private Trust MIR extraction path",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["upstream-toolchain"],
        script: "scripts/check_upstream_rust_test_toolchain.sh",
        summary: "Preflight upstream Rust test toolchain state",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["compat"],
        script: "scripts/compat_check.sh",
        summary: "Run compatibility harness against crate list",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["build"],
        script: "scripts/build.sh",
        summary: "Run the Trust build orchestrator",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["dev-build"],
        script: "scripts/dev-build.sh",
        summary: "Run fast development build helper",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["dev-test"],
        script: "scripts/dev-test.sh",
        summary: "Run fast development test helper",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["generate-mir-fixtures"],
        script: "scripts/generate_mir_fixtures.sh",
        summary: "Regenerate MIR JSON fixtures",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["test-after-build"],
        script: "scripts/run_tests_after_build.sh",
        summary: "Run tiered tests after a completed Trust build",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["stage2-noverify-mir-test"],
        script: "scripts/stage2_noverify_rustc_mir_transform_test.sh",
        summary: "Run focused no-verification MIR-transform test",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["stage2-noverify-self-build"],
        script: "scripts/stage2_noverify_self_build.sh",
        summary: "Run bounded no-verification stage2 self-build gate",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["stage2-verify-self-build"],
        script: "scripts/stage2_verify_self_build.sh",
        summary: "Run bounded verification-on stage2 self-build gate",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["showcase-demo"],
        script: "scripts/showcase-demo.sh",
        summary: "Run internal model-check showcase demo",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["concurrency-cap"],
        script: "scripts/cargo-concurrency-cap.sh",
        summary: "Run cargo under the host concurrency limiter",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["memory-monitor"],
        script: "scripts/monitor-build-memory.sh",
        summary: "Monitor RSS for a build process",
        runner: MaintenanceRunner::Shell,
    },
];

static BOOTSTRAP_SPECS: &[MaintenanceSpec] = &[
    MaintenanceSpec {
        names: &["recreate"],
        script: "scripts/recreate_bootstrap.py",
        summary: "Recreate local bootstrap artifacts from system Rust",
        runner: MaintenanceRunner::Python,
    },
    MaintenanceSpec {
        names: &["create-local-genesis"],
        script: "scripts/create_local_genesis_stage0.py",
        summary: "Create an explicit local genesis stage0 adapter",
        runner: MaintenanceRunner::Python,
    },
    MaintenanceSpec {
        names: &["discover-stage0"],
        script: "scripts/discover_trust_stage0_seed.py",
        summary: "Discover materialized Trust-owned stage0 payload roots",
        runner: MaintenanceRunner::Python,
    },
    MaintenanceSpec {
        names: &["fetch-stage0"],
        script: "scripts/fetch_trust_stage0_payloads.py",
        summary: "Fetch declared checksum-pinned Trust stage0 payloads",
        runner: MaintenanceRunner::Python,
    },
    MaintenanceSpec {
        names: &["check-seed-freshness"],
        script: "scripts/check_seed_freshness.py",
        summary: "Validate seed/source cadence and optionally materialized payloads",
        runner: MaintenanceRunner::Python,
    },
    MaintenanceSpec {
        names: &["seed-stage0"],
        script: "scripts/seed_stage0_after_tests.sh",
        summary: "Re-seed bootstrap/trust-stage0 after successful tests",
        runner: MaintenanceRunner::Shell,
    },
    MaintenanceSpec {
        names: &["rustup-link"],
        script: "scripts/rustup-link-trust.sh",
        summary: "Register the stage1/stage2 Trust toolchain with rustup",
        runner: MaintenanceRunner::Shell,
    },
];

pub(crate) fn run_verify_subcommand(args: &[String]) -> ExitCode {
    match args.first().map(String::as_str) {
        Some("examples") => crate::verify_examples_cli::run(&args[1..]),
        Some("full") => {
            eprintln!(
                "targo trust verify full: shell orchestration has been removed from the public Trust CLI"
            );
            eprintln!(
                "  Use Rust-native gates ({RUST_NATIVE_RELEASE_GATE_ADVICE}) for release evidence."
            );
            ExitCode::from(2)
        }
        Some(alias @ ("preflight" | "full-preflight")) => {
            eprintln!(
                "targo trust verify {alias}: removed shell/Python-era release alias"
            );
            eprintln!(
                "  Use Rust-native gates ({RUST_NATIVE_RELEASE_GATE_ADVICE}) for release evidence."
            );
            ExitCode::from(2)
        }
        Some("cargo-cache") => crate::cargo_cache_materialization_cli::run(&args[1..]),
        Some("repo-gate") => run_verify_repo_gate(&args[1..]),
        Some("solvers") => run_trust_cli_subcommand("verify solvers", "solvers", &args[1..]),
        Some("self") => crate::self_verify_cli::run(&args[1..]),
        Some(alias @ ("example-corpus" | "verify-examples")) => {
            removed_verify_alias(alias, "examples")
        }
        Some(alias @ ("cache-materialize" | "cache-materialization")) => {
            removed_verify_alias(alias, "cargo-cache")
        }
        Some(alias @ ("solver-check" | "native-solver-sample")) => {
            removed_verify_alias(alias, "solvers")
        }
        Some(alias @ ("gate" | "check-all")) => removed_verify_alias(alias, "repo-gate"),
        Some(alias @ ("compiler" | "compiler-verifier")) => {
            removed_verify_alias(alias, "self --full-verifier")
        }
        _ => run_leaf_command("verify", args, VERIFY_SPECS, VERIFY_USAGE),
    }
}

fn removed_verify_alias(alias: &str, replacement: &str) -> ExitCode {
    eprintln!(
        "targo trust verify {alias}: removed alias; use `targo trust verify {replacement}`"
    );
    ExitCode::from(2)
}

fn run_verify_repo_gate(args: &[String]) -> ExitCode {
    let mut include_cargo = true;
    let mut forwarded = Vec::with_capacity(args.len());
    for arg in args {
        match arg.as_str() {
            "--quick" | "--no-cargo" => include_cargo = false,
            other => forwarded.push(other.to_string()),
        }
    }
    run_check_all_gate(&forwarded, include_cargo, "targo trust verify repo-gate")
}

pub(crate) fn run_deps_subcommand(args: &[String]) -> ExitCode {
    run_deps_rust_subcommand(args)
        .unwrap_or_else(|| run_leaf_command("deps", args, DEPS_SPECS, DEPS_USAGE))
}

pub(crate) fn run_repo_subcommand(args: &[String]) -> ExitCode {
    match args.first().map(String::as_str) {
        Some(command) if is_help_arg(command) => {
            print!("{REPO_USAGE}");
            ExitCode::SUCCESS
        }
        Some("check") => run_check_all_gate(&args[1..], true, "targo trust repo check"),
        Some("scripts") => run_check_all_gate(&args[1..], false, "targo trust repo scripts"),
        Some("verify-examples") => crate::verify_examples_cli::run(&args[1..]),
        Some("check-all") => removed_repo_alias("check-all", "check"),
        Some("script-syntax") => removed_repo_alias("script-syntax", "scripts"),
        Some("examples") => removed_repo_alias("examples", "verify-examples"),
        _ => run_maintenance_leaf_command("repo", args, REPO_SPECS, REPO_USAGE),
    }
}

fn removed_repo_alias(alias: &str, replacement: &str) -> ExitCode {
    eprintln!("targo trust repo {alias}: removed alias; use `targo trust repo {replacement}`");
    ExitCode::from(2)
}

pub(crate) fn run_bootstrap_subcommand(args: &[String]) -> ExitCode {
    match args.first().map(String::as_str) {
        _ => run_maintenance_leaf_command("bootstrap", args, BOOTSTRAP_SPECS, BOOTSTRAP_USAGE),
    }
}

pub(crate) fn run_gate_subcommand(args: &[String]) -> ExitCode {
    match args.first().map(String::as_str) {
        Some(command) if is_help_arg(command) => {
            print!("{GATE_USAGE}");
            ExitCode::SUCCESS
        }
        Some("check-all") => run_check_all_gate(&args[1..], true, "targo trust gate check-all"),
        Some("scripts") => run_check_all_gate(&args[1..], false, "targo trust gate scripts"),
        Some("coherence") => run_coherence_gate(&args[1..]),
        Some("verify-examples") => crate::verify_examples_cli::run(&args[1..]),
        Some(command) => {
            eprintln!("targo trust gate: unknown command `{command}`");
            eprint!("{GATE_USAGE}");
            ExitCode::from(2)
        }
        None => {
            eprint!("{GATE_USAGE}");
            ExitCode::from(2)
        }
    }
}

/// `targo trust gate coherence` — verify the recorded first-party submodule SHAs
/// type-check together. Wraps `scripts/submodule-coherence-gate.sh` so the
/// build-coherence gate is reachable from the toolchain CLI (agents keep
/// bumping `trust-ir` ahead of its consumers and pushing non-building states).
fn run_coherence_gate(args: &[String]) -> ExitCode {
    let mut repo_root_arg: Option<PathBuf> = None;
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "--repo-root" | "--root" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust gate coherence: {} requires a path", args[index]);
                    return ExitCode::from(2);
                };
                repo_root_arg = Some(PathBuf::from(value));
                index += 2;
            }
            "-h" | "--help" => {
                println!("Usage: targo trust gate coherence [--repo-root PATH]");
                return ExitCode::SUCCESS;
            }
            other => {
                eprintln!("targo trust gate coherence: unknown option `{other}`");
                return ExitCode::from(2);
            }
        }
    }

    let repo_marker = "targo-trust/Cargo.toml";
    let Some((repo_root, _)) = repo_root_arg
        .map(|root| root.join(repo_marker).is_file().then_some((root, PathBuf::new())))
        .unwrap_or_else(|| resolve_repo_file(repo_marker))
    else {
        eprintln!("targo trust gate coherence: could not find {repo_marker}");
        eprintln!("  Run from a Trust checkout or set TRUST_REPO_ROOT=/path/to/Trust.");
        return ExitCode::from(2);
    };

    let script = "scripts/submodule-coherence-gate.sh";
    if !repo_root.join(script).is_file() {
        eprintln!("targo trust gate coherence: {script} not found under {}", repo_root.display());
        return ExitCode::from(2);
    }

    println!("=== Submodule coherence (recorded SHAs type-check together) ===");
    let mut command = command_in_repo("bash".to_string(), &repo_root, [script]);
    match bounded_script_output(&mut command, "submodule coherence gate") {
        Ok(output) if output.status.success() => {
            emit_script_output(&output);
            println!("targo trust gate coherence: PASS");
            ExitCode::SUCCESS
        }
        Ok(output) => {
            emit_script_output(&output);
            eprintln!("targo trust gate coherence: FAIL (gate exit {:?})", output.status.code());
            ExitCode::from(output.status.code().unwrap_or(1).clamp(1, 255) as u8)
        }
        Err(error) => {
            eprintln!("targo trust gate coherence: failed to run {script}: {error}");
            ExitCode::from(1)
        }
    }
}

const FALSIFY_USAGE: &str = "\
Usage: targo trust falsify [bash-gate args...]

Run the verifier falsification self-test (mutation gate). For every fixture in
tests/trust-falsification/proved/ the verifier MUST prove it; for every fixture
in tests/trust-falsification/mutant/ (a one-line-buggy twin of a proved case) it
MUST fail closed. Green only if every proof is non-vacuous AND every mutant is
refuted -- the load-bearing check that `proved` means something.

The gate runs against the toolchain's freshly-built stage2 trustc (override with
TRUSTC=/path/to/trustc). Exit 0 = GREEN, 1 = RED (a vacuous proof or surviving
mutant), 2 = could not locate the gate script.

Examples:
  targo trust falsify
  TRUSTC=build/aarch64-apple-darwin/stage2/bin/trustc targo trust falsify
";

/// `targo trust falsify` -- run the verifier mutation self-test natively.
///
/// Wraps `scripts/trust_falsification_gate.sh` as a first-class subcommand and
/// points it at the toolchain's own stage2 trustc, so soundness non-vacuity is a
/// built-in toolchain check rather than an out-of-tree script.
pub(crate) fn run_falsify_subcommand(args: &[String]) -> ExitCode {
    if args.first().map(String::as_str).is_some_and(is_help_arg) {
        print!("{FALSIFY_USAGE}");
        return ExitCode::SUCCESS;
    }

    let Some((repo_root, script_path)) = resolve_repo_file("scripts/trust_falsification_gate.sh")
    else {
        eprintln!(
            "targo trust falsify: requires `scripts/trust_falsification_gate.sh`, but it was not found"
        );
        eprintln!("  Run from a Trust checkout or set TRUST_REPO_ROOT=/path/to/Trust.");
        return ExitCode::from(2);
    };

    let trustc_override = env::var_os("TRUSTC");
    let timeout_override = env::var_os("GATE_VERIFY_TIMEOUT_SECS");
    #[cfg(unix)]
    let bash = Path::new("/bin/bash");
    #[cfg(not(unix))]
    let bash: &Path = {
        eprintln!(
            "targo trust falsify: the hardened gate requires the trusted /bin/bash process-group boundary available on Unix hosts"
        );
        return ExitCode::from(2);
    };
    let mut command = Command::new(bash);
    command
        .env_clear()
        .env("PATH", "/usr/bin:/bin:/usr/sbin:/sbin")
        .env("LC_ALL", "C")
        .env("LANG", "C")
        .env("TZ", "UTC")
        .arg(&script_path)
        .args(args)
        .current_dir(&repo_root);
    if let Some(timeout) = timeout_override {
        command.env("GATE_VERIFY_TIMEOUT_SECS", timeout);
    }

    // Default the gate at the toolchain's freshly-built stage2 trustc; the
    // script's own `build/host/...` default can be stale on a multi-target tree.
    if let Some(trustc) = trustc_override {
        command.env("TRUSTC", trustc);
    } else {
        match find_stage2_trustc(&repo_root) {
            Ok(Some(trustc)) => {
                command.env("TRUSTC", trustc);
            }
            Ok(None) => {
                eprintln!("targo trust falsify: no repo-local stage2 trustc was found");
                return ExitCode::from(2);
            }
            Err(error) => {
                eprintln!("targo trust falsify: {error}");
                return ExitCode::from(2);
            }
        }
    }

    run_child("targo trust falsify", command)
}

const SURVEY_USAGE: &str = "\
Usage: targo trust survey <crate> [out-dir] [--contracts]

Survey a cargo package through the Trust verifier and emit deterministic
per-obligation JSON (status + the precise blocking MIR reason), bounded so no
single hard obligation can hang the run. Operates on the current cargo workspace.

  crate        cargo package name to survey (required)
  out-dir      where to drop the JSON + log (default: target/trust/survey)
  --contracts  label a second contracts replay for cite-discharge compatibility;
               verifier runs already activate cfg(trust_verify) and include contracts

Pairs with `targo trust gap` to classify the result. Runs against the
canonical targo bound to the selected Trust compiler.

Examples:
  targo trust survey my-crate
  targo trust survey my-crate --contracts
";

/// The `gap` usage text, so its refusal path can print the same help the
/// `--help` path does instead of a second, drifting copy.
pub(crate) fn gap_usage_text() -> &'static str {
    GAP_USAGE
}

const GAP_USAGE: &str = "\
Usage: targo trust gap [survey.json]

Classify a `targo trust survey` JSON into user-logic vs compiler-derived
boilerplate and print the user-logic gap (proved/unknown/failed) plus a
by-reason histogram of what is blocking each unknown/failed obligation.

  survey.json  a survey JSON (default: newest target/trust/survey/*.json)

Examples:
  targo trust survey my-crate && targo trust gap
  targo trust gap target/trust/survey/my-crate-20260615-101500.json
";

/// `targo trust survey` -- run a package through the verifier and emit
/// per-obligation JSON. Inherits the caller's workspace cwd. The script invokes
/// the public `targo trust check --survey` policy instead of relying on an
/// ambient compiler-policy variable, which the hardened frontend rejects.
pub(crate) fn run_survey_subcommand(args: &[String]) -> ExitCode {
    if args.first().map(String::as_str).is_some_and(is_help_arg) {
        print!("{SURVEY_USAGE}");
        return ExitCode::SUCCESS;
    }

    let Some((_repo_root, script_path)) = resolve_repo_file("scripts/trust_survey.sh") else {
        eprintln!("targo trust survey: requires `scripts/trust_survey.sh`, but it was not found");
        eprintln!("  Run from a Trust checkout or set TRUST_REPO_ROOT=/path/to/Trust.");
        return ExitCode::from(2);
    };

    let mut command = Command::new("bash");
    // Inherit the caller's cwd (their cargo workspace); do NOT chdir to the
    // toolchain root. Always replace an ambient TARGO value with the canonical
    // frontend bound to this Trust compiler so the script cannot cross sysroots.
    command.arg(&script_path).args(args);
    let targo = match crate::pipeline::discover_native_trust_cargo_checked() {
        Ok(targo) => targo,
        Err(error) => {
            eprintln!("targo trust survey: {error}");
            return ExitCode::from(2);
        }
    };
    command.env("TARGO", targo);

    run_child("targo trust survey", command)
}

/// `targo trust gap` -- classify a survey JSON into user-logic vs derived
/// boilerplate with a by-reason histogram. Inherits the caller's cwd, so the
/// default newest-survey lookup resolves under their `./target/trust/survey`.
///
/// The subject here is the caller's own crate, not this repository, so the
/// classification runs in-process. Reading a JSON the user just produced does
/// not need a Trust checkout or a Python interpreter, and demanding either put
/// a per-crate report out of reach of anyone running an installed toolchain.
pub(crate) fn run_gap_subcommand(args: &[String]) -> ExitCode {
    if args.first().map(String::as_str).is_some_and(is_help_arg) {
        print!("{GAP_USAGE}");
        return ExitCode::SUCCESS;
    }

    crate::gap::run(args)
}

/// `targo trust cite-discharge` -- compose the proof-carrying certificate (Trust =
/// Clean fusion) from a structural survey (L0) + a `--contracts` survey (L0+L1) + a
/// cite-map + the Clean corpus. Fail-closed: a captured-but-undischarged postcondition
/// reaches `CertifiedModuloCite` only when its cited theorem is declared and sorry-free.
pub(crate) fn run_cite_discharge_subcommand(args: &[String]) -> ExitCode {
    if args.first().map(String::as_str).is_some_and(is_help_arg) {
        print!(
            "Usage: targo trust cite-discharge --structural S.json --contracts C.json \
             --cite-map M.json --corpus DIR\n\n\
             Compose the proof-carrying certificate: combine a structural survey (L0 \
             safety) + a --contracts survey (L0+L1) + a cite-map + the Clean corpus into \
             the honest per-function ProofCarryingStatus (CertifiedToAxioms / \
             CertifiedModuloCite / L0OnlyL1Open / Incomplete). Fail-closed.\n"
        );
        return ExitCode::SUCCESS;
    }

    let Some((_repo_root, script_path)) = resolve_repo_file("scripts/trust_cite_discharge.py")
    else {
        eprintln!(
            "targo trust cite-discharge: requires `scripts/trust_cite_discharge.py`, \
             but it was not found"
        );
        eprintln!("  Run from a Trust checkout or set TRUST_REPO_ROOT=/path/to/Trust.");
        return ExitCode::from(2);
    };

    let mut command = Command::new(python_command());
    command.arg(&script_path).args(args);

    run_child("targo trust cite-discharge", command)
}

pub(crate) fn try_run_release_script_subcommand(args: &[String]) -> Option<ExitCode> {
    match args.first().map(String::as_str) {
        Some("validate") => Some(run_release_validate_subcommand(&args[1..])),
        _ => None,
    }
}

pub(crate) fn release_script_usage_text() -> &'static str {
    "\
  targo trust release validate <gate>  Run release validation gates"
}

fn run_release_validate_subcommand(args: &[String]) -> ExitCode {
    match args.first().map(String::as_str) {
        Some(command) if is_help_arg(command) => {
            print!("{RELEASE_VALIDATE_USAGE}");
            ExitCode::SUCCESS
        }
        _ => run_leaf_command(
            "release validate",
            args,
            RELEASE_VALIDATE_SPECS,
            RELEASE_VALIDATE_USAGE,
        ),
    }
}

fn run_deps_rust_subcommand(args: &[String]) -> Option<ExitCode> {
    let command = args.first().map(String::as_str)?;
    if is_help_arg(command) {
        print!("{DEPS_USAGE}");
        return Some(ExitCode::SUCCESS);
    }

    match command {
        "status" => Some(run_deps_report(command, &args[1..], false)),
        "diff" | "upstream-plan" => Some(run_deps_report(command, &args[1..], false)),
        "export" | "import" | "lock" => Some(run_deps_mutation(command, &args[1..])),
        "validate" => Some(run_deps_report(command, &args[1..], true)),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DepsGate {
    None,
    Full,
    LiveCloneAlignment,
    SnapshotIntegrity,
    RefreshReadiness,
}

impl DepsGate {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "all" | "full" | "verify" | "validation" => Ok(Self::Full),
            "live-clone-alignment" | "live-clones" => Ok(Self::LiveCloneAlignment),
            "snapshot-integrity" | "snapshots" => Ok(Self::SnapshotIntegrity),
            "refresh-readiness" | "refresh" => Ok(Self::RefreshReadiness),
            other => Err(format!("unsupported --gate `{other}`")),
        }
    }

    fn requires_deep_hash(self) -> bool {
        matches!(self, Self::Full | Self::SnapshotIntegrity | Self::RefreshReadiness)
    }

    fn failed(self, report: &trust_deps::AlignmentReport) -> bool {
        match self {
            Self::None => false,
            Self::Full | Self::RefreshReadiness => report.summary.failed > 0,
            Self::LiveCloneAlignment => report.summary.live_clone_misaligned > 0,
            Self::SnapshotIntegrity => report.summary.snapshot_mismatch > 0,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DepsView {
    Status,
    Diff,
    RefreshPlan,
}

impl DepsView {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "status" | "summary" => Ok(Self::Status),
            "diff" | "drift" => Ok(Self::Diff),
            "refresh-plan" | "upstream-plan" => Ok(Self::RefreshPlan),
            other => Err(format!("unsupported --view `{other}`")),
        }
    }
}

fn run_deps_mutation(command: &str, args: &[String]) -> ExitCode {
    let mut json = false;
    let mut options = trust_deps::MutationOptions::for_root(
        env::current_dir().unwrap_or_else(|_| PathBuf::from(".")),
    );
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "--json" | "--format=json" => {
                json = true;
                index += 1;
            }
            "--format" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: --format requires a value");
                    return ExitCode::from(2);
                };
                match value.as_str() {
                    "json" => json = true,
                    "text" | "terminal" => json = false,
                    other => {
                        eprintln!("targo trust deps {command}: unsupported --format `{other}`");
                        return ExitCode::from(2);
                    }
                }
                index += 2;
            }
            "--apply" | "--write" | "--in-place" => {
                options.apply = true;
                index += 1;
            }
            "--fetch" => {
                options.fetch = true;
                index += 1;
            }
            "--allow-overwrite-local-drift" => {
                options.allow_overwrite_local_drift = true;
                index += 1;
            }
            "--overlay-policy" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: --overlay-policy requires a value");
                    return ExitCode::from(2);
                };
                let Some(policy) = trust_deps::OverlayPolicy::parse(value) else {
                    eprintln!("targo trust deps {command}: unsupported --overlay-policy `{value}`");
                    return ExitCode::from(2);
                };
                options.overlay_policy = policy;
                index += 2;
            }
            "--allow-bootstrap-overlays" => {
                options.overlay_policy = trust_deps::OverlayPolicy::Bootstrap;
                index += 1;
            }
            "--repo-root" | "--root" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: {} requires a path", args[index]);
                    return ExitCode::from(2);
                };
                options.root = PathBuf::from(value);
                options.lock_file = options.root.join("trust-engines.lock");
                index += 2;
            }
            "--lock-file" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: --lock-file requires a path");
                    return ExitCode::from(2);
                };
                options.lock_file = PathBuf::from(value);
                index += 2;
            }
            "--clone-root" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: --clone-root requires a path");
                    return ExitCode::from(2);
                };
                options.clone_root = PathBuf::from(value);
                index += 2;
            }
            "--out" | "--output-dir" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: {} requires a path", args[index]);
                    return ExitCode::from(2);
                };
                options.output_dir = Some(PathBuf::from(value));
                index += 2;
            }
            "--dependency" | "--dep" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: {} requires a name", args[index]);
                    return ExitCode::from(2);
                };
                options.dependencies.push(value.clone());
                index += 2;
            }
            "-h" | "--help" => {
                print!(
                    "Usage: targo trust deps {command} [--json] [--fetch] [--dependency NAME] [--apply]\n\n\
                     Additional options:\n\
                       --repo-root PATH\n\
                       --lock-file PATH\n\
                       --clone-root PATH\n\
                       --out DIR                         export only; write patch manifest\n\
                       --allow-overwrite-local-drift      import only; confirms exported drift was reviewed\n\
                       --overlay-policy forbid|bootstrap  default forbid; bootstrap explicitly applies dependency-modes overlays\n"
                );
                return ExitCode::SUCCESS;
            }
            other if other.starts_with('-') => {
                eprintln!("targo trust deps {command}: unknown option `{other}`");
                return ExitCode::from(2);
            }
            other => {
                options.dependencies.push(other.to_string());
                index += 1;
            }
        }
    }

    if command != "import" && options.allow_overwrite_local_drift {
        eprintln!("targo trust deps {command}: --allow-overwrite-local-drift is import-only");
        return ExitCode::from(2);
    }

    let report = match command {
        "export" => trust_deps::run_export_transaction(&options),
        "import" => trust_deps::run_import_transaction(&options),
        "lock" => trust_deps::run_lock_transaction(&options),
        _ => unreachable!("validated dependency mutation command"),
    };
    let report = match report {
        Ok(report) => report,
        Err(error) => {
            eprintln!("targo trust deps {command}: {error}");
            return ExitCode::from(1);
        }
    };

    if json {
        match trust_deps::render_mutation_json(&report) {
            Ok(rendered) => println!("{rendered}"),
            Err(error) => {
                eprintln!("targo trust deps {command}: failed to render JSON: {error}");
                return ExitCode::from(1);
            }
        }
    } else {
        print!("{}", trust_deps::render_mutation_text(&report));
    }

    if report.summary.failed > 0 { ExitCode::from(1) } else { ExitCode::SUCCESS }
}

fn run_deps_report(command: &str, args: &[String], gate: bool) -> ExitCode {
    let mut json = false;
    let mut json_output: Option<PathBuf> = None;
    let mut gate_mode = if gate { DepsGate::Full } else { DepsGate::None };
    let mut view = match command {
        "diff" => DepsView::Diff,
        "upstream-plan" => DepsView::RefreshPlan,
        _ => DepsView::Status,
    };
    let mut options = trust_deps::StatusOptions::for_root(
        env::current_dir().unwrap_or_else(|_| PathBuf::from(".")),
    );
    if gate_mode.requires_deep_hash() {
        options.deep_hash = true;
    }
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "--json" | "--format=json" => {
                json = true;
                index += 1;
            }
            "--format" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: --format requires a value");
                    return ExitCode::from(2);
                };
                match value.as_str() {
                    "json" => json = true,
                    "text" | "terminal" => json = false,
                    other => {
                        eprintln!("targo trust deps {command}: unsupported --format `{other}`");
                        return ExitCode::from(2);
                    }
                }
                index += 2;
            }
            "--fetch" => {
                options.fetch = true;
                index += 1;
            }
            option if option.starts_with("--json-output=") => {
                let value = option.strip_prefix("--json-output=").expect("prefix checked");
                if value.is_empty() {
                    eprintln!("targo trust deps {command}: --json-output requires a path");
                    return ExitCode::from(2);
                }
                json_output = Some(PathBuf::from(value));
                index += 1;
            }
            option if option.starts_with("--report=") => {
                let value = option.strip_prefix("--report=").expect("prefix checked");
                if value.is_empty() {
                    eprintln!("targo trust deps {command}: --report requires a path");
                    return ExitCode::from(2);
                }
                json_output = Some(PathBuf::from(value));
                index += 1;
            }
            "--json-output" | "--report" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: {} requires a path", args[index]);
                    return ExitCode::from(2);
                };
                json_output = Some(PathBuf::from(value));
                index += 2;
            }
            "--deep-hash" => {
                options.deep_hash = true;
                index += 1;
            }
            "--production" => {
                // Production dependency evidence must compare the checked-in
                // source snapshot hash, even for non-gating status reports.
                options.deep_hash = true;
                index += 1;
            }
            option if option.starts_with("--source=") => {
                let value = option.strip_prefix("--source=").expect("prefix checked");
                if !apply_deps_source(command, value, &mut options) {
                    return ExitCode::from(2);
                }
                index += 1;
            }
            "--source" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: --source requires a value");
                    return ExitCode::from(2);
                };
                if !apply_deps_source(command, value, &mut options) {
                    return ExitCode::from(2);
                }
                index += 2;
            }
            option if option.starts_with("--gate=") => {
                let value = option.strip_prefix("--gate=").expect("prefix checked");
                match DepsGate::parse(value) {
                    Ok(parsed) => {
                        gate_mode = parsed;
                        if gate_mode.requires_deep_hash() {
                            options.deep_hash = true;
                        }
                        index += 1;
                    }
                    Err(message) => {
                        eprintln!("targo trust deps {command}: {message}");
                        return ExitCode::from(2);
                    }
                }
            }
            "--gate" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: --gate requires a value");
                    return ExitCode::from(2);
                };
                match DepsGate::parse(value) {
                    Ok(parsed) => {
                        gate_mode = parsed;
                        if gate_mode.requires_deep_hash() {
                            options.deep_hash = true;
                        }
                        index += 2;
                    }
                    Err(message) => {
                        eprintln!("targo trust deps {command}: {message}");
                        return ExitCode::from(2);
                    }
                }
            }
            option if option.starts_with("--view=") => {
                let value = option.strip_prefix("--view=").expect("prefix checked");
                match DepsView::parse(value) {
                    Ok(parsed) => {
                        view = parsed;
                        index += 1;
                    }
                    Err(message) => {
                        eprintln!("targo trust deps {command}: {message}");
                        return ExitCode::from(2);
                    }
                }
            }
            "--view" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: --view requires a value");
                    return ExitCode::from(2);
                };
                match DepsView::parse(value) {
                    Ok(parsed) => {
                        view = parsed;
                        index += 2;
                    }
                    Err(message) => {
                        eprintln!("targo trust deps {command}: {message}");
                        return ExitCode::from(2);
                    }
                }
            }
            "--repo-root" | "--root" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: {} requires a path", args[index]);
                    return ExitCode::from(2);
                };
                options.root = PathBuf::from(value);
                options.lock_file = options.root.join("trust-engines.lock");
                index += 2;
            }
            "--lock-file" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: --lock-file requires a path");
                    return ExitCode::from(2);
                };
                options.lock_file = PathBuf::from(value);
                index += 2;
            }
            "--clone-root" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: --clone-root requires a path");
                    return ExitCode::from(2);
                };
                options.clone_root = PathBuf::from(value);
                index += 2;
            }
            "--dependency" | "--dep" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("targo trust deps {command}: {} requires a name", args[index]);
                    return ExitCode::from(2);
                };
                options.dependencies.push(value.clone());
                index += 2;
            }
            "-h" | "--help" => {
                print!("{DEPS_USAGE}");
                return ExitCode::SUCCESS;
            }
            other => {
                eprintln!("targo trust deps {command}: unknown option `{other}`");
                return ExitCode::from(2);
            }
        }
    }

    let report = match trust_deps::collect_status(&options) {
        Ok(report) => report,
        Err(error) => {
            eprintln!("targo trust deps {command}: {error}");
            return ExitCode::from(1);
        }
    };

    let rendered_json = if json || json_output.is_some() {
        match trust_deps::render_json(&report) {
            Ok(rendered) => Some(rendered),
            Err(error) => {
                eprintln!("targo trust deps {command}: failed to render JSON: {error}");
                return ExitCode::from(1);
            }
        }
    } else {
        None
    };

    if let Some(path) = &json_output {
        if let Err(error) = write_deps_json_report(
            &options.root,
            path,
            rendered_json.as_deref().expect("rendered JSON"),
        ) {
            eprintln!(
                "targo trust deps {command}: failed to write JSON report to {}: {error}",
                path.display()
            );
            return ExitCode::from(2);
        }
    }

    if json {
        println!("{}", rendered_json.as_deref().expect("rendered JSON"));
    } else {
        match view {
            DepsView::Diff => print!("{}", trust_deps::render_diff_text(&report)),
            DepsView::RefreshPlan => {
                print!("{}", trust_deps::render_upstream_plan_text(&report))
            }
            DepsView::Status => print!("{}", trust_deps::render_text(&report)),
        }
    }

    if gate_mode.failed(&report) { ExitCode::from(1) } else { ExitCode::SUCCESS }
}

fn write_deps_json_report(root: &Path, path: &Path, rendered: &str) -> Result<(), String> {
    let output_path = if path.is_absolute() { path.to_path_buf() } else { root.join(path) };
    if let Some(parent) = output_path.parent().filter(|parent| !parent.as_os_str().is_empty()) {
        fs::create_dir_all(parent)
            .map_err(|error| format!("could not create directory: {error}"))?;
    }
    fs::write(output_path, format!("{rendered}\n"))
        .map_err(|error| format!("could not write report: {error}"))
}

fn apply_deps_source(command: &str, value: &str, options: &mut trust_deps::StatusOptions) -> bool {
    match value {
        "git-index" | "checked-in" | "snapshot" => {
            options.deep_hash = true;
            true
        }
        "fingerprint" | "fast" => true,
        other => {
            eprintln!("targo trust deps {command}: unsupported --source `{other}`");
            false
        }
    }
}

fn run_check_all_gate(args: &[String], mut include_cargo: bool, usage_command: &str) -> ExitCode {
    let mut repo_root_arg: Option<PathBuf> = None;
    let mut targo_arg: Option<(PathBuf, &'static str)> = None;
    let mut run_tests = false;
    let mut run_host_diagnostics = false;
    let mut index = 0;

    while index < args.len() {
        match args[index].as_str() {
            "--repo-root" | "--root" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("{usage_command}: {} requires a path", args[index]);
                    return ExitCode::from(2);
                };
                repo_root_arg = Some(PathBuf::from(value));
                index += 2;
            }
            "--targo" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("{usage_command}: --targo requires an executable");
                    return ExitCode::from(2);
                };
                targo_arg = Some((PathBuf::from(value), "--targo"));
                index += 2;
            }
            "--cargo" => {
                let Some(value) = args.get(index + 1) else {
                    eprintln!("{usage_command}: --cargo requires an executable");
                    return ExitCode::from(2);
                };
                targo_arg = Some((PathBuf::from(value), "--cargo"));
                index += 2;
            }
            "--quick" | "--no-cargo" => {
                include_cargo = false;
                index += 1;
            }
            "--run-tests" => {
                run_tests = true;
                index += 1;
            }
            "--host-diagnostics" => {
                run_host_diagnostics = true;
                index += 1;
            }
            "-h" | "--help" => {
                print!(
                    "Usage: {usage_command} [--repo-root PATH] [--targo TARGO] [--quick|--no-cargo] [--run-tests] [--host-diagnostics]\n"
                );
                return ExitCode::SUCCESS;
            }
            other => {
                eprintln!("{usage_command}: unknown option `{other}`");
                return ExitCode::from(2);
            }
        }
    }

    if run_tests && !include_cargo {
        eprintln!("{usage_command}: --run-tests conflicts with --quick/--no-cargo");
        return ExitCode::from(2);
    }

    let repo_marker = "targo-trust/Cargo.toml";
    let Some((repo_root, _)) = repo_root_arg
        .map(|root| root.join(repo_marker).is_file().then_some((root, PathBuf::new())))
        .unwrap_or_else(|| resolve_repo_file(repo_marker))
    else {
        eprintln!("{usage_command}: could not find {repo_marker}");
        eprintln!("  Run from a Trust checkout or set TRUST_REPO_ROOT=/path/to/Trust.");
        return ExitCode::from(2);
    };
    let repo_root = match fs::canonicalize(&repo_root) {
        Ok(root) => root,
        Err(error) => {
            eprintln!("{usage_command}: could not canonicalize repository root: {error}");
            return ExitCode::from(2);
        }
    };
    if let Err(error) = require_clean_git_checkout(&repo_root) {
        eprintln!("{usage_command}: {error}");
        return ExitCode::from(2);
    }

    let targo = if include_cargo {
        match resolve_stage2_targo(
            &repo_root,
            targo_arg.as_ref().map(|(path, flag)| (path.as_path(), *flag)),
        ) {
            Ok(targo) => Some(targo),
            Err(error) => {
                eprintln!("{usage_command}: {error}");
                return ExitCode::from(2);
            }
        }
    } else {
        None
    };
    let stage2_identity = if let Some(targo) = targo.as_deref() {
        match validate_check_all_stage2_toolchain(&repo_root, targo) {
            Ok(identity) => Some(identity),
            Err(error) => {
                eprintln!("{usage_command}: {error}");
                return ExitCode::from(2);
            }
        }
    } else {
        None
    };

    let mut failed = false;

    println!("=== Script syntax and verifier examples ===");
    failed |= !run_gate_step(
        "python syntax",
        command_in_repo(
            python_command(),
            &repo_root,
            [
                "-m",
                "py_compile",
                "scripts/check_cargo_manifest_alignment.py",
                "scripts/check_ledger_expirations.py",
                "scripts/check_seed_freshness.py",
                "scripts/check_toolchain_coherence.py",
            ],
        ),
    );
    failed |= !run_shell_syntax_gate(&repo_root);

    println!("\n=== Test-parity ledger expirations ===");
    failed |= !run_gate_step(
        "test-parity ledger expirations",
        command_in_repo(
            python_command(),
            &repo_root,
            ["scripts/check_ledger_expirations.py", "--warn-days", "14"],
        ),
    );

    println!("\n=== Cargo manifest alignment ===");
    failed |= !run_gate_step(
        "cargo manifest alignment",
        command_in_repo(
            python_command(),
            &repo_root,
            ["scripts/check_cargo_manifest_alignment.py", "--workspace-drift-advisory"],
        ),
    );
    failed |= !run_gate_step(
        "cargo manifest checker self-check",
        command_in_repo(
            python_command(),
            &repo_root,
            ["scripts/check_cargo_manifest_alignment.py", "--self-check"],
        ),
    );
    failed |= !run_gate_step(
        "cargo default fanout tree proof",
        command_in_repo(
            python_command(),
            &repo_root,
            ["scripts/check_cargo_manifest_alignment.py", "--fanout-tree-proof"],
        ),
    );

    println!("\n=== Toolchain coherence ===");
    failed |= !run_gate_step(
        "toolchain coherence",
        command_in_repo(python_command(), &repo_root, ["scripts/check_toolchain_coherence.py"]),
    );

    println!("\n=== Stage0 seed freshness ===");
    failed |= !run_gate_step(
        "stage0 seed freshness",
        command_in_repo(python_command(), &repo_root, ["scripts/check_seed_freshness.py"]),
    );

    println!("\n=== TCB panic-freedom ratchet ===");
    failed |= !run_gate_step(
        "TCB panic surface within baseline",
        command_in_repo("bash".to_string(), &repo_root, ["scripts/check_tcb_panic_freedom.sh"]),
    );

    println!("\n=== Submodule pin coherence ===");
    failed |= !run_gate_step(
        "submodule pin coherence",
        command_in_repo("bash".to_string(), &repo_root, ["scripts/check_pin_coherence.sh"]),
    );

    println!("\n=== Lean bridge pin coherence ===");
    failed |= !run_gate_step(
        "Lean bridge pin coherence",
        command_in_repo("bash".to_string(), &repo_root, ["scripts/check_bridge_pin.sh", "--check"]),
    );
    if include_cargo {
        println!("=== stage2 verify examples ===");
        let authenticated_trustc =
            stage2_identity.as_ref().map(|identity| identity.trustc_path.as_path());
        if authenticated_trustc
            .is_some_and(|trustc| run_stage2_verify_examples_gate(&repo_root, trustc))
        {
            println!("PASS: stage2 verify examples");
        } else {
            eprintln!("FAIL: stage2 verify examples");
            failed = true;
        }
    } else {
        println!("=== verify-example metadata ===");
        if crate::examples_cli::run_verify_metadata_gate(&repo_root) {
            println!("PASS: verify-example metadata");
        } else {
            eprintln!("FAIL: verify-example metadata");
            failed = true;
        }
    }

    if include_cargo {
        failed |= !require_file(
            &repo_root.join("crates/Cargo.lock"),
            "lockfile required for --locked gate",
        );
        failed |= !require_file(
            &repo_root.join("targo-trust/Cargo.lock"),
            "lockfile required for --locked gate",
        );
        failed |= !require_file(
            &repo_root.join(TEMPORAL_FABRIC_LOCK),
            "temporal boundary fixture lockfile required for --locked gate",
        );

        println!("\n=== Temporal fixture boundary (fail-closed) ===");
        // This external-consumer fixture intentionally omits the non-transitive
        // source patches needed for proof-bearing compilation. Its complete
        // dependency graph must still resolve reproducibly, and the public
        // automatic temporal route must reject it for the primary unbound-build
        // reason without executing ty. Seed only the exact locked graph before
        // making both observations offline; successful compilation is not
        // expected.
        failed |= !run_targo_gate(
            &repo_root,
            targo.as_deref().expect("resolved targo"),
            ["fetch", "--manifest-path", TEMPORAL_FABRIC_MANIFEST, "--locked"],
        );
        failed |= !run_targo_gate(
            &repo_root,
            targo.as_deref().expect("resolved targo"),
            [
                "tree",
                "--manifest-path",
                TEMPORAL_FABRIC_MANIFEST,
                "--locked",
                "--offline",
                "--edges",
                "normal",
            ],
        );
        failed |= !run_temporal_fixture_boundary_gate(
            &repo_root,
            targo.as_deref().expect("resolved targo"),
        );

        println!("\n=== G19 build determinism (trust-ir conformance) ===");
        failed |= !run_targo_gate(
            &repo_root,
            targo.as_deref().expect("resolved targo"),
            [
                "test",
                "--manifest-path",
                "first-party/trust-ir/Cargo.toml",
                "--locked",
                "-p",
                "trust-ir-conformance",
                "--test",
                "build_determinism",
            ],
        );

        println!("\n=== Workspace trust crates (lib check) ===");
        failed |= !run_targo_gate(
            &repo_root,
            targo.as_deref().expect("resolved targo"),
            ["check", "--manifest-path", "crates/Cargo.toml", "--locked", "--workspace", "--lib"],
        );

        println!("\n=== Integration tests (test targets) ===");
        failed |= !run_targo_gate(
            &repo_root,
            targo.as_deref().expect("resolved targo"),
            [
                "check",
                "--manifest-path",
                "crates/Cargo.toml",
                "--locked",
                "--tests",
                "-p",
                "trust-integration-tests",
            ],
        );

        println!("\n=== targo-trust CLI (all targets) ===");
        failed |= !run_targo_gate(
            &repo_root,
            targo.as_deref().expect("resolved targo"),
            ["check", "--manifest-path", "targo-trust/Cargo.toml", "--locked", "--all-targets"],
        );

        println!("\n=== Upstream compatibility scorecard smoke ===");
        for test in [
            "smoke_porting_imports_fixture_files_and_records_audit_and_missing_proof",
            "scorecard_log_mode_reports_seeded_failures_and_reviewed_drift",
        ] {
            failed |= !run_targo_gate(
                &repo_root,
                targo.as_deref().expect("resolved targo"),
                [
                    "test",
                    "--manifest-path",
                    "crates/Cargo.toml",
                    "--locked",
                    "-p",
                    "trust-upstream-compat",
                    "--test",
                    "porting_engine",
                    test,
                ],
            );
        }

        if run_tests {
            println!("\n=== Workspace Trust tests ===");
            failed |= !run_targo_gate(
                &repo_root,
                targo.as_deref().expect("resolved targo"),
                [
                    "test",
                    "--manifest-path",
                    "crates/Cargo.toml",
                    "--locked",
                    "--workspace",
                    "--lib",
                    "--tests",
                    "--features",
                    "trust-bmc/trust-mc-core-types",
                    "--no-fail-fast",
                ],
            );
            println!("\n=== targo-trust tests ===");
            failed |= !run_targo_gate(
                &repo_root,
                targo.as_deref().expect("resolved targo"),
                [
                    "test",
                    "--manifest-path",
                    "targo-trust/Cargo.toml",
                    "--locked",
                    "--all-targets",
                    "--no-fail-fast",
                ],
            );
        }
    }

    if run_host_diagnostics {
        println!("\n=== Host cargo diagnostics (advisory) ===");
        let host_cargo = env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
        let mut command = Command::new(host_cargo);
        command.current_dir(&repo_root).env("CARGO_SKIP_CACHE", "1").args([
            "check",
            "--manifest-path",
            "targo-trust/Cargo.toml",
            "--locked",
            "--all-targets",
        ]);
        if !run_gate_step("host cargo diagnostics", command) {
            eprintln!(
                "WARN: optional host Cargo diagnostics failed; golden Trust gates are unaffected"
            );
        }
    }

    if let (Some(expected), Some(targo)) = (stage2_identity.as_ref(), targo.as_deref()) {
        println!("\n=== Stage2 toolchain identity recheck ===");
        match validate_check_all_stage2_toolchain(&repo_root, targo) {
            Ok(observed) if observed == *expected => {
                println!("PASS: stage2 Targo/Trustc identity remained stable");
            }
            Ok(observed) => {
                eprintln!(
                    "FAIL: stage2 Targo/Trustc identity changed while the gate was running\n  before: {expected:?}\n  after:  {observed:?}"
                );
                failed = true;
            }
            Err(error) => {
                eprintln!("FAIL: stage2 Targo/Trustc identity recheck failed: {error}");
                failed = true;
            }
        }
    }
    println!("\n=== Repository cleanliness recheck ===");
    if let Err(error) = require_clean_git_checkout(&repo_root) {
        eprintln!("FAIL: {error}");
        failed = true;
    } else {
        println!("PASS: repository remained clean");
    }

    if failed {
        eprintln!("{usage_command}: one or more checks failed");
        ExitCode::from(1)
    } else {
        println!("{usage_command}: all selected checks passed");
        ExitCode::SUCCESS
    }
}

fn run_stage2_verify_examples_gate(repo_root: &Path, authenticated_trustc: &Path) -> bool {
    crate::verify_examples_cli::run(&stage2_verify_examples_args(repo_root, authenticated_trustc))
        == ExitCode::SUCCESS
}

fn stage2_verify_examples_args(repo_root: &Path, authenticated_trustc: &Path) -> Vec<String> {
    let report = repo_root.join("target/trust/gates/verify-examples.json");
    vec![
        "--repo-root".to_string(),
        repo_root.display().to_string(),
        "--trustc".to_string(),
        authenticated_trustc.display().to_string(),
        "--json-output".to_string(),
        report.display().to_string(),
    ]
}

fn find_stage2_trustc(repo_root: &Path) -> Result<Option<PathBuf>, String> {
    discover_unique_repo_stage2_tool(repo_root, "trustc")
}

fn resolve_stage2_targo(
    repo_root: &Path,
    explicit: Option<(&Path, &'static str)>,
) -> Result<PathBuf, String> {
    if let Some((path, flag)) = explicit {
        let path = if path.is_absolute() { path.to_path_buf() } else { repo_root.join(path) };
        match validate_repo_stage2_tool(repo_root, &path, flag, "targo") {
            Ok(path) => return Ok(path),
            Err(direct_error) => {
                // Bootstrap's `build/host` convenience alias is normally a
                // directory symlink. Resolve only an intermediate alias, then
                // retain and execute the exact canonical repo-local stage2
                // path. A symlinked executable leaf remains forbidden.
                if fs::symlink_metadata(&path)
                    .is_ok_and(|metadata| !metadata.file_type().is_symlink())
                {
                    if let Ok(canonical) = fs::canonicalize(&path) {
                        if canonical != path {
                            if let Ok(validated) =
                                validate_repo_stage2_tool(repo_root, &canonical, flag, "targo")
                            {
                                return Ok(validated);
                            }
                        }
                    }
                }
                return Err(direct_error);
            }
        }
    }

    find_stage2_targo(repo_root)?.ok_or_else(|| {
        "stage2 targo not found; build build/host/stage2/bin/targo or pass --targo build/host/stage2/bin/targo"
            .to_string()
    })
}

fn find_stage2_targo(repo_root: &Path) -> Result<Option<PathBuf>, String> {
    discover_unique_repo_stage2_tool(repo_root, "targo")
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CheckAllStage2Identity {
    repo_head: String,
    targo_path: PathBuf,
    targo_sha256: String,
    targo_release: String,
    targo_host: String,
    trustc_path: PathBuf,
    trustc_sha256: String,
    trustc_commit: String,
}

fn validate_check_all_stage2_toolchain(
    repo_root: &Path,
    targo: &Path,
) -> Result<CheckAllStage2Identity, String> {
    let targo = validate_repo_stage2_tool(repo_root, targo, "check-all", "targo")?;
    let bin_dir = targo.parent().ok_or_else(|| {
        format!("check-all stage2 targo has no bin directory: {}", targo.display())
    })?;
    let trustc = validate_repo_stage2_tool(
        repo_root,
        &bin_dir.join(format!("trustc{}", env::consts::EXE_SUFFIX)),
        "check-all sibling",
        "trustc",
    )?;

    let repo_head = git_head(repo_root)?;
    let targo_sha256 = sha256_executable(&targo)?;
    let trustc_sha256 = sha256_executable(&trustc)?;
    let trustc_version = checked_version_output(&trustc, "-vV", "trustc")?;
    let trustc_commit = unique_version_field(&trustc_version, "commit-hash")?;
    if !is_full_git_sha(&trustc_commit) {
        return Err(format!(
            "check-all sibling trustc reported malformed commit-hash `{trustc_commit}`"
        ));
    }
    if trustc_commit != repo_head {
        return Err(format!(
            "check-all refuses stale stage2 trustc: {} reports {}, current repository HEAD is {}; rebuild stage2 from the committed tree",
            trustc.display(),
            trustc_commit,
            repo_head
        ));
    }

    let targo_version = checked_version_output(&targo, "-Vv", "targo")?;
    let first_line = targo_version.lines().next().unwrap_or_default();
    if !first_line.starts_with("targo ") || first_line["targo ".len()..].trim().is_empty() {
        return Err(format!(
            "check-all stage2 executable did not identify as Targo: {} reported `{first_line}`",
            targo.display()
        ));
    }
    let targo_release = unique_version_field(&targo_version, "release")?;
    let targo_host = unique_version_field(&targo_version, "host")?;
    if targo_release.trim().is_empty() || targo_host.trim().is_empty() {
        return Err("check-all stage2 Targo reported an empty release or host identity".to_string());
    }
    let targo_sha256_after = sha256_executable(&targo)?;
    let trustc_sha256_after = sha256_executable(&trustc)?;
    let repo_head_after = git_head(repo_root)?;
    if targo_sha256_after != targo_sha256
        || trustc_sha256_after != trustc_sha256
        || repo_head_after != repo_head
    {
        return Err(
            "check-all stage2 tool bytes or repository HEAD changed during identity validation"
                .to_string(),
        );
    }

    Ok(CheckAllStage2Identity {
        repo_head,
        targo_sha256,
        targo_path: targo,
        targo_release,
        targo_host,
        trustc_sha256,
        trustc_path: trustc,
        trustc_commit,
    })
}

fn git_head(repo_root: &Path) -> Result<String, String> {
    crate::controlled_git::canonical_head(
        repo_root,
        "check-all repository HEAD probe",
        64 * 1024,
        Duration::from_secs(10),
    )
}

fn require_clean_git_checkout(repo_root: &Path) -> Result<(), String> {
    const MAX_STATUS_BYTES: usize = 1024 * 1024;
    let status = crate::controlled_git::exact_status_porcelain_v1(
        repo_root,
        "check-all repository cleanliness probe",
        MAX_STATUS_BYTES,
        Duration::from_secs(30),
    )?;
    if status.is_empty() {
        return Ok(());
    }
    let preview = status.iter().take(20).cloned().collect::<Vec<_>>().join("\n");
    Err(format!(
        "check-all requires a clean committed checkout; commit or remove these changes:\n{preview}"
    ))
}

fn checked_version_output(program: &Path, flag: &str, tool: &str) -> Result<String, String> {
    const MAX_VERSION_BYTES: usize = 64 * 1024;
    let mut command = Command::new(program);
    command.arg(flag);
    let output = bounded_process::output(
        &mut command,
        &format!("check-all stage2 {tool} identity probe"),
        MAX_VERSION_BYTES,
        Duration::from_secs(10),
    )
    .map_err(|error| {
        format!("check-all could not run stage2 {tool} {}: {error}", program.display())
    })?;
    if !output.status.success() {
        return Err(format!(
            "check-all stage2 {tool} identity probe exited {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|_| format!("check-all stage2 {tool} identity output was not valid UTF-8"))
}

fn unique_version_field(output: &str, field: &str) -> Result<String, String> {
    let prefix = format!("{field}:");
    let mut values = output.lines().filter_map(|line| line.strip_prefix(&prefix).map(str::trim));
    let value = values
        .next()
        .filter(|value| !value.is_empty())
        .ok_or_else(|| format!("stage2 identity output omitted `{field}:`"))?;
    if values.next().is_some() {
        return Err(format!("stage2 identity output repeated `{field}:`"));
    }
    Ok(value.to_string())
}

fn is_full_git_sha(value: &str) -> bool {
    value.len() == 40 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn sha256_executable(path: &Path) -> Result<String, String> {
    const MAX_TOOL_BYTES: u64 = 1024 * 1024 * 1024;
    let before = fs::symlink_metadata(path).map_err(|error| {
        format!("check-all could not stat stage2 tool {}: {error}", path.display())
    })?;
    if before.file_type().is_symlink() || !before.file_type().is_file() {
        return Err(format!(
            "check-all stage2 tool is not an exact regular file: {}",
            path.display()
        ));
    }
    if before.len() > MAX_TOOL_BYTES {
        return Err(format!(
            "check-all stage2 tool exceeds the {MAX_TOOL_BYTES}-byte identity limit: {}",
            path.display()
        ));
    }
    let mut file = fs::File::open(path).map_err(|error| {
        format!("check-all could not open stage2 tool {}: {error}", path.display())
    })?;
    let opened = file.metadata().map_err(|error| {
        format!("check-all could not inspect opened stage2 tool {}: {error}", path.display())
    })?;
    if !opened.file_type().is_file() || !same_stage2_file_identity(&before, &opened) {
        return Err(format!(
            "check-all stage2 tool changed while it was being opened: {}",
            path.display()
        ));
    }
    let expected_bytes = before.len();
    let read_limit = expected_bytes
        .checked_add(1)
        .ok_or_else(|| format!("check-all stage2 tool length overflowed: {}", path.display()))?;
    let mut hasher = Sha256::new();
    let copied = io::copy(&mut (&mut file).take(read_limit), &mut hasher).map_err(|error| {
        format!("check-all could not hash stage2 tool {}: {error}", path.display())
    })?;
    if copied != expected_bytes {
        return Err(format!(
            "check-all stage2 tool length changed while it was being hashed: {}",
            path.display()
        ));
    }
    let after = fs::symlink_metadata(path).map_err(|error| {
        format!("check-all could not restat stage2 tool {}: {error}", path.display())
    })?;
    if after.file_type().is_symlink()
        || !after.file_type().is_file()
        || !same_stage2_file_identity(&before, &after)
        || after.len() != before.len()
    {
        return Err(format!(
            "check-all stage2 tool changed while it was being hashed: {}",
            path.display()
        ));
    }
    Ok(format!("{:x}", hasher.finalize()))
}

#[cfg(unix)]
fn same_stage2_file_identity(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    use std::os::unix::fs::MetadataExt as _;

    left.dev() == right.dev() && left.ino() == right.ino()
}

#[cfg(not(unix))]
fn same_stage2_file_identity(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.is_file() && right.is_file() && left.len() == right.len()
}

fn command_in_repo<I, S>(program: String, repo_root: &Path, args: I) -> Command
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    let mut command = Command::new(program);
    command.current_dir(repo_root).args(args);
    command
}

fn run_shell_syntax_gate(repo_root: &Path) -> bool {
    let mut scripts = match fs::read_dir(repo_root.join("scripts")) {
        Ok(entries) => entries
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .filter(|path| path.extension().is_some_and(|extension| extension == "sh"))
            .collect::<Vec<_>>(),
        Err(error) => {
            eprintln!("FAIL: could not read scripts directory: {error}");
            return false;
        }
    };
    scripts.sort();

    if scripts.is_empty() {
        eprintln!("FAIL: no shell scripts found under scripts/");
        return false;
    }

    let mut command = Command::new("bash");
    command.current_dir(repo_root).arg("-n").args(scripts);
    run_gate_step("shell syntax", command)
}

fn run_targo_gate<I, S>(repo_root: &Path, targo: &Path, args: I) -> bool
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    let mut command = targo_gate_command(repo_root, targo, false);
    command.args(args);
    run_gate_step("targo", command)
}

fn targo_gate_command(repo_root: &Path, targo: &Path, offline: bool) -> Command {
    let mut command = Command::new(targo);
    command.current_dir(repo_root).env("CARGO_SKIP_CACHE", "1").arg("--unverified");
    if offline {
        command.env("CARGO_NET_OFFLINE", "true");
    }
    command
}

fn run_temporal_fixture_boundary_gate(repo_root: &Path, targo: &Path) -> bool {
    let mut command = targo_gate_command(repo_root, targo, true);
    command.args(["trust", "temporal", "targo-trust/tests/fixtures/fabric"]);
    match bounded_script_output(&mut command, "temporal fixture boundary") {
        Ok(output) => {
            emit_script_output(&output);
            match validate_temporal_fixture_boundary_output(&output) {
                Ok(()) => {
                    println!("PASS: temporal fixture fails closed with unbound evidence");
                    true
                }
                Err(error) => {
                    eprintln!("FAIL: temporal fixture boundary: {error}");
                    false
                }
            }
        }
        Err(error) => {
            eprintln!("FAIL: temporal fixture boundary could not start: {error}");
            false
        }
    }
}

fn validate_temporal_fixture_boundary_output(output: &Output) -> Result<(), String> {
    validate_temporal_fixture_boundary_parts(output.status.code(), &output.stderr)
        .map_err(|error| format!("{error}; observed status {}", output.status))
}

fn validate_temporal_fixture_boundary_parts(
    status_code: Option<i32>,
    stderr_bytes: &[u8],
) -> Result<(), String> {
    if status_code != Some(2) {
        return Err(format!("expected exit code 2, observed {status_code:?}"));
    }
    let stderr =
        std::str::from_utf8(stderr_bytes).map_err(|_| "stderr was not valid UTF-8".to_string())?;
    let expected =
        format!("targo trust temporal: {}", crate::temporal_cli::UNBOUND_TEMPORAL_EVIDENCE);
    let matches = stderr.lines().filter(|line| *line == expected).count();
    if matches != 1 {
        return Err(format!(
            "expected exactly one primary unbound-evidence diagnostic, observed {matches}"
        ));
    }
    if stderr.contains("repository-owned ty selected")
        || stderr.contains("canonical ty identity rejected")
    {
        return Err("automatic rejection unexpectedly depended on ty discovery".to_string());
    }
    Ok(())
}

fn run_gate_step(label: &str, mut command: Command) -> bool {
    match bounded_script_output(&mut command, label) {
        Ok(output) if output.status.success() => {
            emit_script_output(&output);
            println!("PASS: {label}");
            true
        }
        Ok(output) => {
            emit_script_output(&output);
            eprintln!("FAIL: {label} exited with {}", output.status);
            false
        }
        Err(error) => {
            eprintln!("FAIL: {label} could not start: {error}");
            false
        }
    }
}

fn require_file(path: &Path, label: &str) -> bool {
    if path.is_file() {
        true
    } else {
        eprintln!("FAIL: {label}: {}", path.display());
        false
    }
}

fn run_leaf_command(group: &str, args: &[String], specs: &[ScriptSpec], usage: &str) -> ExitCode {
    debug_assert!(specs.iter().all(|spec| !spec.summary.is_empty()));

    let Some(command) = args.first().map(String::as_str) else {
        eprint!("{usage}");
        return ExitCode::from(2);
    };

    if is_help_arg(command) {
        print!("{usage}");
        return ExitCode::SUCCESS;
    }

    if let Some(spec) = specs.iter().find(|spec| spec.matches(command)) {
        let script_args = spec
            .fixed_args
            .iter()
            .map(|arg| (*arg).to_string())
            .chain(args[1..].iter().cloned())
            .collect::<Vec<_>>();
        return run_maintenance_script(
            &format!("targo trust {group} {}", spec.canonical_name()),
            spec.script,
            spec.runner,
            &script_args,
        );
    }

    eprintln!("targo trust {group}: unknown command `{command}`");
    eprint!("{usage}");
    ExitCode::from(2)
}

fn run_maintenance_leaf_command(
    group: &str,
    args: &[String],
    specs: &[MaintenanceSpec],
    usage: &str,
) -> ExitCode {
    debug_assert!(specs.iter().all(|spec| !spec.summary.is_empty()));

    let Some(command) = args.first().map(String::as_str) else {
        eprint!("{usage}");
        return ExitCode::from(2);
    };

    if is_help_arg(command) {
        print!("{usage}");
        return ExitCode::SUCCESS;
    }

    if let Some(spec) = specs.iter().find(|spec| spec.matches(command)) {
        return run_maintenance_script(
            &format!("targo trust {group} {}", spec.canonical_name()),
            spec.script,
            spec.runner,
            &args[1..],
        );
    }

    eprintln!("targo trust {group}: unknown command `{command}`");
    eprint!("{usage}");
    ExitCode::from(2)
}

fn run_maintenance_script(
    label: &str,
    script: &str,
    runner: MaintenanceRunner,
    args: &[String],
) -> ExitCode {
    let (repo_root, script_path) = match resolve_repo_file(script) {
        Some(resolved) => resolved,
        None => {
            eprintln!("targo trust: {label} requires `{script}`, but it was not found");
            eprintln!("  Run from a Trust checkout or set TRUST_REPO_ROOT=/path/to/Trust.");
            return ExitCode::from(2);
        }
    };

    let mut command = match runner {
        MaintenanceRunner::Python => {
            warn_deprecated_python_adapter(label);
            let mut command = Command::new(python_command());
            command.arg(script_path);
            command
        }
        MaintenanceRunner::Shell => {
            let mut command = Command::new(TRUSTED_BASH);
            command.arg(script_path);
            command
        }
    };
    if script == CERTIFIED_MONITOR_RELEASE_SCRIPT {
        configure_certified_monitor_release_environment(&mut command);
        let initial_head = match certified_monitor_source_authority(&repo_root, "before") {
            Ok(head) => head,
            Err(error) => {
                eprintln!("targo trust: {label} source authority failed before execution: {error}");
                return ExitCode::from(2);
            }
        };
        command
            .env(CERTIFIED_MONITOR_EXPECTED_HEAD_ENV, &initial_head)
            .current_dir(&repo_root)
            .args(args);
        let result = run_child(label, command);
        let terminal_head = match certified_monitor_source_authority(&repo_root, "after") {
            Ok(head) => head,
            Err(error) => {
                eprintln!("targo trust: {label} source authority failed after execution: {error}");
                return ExitCode::FAILURE;
            }
        };
        if terminal_head != initial_head {
            eprintln!(
                "targo trust: {label} repository HEAD changed during execution: \
                 {initial_head} -> {terminal_head}"
            );
            return ExitCode::FAILURE;
        }
        if result == ExitCode::SUCCESS {
            println!(
                "certified-monitor release gate: PASS (native controlled-Git source authority \
                 verified before and after at {initial_head})"
            );
        }
        return result;
    }
    command.current_dir(repo_root).args(args);
    run_child(label, command)
}

/// Bind the certified-monitor shell payload to the real worktree, HEAD object,
/// tracked bytes, index authority, untracked inventory, and recursive submodule
/// graph through the same fixed-system-Git implementation used by native
/// evidence producers.  The shell's own Git probes remain diagnostics only;
/// they cannot nominate the worktree or commit accepted by this boundary.
fn certified_monitor_source_authority(repo_root: &Path, phase: &str) -> Result<String, String> {
    const MAX_STATUS_BYTES: usize = 8 * 1024 * 1024;
    let requested = fs::canonicalize(repo_root).map_err(|error| {
        format!("could not canonicalize certified-monitor repository root: {error}")
    })?;
    let controlled = crate::controlled_git::resolve_repo_root(&requested)?;
    if controlled != requested {
        return Err(format!(
            "certified-monitor repository root mismatch: requested {}, controlled Git resolved {}",
            requested.display(),
            controlled.display()
        ));
    }
    let status = crate::controlled_git::exact_status_porcelain_v1(
        &controlled,
        &format!("certified-monitor {phase} source-authority probe"),
        MAX_STATUS_BYTES,
        Duration::from_secs(30),
    )?;
    if !status.is_empty() {
        let preview = status.iter().take(20).cloned().collect::<Vec<_>>().join("\n");
        return Err(format!(
            "certified-monitor requires a content-authoritatively clean recursive checkout {phase} execution:\n{preview}"
        ));
    }
    crate::controlled_git::canonical_head(
        &controlled,
        &format!("certified-monitor {phase} HEAD probe"),
        64 * 1024,
        Duration::from_secs(30),
    )
}

/// Keep the release monitor gate independent of caller PATH/tool shadows and
/// of compiler/wrapper/loader authority inherited from an interactive shell.
/// The gate receives one read-only cache seed location, then constructs fresh
/// private HOME/CARGO_HOME/TMPDIR state without copying user configuration or
/// unpacked/compiled artifacts.
fn configure_certified_monitor_release_environment(command: &mut Command) {
    const PRESERVED: &[&str] = &[
        "TRUST_STAGE2_SYSROOT",
        "TRUST_CERTIFIED_MONITOR_E2E_RUN_ID",
        "TRUST_CERTIFIED_MONITOR_E2E_LOG_DIR",
        "TRUST_CERTIFIED_MONITOR_E2E_TARGET_DIR",
    ];
    // Preserve the documented explicit seed verbatim; CARGO_HOME/HOME are
    // accepted only as discovery fallbacks and are never inherited under
    // their authority-bearing names after env_clear.
    let cache_home = env::var_os(CERTIFIED_MONITOR_CACHE_HOME_ENV)
        .or_else(|| env::var_os("CARGO_HOME"))
        .or_else(|| {
            env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo").into_os_string())
        });
    let preserved = PRESERVED
        .iter()
        .filter_map(|name| env::var_os(name).map(|value| (*name, value)))
        .collect::<Vec<_>>();

    command.env_clear();
    command
        .env("PATH", CERTIFIED_MONITOR_RELEASE_PATH)
        .env("LC_ALL", "C")
        .env("LANG", "C")
        .env("TZ", "UTC")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1");
    if let Some(cache_home) = cache_home {
        command.env(CERTIFIED_MONITOR_CACHE_HOME_ENV, cache_home);
    }
    for (name, value) in preserved {
        command.env(name, value);
    }
}

fn warn_deprecated_python_adapter(label: &str) {
    eprintln!(
        "targo trust: {label} uses a deprecated Python-backed adapter; prefer Rust-native targo trust gates for full/default evidence"
    );
}

fn run_child(label: &str, mut command: Command) -> ExitCode {
    match bounded_script_output(&mut command, label) {
        Ok(output) => {
            emit_script_output(&output);
            match output.status.code() {
                Some(code) if (0..=255).contains(&code) => ExitCode::from(code as u8),
                Some(code) => {
                    eprintln!("targo trust: {label} exited with unsupported status {code}");
                    ExitCode::FAILURE
                }
                None => {
                    eprintln!("targo trust: {label} terminated by signal");
                    ExitCode::FAILURE
                }
            }
        }
        Err(error) => {
            eprintln!("targo trust: failed to run {label}: {error}");
            ExitCode::from(2)
        }
    }
}

fn bounded_script_output(
    command: &mut Command,
    label: &str,
) -> Result<std::process::Output, String> {
    bounded_process::output(command, label, SCRIPT_MAX_STREAM_BYTES, SCRIPT_TIMEOUT)
}

fn emit_script_output(output: &std::process::Output) {
    if !output.stdout.is_empty() {
        print!("{}", String::from_utf8_lossy(&output.stdout));
    }
    if !output.stderr.is_empty() {
        eprint!("{}", String::from_utf8_lossy(&output.stderr));
    }
}

fn run_trust_cli_subcommand(group: &str, subcommand: &str, args: &[String]) -> ExitCode {
    let current_exe = match env::current_exe() {
        Ok(path) => path,
        Err(error) => {
            eprintln!("targo trust {group}: failed to resolve current executable: {error}");
            return ExitCode::from(2);
        }
    };
    let mut command = Command::new(current_exe);
    command.arg("trust").arg(subcommand).args(args);
    run_child(&format!("targo trust {group}"), command)
}

pub(crate) fn python_command() -> String {
    ["TRUST_SCRIPT_PYTHON", "FULL_VERIFY_PYTHON", "PYTHON3"]
        .into_iter()
        .filter_map(|key| env::var(key).ok())
        .find(|value| !value.is_empty())
        .unwrap_or_else(|| "python3".to_string())
}

pub(crate) fn resolve_repo_file(relative: &str) -> Option<(PathBuf, PathBuf)> {
    candidate_roots().into_iter().find_map(|root| {
        let candidate = root.join(relative);
        candidate.is_file().then_some((root, candidate))
    })
}

fn candidate_roots() -> Vec<PathBuf> {
    let mut roots = Vec::new();

    if let Ok(root) = env::var("TRUST_REPO_ROOT") {
        push_unique_root(&mut roots, PathBuf::from(root));
    }

    if let Ok(cwd) = env::current_dir() {
        for ancestor in cwd.ancestors() {
            push_unique_root(&mut roots, ancestor.to_path_buf());
        }
    }

    if let Some(root) = Path::new(env!("CARGO_MANIFEST_DIR")).parent() {
        push_unique_root(&mut roots, root.to_path_buf());
    }

    roots
}

fn push_unique_root(roots: &mut Vec<PathBuf>, root: PathBuf) {
    if !roots.iter().any(|existing| existing == &root) {
        roots.push(root);
    }
}

fn is_help_arg(value: &str) -> bool {
    matches!(value, "help" | "--help" | "-h")
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::ffi::OsStr;

    use super::*;

    #[test]
    fn temporal_fixture_seed_is_online_and_boundary_is_offline() {
        let repo_root = Path::new("/repo");
        let targo = Path::new("/bin/targo");
        let online = targo_gate_command(repo_root, targo, false);
        let offline = targo_gate_command(repo_root, targo, true);
        let cargo_offline = OsStr::new("CARGO_NET_OFFLINE");

        assert!(
            online.get_envs().all(|(name, _)| name != cargo_offline),
            "the graph-seeding fetch must not force Cargo into offline mode"
        );
        assert!(
            offline.get_envs().any(|(name, value)| {
                name == cargo_offline && value == Some(OsStr::new("true"))
            })
        );
    }

    #[test]
    fn temporal_fixture_boundary_requires_the_primary_deterministic_rejection() {
        let expected = format!(
            "prefix diagnostic\ntargo trust temporal: {}\n",
            crate::temporal_cli::UNBOUND_TEMPORAL_EVIDENCE
        );
        assert!(validate_temporal_fixture_boundary_parts(Some(2), expected.as_bytes()).is_ok());

        assert!(
            validate_temporal_fixture_boundary_parts(Some(1), expected.as_bytes()).is_err(),
            "an arbitrary failing exit code is not the documented boundary"
        );
        assert!(
            validate_temporal_fixture_boundary_parts(
                Some(2),
                b"error[E0277]: RepositoryCleanKernelUniverse is not satisfied\n",
            )
            .is_err(),
            "the intentional split-universe compile failure is not itself proof of the public boundary"
        );
        let tool_dependent = format!(
            "targo trust temporal: repository-owned ty selected but not executed\n\
             targo trust temporal: {}\n",
            crate::temporal_cli::UNBOUND_TEMPORAL_EVIDENCE
        );
        assert!(
            validate_temporal_fixture_boundary_parts(Some(2), tool_dependent.as_bytes()).is_err(),
            "the unconditional rejection must not depend on a built ty artifact"
        );
    }

    #[test]
    fn survey_script_uses_the_public_non_aborting_policy() {
        let script = include_str!("../../scripts/trust_survey.sh");

        assert!(script.contains("trust check -p \"$CRATE\" --format json --survey"));
        assert!(!script.contains("export TRUST_VERIFY_SURVEY="));
        assert!(!script.contains("TRUST_SKIP_FUNCTIONS patterns"));
        assert!(script.contains("--skip has been removed"));
        assert!(!script.contains("--allow-l0-gaps"));
        assert!(!script.contains("--cfg trust_verify"));
    }

    fn assert_unique_aliases(group: &str, specs: &[ScriptSpec]) {
        let mut seen = HashSet::new();
        for spec in specs {
            for name in spec.names {
                assert!(seen.insert(*name), "{group} repeats command alias `{name}`");
            }
        }
    }

    fn assert_unique_maintenance_aliases(group: &str, specs: &[MaintenanceSpec]) {
        let mut seen = HashSet::new();
        for spec in specs {
            for name in spec.names {
                assert!(seen.insert(*name), "{group} repeats command alias `{name}`");
            }
        }
    }

    #[test]
    fn usages_document_unified_trust_surface() {
        assert!(!VERIFY_USAGE.contains("Removed commands:"));
        assert!(VERIFY_USAGE.contains("Removed verify aliases reject when invoked"));
        assert!(VERIFY_USAGE.contains("targo trust verify cargo-cache"));
        assert!(VERIFY_USAGE.contains("targo trust verify repo-gate --quick"));
        assert!(VERIFY_USAGE.contains("verify self --full-verifier"));
        assert!(VERIFY_USAGE.contains("release check"));
        assert!(
            !VERIFY_USAGE.contains("targo trust verify full-preflight"),
            "removed full-preflight must not be advertised as a normal verify example"
        );
        assert!(DEPS_USAGE.contains("targo trust deps validate"));
        assert!(DEPS_USAGE.contains("targo trust deps validate --production"));
        assert!(DEPS_USAGE.contains("--json-output"));
        assert!(!DEPS_USAGE.contains("targo trust deps matrix"));
        assert!(!DEPS_USAGE.contains("  matrix"));
        assert!(!DEPS_USAGE.contains("  report"));
        assert!(!DEPS_USAGE.contains("  verify"));
        assert!(!DEPS_USAGE.contains("  alignment"));
        assert!(!DEPS_USAGE.contains("targo trust deps report"));
        assert!(!DEPS_USAGE.contains("targo trust deps verify"));
        assert!(!DEPS_USAGE.contains("targo trust deps alignment"));
        assert!(DEPS_USAGE.contains("upstream-test-inventory"));
        assert!(
            !DEPS_USAGE.lines().any(|line| line.trim_start().starts_with("inventory ")),
            "removed deps inventory alias must not be advertised"
        );
        assert!(DEPS_USAGE.contains("targo trust deps status --dependency ty --json"));
        assert!(DEPS_USAGE.contains("targo trust deps status --json"));
        assert!(DEPS_USAGE.contains("targo trust deps status --fetch --gate snapshot-integrity"));
        assert!(DEPS_USAGE.contains("targo trust deps validate --source git-index --json"));
        assert!(RELEASE_VALIDATE_USAGE.contains("targo trust release validate"));
        assert!(RELEASE_VALIDATE_USAGE.contains("seed-freshness"));
        assert!(RELEASE_VALIDATE_USAGE.contains("certified-monitors"));
        assert!(
            RELEASE_VALIDATE_USAGE
                .lines()
                .any(|line| line.trim_start().starts_with("ledger-expirations ")),
            "release validation usage must advertise the canonical ledger gate"
        );
        assert!(
            !RELEASE_VALIDATE_USAGE.lines().any(|line| line.trim_start().starts_with("ledger ")),
            "removed release validate ledger alias must not be advertised"
        );
        assert!(GATE_USAGE.contains("targo trust gate check-all"));
        assert!(GATE_USAGE.contains("targo trust gate verify-examples"));
        assert!(REPO_USAGE.contains("targo trust repo check"));
        assert!(REPO_USAGE.contains("targo trust repo verify-examples --trustc"));
        assert!(REPO_USAGE.contains("targo trust repo submodule-reachability --json"));
        assert!(BOOTSTRAP_USAGE.contains("targo trust bootstrap recreate --check"));
        assert!(BOOTSTRAP_USAGE.contains("Trust stage0 maintenance scripts"));
        assert!(BOOTSTRAP_USAGE.contains("do not configure the targo frontend"));
        assert!(!BOOTSTRAP_USAGE.contains("cargo.rs"));
    }

    #[test]
    fn script_specs_do_not_duplicate_command_aliases() {
        assert_unique_aliases("verify", VERIFY_SPECS);
        assert_unique_aliases("deps", DEPS_SPECS);
        assert_unique_aliases("release validate", RELEASE_VALIDATE_SPECS);
        assert_unique_maintenance_aliases("repo", REPO_SPECS);
        assert_unique_maintenance_aliases("bootstrap", BOOTSTRAP_SPECS);
    }

    #[test]
    fn release_seed_freshness_always_requires_materialized_payloads() {
        let spec = RELEASE_VALIDATE_SPECS
            .iter()
            .find(|spec| spec.matches("seed-freshness"))
            .expect("release seed-freshness command");
        assert_eq!(spec.fixed_args, &["--require-payloads"]);
    }

    #[test]
    fn release_certified_monitors_uses_fail_closed_shell_gate() {
        let spec = RELEASE_VALIDATE_SPECS
            .iter()
            .find(|spec| spec.matches("certified-monitors"))
            .expect("release certified-monitors command");
        assert_eq!(spec.script, CERTIFIED_MONITOR_RELEASE_SCRIPT);
        assert_eq!(spec.runner, MaintenanceRunner::Shell);
        assert!(spec.fixed_args.is_empty());

        let script = std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .expect("repository root")
                .join(spec.script),
        )
        .expect("read certified-monitor release gate");
        for test in [
            "tests::real_targo_test_instruments_library_used_by_integration_test",
            "tests::real_targo_test_executes_authorized_satisfying_integration_test",
            "tests::real_targo_test_rejects_unharnessed_test_target_before_execution",
        ] {
            assert!(script.contains(test), "release gate omits {test}");
        }
        assert!(script.contains("--exact --ignored"));
        assert!(script.contains("RELEASE_TEST_PREFIX=\"tests::real_targo_test_\""));
        assert!(script.contains("does not match the exact reviewed set"));
        assert!(
            !script.contains("mapfile"),
            "macOS /bin/bash 3.2 has no mapfile; release inventory must remain portable"
        );
        assert!(script.contains("SHA256_TOOL=/usr/bin/shasum"));
        assert!(script.contains("SHA256_TOOL=/usr/bin/sha256sum"));
        assert!(
            !script.contains("| sha256sum"),
            "macOS release evidence must not depend on a non-system GNU sha256sum"
        );
        assert!(script.contains("while IFS= read -r inventory_name"));
        assert!(script.contains("/usr/bin/env -i"));
        assert!(script.contains("export PATH=/usr/bin:/bin"));
        assert!(script.contains("cd / || exit 1"));
        assert!(script.contains("neither a checkout-local ignored config nor a user"));
        assert!(script.contains("umask 077"));
        assert!(script.contains("--untracked-files=all"));
        assert!(script.contains("create_fresh_private_directory"));
        assert!(script.contains("seed_private_cargo_home"));
        assert!(script.contains("CARGO_HOME=$PRIVATE_CARGO_HOME"));
        assert!(script.contains("cp --reflink=auto"));
        assert!(script.contains("private registry archive $archive"));
        assert!(script.contains("cp -a -- \"$source_index/.\""));
        assert!(script.contains("require_plain_tree"));
        assert!(script.contains("admits only checksummed registry archives"));
        assert!(!script.contains("ln -s -- \"$source_git_db\""));
        assert!(script.contains("registry/src, git/checkouts"));
        assert!(script.contains("cleanup_private_target"));
        assert!(script.contains("FINAL_TRUSTC_SHA256"));
        assert!(script.contains("FINAL_TARGO_SHA256"));
        assert!(script.contains("FINAL_TARGO_TRUST_SHA256"));
        assert!(script.contains("hash_stable_stage2_tree"));
        assert!(script.contains("STAGE2_TREE_SHA256"));
        assert!(script.contains("FINAL_STAGE2_TREE_SHA256"));
        assert!(script.contains("TERMINAL_STAGE2_TREE_SHA256"));
        assert!(script.contains("stage2 rust-src link escapes the exact checkout"));
        assert!(script.contains("gate-identity.txt"));
        assert!(script.contains("evidence.sha256"));
        assert!(script.contains("EVIDENCE_MANIFEST_SHA256"));
        assert!(script.contains("result_scope=payload-only"));
        assert!(script.contains("source_authority=unverified"));
        assert!(script.contains("native controlled-Git postcheck required for release PASS"));
        assert!(!script.contains("certified-monitor E2E: PASS"));
        assert!(script.contains("hash_stable_regular_file \"$evidence_file\""));
        assert!(script.contains("chmod 400 \"$evidence_file\""));
        assert!(script.contains("chmod 500 \"$LOG_DIR\""));
        assert!(script.contains("FINAL_MANIFEST_SHA256"));
        assert!(script.contains("FINAL_LOCK_SHA256"));
        assert!(script.contains("TERMINAL_TRUSTC_SHA256"));
        assert!(script.contains("TERMINAL_TARGO_SHA256"));
        assert!(script.contains("TERMINAL_TARGO_TRUST_SHA256"));
        assert!(script.contains("\"$TARGO\" -Vv"));
        assert!(script.contains("\"$TARGO_TRUST\" --version"));
        assert!(script.contains("TARGO_COMMIT=\"$(trust_repo_commit_from_version"));
        assert!(script.contains("TARGO_TRUST_COMMIT=\"$(trust_repo_commit_from_version"));
        assert!(script.contains("stale stage2 Targo reports Trust repo commit"));
        assert!(script.contains("stale stage2 targo-trust reports Trust repo commit"));
        assert!(
            !script.contains("mkdir -p \"$LOG_DIR\" \"$TARGET_DIR\""),
            "release evidence directories must never reuse caller-created state"
        );
        assert!(
            !script.contains("RUSTC=\"$TRUSTC\""),
            "outer compiler override would poison each nested evidence-grade Targo invocation"
        );

        #[cfg(unix)]
        assert_eq!(TRUSTED_BASH, "/bin/bash");
        let mut command = Command::new(TRUSTED_BASH);
        configure_certified_monitor_release_environment(&mut command);
        let environment = command
            .get_envs()
            .map(|(name, value)| {
                (
                    name.to_string_lossy().into_owned(),
                    value.map(|value| value.to_string_lossy().into_owned()),
                )
            })
            .collect::<std::collections::BTreeMap<_, _>>();
        assert_eq!(
            environment.get("PATH").and_then(Option::as_deref),
            Some(CERTIFIED_MONITOR_RELEASE_PATH)
        );
        assert_eq!(environment.get("LC_ALL").and_then(Option::as_deref), Some("C"));
        assert_eq!(environment.get("LANG").and_then(Option::as_deref), Some("C"));
        assert_eq!(environment.get("TZ").and_then(Option::as_deref), Some("UTC"));
        assert_eq!(
            environment.get("GIT_CONFIG_GLOBAL").and_then(Option::as_deref),
            Some("/dev/null")
        );
        assert_eq!(environment.get("GIT_CONFIG_NOSYSTEM").and_then(Option::as_deref), Some("1"));
        assert!(environment.contains_key(CERTIFIED_MONITOR_CACHE_HOME_ENV));
        for forbidden in [
            "HOME",
            "CARGO_HOME",
            "TMPDIR",
            "CARGO",
            "RUSTC",
            "CARGO_BUILD_RUSTC",
            "RUSTC_WRAPPER",
            "RUSTC_WORKSPACE_WRAPPER",
            "CARGO_ENCODED_RUSTFLAGS",
            "RUSTFLAGS",
            "LD_PRELOAD",
            "BASH_ENV",
        ] {
            assert!(
                !environment.contains_key(forbidden),
                "release command retained authority environment {forbidden}"
            );
        }
    }

    /// Every maintenance leaf carries exactly one spelling, and an unrecognized
    /// one exits 2 rather than silently resolving to a neighbouring script.
    #[test]
    fn maintenance_leaves_have_one_canonical_spelling() {
        assert!(
            RELEASE_VALIDATE_SPECS.iter().any(|spec| spec.matches("ledger-expirations")),
            "canonical release validate ledger-expirations command must remain live"
        );
        assert_eq!(
            run_release_validate_subcommand(&["ledger".to_string()]),
            ExitCode::from(2),
            "an unrecognized release validate leaf must fail closed"
        );

        assert!(
            DEPS_SPECS.iter().any(|spec| spec.matches("upstream-test-inventory")),
            "canonical deps upstream-test-inventory command must remain live"
        );
        assert_eq!(
            run_deps_subcommand(&["inventory".to_string()]),
            ExitCode::from(2),
            "an unrecognized deps leaf must fail closed"
        );
    }

    #[test]
    fn check_all_discovers_repo_local_stage2_targo() {
        let root = temp_test_dir("check-all-stage2-targo");
        let targo = root.join("build/host/stage2/bin/targo");
        fs::create_dir_all(targo.parent().expect("targo parent")).expect("create stage2 bin");
        write_executable(&targo);

        assert_eq!(
            resolve_stage2_targo(&root, None).expect("resolve stage2 targo"),
            fs::canonicalize(&targo).expect("canonical stage2 targo")
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn check_all_rejects_ambiguous_stage2_targo_discovery() {
        let root = temp_test_dir("check-all-ambiguous-stage2-targo");
        for target in ["alpha", "beta"] {
            let targo = root.join("build").join(target).join("stage2/bin/targo");
            fs::create_dir_all(targo.parent().expect("targo parent")).expect("create stage2 bin");
            write_executable(&targo);
        }

        let error = resolve_stage2_targo(&root, None)
            .expect_err("implicit discovery must reject multiple non-preferred stage2 toolchains");
        assert!(error.contains("multiple `targo` executables"), "{error}");

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn check_all_rejects_legacy_cargo_as_targo_evidence() {
        let root = temp_test_dir("check-all-rejects-cargo");
        fs::create_dir_all(&root).expect("create temp root");

        let error = resolve_stage2_targo(&root, Some((Path::new("cargo"), "--cargo")))
            .expect_err("plain cargo must not satisfy Trust targo evidence");
        assert!(error.contains("canonical `targo`"), "{error}");

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn check_all_rejects_external_targo_as_golden_path_evidence() {
        let root = temp_test_dir("check-all-external-targo-root");
        let external = temp_test_dir("check-all-external-targo").join("targo");
        fs::create_dir_all(&root).expect("create temp root");
        fs::create_dir_all(external.parent().expect("external parent"))
            .expect("create external parent");
        write_executable(&external);

        let error = resolve_stage2_targo(&root, Some((&external, "--targo")))
            .expect_err("external targo must not satisfy Trust targo evidence");
        assert!(error.contains("repo-local stage2 targo"), "{error}");

        let _ = fs::remove_dir_all(root);
        let _ = fs::remove_dir_all(external.parent().expect("external parent"));
    }

    #[test]
    fn check_all_rejects_nested_stage2_targo_lookalike() {
        let root = temp_test_dir("check-all-nested-stage2-targo");
        let nested = root.join("build/host/stage2/bin/nested/targo");
        fs::create_dir_all(nested.parent().expect("nested parent"))
            .expect("create nested stage2 bin");
        write_executable(&nested);

        let error = resolve_stage2_targo(&root, Some((&nested, "--targo")))
            .expect_err("nested path must not satisfy exact stage2 tool identity");
        assert!(error.contains("build/*/stage2/bin/targo"), "{error}");

        let _ = fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn check_all_rejects_symlinked_stage2_targo() {
        use std::os::unix::fs::symlink;

        let root = temp_test_dir("check-all-symlink-stage2-targo");
        let external = temp_test_dir("check-all-symlink-stage2-target").join("targo");
        let targo = root.join("build/host/stage2/bin/targo");
        fs::create_dir_all(targo.parent().expect("targo parent")).expect("create stage2 bin");
        fs::create_dir_all(external.parent().expect("external parent"))
            .expect("create external parent");
        write_executable(&external);
        symlink(&external, &targo).expect("create stage2 targo symlink");

        let error = resolve_stage2_targo(&root, Some((&targo, "--targo")))
            .expect_err("symlink must not satisfy stage2 tool identity");
        assert!(error.contains("must not use symlinks"), "{error}");

        let _ = fs::remove_dir_all(root);
        let _ = fs::remove_dir_all(external.parent().expect("external parent"));
    }

    #[cfg(unix)]
    #[test]
    fn check_all_rejects_symlinked_stage2_directory() {
        use std::os::unix::fs::symlink;

        let root = temp_test_dir("check-all-symlink-stage2-dir");
        let external = temp_test_dir("check-all-symlink-stage2-dir-target");
        let host = root.join("build/host");
        let external_targo = external.join("stage2/bin/targo");
        fs::create_dir_all(host.parent().expect("host parent")).expect("create build dir");
        fs::create_dir_all(external_targo.parent().expect("external targo parent"))
            .expect("create external stage2 bin");
        write_executable(&external_targo);
        symlink(&external, &host).expect("create host directory symlink");
        let targo = host.join("stage2/bin/targo");

        let error = resolve_stage2_targo(&root, Some((&targo, "--targo")))
            .expect_err("symlinked directory must not satisfy stage2 tool identity");
        assert!(error.contains("must not use symlinks"), "{error}");

        let _ = fs::remove_dir_all(root);
        let _ = fs::remove_dir_all(external);
    }

    #[cfg(unix)]
    #[test]
    fn check_all_resolves_bootstrap_host_alias_to_exact_internal_stage2_targo() {
        use std::os::unix::fs::symlink;

        let root = temp_test_dir("check-all-bootstrap-host-alias");
        let actual_host = root.join("build/test-host");
        let actual_targo = actual_host.join("stage2/bin/targo");
        fs::create_dir_all(actual_targo.parent().expect("actual targo parent"))
            .expect("create actual stage2 bin");
        write_executable(&actual_targo);
        symlink(&actual_host, root.join("build/host")).expect("create bootstrap host alias");

        assert_eq!(
            resolve_stage2_targo(
                &root,
                Some((Path::new("build/host/stage2/bin/targo"), "--targo")),
            )
            .expect("bootstrap host alias resolves to exact tool"),
            fs::canonicalize(&actual_targo).expect("canonical actual targo")
        );

        let _ = fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn check_all_rejects_non_executable_stage2_targo() {
        let root = temp_test_dir("check-all-non-executable-targo");
        let targo = root.join("build/host/stage2/bin/targo");
        fs::create_dir_all(targo.parent().expect("targo parent")).expect("create stage2 bin");
        fs::write(&targo, "#!/usr/bin/env sh\nexit 0\n").expect("write non-executable targo");

        let error = resolve_stage2_targo(&root, Some((&targo, "--targo")))
            .expect_err("non-executable targo must not satisfy Trust targo evidence");
        assert!(error.contains("not an executable file"), "{error}");

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn stage2_identity_fields_are_unique_and_git_hashes_are_exact() {
        assert_eq!(
            unique_version_field("release: 1.99\nhost: test\n", "release"),
            Ok("1.99".into())
        );
        assert!(unique_version_field("release: one\nrelease: two\n", "release").is_err());
        assert!(unique_version_field("host: test\n", "release").is_err());
        assert!(is_full_git_sha("0123456789abcdef0123456789abcdef01234567"));
        assert!(!is_full_git_sha("0123456789abcdef"));
        assert!(!is_full_git_sha("g123456789abcdef0123456789abcdef01234567"));
    }

    #[cfg(unix)]
    #[test]
    fn bounded_command_output_rejects_oversized_and_nonterminating_probes() {
        let mut oversized = Command::new("sh");
        oversized.args(["-c", "printf '%70000s' x"]);
        let error = bounded_process::output(
            &mut oversized,
            "oversized fixture",
            64 * 1024,
            Duration::from_secs(2),
        )
        .expect_err("oversized output must fail closed");
        assert!(error.contains("output exceeded"), "{error}");

        let mut nonterminating = Command::new("sh");
        nonterminating.args(["-c", "while :; do :; done"]);
        let error = bounded_process::output(
            &mut nonterminating,
            "timeout fixture",
            64 * 1024,
            Duration::from_millis(50),
        )
        .expect_err("nonterminating identity probe must time out");
        assert!(error.contains("timeout"), "{error}");

        let mut background_descendant = Command::new("sh");
        background_descendant.args(["-c", "sleep 60 &"]);
        let started = Instant::now();
        let error = bounded_process::output(
            &mut background_descendant,
            "background fixture",
            64 * 1024,
            Duration::from_secs(2),
        )
        .expect_err("background descendant must fail closed without retaining probe pipes");
        assert!(error.contains("background descendant"), "{error}");
        assert!(started.elapsed() < Duration::from_secs(1), "probe cleanup was not bounded");
    }

    #[cfg(unix)]
    #[test]
    fn check_all_authenticates_stage2_bytes_and_exact_trustc_commit() {
        let root = temp_test_dir("check-all-stage2-identity");
        fs::create_dir_all(&root).expect("create repository root");
        let git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .current_dir(&root)
                .args(args)
                .status()
                .expect("run git fixture command");
            assert!(status.success(), "git fixture command failed: {args:?}");
        };
        git(&["init", "-q"]);
        fs::write(root.join("README"), "identity fixture\n").expect("write tracked fixture");
        fs::write(root.join(".gitignore"), "build/\ntarget/\n")
            .expect("write fixture ignore rules");
        git(&["add", "README", ".gitignore"]);
        git(&[
            "-c",
            "user.name=Trust Test",
            "-c",
            "user.email=trust-test@example.invalid",
            "commit",
            "-qm",
            "identity fixture",
        ]);
        let head = git_head(&root).expect("fixture HEAD");
        require_clean_git_checkout(&root).expect("fresh fixture is clean");

        let bin = root.join("build/host/stage2/bin");
        fs::create_dir_all(&bin).expect("create stage2 bin");
        let targo = bin.join("targo");
        let trustc = bin.join("trustc");
        write_executable_script(
            &targo,
            "#!/bin/sh\n[ \"${1:-}\" = \"-Vv\" ] || exit 2\nprintf 'targo 1.99.0-dev\\nrelease: 1.99.0-dev\\nhost: test-host\\n'\n",
        );
        write_executable_script(
            &trustc,
            &format!(
                "#!/bin/sh\n[ \"${{1:-}}\" = \"-vV\" ] || exit 2\nprintf 'trustc 1.99.0-dev\\ncommit-hash: {head}\\nhost: test-host\\n'\n"
            ),
        );

        let identity = validate_check_all_stage2_toolchain(&root, &targo)
            .expect("exact stage2 toolchain should authenticate");
        assert_eq!(identity.repo_head, head);
        assert_eq!(identity.trustc_commit, head);
        assert_eq!(identity.targo_release, "1.99.0-dev");
        assert_eq!(identity.targo_host, "test-host");
        assert_eq!(identity.targo_sha256.len(), 64);
        assert_eq!(identity.trustc_sha256.len(), 64);
        fs::write(root.join("untracked-change"), "dirty\n").expect("write dirty fixture");
        let dirty_error = require_clean_git_checkout(&root)
            .expect_err("untracked source must invalidate reproducible gate evidence");
        assert!(dirty_error.contains("untracked-change"), "{dirty_error}");
        fs::remove_file(root.join("untracked-change")).expect("remove dirty fixture");
        require_clean_git_checkout(&root).expect("fixture is clean after removal");

        let other_bin = root.join("build/other/stage2/bin");
        fs::create_dir_all(&other_bin).expect("create second stage2 bin");
        let other_targo = other_bin.join("targo");
        let other_trustc = other_bin.join("trustc");
        write_executable_script(
            &other_targo,
            "#!/bin/sh\nprintf 'targo 1.99.0-other\\nrelease: 1.99.0-other\\nhost: other-host\\n'\n",
        );
        write_executable_script(
            &other_trustc,
            &format!(
                "#!/bin/sh\nprintf 'trustc 1.99.0-other\\ncommit-hash: {head}\\nhost: other-host\\n'\n"
            ),
        );
        let other_identity = validate_check_all_stage2_toolchain(&root, &other_targo)
            .expect("explicit second stage2 toolchain should authenticate as one unit");
        let discovery_error = find_stage2_trustc(&root)
            .expect_err("ambient discovery must reject two concrete host toolchains");
        assert!(discovery_error.contains("multiple `trustc` executables"));
        let verify_args = stage2_verify_examples_args(&root, &other_identity.trustc_path);
        let trustc_index = verify_args
            .iter()
            .position(|arg| arg == "--trustc")
            .expect("verify args include trustc");
        assert_eq!(
            verify_args.get(trustc_index + 1),
            Some(&other_identity.trustc_path.display().to_string()),
            "check-all verification must use the authenticated selected sibling, not rediscovery"
        );

        write_executable_script(
            &trustc,
            "#!/bin/sh\nprintf 'trustc 1.99.0-dev\\ncommit-hash: 0000000000000000000000000000000000000000\\nhost: test-host\\n'\n",
        );
        let error = validate_check_all_stage2_toolchain(&root, &targo)
            .expect_err("stale sibling trustc must invalidate Targo gate evidence");
        assert!(error.contains("refuses stale stage2 trustc"), "{error}");

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn script_specs_only_dispatch_reviewed_runner_types() {
        for (group, specs) in [("verify", VERIFY_SPECS), ("deps", DEPS_SPECS)] {
            for spec in specs {
                assert!(
                    !spec.script.ends_with(".sh"),
                    "targo trust {group} {} must not dispatch a shell script",
                    spec.canonical_name()
                );
            }
        }

        for spec in RELEASE_VALIDATE_SPECS {
            match spec.runner {
                MaintenanceRunner::Python => assert!(
                    spec.script.ends_with(".py"),
                    "release gate {} has a Python runner but not a .py source",
                    spec.canonical_name()
                ),
                MaintenanceRunner::Shell => {
                    assert_eq!(
                        spec.canonical_name(),
                        "certified-monitors",
                        "only the reviewed certified-monitor release gate may dispatch shell"
                    );
                    assert_eq!(spec.script, CERTIFIED_MONITOR_RELEASE_SCRIPT);
                }
            }
        }
    }

    #[test]
    fn repo_and_bootstrap_specs_are_documented_and_explicitly_typed() {
        for spec in REPO_SPECS.iter().chain(BOOTSTRAP_SPECS.iter()) {
            assert!(!spec.summary.is_empty());
            assert!(
                REPO_USAGE.contains(spec.canonical_name())
                    || BOOTSTRAP_USAGE.contains(spec.canonical_name())
            );
            match spec.runner {
                MaintenanceRunner::Python => assert!(spec.script.ends_with(".py")),
                MaintenanceRunner::Shell => assert!(spec.script.ends_with(".sh")),
            }
        }
    }

    #[test]
    fn release_conformance_is_validate_gate_only() {
        let args = vec!["conformance".to_string()];
        assert!(try_run_release_script_subcommand(&args).is_none());
        assert!(RELEASE_VALIDATE_USAGE.contains("conformance"));
    }

    #[test]
    fn deps_gate_failure_modes_are_targeted() {
        let report = trust_deps::AlignmentReport {
            schema: "trust.deps.alignment.v1",
            root: ".".to_string(),
            lock_file: "trust-engines.lock".to_string(),
            fetch: false,
            summary: trust_deps::AlignmentSummary {
                total: 7,
                ok: 5,
                failed: 2,
                stale_lock: 1,
                snapshot_mismatch: 1,
                live_clone_misaligned: 0,
                dirty_live_clone: 0,
                metadata_mismatch: 0,
            },
            dependencies: Vec::new(),
        };

        assert!(DepsGate::Full.failed(&report));
        assert!(DepsGate::SnapshotIntegrity.failed(&report));
        assert!(DepsGate::RefreshReadiness.failed(&report));
        assert!(!DepsGate::LiveCloneAlignment.failed(&report));
        assert!(!DepsGate::None.failed(&report));
    }

    #[test]
    fn deps_gate_and_view_aliases_match_runbook_terms() {
        assert_eq!(
            DepsGate::parse("snapshot-integrity").expect("gate"),
            DepsGate::SnapshotIntegrity
        );
        assert_eq!(
            DepsGate::parse("live-clone-alignment").expect("gate"),
            DepsGate::LiveCloneAlignment
        );
        assert_eq!(DepsGate::parse("refresh-readiness").expect("gate"), DepsGate::RefreshReadiness);
        assert!(DepsGate::parse("unknown-gate").is_err());

        assert_eq!(DepsView::parse("refresh-plan").expect("view"), DepsView::RefreshPlan);
        assert_eq!(DepsView::parse("upstream-plan").expect("view"), DepsView::RefreshPlan);
        assert_eq!(DepsView::parse("diff").expect("view"), DepsView::Diff);
        assert!(DepsView::parse("unknown-view").is_err());
    }

    #[test]
    fn deps_json_report_writer_creates_parent_dirs_and_trailing_newline() {
        let root = temp_test_dir("deps-json-report");
        let report_path = PathBuf::from("reports").join("deps").join("release.json");
        let report = trust_deps::AlignmentReport {
            schema: "trust.deps.alignment.v1",
            root: ".".to_string(),
            lock_file: "trust-engines.lock".to_string(),
            fetch: false,
            summary: trust_deps::AlignmentSummary {
                total: 0,
                ok: 0,
                failed: 0,
                stale_lock: 0,
                snapshot_mismatch: 0,
                live_clone_misaligned: 0,
                dirty_live_clone: 0,
                metadata_mismatch: 0,
            },
            dependencies: Vec::new(),
        };
        let rendered = trust_deps::render_json(&report).expect("render deps report");

        write_deps_json_report(&root, &report_path, &rendered).expect("write deps report");

        let text = fs::read_to_string(root.join(&report_path)).expect("read deps report");
        assert!(text.ends_with('\n'));
        let json: serde_json::Value = serde_json::from_str(&text).expect("valid report JSON");
        assert_eq!(json["schema"], "trust.deps.alignment.v1");

        let _ = fs::remove_dir_all(root);
    }

    fn temp_test_dir(label: &str) -> PathBuf {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        std::env::temp_dir().join(format!("targo-trust-{label}-{}-{unique}", std::process::id()))
    }

    fn write_executable(path: &Path) {
        write_executable_script(path, "#!/usr/bin/env sh\nexit 0\n");
    }

    fn write_executable_script(path: &Path, script: &str) {
        fs::write(path, script).expect("write executable");
        make_executable(path);
    }

    #[cfg(unix)]
    fn make_executable(path: &Path) {
        use std::os::unix::fs::PermissionsExt;

        let mut permissions = fs::metadata(path).expect("metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions).expect("chmod executable");
    }

    #[cfg(not(unix))]
    fn make_executable(_path: &Path) {}
}
