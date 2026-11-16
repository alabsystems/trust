//! Native (Rust-owned) execution for `targo trust domination trust-added` modes.
//!
//! Ports trust-added modes out of `tests/run_trust_superset_suite.sh` into
//! structured, shell-free local diagnostics, one mode at a time. Every step
//! here is a direct process spawn of a selected repo-local/path-constrained
//! binary plus in-Rust file and Git inspection — no `bash`, no `x.py`, no
//! Python. Mutable ignored binaries and ambient child state mean these ports
//! are not canonical release authority; release dispatch fails closed.
//!
//! Modes not yet ported keep the explicit registered-but-disabled refusal in
//! `rust_vs_trust.rs`, so partial porting can never silently pass a gate it
//! did not actually run.
//!
//! Ported so far:
//! - `quick` — the fast trust crate feedback gate (`dev-test.sh --lib`
//!   equivalent + the targo-trust test suite).
//! - `trust-added-compiletest` — the tRust-added compiletest corpus: primary
//!   compiletest files present locally but absent from the audited upstream
//!   baseline revision, minus the documented (validated, unexpired) exception
//!   ledger, driven through the Rust bootstrap binary.
//! - `trustc-native` — the native verification transport gate: compiler
//!   transport + regression probes, the `targo trust` public CLI surface, and
//!   config/cache root resolution (see `trustc_native.rs`).

use std::collections::BTreeSet;
use std::env;
use std::ffi::OsString;
use std::fs::{self, OpenOptions};
use std::io::Read as _;
#[cfg(unix)]
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use anyhow::{Context, Result, bail};

use crate::bounded_process;
use crate::stage2_tools::{
    discover_unique_repo_stage2_tool, host_executable_name, revalidate_exact_executable,
    snapshot_exact_executable, validate_repo_stage2_tool,
};

mod binary_decomp_golden;
mod launch;
mod pipeline_v2;
mod prepublish;
mod public_distribution;
mod stage0_lineage;
mod standalone_toolchain;
mod trust_extra;
mod trustc_native;

/// Execution policy carried through every native gate. Canonical release
/// requests are rejected before dispatch and again in [`run`]; retaining the
/// bit prevents a direct subgate call from silently becoming a local result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct GatePolicy {
    pub(super) strict: bool,
    pub(super) release: bool,
}

/// Compiler/front-end authority inherited from a caller is never suitable for
/// even a local Trust diagnostic. The selected command rebuilds the small set
/// of variables it actually needs after this blacklist scrub. This is not an
/// isolated or allowlisted release environment; canonical release dispatch is
/// blocked before reaching it.
pub(super) const COMPILER_OVERRIDE_ENV: &[&str] = &[
    "TRUSTC",
    "TRUST_NO_VERIFY",
    "TRUST_TARGO_BIN",
    "TRUST_UPSTREAM_COMPAT_CARGO",
    "CARGO_TRUST_BIN",
    "RUSTUP_TOOLCHAIN",
    "RUSTC",
    "RUSTDOC",
    "RUSTFLAGS",
    "RUSTDOCFLAGS",
    "RUSTC_BOOTSTRAP",
    "CARGO_ENCODED_RUSTFLAGS",
    "CARGO_ENCODED_RUSTDOCFLAGS",
    "CARGO_BUILD_RUSTFLAGS",
    "CARGO_BUILD_RUSTDOCFLAGS",
    "CARGO_BUILD_TARGET",
    "CARGO_BUILD_TARGET_DIR",
    "CARGO_TARGET_DIR",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC",
    "CARGO_BUILD_RUSTDOC",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
];

const FIXED_LOADER_ENV: &[&str] = &[
    "LD_PRELOAD",
    "LD_LIBRARY_PATH",
    "DYLD_INSERT_LIBRARIES",
    "DYLD_LIBRARY_PATH",
    "DYLD_FRAMEWORK_PATH",
    "DYLD_FALLBACK_LIBRARY_PATH",
    "DYLD_FALLBACK_FRAMEWORK_PATH",
    "LIBPATH",
    "SHLIB_PATH",
    "LDR_PRELOAD",
];

const MAX_BASELINE_BYTES: u64 = 4 * 1024 * 1024;
const MAX_EXCEPTION_LEDGER_BYTES: u64 = 1024 * 1024;
const MAX_GATE_OUTPUT_BYTES_PER_STREAM: usize = 64 * 1024 * 1024;
const GATE_STEP_TIMEOUT: Duration = Duration::from_secs(2 * 60 * 60);
const MAX_GIT_OUTPUT_BYTES_PER_STREAM: usize = 64 * 1024 * 1024;
const GIT_COMMAND_TIMEOUT: Duration = Duration::from_secs(5 * 60);
#[cfg(target_os = "macos")]
const HOST_MEMORY_PROBE_MAX_STREAM_BYTES: usize = 64 * 1024;
#[cfg(target_os = "macos")]
const HOST_MEMORY_PROBE_TIMEOUT: Duration = Duration::from_secs(5);

/// Remove compiler and dynamic-loader injection channels from a child. The
/// prefix sweep covers platform-specific loader variables beyond the fixed
/// high-risk list.
pub(super) fn scrub_gate_process_environment(command: &mut Command) {
    for name in COMPILER_OVERRIDE_ENV.iter().chain(FIXED_LOADER_ENV) {
        command.env_remove(name);
    }
    for (name, _) in env::vars_os() {
        let Some(name_text) = name.to_str() else { continue };
        if name_text.starts_with("LD_")
            || name_text.starts_with("DYLD_")
            || name_text.starts_with("CARGO_TARGET_")
        {
            command.env_remove(name);
        }
    }
    // Empty wrapper/encoded-flag variables override Cargo configuration;
    // merely removing ambient environment values lets a user or repository
    // `.cargo/config.toml` reintroduce compiler wrappers or rustflags after the
    // diagnostic selected its toolchain.
    for name in [
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
        "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_ENCODED_RUSTDOCFLAGS",
    ] {
        command.env(name, "");
    }
}

/// Pin Cargo's compiler and documentation-driver selection spellings to the
/// exact siblings beside the selected repo-local `targo`. This overrides
/// `build.rustc` and `build.rustdoc` from Cargo configuration; wrapper
/// variables were already forced empty by the common scrub.
pub(super) fn pin_targo_sibling_toolchain(command: &mut Command, targo: &Path) -> Result<()> {
    let bin = targo.parent().context("selected targo has no bin directory")?;
    let canonical_bin = fs::canonicalize(bin)
        .with_context(|| format!("failed to canonicalize targo bin directory {}", bin.display()))?;
    let canonical_targo = fs::canonicalize(targo)
        .with_context(|| format!("failed to canonicalize targo {}", targo.display()))?;
    if canonical_targo.parent() != Some(canonical_bin.as_path())
        || !is_executable_file(&canonical_targo)
    {
        bail!(
            "targo escapes its selected bin directory or is not executable: {}",
            canonical_targo.display()
        );
    }

    let sibling = |tool: &str| -> Result<PathBuf> {
        let candidate = bin.join(host_executable_name(tool));
        let canonical = fs::canonicalize(&candidate).with_context(|| {
            format!("selected targo has no sibling {tool} at {}", candidate.display())
        })?;
        if canonical.parent() != Some(canonical_bin.as_path()) || !is_executable_file(&canonical) {
            bail!(
                "targo sibling {tool} escapes the selected bin directory or is not executable: {}",
                canonical.display()
            );
        }
        Ok(canonical)
    };
    let trustc = sibling("trustc")?;
    let trustdoc = sibling("trustdoc")?;
    command
        .env("RUSTC", &trustc)
        .env("CARGO_BUILD_RUSTC", &trustc)
        .env("RUSTDOC", &trustdoc)
        .env("CARGO_BUILD_RUSTDOC", &trustdoc);
    Ok(())
}

/// Read one bounded, exact regular file below a trusted root. Every relative
/// component is required to be normal and non-symlinked; the final open uses
/// `O_NOFOLLOW` where available and is checked against the inspected inode.
/// Reading through the same handle removes the metadata/read pathname race.
pub(super) fn read_bounded_exact_file_under(
    root: &Path,
    relative: &Path,
    max_bytes: u64,
) -> Result<Vec<u8>> {
    if relative.as_os_str().is_empty()
        || relative.is_absolute()
        || !relative.components().all(|component| matches!(component, Component::Normal(_)))
    {
        bail!("evidence path must be a non-empty canonical relative path: {}", relative.display());
    }

    let components = relative.components().collect::<Vec<_>>();
    let mut path = root.to_path_buf();
    for (index, component) in components.iter().enumerate() {
        path.push(component.as_os_str());
        let metadata = fs::symlink_metadata(&path)
            .with_context(|| format!("failed to inspect exact evidence file {}", path.display()))?;
        let is_last = index + 1 == components.len();
        if metadata.file_type().is_symlink()
            || (is_last && !metadata.file_type().is_file())
            || (!is_last && !metadata.file_type().is_dir())
        {
            bail!("evidence path contains a symlink or wrong file type: {}", path.display());
        }
    }

    let expected = fs::symlink_metadata(&path)
        .with_context(|| format!("failed to inspect exact evidence file {}", path.display()))?;
    if expected.len() > max_bytes {
        bail!(
            "evidence file exceeds the {max_bytes}-byte limit ({} bytes): {}",
            expected.len(),
            path.display()
        );
    }

    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    options.custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW);
    let mut file = options
        .open(&path)
        .with_context(|| format!("failed to open exact evidence file {}", path.display()))?;
    let opened = file
        .metadata()
        .with_context(|| format!("failed to inspect opened evidence file {}", path.display()))?;
    if !opened.file_type().is_file() || opened.len() != expected.len() {
        bail!("evidence file changed while it was being opened: {}", path.display());
    }
    #[cfg(unix)]
    if opened.dev() != expected.dev() || opened.ino() != expected.ino() {
        bail!("evidence file changed while it was being opened: {}", path.display());
    }

    let mut bytes = Vec::with_capacity(opened.len().try_into().unwrap_or(0));
    (&mut file)
        .take(max_bytes.saturating_add(1))
        .read_to_end(&mut bytes)
        .with_context(|| format!("failed to read exact evidence file {}", path.display()))?;
    let after = file
        .metadata()
        .with_context(|| format!("failed to re-inspect evidence file {}", path.display()))?;
    if bytes.len() as u64 > max_bytes
        || bytes.len() as u64 != opened.len()
        || after.len() != opened.len()
    {
        bail!("evidence file changed or exceeded its bound while read: {}", path.display());
    }
    #[cfg(unix)]
    if after.dev() != opened.dev() || after.ino() != opened.ino() {
        bail!("evidence file changed while it was being read: {}", path.display());
    }
    Ok(bytes)
}

/// Modes with a Rust-native implementation. Everything else remains
/// registered-but-disabled inventory in `rust_vs_trust.rs`.
pub(crate) fn is_native_mode(mode: &str) -> bool {
    matches!(
        mode,
        "quick"
            | "trust-added-compiletest"
            | "trustc-native"
            | "native-contracts-pipeline-v2"
            | "binary-decompilation-golden"
            | "launch"
            // These explicitly weaker diagnostics are useful during local
            // development, but must never satisfy the canonical release-gate
            // inventory IDs whose documented evidence is stronger.
            | "local-stage2-surface-smoke"
            | "trust-extra-smoke"
            | "public-distribution-cull-smoke"
            | "prepublish-local-surface-smoke"
            | "stage0-metadata-coherence-smoke"
    )
}

/// Execute a natively-ported mode. `strict`/`release` mirror the CLI flags;
/// the engine-facing env (`TRUST_STRICT`, `TRUST_RELEASE_GATE`) is honored the
/// same way the shell gates read it.
pub(crate) fn run(root: &Path, mode: &str, strict: bool, release: bool) -> Result<()> {
    let release = release || env_flag("TRUST_RELEASE_GATE");
    let strict = strict || release || env_flag("TRUST_STRICT");
    let policy = GatePolicy { strict, release };
    if policy.release {
        bail!(
            "canonical release mode `{mode}` is blocked before native execution: no independently authenticated, isolated child-process authority boundary exists; run without release policy only as a local diagnostic"
        );
    }
    match mode {
        "quick" => run_quick(root, policy),
        "trust-added-compiletest" => run_trust_added_compiletest(root, policy),
        "trustc-native" => trustc_native::run(root, policy),
        "native-contracts-pipeline-v2" => pipeline_v2::run(root, policy),
        "binary-decompilation-golden" => binary_decomp_golden::run(root, policy),
        "launch" => launch::run(root, policy),
        "local-stage2-surface-smoke" => standalone_toolchain::run(root, policy),
        "trust-extra-smoke" => trust_extra::run(root, policy),
        "public-distribution-cull-smoke" => public_distribution::run(root, policy),
        "prepublish-local-surface-smoke" => prepublish::run(root, policy),
        "stage0-metadata-coherence-smoke" => stage0_lineage::run(root, policy),
        other => bail!("mode `{other}` has no Rust-native implementation"),
    }
}

fn env_flag(name: &str) -> bool {
    env::var(name).is_ok_and(|value| value == "1")
}

pub(super) fn section(title: &str) {
    println!();
    println!("--- {title}");
}

// ---------------------------------------------------------------------------
// quick — fast trust crate feedback
// ---------------------------------------------------------------------------

/// `quick`: library tests for the Trust-owned crates workspace (the
/// `dev-test.sh --lib` gate) followed by the targo-trust test suite.
///
/// Even in developer mode, this diagnostic refuses an ambient/PATH driver.
/// A zero-exit executable named `targo` is not authority for the result.
fn run_quick(root: &Path, policy: GatePolicy) -> Result<()> {
    section("Fast trust crate feedback");
    let targo = resolve_gate_targo(root, true)?;
    let targo_identity =
        snapshot_exact_executable(&targo, "trust-added quick", "repo-local stage2 targo")
            .map_err(anyhow::Error::msg)?;
    println!("Targo: {}", targo.display());

    // dev-test.sh caps -j by BOTH cores and RAM (~5 GB/job): hw.ncpu on a
    // 24 GB host exhausted the VM compressor and panicked the machine.
    let jobs = memory_aware_jobs();
    let run_result = (|| -> Result<()> {
        run_step(
            &targo,
            &[
                // `targo test` now refuses to create an implicitly unverified
                // native artifact; this dev-mode crate-feedback lane is
                // explicitly the unverified native build (the verified path is
                // `targo trust test`), so authorize it like trust-extra's
                // dev_test_lib does.
                os("--unverified"),
                os("test"),
                os("--locked"),
                os("-j"),
                os(jobs.to_string()),
                os("--workspace"),
                os("--lib"),
            ],
            Some(&root.join("crates")),
            &[("CARGO_INCREMENTAL", "1"), ("CARGO_SKIP_CACHE", "1")],
            policy.strict,
        )?;

        // Unpinned: these targo-trust unit tests exercise the evidence-grade
        // compiler-override guard, which rejects a pinned ambient RUSTC (it would
        // leak from `cargo test` into the test binary). The stage2 `targo` already
        // uses the sibling trustc without the pin. See `run_step_unpinned`.
        run_step_unpinned(
            &targo,
            &[
                os("--unverified"),
                os("test"),
                os("--locked"),
                os("--manifest-path"),
                root.join("targo-trust/Cargo.toml").into_os_string(),
            ],
            None,
            &[],
            policy.strict,
        )
    })();
    let identity_result = revalidate_exact_executable(
        &targo_identity,
        "trust-added quick after-use check",
        "repo-local stage2 targo",
    )
    .map_err(anyhow::Error::msg);
    run_result?;
    identity_result
}

/// Per-job memory budget for a compiler fan-out, in bytes.
///
/// Provenance of the sample, stated first because it bounds every claim below.
/// On 2026-09-09 (seal trust-0028666c) one ISOLATED run of
/// `-p ay-arrays --all-targets` over the `ay` workspace was sampled every ~5 s
/// for 18 minutes: 176 instants, 32 distinct compiler units
/// (`scratchpad/memtrace.tsv`). It is NOT the failing command — that is
/// `--workspace --all-targets --all-features` over 69 workspace members — but
/// it is the run that reproduces the kill, and it is the only per-unit
/// measurement that exists. A full-workspace graph has many more ready units
/// than a `-p` graph, so the concurrency figures below are a LOWER bound on
/// what the failing command reaches; the per-unit sizes are the sizes of the
/// units this budget is about.
///
/// Peak resident set per unit, GiB (`rss_kb / 1024^2`; the sample's own
/// `DIAGNOSIS-DATA.txt` uses the same divisor while labelling it GB):
///
/// ```text
///   66.90  ay_arrays (lib test)   <- pathological pair, uncovered by design
///   63.10  ay_arrays (lib)        <- pathological pair, uncovered by design
///   11.90  ay_jit (test)          <- largest unit outside that pair
///    7.44  ay_frontend (test)
///    7.33  ay_frontend (lib)
///    0.60  syn, then 26 further units at or below 0.33
/// ```
///
/// The budget is 12 GiB because 11.90 GiB, rounded up to the next whole GiB,
/// is the smallest budget that COVERS every unit outside the pathological
/// pair: 30 of the 32 units fit under it, 27 of them under 0.63 GiB. That is
/// one order statistic (rank 30 of 32), described as what it is. It is not a
/// percentile: with n = 32 the sample is bimodal, and the 95th percentile
/// straddles the 11.90 -> 63.10 gap (36.6 GiB linear, 66.2 GiB nearest-rank),
/// so no percentile of this sample is a stable number. An earlier revision of
/// this comment claimed 11.90 was both the p95 and the largest non-tail unit,
/// i.e. two independent readings; that was wrong — it is one reading counted
/// twice, and the p95 half of it was false.
///
/// Why not keep 5 GiB: not because it was "the mean" (the mean of the 32 unit
/// peaks is 5.05 GiB, so it was, but that is a coincidence of this sample and
/// no argument either way). Because a budget below 11.90 GiB makes the rule's
/// own arithmetic false: `jobs * budget + reserve <= RAM` is only a bound on
/// demand if `budget` actually covers a unit, and at 5 GiB two of the five
/// non-trivial units exceed it.
///
/// This budget deliberately does NOT accommodate the 66.90 GiB pair. Doing so
/// yields one job on a 128 GiB host and turns a 40-minute check into hours.
/// See [`jobs_for_host`] for what the clamp does and — importantly — does not
/// buy on this trace.
const PER_JOB_MEMORY_BUDGET_BYTES: u64 = 12 * 1024 * 1024 * 1024;

/// Host memory the fan-out must not hand out, in bytes.
///
/// Dividing `hw.memsize` charges compiler jobs for memory the kernel already
/// holds. At the first sample of the same trace, before any unit had ramped,
/// the host reported `wired_gb=3.97` and `comp_gb=5.14` (9.11 GiB). Reserve
/// the next whole GiB above that measurement.
///
/// This is one measurement on one 128 GiB host, held flat rather than scaled.
/// On a small host it is a large fraction of RAM and therefore conservative;
/// given that this tree's only 24 GB datum is a machine panic, conservative is
/// the direction to be wrong in. Deriving the reserve from free memory at
/// start instead of a constant was considered and rejected: it makes the job
/// count depend on whatever else the operator happens to be running, so two
/// runs of the same gate on the same host would legitimately disagree about
/// how wide they ran, and neither the number nor the failure would be
/// reproducible.
const HOST_MEMORY_RESERVE_BYTES: u64 = 10 * 1024 * 1024 * 1024;

/// Memory-aware default parallelism: `min(cores, (RAM - reserve) / budget)`,
/// at least 1. See [`PER_JOB_MEMORY_BUDGET_BYTES`] for where the constants
/// come from.
pub(crate) fn memory_aware_jobs() -> usize {
    let cores = std::thread::available_parallelism().map_or(8, usize::from);
    host_memory_bytes().map_or(cores, |bytes| jobs_for_host(cores, bytes))
}

/// The arithmetic behind [`memory_aware_jobs`], split out so the rule can be
/// exercised at host sizes this machine does not have.
///
/// ```text
///   host      old min(cores, RAM/5GiB)   new min(cores, (RAM-10GiB)/12GiB)
///   128 GiB   18 (core-clamped)          9
///    48 GiB    9 (memory-clamped)        3
///    24 GiB    4 (memory-clamped)        1
/// ```
///
/// WHAT THIS CLAMP DOES NOT DO, on the only trace that exists. Measured over
/// the 176 sampled instants of that trace: the widest instant carried 20 live
/// units and totalled 16.96 GiB (a build-script burst); EVERY instant above
/// 60 GiB co-resident carried 3 to 5 live units; the co-resident maximum was
/// 89.36 GiB at 4 live units, and system free memory bottomed at 0.05 GiB
/// there. So any scalar cap of 6 or more — 9 included — binds at no pressure
/// instant in that trace. This change buys approximately zero headroom
/// against the specific `ay_arrays` SIGKILL it was written for, and the
/// residual risk is not "may recur" but "is untouched".
///
/// What it does do, and why it is still the right change:
///
///  * It bounds the WIDE fan-out class, which is a different failure with its
///    own recorded fatalities in this tree: `run_quick` above records `hw.ncpu`
///    on a 24 GB host exhausting the VM compressor and panicking the machine,
///    and `trust_extra`'s workspace step records 14 threads on a 48 GB host
///    dying to SIGKILL. The old rule answered 4 and 9 on those hosts. A `-p`
///    graph reaches 20 ready units only in its build-script burst; a 69-member
///    `--workspace --all-targets --all-features` graph reaches Cargo's `-j`
///    ceiling routinely, and 18 units that each merely reach the 7.4 GiB of
///    `ay_frontend` is 133 GiB on a 128 GiB host.
///  * `jobs * 12 GiB + 10 GiB reserve <= RAM` is a true bound on demand for
///    30 of the 32 measured units, which the old 5 GiB budget was not.
///
/// The two `ay_arrays` units are independent compilations of one crate, both
/// ready together, and 66.90 + 63.10 GiB exceeds this host at any `-j >= 2`;
/// the only provably safe static job count for that pair is 1, at which the
/// check is serial. Bounding that pair needs an admission gate that knows a
/// unit's size before it starts — which is what `trustd` already is for
/// SOLVER memory (see `apply_crate_memory_coordination` in `pipeline/run.rs`)
/// and what nothing in the tree is for a compiler unit's own footprint.
/// Cargo's job count cannot express it.
pub(crate) fn jobs_for_host(cores: usize, host_memory_bytes: u64) -> usize {
    let usable = host_memory_bytes.saturating_sub(HOST_MEMORY_RESERVE_BYTES);
    let mem_jobs = usize::try_from(usable / PER_JOB_MEMORY_BUDGET_BYTES).unwrap_or(usize::MAX);
    cores.min(mem_jobs).max(1)
}

fn host_memory_bytes() -> Option<u64> {
    #[cfg(target_os = "macos")]
    {
        let mut command = Command::new("/usr/sbin/sysctl");
        command.args(["-n", "hw.memsize"]);
        let output = bounded_process::output(
            &mut command,
            "host memory size probe",
            HOST_MEMORY_PROBE_MAX_STREAM_BYTES,
            HOST_MEMORY_PROBE_TIMEOUT,
        )
        .ok()?;
        if !output.status.success() {
            return None;
        }
        let stdout = String::from_utf8(output.stdout).ok()?;
        let value = stdout.strip_suffix('\n').unwrap_or(&stdout);
        let value = value.strip_suffix('\r').unwrap_or(value);
        if value.is_empty() || value.contains('\n') || value.contains('\r') {
            return None;
        }
        value.parse().ok()
    }
    #[cfg(not(target_os = "macos"))]
    {
        // procfs reports `st_size == 0`, so the stable regular-file reader is
        // intentionally inapplicable. Bound the fixed kernel pseudo-file as a
        // stream before decoding it instead.
        const MAX_PROC_MEMINFO_BYTES: usize = 256 * 1024;
        let meminfo = crate::input_limits::read_bounded_utf8_stream(
            fs::File::open("/proc/meminfo").ok()?,
            MAX_PROC_MEMINFO_BYTES,
        )
        .ok()?;
        let line = meminfo.lines().find(|line| line.starts_with("MemTotal"))?;
        let kib: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
        Some(kib * 1024)
    }
}

/// Resolve the Trust targo binary for a gate step, mirroring the dev-test
/// resolution order: `TRUST_TARGO_BIN`, then `TRUST_UPSTREAM_COMPAT_CARGO`
/// (the porting engine's driver hand-off), then the repo-local stage2 targo.
/// Path-constrained runs refuse ambient PATH fallbacks; looser developer runs
/// may fall back to a PATH `targo` (never `cargo`), with a loud DEV-FALLBACK
/// note. Neither mode is canonical release authority.
fn resolve_gate_targo(root: &Path, repo_local_only: bool) -> Result<PathBuf> {
    for (var, label) in [
        ("TRUST_TARGO_BIN", "TRUST_TARGO_BIN"),
        ("TRUST_UPSTREAM_COMPAT_CARGO", "TRUST_UPSTREAM_COMPAT_CARGO"),
    ] {
        if let Ok(configured) = env::var(var) {
            let configured = configured.trim();
            if configured.is_empty() {
                bail!("{label} is empty");
            }
            // The compat driver env may be a single path; reject multi-word
            // drivers here — gate steps need one canonical binary.
            let path = root_path(root, Path::new(configured));
            if repo_local_only {
                return validate_repo_stage2_tool(root, &path, label, "targo")
                    .map_err(anyhow::Error::msg);
            }
            validate_gate_targo_path(&path, label)?;
            return Ok(path);
        }
    }

    if let Some(stage2) =
        discover_unique_repo_stage2_tool(root, "targo").map_err(anyhow::Error::msg)?
    {
        return Ok(stage2);
    }

    if repo_local_only {
        bail!(
            "this trust-added diagnostic requires a path-constrained repo-local stage2 Trust targo; build build/<host>/stage2/bin/targo or set TRUST_TARGO_BIN to that exact binary (path and exact-file checks are not independent provenance)"
        );
    }

    if let Some(path_targo) = which_targo() {
        eprintln!(
            "DEV-FALLBACK: trust-added gate is using PATH targo ({}) because stage2 Trust targo was not found.",
            path_targo.display()
        );
        return Ok(path_targo);
    }

    bail!("no Trust targo was found; build stage2 or set TRUST_TARGO_BIN")
}

fn validate_gate_targo_path(path: &Path, source: &str) -> Result<()> {
    if path.file_name().and_then(|name| name.to_str())
        != Some(host_executable_name("targo").as_str())
    {
        bail!("{source} must point at canonical targo, got: {}", path.display());
    }
    if !is_executable_file(path) {
        bail!("{source} is not a runnable Trust targo: {}", path.display());
    }
    Ok(())
}

pub(super) fn find_stage2_tool(root: &Path, tool: &str) -> Result<Option<PathBuf>> {
    discover_unique_repo_stage2_tool(root, tool).map_err(anyhow::Error::msg)
}

fn which_targo() -> Option<PathBuf> {
    let paths = env::var_os("PATH")?;
    let executable = host_executable_name("targo");
    env::split_paths(&paths).map(|dir| dir.join(&executable)).find(|path| is_executable_file(path))
}

fn is_executable_file(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        path.metadata().is_ok_and(|meta| meta.is_file() && meta.permissions().mode() & 0o111 != 0)
    }
    #[cfg(not(unix))]
    {
        path.is_file()
    }
}

fn root_path(root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() { path.to_path_buf() } else { root.join(path) }
}

fn os(value: impl Into<OsString>) -> OsString {
    value.into()
}

/// Run one gate step with bounded output, a finite deadline, and process-group
/// cleanup. When `scan_skips` is set (release-like fail-closed semantics), an
/// unexpected `SKIP:`/`SKIPPING:`/`SKIPPED:` marker fails the step even if the
/// child exits 0. Output is replayed after capture so the diagnostic remains
/// visible without allowing a child to keep the gate alive indefinitely.
pub(super) fn run_step(
    program: &Path,
    args: &[OsString],
    cwd: Option<&Path>,
    envs: &[(&str, &str)],
    scan_skips: bool,
) -> Result<()> {
    run_step_inner(program, args, cwd, envs, scan_skips, true)
}

/// Like [`run_step`] but does NOT pin `RUSTC`/`RUSTDOC` onto the child.
///
/// The resolved gate `targo` is the stage2 toolchain's own driver, so it
/// already compiles with the sibling `trustc` by construction — the explicit
/// pin is redundant here. It is also actively harmful for a `targo test` step
/// whose crate UNIT-tests exercise the evidence-grade compiler-override guard
/// (`cargo_compiler_override_diagnostic`): that guard rejects any non-empty
/// ambient `RUSTC`, and a pinned `RUSTC` leaks from the outer `cargo test` into
/// the test binary, so the guard's own unit tests would false-fail. Production
/// `targo trust` invocations scrub the environment before the guard runs, which
/// this unpinned step reproduces.
pub(super) fn run_step_unpinned(
    program: &Path,
    args: &[OsString],
    cwd: Option<&Path>,
    envs: &[(&str, &str)],
    scan_skips: bool,
) -> Result<()> {
    run_step_inner(program, args, cwd, envs, scan_skips, false)
}

fn run_step_inner(
    program: &Path,
    args: &[OsString],
    cwd: Option<&Path>,
    envs: &[(&str, &str)],
    scan_skips: bool,
    pin_toolchain: bool,
) -> Result<()> {
    println!();
    println!(
        ">>> {} {}",
        program.display(),
        args.iter().map(|arg| arg.to_string_lossy().into_owned()).collect::<Vec<_>>().join(" ")
    );

    let mut command = Command::new(program);
    command.args(args);
    scrub_gate_process_environment(&mut command);
    if pin_toolchain
        && program.file_name().and_then(|name| name.to_str())
            == Some(host_executable_name("targo").as_str())
    {
        pin_targo_sibling_toolchain(&mut command, program)?;
    }
    if let Some(dir) = cwd {
        command.current_dir(dir);
    }
    for (key, value) in envs {
        command.env(key, value);
    }

    let context = format!("trust-added gate step {}", program.display());
    let output = bounded_process::output(
        &mut command,
        &context,
        MAX_GATE_OUTPUT_BYTES_PER_STREAM,
        GATE_STEP_TIMEOUT,
    )
    .map_err(anyhow::Error::msg)?;
    let stdout = String::from_utf8(output.stdout)
        .with_context(|| format!("{context} stdout was not valid UTF-8"))?;
    let stderr = String::from_utf8(output.stderr)
        .with_context(|| format!("{context} stderr was not valid UTF-8"))?;
    print!("{stdout}");
    eprint!("{stderr}");
    if !output.status.success() {
        bail!("step exited with {}", output.status);
    }
    if scan_skips && stdout.lines().chain(stderr.lines()).any(line_has_unexpected_skip) {
        bail!(
            "step reported an unexpected SKIP; release-like trust-added gates require a complete, skip-free transcript"
        );
    }
    Ok(())
}

/// Port of the robust-suite skip detector: `(^|[\s(])SKIP(?:PING|PED)?\s*:`
/// after stripping ANSI escapes.
fn line_has_unexpected_skip(line: &str) -> bool {
    let clean = strip_terminal_controls(line);
    let mut search_from = 0;
    while let Some(found) = clean[search_from..].find("SKIP") {
        let start = search_from + found;
        let boundary_ok = start == 0
            || clean[..start].chars().next_back().is_some_and(|ch| ch.is_whitespace() || ch == '(');
        let rest = &clean[start + "SKIP".len()..];
        let rest = rest.strip_prefix("PING").or_else(|| rest.strip_prefix("PED")).unwrap_or(rest);
        if boundary_ok && rest.trim_start_matches([' ', '\t']).starts_with(':') {
            return true;
        }
        search_from = start + "SKIP".len();
    }
    false
}

/// Remove terminal controls before evaluating transcript policy. Backspace is
/// applied so `Sx\x08KIP:` cannot render as a concealed skip marker; CSI,
/// OSC, DCS, SOS, PM, APC, and their C1 forms are discarded.
fn strip_terminal_controls(line: &str) -> String {
    let mut clean = String::with_capacity(line.len());
    let mut chars = line.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '\u{8}' => {
                clean.pop();
            }
            '\u{1b}' => match chars.next() {
                Some('[') => {
                    for control in chars.by_ref() {
                        if ('@'..='~').contains(&control) {
                            break;
                        }
                    }
                }
                Some(']' | 'P' | 'X' | '^' | '_') => {
                    let mut saw_escape = false;
                    for control in chars.by_ref() {
                        if control == '\u{7}' || (saw_escape && control == '\\') {
                            break;
                        }
                        saw_escape = control == '\u{1b}';
                    }
                }
                Some(_) | None => {}
            },
            '\u{9b}' => {
                for control in chars.by_ref() {
                    if ('@'..='~').contains(&control) {
                        break;
                    }
                }
            }
            control if control.is_control() && control != '\t' => {}
            printable => clean.push(printable),
        }
    }
    clean
}

// ---------------------------------------------------------------------------
// trust-added-compiletest — the tRust-added compiletest corpus
// ---------------------------------------------------------------------------

/// Compiletest suites eligible for the trust-added corpus (mirrors the shell
/// gate's suite list).
const COMPILETEST_SUITES: &[&str] = &[
    "tests/assembly-llvm/",
    "tests/build-std/",
    "tests/codegen-llvm/",
    "tests/codegen-units/",
    "tests/coverage/",
    "tests/coverage-run-rustdoc/",
    "tests/crashes/",
    "tests/debuginfo/",
    "tests/incremental/",
    "tests/mir-opt/",
    "tests/pretty/",
    "tests/run-make/",
    "tests/run-make-cargo/",
    "tests/rustdoc-gui/",
    "tests/rustdoc-html/",
    "tests/rustdoc-json/",
    "tests/rustdoc-js/",
    "tests/rustdoc-js-std/",
    "tests/rustdoc-ui/",
    "tests/ui/",
    "tests/ui-fulldeps/",
];

const SOURCE_SUFFIXES: &[&str] = &[".rs", ".js", ".goml"];

const ALLOWED_EXCEPTION_KINDS: &[&str] = &[
    "compiler-ice",
    "diagnostic-drift",
    "environment-or-dependency-gap",
    "missing-blessed-output",
    "pending-compiler-behavior",
    "runtime-regression",
];

const ALLOWED_EXCEPTION_STATUSES: &[&str] = &["active", "retired"];

const REQUIRED_EXCEPTION_FIELDS: &[&str] =
    &["path", "kind", "status", "owner", "issue", "reviewed_on", "expires_on", "reason"];
const EXCEPTION_LEDGER_TOP_LEVEL_FIELDS: &[&str] = &["schema_version", "exceptions"];
const MAX_EXCEPTION_FIELD_BYTES: usize = 4096;

/// `trust-added-compiletest`: run compiletest primary files that are present
/// in tRust but absent from the audited upstream Rust baseline, minus the
/// documented (validated, unexpired) exception ledger, through the Rust
/// bootstrap binary.
fn run_trust_added_compiletest(root: &Path, policy: GatePolicy) -> Result<()> {
    let baseline = Path::new("tests/upstream-rust/baseline.toml");
    let exceptions_path = Path::new("tests/trust-added/compiletest-exceptions.toml");

    let all_paths = collect_trust_added_primary_paths(root, baseline, policy.strict)?;
    if policy.strict && env::var_os("TRUST_EXCEPTION_VALIDATION_DATE").is_some() {
        bail!(
            "strict trust-added compiletest gates reject TRUST_EXCEPTION_VALIDATION_DATE; release evidence must use the current UTC date"
        );
    }
    let exceptions = load_active_exceptions(root, exceptions_path, &all_paths)?;
    let runnable: Vec<&String> =
        all_paths.iter().filter(|path| !exceptions.active_paths.contains(*path)).collect();

    section("tRust-added compiletest corpus");
    println!(
        "Scope: runs compiletest primary files that are present in tRust but absent from the audited upstream Rust baseline."
    );
    println!(
        "Verifier pass: this Trust-added compiletest diagnostic explicitly enables Trust verification for this corpus."
    );
    println!("tRust-added compiletest paths: {}", all_paths.len());
    println!(
        "Runnable tRust-added compiletest paths after documented exceptions: {}",
        runnable.len()
    );
    if all_paths.len() != runnable.len() {
        println!(
            "Active exceptions are known failing tRust-added tests, not skipped passes; a green run covers only the runnable paths above."
        );
        println!("Documented tRust-added compiletest exceptions:");
        for entry in &exceptions.active_display {
            println!("  {entry}");
        }
    }
    if all_paths.is_empty() {
        if policy.strict {
            bail!("strict trust-added compiletest gate found no tRust-added primary paths");
        }
        println!("No tRust-added compiletest paths were found (developer mode only).");
        return Ok(());
    }
    if runnable.is_empty() {
        if policy.strict {
            bail!(
                "strict trust-added compiletest diagnostic has no runnable paths after exceptions; exceptions cannot replace execution"
            );
        }
        println!(
            "No runnable tRust-added compiletest paths remain after documented exceptions (developer mode only)."
        );
        return Ok(());
    }

    let bootstrap = rust_bootstrap_binary(root)?;
    let bootstrap_identity = snapshot_exact_executable(
        &bootstrap,
        "trust-added-compiletest",
        "repository bootstrap executable",
    )
    .map_err(anyhow::Error::msg)?;
    let mut common = vec![
        os("test"),
        os("--src"),
        root.as_os_str().to_owned(),
        os("--stage"),
        os("2"),
        os("--no-fail-fast"),
        os("--force-rerun"),
        os("--set"),
        os("build.submodules=false"),
    ];
    common.extend(runnable.iter().map(|path| os(path.as_str())));
    common.extend(validated_bootstrap_extra_args()?);

    // Compatibility and verifier diagnostic results are distinct. The vanilla
    // pass proves drop-in compiletest behavior; the second pass deliberately
    // omits --trust-vanilla so Trust verification remains enabled by default.
    let mut vanilla = common.clone();
    vanilla.insert(5, os("--trust-vanilla"));
    section("tRust-added compiletest vanilla compatibility pass");
    let run_result = (|| -> Result<()> {
        run_step(&bootstrap, &vanilla, Some(root), &[], policy.strict)?;

        section("tRust-added compiletest verification-enabled pass");
        run_step(&bootstrap, &common, Some(root), &[], policy.strict)
    })();
    let identity_result = revalidate_exact_executable(
        &bootstrap_identity,
        "trust-added-compiletest after-use check",
        "repository bootstrap executable",
    )
    .map_err(anyhow::Error::msg);
    run_result?;
    identity_result
}

/// Closed parsing for the legacy bootstrap-argument handoff. These options
/// may tune build mechanics but cannot replace the stage, source root,
/// verification lane, test selection, or failure policy established above.
fn validated_bootstrap_extra_args() -> Result<Vec<OsString>> {
    let Ok(raw) = env::var("TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS") else {
        return Ok(Vec::new());
    };
    validated_bootstrap_extra_args_from(&raw)
}

fn validated_bootstrap_extra_args_from(raw: &str) -> Result<Vec<OsString>> {
    let words = raw.split_whitespace().collect::<Vec<_>>();
    let mut accepted = Vec::new();
    let mut index = 0;
    while index < words.len() {
        match words[index] {
            "--set" => {
                let Some(value) = words.get(index + 1).copied() else {
                    bail!("TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS: --set requires a value");
                };
                if !matches!(value, "llvm.ninja=false" | "build.submodules=false") {
                    bail!(
                        "TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS may set only llvm.ninja=false or build.submodules=false, got `{value}`"
                    );
                }
                accepted.extend([os("--set"), os(value)]);
                index += 2;
            }
            "-j" | "--jobs" => {
                let Some(value) = words.get(index + 1).copied() else {
                    bail!("TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS: {} requires a value", words[index]);
                };
                if value.parse::<usize>().ok().filter(|jobs| *jobs > 0).is_none() {
                    bail!("TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS has invalid job count `{value}`");
                }
                accepted.extend([os(words[index]), os(value)]);
                index += 2;
            }
            value if value.starts_with("--jobs=") => {
                let jobs = value.trim_start_matches("--jobs=");
                if jobs.parse::<usize>().ok().filter(|jobs| *jobs > 0).is_none() {
                    bail!("TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS has invalid job count `{jobs}`");
                }
                accepted.push(os(value));
                index += 1;
            }
            other => bail!(
                "TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS contains policy-changing or unsupported option `{other}`"
            ),
        }
    }
    Ok(accepted)
}

/// Locate the Rust bootstrap binary — the same resolution the upstream
/// porting engine uses. `x.py`, Python, and shell wrappers are rejected:
/// this local diagnostic drives the bootstrap binary directly.
fn rust_bootstrap_binary(root: &Path) -> Result<PathBuf> {
    if let Ok(configured) = env::var("TRUST_UPSTREAM_RUST_BOOTSTRAP") {
        let configured = configured.trim();
        if configured.is_empty() {
            bail!("TRUST_UPSTREAM_RUST_BOOTSTRAP is empty");
        }
        let path = root_path(root, Path::new(configured));
        return validate_repo_bootstrap_binary(root, &path, "TRUST_UPSTREAM_RUST_BOOTSTRAP");
    }
    let executable = host_executable_name("bootstrap");
    for candidate in [
        root.join("build/bootstrap/debug").join(&executable),
        root.join("build/bootstrap").join(&executable),
    ] {
        match fs::symlink_metadata(&candidate) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                bail!("could not inspect bootstrap candidate {}: {error}", candidate.display())
            }
            Ok(_) => {
                return validate_repo_bootstrap_binary(root, &candidate, "bootstrap discovery");
            }
        }
    }
    bail!(
        "Rust bootstrap binary not found; build src/bootstrap or set TRUST_UPSTREAM_RUST_BOOTSTRAP"
    )
}

fn validate_repo_bootstrap_binary(root: &Path, path: &Path, source: &str) -> Result<PathBuf> {
    let executable = host_executable_name("bootstrap");
    if path.file_name().and_then(|name| name.to_str()) != Some(executable.as_str()) {
        bail!("{source} must name the canonical Rust bootstrap binary: {}", path.display());
    }
    let canonical_root = fs::canonicalize(root)
        .with_context(|| format!("{source} could not canonicalize {}", root.display()))?;
    let relative = path
        .strip_prefix(root)
        .or_else(|_| path.strip_prefix(&canonical_root))
        .with_context(|| {
            format!("{source} must be repository-local under build/bootstrap: {}", path.display())
        })?;
    let components = relative
        .components()
        .map(|component| match component {
            Component::Normal(value) => value.to_str(),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
        .with_context(|| format!("{source} path has non-normal components: {}", path.display()))?;
    // `build` may be the sanctioned link to `build.noindex` (docs/BUILD_AND_INSTALL.md,
    // "Keeping Spotlight out of build/"), so either spelling of its first
    // component names the repository's build tree.
    let valid_shape = components
        .first()
        .is_some_and(|first| crate::stage2_tools::is_repo_build_component(&canonical_root, first))
        && (components[1..] == ["bootstrap", executable.as_str()]
            || components[1..] == ["bootstrap", "debug", executable.as_str()]);
    if !valid_shape {
        bail!(
            "{source} must be build/bootstrap/{0} or build/bootstrap/debug/{0}: {1}",
            executable,
            path.display()
        );
    }

    let mut prefix = canonical_root.clone();
    for (index, component) in relative.components().enumerate() {
        let Component::Normal(value) = component else {
            bail!("{source} path has non-normal components: {}", path.display());
        };
        prefix.push(value);
        let metadata = fs::symlink_metadata(&prefix)
            .with_context(|| format!("{source} could not inspect {}", prefix.display()))?;
        // The one admitted link is `build` itself, and only as the sanctioned
        // `build -> build.noindex`; the canonical path bound below then names
        // `build.noindex`. Every other link is still refused.
        let sanctioned_build_link = index == 0
            && value == "build"
            && crate::stage2_tools::is_sanctioned_build_link(&canonical_root);
        if metadata.file_type().is_symlink() && !sanctioned_build_link {
            bail!("{source} must not traverse a symlink: {}", prefix.display());
        }
    }
    let canonical = fs::canonicalize(&prefix)
        .with_context(|| format!("{source} could not canonicalize {}", prefix.display()))?;
    if !canonical.starts_with(&canonical_root) || !is_executable_file(&canonical) {
        bail!("{source} is not an executable regular file: {}", canonical.display());
    }
    Ok(canonical)
}

/// Primary compiletest files present locally but absent from the baseline's
/// upstream revision. run-make tests collapse to their directory; other
/// suites keep source files (`.rs`, `.js`, `.goml`). Sorted, deduplicated.
fn collect_trust_added_primary_paths(
    root: &Path,
    baseline: &Path,
    fixed_system_git_only: bool,
) -> Result<Vec<String>> {
    let git = resolve_gate_git(root, fixed_system_git_only)?;
    if !git_is_worktree(&git, root)? {
        bail!(
            "trust-added compiletest requires a Git worktree to authenticate the upstream baseline and local primary-file inventory"
        );
    }

    let revision = baseline_upstream_revision(root, baseline)?;
    let upstream: BTreeSet<String> = git_path_records(
        &git,
        root,
        &["ls-tree", "-r", "-z", "--name-only", revision.as_str(), "--", "tests"],
    )?
    .into_iter()
    .collect();
    let current = git_path_records(&git, root, &["ls-files", "-z", "--", "tests"])?;

    let mut seen = BTreeSet::new();
    for path in current {
        if upstream.contains(&path)
            || !COMPILETEST_SUITES.iter().any(|suite| path.starts_with(suite))
        {
            continue;
        }
        let primary = if path.starts_with("tests/run-make/") {
            let mut parts = path.split('/');
            let (Some(a), Some(b), Some(c)) = (parts.next(), parts.next(), parts.next()) else {
                continue;
            };
            format!("{a}/{b}/{c}")
        } else if SOURCE_SUFFIXES.iter().any(|suffix| path.ends_with(suffix)) {
            path
        } else {
            continue;
        };
        seen.insert(primary);
    }
    Ok(seen.into_iter().collect())
}

fn baseline_upstream_revision(root: &Path, baseline: &Path) -> Result<String> {
    let bytes = read_bounded_exact_file_under(root, baseline, MAX_BASELINE_BYTES)?;
    let input = String::from_utf8(bytes)
        .with_context(|| format!("{} is not valid UTF-8", baseline.display()))?;
    let value: toml::Value =
        input.parse().with_context(|| format!("failed to parse {}", baseline.display()))?;
    let revision = value
        .get("upstream")
        .and_then(|upstream| upstream.get("revision"))
        .and_then(toml::Value::as_str)
        .with_context(|| format!("{} is missing upstream.revision", baseline.display()))?;
    let revision = revision.split_once(':').map_or(revision, |(_, rev)| rev);
    if revision.len() != 40
        || !revision.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        bail!(
            "{} upstream.revision must end in a canonical lowercase 40-hex commit",
            baseline.display()
        );
    }
    Ok(revision.to_string())
}

pub(super) fn resolve_gate_git(root: &Path, fixed_system_only: bool) -> Result<PathBuf> {
    #[cfg(unix)]
    const SYSTEM_GIT_CANDIDATES: &[&str] =
        &["/usr/bin/git", "/usr/local/bin/git", "/opt/homebrew/bin/git"];
    #[cfg(windows)]
    const SYSTEM_GIT_CANDIDATES: &[&str] =
        &[r"C:\Program Files\Git\cmd\git.exe", r"C:\Program Files\Git\bin\git.exe"];
    #[cfg(not(any(unix, windows)))]
    const SYSTEM_GIT_CANDIDATES: &[&str] = &[];

    for candidate in SYSTEM_GIT_CANDIDATES {
        let candidate = Path::new(candidate);
        if is_executable_file(candidate) {
            return fs::canonicalize(candidate).with_context(|| {
                format!("failed to canonicalize system Git {}", candidate.display())
            });
        }
    }
    if fixed_system_only {
        bail!("strict Trust gate requires a fixed system Git executable");
    }

    let Some(path) = env::var_os("PATH").and_then(|paths| {
        env::split_paths(&paths)
            .map(|dir| dir.join(host_executable_name("git")))
            .find(|candidate| is_executable_file(candidate))
    }) else {
        bail!("Git executable not found");
    };
    let canonical = fs::canonicalize(&path)
        .with_context(|| format!("failed to canonicalize Git executable {}", path.display()))?;
    let canonical_root = fs::canonicalize(root)
        .with_context(|| format!("failed to canonicalize repository root {}", root.display()))?;
    if canonical.starts_with(canonical_root) {
        bail!(
            "developer Git fallback must not resolve inside the repository: {}",
            canonical.display()
        );
    }
    Ok(canonical)
}

pub(super) fn gate_git_command(git: &Path, root: &Path) -> Command {
    let mut command = Command::new(git);
    for (name, _) in env::vars_os() {
        if name.to_str().is_some_and(|name| name.starts_with("GIT_")) {
            command.env_remove(name);
        }
    }
    command
        .env_remove("HOME")
        .env_remove("XDG_CONFIG_HOME")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", if cfg!(windows) { "NUL" } else { "/dev/null" })
        .env("GIT_OPTIONAL_LOCKS", "0")
        .env("LC_ALL", "C")
        .args(["--no-pager", "--literal-pathspecs", "-c", "core.fsmonitor=false", "-C"])
        .arg(root);
    command
}

fn git_is_worktree(git: &Path, root: &Path) -> Result<bool> {
    let mut command = gate_git_command(git, root);
    command.args(["rev-parse", "--is-inside-work-tree"]);
    let output = bounded_process::output(
        &mut command,
        "fixed-config Git rev-parse",
        MAX_GIT_OUTPUT_BYTES_PER_STREAM,
        GIT_COMMAND_TIMEOUT,
    )
    .map_err(anyhow::Error::msg)?;
    if !output.status.success() {
        return Ok(false);
    }
    Ok(output.stdout == b"true\n" || output.stdout == b"true\r\n")
}

fn git_path_records(git: &Path, root: &Path, args: &[&str]) -> Result<Vec<String>> {
    let description = format!("fixed-config Git {}", args.join(" "));
    let mut command = gate_git_command(git, root);
    command.args(args);
    let output = bounded_process::output(
        &mut command,
        &description,
        MAX_GIT_OUTPUT_BYTES_PER_STREAM,
        GIT_COMMAND_TIMEOUT,
    )
    .map_err(anyhow::Error::msg)?;
    if !output.status.success() {
        let stderr = String::from_utf8(output.stderr)
            .context("Git failure diagnostics were not valid UTF-8")?;
        bail!("git {} failed: {}", args.join(" "), stderr.trim());
    }
    parse_git_path_records(&output.stdout)
        .with_context(|| format!("git {} emitted an invalid path inventory", args.join(" ")))
}

fn parse_git_path_records(output: &[u8]) -> Result<Vec<String>> {
    if !output.is_empty() && output.last() != Some(&0) {
        bail!("path stream is not terminated by NUL");
    }
    let records = output
        .strip_suffix(&[0])
        .unwrap_or(output)
        .split(|byte| *byte == 0)
        .filter(|record| !record.is_empty())
        .map(|record| {
            let path = std::str::from_utf8(record)
                .context("inventory contains a non-UTF-8 path that compiletest cannot name")?;
            if Path::new(path).is_absolute()
                || path.bytes().any(|byte| byte.is_ascii_control())
                || !Path::new(path)
                    .components()
                    .all(|component| matches!(component, Component::Normal(_)))
            {
                bail!("inventory contains a non-canonical relative path: {path:?}");
            }
            Ok(path.to_string())
        })
        .collect::<Result<Vec<_>>>()?;
    let mut seen = BTreeSet::new();
    for path in &records {
        if !seen.insert(path.as_str()) {
            bail!("inventory contains a duplicate path: {path:?}");
        }
    }
    Ok(records)
}

struct ActiveExceptions {
    active_paths: BTreeSet<String>,
    active_display: Vec<String>,
}

/// Parse + validate the trust-added compiletest exception ledger (schema
/// 0.2.0). Validation is fail-closed: any malformed, incomplete, or expired
/// entry rejects the whole gate, exactly like the shell gate it replaces.
fn load_active_exceptions(
    root: &Path,
    path: &Path,
    primary_paths: &[String],
) -> Result<ActiveExceptions> {
    let mut result = ActiveExceptions { active_paths: BTreeSet::new(), active_display: Vec::new() };
    match fs::symlink_metadata(root.join(path)) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(result),
        Err(error) => {
            return Err(error)
                .with_context(|| format!("failed to inspect exception ledger {}", path.display()));
        }
        Ok(_) => {}
    }
    let primaries: BTreeSet<&str> = primary_paths.iter().map(String::as_str).collect();
    let bytes = read_bounded_exact_file_under(root, path, MAX_EXCEPTION_LEDGER_BYTES)?;
    let input = String::from_utf8(bytes)
        .with_context(|| format!("{} is not valid UTF-8", path.display()))?;
    let ledger: toml::Value =
        input.parse().with_context(|| format!("failed to parse {}", path.display()))?;

    let mut errors = Vec::new();
    let Some(ledger_table) = ledger.as_table() else {
        bail!("trust-added compiletest exception ledger root must be a TOML table");
    };
    for field in ledger_table.keys() {
        if !EXCEPTION_LEDGER_TOP_LEVEL_FIELDS.contains(&field.as_str()) {
            errors.push(format!(
                "trust-added compiletest exception ledger has unknown top-level field: {field}"
            ));
        }
    }
    if ledger.get("schema_version").and_then(toml::Value::as_str) != Some("0.2.0") {
        errors.push("trust-added compiletest exception ledger schema_version must be 0.2.0".into());
    }
    let validation_date =
        env::var("TRUST_EXCEPTION_VALIDATION_DATE").unwrap_or_else(|_| today_utc_yyyy_mm_dd());
    let validation_date_is_valid = is_yyyy_mm_dd(&validation_date);
    if !validation_date_is_valid {
        errors
            .push(format!("TRUST_EXCEPTION_VALIDATION_DATE must be YYYY-MM-DD: {validation_date}"));
    }

    let empty = Vec::new();
    let entries = match ledger.get("exceptions") {
        Some(toml::Value::Array(entries)) => entries,
        Some(_) => {
            errors.push(
                "trust-added compiletest exception ledger exceptions must be an array".into(),
            );
            &empty
        }
        None => {
            errors.push(
                "trust-added compiletest exception ledger is missing exceptions array".into(),
            );
            &empty
        }
    };
    let mut seen_paths = BTreeSet::new();
    for (index, entry) in entries.iter().enumerate() {
        let idx = index + 1;
        let Some(entry_table) = entry.as_table() else {
            errors.push(format!("exceptions[{idx}] must be a TOML table"));
            continue;
        };
        for name in entry_table.keys() {
            if !REQUIRED_EXCEPTION_FIELDS.contains(&name.as_str()) {
                errors.push(format!("exceptions[{idx}] has unknown field: {name}"));
            }
        }
        let field = |name: &str| -> Option<&str> {
            entry_table
                .get(name)
                .and_then(toml::Value::as_str)
                .filter(|value| !value.trim().is_empty())
        };
        let missing: Vec<&str> = REQUIRED_EXCEPTION_FIELDS
            .iter()
            .copied()
            .filter(|name| field(name).is_none())
            .collect();
        if !missing.is_empty() {
            errors.push(format!(
                "exceptions[{idx}] missing required metadata: {}",
                missing.join(", ")
            ));
            continue;
        }
        let mut malformed_field = false;
        for name in REQUIRED_EXCEPTION_FIELDS {
            let value = field(name).expect("required field checked");
            if value != value.trim()
                || value.len() > MAX_EXCEPTION_FIELD_BYTES
                || value.chars().any(char::is_control)
            {
                errors.push(format!(
                    "exceptions[{idx}] {name} must be canonical, control-free, and at most {MAX_EXCEPTION_FIELD_BYTES} bytes"
                ));
                malformed_field = true;
            }
        }
        if malformed_field {
            continue;
        }
        let path_value = field("path").expect("checked");
        let kind = field("kind").expect("checked");
        let status = field("status").expect("checked");
        let owner = field("owner").expect("checked");
        let issue = field("issue").expect("checked");
        let reviewed_on = field("reviewed_on").expect("checked");
        let expires_on = field("expires_on").expect("checked");

        if !seen_paths.insert(path_value) {
            errors.push(format!("exceptions[{idx}] duplicates path: {path_value}"));
            continue;
        }
        if !primaries.contains(path_value) {
            errors.push(format!(
                "exceptions[{idx}] path is not a tRust-added compiletest primary file: {path_value}"
            ));
            continue;
        }
        if !ALLOWED_EXCEPTION_KINDS.contains(&kind) {
            errors.push(format!("exceptions[{idx}] kind is not allowed: {kind}"));
        }
        if !ALLOWED_EXCEPTION_STATUSES.contains(&status) {
            errors.push(format!("exceptions[{idx}] status is not allowed: {status}"));
        }
        let valid_owner = owner.strip_prefix('@').is_some_and(|team| {
            !team.is_empty()
                && team
                    .bytes()
                    .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
                && team.as_bytes().first().is_some_and(u8::is_ascii_alphanumeric)
                && team.as_bytes().last().is_some_and(u8::is_ascii_alphanumeric)
        });
        if !valid_owner {
            errors.push(format!("exceptions[{idx}] owner must be an @team: {owner}"));
        }
        if !has_reviewed_issue_anchor(issue) {
            errors.push(format!(
                "exceptions[{idx}] issue must be a real tracker URL or local review-report anchor: {issue}"
            ));
        }
        if !is_yyyy_mm_dd(reviewed_on) {
            errors.push(format!("exceptions[{idx}] reviewed_on must be YYYY-MM-DD: {reviewed_on}"));
        }
        if !is_yyyy_mm_dd(expires_on) {
            errors.push(format!("exceptions[{idx}] expires_on must be YYYY-MM-DD: {expires_on}"));
        }
        if is_yyyy_mm_dd(reviewed_on) && is_yyyy_mm_dd(expires_on) {
            if expires_on <= reviewed_on {
                errors.push(format!(
                    "exceptions[{idx}] expires_on must be after reviewed_on: {expires_on}"
                ));
            }
            if status == "active"
                && validation_date_is_valid
                && expires_on <= validation_date.as_str()
            {
                errors.push(format!("exceptions[{idx}] active exception expired on {expires_on}"));
            }
        }
        if status == "active" {
            result.active_paths.insert(path_value.to_string());
            result.active_display.push(format!(
                "{path_value} [{kind}] owner={owner} expires={expires_on} — {}",
                field("reason").expect("checked")
            ));
        }
    }

    if !errors.is_empty() {
        for error in &errors {
            eprintln!("FAIL: {error}");
        }
        bail!(
            "trust-added compiletest exception ledger failed validation ({} finding(s))",
            errors.len()
        );
    }
    Ok(result)
}

/// Reviewed-issue anchors: a real upstream/Trust tracker URL with a numeric
/// id, or a local review-report anchor. Bare `#123` and self-referential
/// strings are rejected.
fn has_reviewed_issue_anchor(issue: &str) -> bool {
    if issue.is_empty() || issue.starts_with('#') || issue.contains("trust-added-compiletest") {
        return false;
    }
    for prefix in [
        "https://github.com/rust-lang/rust/issues/",
        "https://github.com/alabsystems/Trust/issues/",
    ] {
        if let Some(rest) = issue.strip_prefix(prefix) {
            return !rest.is_empty() && rest.bytes().all(|byte| byte.is_ascii_digit());
        }
    }
    let Some((report, anchor)) = issue.split_once('#') else { return false };
    report.starts_with("reports/trust-added/")
        && report.ends_with(".md")
        && !report.contains('\\')
        && report
            .split('/')
            .all(|component| !component.is_empty() && component != "." && component != "..")
        && !anchor.is_empty()
        && anchor
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
}

// ---------------------------------------------------------------------------
// Dates (no chrono: civil-from-days is ~10 lines and this stays dependency-free)
// ---------------------------------------------------------------------------

fn is_yyyy_mm_dd(value: &str) -> bool {
    let bytes = value.as_bytes();
    if bytes.len() != 10 || bytes[4] != b'-' || bytes[7] != b'-' {
        return false;
    }
    if !value[..4].bytes().all(|byte| byte.is_ascii_digit())
        || !value[5..7].bytes().all(|byte| byte.is_ascii_digit())
        || !value[8..].bytes().all(|byte| byte.is_ascii_digit())
    {
        return false;
    }
    let year: i64 = value[..4].parse().unwrap_or(0);
    let month: u32 = value[5..7].parse().unwrap_or(0);
    let day: u32 = value[8..].parse().unwrap_or(0);
    (1..=9999).contains(&year)
        && (1..=12).contains(&month)
        && day >= 1
        && day <= days_in_month(year, month)
}

fn days_in_month(year: i64, month: u32) -> u32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) => 29,
        2 => 28,
        _ => 0,
    }
}

/// Today's UTC date, via the civil-from-days algorithm (Howard Hinnant).
fn today_utc_yyyy_mm_dd() -> String {
    let secs = SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_secs()) as i64;
    let z = secs.div_euclid(86_400) + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let year = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = if month <= 2 { year + 1 } else { year };
    format!("{year:04}-{month:02}-{day:02}")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn command_env(command: &Command, key: &str) -> Option<Option<OsString>> {
        command
            .get_envs()
            .find(|(name, _)| *name == std::ffi::OsStr::new(key))
            .map(|(_, value)| value.map(OsString::from))
    }

    #[test]
    fn compiler_and_loader_authority_is_scrubbed() {
        let mut command = Command::new("unused-test-program");
        for key in COMPILER_OVERRIDE_ENV.iter().chain(FIXED_LOADER_ENV) {
            command.env(key, "hostile");
        }
        scrub_gate_process_environment(&mut command);

        for key in ["TRUSTC", "TRUST_NO_VERIFY", "RUSTC", "RUSTDOC", "LD_PRELOAD"] {
            assert_eq!(command_env(&command, key), Some(None), "{key} survived the scrub");
        }
        for key in [
            "RUSTC_WRAPPER",
            "RUSTC_WORKSPACE_WRAPPER",
            "CARGO_BUILD_RUSTC_WRAPPER",
            "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
            "CARGO_ENCODED_RUSTFLAGS",
            "CARGO_ENCODED_RUSTDOCFLAGS",
        ] {
            assert_eq!(
                command_env(&command, key),
                Some(Some(OsString::new())),
                "{key} must explicitly override Cargo configuration"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn targo_commands_pin_exact_sibling_trust_drivers() {
        use std::os::unix::fs::PermissionsExt as _;

        let temp = tempfile::tempdir().expect("toolchain fixture");
        let bin = temp.path().join("bin");
        fs::create_dir_all(&bin).expect("create toolchain bin");
        for tool in ["targo", "trustc", "trustdoc"] {
            let path = bin.join(host_executable_name(tool));
            fs::write(&path, b"#!/bin/sh\nexit 0\n").expect("write tool fixture");
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700))
                .expect("make tool fixture executable");
        }

        let targo = bin.join(host_executable_name("targo"));
        let trustc =
            fs::canonicalize(bin.join(host_executable_name("trustc"))).expect("canonical trustc");
        let trustdoc = fs::canonicalize(bin.join(host_executable_name("trustdoc")))
            .expect("canonical trustdoc");
        let mut command = Command::new(&targo);
        scrub_gate_process_environment(&mut command);
        pin_targo_sibling_toolchain(&mut command, &targo).expect("pin sibling Trust drivers");

        assert_eq!(command_env(&command, "RUSTC"), Some(Some(trustc.clone().into_os_string())));
        assert_eq!(command_env(&command, "CARGO_BUILD_RUSTC"), Some(Some(trustc.into_os_string())));
        assert_eq!(command_env(&command, "RUSTDOC"), Some(Some(trustdoc.clone().into_os_string())));
        assert_eq!(
            command_env(&command, "CARGO_BUILD_RUSTDOC"),
            Some(Some(trustdoc.into_os_string()))
        );
    }

    #[cfg(unix)]
    #[test]
    fn targo_commands_reject_redirected_sibling_drivers() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let temp = tempfile::tempdir().expect("redirected toolchain fixture");
        let bin = temp.path().join("bin");
        fs::create_dir_all(&bin).expect("create toolchain bin");
        for tool in ["targo", "trustc"] {
            let path = bin.join(host_executable_name(tool));
            fs::write(&path, b"#!/bin/sh\nexit 0\n").expect("write tool fixture");
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700))
                .expect("make tool fixture executable");
        }
        let external = temp.path().join("external-trustdoc");
        fs::write(&external, b"#!/bin/sh\nexit 0\n").expect("write external driver");
        fs::set_permissions(&external, fs::Permissions::from_mode(0o700))
            .expect("make external driver executable");
        symlink(&external, bin.join(host_executable_name("trustdoc"))).expect("redirect trustdoc");

        let targo = bin.join(host_executable_name("targo"));
        let mut command = Command::new(&targo);
        assert!(
            pin_targo_sibling_toolchain(&mut command, &targo).is_err(),
            "an external trustdoc symlink must not become gate authority"
        );
    }

    #[test]
    fn native_modes_are_exactly_the_ported_set() {
        assert!(is_native_mode("quick"));
        assert!(is_native_mode("trust-added-compiletest"));
        assert!(is_native_mode("trustc-native"));
        assert!(is_native_mode("native-contracts-pipeline-v2"));
        assert!(is_native_mode("binary-decompilation-golden"));
        assert!(is_native_mode("launch"));
        assert!(is_native_mode("local-stage2-surface-smoke"));
        assert!(is_native_mode("trust-extra-smoke"));
        assert!(is_native_mode("public-distribution-cull-smoke"));
        assert!(is_native_mode("prepublish-local-surface-smoke"));
        assert!(is_native_mode("stage0-metadata-coherence-smoke"));
        for canonical_blocked in [
            "installed",
            "installed-default",
            "trust-extra",
            "public-distribution",
            "prepublish",
            "stage0-lineage",
        ] {
            assert!(
                !is_native_mode(canonical_blocked),
                "{canonical_blocked} must remain blocked until its documented release evidence exists"
            );
        }
        // Non-manifest aggregate aliases remain unported (not domination gates).
        for pending in ["smoke", "parity", "full"] {
            assert!(!is_native_mode(pending), "{pending} is not ported yet");
        }
    }

    #[test]
    fn skip_detector_matches_shell_regex_semantics() {
        assert!(line_has_unexpected_skip("SKIP: missing tool"));
        assert!(line_has_unexpected_skip("note SKIPPING: bad env"));
        assert!(line_has_unexpected_skip("(SKIPPED: fixture)"));
        assert!(line_has_unexpected_skip("\t SKIP : spaced colon"));
        assert!(line_has_unexpected_skip("\u{1b}[32mSKIP\u{1b}[0m: colored"));
        assert!(line_has_unexpected_skip("\u{1b}[2KSKIP: erased-line control"));
        assert!(!line_has_unexpected_skip("test result: ok. 3 passed; 2 ignored"));
        assert!(!line_has_unexpected_skip("SKIPPINGS: not a marker"));
        assert!(!line_has_unexpected_skip("prefixSKIP: embedded word"));
        assert!(!line_has_unexpected_skip("SKIP without colon"));
    }

    #[test]
    fn yyyy_mm_dd_validation_matches_python_date_semantics() {
        assert!(is_yyyy_mm_dd("2026-07-11"));
        assert!(is_yyyy_mm_dd("2024-02-29")); // leap day
        assert!(!is_yyyy_mm_dd("2026-02-29")); // not a leap year
        assert!(!is_yyyy_mm_dd("2026-13-01"));
        assert!(!is_yyyy_mm_dd("2026-00-10"));
        assert!(!is_yyyy_mm_dd("2026-07-32"));
        assert!(!is_yyyy_mm_dd("26-07-11"));
        assert!(!is_yyyy_mm_dd("2026/07/11"));
        assert!(!is_yyyy_mm_dd("2026-7-11"));
        assert!(!is_yyyy_mm_dd("0000-01-01"));
    }

    #[test]
    fn today_utc_is_a_valid_date() {
        assert!(is_yyyy_mm_dd(&today_utc_yyyy_mm_dd()));
    }

    #[test]
    fn issue_anchor_rules_match_shell_gate() {
        assert!(has_reviewed_issue_anchor("https://github.com/rust-lang/rust/issues/128044"));
        assert!(has_reviewed_issue_anchor("https://github.com/alabsystems/Trust/issues/12"));
        assert!(has_reviewed_issue_anchor("reports/trust-added/review.md#finding-3"));
        assert!(!has_reviewed_issue_anchor("#123"));
        assert!(!has_reviewed_issue_anchor("https://github.com/rust-lang/rust/issues/abc"));
        assert!(!has_reviewed_issue_anchor(
            "https://github.com/rust-lang/rust/issues/archive/128044"
        ));
        assert!(!has_reviewed_issue_anchor("reports/trust-added/review.md"));
        assert!(!has_reviewed_issue_anchor("reports/trust-added/../forged.md#finding-3"));
        assert!(!has_reviewed_issue_anchor("reports/trust-added/review.md#finding/3"));
        assert!(!has_reviewed_issue_anchor("see trust-added-compiletest ledger"));
        assert!(!has_reviewed_issue_anchor(""));
    }

    #[test]
    fn git_inventory_is_nul_terminated_canonical_and_unique() {
        assert_eq!(
            parse_git_path_records(b"tests/ui/a.rs\0tests/run-make/example\0")
                .expect("canonical inventory"),
            ["tests/ui/a.rs", "tests/run-make/example"]
        );
        for invalid in [
            b"tests/ui/a.rs".as_slice(),
            b"../tests/ui/a.rs\0".as_slice(),
            b"tests/ui/a.rs\ntests/ui/b.rs\0".as_slice(),
            b"tests/ui/a.rs\0tests/ui/a.rs\0".as_slice(),
        ] {
            assert!(parse_git_path_records(invalid).is_err(), "accepted {invalid:?}");
        }
    }

    fn exception_ledger(top_extra: &str, entry_extra: &str) -> String {
        format!(
            r#"schema_version = "0.2.0"
{top_extra}
[[exceptions]]
path = "tests/ui/trust/sample.rs"
kind = "pending-compiler-behavior"
status = "active"
owner = "@trust-compiler"
issue = "reports/trust-added/review.md#sample"
reviewed_on = "2026-07-01"
expires_on = "9999-12-31"
reason = "A reviewed, bounded exception."
{entry_extra}
"#
        )
    }

    #[test]
    fn exception_ledger_schema_is_closed_and_typed() {
        let temp = tempfile::tempdir().expect("exception ledger fixture");
        let relative = Path::new("ledger.toml");
        let ledger = temp.path().join(relative);
        let primaries = vec!["tests/ui/trust/sample.rs".to_string()];

        fs::write(&ledger, exception_ledger("", "")).expect("valid ledger");
        let active =
            load_active_exceptions(temp.path(), relative, &primaries).expect("closed valid ledger");
        assert!(active.active_paths.contains("tests/ui/trust/sample.rs"));

        for invalid in [
            exception_ledger("unexpected = true", ""),
            exception_ledger("", "unexpected = true"),
            exception_ledger("", "")
                .replace("reason = \"A reviewed, bounded exception.\"", "reason = 7"),
            exception_ledger("", "").replace("@trust-compiler", "@trust compiler"),
            exception_ledger("", "")
                .replace("A reviewed, bounded exception.", "A reviewed,\\u001bforged exception."),
        ] {
            fs::write(&ledger, invalid).expect("invalid ledger fixture");
            assert!(
                load_active_exceptions(temp.path(), relative, &primaries).is_err(),
                "malformed ledger was accepted"
            );
        }

        let valid = exception_ledger("", "");
        let (_, entry) = valid.split_once("[[exceptions]]").expect("entry marker");
        fs::write(&ledger, format!("{valid}\n[[exceptions]]{entry}"))
            .expect("duplicate ledger fixture");
        assert!(load_active_exceptions(temp.path(), relative, &primaries).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn exception_ledger_rejects_symlink() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("exception symlink fixture");
        let target = temp.path().join("real.toml");
        fs::write(&target, exception_ledger("", "")).expect("real ledger");
        symlink(&target, temp.path().join("ledger.toml")).expect("ledger symlink");
        let primaries = vec!["tests/ui/trust/sample.rs".to_string()];
        assert!(load_active_exceptions(temp.path(), Path::new("ledger.toml"), &primaries).is_err());
    }

    #[test]
    fn ansi_stripping_removes_color_codes() {
        assert_eq!(strip_terminal_controls("\u{1b}[1;32mok\u{1b}[0m"), "ok");
        assert_eq!(strip_terminal_controls("\u{1b}[2Kvisible"), "visible");
        assert_eq!(strip_terminal_controls("plain"), "plain");
        assert_eq!(strip_terminal_controls("Sx\u{8}KIP: hidden"), "SKIP: hidden");
        assert_eq!(
            strip_terminal_controls(
                "\u{1b}]8;;https://example.invalid\u{1b}\\SKIP:\u{1b}]8;;\u{1b}\\ hidden"
            ),
            "SKIP: hidden"
        );
    }

    #[test]
    fn bootstrap_extra_args_are_mechanical_only() {
        let accepted = validated_bootstrap_extra_args_from(
            "--set llvm.ninja=false --set build.submodules=false --jobs=3 -j 2",
        )
        .expect("mechanical bootstrap options");
        assert_eq!(
            accepted,
            [
                "--set",
                "llvm.ninja=false",
                "--set",
                "build.submodules=false",
                "--jobs=3",
                "-j",
                "2",
            ]
            .map(OsString::from)
        );
        for rejected in [
            "--stage 0",
            "--trust-vanilla",
            "--exclude tests/ui/trust",
            "--set rust.download-rustc=true",
            "--jobs=0",
        ] {
            assert!(
                validated_bootstrap_extra_args_from(rejected).is_err(),
                "unexpectedly accepted {rejected}"
            );
        }
    }

    const GIB: u64 = 1024 * 1024 * 1024;

    /// The rule must clamp below the core count on the host that produced the
    /// SIGKILL. The old rule (`min(cores, RAM / 5 GiB)`) answered 18 there and
    /// clamped nothing at all.
    ///
    /// Note what this does and does not assert. It asserts the clamp binds on
    /// this host. It does NOT assert the clamp would have prevented the
    /// sampled kill: see `clamp_cannot_bind_at_the_sampled_pressure_instants`.
    #[test]
    fn measured_128_gib_host_is_clamped_well_below_its_core_count() {
        let jobs = jobs_for_host(18, 128 * GIB);
        assert_eq!(jobs, 9, "128 GiB / 18 cores must not run at Cargo's default width");
        assert!(jobs < 18, "the rule must clamp below cores on the host that produced the SIGKILL");
    }

    /// The honest limit of this change, pinned so nobody later reads the
    /// clamp as a fix for the `ay_arrays` kill.
    ///
    /// Measured over the 176 sampled instants: every instant above 60 GiB
    /// co-resident carried 3 to 5 live units, the co-resident maximum was
    /// 89.36 GiB at 4 live units, and the widest instant (20 live units)
    /// totalled 16.96 GiB. A cap of 9 is therefore inert at every pressure
    /// instant in that trace, and the pathological pair alone does not fit
    /// under any cap above 1.
    #[test]
    fn clamp_cannot_bind_at_the_sampled_pressure_instants() {
        const MAX_LIVE_UNITS_AT_PRESSURE: usize = 5;
        assert!(
            jobs_for_host(18, 128 * GIB) > MAX_LIVE_UNITS_AT_PRESSURE,
            "if this ever becomes false the clamp has started binding at the sampled failure, \
             and the doc comments claiming it does not must be rewritten"
        );
        // The pathological pair: 66.90 + 63.10 GiB co-resident.
        const TAIL_PAIR_BYTES: u64 = 130 * GIB;
        const {
            assert!(
                2 * PER_JOB_MEMORY_BUDGET_BYTES < TAIL_PAIR_BYTES,
                "the budget must not be mistaken for one that admits the tail pair"
            );
        };
        const {
            assert!(
                TAIL_PAIR_BYTES > 128 * GIB - HOST_MEMORY_RESERVE_BYTES,
                "the tail pair exceeds the measured host at any job count above 1"
            );
        };
    }

    /// A 24 GiB host gets one job. This row is NOT measured: nothing records a
    /// 24 GB host succeeding or failing at 4, the old rule's answer. What is
    /// recorded (in `run_quick` above) is that `hw.ncpu` on a 24 GB host
    /// "exhausted the VM compressor and panicked the machine". One job is what
    /// a 12 GiB budget plus a 10 GiB reserve yields there, and its cost is
    /// real: a fully serial check on that host, a 4x reduction.
    #[test]
    fn twenty_four_gib_host_admits_a_single_job() {
        assert_eq!(jobs_for_host(18, 24 * GIB), 1);
        assert_eq!(jobs_for_host(8, 24 * GIB), 1);
    }

    /// `trust_extra`'s workspace step measured 4 threads good and 14 fatal on
    /// a 48 GB host. The rule must land at or below the measured-good width,
    /// approaching it from below. 3 rather than 4 is a choice, not a
    /// measurement: it is what the budget yields, one job conservative.
    #[test]
    fn forty_eight_gib_host_stays_within_its_measured_good_width() {
        let jobs = jobs_for_host(12, 48 * GIB);
        assert_eq!(jobs, 3);
        assert!(jobs <= 4, "48 GB measured 4 threads good and 14 fatal");
    }

    /// Cores still bound the answer on a host with memory to spare, and the
    /// floor is one job however small the host is.
    #[test]
    fn job_count_is_bounded_by_cores_and_floored_at_one() {
        assert_eq!(jobs_for_host(2, 512 * GIB), 2, "cores must still clamp a large host");
        assert_eq!(jobs_for_host(18, 8 * GIB), 1, "a host below the reserve still gets one job");
        assert_eq!(jobs_for_host(18, 0), 1);
        assert_eq!(jobs_for_host(0, 128 * GIB), 1, "a zero core probe must not produce zero jobs");
    }

    /// The reserve is part of the rule, not decoration: budgeting against
    /// total memory instead of usable memory would hand out a tenth job on
    /// this host that the kernel's own wired plus compressed footprint
    /// (9.11 GiB measured at the start of the trace) has already spent.
    #[test]
    fn host_reserve_is_subtracted_before_the_budget_divides() {
        assert_eq!(HOST_MEMORY_RESERVE_BYTES, 10 * GIB);
        let with_reserve = jobs_for_host(64, 128 * GIB);
        let without_reserve = usize::try_from(128 * GIB / PER_JOB_MEMORY_BUDGET_BYTES).unwrap();
        assert_eq!(without_reserve, 10);
        assert_eq!(with_reserve, 9, "the reserve must cost exactly the jobs it pays for");
    }

    /// The budget must COVER the largest measured unit outside the
    /// pathological `ay_arrays` pair — 11.90 GiB, rank 30 of the 32 sampled
    /// unit peaks. Below that, `jobs * budget + reserve <= RAM` stops being a
    /// bound on anything, which is what was wrong with 5 GiB: two of the five
    /// non-trivial units exceeded it.
    ///
    /// This is one order statistic, not a percentile. The p95 of this sample
    /// is not 11.90 (it is 36.6 GiB linear / 66.2 GiB nearest-rank) and is not
    /// a usable number, because the sample is bimodal across the 11.90 ->
    /// 63.10 gap.
    #[test]
    fn per_job_budget_covers_every_non_pathological_measured_unit() {
        // 11.90 GiB, the largest of the 30 units outside the `ay_arrays` pair.
        const LARGEST_NON_PATHOLOGICAL_BYTES: u64 = 11_900 * GIB / 1_000;
        const {
            assert!(
                PER_JOB_MEMORY_BUDGET_BYTES >= LARGEST_NON_PATHOLOGICAL_BYTES,
                "the budget must cover the largest non-pathological measured unit"
            );
        };
        // 7.44 GiB, `ay_frontend`'s test unit: a budget that did not cover it
        // would be describing a fan-out width the host cannot actually run.
        const {
            assert!(PER_JOB_MEMORY_BUDGET_BYTES > 7_440 * GIB / 1_000);
        };
        const {
            assert!(
                PER_JOB_MEMORY_BUDGET_BYTES > 5 * GIB,
                "5 GiB failed to cover two of the five non-trivial measured units"
            );
        };
    }

    /// `build -> build.noindex` (docs/BUILD_AND_INSTALL.md, "Keeping Spotlight
    /// out of build/") is the one link the repository bootstrap binary may be
    /// reached through, spelled either way; any other `build` link is refused.
    #[cfg(unix)]
    #[test]
    fn repo_bootstrap_binary_admits_only_the_sanctioned_build_link() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let temp = tempfile::tempdir().expect("bootstrap fixture");
        let root = temp.path().canonicalize().expect("canonical fixture root");
        let executable = host_executable_name("bootstrap");
        let physical = root.join("build.noindex/bootstrap/debug").join(&executable);
        fs::create_dir_all(physical.parent().expect("bootstrap dir")).expect("create dir");
        fs::write(&physical, b"#!/bin/sh\nexit 0\n").expect("write bootstrap");
        fs::set_permissions(&physical, fs::Permissions::from_mode(0o755)).expect("chmod");
        symlink("build.noindex", root.join("build")).expect("link build");
        let lexical = root.join("build/bootstrap/debug").join(&executable);

        for spelling in [&lexical, &physical] {
            assert_eq!(
                validate_repo_bootstrap_binary(&root, spelling, "test")
                    .unwrap_or_else(|error| panic!("{}: {error:#}", spelling.display())),
                physical
            );
        }
        // Discovery reads `TRUST_UPSTREAM_RUST_BOOTSTRAP` first; exercise it only
        // when the test environment does not set one.
        if env::var_os("TRUST_UPSTREAM_RUST_BOOTSTRAP").is_none() {
            assert_eq!(rust_bootstrap_binary(&root).expect("bootstrap discovery"), physical);
        }

        // Any other `build` link is refused, in either spelling.
        fs::remove_file(root.join("build")).expect("remove build link");
        fs::rename(root.join("build.noindex"), root.join("elsewhere")).expect("move tree");
        symlink("elsewhere", root.join("build")).expect("unsanctioned build link");
        let error = validate_repo_bootstrap_binary(&root, &lexical, "test")
            .expect_err("an unsanctioned build link");
        assert!(format!("{error:#}").contains("must not traverse a symlink"), "{error:#}");
        let error = validate_repo_bootstrap_binary(
            &root,
            &root.join("elsewhere/bootstrap/debug").join(&executable),
            "test",
        )
        .expect_err("a tree outside build/ is not the repository bootstrap");
        assert!(format!("{error:#}").contains("must be build/bootstrap/"), "{error:#}");
    }
}
