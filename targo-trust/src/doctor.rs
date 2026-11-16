//! targo-trust doctor subcommand: environment, compiler, backend, solver,
//! and verifier-suite readiness reporting.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs;
use std::path::{Path, PathBuf};

use serde::Serialize;
use trust_verifier_api::{
    BundleSubject, EngineManifest, EvidenceStatus, ObligationKind, SourceLocation, SupportLevel,
    TrustContractBundle, TrustObligation, VerificationEngine, VerificationRunStatus,
    VerifierExecutionContext,
};

use crate::cli::SubcommandArgs;
use crate::config::{
    DEFAULT_CODEGEN_BACKEND, DEFAULT_TRUST_PROFILE, TrustConfig, TrustConfigSource,
    discover_manifest, resolve_trust_config,
};
use crate::pipeline::{
    LinkedTrustCargoSurfaceKind, LinkedTrustCargoSurfaceStatus, LinkedTrustSurfaceToolStatus,
    LinkedTrustSurfaceToolStatusKind, LinkedTrustToolchainStatusKind, NativeRustcDiscoverySource,
    detect_linked_trust_cargo_surface, detect_linked_trust_toolchain,
    detect_native_rustc_capabilities, discover_native_rustc_checked,
};
use crate::project_root::resolve_project_root;
use crate::solver_detect;

#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum DoctorBackendSource {
    Cli,
    Config,
    Default,
}

impl DoctorBackendSource {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Cli => "CLI override",
            Self::Config => "project configuration",
            Self::Default => "default",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct DoctorBackendStatus {
    pub(crate) selected: String,
    pub(crate) source: DoctorBackendSource,
}

#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum DoctorConfigSourceKind {
    /// The `[trust]` table of the project manifest.
    Manifest,
    /// The deprecated stand-alone `trust.toml`.
    LegacyFile,
    Defaults,
    Invalid,
    Unreadable,
}

impl DoctorConfigSourceKind {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Manifest => "manifest [trust] table",
            Self::LegacyFile => "trust.toml (deprecated)",
            Self::Defaults => "defaults",
            Self::Invalid => "defaults (invalid configuration)",
            Self::Unreadable => "defaults (unreadable configuration)",
        }
    }

    pub(crate) fn has_error(self) -> bool {
        matches!(self, Self::Invalid | Self::Unreadable)
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct DoctorConfigStatus {
    pub(crate) source: DoctorConfigSourceKind,
    pub(crate) path: PathBuf,
    pub(crate) detail: Option<String>,
    pub(crate) enabled: bool,
    pub(crate) level: String,
    /// The one effort count's scale `k` (`[trust] effort`).
    pub(crate) effort: u64,
    /// The backstop, per mille of the reference clocks (`[trust] backstop`).
    pub(crate) backstop: u32,
    /// The budget profile header line: the id, its bounds and the derived
    /// clocks.
    pub(crate) budget_profile: String,
    pub(crate) configured_codegen_backend: Option<String>,
    pub(crate) configured_hardened: Option<bool>,
    pub(crate) configured_trust_profile: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct DoctorCompilerStatus {
    pub(crate) path: Option<PathBuf>,
    pub(crate) discovery_source: Option<NativeRustcDiscoverySource>,
    pub(crate) discovery_error: Option<String>,
    pub(crate) linked_toolchain_status: LinkedTrustToolchainStatusKind,
    pub(crate) linked_toolchain_path: Option<PathBuf>,
    pub(crate) linked_toolchain_detail: Option<String>,
    pub(crate) daily_driver: DoctorDailyDriverStatus,
    pub(crate) trust_verify: Option<bool>,
    pub(crate) json_transport: Option<bool>,
    pub(crate) check_report_mode: DoctorCheckReportMode,
    /// The selected compiler's build commit and its age (`trustc -vV`). A
    /// delivered seal does not move while main does, so its age is how far
    /// this machine's verifier lags what has landed.
    pub(crate) toolchain_age: Option<DoctorToolchainAge>,
}

/// Past this age `targo trust doctor` warns that the toolchain is stale. It
/// does not change readiness: an old seal still verifies what it verifies.
pub(crate) const TOOLCHAIN_STALE_AFTER_DAYS: i64 = 42;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct DoctorToolchainAge {
    pub(crate) commit_hash: Option<String>,
    pub(crate) commit_date: String,
    /// Whole days from `commit_date` to today (UTC); `None` when the clock is
    /// before the epoch or the date does not parse.
    pub(crate) age_days: Option<i64>,
    pub(crate) stale: bool,
}

/// Read `commit-hash:` and `commit-date:` from `trustc -vV` output.
pub(crate) fn parse_toolchain_age(
    verbose_version: &str,
    today_days: Option<i64>,
) -> Option<DoctorToolchainAge> {
    let field = |key: &str| {
        verbose_version.lines().find_map(|line| {
            line.strip_prefix(key)
                .map(str::trim)
                .filter(|value| !value.is_empty() && *value != "unknown")
                .map(str::to_string)
        })
    };
    let commit_date = field("commit-date:")?;
    let age_days = days_from_civil_date(&commit_date)
        .zip(today_days)
        .map(|(built, today)| today - built)
        .filter(|age| *age >= 0);
    Some(DoctorToolchainAge {
        commit_hash: field("commit-hash:"),
        commit_date,
        age_days,
        stale: age_days.is_some_and(|age| age > TOOLCHAIN_STALE_AFTER_DAYS),
    })
}

/// Days since 1970-01-01 of a `YYYY-MM-DD` date (proleptic Gregorian).
fn days_from_civil_date(date: &str) -> Option<i64> {
    let mut parts = date.splitn(3, '-');
    let year: i64 = parts.next()?.parse().ok()?;
    let month: i64 = parts.next()?.parse().ok()?;
    let day: i64 = parts.next()?.parse().ok()?;
    if !(1..=12).contains(&month) || !(1..=31).contains(&day) {
        return None;
    }
    let year = if month <= 2 { year - 1 } else { year };
    let era = year.div_euclid(400);
    let year_of_era = year - era * 400;
    let month_index = (month + 9) % 12;
    let day_of_year = (153 * month_index + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    Some(era * 146_097 + day_of_era - 719_468)
}

fn today_days_utc() -> Option<i64> {
    let seconds =
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).ok()?.as_secs();
    i64::try_from(seconds / 86_400).ok()
}

/// The age probe's production bound: the selected compiler's `-vV` host probe
/// (`exact_rustc_host_triple_budget`, `pipeline/run.rs`) uses the same.
const TOOLCHAIN_AGE_PROBE_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(10);

fn detect_toolchain_age(rustc: &Path) -> Option<DoctorToolchainAge> {
    detect_toolchain_age_within(
        rustc,
        crate::bounded_process::resolve_probe_deadline(TOOLCHAIN_AGE_PROBE_TIMEOUT),
    )
}

/// `rustc -vV` as the host probe runs it: a cleared environment, a deadline and a
/// 64 KiB output cap. A compiler that hangs (an exec stuck at `_dyld_start`, say),
/// fails or floods gives no age, and doctor goes on to its other checks.
fn detect_toolchain_age_within(
    rustc: &Path,
    timeout: std::time::Duration,
) -> Option<DoctorToolchainAge> {
    let mut command = std::process::Command::new(rustc);
    command.arg("-vV").env_clear();
    let output = crate::bounded_process::output_with_exact_deadline(
        &mut command,
        &format!("selected compiler {} -vV age probe", rustc.display()),
        64 * 1024,
        timeout,
    )
    .ok()?;
    if !output.status.success() {
        return None;
    }
    parse_toolchain_age(&String::from_utf8_lossy(&output.stdout), today_days_utc())
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct DoctorDailyDriverStatus {
    pub(crate) surface_kind: LinkedTrustCargoSurfaceKind,
    pub(crate) ready: bool,
    pub(crate) detail: Option<String>,
    pub(crate) linked_targo_path: Option<PathBuf>,
    pub(crate) linked_targo_trust_path: Option<PathBuf>,
    pub(crate) required_tools: Vec<LinkedTrustSurfaceToolStatus>,
    pub(crate) optional_tools: Vec<LinkedTrustSurfaceToolStatus>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum DoctorCheckReportMode {
    NativeCompiler,
    NativeRequired,
}

impl DoctorCheckReportMode {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::NativeCompiler => "native compiler",
            Self::NativeRequired => "native compiler required",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct DoctorSolverStatus {
    pub(crate) requested: Option<String>,
    pub(crate) external_available: usize,
    pub(crate) native_suite_available: usize,
    pub(crate) available: usize,
    pub(crate) routed_available: usize,
    pub(crate) total: usize,
    pub(crate) solvers: Vec<solver_detect::SolverInfo>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct DoctorVerifierSuiteStatus {
    pub(crate) name: &'static str,
    pub(crate) adapter_compiled: bool,
    /// Truthful capability signal: the compiled in-process adapter declares it can
    /// handle ≥1 obligation kind (its manifest has a Supported capability). This is
    /// distinct from `in_process_available`, which reflects the doctor SMOKE probe:
    /// a canonical request (the bundle carries the one obligation it asks about;
    /// for trust-mc under `trust-mc-in-process` it is a real typed-CHC bundle the
    /// native solver genuinely solves) dispatched through the public validated
    /// `verify_with_context`. That public boundary deliberately never mints
    /// `Proved` for native CHC/PDR candidates without a deliverable live receipt,
    /// so the smoke stays honestly non-available today — its `detail` says why. A
    /// consumer asking "is this batteries-on engine actually wired/capable?"
    /// should read THIS, not the smoke result; real proof-grade behavior is
    /// exercised by compilation (see the falsification gate).
    pub(crate) capability_available: bool,
    pub(crate) in_process_available: bool,
    pub(crate) in_process_status: &'static str,
    pub(crate) in_process_detail: Option<String>,
    pub(crate) in_process_feature: &'static str,
    pub(crate) manifest: EngineManifest,
    pub(crate) external_executable_available: bool,
    pub(crate) external_executable_path: Option<PathBuf>,
    pub(crate) external_executable_version: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct DoctorReport {
    pub(crate) ready: bool,
    pub(crate) status: &'static str,
    pub(crate) compiler: DoctorCompilerStatus,
    pub(crate) backend: DoctorBackendStatus,
    pub(crate) config: DoctorConfigStatus,
    pub(crate) solvers: DoctorSolverStatus,
    pub(crate) verifier_suites: Vec<DoctorVerifierSuiteStatus>,
}

pub(crate) fn backend_status(
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
) -> DoctorBackendStatus {
    if let Some(backend) = sub_args.backend.as_deref() {
        DoctorBackendStatus { selected: backend.to_string(), source: DoctorBackendSource::Cli }
    } else if let Some(backend) = config.codegen_backend.as_deref() {
        DoctorBackendStatus { selected: backend.to_string(), source: DoctorBackendSource::Config }
    } else {
        DoctorBackendStatus {
            selected: DEFAULT_CODEGEN_BACKEND.to_string(),
            source: DoctorBackendSource::Default,
        }
    }
}

pub(crate) fn apply_configured_trust_profile(sub_args: &mut SubcommandArgs, config: &TrustConfig) {
    match sub_args.hardened_override {
        Some(false) => {
            sub_args.hardened = false;
            sub_args.trust_profile = None;
            return;
        }
        Some(true) => {
            sub_args.hardened = true;
            if sub_args.trust_profile.is_none() {
                sub_args.trust_profile = Some(DEFAULT_TRUST_PROFILE.to_string());
            }
            return;
        }
        None => {}
    }

    if config.hardened == Some(false) {
        sub_args.hardened = false;
        sub_args.trust_profile = None;
        return;
    }

    sub_args.hardened = true;
    sub_args.trust_profile = Some(
        config
            .trust_profile
            .as_deref()
            .filter(|profile| !profile.trim().is_empty())
            .unwrap_or(DEFAULT_TRUST_PROFILE)
            .to_string(),
    );
}

/// Report the effective policy and where it came from.
///
/// The doctor is a diagnostic, not a front door: an unusable configuration is
/// described rather than fatal, so a user can run `doctor` precisely to find
/// out why `check` refuses to start.
pub(crate) fn load_doctor_config(crate_root: &Path) -> (TrustConfig, DoctorConfigStatus) {
    fn status_for(
        source: DoctorConfigSourceKind,
        path: PathBuf,
        detail: Option<String>,
        config: &TrustConfig,
    ) -> DoctorConfigStatus {
        DoctorConfigStatus {
            source,
            path,
            detail,
            enabled: config.enabled,
            level: config.level.clone(),
            effort: config.effort.conflicts_per_node,
            backstop: config.backstop.per_mille,
            budget_profile: crate::determinism_report::budget_profile(config).header_line(),
            configured_codegen_backend: config.codegen_backend.clone(),
            configured_hardened: config.hardened,
            configured_trust_profile: config.trust_profile.clone(),
        }
    }

    match resolve_trust_config(crate_root, None) {
        Ok(resolved) => {
            let mut detail = resolved.member_manifest.as_ref().map(|member| {
                format!(
                    "{} is a workspace member; its policy is the workspace root's",
                    member.display()
                )
            });
            let (kind, path) = match resolved.source {
                TrustConfigSource::Manifest(path) => (DoctorConfigSourceKind::Manifest, path),
                TrustConfigSource::LegacyFile(path) => {
                    detail = Some(crate::config::legacy_config_deprecation_notice());
                    (DoctorConfigSourceKind::LegacyFile, path)
                }
                TrustConfigSource::Defaults => {
                    let path =
                        discover_manifest(crate_root).unwrap_or_else(|| crate_root.to_path_buf());
                    detail = Some("no [trust] table declared".to_string());
                    (DoctorConfigSourceKind::Defaults, path)
                }
            };
            let status = status_for(kind, path, detail, &resolved.config);
            (resolved.config, status)
        }
        Err(error) => {
            let kind = match error.action {
                "inspect" | "read" => DoctorConfigSourceKind::Unreadable,
                _ => DoctorConfigSourceKind::Invalid,
            };
            let config = TrustConfig::default();
            let status = status_for(kind, error.path.clone(), Some(error.detail.clone()), &config);
            (config, status)
        }
    }
}

pub(crate) fn describe_capability(supported: Option<bool>) -> &'static str {
    match supported {
        Some(true) => "supported",
        Some(false) => "not supported",
        None => "unknown",
    }
}

fn describe_surface_tool_status(status: LinkedTrustSurfaceToolStatusKind) -> &'static str {
    match status {
        LinkedTrustSurfaceToolStatusKind::Present => "present",
        LinkedTrustSurfaceToolStatusKind::Missing => "missing",
        LinkedTrustSurfaceToolStatusKind::OptionalMissing => "optional-missing",
        LinkedTrustSurfaceToolStatusKind::AmbientFallback => "ambient-fallback",
    }
}

fn describe_linked_toolchain(
    status: LinkedTrustToolchainStatusKind,
    path: Option<&Path>,
    detail: Option<&str>,
) -> String {
    match status {
        LinkedTrustToolchainStatusKind::Visible => path
            .map(|path| format!("visible at {}", path.display()))
            .unwrap_or_else(|| "visible".to_string()),
        LinkedTrustToolchainStatusKind::Missing => detail
            .map(|detail| format!("not visible ({detail})"))
            .unwrap_or_else(|| "not visible".to_string()),
    }
}

fn doctor_check_report_mode(
    compiler_path: Option<&Path>,
    trust_verify: Option<bool>,
) -> DoctorCheckReportMode {
    if compiler_path.is_some() && trust_verify == Some(true) {
        DoctorCheckReportMode::NativeCompiler
    } else {
        DoctorCheckReportMode::NativeRequired
    }
}

fn canonicalize_or_self(path: &Path) -> PathBuf {
    fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

fn canonical_parent(path: &Path) -> Option<PathBuf> {
    path.parent().map(canonicalize_or_self)
}

fn build_doctor_daily_driver_status(
    compiler_path: Option<&Path>,
    linked_toolchain_path: Option<&Path>,
    surface: &LinkedTrustCargoSurfaceStatus,
) -> DoctorDailyDriverStatus {
    let mut status = DoctorDailyDriverStatus {
        surface_kind: surface.kind,
        ready: surface.ready,
        detail: surface.detail.clone(),
        linked_targo_path: surface.targo.clone(),
        linked_targo_trust_path: surface.targo_trust.clone(),
        required_tools: surface.required_tools.clone(),
        optional_tools: surface.optional_tools.clone(),
    };

    if !status.ready {
        return status;
    }

    let Some(compiler_path) = compiler_path else {
        status.ready = false;
        status.detail = Some(
            "Trust package surfaces are visible, but no native Trust compiler was discovered"
                .to_string(),
        );
        return status;
    };
    let Some(linked_toolchain_path) = linked_toolchain_path else {
        status.ready = false;
        status.detail = Some(
            "Trust package surfaces are visible, but the selected compiler path is missing"
                .to_string(),
        );
        return status;
    };

    let compiler_bin = canonical_parent(compiler_path);
    let linked_bin = canonical_parent(linked_toolchain_path);
    if compiler_bin != linked_bin {
        status.ready = false;
        status.surface_kind = LinkedTrustCargoSurfaceKind::AmbientFallback;
        status.detail = Some(format!(
            "Trust package surface resolves to {}, but targo-trust is using compiler {}; select one Trust root before collecting daily-driver evidence",
            linked_toolchain_path.display(),
            compiler_path.display()
        ));
    }

    status
}

/// The terminal line for the compiler's build commit and age, with the stale
/// warning past [`TOOLCHAIN_STALE_AFTER_DAYS`].
pub(crate) fn describe_toolchain_age(age: Option<&DoctorToolchainAge>) -> Option<String> {
    let age = age?;
    let commit = age.commit_hash.as_deref().map(|hash| {
        let short = hash.get(..10).unwrap_or(hash);
        format!("{short}, ")
    });
    let commit = commit.unwrap_or_default();
    let mut line = match age.age_days {
        Some(days) => format!("built from: {commit}{} ({days} days ago)", age.commit_date),
        None => format!("built from: {commit}{}", age.commit_date),
    };
    if age.stale {
        line.push_str(&format!(
            "\n  warning: this toolchain is more than {TOOLCHAIN_STALE_AFTER_DAYS} days old; \
             work landed on Trust's main since then does not run here until a newer Trust \
             toolchain is installed"
        ));
    }
    Some(line)
}

pub(crate) fn describe_config_source(config: &DoctorConfigStatus) -> String {
    match config.source {
        DoctorConfigSourceKind::Manifest | DoctorConfigSourceKind::LegacyFile => {
            let described = format!("{} ({})", config.source.label(), config.path.display());
            match config.detail.as_deref() {
                Some(detail) => format!("{described}: {detail}"),
                None => described,
            }
        }
        DoctorConfigSourceKind::Defaults
        | DoctorConfigSourceKind::Invalid
        | DoctorConfigSourceKind::Unreadable => {
            if let Some(detail) = config.detail.as_deref() {
                format!("{} at {}: {detail}", config.source.label(), config.path.display())
            } else {
                format!("{} at {}", config.source.label(), config.path.display())
            }
        }
    }
}

fn doctor_next_steps(report: &DoctorReport) -> Vec<String> {
    let mut steps = Vec::new();

    if report.compiler.path.is_none() {
        if let Some(error) = report.compiler.discovery_error.as_deref() {
            steps.push(format!("Fix compiler discovery: {error}."));
        }
        steps.push(
            "Make canonical `trustc` discoverable through a sibling Trust install or a repo-local stage2/stage3 build."
                .to_string(),
        );
        match report.compiler.linked_toolchain_status {
            LinkedTrustToolchainStatusKind::Missing => steps.push(
                "Install or select a Trust root with canonical trustc, targo, targo-trust, trustd, trustdoc, trustfmt, targo-fmt, tippy, targo-tippy, tippy-driver, and trust-analyzer."
                    .to_string(),
            ),
            LinkedTrustToolchainStatusKind::Visible => {}
        }
    } else if report.compiler.trust_verify == Some(false) {
        steps.push(
            "Use a Trust compiler whose default compilation path emits Trust verification output."
                .to_string(),
        );
    }

    if !report.compiler.daily_driver.ready {
        if let Some(detail) = report.compiler.daily_driver.detail.as_deref() {
            steps.push(format!("Fix linked daily-driver toolchain surface: {detail}."));
        }
        steps.push(
            "Select one Trust root and ensure every required Trust-owned daily-driver entrypoint resolves from that exact toolchain."
                .to_string(),
        );
    }

    if report.compiler.check_report_mode == DoctorCheckReportMode::NativeRequired {
        steps.push(
            "`targo trust check` and `targo trust report` require a native Trust compiler by default; use `--standalone` only when you explicitly want source-only analysis."
                .to_string(),
        );
    }

    if let Some(requested) = report.solvers.requested.as_deref() {
        if !is_source_solver_routed(requested) {
            steps.push(format!(
                "Requested solver `{requested}` is detectable but not wired into compiler-backed source verification; use `ay` or omit `--solver`."
            ));
        }
    }

    let missing_native_routes = missing_default_native_source_routes(&report.verifier_suites);
    if !missing_native_routes.is_empty() {
        steps.push(format!(
            "Build/link Targo Trust with every default typed native source route enabled; missing capable route(s): {}.",
            missing_native_routes.join(", ")
        ));
    }

    if report.solvers.routed_available == 0 {
        steps.push(
            "No solver in this report is routed for compiler-backed source verification, which runs the `ay` linked into the Trust compiler: omit `--solver`, or pass `--solver ay`."
                .to_string(),
        );
    }
    if report.config.source.has_error() {
        steps.push(format!(
            "Fix or remove {} so targo-trust can load configuration cleanly.",
            report.config.path.display()
        ));
    }

    steps
}

pub(crate) fn is_source_solver_routed(name: &str) -> bool {
    name == COMPILER_LINKED_SOURCE_SOLVER
}

/// Plan P4 / T4.1: the source solver the Trust compiler links. Compiler-backed
/// source verification routes through it whether or not an external `ay` is
/// installed; an external `ay` binary is used only by `verify-binary`.
pub(crate) const COMPILER_LINKED_SOURCE_SOLVER: &str = "ay";

/// The routing column of a solver row in `doctor` and `solvers`.
fn source_routing_label(
    solver: &solver_detect::SolverInfo,
    verifier_suites: &[DoctorVerifierSuiteStatus],
) -> &'static str {
    if is_source_solver_routed(&solver.name) {
        "source-routed: linked into trustc"
    } else if doctor_solver_has_native_source_route(&solver.name, verifier_suites) {
        "in-process source-routed"
    } else if solver.available {
        "detected-only"
    } else {
        "not source-routed"
    }
}

/// A solver row's probe error. For the compiler-linked solver it concerns only
/// the external binary `verify-binary` runs.
fn print_solver_diagnostic(solver: &solver_detect::SolverInfo) {
    let Some(diagnostic) = &solver.diagnostic else { return };
    let diagnostic = solver_detect::terminal_safe(diagnostic);
    if is_source_solver_routed(&solver.name) {
        eprintln!("             external binary for verify-binary: {diagnostic}");
    } else {
        eprintln!("             ERROR: {diagnostic}");
    }
}

/// Where a solver row's binary is. For the compiler-linked solver the path is
/// the external binary `verify-binary` runs, not what source verification uses.
fn solver_path_suffix(solver: &solver_detect::SolverInfo) -> String {
    let Some(path) = solver.path.as_deref() else { return String::new() };
    let path = solver_detect::terminal_safe(&path.display().to_string());
    if is_source_solver_routed(&solver.name) {
        format!(" (external binary for verify-binary at {path})")
    } else {
        format!(" at {path}")
    }
}

pub(crate) fn supported_source_solver_names() -> &'static str {
    "ay"
}

const DEFAULT_NATIVE_SOURCE_ROUTES: &[&str] = &["trust-mc", "trust-vc"];

fn missing_default_native_source_routes(
    verifier_suites: &[DoctorVerifierSuiteStatus],
) -> Vec<&'static str> {
    DEFAULT_NATIVE_SOURCE_ROUTES
        .iter()
        .copied()
        .filter(|required_name| {
            !verifier_suites.iter().any(|suite| {
                suite.name == *required_name && doctor_suite_has_native_source_route(suite)
            })
        })
        .collect()
}

fn doctor_is_ready(
    compiler: &DoctorCompilerStatus,
    config: &DoctorConfigStatus,
    routed_available: usize,
    verifier_suites: &[DoctorVerifierSuiteStatus],
) -> bool {
    compiler.trust_verify == Some(true)
        && compiler.daily_driver.ready
        && routed_available > 0
        && missing_default_native_source_routes(verifier_suites).is_empty()
        && !config.source.has_error()
}

pub(crate) fn build_doctor_report(sub_args: &SubcommandArgs) -> DoctorReport {
    let crate_root = resolve_project_root(sub_args).root;
    let (config, config_status) = load_doctor_config(&crate_root);
    let backend = backend_status(sub_args, &config);

    let linked_toolchain = detect_linked_trust_toolchain();
    let linked_cargo_surface = detect_linked_trust_cargo_surface(&linked_toolchain);
    let compiler_discovery = discover_native_rustc_checked();
    let discovery_error = None;
    let capabilities = compiler_discovery
        .as_ref()
        .map(|discovery| detect_native_rustc_capabilities(&discovery.rustc));

    let compiler = DoctorCompilerStatus {
        path: compiler_discovery.as_ref().map(|discovery| discovery.rustc.clone()),
        discovery_source: compiler_discovery.as_ref().map(|discovery| discovery.source),
        discovery_error,
        linked_toolchain_status: linked_toolchain.status,
        linked_toolchain_path: linked_toolchain.rustc.clone(),
        linked_toolchain_detail: linked_toolchain.detail.clone(),
        daily_driver: build_doctor_daily_driver_status(
            compiler_discovery.as_ref().map(|discovery| discovery.rustc.as_path()),
            linked_toolchain.rustc.as_deref(),
            &linked_cargo_surface,
        ),
        trust_verify: capabilities.map(|caps| caps.trust_verify),
        json_transport: capabilities.map(|caps| caps.json_transport),
        check_report_mode: doctor_check_report_mode(
            compiler_discovery.as_ref().map(|discovery| discovery.rustc.as_path()),
            capabilities.map(|caps| caps.trust_verify),
        ),
        toolchain_age: compiler_discovery
            .as_ref()
            .and_then(|discovery| detect_toolchain_age(&discovery.rustc)),
    };

    let verifier_suites = verifier_suite_statuses();
    let mut solvers = if let Some(ref name) = sub_args.solver {
        vec![solver_detect::detect_solver(name)]
    } else {
        solver_detect::detect_all_solvers()
    };
    let external_available = solvers.iter().filter(|solver| solver.available).count();
    mark_doctor_in_process_solver_routes(&mut solvers, &verifier_suites);
    let native_suite_available =
        verifier_suites.iter().filter(|suite| doctor_suite_has_native_source_route(suite)).count();
    let available = solvers.iter().filter(|solver| solver.available).count();
    let routed_available = solvers
        .iter()
        .filter(|solver| {
            solver.available
                && (is_source_solver_routed(&solver.name)
                    || doctor_solver_has_native_source_route(&solver.name, &verifier_suites))
        })
        .count();

    let ready = doctor_is_ready(&compiler, &config_status, routed_available, &verifier_suites);

    DoctorReport {
        ready,
        status: if ready { "ready" } else { "needs_attention" },
        compiler,
        backend,
        config: config_status,
        solvers: DoctorSolverStatus {
            requested: sub_args.solver.clone(),
            external_available,
            native_suite_available,
            available,
            routed_available,
            total: solvers.len(),
            solvers,
        },
        verifier_suites,
    }
}

pub(crate) fn mark_doctor_in_process_solver_routes(
    solvers: &mut [solver_detect::SolverInfo],
    verifier_suites: &[DoctorVerifierSuiteStatus],
) {
    for solver in solvers {
        if solver.available {
            continue;
        }
        if is_source_solver_routed(&solver.name) {
            // Plan P4 / T4.1: no external binary is needed for source
            // verification; the probe's result speaks only for verify-binary.
            solver.available = true;
            solver.version = Some("linked into trustc".to_string());
            continue;
        }
        if let Some(suite) = doctor_native_suite_for_solver(&solver.name, verifier_suites) {
            solver.available = true;
            solver.version = Some(format!("in-process {}", suite.manifest.version));
        }
    }
}

pub(crate) fn doctor_solver_has_native_source_route(
    solver_name: &str,
    verifier_suites: &[DoctorVerifierSuiteStatus],
) -> bool {
    doctor_native_suite_for_solver(solver_name, verifier_suites).is_some()
}

fn doctor_native_suite_for_solver<'a>(
    solver_name: &str,
    verifier_suites: &'a [DoctorVerifierSuiteStatus],
) -> Option<&'a DoctorVerifierSuiteStatus> {
    verifier_suites
        .iter()
        .find(|suite| suite.name == solver_name && doctor_suite_has_native_source_route(suite))
}

pub(crate) fn doctor_suite_has_native_source_route(suite: &DoctorVerifierSuiteStatus) -> bool {
    suite.adapter_compiled
        && matches!(suite.name, "trust-mc" | "trust-vc")
        && suite.manifest.capabilities.iter().any(|capability| {
            matches!(capability.support, SupportLevel::Supported | SupportLevel::Preferred)
        })
}

pub(crate) fn verifier_suite_statuses() -> Vec<DoctorVerifierSuiteStatus> {
    let trust_mc = trust_bmc::TrustMcVerifierApiAdapter::default();
    let trust_wp = trust_wp::TrustWpVerificationEngine::default();
    let trust_vc = trust_vc_bridge::TrustVcVerificationEngine::default();

    vec![
        verifier_suite_status(
            "trust-mc",
            "trust-mc-in-process",
            ObligationKind::Assertion,
            &trust_mc,
        ),
        verifier_suite_status(
            "trust-wp",
            "trust-wp-in-process",
            ObligationKind::Precondition,
            &trust_wp,
        ),
        verifier_suite_status(
            "trust-vc",
            "trust-vc-in-process",
            ObligationKind::MemorySafety,
            &trust_vc,
        ),
    ]
}

fn verifier_suite_status(
    name: &'static str,
    in_process_feature: &'static str,
    smoke_obligation_kind: ObligationKind,
    engine: &dyn VerificationEngine,
) -> DoctorVerifierSuiteStatus {
    let manifest = engine.manifest().clone();
    let external = solver_detect::detect_solver(name);
    let in_process = verifier_engine_smoke_probe(name, smoke_obligation_kind, engine);
    // Honest "is this batteries-on engine actually WIRED/capable?" signal: at least
    // one obligation kind is `Supported` (or `Preferred`). Deliberately EXCLUDES
    // `Experimental` (which means "owns the lane but the proof path is not wired" —
    // e.g. trust-vc's "native ... proof adapter is not wired") and `Unsupported`.
    // This is stricter than `SupportLevel::is_supported()` (which is `!Unsupported`,
    // so it counts Experimental) precisely so an unwired adapter reports `false`.
    let capability_available = manifest.capabilities.iter().any(|capability| {
        matches!(capability.support, SupportLevel::Supported | SupportLevel::Preferred)
    });
    DoctorVerifierSuiteStatus {
        name,
        adapter_compiled: true,
        capability_available,
        in_process_available: in_process.available,
        in_process_status: in_process.status,
        in_process_detail: in_process.detail,
        in_process_feature,
        manifest,
        external_executable_available: external.available,
        external_executable_path: external.path,
        external_executable_version: external.version,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct VerifierEngineSmokeProbe {
    available: bool,
    status: &'static str,
    detail: Option<String>,
}

/// Build the smoke-probe request for one verifier suite.
///
/// The request must be CANONICAL: the hardened `verify_with_context` wrapper
/// fail-closes when a requested obligation is missing from the bundle's own
/// obligation inventory — as it must — so the bundle carries the one
/// obligation it asks about. (Empty publication metadata is fine: nothing on
/// the probe path requires publication hashes.)
///
/// For trust-mc, when the in-process native adapter is compiled
/// (`trust-mc-in-process`), the probe uses trust-bmc's canonical
/// one-obligation typed-CHC doctor bundle so the smoke exercises the real
/// native typed-CHC lane end-to-end instead of a payload-less synthetic
/// obligation. The constructor only BUILDS the request; verification still
/// goes through the public validated `verify_with_context` below.
fn doctor_smoke_probe_request(
    suite_name: &str,
    run_id: &str,
    obligation_kind: ObligationKind,
) -> (TrustContractBundle, TrustObligation) {
    #[cfg(feature = "trust-mc-in-process")]
    if suite_name == "trust-mc" {
        return trust_bmc::doctor_smoke_bundle();
    }

    let obligation = TrustObligation {
        obligation_id: format!("{run_id}-obligation"),
        kind: obligation_kind,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "targo-trust doctor in-process verifier API smoke".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    };
    let mut bundle = TrustContractBundle::empty(
        format!("{run_id}-bundle"),
        BundleSubject::Artifact { name: suite_name.to_string(), kind: "doctor-smoke".to_string() },
    );
    bundle.obligations = vec![obligation.clone()];
    (bundle, obligation)
}

fn verifier_engine_smoke_probe(
    suite_name: &str,
    obligation_kind: ObligationKind,
    engine: &dyn VerificationEngine,
) -> VerifierEngineSmokeProbe {
    let run_id = format!("targo-trust-doctor-{suite_name}-smoke");
    let (bundle, obligation) = doctor_smoke_probe_request(suite_name, &run_id, obligation_kind);

    let support = engine.supports(&obligation);
    if !support.is_supported() {
        return VerifierEngineSmokeProbe {
            available: false,
            status: "unsupported",
            detail: Some(describe_support_level(&support)),
        };
    }

    let context = VerifierExecutionContext::new(run_id.clone());
    let result = engine.verify_with_context(&bundle, std::slice::from_ref(&obligation), &context);
    let manifest = engine.manifest();

    let structurally_valid = result.run_id == run_id
        && result.bundle_id == bundle.bundle_id
        && result.engine.name == manifest.name
        && result.engine.api_version == manifest.api_version
        && result.context.run_id == run_id
        && result.status != VerificationRunStatus::Empty
        && result.summary.requested_obligations == 1
        && result.summary.evidence_count == 1
        && result.requested_obligations.as_slice() == std::slice::from_ref(&obligation)
        && result.evidence.len() == 1
        && result.evidence[0].obligation_id == obligation.obligation_id
        && result.evidence[0].engine.name == manifest.name;

    if !structurally_valid {
        return VerifierEngineSmokeProbe {
            available: false,
            status: "unavailable",
            detail: Some(
                "in-process verifier smoke did not return a valid one-obligation run envelope"
                    .to_string(),
            ),
        };
    }

    let evidence = &result.evidence[0];
    if evidence.status == EvidenceStatus::Unsupported {
        return VerifierEngineSmokeProbe {
            available: false,
            status: "unsupported",
            detail: evidence
                .diagnostics
                .first()
                .cloned()
                .or_else(|| Some("in-process verifier returned Unsupported evidence".to_string())),
        };
    }
    if evidence.status != EvidenceStatus::Proved {
        // v7/D3: a refusal must carry the fix — surface the engine's own
        // summary (its LAST diagnostic) so e.g. a solved-but-non-definitive
        // native candidate explains itself instead of hiding behind a bare
        // status word.
        let mut detail = format!(
            "in-process verifier returned {:?} evidence for smoke obligation",
            evidence.status
        );
        if let Some(reason) = evidence.diagnostics.last() {
            detail.push_str(": ");
            detail.push_str(reason);
        }
        return VerifierEngineSmokeProbe {
            available: false,
            status: "unavailable",
            detail: Some(detail),
        };
    }
    if !doctor_suite_evidence_has_native_artifacts(suite_name, evidence) {
        return VerifierEngineSmokeProbe {
            available: false,
            status: "unavailable",
            detail: Some(
                "in-process verifier smoke proof lacked suite-native proof artifacts".to_string(),
            ),
        };
    }

    VerifierEngineSmokeProbe {
        available: true,
        status: "available",
        detail: Some("proof-grade in-process verifier smoke evidence accepted".to_string()),
    }
}

fn describe_support_level(support: &SupportLevel) -> String {
    match support {
        SupportLevel::Supported => "supported".to_string(),
        SupportLevel::Preferred => "preferred".to_string(),
        SupportLevel::Experimental { reason } => format!("experimental: {reason}"),
        SupportLevel::Unsupported { reason } => format!("unsupported: {reason}"),
        _ => "unrecognized support level".to_string(),
    }
}

fn doctor_suite_evidence_has_native_artifacts(
    suite_name: &str,
    evidence: &trust_verifier_api::ObligationEvidence,
) -> bool {
    if !evidence.satisfies_proof_artifact_policy() {
        return false;
    }
    let has = |kind| evidence.artifacts.iter().any(|artifact| artifact.kind == kind);
    match suite_name {
        "trust-mc" => {
            has(trust_verifier_api::EvidenceArtifactKind::SolverTranscript)
                && has(trust_verifier_api::EvidenceArtifactKind::ReplayLog)
                && has(trust_verifier_api::EvidenceArtifactKind::ProofCheckReport)
        }
        "trust-wp" => {
            has(trust_verifier_api::EvidenceArtifactKind::SolverTranscript)
                && has(trust_verifier_api::EvidenceArtifactKind::ProofCheckReport)
        }
        "trust-vc" => has(trust_verifier_api::EvidenceArtifactKind::ProofCertificate),
        _ => true,
    }
}

pub(crate) fn print_doctor_terminal(report: &DoctorReport) {
    eprintln!();
    eprintln!("=== Trust Doctor ===");
    eprintln!();
    eprintln!("Status: {}", if report.ready { "READY" } else { "NEEDS ATTENTION" });
    eprintln!();
    eprintln!("Compiler:");
    match report.compiler.path.as_deref() {
        Some(path) => eprintln!("  compiler: {}", path.display()),
        None => eprintln!("  compiler: not found"),
    }
    match report.compiler.discovery_source {
        Some(source) => eprintln!("  discovery: {}", source.label()),
        None => eprintln!("  discovery: unresolved"),
    }
    if let Some(line) = describe_toolchain_age(report.compiler.toolchain_age.as_ref()) {
        eprintln!("  {line}");
    }
    eprintln!(
        "  Trust toolchain surface: {}",
        describe_linked_toolchain(
            report.compiler.linked_toolchain_status,
            report.compiler.linked_toolchain_path.as_deref(),
            report.compiler.linked_toolchain_detail.as_deref(),
        )
    );
    eprintln!(
        "  daily-driver Trust package surface: {}",
        report.compiler.daily_driver.surface_kind.label()
    );
    if let Some(detail) = report.compiler.daily_driver.detail.as_deref() {
        eprintln!("    detail: {detail}");
    }
    if let Some(path) = report.compiler.daily_driver.linked_targo_path.as_deref() {
        eprintln!("    targo: {}", path.display());
    }
    if let Some(path) = report.compiler.daily_driver.linked_targo_trust_path.as_deref() {
        eprintln!("    targo-trust: {}", path.display());
    }
    eprintln!("    required tools:");
    for tool in &report.compiler.daily_driver.required_tools {
        let path =
            tool.path.as_deref().map(|path| format!(" at {}", path.display())).unwrap_or_default();
        eprintln!("      {:<15} {}{}", tool.name, describe_surface_tool_status(tool.status), path);
    }
    eprintln!("    optional tools:");
    for tool in &report.compiler.daily_driver.optional_tools {
        let detail =
            tool.detail.as_deref().map(|detail| format!(" ({detail})")).unwrap_or_default();
        let path =
            tool.path.as_deref().map(|path| format!(" at {}", path.display())).unwrap_or_default();
        eprintln!(
            "      {:<15} {}{}{}",
            tool.name,
            describe_surface_tool_status(tool.status),
            path,
            detail
        );
    }
    eprintln!(
        "  default Trust verification: {}",
        describe_capability(report.compiler.trust_verify)
    );
    eprintln!(
        "  -Z trust-verify-output=json: {}",
        describe_capability(report.compiler.json_transport)
    );
    eprintln!("  check/report mode: {}", report.compiler.check_report_mode.label());
    eprintln!();
    eprintln!("Backend:");
    eprintln!("  selected: {} ({})", report.backend.selected, report.backend.source.label());
    eprintln!("  available: llvm (default), trust-cg (opt-in)");
    eprintln!();
    eprintln!("Config:");
    eprintln!("  source: {}", describe_config_source(&report.config));
    eprintln!("  enabled: {}", report.config.enabled);
    eprintln!("  level: {}", report.config.level);
    eprintln!("  {}", report.config.budget_profile);
    if let Some(backend) = report.config.configured_codegen_backend.as_deref() {
        eprintln!("  configured backend: {backend}");
    }
    match report.config.configured_hardened {
        Some(value) => eprintln!("  configured hardened: {value}"),
        None => eprintln!("  configured hardened: default (unix_hardened)"),
    }
    if let Some(profile) = report.config.configured_trust_profile.as_deref() {
        eprintln!("  configured trust_profile: {profile}");
    }
    eprintln!();
    eprintln!("Solvers:");
    eprintln!(
        "  available: {}/{} (external binaries: {}, in-process native suites: {})",
        report.solvers.available,
        report.solvers.total,
        report.solvers.external_available,
        report.solvers.native_suite_available
    );
    eprintln!(
        "  routed for source verification: {}/{}",
        report.solvers.routed_available, report.solvers.total
    );
    if let Some(requested) = report.solvers.requested.as_deref() {
        eprintln!("  requested: {}", solver_detect::terminal_safe(requested));
    }
    for solver in &report.solvers.solvers {
        let status = if solver.available { "FOUND" } else { "MISSING" };
        let routing = source_routing_label(solver, &report.verifier_suites);
        let version = solver
            .version
            .as_deref()
            .map(|value| format!(" ({})", solver_detect::terminal_safe(value)))
            .unwrap_or_default();
        let path = solver_path_suffix(solver);
        eprintln!(
            "  [{status:>7}] {:<10} {} [{routing}]{version}{path}",
            solver_detect::terminal_safe(&solver.name),
            solver_detect::terminal_safe(&solver.description)
        );
        print_solver_diagnostic(solver);
    }
    eprintln!();
    eprintln!("Verifier suites:");
    for suite in &report.verifier_suites {
        let in_process = suite.in_process_status;
        let in_process_detail = suite
            .in_process_detail
            .as_deref()
            .map(|detail| format!(" ({detail})"))
            .unwrap_or_default();
        let external =
            if suite.external_executable_available { "external found" } else { "external missing" };
        let external_version = suite
            .external_executable_version
            .as_deref()
            .map(|version| format!(" ({})", solver_detect::terminal_safe(version)))
            .unwrap_or_default();
        let external_path = suite
            .external_executable_path
            .as_deref()
            .map(|path| {
                format!(" at {}", solver_detect::terminal_safe(&path.display().to_string()))
            })
            .unwrap_or_default();
        eprintln!(
            "  {:<10} adapter compiled; in-process: {in_process}{in_process_detail} via `{}`; {external}{external_version}{external_path}; manifest: {} {}",
            suite.name, suite.in_process_feature, suite.manifest.name, suite.manifest.version
        );
    }

    if !report.ready {
        eprintln!();
        eprintln!("Next steps:");
        for step in doctor_next_steps(report) {
            eprintln!("  {}", solver_detect::terminal_safe(&step));
        }
    }

    eprintln!();
    eprintln!("====================");
}

pub(crate) fn print_solvers_terminal(
    solvers: &[solver_detect::SolverInfo],
    verifier_suites: &[DoctorVerifierSuiteStatus],
) {
    let available = solvers.iter().filter(|solver| solver.available).count();
    let routed_available = solvers
        .iter()
        .filter(|solver| {
            solver.available
                && (is_source_solver_routed(&solver.name)
                    || doctor_solver_has_native_source_route(&solver.name, verifier_suites))
        })
        .count();

    eprintln!();
    eprintln!("=== Trust Solver Detection ===");
    eprintln!();
    for solver in solvers {
        let status = if solver.available { "FOUND" } else { "MISSING" };
        let routing = source_routing_label(solver, verifier_suites);
        let levels = if solver.proof_levels.is_empty() {
            String::new()
        } else {
            format!(" [{}]", solver.proof_levels.join(", "))
        };
        let version = solver
            .version
            .as_deref()
            .map(|value| format!(" ({})", solver_detect::terminal_safe(value)))
            .unwrap_or_default();
        let path = solver_path_suffix(solver);
        eprintln!(
            "  [{status:>7}] {:<10} {}{levels} [{routing}]{version}{path}",
            solver_detect::terminal_safe(&solver.name),
            solver_detect::terminal_safe(&solver.description)
        );
        print_solver_diagnostic(solver);
    }

    let (availability_summary, routing_summary) =
        solver_summary_lines(available, routed_available, solvers.len());
    eprintln!();
    eprintln!("{availability_summary}");
    eprintln!("{routing_summary}");

    if routed_available == 0 {
        eprintln!();
        eprintln!(
            "No solver listed here is routed for compiler-backed source verification, which runs the `ay` linked into the Trust compiler: omit `--solver`, or pass `--solver ay`."
        );
    } else if available > routed_available {
        eprintln!();
        eprintln!(
            "Detected-only tools are reported for inventory; they are not accepted by compiler-backed `--solver` until native routing is wired."
        );
    }

    eprintln!("==============================");
}

fn solver_summary_lines(
    available: usize,
    routed_available: usize,
    total: usize,
) -> (String, String) {
    (
        format!("Solver availability: {available}/{total} available"),
        format!(
            "Source verification routing: {routed_available}/{total} routed ({} linked into trustc, plus compiled native suites)",
            supported_source_solver_names()
        ),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver_detect::SolverInfo;

    fn available_solver() -> SolverInfo {
        SolverInfo {
            name: "ay".to_string(),
            description: "Primary SMT solver".to_string(),
            proof_levels: vec!["L0".to_string()],
            available: true,
            path: Some(PathBuf::from("/tmp/ay")),
            version: Some("1.0".to_string()),
            diagnostic: None,
        }
    }

    fn ready_daily_driver_status() -> DoctorDailyDriverStatus {
        DoctorDailyDriverStatus {
            surface_kind: LinkedTrustCargoSurfaceKind::InstalledReady,
            ready: true,
            detail: None,
            linked_targo_path: Some(PathBuf::from("/tmp/trust/bin/targo")),
            linked_targo_trust_path: Some(PathBuf::from("/tmp/trust/bin/targo-trust")),
            required_tools: vec![],
            optional_tools: vec![],
        }
    }

    fn fully_capable_default_native_suites() -> Vec<DoctorVerifierSuiteStatus> {
        let mut suites = verifier_suite_statuses();
        for suite in &mut suites {
            suite.adapter_compiled = true;
            if DEFAULT_NATIVE_SOURCE_ROUTES.contains(&suite.name) {
                assert!(
                    !suite.manifest.capabilities.is_empty(),
                    "{} test fixture must declare at least one capability",
                    suite.name
                );
                for capability in &mut suite.manifest.capabilities {
                    capability.support = SupportLevel::Supported;
                }
            } else {
                assert_eq!(suite.name, "trust-wp", "unexpected diagnostic verifier suite");
                assert!(
                    suite.manifest.capabilities.is_empty(),
                    "retired trust-wp source authority must remain zero-capability"
                );
            }
        }
        suites
    }

    fn report_with_compiler(compiler: DoctorCompilerStatus) -> DoctorReport {
        DoctorReport {
            ready: false,
            status: "needs_attention",
            compiler,
            backend: DoctorBackendStatus {
                selected: DEFAULT_CODEGEN_BACKEND.to_string(),
                source: DoctorBackendSource::Default,
            },
            config: DoctorConfigStatus {
                source: DoctorConfigSourceKind::Defaults,
                path: PathBuf::from("Cargo.toml"),
                detail: None,
                enabled: true,
                level: "L1".to_string(),
                effort: trust_types::determinism::EffortScale::BUILTIN.conflicts_per_node,
                backstop: trust_types::determinism::Backstop::BUILTIN.per_mille,
                budget_profile: trust_types::determinism::BudgetProfile::builtin().header_line(),
                configured_codegen_backend: None,
                configured_hardened: None,
                configured_trust_profile: None,
            },
            solvers: DoctorSolverStatus {
                requested: None,
                external_available: 1,
                native_suite_available: 0,
                available: 1,
                routed_available: 1,
                total: 1,
                solvers: vec![available_solver()],
            },
            verifier_suites: verifier_suite_statuses(),
        }
    }

    #[test]
    fn test_doctor_check_report_mode_prefers_native_compiler_when_supported() {
        assert_eq!(
            doctor_check_report_mode(Some(Path::new("/tmp/rustc")), Some(true)),
            DoctorCheckReportMode::NativeCompiler
        );
        assert_eq!(
            doctor_check_report_mode(Some(Path::new("/tmp/rustc")), Some(false)),
            DoctorCheckReportMode::NativeRequired
        );
        assert_eq!(doctor_check_report_mode(None, None), DoctorCheckReportMode::NativeRequired);
    }

    #[test]
    fn test_doctor_daily_driver_accepts_linked_tools_in_selected_compiler_bin() {
        let daily = ready_daily_driver_status();
        let surface = LinkedTrustCargoSurfaceStatus {
            kind: LinkedTrustCargoSurfaceKind::InstalledReady,
            ready: true,
            same_sysroot: true,
            sysroot: Some(PathBuf::from("/tmp/trust")),
            bin_dir: Some(PathBuf::from("/tmp/trust/bin")),
            targo: daily.linked_targo_path.clone(),
            targo_trust: daily.linked_targo_trust_path.clone(),
            required_tools: daily.required_tools.clone(),
            optional_tools: daily.optional_tools.clone(),
            detail: None,
        };

        let status = build_doctor_daily_driver_status(
            Some(Path::new("/tmp/trust/bin/trustc")),
            Some(Path::new("/tmp/trust/bin/trustc")),
            &surface,
        );

        assert!(status.ready, "{status:?}");
        assert_eq!(status.surface_kind, LinkedTrustCargoSurfaceKind::InstalledReady);
        assert!(status.detail.is_none());
    }

    #[test]
    fn test_doctor_daily_driver_rejects_stale_linked_toolchain_alias() {
        let daily = ready_daily_driver_status();
        let surface = LinkedTrustCargoSurfaceStatus {
            kind: LinkedTrustCargoSurfaceKind::Stage2Ready,
            ready: true,
            same_sysroot: true,
            sysroot: Some(PathBuf::from("/tmp/stage2")),
            bin_dir: Some(PathBuf::from("/tmp/stage2/bin")),
            targo: daily.linked_targo_path.clone(),
            targo_trust: daily.linked_targo_trust_path.clone(),
            required_tools: daily.required_tools.clone(),
            optional_tools: daily.optional_tools.clone(),
            detail: None,
        };

        let status = build_doctor_daily_driver_status(
            Some(Path::new("/tmp/stage2/bin/trustc")),
            Some(Path::new("/tmp/stage1/bin/trustc")),
            &surface,
        );

        assert!(!status.ready);
        assert_eq!(status.surface_kind, LinkedTrustCargoSurfaceKind::AmbientFallback);
        assert!(
            status.detail.as_deref().is_some_and(|detail| detail.contains("select one Trust root")),
            "detail should explain Trust root remediation: {status:?}"
        );
    }

    #[test]
    fn test_native_suite_source_route_uses_compiled_manifest_not_generic_smoke() {
        let mut suite = verifier_suite_statuses()
            .into_iter()
            .find(|suite| suite.name == "trust-mc")
            .expect("trust-mc verifier suite should be present");

        for capability in &mut suite.manifest.capabilities {
            capability.support = SupportLevel::Supported;
        }
        suite.in_process_available = false;
        assert!(
            doctor_suite_has_native_source_route(&suite),
            "typed native routes must count even when the generic smoke probe is unsupported"
        );

        suite.adapter_compiled = false;
        assert!(
            !doctor_suite_has_native_source_route(&suite),
            "uncompiled native adapters must not count as routed"
        );

        suite.adapter_compiled = true;
        for capability in &mut suite.manifest.capabilities {
            capability.support =
                SupportLevel::Experimental { reason: "test-only unwired route".to_string() };
        }
        assert!(
            !doctor_suite_has_native_source_route(&suite),
            "experimental capability ownership must not count as a routed proof lane"
        );

        suite.manifest.capabilities.clear();
        assert!(
            !doctor_suite_has_native_source_route(&suite),
            "native adapters without declared capabilities must not count as routed"
        );
    }

    /// The smoke request must be CANONICAL: the bundle carries the one
    /// obligation it asks about, so the hardened `verify_with_context`
    /// wrapper's inventory validation passes and the engine actually runs.
    #[test]
    fn test_doctor_smoke_probe_request_is_canonical() {
        let (bundle, obligation) = doctor_smoke_probe_request(
            "trust-wp",
            "targo-trust-doctor-trust-wp-smoke",
            ObligationKind::Precondition,
        );
        assert_eq!(bundle.obligations.as_slice(), std::slice::from_ref(&obligation));
        bundle
            .validate_requested_obligations(std::slice::from_ref(&obligation))
            .expect("doctor smoke request must be an exact subset of its own bundle");
    }

    /// The trust-mc smoke must reach the engine and report the engine's own
    /// honest verdict — never the pre-fix "invalid one-obligation run
    /// envelope" message, which meant the hardened wrapper had (correctly)
    /// fail-closed on a non-canonical request and the engine never ran.
    #[test]
    fn test_trust_mc_smoke_probe_reports_engine_verdict_not_envelope_failure() {
        let engine = trust_bmc::TrustMcVerifierApiAdapter::default();
        let probe = verifier_engine_smoke_probe("trust-mc", ObligationKind::Assertion, &engine);

        assert!(!probe.available, "{probe:?}");
        let detail = probe.detail.as_deref().unwrap_or_default();
        assert!(
            !detail.contains("one-obligation run envelope"),
            "smoke must not report the misleading envelope message: {probe:?}"
        );
        #[cfg(not(feature = "trust-mc-in-process"))]
        {
            // Default build: the fail-closed metadata-only stub adapter runs
            // and declines with its actionable feature-gate diagnostic.
            assert_eq!(probe.status, "unsupported", "{probe:?}");
            assert!(
                detail.contains("disabled in the default trust-bmc build"),
                "stub decline must carry its actionable reason: {probe:?}"
            );
        }
        #[cfg(feature = "trust-mc-in-process")]
        {
            // Shipped feature set: the native solver genuinely solves the
            // canonical typed-CHC smoke bundle, and public dispatch keeps the
            // candidate NON-definitive (Proved requires a deliverable live
            // receipt), so the probe honestly reports the engine's Unknown
            // verdict with the engine's own explanation.
            assert_eq!(probe.status, "unavailable", "{probe:?}");
            assert!(
                detail.contains("returned Unknown evidence"),
                "native candidate outcome must be surfaced: {probe:?}"
            );
        }
    }

    #[test]
    fn test_doctor_readiness_requires_every_default_native_source_route() {
        let report = report_with_compiler(DoctorCompilerStatus {
            path: Some(PathBuf::from("/tmp/trust/bin/trustc")),
            discovery_source: None,
            discovery_error: None,
            linked_toolchain_status: LinkedTrustToolchainStatusKind::Visible,
            linked_toolchain_path: Some(PathBuf::from("/tmp/trust/bin/trustc")),
            linked_toolchain_detail: None,
            daily_driver: ready_daily_driver_status(),
            trust_verify: Some(true),
            json_transport: Some(true),
            check_report_mode: DoctorCheckReportMode::NativeCompiler,
            toolchain_age: None,
        });
        let capable_suites = fully_capable_default_native_suites();

        assert!(doctor_is_ready(&report.compiler, &report.config, 1, &capable_suites));

        for missing_name in DEFAULT_NATIVE_SOURCE_ROUTES {
            let missing_suite = capable_suites
                .iter()
                .filter(|suite| suite.name != *missing_name)
                .cloned()
                .collect::<Vec<_>>();
            assert!(
                !doctor_is_ready(&report.compiler, &report.config, 1, &missing_suite),
                "ay availability must not hide a missing {missing_name} native route"
            );
        }

        let trust_wp = capable_suites
            .iter()
            .find(|suite| suite.name == "trust-wp")
            .expect("trust-wp diagnostic fixture");
        assert!(trust_wp.manifest.capabilities.is_empty());
        assert!(!doctor_suite_has_native_source_route(trust_wp));
        let mut forged_trust_wp = trust_wp.clone();
        forged_trust_wp.manifest.capabilities = capable_suites
            .iter()
            .find(|suite| suite.name == "trust-mc")
            .expect("trust-mc fixture")
            .manifest
            .capabilities
            .clone();
        for capability in &mut forged_trust_wp.manifest.capabilities {
            capability.support = SupportLevel::Supported;
        }
        assert!(
            !doctor_suite_has_native_source_route(&forged_trust_wp),
            "even a drifted historical TrustWP manifest must not revive a source route"
        );
        assert!(
            doctor_is_ready(&report.compiler, &report.config, 1, &capable_suites),
            "zero-capability trust-wp diagnostics must not block required native routes"
        );

        let without_trust_wp = capable_suites
            .iter()
            .filter(|suite| suite.name != "trust-wp")
            .cloned()
            .collect::<Vec<_>>();
        assert!(
            doctor_is_ready(&report.compiler, &report.config, 1, &without_trust_wp),
            "retired trust-wp inventory must not be a readiness requirement"
        );

        let mut steps_report = report;
        steps_report.verifier_suites = without_trust_wp;
        steps_report.solvers.routed_available = 1;
        let steps = doctor_next_steps(&steps_report);
        assert!(
            steps.iter().all(|step| !step.contains("trust-wp")),
            "doctor must not prescribe rebuilding retired trust-wp authority: {steps:?}"
        );
    }

    /// Plan P4 / T4.1: compiler-backed source verification runs the `ay` linked
    /// into trustc, so a missing external `ay` neither unroutes it nor makes
    /// doctor tell the user to install one. A found external `ay` keeps its
    /// probe identity, which is what `verify-binary` runs.
    #[test]
    fn test_linked_ay_is_routed_without_an_external_binary() {
        let mut missing = available_solver();
        missing.available = false;
        missing.path = None;
        missing.version = None;
        missing.diagnostic = Some("`ay` was not found beside targo-trust or on PATH".to_string());
        let found = available_solver();
        let mut other = available_solver();
        other.name = "cvc5".to_string();
        other.available = false;
        other.path = None;
        let suites = fully_capable_default_native_suites();

        let mut solvers = vec![missing, found.clone(), other];
        mark_doctor_in_process_solver_routes(&mut solvers, &suites);

        assert!(solvers[0].available, "the linked ay needs no external binary");
        assert_eq!(solvers[0].version.as_deref(), Some("linked into trustc"));
        assert_eq!(source_routing_label(&solvers[0], &suites), "source-routed: linked into trustc");
        assert_eq!(
            (&solvers[1].path, &solvers[1].version),
            (&found.path, &found.version),
            "an external ay keeps its probe identity"
        );
        assert!(solver_path_suffix(&solvers[1]).contains("external binary for verify-binary"));
        assert!(!solvers[2].available, "an unrouted solver is not marked by the ay rule");

        let mut report = report_with_compiler(DoctorCompilerStatus {
            path: Some(PathBuf::from("/tmp/trust/bin/trustc")),
            discovery_source: None,
            discovery_error: None,
            linked_toolchain_status: LinkedTrustToolchainStatusKind::Visible,
            linked_toolchain_path: Some(PathBuf::from("/tmp/trust/bin/trustc")),
            linked_toolchain_detail: None,
            daily_driver: ready_daily_driver_status(),
            trust_verify: Some(true),
            json_transport: Some(true),
            check_report_mode: DoctorCheckReportMode::NativeCompiler,
            toolchain_age: None,
        });
        report.solvers.routed_available = 0;
        let steps = doctor_next_steps(&report);
        assert!(
            steps.iter().all(|step| !step.contains("Install `ay`") && !step.contains("AY_PATH")),
            "no next step may send the user after an external ay for source verification: \
             {steps:?}"
        );
    }

    #[test]
    fn test_solver_summary_distinguishes_inventory_from_source_routes() {
        let (availability, routing) = solver_summary_lines(6, 4, 6);

        assert_eq!(availability, "Solver availability: 6/6 available");
        assert!(!availability.contains("route"));
        assert_eq!(
            routing,
            "Source verification routing: 4/6 routed (ay linked into trustc, plus compiled native suites)"
        );
    }

    #[test]
    fn test_doctor_next_steps_suggests_selecting_trust_root() {
        let report = report_with_compiler(DoctorCompilerStatus {
            path: None,
            discovery_source: None,
            discovery_error: None,
            linked_toolchain_status: LinkedTrustToolchainStatusKind::Missing,
            linked_toolchain_path: None,
            linked_toolchain_detail: Some("toolchain `trust` is not installed".to_string()),
            daily_driver: DoctorDailyDriverStatus {
                surface_kind: LinkedTrustCargoSurfaceKind::Missing,
                ready: false,
                detail: Some("toolchain `trust` is not installed".to_string()),
                linked_targo_path: None,
                linked_targo_trust_path: None,
                required_tools: vec![],
                optional_tools: vec![],
            },
            trust_verify: None,
            json_transport: None,
            check_report_mode: DoctorCheckReportMode::NativeRequired,
            toolchain_age: None,
        });

        let steps = doctor_next_steps(&report);
        assert!(steps.iter().any(|step| step.contains("canonical `trustc`")));
        assert!(steps.iter().any(|step| step.contains("trustdoc")
            && step.contains("trustd")
            && step.contains("trustfmt")
            && step.contains("trust-analyzer")));
        assert!(steps.iter().any(|step| step.contains("daily-driver toolchain surface")));
    }

    #[test]
    fn toolchain_age_reads_trustc_verbose_version_and_warns_past_the_limit() {
        let vv = "rustc 1.101.0-dev (29ebb403d 2026-10-28) (trustc 0.12.0+g29ebb403d)\n\
                  binary: trustc\n\
                  commit-hash: 29ebb403de7a102850d6cb10a62d5cc3baf723ed\n\
                  commit-date: 2026-10-28\n\
                  host: aarch64-apple-darwin\n";
        let built = super::days_from_civil_date("2026-10-28").expect("date parses");
        assert_eq!(super::days_from_civil_date("1970-01-01"), Some(0));
        assert_eq!(super::days_from_civil_date("2000-03-01"), Some(11_017));

        let fresh = super::parse_toolchain_age(vv, Some(built + 16)).expect("age parses");
        assert_eq!(fresh.commit_hash.as_deref(), Some("29ebb403de7a102850d6cb10a62d5cc3baf723ed"));
        assert_eq!(fresh.commit_date, "2026-10-28");
        assert_eq!(fresh.age_days, Some(16));
        assert!(!fresh.stale);
        let line = super::describe_toolchain_age(Some(&fresh)).expect("line");
        assert_eq!(line, "built from: 29ebb403de, 2026-10-28 (16 days ago)");

        let at_limit = super::parse_toolchain_age(vv, Some(built + 42)).unwrap();
        assert!(!at_limit.stale, "the limit itself is not stale");
        let stale = super::parse_toolchain_age(vv, Some(built + 43)).unwrap();
        assert!(stale.stale);
        assert!(
            super::describe_toolchain_age(Some(&stale)).unwrap().contains("more than 42 days old"),
        );

        let unknown = "rustc 1.101.0-dev\ncommit-hash: unknown\ncommit-date: unknown\n";
        assert_eq!(super::parse_toolchain_age(unknown, Some(built)), None);
        let clockless = super::parse_toolchain_age(vv, None).unwrap();
        assert_eq!(clockless.age_days, None);
        assert!(!clockless.stale);
    }

    /// A compiler whose `-vV` never returns must not hang `targo trust doctor`.
    /// Control: the production probe, under the harness's stretched deadline
    /// (`resolve_probe_deadline`), reads a fake compiler that answers. A fixed
    /// short deadline there would fail on a loaded Mac, where a newly written
    /// script can wait in the system's program check before it starts.
    #[cfg(unix)]
    #[test]
    fn toolchain_age_probe_is_bounded() {
        use std::os::unix::fs::PermissionsExt;
        let dir = tempfile::tempdir().expect("tempdir");
        let fake = |name: &str, body: &str| {
            let path = dir.path().join(name);
            std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).expect("write fake trustc");
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
                .expect("chmod fake trustc");
            path
        };
        let answers = fake(
            "answers",
            "printf 'rustc 1.101.0-dev\\ncommit-hash: 29ebb403de7a102850d6cb10a62d5cc3baf723ed\\n\
             commit-date: 2026-10-28\\nhost: aarch64-apple-darwin\\n'",
        );
        let control = super::detect_toolchain_age(&answers).expect("the control compiler's age is read");
        assert_eq!(control.commit_date, "2026-10-28");

        let hangs = fake("hangs", "exec /bin/sleep 60");
        let started = std::time::Instant::now();
        assert!(
            super::detect_toolchain_age_within(&hangs, std::time::Duration::from_millis(500)).is_none(),
            "a compiler that never answers has no age"
        );
        assert!(
            started.elapsed() < std::time::Duration::from_secs(20),
            "the probe waited {:?} for a hung compiler",
            started.elapsed()
        );
    }
}
