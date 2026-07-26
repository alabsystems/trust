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
    pub(crate) timeout_ms: u64,
    pub(crate) function_budget_ms: u64,
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
    /// distinct from `in_process_available` (which reflects only the contentless
    /// doctor SMOKE probe, and is honestly `false` because a bare obligation carries
    /// no typed CHC input to prove). A consumer asking "is this batteries-on engine
    /// actually wired/capable?" should read THIS, not the smoke result; real
    /// proof-grade behavior is exercised by compilation (see the falsification gate).
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
            timeout_ms: config.timeout_ms,
            function_budget_ms: config.function_budget_ms,
            configured_codegen_backend: config.codegen_backend.clone(),
            configured_hardened: config.hardened,
            configured_trust_profile: config.trust_profile.clone(),
        }
    }

    match resolve_trust_config(crate_root, None) {
        Ok(resolved) => {
            let mut detail = resolved.workspace_defaults_from.as_ref().map(|workspace| {
                format!("unset keys inherited from {}", workspace.display())
            });
            let (kind, path) = match resolved.source {
                TrustConfigSource::Manifest(path) => (DoctorConfigSourceKind::Manifest, path),
                TrustConfigSource::LegacyFile(path) => {
                    detail = Some(crate::config::legacy_config_deprecation_notice());
                    (DoctorConfigSourceKind::LegacyFile, path)
                }
                TrustConfigSource::Defaults => {
                    let path = discover_manifest(crate_root)
                        .unwrap_or_else(|| crate_root.to_path_buf());
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
            "Install `ay` or set AY_PATH, or build/link a Trust toolchain with in-process native verifier suites, so compiler-backed source verification has a routed solver."
                .to_string(),
        );
    }
    if report.config.source.has_error() {
        steps.push(
            format!(
                "Fix or remove {} so targo-trust can load configuration cleanly.",
                report.config.path.display()
            ),
        );
    }

    steps
}

pub(crate) fn is_source_solver_routed(name: &str) -> bool {
    matches!(name, "ay")
}

pub(crate) fn supported_source_solver_names() -> &'static str {
    "ay"
}

const DEFAULT_NATIVE_SOURCE_ROUTES: &[&str] = &["trust-mc", "trust-wp", "trust-vc"];

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
        && matches!(suite.name, "trust-mc" | "trust-wp" | "trust-vc")
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

fn verifier_engine_smoke_probe(
    suite_name: &str,
    obligation_kind: ObligationKind,
    engine: &dyn VerificationEngine,
) -> VerifierEngineSmokeProbe {
    let run_id = format!("targo-trust-doctor-{suite_name}-smoke");
    let bundle = TrustContractBundle::empty(
        format!("{run_id}-bundle"),
        BundleSubject::Artifact { name: suite_name.to_string(), kind: "doctor-smoke".to_string() },
    );
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
        && result.requested_obligations == [obligation]
        && result.evidence.len() == 1
        && result.evidence[0].obligation_id == format!("{run_id}-obligation")
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
        return VerifierEngineSmokeProbe {
            available: false,
            status: "unavailable",
            detail: Some(format!(
                "in-process verifier returned {:?} evidence for smoke obligation",
                evidence.status
            )),
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
    eprintln!("  timeout_ms: {}", report.config.timeout_ms);
    eprintln!("  function_budget_ms: {}", report.config.function_budget_ms);
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
        let routing = if is_source_solver_routed(&solver.name) {
            "source-routed"
        } else if doctor_solver_has_native_source_route(&solver.name, &report.verifier_suites) {
            "in-process source-routed"
        } else {
            "not source-routed"
        };
        let version = solver
            .version
            .as_deref()
            .map(|value| format!(" ({})", solver_detect::terminal_safe(value)))
            .unwrap_or_default();
        let path = solver
            .path
            .as_deref()
            .map(|path| {
                format!(" at {}", solver_detect::terminal_safe(&path.display().to_string()))
            })
            .unwrap_or_default();
        eprintln!(
            "  [{status:>7}] {:<10} {} [{routing}]{version}{path}",
            solver_detect::terminal_safe(&solver.name),
            solver_detect::terminal_safe(&solver.description)
        );
        if let Some(diagnostic) = &solver.diagnostic {
            eprintln!("             ERROR: {}", solver_detect::terminal_safe(diagnostic));
        }
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
        let routing = if is_source_solver_routed(&solver.name) {
            "source-routed"
        } else if doctor_solver_has_native_source_route(&solver.name, verifier_suites) {
            "in-process source-routed"
        } else if solver.available {
            "detected-only"
        } else {
            "not source-routed"
        };
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
        let path = solver
            .path
            .as_deref()
            .map(|path| {
                format!(" at {}", solver_detect::terminal_safe(&path.display().to_string()))
            })
            .unwrap_or_default();
        eprintln!(
            "  [{status:>7}] {:<10} {}{levels} [{routing}]{version}{path}",
            solver_detect::terminal_safe(&solver.name),
            solver_detect::terminal_safe(&solver.description)
        );
        if let Some(diagnostic) = &solver.diagnostic {
            eprintln!("             ERROR: {}", solver_detect::terminal_safe(diagnostic));
        }
    }

    let (availability_summary, routing_summary) =
        solver_summary_lines(available, routed_available, solvers.len());
    eprintln!();
    eprintln!("{availability_summary}");
    eprintln!("{routing_summary}");

    if routed_available == 0 {
        eprintln!();
        eprintln!(
            "No routed source solver found. Install ay, set AY_PATH, or build/link Trust with in-process native verifier suites."
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
            "Source verification routing: {routed_available}/{total} routed ({}, plus compiled native suites)",
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
            assert!(
                DEFAULT_NATIVE_SOURCE_ROUTES.contains(&suite.name),
                "unexpected default verifier suite in test fixture: {}",
                suite.name
            );
            assert!(
                !suite.manifest.capabilities.is_empty(),
                "{} test fixture must declare at least one capability",
                suite.name
            );
            suite.adapter_compiled = true;
            for capability in &mut suite.manifest.capabilities {
                capability.support = SupportLevel::Supported;
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
                timeout_ms: 5_000,
                function_budget_ms: 120_000,
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

        let mut incapable_suite = capable_suites.clone();
        let trust_wp = incapable_suite
            .iter_mut()
            .find(|suite| suite.name == "trust-wp")
            .expect("trust-wp fixture");
        for capability in &mut trust_wp.manifest.capabilities {
            capability.support =
                SupportLevel::Experimental { reason: "test-only unwired route".to_string() };
        }
        assert!(
            !doctor_is_ready(&report.compiler, &report.config, 1, &incapable_suite),
            "an installed ay must not make an incapable trust-wp route ready"
        );

        let mut steps_report = report;
        steps_report.verifier_suites = incapable_suite;
        steps_report.solvers.routed_available = 1;
        let steps = doctor_next_steps(&steps_report);
        assert!(
            steps.iter().any(|step| step.contains("trust-wp")),
            "doctor remediation must name the missing native route: {steps:?}"
        );
    }

    #[test]
    fn test_solver_summary_distinguishes_inventory_from_source_routes() {
        let (availability, routing) = solver_summary_lines(6, 4, 6);

        assert_eq!(availability, "Solver availability: 6/6 available");
        assert!(!availability.contains("route"));
        assert_eq!(
            routing,
            "Source verification routing: 4/6 routed (ay, plus compiled native suites)"
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
        });

        let steps = doctor_next_steps(&report);
        assert!(steps.iter().any(|step| step.contains("canonical `trustc`")));
        assert!(steps.iter().any(|step| step.contains("trustdoc")
            && step.contains("trustd")
            && step.contains("trustfmt")
            && step.contains("trust-analyzer")));
        assert!(steps.iter().any(|step| step.contains("daily-driver toolchain surface")));
    }
}
