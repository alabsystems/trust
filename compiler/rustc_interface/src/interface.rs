use std::hash::Hash;
use std::path::PathBuf;
use std::result;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use rustc_ast::{LitKind, MetaItemKind, token};
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_data_structures::jobserver::{self, Proxy};
use rustc_data_structures::stable_hash::StableHasher;
use rustc_errors::{DiagCtxtHandle, ErrorGuaranteed};
use rustc_lint::LintStore;
use rustc_middle::ty;
use rustc_middle::ty::CurrentGcx;
use rustc_middle::util::Providers;
use rustc_parse::lexer::StripTokens;
use rustc_parse::new_parser_from_source_str;
use rustc_parse::parser::Recovery;
use rustc_parse::parser::attr::AllowLeadingUnsafe;
use rustc_query_impl::print_query_stack;
use rustc_session::config::{self, Cfg, CheckCfg, ExpectedValues, Input, OutFileName};
use rustc_session::parse::ParseSess;
use rustc_session::{CompilerIO, EarlyDiagCtxt, Session, lint};
use rustc_span::source_map::{FileLoader, RealFileLoader, SourceMapInputs};
use rustc_span::{FileName, sym};
use tracing::trace;

use crate::util;

pub type Result<T> = result::Result<T, ErrorGuaranteed>;

static TRUST_VERIFIER_INVOCATION_SEQUENCE: AtomicU64 = AtomicU64::new(0);

fn hash_fresh_trust_verifier_invocation(hasher: &mut StableHasher) {
    let sequence = TRUST_VERIFIER_INVOCATION_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let epoch_nanos = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_nanos();
    ("rustc-interface:trust-verifier-invocation:v1", std::process::id(), sequence, epoch_nanos)
        .hash(hasher);
}

/// Finalize state that must invalidate incremental queries without changing the
/// downstream crate hash. Trust verification deliberately receives a fresh
/// per-rustc-invocation identity: proof diagnostics and transport must never be
/// silently reused from an earlier compiler process. Targo additionally passes
/// `-Z trust-verify-session` so Cargo itself schedules rustc once per proof run.
#[allow(rustc::bad_opt_access)]
pub(crate) fn finalize_untracked_session_state(
    sess: &mut Session,
    track_state: Option<Box<dyn FnOnce(&Session) + Send>>,
) {
    if track_state.is_none() && !sess.trust_verification_enabled() {
        return;
    }

    // The external solver can affect certified-check elision and therefore
    // emitted MIR. Snapshot it once, before any dependency hash is consumed,
    // and bind the exact copied bytes (not merely the configured path) into a
    // TRACKED top-level option. The verifier later executes this same snapshot.
    if sess.trust_verification_enabled() {
        rustc_mir_transform::trust_initialize_ay_solver_identity(sess);
    }

    if sess.trust_verification_enabled() {
        let mut hasher = StableHasher::new();
        hash_fresh_trust_verifier_invocation(&mut hasher);
        sess.opts.untracked_state_hash = hasher.finish();
    }
    if let Some(track_state) = track_state {
        // Current rustc tracks custom-driver state through env/file dep-info;
        // retain that upstream API independently from Trust's fresh verifier
        // query identity above.
        track_state(sess);
    }
}

/// Represents a compiler session. Note that every `Compiler` contains a
/// `Session`, but `Compiler` also contains some things that cannot be in
/// `Session`, due to `Session` being in a crate that has many fewer
/// dependencies than this crate.
///
/// Can be used to run `rustc_interface` queries.
/// Created by passing [`Config`] to [`run_compiler`].
pub struct Compiler {
    pub sess: Session,
    pub codegen_backend: Box<dyn CodegenBackend>,
    pub(crate) override_queries: Option<fn(&Session, &mut Providers)>,

    /// A reference to the current `GlobalCtxt` which we pass on to `GlobalCtxt`.
    pub(crate) current_gcx: CurrentGcx,

    /// A jobserver reference which we pass on to `GlobalCtxt`.
    pub(crate) jobserver_proxy: Arc<Proxy>,
}

/// Converts strings provided as `--cfg [cfgspec]` into a `Cfg`.
pub(crate) fn parse_cfg(dcx: DiagCtxtHandle<'_>, cfgs: Vec<String>) -> Cfg {
    cfgs.into_iter()
        .map(|s| {
            let psess = ParseSess::emitter_with_note(format!(
                "this occurred on the command line: `--cfg={s}`"
            ));
            let filename = FileName::cfg_spec_source_code(&s);

            macro_rules! error {
                ($reason: expr) => {
                    dcx.fatal(format!("invalid `--cfg` argument: `{s}` ({})", $reason));
                };
            }

            match new_parser_from_source_str(&psess, filename, s.to_string(), StripTokens::Nothing)
            {
                Ok(mut parser) => {
                    parser = parser.recovery(Recovery::Forbidden);
                    match parser.parse_meta_item(AllowLeadingUnsafe::No) {
                        Ok(meta_item)
                            if parser.token == token::Eof
                                && parser.dcx().has_errors().is_none() =>
                        {
                            if meta_item.path.segments.len() != 1 {
                                error!("argument key must be an identifier");
                            }
                            match &meta_item.kind {
                                MetaItemKind::List(..) => {}
                                MetaItemKind::NameValue(lit) if !lit.kind.is_str() => {
                                    error!("argument value must be a string");
                                }
                                MetaItemKind::NameValue(..) | MetaItemKind::Word => {
                                    let ident = meta_item.ident().expect("multi-segment cfg key");

                                    if ident.is_path_segment_keyword() {
                                        error!(
                                            "malformed `cfg` input, expected a valid identifier"
                                        );
                                    }

                                    return (ident.name, meta_item.value_str());
                                }
                            }
                        }
                        Ok(..) => {}
                        Err(err) => err.cancel(),
                    }
                }
                Err(errs) => errs.into_iter().for_each(|err| err.cancel()),
            };

            // If the user tried to use a key="value" flag, but is missing the quotes, provide
            // a hint about how to resolve this.
            if s.contains('=') && !s.contains("=\"") && !s.ends_with('"') {
                error!(concat!(
                    r#"expected `key` or `key="value"`, ensure escaping is appropriate"#,
                    r#" for your shell, try 'key="value"' or key=\"value\""#
                ));
            } else {
                error!(r#"expected `key` or `key="value"`"#);
            }
        })
        .collect::<Cfg>()
}

/// Converts strings provided as `--check-cfg [specs]` into a `CheckCfg`.
pub(crate) fn parse_check_cfg(dcx: DiagCtxtHandle<'_>, specs: Vec<String>) -> CheckCfg {
    // If any --check-cfg is passed then exhaustive_values and exhaustive_names
    // are enabled by default.
    let exhaustive_names = !specs.is_empty();
    let exhaustive_values = !specs.is_empty();
    let mut check_cfg = CheckCfg { exhaustive_names, exhaustive_values, ..CheckCfg::default() };

    for s in specs {
        let psess = ParseSess::emitter_with_note(format!(
            "this occurred on the command line: `--check-cfg={s}`"
        ));
        let filename = FileName::cfg_spec_source_code(&s);

        const VISIT: &str = "visit the Trust trustc check-cfg documentation for more details";

        macro_rules! error {
            ($reason:expr) => {{
                let mut diag = dcx.struct_fatal(format!("invalid `--check-cfg` argument: `{s}`"));
                diag.note($reason);
                diag.note(VISIT);
                diag.emit()
            }};
            (in $arg:expr, $reason:expr) => {{
                let mut diag = dcx.struct_fatal(format!("invalid `--check-cfg` argument: `{s}`"));

                let pparg = rustc_ast_pretty::pprust::meta_list_item_to_string($arg);
                if let Some(lit) = $arg.lit() {
                    let (lit_kind_article, lit_kind_descr) = {
                        let lit_kind = lit.as_token_lit().kind;
                        (lit_kind.article(), lit_kind.descr())
                    };
                    diag.note(format!("`{pparg}` is {lit_kind_article} {lit_kind_descr} literal"));
                } else {
                    diag.note(format!("`{pparg}` is invalid"));
                }

                diag.note($reason);
                diag.note(VISIT);
                diag.emit()
            }};
        }

        let expected_error = || -> ! {
            error!("expected `cfg(name, values(\"value1\", \"value2\", ... \"valueN\"))`")
        };

        let mut parser =
            match new_parser_from_source_str(&psess, filename, s.to_string(), StripTokens::Nothing)
            {
                Ok(parser) => parser.recovery(Recovery::Forbidden),
                Err(errs) => {
                    errs.into_iter().for_each(|err| err.cancel());
                    expected_error();
                }
            };

        let meta_item = match parser.parse_meta_item(AllowLeadingUnsafe::No) {
            Ok(meta_item) if parser.token == token::Eof && parser.dcx().has_errors().is_none() => {
                meta_item
            }
            Ok(..) => expected_error(),
            Err(err) => {
                err.cancel();
                expected_error();
            }
        };

        let Some(args) = meta_item.meta_item_list() else {
            expected_error();
        };

        if !meta_item.has_name(sym::cfg) {
            expected_error();
        }

        let mut names = Vec::new();
        let mut values: FxHashSet<_> = Default::default();

        let mut any_specified = false;
        let mut values_specified = false;
        let mut values_any_specified = false;

        for arg in args {
            if arg.is_word()
                && let Some(ident) = arg.ident()
            {
                if values_specified {
                    error!("`cfg()` names cannot be after values");
                }

                if ident.is_path_segment_keyword() {
                    error!("malformed `cfg` input, expected a valid identifier");
                }

                names.push(ident);
            } else if let Some(boolean) = arg.boolean_literal() {
                if values_specified {
                    error!("`cfg()` names cannot be after values");
                }
                names.push(rustc_span::Ident::new(
                    if boolean { rustc_span::kw::True } else { rustc_span::kw::False },
                    arg.span(),
                ));
            } else if arg.has_name(sym::any)
                && let Some(args) = arg.meta_item_list()
            {
                if any_specified {
                    error!("`any()` cannot be specified multiple times");
                }
                any_specified = true;
                if !args.is_empty() {
                    error!(in arg, "`any()` takes no argument");
                }
            } else if arg.has_name(sym::values)
                && let Some(args) = arg.meta_item_list()
            {
                if names.is_empty() {
                    error!("`values()` cannot be specified before the names");
                } else if values_specified {
                    error!("`values()` cannot be specified multiple times");
                }
                values_specified = true;

                for arg in args {
                    if let Some(LitKind::Str(s, _)) = arg.lit().map(|lit| &lit.kind) {
                        values.insert(Some(*s));
                    } else if arg.has_name(sym::any)
                        && let Some(args) = arg.meta_item_list()
                    {
                        if values_any_specified {
                            error!(in arg, "`any()` in `values()` cannot be specified multiple times");
                        }
                        values_any_specified = true;
                        if !args.is_empty() {
                            error!(in arg, "`any()` in `values()` takes no argument");
                        }
                    } else if arg.has_name(sym::none)
                        && let Some(args) = arg.meta_item_list()
                    {
                        values.insert(None);
                        if !args.is_empty() {
                            error!(in arg, "`none()` in `values()` takes no argument");
                        }
                    } else {
                        error!(in arg, "`values()` arguments must be string literals, `none()` or `any()`");
                    }
                }
            } else {
                error!(in arg, "`cfg()` arguments must be simple identifiers, `any()` or `values(...)`");
            }
        }

        if !values_specified && !any_specified {
            // `cfg(name)` is equivalent to `cfg(name, values(none()))` so add
            // an implicit `none()`
            values.insert(None);
        } else if !values.is_empty() && values_any_specified {
            error!(
                "`values()` arguments cannot specify string literals and `any()` at the same time"
            );
        }

        if any_specified {
            if names.is_empty() && values.is_empty() && !values_specified && !values_any_specified {
                check_cfg.exhaustive_names = false;
            } else {
                error!("`cfg(any())` can only be provided in isolation");
            }
        } else {
            for name in names {
                check_cfg
                    .expecteds
                    .entry(name.name)
                    .and_modify(|v| match v {
                        ExpectedValues::Some(v) if !values_any_specified =>
                        {
                            #[allow(rustc::potential_query_instability)]
                            v.extend(values.clone())
                        }
                        ExpectedValues::Some(_) => *v = ExpectedValues::Any,
                        ExpectedValues::Any => {}
                    })
                    .or_insert_with(|| {
                        if values_any_specified {
                            ExpectedValues::Any
                        } else {
                            ExpectedValues::Some(values.clone())
                        }
                    });
            }
        }
    }

    check_cfg
}

/// The compiler configuration
pub struct Config {
    /// Command line options
    pub opts: config::Options,

    /// Unparsed cfg! configuration in addition to the default ones.
    pub crate_cfg: Vec<String>,
    pub crate_check_cfg: Vec<String>,

    pub input: Input,
    pub output_dir: Option<PathBuf>,
    pub output_file: Option<OutFileName>,
    pub ice_file: Option<PathBuf>,
    /// Load files from sources other than the file system.
    ///
    /// Has no uses within this repository, but may be used in the future by
    /// bjorn3 for "hooking rust-analyzer's VFS into rustc at some point for
    /// running rustc without having to save". (See #102759.)
    pub file_loader: Option<Box<dyn FileLoader + Send + Sync>>,

    pub lint_caps: FxHashMap<lint::LintId, lint::Level>,

    /// This is a callback from the driver that is called when [`ParseSess`] is created.
    pub psess_created: Option<Box<dyn FnOnce(&mut ParseSess) + Send>>,

    /// This is a callback to track otherwise untracked state used by the caller.
    ///
    /// You can write to `sess.env_depinfo` and `sess.file_depinfo` to track env vars and files.
    pub track_state: Option<Box<dyn FnOnce(&Session) + Send>>,

    /// This is a callback from the driver that is called when we're registering lints;
    /// it is called during lint loading when we have the LintStore in a non-shared state.
    ///
    /// Note that if you find a Some here you probably want to call that function in the new
    /// function being registered.
    pub register_lints: Option<Box<dyn Fn(&Session, &mut LintStore) + Send + Sync>>,

    /// This is a callback from the driver that is called just after we have populated
    /// the list of queries.
    pub override_queries: Option<fn(&Session, &mut Providers)>,

    /// An extra set of symbols to add to the symbol interner, the symbol indices
    /// will start at [`PREDEFINED_SYMBOLS_COUNT`](rustc_span::symbol::PREDEFINED_SYMBOLS_COUNT)
    pub extra_symbols: Vec<&'static str>,

    /// This is a callback from the driver that is called to create a codegen backend.
    ///
    /// Has no uses within this repository, but is used by bjorn3 for "the
    /// hotswapping branch of cg_clif" for "setting the codegen backend from a
    /// custom driver where the custom codegen backend has arbitrary data."
    /// (See #102759.)
    ///
    /// Mutually exclusive with an explicit `-Zcodegen-backend`: a callback
    /// factory must not silently replace the backend named by the invocation.
    pub make_codegen_backend: Option<Box<dyn FnOnce(&Session) -> Box<dyn CodegenBackend> + Send>>,

    /// The inner atomic value is set to true when a feature marked as `internal` is
    /// enabled. Makes it so that "please report a bug" is hidden, as ICEs with
    /// internal features are wontfix, and they are usually the cause of the ICEs.
    pub using_internal_features: &'static std::sync::atomic::AtomicBool,
}

/// Initialize jobserver before getting `jobserver::client` and `build_session`.
pub(crate) fn initialize_checked_jobserver(early_dcx: &EarlyDiagCtxt) {
    jobserver::initialize_checked(|err| {
        early_dcx
            .early_struct_warn(err)
            .with_note("the build environment is likely misconfigured")
            .emit()
    });
}

/// The loader treats any spelling containing `.` as an explicit dylib path;
/// the path itself, rather than a backend-reported name, authenticates that
/// selection. Named backends must report the same identity they were selected
/// under. Keep Trust's historical underscore spelling as an input alias only.
pub(crate) fn expected_explicit_codegen_backend_name(requested: &str) -> Option<&str> {
    if requested.contains('.') {
        return None;
    }
    Some(if requested == "trust_cg" { "trust-cg" } else { requested })
}

pub(crate) fn explicit_codegen_backend_name_mismatch<'a>(
    requested: &'a str,
    actual: &str,
) -> Option<&'a str> {
    expected_explicit_codegen_backend_name(requested).filter(|expected| *expected != actual)
}

pub(crate) fn callback_codegen_backend_factory_conflicts(
    requested: Option<&str>,
    callback_factory: bool,
    trust_verification: bool,
    trust_ir_lower: bool,
) -> bool {
    callback_factory && (requested.is_some() || trust_verification || trust_ir_lower)
}

/// Marker selecting a current-invocation policy that cannot verify, lower, or
/// publish Trust evidence through compiler-managed codegen routes.
///
/// Compiler-owned entry points are process-tracked: an evidence-inert route is
/// rejected after a backend-capable compiler route and excludes concurrent
/// backend-capable compiler routes. Arbitrary host code that calls LLVM or a
/// backend directly remains outside that marker.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NoTrustEvidence;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FrontendTrustPolicy {
    CanonicalTrustc,
    EmbeddedNoOfficialEvidence,
    EvidenceInert,
}

impl FrontendTrustPolicy {
    fn deauthorizes_official_evidence(self) -> bool {
        self != Self::CanonicalTrustc
    }

    fn requires_evidence_inert_backend(self) -> bool {
        self == Self::EvidenceInert
    }

    fn compiler_backend_route(self) -> config::CompilerBackendRoute {
        if self.requires_evidence_inert_backend() {
            config::CompilerBackendRoute::EvidenceInert
        } else {
            config::CompilerBackendRoute::BackendCapable
        }
    }

    fn diagnostic_name(self) -> &'static str {
        match self {
            Self::CanonicalTrustc => "CanonicalTrustc",
            Self::EmbeddedNoOfficialEvidence => "EmbeddedNoOfficialEvidence",
            Self::EvidenceInert => "NoTrustEvidence",
        }
    }
}

pub(crate) fn no_trust_evidence_codegen_backend_error(
    requested: Option<&str>,
    effective_backend: &str,
    callback_factory: bool,
    builtin_available: bool,
) -> Option<String> {
    if callback_factory {
        Some(
            "NoTrustEvidence compiler frontend rejects callback-provided codegen backend factories"
                .to_string(),
        )
    } else if requested.is_some() {
        Some(
            "NoTrustEvidence compiler frontend rejects explicit -Zcodegen-backend selection"
                .to_string(),
        )
    } else if !matches!(effective_backend, "llvm" | "dummy") || !builtin_available {
        Some(format!(
            "NoTrustEvidence compiler frontend rejects effective codegen backend `{effective_backend}`; target and toolchain defaults must select an already-linked `llvm` or `dummy` backend"
        ))
    } else {
        None
    }
}

#[allow(rustc::bad_opt_access)]
pub(crate) fn apply_no_trust_evidence_typed_policy(
    opts: &mut config::Options,
) -> std::result::Result<(), String> {
    if let Some(option) =
        config::TrustFrontendAuthoritySnapshot::first_nondefault_evidence_control(opts)
    {
        return Err(option);
    }
    config::TrustFrontendAuthoritySnapshot::deauthorize(opts);
    Ok(())
}

#[allow(rustc::bad_opt_access)]
pub(crate) fn no_trust_evidence_typed_backend_control(
    opts: &config::Options,
) -> Option<&'static str> {
    config::evidence_inert_llvm_control(opts)
}

/// Run an embedded compiler configuration without granting it authority to
/// produce official Trust evidence. Custom backends and ordinary compiler
/// hooks remain available for tools such as rustdoc, Miri, and Kani.
// JUSTIFICATION: before session exists, only config
#[allow(rustc::bad_opt_access)]
pub fn run_compiler<R: Send>(config: Config, f: impl FnOnce(&Compiler) -> R + Send) -> R {
    run_compiler_with_frontend_trust_policy(
        config,
        FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
        f,
    )
}

/// Canonical Trust policy dispatch for `rustc_driver_impl`.
///
/// This symbol is public only because Rust has no friend-crate visibility. It
/// is routing, not proof authority: Targo must authenticate the exact executed
/// `trustc` image before treating any resulting evidence as official.
#[doc(hidden)]
// JUSTIFICATION: before session exists, only config
#[allow(rustc::bad_opt_access)]
pub fn run_compiler_with_canonical_trustc_policy_unchecked<R: Send>(
    config: Config,
    f: impl FnOnce(&Compiler) -> R + Send,
) -> R {
    run_compiler_with_frontend_trust_policy(config, FrontendTrustPolicy::CanonicalTrustc, f)
}

/// Run a caller-owned compiler configuration after forcibly deauthorizing
/// Trust verification, TrustIR publication, and non-builtin codegen backends.
/// The [`NoTrustEvidence`] process-isolation limitation applies.
// JUSTIFICATION: before session exists, only config
#[allow(rustc::bad_opt_access)]
pub fn run_compiler_with_no_trust_evidence<R: Send>(
    config: Config,
    _authority: NoTrustEvidence,
    f: impl FnOnce(&Compiler) -> R + Send,
) -> R {
    run_compiler_with_frontend_trust_policy(config, FrontendTrustPolicy::EvidenceInert, f)
}

/// Structural handoff from the guarded driver into the evidence-inert
/// interface implementation.
///
/// This symbol is public only because Rust has no friend-crate visibility. The
/// supplied one-shot token is consumed and checked so a backend-capable route
/// cannot be relabeled as evidence-inert or reused for a second invocation.
#[doc(hidden)]
// JUSTIFICATION: before session exists, only config
#[allow(rustc::bad_opt_access)]
pub fn run_compiler_with_no_trust_evidence_driver_handoff_unchecked<R: Send>(
    config: Config,
    _authority: NoTrustEvidence,
    route_guard: config::CompilerBackendRouteGuard,
    f: impl FnOnce(&Compiler) -> R + Send,
) -> R {
    let route = config::CompilerBackendRoute::EvidenceInert;
    if !route_guard.validates(route) {
        EarlyDiagCtxt::new(config.opts.error_format).early_fatal(
            "NoTrustEvidence driver handoff requires an evidence-inert compiler route guard",
        );
    }
    run_compiler_after_backend_route_transition(
        config,
        FrontendTrustPolicy::EvidenceInert,
        &route_guard,
        f,
    )
}

// JUSTIFICATION: before session exists, only config
#[allow(rustc::bad_opt_access)]
fn run_compiler_with_frontend_trust_policy<R: Send>(
    config: Config,
    frontend_trust_policy: FrontendTrustPolicy,
    f: impl FnOnce(&Compiler) -> R + Send,
) -> R {
    let compiler_backend_route_guard =
        config::enter_compiler_backend_route(frontend_trust_policy.compiler_backend_route())
            .unwrap_or_else(|error| {
                EarlyDiagCtxt::new(config.opts.error_format).early_fatal(error)
            });
    run_compiler_after_backend_route_transition(
        config,
        frontend_trust_policy,
        &compiler_backend_route_guard,
        f,
    )
}

// JUSTIFICATION: before session exists, only config
#[allow(rustc::bad_opt_access)]
fn run_compiler_after_backend_route_transition<R: Send>(
    mut config: Config,
    frontend_trust_policy: FrontendTrustPolicy,
    route_guard: &config::CompilerBackendRouteGuard,
    f: impl FnOnce(&Compiler) -> R + Send,
) -> R {
    debug_assert!(route_guard.validates(frontend_trust_policy.compiler_backend_route()));
    trace!("run_compiler");

    if frontend_trust_policy.deauthorizes_official_evidence() {
        let early_dcx = EarlyDiagCtxt::new(config.opts.error_format);
        if let Err(option) = apply_no_trust_evidence_typed_policy(&mut config.opts) {
            early_dcx.early_fatal(format!(
                "{} compiler frontend rejects typed Trust evidence control `{option}`",
                frontend_trust_policy.diagnostic_name(),
            ));
        }
        if frontend_trust_policy.requires_evidence_inert_backend()
            && let Some(option) = no_trust_evidence_typed_backend_control(&config.opts)
        {
            early_dcx.early_fatal(format!(
                "{} compiler frontend rejects LLVM backend control `{option}`",
                frontend_trust_policy.diagnostic_name(),
            ));
        }
        if let Some(key) = config::forbidden_no_official_evidence_environment_key(
            std::env::vars_os().map(|(key, _)| key),
        ) {
            early_dcx.early_fatal(config::trust_environment_error(&key));
        }
    }

    // Set parallel mode before thread pool creation, which will create `Lock`s.
    rustc_data_structures::sync::set_dyn_thread_safe_mode(
        config.opts.unstable_opts.threads.is_some(),
    );

    // Check jobserver before run_in_thread_pool_with_globals, which call jobserver::acquire_thread
    let early_dcx = EarlyDiagCtxt::new(config.opts.error_format);
    initialize_checked_jobserver(&early_dcx);

    if let Some(error) = config::trust_target_spec_binding_error(
        &config.opts.target_triple,
        config.opts.unstable_opts.trust_verify_target_spec_sha256.as_deref(),
        config.opts.unstable_opts.trust_verify_session.is_some(),
    ) {
        early_dcx.early_fatal(error);
    }

    crate::callbacks::setup_callbacks();

    let target = config::build_target_config(
        &early_dcx,
        &config.opts.target_triple,
        config.opts.sysroot.path(),
        config.opts.unstable_opts.unstable_options,
    );
    if frontend_trust_policy.requires_evidence_inert_backend() {
        if let Some(error) = config::evidence_inert_target_llvm_args_error(
            &config.opts.target_triple,
            !target.options.llvm_args.is_empty(),
        ) {
            early_dcx.early_fatal(error);
        }
        let requested = config.opts.unstable_opts.codegen_backend.as_deref();
        let effective_backend = util::effective_codegen_backend_name(requested, &target);
        if let Some(error) = no_trust_evidence_codegen_backend_error(
            requested,
            effective_backend,
            config.make_codegen_backend.is_some(),
            util::no_trust_evidence_builtin_backend_available(effective_backend),
        ) {
            early_dcx.early_fatal(error);
        }
    }
    // Cargo performs an early policy check for diagnostics, but only rustc has
    // the exact in-memory TargetTuple bytes it parsed. Recheck the resulting
    // semantic target inside the authenticated session so an A -> B -> A file
    // mutation cannot smuggle LLVM plugin arguments between Cargo's reads.
    if config.opts.unstable_opts.trust_verify_session.is_some()
        && !target.options.llvm_args.is_empty()
    {
        early_dcx.early_fatal(
            "authenticated Trust verification rejects non-empty custom-target `llvm-args`: LLVM plugin loading is outside the proof TCB",
        );
    }
    let file_loader = config.file_loader.unwrap_or_else(|| Box::new(RealFileLoader));
    let path_mapping = config.opts.file_path_mapping();
    let hash_kind = config.opts.unstable_opts.src_hash_algorithm(&target);
    let checksum_hash_kind = config.opts.unstable_opts.checksum_hash_algorithm();

    util::run_in_thread_pool_with_globals(
        &early_dcx,
        config.opts.edition,
        config.opts.unstable_opts.threads.unwrap_or(1),
        &config.extra_symbols,
        SourceMapInputs { file_loader, path_mapping, hash_kind, checksum_hash_kind },
        |current_gcx, jobserver_proxy| {
            // The previous `early_dcx` can't be reused here because it doesn't
            // impl `Send`. Creating a new one is fine.
            let early_dcx = EarlyDiagCtxt::new(config.opts.error_format);

            let temps_dir = config.opts.unstable_opts.temps_dir.as_deref().map(PathBuf::from);

            let mut sess = rustc_session::build_session(
                config.opts,
                CompilerIO {
                    input: config.input,
                    output_dir: config.output_dir,
                    output_file: config.output_file,
                    temps_dir,
                },
                config.lint_caps,
                target,
                util::rustc_version_str().unwrap_or("unknown"),
                config.ice_file,
                config.using_internal_features,
            );

            if frontend_trust_policy.deauthorizes_official_evidence() {
                let changed =
                    config::TrustFrontendAuthoritySnapshot::first_nondefault_evidence_control(
                        &sess.opts,
                    );
                if changed.is_some()
                    || sess.trust_verification_enabled()
                    || sess.trust_ir_lower_enabled()
                    || !sess.opts.trust_solver_content_fingerprint.is_empty()
                {
                    sess.dcx().fatal(format!(
                        "{} frontend deauthorization changed before backend construction{}",
                        frontend_trust_policy.diagnostic_name(),
                        changed.map_or_else(String::new, |option| format!(": `{option}`")),
                    ));
                }
                if let Some(key) = config::forbidden_no_official_evidence_environment_key(
                    std::env::vars_os().map(|(key, _)| key),
                ) {
                    sess.dcx().fatal(config::trust_environment_error(&key));
                }
            }

            // Do this immediately after Session construction, before even a
            // custom codegen backend can observe dependency hashes. The later
            // untracked-state finalizer is intentionally idempotent and keeps
            // direct Session tests/custom construction on the same path.
            if sess.trust_verification_enabled() {
                rustc_mir_transform::trust_initialize_ay_solver_identity(&mut sess);
            }

            let requested_codegen_backend = sess.opts.unstable_opts.codegen_backend.clone();
            let callback_codegen_backend = config.make_codegen_backend.is_some();
            if callback_codegen_backend_factory_conflicts(
                requested_codegen_backend.as_deref(),
                callback_codegen_backend,
                sess.trust_verification_enabled(),
                sess.trust_ir_lower_enabled(),
            ) {
                sess.dcx().fatal(
                    "a compiler callback cannot replace an explicit -Zcodegen-backend selection or select the backend while Trust verification or direct TrustIR lowering is active; remove the callback backend factory",
                );
            }

            let codegen_backend = if frontend_trust_policy.requires_evidence_inert_backend() {
                util::get_no_trust_evidence_codegen_backend(
                    sess.opts.unstable_opts.codegen_backend.as_deref(),
                    &sess.target,
                )
                .unwrap_or_else(|| {
                    sess.dcx().fatal(
                        "NoTrustEvidence backend selection changed after typed preflight; refusing external-backend fallback",
                    )
                })
            } else {
                match config.make_codegen_backend {
                    None => util::get_codegen_backend(
                        &early_dcx,
                        &sess.opts.sysroot,
                        sess.opts.unstable_opts.codegen_backend.as_deref(),
                        &sess.target,
                    ),
                    Some(make_codegen_backend) => {
                        // N.B. `make_codegen_backend` takes precedence over
                        // `target.default_codegen_backend`, which is ignored in this case.
                        make_codegen_backend(&sess)
                    }
                }
            };
            if let Some(requested) = requested_codegen_backend.as_deref()
                && let Some(expected) =
                    explicit_codegen_backend_name_mismatch(requested, codegen_backend.name())
            {
                sess.dcx().fatal(format!(
                    "explicit -Zcodegen-backend requested `{requested}` (canonical identity `{expected}`), but the selected backend reports `{}`",
                    codegen_backend.name(),
                ));
            }
            codegen_backend.init(&sess);
            sess.replaced_intrinsics = FxHashSet::from_iter(codegen_backend.replaced_intrinsics());
            sess.fallback_intrinsics = FxHashSet::from_iter(codegen_backend.fallback_intrinsics());
            sess.thin_lto_supported = codegen_backend.thin_lto_supported();

            let cfg = parse_cfg(sess.dcx(), config.crate_cfg);
            let mut cfg = config::build_configuration(&sess, cfg);
            util::add_configuration(&mut cfg, &mut sess, &*codegen_backend);
            sess.config = cfg;

            let mut check_cfg = parse_check_cfg(sess.dcx(), config.crate_check_cfg);
            check_cfg.fill_well_known(&sess.target);
            sess.check_config = check_cfg;

            if let Some(psess_created) = config.psess_created {
                psess_created(&mut sess.psess);
            }

            finalize_untracked_session_state(&mut sess, config.track_state);

            // Even though the session holds the lint store, we can't build the
            // lint store until after the session exists. And we wait until now
            // so that `register_lints` sees the fully initialized session.
            let mut lint_store = rustc_lint::new_lint_store(sess.enable_internal_lints());
            if let Some(register_lints) = config.register_lints.as_deref() {
                register_lints(&sess, &mut lint_store);
            }
            sess.lint_store = Some(Arc::new(lint_store));

            util::check_abi_required_features(&sess);

            let compiler = Compiler {
                sess,
                codegen_backend,
                override_queries: config.override_queries,
                current_gcx,
                jobserver_proxy,
            };

            // There are two paths out of `f`.
            // - Normal exit.
            // - Panic, e.g. triggered by `abort_if_errors` or a fatal error.
            //
            // We must run `finish_diagnostics` in both cases.
            let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(&compiler)));

            compiler.sess.finish_diagnostics();

            // If error diagnostics have been emitted, we can't return an
            // error directly, because the return type of this function
            // is `R`, not `Result<R, E>`. But we need to communicate the
            // errors' existence to the caller, otherwise the caller might
            // mistakenly think that no errors occurred and return a zero
            // exit code. So we abort (panic) instead, similar to if `f`
            // had panicked.
            if res.is_ok() {
                compiler.sess.dcx().abort_if_errors();
            }

            // Also make sure to flush delayed bugs as if we panicked, the
            // bugs would be flushed by the Drop impl of DiagCtxt while
            // unwinding, which would result in an abort with
            // "panic in a destructor during cleanup".
            compiler.sess.dcx().flush_delayed();

            let res = match res {
                Ok(res) => res,
                // Resume unwinding if a panic happened.
                Err(err) => std::panic::resume_unwind(err),
            };

            let prof = compiler.sess.prof.clone();
            prof.generic_activity("drop_compiler").run(move || drop(compiler));

            res
        },
    )
}

pub fn try_print_query_stack(
    dcx: DiagCtxtHandle<'_>,
    limit_frames: Option<usize>,
    file: Option<std::fs::File>,
) {
    eprintln!("query stack during panic:");

    // Be careful relying on global state here: this code is called from
    // a panic hook, which means that the global `DiagCtxt` may be in a weird
    // state if it was responsible for triggering the panic.
    let all_frames = ty::tls::with_context_opt(|icx| {
        if let Some(icx) = icx {
            ty::print::with_no_queries!(print_query_stack(
                icx.tcx,
                icx.query,
                dcx,
                limit_frames,
                file,
            ))
        } else {
            0
        }
    });

    if let Some(limit_frames) = limit_frames
        && all_frames > limit_frames
    {
        eprintln!(
            "... and {} other queries... use `env RUST_BACKTRACE=1` to see the full query stack",
            all_frames - limit_frames
        );
    } else {
        eprintln!("end of query stack");
    }
}
