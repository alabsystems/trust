// ignore-tidy-file-filelength (Trust: the -Z trust-* options)
use std::collections::BTreeMap;
use std::num::{IntErrorKind, NonZero};
use std::path::PathBuf;
use std::str;

use rustc_abi::Align;
use rustc_ast::attr::version::RustcVersion;
use rustc_data_structures::fx::FxIndexMap;
use rustc_data_structures::profiling::TimePassesFormat;
use rustc_data_structures::stable_hash::StableHasher;
use rustc_errors::{ColorConfig, TerminalUrl};
use rustc_feature::UnstableFeatures;
use rustc_hashes::Hash64;
use rustc_macros::{BlobDecodable, Encodable};
use rustc_span::edit_distance::edit_distance;
use rustc_span::edition::Edition;
use rustc_span::{RealFileName, RemapPathScopeComponents, SourceFileHashAlgorithm};
use rustc_structures::{CollapseMacroDebuginfo, CrateType};
use rustc_target::spec::{
    CodeModel, FramePointer, LinkerFlavorCli, MergeFunctions, OnBrokenPipe, PanicStrategy,
    RelocModel, RelroLevel, SanitizerSet, SplitDebuginfo, StackProtector, SymbolVisibility,
    TargetTuple, TlsModel,
};

use crate::config::*;
use crate::search_paths::SearchPath;
use crate::utils::NativeLib;
use crate::{EarlyDiagCtxt, Session, lint};

macro_rules! insert {
    ($opt_name:ident, $opt_expr:expr, $sub_hashes:expr) => {
        if $sub_hashes
            .insert(stringify!($opt_name), $opt_expr as &dyn dep_tracking::DepTrackingHash)
            .is_some()
        {
            panic!("duplicate key in CLI DepTrackingHash: {}", stringify!($opt_name))
        }
    };
}

macro_rules! hash_opt {
    ($opt_name:ident, $opt_expr:expr, $sub_hashes:expr, $_for_crate_hash: ident, [UNTRACKED]) => {{}};
    ($opt_name:ident, $opt_expr:expr, $sub_hashes:expr, $_for_crate_hash: ident, [TRACKED]) => {{ insert!($opt_name, $opt_expr, $sub_hashes) }};
    ($opt_name:ident, $opt_expr:expr, $sub_hashes:expr, $for_crate_hash: ident, [TRACKED_NO_CRATE_HASH]) => {{
        if !$for_crate_hash {
            insert!($opt_name, $opt_expr, $sub_hashes)
        }
    }};
    ($opt_name:ident, $opt_expr:expr, $sub_hashes:expr, $_for_crate_hash: ident, [SUBSTRUCT]) => {{}};
}

macro_rules! hash_substruct {
    ($opt_name:ident, $opt_expr:expr, $error_format:expr, $for_crate_hash:expr, $hasher:expr, [UNTRACKED]) => {{}};
    ($opt_name:ident, $opt_expr:expr, $error_format:expr, $for_crate_hash:expr, $hasher:expr, [TRACKED]) => {{}};
    ($opt_name:ident, $opt_expr:expr, $error_format:expr, $for_crate_hash:expr, $hasher:expr, [TRACKED_NO_CRATE_HASH]) => {{}};
    ($opt_name:ident, $opt_expr:expr, $error_format:expr, $for_crate_hash:expr, $hasher:expr, [SUBSTRUCT]) => {{
        use crate::config::dep_tracking::DepTrackingHash;
        $opt_expr.dep_tracking_hash($for_crate_hash, $error_format).hash(
            $hasher,
            $error_format,
            $for_crate_hash,
        );
    }};
}

/// Extended target modifier info.
/// For example, when external target modifier is '-Zregparm=2':
/// Target modifier enum value + user value ('2') from external crate
/// is converted into description: prefix ('Z'), name ('regparm'), tech value ('Some(2)').
pub struct ExtendedTargetModifierInfo {
    /// Flag prefix (usually, 'C' for codegen flags or 'Z' for unstable flags)
    pub prefix: String,
    /// Flag name
    pub name: String,
    /// Flag parsed technical value
    pub tech_value: String,
}

/// A recorded -Zopt_name=opt_value (or -Copt_name=opt_value)
/// which alter the ABI or effectiveness of exploit mitigations.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Encodable, BlobDecodable)]
pub struct TargetModifier {
    /// Option enum value
    pub opt: OptionsTargetModifiers,
    /// User-provided option value (before parsing)
    pub value_name: String,
}

pub mod mitigation_coverage;

mod target_modifier_consistency_check {
    use super::*;
    pub(super) fn sanitizer(
        sess: &Session,
        l: &TargetModifier,
        r: Option<&TargetModifier>,
    ) -> bool {
        let mut lparsed: SanitizerSet = SanitizerSet::empty();
        let lval = if l.value_name.is_empty() { None } else { Some(l.value_name.as_str()) };
        parse::parse_sanitizers(&mut lparsed, lval);
        let lparsed = lparsed.combine_with_defaults(sess.target.options.default_sanitizers);

        let mut rparsed: SanitizerSet = SanitizerSet::empty();
        let rval = r.filter(|v| !v.value_name.is_empty()).map(|v| v.value_name.as_str());
        parse::parse_sanitizers(&mut rparsed, rval);
        let rparsed = rparsed.combine_with_defaults(sess.target.options.default_sanitizers);

        // Some sanitizers need to be target modifiers, and some do not.
        // For now, we should mark all sanitizers as target modifiers except for these:
        // AddressSanitizer, LeakSanitizer
        let tmod_sanitizers = SanitizerSet::MEMORY
            | SanitizerSet::THREAD
            | SanitizerSet::HWADDRESS
            | SanitizerSet::CFI
            | SanitizerSet::MEMTAG
            | SanitizerSet::SHADOWCALLSTACK
            | SanitizerSet::KCFI
            | SanitizerSet::KERNELADDRESS
            | SanitizerSet::KERNELHWADDRESS
            | SanitizerSet::SAFESTACK
            | SanitizerSet::DATAFLOW;

        lparsed & tmod_sanitizers == rparsed & tmod_sanitizers
    }
    pub(super) fn sanitizer_cfi_normalize_integers(
        sess: &Session,
        l: &TargetModifier,
        r: Option<&TargetModifier>,
    ) -> bool {
        // For kCFI, the helper flag -Zsanitizer-cfi-normalize-integers should also be a target modifier
        if sess.sanitizers().contains(SanitizerSet::KCFI) {
            if let Some(r) = r {
                return l.extend().tech_value == r.extend().tech_value;
            } else {
                return false;
            }
        }
        true
    }
    pub(super) fn sanitizer_cfi_minimal_runtime(
        sess: &Session,
        l: &TargetModifier,
        r: Option<&TargetModifier>,
    ) -> bool {
        // For CFI, the helper flag -Zsanitizer-cfi-minimal-runtime should also be a target modifier
        if sess.sanitizers().contains(SanitizerSet::CFI) {
            if let Some(r) = r {
                return l.extend().tech_value == r.extend().tech_value;
            } else {
                return false;
            }
        }
        true
    }
    pub(super) fn target_cpu(
        sess: &Session,
        l: &TargetModifier,
        r: Option<&TargetModifier>,
    ) -> bool {
        if !sess.target.requires_consistent_cpu {
            return true;
        }
        let l_tech_value = l.extend().tech_value;
        let r_tech_value = match r {
            Some(r) => r.extend().tech_value,
            // If only one of the two compared crates specifies the CPU
            // explicitly we compare against the target's default CPU.
            None => {
                // We reuse the same parsing logic.
                CodegenOptionsTargetModifiers::TargetCpu
                    .reparse(sess.target.cpu.as_ref())
                    .tech_value
            }
        };
        l_tech_value == r_tech_value
    }
}

impl TargetModifier {
    pub fn extend(&self) -> ExtendedTargetModifierInfo {
        self.opt.reparse(&self.value_name)
    }
    // Custom consistency check for target modifiers (or default `l.tech_value == r.tech_value`)
    // When other is None, consistency with default value is checked
    pub fn consistent(&self, sess: &Session, other: Option<&TargetModifier>) -> bool {
        assert!(other.is_none() || self.opt == other.unwrap().opt);
        match self.opt {
            OptionsTargetModifiers::UnstableOptions(unstable) => match unstable {
                UnstableOptionsTargetModifiers::Sanitizer => {
                    return target_modifier_consistency_check::sanitizer(sess, self, other);
                }
                UnstableOptionsTargetModifiers::SanitizerCfiNormalizeIntegers => {
                    return target_modifier_consistency_check::sanitizer_cfi_normalize_integers(
                        sess, self, other,
                    );
                }
                UnstableOptionsTargetModifiers::SanitizerCfiMinimalRuntime => {
                    return target_modifier_consistency_check::sanitizer_cfi_minimal_runtime(
                        sess, self, other,
                    );
                }
                _ => {}
            },
            OptionsTargetModifiers::CodegenOptions(codegen) => match codegen {
                CodegenOptionsTargetModifiers::TargetCpu => {
                    return target_modifier_consistency_check::target_cpu(sess, self, other);
                }
            },
        };
        match other {
            Some(other) => self.extend().tech_value == other.extend().tech_value,
            None => false,
        }
    }
}

fn tmod_push_impl(
    opt: OptionsTargetModifiers,
    tmod_vals: &BTreeMap<OptionsTargetModifiers, String>,
    tmods: &mut Vec<TargetModifier>,
) {
    if let Some(v) = tmod_vals.get(&opt) {
        tmods.push(TargetModifier { opt, value_name: v.clone() })
    }
}

macro_rules! top_level_options {
    (
        $(#[$top_level_attr:meta])*
        pub struct Options {
            $(
                $(#[$attr:meta])*
                $opt:ident : $t:ty
                [$dep_tracking_marker:ident]
                $( { TARGET_MODIFIER: $tmod_variant:ident($tmod_enum:ident) } )?
                ,
            )*
        }
    ) => {
        #[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Copy, Clone, Encodable, BlobDecodable)]
        pub enum OptionsTargetModifiers {
            $(
                $(
                    $tmod_variant($tmod_enum),
                )?
            )*
        }

        impl OptionsTargetModifiers {
            pub fn reparse(&self, user_value: &str) -> ExtendedTargetModifierInfo {
                match self {
                    $(
                        $(
                            Self::$tmod_variant(v) => v.reparse(user_value),
                        )?
                    )*
                    #[allow(unreachable_patterns)]
                    _ => panic!("unknown target modifier option: {self:?}"),
                }
            }

            pub fn is_target_modifier(flag_name: &str) -> bool {
                $(
                    $(
                        if $tmod_enum::is_target_modifier(flag_name) {
                            return true
                        }
                    )?
                )*
                false
            }
        }

        #[derive(Clone)]
        $(#[$top_level_attr])*
        pub struct Options {
            $(
                $(#[$attr])*
                pub $opt: $t,
            )*
            pub target_modifiers: BTreeMap<OptionsTargetModifiers, String>,
            pub mitigation_coverage_map: mitigation_coverage::MitigationCoverageMap,
        }

        impl Options {
            pub fn dep_tracking_hash(&self, for_crate_hash: bool) -> Hash64 {
                let mut sub_hashes = BTreeMap::new();
                $(
                    hash_opt!(
                        $opt,
                        &self.$opt,
                        &mut sub_hashes,
                        for_crate_hash,
                        [$dep_tracking_marker]
                    );
                )*
                let mut hasher = StableHasher::new();
                dep_tracking::stable_hash(
                    sub_hashes,
                    &mut hasher,
                    self.error_format,
                    for_crate_hash,
                );
                $(
                    hash_substruct!(
                        $opt,
                        &self.$opt,
                        self.error_format,
                        for_crate_hash,
                        &mut hasher,
                        [$dep_tracking_marker]
                    );
                )*
                hasher.finish()
            }

            pub fn gather_target_modifiers(&self) -> Vec<TargetModifier> {
                let mut mods = Vec::<TargetModifier>::new();
                $(
                    $(
                        // Only expand for flags that have `TARGET_MODIFIER`.
                        ${ignore($tmod_enum)}
                        self.$opt.gather_target_modifiers(&mut mods, &self.target_modifiers);
                    )?
                )*
                mods.sort_by(|a, b| a.opt.cmp(&b.opt));
                mods
            }
        }
    }
}

top_level_options!(
    /// The top-level command-line options struct.
    ///
    /// For each option, one has to specify how it behaves with regard to the
    /// dependency tracking system of incremental compilation. This is done via the
    /// square-bracketed directive after the field type. The options are:
    ///
    /// - `[TRACKED]`
    /// A change in the given field will cause the compiler to completely clear the
    /// incremental compilation cache before proceeding.
    ///
    /// - `[TRACKED_NO_CRATE_HASH]`
    /// Same as `[TRACKED]`, but will not affect the crate hash. This is useful for options that
    /// only affect the incremental cache.
    ///
    /// - `[UNTRACKED]`
    /// Incremental compilation is not influenced by this option.
    ///
    /// - `[SUBSTRUCT]`
    /// Second-level sub-structs containing more options.
    ///
    /// If you add a new option to this struct or one of the sub-structs like
    /// `CodegenOptions`, think about how it influences incremental compilation. If in
    /// doubt, specify `[TRACKED]`, which is always "correct" but might lead to
    /// unnecessary re-compilation.
    #[rustc_lint_opt_ty]
    pub struct Options {
        /// The crate config requested for the session, which may be combined
        /// with additional crate configurations during the compile process.
        #[rustc_lint_opt_deny_field_access("use `TyCtxt::crate_types` instead of this field")]
        crate_types: Vec<CrateType> [TRACKED],
        optimize: OptLevel [TRACKED],
        /// Include the `debug_assertions` flag in dependency tracking, since it
        /// can influence whether overflow checks are done or not.
        debug_assertions: bool [TRACKED],
        debuginfo: DebugInfo [TRACKED],
        lint_opts: Vec<(String, lint::Level)> [TRACKED_NO_CRATE_HASH],
        lint_cap: Option<lint::Level> [TRACKED_NO_CRATE_HASH],
        describe_lints: bool [UNTRACKED],
        output_types: OutputTypes [TRACKED],
        search_paths: Vec<SearchPath> [UNTRACKED],
        libs: Vec<NativeLib> [TRACKED],
        sysroot: Sysroot [UNTRACKED],

        target_triple: TargetTuple [TRACKED],

        /// Effective logical environment used by `env!`/`option_env!` macros
        logical_env: FxIndexMap<String, String> [TRACKED],

        test: bool [TRACKED],
        error_format: ErrorOutputType [UNTRACKED],
        diagnostic_width: Option<usize> [UNTRACKED],

        /// If `Some`, enable incremental compilation, using the given
        /// directory to store intermediate results.
        incremental: Option<PathBuf> [UNTRACKED],

        /// Fresh verifier invocation identity. It participates in incremental
        /// query hashing but not downstream crate hashes, preventing proof
        /// diagnostics from being reused across compiler processes.
        untracked_state_hash: Hash64 [TRACKED_NO_CRATE_HASH],

        /// Trust (loud-when-off): set when OFF reached the canonical frontend
        /// through the caller's own `-Ztrust-verify=off` argv spelling OR the
        /// inherited `TRUST_NO_VERIFY=1` nested-process transport — never by
        /// embedded/doctest frontend deauthorization. An announced parent
        /// (bootstrap, compiletest) quiets the downstream note with the
        /// `TRUST_VANILLA_ANNOUNCED=1` marker, not by leaving this bit clear;
        /// a bare-shell `TRUST_NO_VERIFY=1 trustc x.rs` therefore announces
        /// (it used to check nothing and say nothing). Drives only the
        /// once-per-crate "compiled WITHOUT Trust verification" note, so it is
        /// untracked.
        trust_verify_explicit_off: bool [UNTRACKED],

        unstable_opts: UnstableOptions [SUBSTRUCT] { TARGET_MODIFIER: UnstableOptions(UnstableOptionsTargetModifiers) },
        prints: Vec<PrintRequest> [UNTRACKED],
        cg: CodegenOptions [SUBSTRUCT] { TARGET_MODIFIER: CodegenOptions(CodegenOptionsTargetModifiers) },
        externs: Externs [UNTRACKED],
        crate_name: Option<String> [TRACKED],
        /// Indicates how the compiler should treat unstable features.
        unstable_features: UnstableFeatures [TRACKED],

        /// Indicates whether this run of the compiler is actually rustdoc. This
        /// is currently just a hack and will be removed eventually, so please
        /// try to not rely on this too much.
        actually_rustdoc: bool [TRACKED],
        /// Whether name resolver should resolve documentation links.
        resolve_doc_links: ResolveDocLinks [TRACKED],

        /// Control path trimming.
        trimmed_def_paths: bool [TRACKED],

        /// Specifications of codegen units / ThinLTO which are forced as a
        /// result of parsing command line options. These are not necessarily
        /// what rustc was invoked with, but massaged a bit to agree with
        /// commands like `--emit llvm-ir` which they're often incompatible with
        /// if we otherwise use the defaults of rustc.
        #[rustc_lint_opt_deny_field_access("use `Session::codegen_units` instead of this field")]
        cli_forced_codegen_units: Option<usize> [UNTRACKED],
        #[rustc_lint_opt_deny_field_access("use `Session::lto` instead of this field")]
        cli_forced_local_thinlto_off: bool [UNTRACKED],

        /// Remap source path prefixes in all output (messages, object files, debug, etc.).
        remap_path_prefix: Vec<(PathBuf, PathBuf)> [TRACKED_NO_CRATE_HASH],
        /// Defines which scopes of paths should be remapped by `--remap-path-prefix`.
        remap_path_scope: RemapPathScopeComponents [TRACKED_NO_CRATE_HASH],

        /// Base directory containing the `library/` directory for the Rust standard library.
        /// Right now it's always `$sysroot/lib/rustlib/src/rust`
        /// (i.e. the `rustup` `rust-src` component).
        ///
        /// This directory is what the virtual `/rustc/$hash` is translated back to,
        /// if Rust was built with path remapping to `/rustc/$hash` enabled
        /// (the `rust.remap-debuginfo` option in `bootstrap.toml`).
        real_rust_source_base_dir: Option<PathBuf> [TRACKED_NO_CRATE_HASH],

        /// Base directory containing the `compiler/` directory for the rustc sources.
        /// Right now it's always `$sysroot/lib/rustlib/rustc-src/rust`
        /// (i.e. the `rustup` `rustc-dev` component).
        ///
        /// This directory is what the virtual `/rustc-dev/$hash` is translated back to,
        /// if Rust was built with path remapping to `/rustc/$hash` enabled
        /// (the `rust.remap-debuginfo` option in `bootstrap.toml`).
        real_rustc_dev_source_base_dir: Option<PathBuf> [TRACKED_NO_CRATE_HASH],

        edition: Edition [TRACKED],

        /// `true` if we're emitting JSON blobs about each artifact produced
        /// by the compiler.
        json_artifact_notifications: bool [TRACKED],

        /// `true` if we're emitting JSON timings with the start and end of
        /// high-level compilation sections
        json_timings: bool [UNTRACKED],

        /// `true` if we're emitting a JSON blob containing the unused externs
        json_unused_externs: JsonUnusedExterns [UNTRACKED],

        /// `true` if we're emitting a JSON job containing a future-incompat report for lints
        json_future_incompat: bool [TRACKED],

        pretty: Option<PpMode> [UNTRACKED],

        /// The (potentially remapped) working directory
        #[rustc_lint_opt_deny_field_access("use `SourceMap::working_dir` instead of this field")]
        working_dir: RealFileName [TRACKED],
        color: ColorConfig [UNTRACKED],
        verbose: bool [TRACKED_NO_CRATE_HASH],
        jobs: Jobs [UNTRACKED],
        // Trust: mandatory per-unit runtime CPU ownership handshake.
        resource_worker_v2: bool [UNTRACKED],
        resource_worker_v3: bool [UNTRACKED],
        resource_subgroups_v3: bool [UNTRACKED],
        // Trust: routing DATA; only the actual private native issuer admits it.
        resource_bootstrap_fixed_v1: bool [UNTRACKED],
        recommended_stack_size: usize [UNTRACKED],
    }
);

#[derive(Default)]
pub struct CollectedOptions {
    pub target_modifiers: BTreeMap<OptionsTargetModifiers, String>,
    pub mitigations: mitigation_coverage::MitigationCoverageMap,
}

macro_rules! setter_for {
    // the allow/deny-mitigations options use collected/index instead of the cg, since they
    // work across option groups
    (allow_partial_mitigations, $struct_name:ident, $parse:ident) => {
        pub(super) fn allow_partial_mitigations(
            _cg: &mut super::$struct_name,
            collected: &mut super::CollectedOptions,
            v: Option<&str>,
            index: usize,
        ) -> bool {
            collected.mitigations.handle_allowdeny_mitigation_option(v, index, true)
        }
    };
    (deny_partial_mitigations, $struct_name:ident, $parse:ident) => {
        pub(super) fn deny_partial_mitigations(
            _cg: &mut super::$struct_name,
            collected: &mut super::CollectedOptions,
            v: Option<&str>,
            index: usize,
        ) -> bool {
            collected.mitigations.handle_allowdeny_mitigation_option(v, index, false)
        }
    };
    ($opt:ident, $struct_name:ident, $parse:ident) => {
        pub(super) fn $opt(
            cg: &mut super::$struct_name,
            _collected: &mut super::CollectedOptions,
            v: Option<&str>,
            _index: usize,
        ) -> bool {
            super::parse::$parse(&mut redirect_field!(cg.$opt), v)
        }
    };
}

/// Trust: how an option participates in the frontend-authority boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustAuthorityClass {
    /// A compiler callback may not change it, but a deauthorized embedded
    /// frontend inherits whatever it finds, because deauthorization overwrites
    /// the field outright rather than trusting the incoming value.
    AuthorityOnly,
    /// Additionally: a deauthorized embedded frontend may not inherit a
    /// non-default EFFECTIVE value, because a caller that set one has already
    /// claimed authority over the evidence or the code this compilation
    /// produces, and a frontend that produces no evidence can neither honour it
    /// nor silently drop it. Either its effect does NOT depend on verification
    /// or lowering running (an artifact sink, a session identity, a
    /// codegen-backend or runtime-monitor control, the Clean-origin emitter
    /// mutation, the typeck-witness lane), or it is an adversarial or
    /// measurement control whose entire purpose is an observable outcome — a
    /// refusal, a warning, a probe line — that dropping it would fake.
    EvidenceControl,
    /// A selector of the verification POSTURE: every effect it has is
    /// conditional on an ACTIVE verification run or on ACTIVE direct Trust-IR
    /// lowering (`Session::trust_ir_lower_enabled`), both of which an
    /// evidence-deauthorized frontend forces off. It produces no artifact,
    /// obligation, verdict or emitted-code change of its own. A
    /// compiler callback may not change it (the authority snapshot compares
    /// every classified field), and an evidence-deauthorized frontend — which
    /// forces verification and lowering off — ACCEPTS any caller value and
    /// resets it to its declared default
    /// ([`crate::config::TrustFrontendAuthoritySnapshot::deauthorize`]), so nothing
    /// downstream can read a posture (a `certify` policy, a proof level, a
    /// hardened profile) that such a frontend cannot honour. This is how a
    /// project's committed posture (`-Ztrust-verify=on -Ztrust-policy=certify
    /// -Ztrust-verify-level=2 …`) can reach `tippy-driver` and `trustdoc`
    /// alongside the effective `-Ztrust-verify=off` Targo appends for them.
    ///
    /// A selector that ALSO carries a non-verification effect may only be
    /// classified here if deauthorization first materializes that effect into
    /// the upstream option that owns it, so the neutralized configuration
    /// compiles exactly what the caller's did: `-Ztrust-verify-profile`'s
    /// declared SIGPIPE disposition becomes `-Zon-broken-pipe`
    /// ([`crate::trust_effective_on_broken_pipe_by_flags`]).
    VerificationSelector,
}

impl TrustAuthorityClass {
    pub const fn is_evidence_control(self) -> bool {
        matches!(self, Self::EvidenceControl)
    }

    pub const fn is_verification_selector(self) -> bool {
        matches!(self, Self::VerificationSelector)
    }
}

/// Trust: one authority-bearing option, as declared by the option table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrustAuthorityControl {
    /// The struct field name, in the table's `snake_case` spelling.
    pub field: &'static str,
    /// The option-class letter the table is parsed under (`Z`, `C`).
    pub prefix: &'static str,
    pub class: TrustAuthorityClass,
}

impl TrustAuthorityControl {
    pub fn spelling(&self) -> String {
        trust_authority_spelling(self.prefix, self.field)
    }
}

fn trust_authority_spelling(prefix: &str, field: &str) -> String {
    format!("-{prefix}{}", field.replace('_', "-"))
}

/// Trust: whether an option field name is part of the Trust surface and must
/// therefore declare an authority class. Deliberately a `const fn` over bytes:
/// the check runs in a `const` block per table entry, so an unregistered Trust
/// option cannot reach a built compiler.
const fn trust_authority_classification_required(field: &str) -> bool {
    let field = field.as_bytes();
    let prefix = b"trust_";
    if field.len() < prefix.len() {
        return false;
    }
    let mut index = 0;
    while index < prefix.len() {
        if field[index] != prefix[index] {
            return false;
        }
        index += 1;
    }
    true
}

/// Defines all `CodegenOptions`/`DebuggingOptions` fields and parsers all at once. The goal of this
/// macro is to define an interface that can be programmatically used by the option parser
/// to initialize the struct without hardcoding field names all over the place.
///
/// The goal is to invoke this macro once with the correct fields, and then this macro generates all
/// necessary code. The main gotcha of this macro is the `cgsetters` module which is a bunch of
/// generated code to parse an option into its respective field in the struct. There are a few
/// hand-written parsers for parsing specific types of values in this module.
macro_rules! options {
    (
        $struct_name:ident,
        $tmod_enum:ident,
        $stat:ident,
        $optmod:ident,
        $prefix:expr,
        $outputname:expr,

        $(
            $(#[$attr:meta])*
            $opt:ident : $t:ty = (
                $init:expr,
                $parse:ident,
                [$dep_tracking_marker:ident]
                $( { TARGET_MODIFIER: $tmod_variant:ident } )?
                $( { MITIGATION: $mitigation_variant:ident } )?
                $( { TRUST_AUTHORITY: $trust_authority:ident } )?
                ,
                $desc:expr
                $(, removed: $removed:ident )?
            ),
        )*
    ) => {
        #[derive(Clone)]
        #[rustc_lint_opt_ty]
        pub struct $struct_name {
            $(
                $(#[$attr])*
                pub $opt: $t,
            )*
        }

        #[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Copy, Clone, Encodable, BlobDecodable)]
        pub enum $tmod_enum {
            $(
                $( $tmod_variant, )?
            )*
        }

        impl $tmod_enum {
            pub fn reparse(&self, _user_value: &str) -> ExtendedTargetModifierInfo {
                match self {
                    $(
                        $(
                            Self::$tmod_variant => {
                                let mut parsed: $t = Default::default();
                                let val = if _user_value.is_empty() { None } else { Some(_user_value) };
                                parse::$parse(&mut parsed, val);
                                ExtendedTargetModifierInfo {
                                    prefix: $prefix.to_string(),
                                    name: stringify!($opt).to_string().replace('_', "-"),
                                    tech_value: format!("{:?}", parsed),
                                }
                            }
                        )?
                    )*

                    #[allow(unreachable_patterns)]
                    _ => panic!("unknown target modifier option: {:?}", *self)
                }
            }

            pub fn is_target_modifier(flag_name: &str) -> bool {
                match flag_name.replace('-', "_").as_str() {
                    $(
                        $(
                            // Only expand for flags that have `TARGET_MODIFIER`.
                            ${ignore($tmod_variant)}
                            stringify!($opt) => true,
                        )?
                    )*
                    _ => false,
                }
            }
        }

        impl Default for $struct_name {
            fn default() -> $struct_name {
                $struct_name {
                    $(
                        $opt: $init,
                    )*
                }
            }
        }

        impl $struct_name {
            pub fn build(
                early_dcx: &EarlyDiagCtxt,
                matches: &getopts::Matches,
                target_modifiers: &mut CollectedOptions,
            ) -> $struct_name {
                build_options(early_dcx, matches, target_modifiers, $stat, $prefix, $outputname)
            }

            /// Trust: the EFFECTIVE values of exactly the frontend-authority
            /// controls (`TRUST_AUTHORITY_CONTROLS`) that `matches` spells —
            /// parsed by this table's own setters in argv order, so a later
            /// occurrence overrides an earlier one precisely as in [`Self::build`]
            /// — together with the fields that were spelled at all. Every other
            /// option is neither parsed nor diagnosed here and stays at its
            /// default: the full [`Self::build`] still runs, once, for the
            /// compilation, so an unrelated option (`-Zhelp`, a removed option's
            /// warning) is not answered twice or ahead of its own early mode. A
            /// malformed value of a classified option is the same fatal error the
            /// full parse raises.
            ///
            /// An evidence-deauthorized frontend decides its Trust options on this
            /// answer instead of on individual occurrences
            /// (`rustc_driver_impl::frontend_forbidden_option`).
            pub fn build_trust_authority_controls(
                early_dcx: &EarlyDiagCtxt,
                matches: &getopts::Matches,
            ) -> ($struct_name, Vec<&'static str>) {
                let mut spelled = Vec::new();
                let effective = build_options_selected(
                    early_dcx,
                    matches,
                    &mut CollectedOptions::default(),
                    $stat,
                    $prefix,
                    $outputname,
                    |name| {
                        let control = Self::TRUST_AUTHORITY_CONTROLS
                            .iter()
                            .find(|control| control.field == name);
                        if let Some(control) = control
                            && !spelled.contains(&control.field)
                        {
                            spelled.push(control.field);
                        }
                        control.is_some()
                    },
                );
                (effective, spelled)
            }

            fn dep_tracking_hash(
                &self,
                for_crate_hash: bool,
                error_format: ErrorOutputType,
            ) -> Hash64 {
                let mut sub_hashes = BTreeMap::new();
                $(
                    hash_opt!(
                        $opt,
                        &self.$opt,
                        &mut sub_hashes,
                        for_crate_hash,
                        [$dep_tracking_marker]
                    );
                )*
                let mut hasher = StableHasher::new();
                dep_tracking::stable_hash(
                    sub_hashes,
                    &mut hasher,
                    error_format,
                    for_crate_hash,
                );
                hasher.finish()
            }

            pub fn gather_target_modifiers(
                &self,
                _mods: &mut Vec<TargetModifier>,
                _tmod_vals: &BTreeMap<OptionsTargetModifiers, String>,
            ) {
                $(
                    $(
                        if self.$opt != $init {
                            tmod_push_impl(
                                OptionsTargetModifiers::$struct_name($tmod_enum::$tmod_variant),
                                _tmod_vals,
                                _mods,
                            );
                        }
                    )?
                )*
            }

            /// Trust: every option in this table that carries frontend
            /// authority, in declaration order. Derived from the table so the
            /// authority boundary and the option surface cannot disagree.
            pub const TRUST_AUTHORITY_CONTROLS: &'static [TrustAuthorityControl] = &[
                $(
                    $(
                        TrustAuthorityControl {
                            field: stringify!($opt),
                            prefix: $prefix,
                            class: TrustAuthorityClass::$trust_authority,
                        },
                    )?
                )*
            ];

            /// Trust: the first authority-bearing option whose value differs
            /// between two configurations of this table.
            pub fn first_changed_trust_authority(&self, _other: &Self) -> Option<String> {
                $(
                    $(
                        ${ignore($trust_authority)}
                        if self.$opt != _other.$opt {
                            return Some(
                                trust_authority_spelling($prefix, stringify!($opt))
                            );
                        }
                    )?
                )*
                None
            }

            /// Trust: the first EVIDENCE-class control this configuration
            /// populated away from its declared default. Authority-only
            /// controls are excluded: their safe-to-inherit state is whatever a
            /// deauthorized frontend overwrites them with, not the default.
            pub fn first_nondefault_trust_evidence_control(&self) -> Option<String> {
                $(
                    $(
                        if TrustAuthorityClass::$trust_authority.is_evidence_control()
                            && self.$opt != $init
                        {
                            return Some(
                                trust_authority_spelling($prefix, stringify!($opt))
                            );
                        }
                    )?
                )*
                None
            }

            /// Trust: the first VERIFICATION-SELECTOR control this
            /// configuration holds away from its declared default — i.e. one a
            /// deauthorized frontend has not (or no longer) neutralized.
            pub fn first_live_trust_verification_selector(&self) -> Option<String> {
                $(
                    $(
                        if TrustAuthorityClass::$trust_authority.is_verification_selector()
                            && self.$opt != $init
                        {
                            return Some(
                                trust_authority_spelling($prefix, stringify!($opt))
                            );
                        }
                    )?
                )*
                None
            }

            /// Trust: reset every VERIFICATION-SELECTOR control to its declared
            /// default. Generated from the table, so a selector cannot be
            /// classified at the declaration and forgotten here. Only
            /// [`crate::config::TrustFrontendAuthoritySnapshot::deauthorize`] calls
            /// this, after materializing the one non-verification effect a
            /// selector carries; see [`TrustAuthorityClass::VerificationSelector`].
            /// Public only so the `-C` table's (empty) instance is not dead
            /// code; it can only lower authority.
            pub fn neutralize_trust_verification_selectors(&mut self) {
                $(
                    $(
                        if TrustAuthorityClass::$trust_authority.is_verification_selector() {
                            self.$opt = $init;
                        }
                    )?
                )*
            }
        }

        // Trust: a `-Ztrust-*` option that declares no authority class is a
        // compile error, not a lint and not a test failure. The inventory this
        // table feeds is the boundary that keeps an embedding frontend from
        // rewriting verification policy, so "someone forgets to register it"
        // has to be unrepresentable rather than merely detectable.
        $(
            const _: () = {
                const CLASSIFIED: bool = false $( || { ${ignore($trust_authority)} true } )?;
                assert!(
                    !trust_authority_classification_required(stringify!($opt)) || CLASSIFIED,
                    "every Trust compiler option must declare a TRUST_AUTHORITY class",
                );
            };
        )*

        pub const $stat: OptionDescrs<$struct_name> = &[
            $(
                OptionDesc {
                    name: stringify!($opt),
                    setter: $optmod::$opt,
                    type_desc: desc::$parse,
                    desc: $desc,
                    removed: None $( .or(Some(RemovedOption::$removed)) )?,
                    tmod: None $( .or(Some(
                        OptionsTargetModifiers::$struct_name($tmod_enum::$tmod_variant)
                    )))?,
                    mitigation: None $( .or(Some(
                        mitigation_coverage::DeniedPartialMitigationKind::$mitigation_variant
                    )))?,
                },
            )*
        ];

        mod $optmod {
            $(
                setter_for!($opt, $struct_name, $parse);
            )*
        }
    }
}

impl CodegenOptions {
    // JUSTIFICATION: defn of the suggested wrapper fn
    #[allow(rustc::bad_opt_access)]
    pub fn instrument_coverage(&self) -> InstrumentCoverage {
        self.instrument_coverage
    }
}

// Sometimes different options need to build a common structure.
// That structure can be kept in one of the options' fields, the others become dummy.
macro_rules! redirect_field {
    ($cg:ident.link_arg) => {
        $cg.link_args
    };
    ($cg:ident.pre_link_arg) => {
        $cg.pre_link_args
    };
    ($cg:ident.$field:ident) => {
        $cg.$field
    };
}

type OptionSetter<O> = fn(&mut O, &mut CollectedOptions, v: Option<&str>, pos: usize) -> bool;
type OptionDescrs<O> = &'static [OptionDesc<O>];

/// Indicates whether a removed option should warn or error.
enum RemovedOption {
    #[allow(unused)] // we might want deprecated options that warn again in the future
    Warn,
    Err,
}

pub struct OptionDesc<O> {
    name: &'static str,
    setter: OptionSetter<O>,
    // description for return value/type from mod desc
    type_desc: &'static str,
    // description for option from options table
    desc: &'static str,
    removed: Option<RemovedOption>,
    tmod: Option<OptionsTargetModifiers>,
    mitigation: Option<mitigation_coverage::DeniedPartialMitigationKind>,
}

impl<O> OptionDesc<O> {
    pub fn name(&self) -> &'static str {
        self.name
    }

    pub fn desc(&self) -> &'static str {
        self.desc
    }
}

fn build_options<O: Default>(
    early_dcx: &EarlyDiagCtxt,
    matches: &getopts::Matches,
    collected_options: &mut CollectedOptions,
    descrs: OptionDescrs<O>,
    prefix: &str,
    outputname: &str,
) -> O {
    // Trust: every option; the selector exists for `build_trust_authority_controls`.
    build_options_selected(
        early_dcx,
        matches,
        collected_options,
        descrs,
        prefix,
        outputname,
        |_| true,
    )
}

// Trust: `build_options` restricted to the options `selected` admits, by their
// canonical (underscore) field name AFTER the bootstrap alias below is resolved.
// Skipped options are neither parsed nor diagnosed; admitted ones go through the
// same setter, in the same order, with the same errors.
fn build_options_selected<O: Default>(
    early_dcx: &EarlyDiagCtxt,
    matches: &getopts::Matches,
    collected_options: &mut CollectedOptions,
    descrs: OptionDescrs<O>,
    prefix: &str,
    outputname: &str,
    mut selected: impl FnMut(&str) -> bool,
) -> O {
    let mut op = O::default();
    for (index, option) in matches.opt_strs_pos(prefix) {
        let (key, value) = match option.split_once('=') {
            None => (option, None),
            Some((k, v)) => (k.to_string(), Some(v)),
        };

        // BOOTSTRAP-ONLY COMPAT ALIAS: `-Zno-trust-verify` -> `-Ztrust-verify=<on|off>`.
        //
        // The flag surface was deliberately consolidated to the single
        // `trust_verify` domain (`576db732cd`, "one flag surface, one taxonomy,
        // one gate"), and `no_trust_verify` was removed. But the bootstrap seed
        // ships a targo that still emits the OLD spelling, and bootstrap
        // necessarily drives the NEWLY built rustc with that OLD cargo when it
        // builds stage1 std — so stage1 rustc must understand it or the build
        // cannot complete. It is a matched-pair problem: the reverse assignment
        // fails symmetrically, because the new targo emits `trust-verify=off`
        // which the seed's stage0 rustc does not know.
        //
        // `#[cfg(bootstrap)]` is what keeps this from re-forking the flag
        // surface it is working around. Bootstrap sets `--cfg=bootstrap` only
        // when compiling WITH stage0 (`bootstrap/src/core/builder/cargo.rs:977`),
        // i.e. only for the stage1 artifacts the seed's targo drives. Stage 2 —
        // the compiler that actually ships — is compiled by stage1, without the
        // cfg, so this alias does not exist there and `-Zno-trust-verify` remains
        // an unknown option for every real user.
        //
        // DELETE THIS the moment the bootstrap seed is advanced past the rename.
        // It is a bridge for exactly one seed generation, not a supported name.
        //
        // The rewrite is exact because it maps the AUTHORED VALUE through the
        // retired option's own parser. `no_trust_verify` was
        // `bool = (false, parse_bool, [TRACKED])`
        // (`576db732cd^:compiler/rustc_session/src/options.rs:2788`), and the
        // pre-rename driver read that bool as
        // `trust_verification_enabled_by_flags(no_trust_verify)`, so:
        //
        //   bare / `=y` / `=yes` / `=on` / `=true` -> no_trust_verify = true
        //                                          -> verification OFF -> `trust-verify=off`
        //   `=n` / `=no` / `=off` / `=false`       -> no_trust_verify = false
        //                                          -> verification ON  -> `trust-verify=on`
        //   anything else                          -> rejected, exactly as
        //                                             `parse_bool` rejected it
        //
        // `=no` is a LOAD-BEARING spelling, not a curiosity: the retired
        // ecosystem used it to opt verification ON. Compiletest emitted it for
        // precisely that (`576db732cd^:src/tools/compiletest/src/directives.rs`,
        // `has_explicit_trust_verification_config`: "`-Zno-trust-verify=no` opts
        // verification ON"), and `is_trust_verify_off_option` in
        // `src/bootstrap/src/utils/shared_helpers.rs` preserves the same split
        // for the mixed-vintage bootstrap. Discarding the value — as this alias
        // did until now — mapped `=no` to `off` and INVERTED the control: a
        // caller that asked for verification got a silently unverified compile.
        //
        // Note the double negative in `=off`/`=false`: under `parse_bool` those
        // set `no_trust_verify = false`, which means verification ON. They are
        // *not* off-requests, however much the spelling suggests it.
        //
        // An unrecognized value is a HARD ERROR rather than a default to `off`.
        // It was a hard error under the retired parser too, so refusing is the
        // exact behavior; and even if it were not, aborting is strictly better
        // than guessing at a verification decision. The message is the same one
        // `parse_bool` would have produced for this option.
        #[cfg(bootstrap)]
        let (key, value) = if prefix == "Z" && key.replace('-', "_") == "no_trust_verify" {
            // `true` meant "do not verify".
            let no_verify = match value {
                None | Some("y" | "yes" | "on" | "true") => true,
                Some("n" | "no" | "off" | "false") => false,
                Some(other) => early_dcx.early_fatal(format!(
                    "incorrect value `{other}` for {outputname} option `{key}` - {} was expected",
                    desc::parse_bool
                )),
            };
            ("trust-verify".to_string(), Some(if no_verify { "off" } else { "on" }))
        } else {
            (key, value)
        };

        let option_to_lookup = key.replace('-', "_");
        // Trust: see `build_options_selected`.
        if !selected(&option_to_lookup) {
            continue;
        }
        match descrs.iter().find(|opt_desc| opt_desc.name == option_to_lookup) {
            Some(OptionDesc { name: _, setter, type_desc, desc, removed, tmod, mitigation }) => {
                if let Some(removed) = removed {
                    // deprecation works for prefixed options only
                    assert!(!prefix.is_empty());
                    match removed {
                        RemovedOption::Warn => {
                            early_dcx.early_warn(format!("`-{prefix} {key}`: {desc}"))
                        }
                        RemovedOption::Err => {
                            early_dcx.early_fatal(format!("`-{prefix} {key}`: {desc}"))
                        }
                    }
                }
                if !setter(&mut op, collected_options, value, index) {
                    match value {
                        None => early_dcx.early_fatal(
                            format!(
                                "{outputname} option `{key}` requires {type_desc} (`-{prefix} {key}=<value>`)"
                            ),
                        ),
                        Some(value) => early_dcx.early_fatal(
                            format!(
                                "incorrect value `{value}` for {outputname} option `{key}` - {type_desc} was expected"
                            ),
                        ),
                    }
                }
                if let Some(tmod) = *tmod {
                    let v = value.map_or(String::new(), ToOwned::to_owned);

                    // Accumulate all the -Zsanitizer flags into a single target modifier.
                    match tmod {
                        OptionsTargetModifiers::UnstableOptions(
                            UnstableOptionsTargetModifiers::Sanitizer,
                        ) => {
                            collected_options
                                .target_modifiers
                                .entry(tmod)
                                .and_modify(|existing| {
                                    existing.push(',');
                                    existing.push_str(&v);
                                })
                                .or_insert(v);
                        }
                        _ => {
                            collected_options.target_modifiers.insert(tmod, v);
                        }
                    }
                }
                if let Some(mitigation) = mitigation {
                    collected_options.mitigations.reset_mitigation(*mitigation, index);
                }
            }
            None => {
                let mut error =
                    early_dcx.early_struct_fatal(format!("unknown {outputname} option: `{key}`"));
                let max_dist = option_to_lookup.chars().count().max(3) / 3;
                if let Some(option) = descrs
                    .iter()
                    .filter(|option| option.removed.is_none())
                    .filter_map(|option| {
                        edit_distance(&option_to_lookup, option.name, max_dist)
                            .map(|dist| (dist, option))
                    })
                    .min_by_key(|(dist, _)| *dist)
                    .map(|(_, option)| option)
                {
                    let name = option.name.replace('_', "-");
                    let value =
                        if option.type_desc == desc::parse_no_value { "" } else { "=<value>" };
                    error.help(format!("you might have meant to use `-{prefix} {name}{value}`"));
                }
                error.emit()
            }
        }
    }
    op
}

#[allow(non_upper_case_globals)]
mod desc {
    pub(crate) const parse_ignore: &str = "<ignored>"; // should not be user-visible
    pub(crate) const parse_no_value: &str = "no value";
    pub(crate) const parse_bool: &str =
        "one of: `y`, `yes`, `on`, `true`, `n`, `no`, `off` or `false`";
    pub(crate) const parse_opt_bool: &str = parse_bool;
    pub(crate) const parse_string: &str = "a string";
    pub(crate) const parse_opt_string: &str = parse_string;
    pub(crate) const parse_string_push: &str = parse_string;
    pub(crate) const parse_opt_pathbuf: &str = "a path";
    pub(crate) const parse_list: &str = "a space-separated list of strings";
    pub(crate) const parse_list_with_polarity: &str =
        "a comma-separated list of strings, with elements beginning with + or -";
    pub(crate) const parse_pointer_authentication_list_with_polarity: &str = "a comma-separated list of options, each of the form `+<name>` or `-<name>`, where `<name>` is one of: `aarch64-jump-table-hardening`, `auth-traps`, `calls`, `elf-got`, `function-pointer-type-discrimination`, `indirect-gotos`, `init-fini`, `init-fini-address-discrimination`, `intrinsics`, `return-addresses`, `typeinfo-vt-ptr-discrimination`, `vt-ptr-addr-discrimination` or `vt-ptr-type-discrimination`";
    pub(crate) const parse_autodiff: &str = "a comma separated list of settings: `Enable`, `PrintSteps`, `PrintTA`, `PrintTAFn`, `PrintAA`, `PrintPerf`, `PrintModBefore`, `PrintModAfter`, `PrintModFinal`, `PrintPasses`, `NoPostopt`, `LooseTypes`, `Inline`, `NoTT`";
    pub(crate) const parse_offload: &str = "a comma separated list of settings: `Host=<Absolute-Path>`, `HostMetadata=<Absolute-Path>`, `Device` (empty manifest) or `Device=<Absolute-Path>`, `Test`";
    pub(crate) const parse_comma_list: &str = "a comma-separated list of strings";
    pub(crate) const parse_opt_comma_list: &str = parse_comma_list;
    pub(crate) const parse_number: &str = "a number";
    pub(crate) const parse_opt_number: &str = parse_number;
    pub(crate) const parse_frame_pointer: &str = "one of `true`/`yes`/`on`, `false`/`no`/`off`, or (with -Zunstable-options) `non-leaf` or `always`";
    pub(crate) const parse_time_passes_format: &str = "`text` (default) or `json`";
    // Trust (F1): which producer supplies the trust-cg backend's per-function
    // input. `mir` is the shipped path; `trust-ir` is the source-first one.
    pub(crate) const parse_trust_cg_frontend: &str = "one of `mir` or `trust-ir`";
    // Trust (step 2 increment 5, sub-step 5.4.2): which consumer compiles F1's trust-ir.
    pub(crate) const parse_trust_cg_f1_backend: &str = "one of `lir` or `compiler`";
    // Trust: keep the compiler transport's finite verifier domains honest at
    // option-parsing time instead of silently coercing typos later in MIR.
    pub(crate) const parse_trust_cg_output_gate: &str =
        "one of `allow-unknown`, `strict`, or `off`";
    pub(crate) const parse_trust_verify: &str = "one of `on` or `off`";
    pub(crate) const parse_trust_ir_lower: &str =
        "one of `off`, `on`, or `strict` (the boolean spellings and a bare flag still mean `on`)";
    pub(crate) const parse_trust_spawn_census_shadow: &str = "one of `off`, `report`, or `check`";
    // Trust (platform protocols, plan L1a): the description IS the refusal text. An unknown
    // spelling and a property this trustc cannot check end in the same parse error, and this
    // sentence is what tells the two apart for the reader (FC-7). A unit test pins that it names
    // every supported and every refused spelling.
    pub(crate) const parse_trust_platform_properties: &str = "a comma-separated list of platform \
         properties: `fd-inherit` (`lock-release` and `fd-identity` are not supported by this \
         trustc)";
    pub(crate) const parse_trust_platform_unanalysed: &str = "one of `warn` or `deny`";
    pub(crate) const parse_trust_platform_budget: &str = "a positive number of states";
    pub(crate) const parse_trust_platform_report: &str = "one of `summary` or `verbose`";
    pub(crate) const parse_trust_policy: &str =
        "one of `strict`, `certify`, `advisory`, or `memory-safe`";
    pub(crate) const parse_trust_witness: &str =
        "one of `auto`, `off`, `mint:<dir>`, or `replay:<dir>`";
    pub(crate) const parse_trust_verify_level: &str = "one of `0`, `1`, or `2`";
    pub(crate) const parse_trust_nonempty_path: &str = "a non-empty path";
    pub(crate) const parse_trust_dump: &str = "`mir:<dir>`, `mir-only:<dir>`, `native-bundle:<dir>`, `ir:<dir>`, or `spec-clean:<dir>` \
         (repeat the option for more than one sink)";
    pub(crate) const parse_trust_bundle_foreign_crate: &str =
        "a non-empty comma-separated list of crate names";
    pub(crate) const parse_trust_verify_crate_role: &str =
        "one of `unscoped`, `primary`, `dependency`, or `build-script`";
    pub(crate) const parse_trust_verify_output: &str = "one of `human`, `json`, or `both`";
    pub(crate) const parse_trust_verify_package_name: &str = "a non-empty package name";
    pub(crate) const parse_trust_verify_profile: &str = "a non-empty Trust profile name";
    pub(crate) const parse_trust_verify_session: &str = "a non-empty session identifier";
    pub(crate) const parse_trust_admission_digest: &str =
        "one canonical SHA-256 digest (no duplicate option)";
    pub(crate) const parse_trust_admission_role: &str =
        "one of primary, test-execution, dependency (no duplicate option)";
    pub(crate) const parse_trust_admission_target: &str =
        "one exact Cargo compile target string (no duplicate option)";
    pub(crate) const parse_trust_verify_target_spec_sha256: &str =
        "exactly 64 lowercase hexadecimal SHA-256 digits";
    pub(crate) const parse_trust_verify_timeout_ms: &str =
        "a positive integer number of milliseconds";
    pub(crate) const parse_trust_verify_effort: &str =
        "an integer number of SAT conflicts per distinct query term, from 1 through 100000";
    pub(crate) const parse_trust_verify_function_budget_steps: &str =
        "a positive integer number of preprocessing steps";
    pub(crate) const parse_trust_verify_worker_threads: &str = "an integer from 0 through 256";
    pub(crate) const parse_passes: &str = "a space-separated list of passes, or `all`";
    pub(crate) const parse_panic_strategy: &str = "either `unwind`, `abort`, or `immediate-abort`";
    pub(crate) const parse_on_broken_pipe: &str = "either `kill`, `error`, or `inherit`";
    pub(crate) const parse_patchable_function_entry: &str = "a comma separated list of (prefix_nops,total_nops,section_name), (prefix_nops,total_nops), or (total_nops). Where prefix_nops <= total_nops where 0 < total_nops <= 255 and prefix_nops <= total_nops";
    pub(crate) const parse_opt_panic_strategy: &str = parse_panic_strategy;
    pub(crate) const parse_relro_level: &str = "one of: `full`, `partial`, or `off`";
    pub(crate) const parse_sanitizers: &str = "comma separated list of sanitizers: `address`, `cfi`, `dataflow`, `hwaddress`, `kcfi`, `kernel-address`, `kernel-hwaddress`, `leak`, `memory`, `memtag`, `safestack`, `shadow-call-stack`, `thread`, or 'realtime'";
    pub(crate) const parse_sanitizer_memory_track_origins: &str = "0, 1, or 2";
    pub(crate) const parse_cfguard: &str =
        "either a boolean (`yes`, `no`, `on`, `off`, etc), `checks`, or `nochecks`";
    pub(crate) const parse_cfprotection: &str = "`none`|`no`|`n` (default), `branch`, `return`, or `full`|`yes`|`y` (equivalent to `branch` and `return`)";
    pub(crate) const parse_debuginfo: &str = "either an integer (0, 1, 2), `none`, `line-directives-only`, `line-tables-only`, `limited`, or `full`";
    pub(crate) const parse_debuginfo_compression: &str = "one of `none`, `zlib`, or `zstd`";
    pub(crate) const parse_mir_strip_debuginfo: &str =
        "one of `none`, `locals-in-tiny-functions`, or `all-locals`";
    pub(crate) const parse_collapse_macro_debuginfo: &str = "one of `no`, `external`, or `yes`";
    pub(crate) const parse_strip: &str = "either `none`, `debuginfo`, or `symbols`";
    pub(crate) const parse_linker_flavor: &str = ::rustc_target::spec::LinkerFlavorCli::one_of();
    pub(crate) const parse_dump_mono_stats: &str = "`markdown` (default) or `json`";
    pub(crate) const parse_instrument_coverage: &str = parse_bool;
    pub(crate) const parse_coverage_options: &str = "`block` | `branch` | `condition`";
    pub(crate) const parse_codegen_retag_options: &str =
        "either no value or a comma-separated list of settings: `no-precise-im`, `no-precise-pin`";
    pub(crate) const parse_instrument_mcount: &str = "either a boolean (`yes`, `no`, `on`, `off`, etc), or `fentry`, `fentry-record`, `fentry-nop-record` on supported targets";
    pub(crate) const parse_instrument_xray: &str = "either a boolean (`yes`, `no`, `on`, `off`, etc), or a comma separated list of settings: `always` or `never` (mutually exclusive), `ignore-loops`, `instruction-threshold=N`, `skip-entry`, `skip-exit`";
    pub(crate) const parse_unpretty: &str = "`string` or `string=string`";
    pub(crate) const parse_treat_err_as_bug: &str = "either no value or a non-negative number";
    pub(crate) const parse_next_solver_config: &str =
        "either `globally` (when used without an argument), or `coherence` (default)";
    pub(crate) const parse_lto: &str =
        "either a boolean (`yes`, `no`, `on`, `off`, etc), `thin`, `fat`, or omitted";
    pub(crate) const parse_linker_plugin_lto: &str =
        "either a boolean (`yes`, `no`, `on`, `off`, etc), or the path to the linker plugin";
    pub(crate) const parse_location_detail: &str = "either `none`, or a comma separated list of location details to track: `file`, `line`, or `column`";
    pub(crate) const parse_fmt_debug: &str = "either `full`, `shallow`, or `none`";
    pub(crate) const parse_switch_with_opt_path: &str =
        "an optional path to the profiling data output directory";
    pub(crate) const parse_merge_functions: &str =
        "one of: `disabled`, `trampolines`, or `aliases`";
    pub(crate) const parse_symbol_mangling_version: &str =
        "one of: `legacy`, `v0` (RFC 2603), or `hashed`";
    pub(crate) const parse_opt_symbol_visibility: &str =
        "one of: `hidden`, `protected`, or `interposable`";
    pub(crate) const parse_cargo_src_file_hash: &str =
        "one of `blake3`, `md5`, `sha1`, or `sha256`";
    pub(crate) const parse_src_file_hash: &str = "one of `md5`, `sha1`, or `sha256`";
    pub(crate) const parse_relocation_model: &str =
        "one of supported relocation models (`rustc --print relocation-models`)";
    pub(crate) const parse_code_model: &str =
        "one of supported code models (`rustc --print code-models`)";
    pub(crate) const parse_tls_model: &str =
        "one of supported TLS models (`rustc --print tls-models`)";
    pub(crate) const parse_target_feature: &str = parse_string;
    pub(crate) const parse_terminal_url: &str =
        "either a boolean (`yes`, `no`, `on`, `off`, etc), or `auto`";
    pub(crate) const parse_wasi_exec_model: &str = "either `command` or `reactor`";
    pub(crate) const parse_split_debuginfo: &str =
        "one of supported split-debuginfo modes (`off`, `packed`, or `unpacked`)";
    pub(crate) const parse_split_dwarf_kind: &str =
        "one of supported split dwarf modes (`split` or `single`)";
    pub(crate) const parse_link_self_contained: &str = "one of: `y`, `yes`, `on`, `n`, `no`, `off`, or a list of enabled (`+` prefix) and disabled (`-` prefix) \
        components: `crto`, `libc`, `unwind`, `linker`, `sanitizers`, `mingw`";
    pub(crate) const parse_linker_features: &str =
        "a list of enabled (`+` prefix) and disabled (`-` prefix) features: `lld`";
    pub(crate) const parse_polonius: &str =
        "either no value or one of `legacy` (the default), `off`, or `next`";
    pub(crate) const parse_annotate_moves: &str =
        "either a boolean (`yes`, `no`, `on`, `off`, etc.), or a size limit in bytes";
    pub(crate) const parse_stack_protector: &str =
        "one of (`none` (default), `basic`, `strong`, or `all`)";
    pub(crate) const parse_branch_protection: &str = "a `,` separated combination of `bti`, `gcs`, `pac-ret`, (optionally with `pc`, `b-key`, `leaf` if `pac-ret` is set)";
    pub(crate) const parse_proc_macro_execution_strategy: &str =
        "one of supported execution strategies (`same-thread`, or `cross-thread`)";
    pub(crate) const parse_inlining_threshold: &str =
        "either a boolean (`yes`, `no`, `on`, `off`, etc), or a non-negative number";
    pub(crate) const parse_llvm_module_flag: &str = "<key>:<type>:<value>:<behavior>. Type must currently be `u32`. Behavior should be one of (`error`, `warning`, `require`, `override`, `append`, `appendunique`, `max`, `min`)";
    pub(crate) const parse_function_return: &str = "`keep` or `thunk-extern`";
    pub(crate) const parse_wasm_c_abi: &str = "`spec`";
    pub(crate) const parse_mir_include_spans: &str =
        "either a boolean (`yes`, `no`, `on`, `off`, etc), or `nll` (default: `nll`)";
    pub(crate) const parse_align: &str = "a number that is a power of 2 between 1 and 2^29";
    pub(crate) const parse_assert_incr_state: &str = "one of: `loaded`, `not-loaded`";
    pub(crate) const parse_allow_partial_mitigations: &str =
        super::mitigation_coverage::DeniedPartialMitigationKind::KINDS;
    pub(crate) const parse_deny_partial_mitigations: &str =
        super::mitigation_coverage::DeniedPartialMitigationKind::KINDS;
    pub(crate) const parse_rust_version: &str = "a rust version (`xx.yy.zz`)";
}

pub mod parse {
    use std::str::FromStr;

    pub(crate) use super::*;

    /// Ignore the value. Used for removed options where we don't actually want to store
    /// anything in the session.
    pub(crate) fn parse_ignore(_slot: &mut (), _v: Option<&str>) -> bool {
        true
    }

    /// This is for boolean options that don't take a value, and are true simply
    /// by existing on the command-line.
    ///
    /// This style of option is deprecated, and is mainly used by old options
    /// beginning with `no-`.
    pub(crate) fn parse_no_value(slot: &mut bool, v: Option<&str>) -> bool {
        match v {
            None => {
                *slot = true;
                true
            }
            // Trying to specify a value is always forbidden.
            Some(_) => false,
        }
    }

    /// Use this for any boolean option that has a static default.
    pub(crate) fn parse_bool(slot: &mut bool, v: Option<&str>) -> bool {
        match v {
            Some("y") | Some("yes") | Some("on") | Some("true") | None => {
                *slot = true;
                true
            }
            Some("n") | Some("no") | Some("off") | Some("false") => {
                *slot = false;
                true
            }
            _ => false,
        }
    }

    /// Use this for any boolean option that lacks a static default. (The
    /// actions taken when such an option is not specified will depend on
    /// other factors, such as other options, or target options.)
    pub(crate) fn parse_opt_bool(slot: &mut Option<bool>, v: Option<&str>) -> bool {
        match v {
            Some("y") | Some("yes") | Some("on") | Some("true") | None => {
                *slot = Some(true);
                true
            }
            Some("n") | Some("no") | Some("off") | Some("false") => {
                *slot = Some(false);
                true
            }
            _ => false,
        }
    }

    /// Parses whether polonius is enabled, and if so, which version.
    pub(crate) fn parse_polonius(slot: &mut Polonius, v: Option<&str>) -> bool {
        match v {
            Some("legacy") | None => {
                *slot = Polonius::Legacy;
                true
            }
            Some("next") => {
                *slot = Polonius::Next;
                true
            }
            Some("off") | Some("no") => {
                *slot = Polonius::Off;
                true
            }
            _ => false,
        }
    }

    pub(crate) fn parse_annotate_moves(slot: &mut AnnotateMoves, v: Option<&str>) -> bool {
        let mut bslot = false;
        let mut nslot = 0u64;

        *slot = match v {
            // No value provided: -Z annotate-moves (enable with default limit)
            None => AnnotateMoves::Enabled(None),
            // Explicit boolean value provided: -Z annotate-moves=yes/no
            s @ Some(_) if parse_bool(&mut bslot, s) => {
                if bslot {
                    AnnotateMoves::Enabled(None)
                } else {
                    AnnotateMoves::Disabled
                }
            }
            // With numeric limit provided: -Z annotate-moves=1234
            s @ Some(_) if parse_number(&mut nslot, s) => AnnotateMoves::Enabled(Some(nslot)),
            _ => return false,
        };

        true
    }

    /// Use this for any string option that has a static default.
    pub(crate) fn parse_string(slot: &mut String, v: Option<&str>) -> bool {
        match v {
            Some(s) => {
                *slot = s.to_string();
                true
            }
            None => false,
        }
    }

    /// Use this for any string option that lacks a static default.
    pub(crate) fn parse_opt_string(slot: &mut Option<String>, v: Option<&str>) -> bool {
        match v {
            Some(s) => {
                *slot = Some(s.to_string());
                true
            }
            None => false,
        }
    }

    pub(crate) fn parse_opt_pathbuf(slot: &mut Option<PathBuf>, v: Option<&str>) -> bool {
        match v {
            Some(s) => {
                *slot = Some(PathBuf::from(s));
                true
            }
            None => false,
        }
    }

    pub(crate) fn parse_string_push(slot: &mut Vec<String>, v: Option<&str>) -> bool {
        match v {
            Some(s) => {
                slot.push(s.to_string());
                true
            }
            None => false,
        }
    }

    pub(crate) fn parse_list(slot: &mut Vec<String>, v: Option<&str>) -> bool {
        match v {
            Some(s) => {
                slot.extend(s.split_whitespace().map(|s| s.to_string()));
                true
            }
            None => false,
        }
    }

    pub(crate) fn parse_list_with_polarity(
        slot: &mut Vec<(String, bool)>,
        v: Option<&str>,
    ) -> bool {
        match v {
            Some(s) => {
                for s in s.split(',') {
                    let Some(pass_name) = s.strip_prefix(&['+', '-'][..]) else { return false };
                    slot.push((pass_name.to_string(), &s[..1] == "+"));
                }
                true
            }
            None => false,
        }
    }

    pub(crate) fn parse_pointer_authentication_list_with_polarity(
        slot: &mut Vec<(PointerAuthOption, bool)>,
        v: Option<&str>,
    ) -> bool {
        let Some(s) = v else {
            return false;
        };

        let mut map = BTreeMap::<PointerAuthOption, bool>::new();

        for item in s.split(',') {
            let Some(name) = item.strip_prefix(&['+', '-'][..]) else {
                return false;
            };

            let Some(opt) = PointerAuthOption::parse(name) else {
                return false;
            };

            let enabled = item.starts_with('+');

            // Last occurrence wins.
            map.insert(opt, enabled);
        }

        slot.clear();
        slot.extend(map);

        true
    }

    pub(crate) fn parse_fmt_debug(opt: &mut FmtDebug, v: Option<&str>) -> bool {
        *opt = match v {
            Some("full") => FmtDebug::Full,
            Some("shallow") => FmtDebug::Shallow,
            Some("none") => FmtDebug::None,
            _ => return false,
        };
        true
    }

    pub(crate) fn parse_location_detail(ld: &mut LocationDetail, v: Option<&str>) -> bool {
        if let Some(v) = v {
            ld.line = false;
            ld.file = false;
            ld.column = false;
            if v == "none" {
                return true;
            }
            for s in v.split(',') {
                match s {
                    "file" => ld.file = true,
                    "line" => ld.line = true,
                    "column" => ld.column = true,
                    _ => return false,
                }
            }
            true
        } else {
            false
        }
    }

    pub(crate) fn parse_comma_list(slot: &mut Vec<String>, v: Option<&str>) -> bool {
        match v {
            Some(s) => {
                let mut v: Vec<_> = s.split(',').map(|s| s.to_string()).collect();
                v.sort_unstable();
                *slot = v;
                true
            }
            None => false,
        }
    }

    pub(crate) fn parse_opt_comma_list(slot: &mut Option<Vec<String>>, v: Option<&str>) -> bool {
        match v {
            Some(s) => {
                let mut v: Vec<_> = s.split(',').map(|s| s.to_string()).collect();
                v.sort_unstable();
                *slot = Some(v);
                true
            }
            None => false,
        }
    }

    /// Use this for any numeric option that has a static default.
    pub(crate) fn parse_number<T: Copy + FromStr>(slot: &mut T, v: Option<&str>) -> bool {
        match v.and_then(|s| s.parse().ok()) {
            Some(i) => {
                *slot = i;
                true
            }
            None => false,
        }
    }

    /// Use this for any numeric option that lacks a static default.
    pub(crate) fn parse_opt_number<T: Copy + FromStr>(
        slot: &mut Option<T>,
        v: Option<&str>,
    ) -> bool {
        match v {
            Some(s) => {
                *slot = s.parse().ok();
                slot.is_some()
            }
            None => false,
        }
    }

    pub(crate) fn parse_frame_pointer(slot: &mut FramePointer, v: Option<&str>) -> bool {
        let mut yes = false;
        match v {
            _ if parse_bool(&mut yes, v) && yes => slot.ratchet(FramePointer::Always),
            _ if parse_bool(&mut yes, v) => slot.ratchet(FramePointer::MayOmit),
            Some("always") => slot.ratchet(FramePointer::Always),
            Some("non-leaf") => slot.ratchet(FramePointer::NonLeaf),
            _ => return false,
        };
        true
    }

    pub(crate) fn parse_passes(slot: &mut Passes, v: Option<&str>) -> bool {
        match v {
            Some("all") => {
                *slot = Passes::All;
                true
            }
            v => {
                let mut passes = vec![];
                if parse_list(&mut passes, v) {
                    slot.extend(passes);
                    true
                } else {
                    false
                }
            }
        }
    }

    pub(crate) fn parse_opt_panic_strategy(
        slot: &mut Option<PanicStrategy>,
        v: Option<&str>,
    ) -> bool {
        match v {
            Some("unwind") => *slot = Some(PanicStrategy::Unwind),
            Some("abort") => *slot = Some(PanicStrategy::Abort),
            Some("immediate-abort") => *slot = Some(PanicStrategy::ImmediateAbort),
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_panic_strategy(slot: &mut PanicStrategy, v: Option<&str>) -> bool {
        match v {
            Some("unwind") => *slot = PanicStrategy::Unwind,
            Some("abort") => *slot = PanicStrategy::Abort,
            Some("immediate-abort") => *slot = PanicStrategy::ImmediateAbort,
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_on_broken_pipe(slot: &mut OnBrokenPipe, v: Option<&str>) -> bool {
        match v {
            // OnBrokenPipe::Default can't be explicitly specified
            Some("kill") => *slot = OnBrokenPipe::Kill,
            Some("error") => *slot = OnBrokenPipe::Error,
            Some("inherit") => *slot = OnBrokenPipe::Inherit,
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_patchable_function_entry(
        slot: &mut PatchableFunctionEntry,
        v: Option<&str>,
    ) -> bool {
        let mut total_nops = 0;
        let mut prefix_nops = 0;
        let mut section = None;

        if !parse_number(&mut total_nops, v) {
            let parts: Vec<_> = v.unwrap_or("").split(',').collect();
            if parts.len() < 2 || parts.len() > 3 {
                return false;
            }

            if !parse_number(&mut total_nops, Some(parts[0])) {
                return false;
            }
            if !parse_number(&mut prefix_nops, Some(parts[1])) {
                return false;
            }
            section = parts.get(2).map(|x| x.to_string());
        }

        if let Some(pfe) = PatchableFunctionEntry::from_parts(total_nops, prefix_nops, section) {
            *slot = pfe;
            return true;
        }
        false
    }

    pub(crate) fn parse_relro_level(slot: &mut Option<RelroLevel>, v: Option<&str>) -> bool {
        match v {
            Some(s) => match s.parse::<RelroLevel>() {
                Ok(level) => *slot = Some(level),
                _ => return false,
            },
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_sanitizers(slot: &mut SanitizerSet, v: Option<&str>) -> bool {
        if let Some(v) = v {
            for s in v.split(',') {
                *slot |= match s {
                    "address" => SanitizerSet::ADDRESS,
                    "cfi" => SanitizerSet::CFI,
                    "dataflow" => SanitizerSet::DATAFLOW,
                    "kcfi" => SanitizerSet::KCFI,
                    "kernel-address" => SanitizerSet::KERNELADDRESS,
                    "kernel-hwaddress" => SanitizerSet::KERNELHWADDRESS,
                    "leak" => SanitizerSet::LEAK,
                    "memory" => SanitizerSet::MEMORY,
                    "memtag" => SanitizerSet::MEMTAG,
                    "shadow-call-stack" => SanitizerSet::SHADOWCALLSTACK,
                    "thread" => SanitizerSet::THREAD,
                    "hwaddress" => SanitizerSet::HWADDRESS,
                    "safestack" => SanitizerSet::SAFESTACK,
                    "realtime" => SanitizerSet::REALTIME,
                    _ => return false,
                }
            }
            true
        } else {
            false
        }
    }

    pub(crate) fn parse_sanitizer_memory_track_origins(slot: &mut usize, v: Option<&str>) -> bool {
        match v {
            Some("2") | None => {
                *slot = 2;
                true
            }
            Some("1") => {
                *slot = 1;
                true
            }
            Some("0") => {
                *slot = 0;
                true
            }
            Some(_) => false,
        }
    }

    pub(crate) fn parse_strip(slot: &mut Strip, v: Option<&str>) -> bool {
        match v {
            Some("none") => *slot = Strip::None,
            Some("debuginfo") => *slot = Strip::Debuginfo,
            Some("symbols") => *slot = Strip::Symbols,
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_cfguard(slot: &mut CFGuard, v: Option<&str>) -> bool {
        if v.is_some() {
            let mut bool_arg = None;
            if parse_opt_bool(&mut bool_arg, v) {
                *slot = if bool_arg.unwrap() { CFGuard::Checks } else { CFGuard::Disabled };
                return true;
            }
        }

        *slot = match v {
            None => CFGuard::Checks,
            Some("checks") => CFGuard::Checks,
            Some("nochecks") => CFGuard::NoChecks,
            Some(_) => return false,
        };
        true
    }

    pub(crate) fn parse_cfprotection(slot: &mut CFProtection, v: Option<&str>) -> bool {
        if v.is_some() {
            let mut bool_arg = None;
            if parse_opt_bool(&mut bool_arg, v) {
                *slot = if bool_arg.unwrap() { CFProtection::Full } else { CFProtection::None };
                return true;
            }
        }

        *slot = match v {
            None | Some("none") => CFProtection::None,
            Some("branch") => CFProtection::Branch,
            Some("return") => CFProtection::Return,
            Some("full") => CFProtection::Full,
            Some(_) => return false,
        };
        true
    }

    pub(crate) fn parse_debuginfo(slot: &mut DebugInfo, v: Option<&str>) -> bool {
        match v {
            Some("0") | Some("none") => *slot = DebugInfo::None,
            Some("line-directives-only") => *slot = DebugInfo::LineDirectivesOnly,
            Some("line-tables-only") => *slot = DebugInfo::LineTablesOnly,
            Some("1") | Some("limited") => *slot = DebugInfo::Limited,
            Some("2") | Some("full") => *slot = DebugInfo::Full,
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_debuginfo_compression(
        slot: &mut DebugInfoCompression,
        v: Option<&str>,
    ) -> bool {
        match v {
            Some("none") => *slot = DebugInfoCompression::None,
            Some("zlib") => *slot = DebugInfoCompression::Zlib,
            Some("zstd") => *slot = DebugInfoCompression::Zstd,
            _ => return false,
        };
        true
    }

    pub(crate) fn parse_mir_strip_debuginfo(slot: &mut MirStripDebugInfo, v: Option<&str>) -> bool {
        match v {
            Some("none") => *slot = MirStripDebugInfo::None,
            Some("locals-in-tiny-functions") => *slot = MirStripDebugInfo::LocalsInTinyFunctions,
            Some("all-locals") => *slot = MirStripDebugInfo::AllLocals,
            _ => return false,
        };
        true
    }

    pub(crate) fn parse_linker_flavor(slot: &mut Option<LinkerFlavorCli>, v: Option<&str>) -> bool {
        match v.and_then(|v| LinkerFlavorCli::from_str(v).ok()) {
            Some(lf) => *slot = Some(lf),
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_opt_symbol_visibility(
        slot: &mut Option<SymbolVisibility>,
        v: Option<&str>,
    ) -> bool {
        if let Some(v) = v {
            if let Ok(vis) = SymbolVisibility::from_str(v) {
                *slot = Some(vis);
            } else {
                return false;
            }
        }
        true
    }

    pub(crate) fn parse_unpretty(slot: &mut Option<String>, v: Option<&str>) -> bool {
        match v {
            None => false,
            Some(s) if s.split('=').count() <= 2 => {
                *slot = Some(s.to_string());
                true
            }
            _ => false,
        }
    }

    pub(crate) fn parse_time_passes_format(slot: &mut TimePassesFormat, v: Option<&str>) -> bool {
        match v {
            None => true,
            Some("json") => {
                *slot = TimePassesFormat::Json;
                true
            }
            Some("text") => {
                *slot = TimePassesFormat::Text;
                true
            }
            Some(_) => false,
        }
    }

    // Trust: `trust-verify-level` is a closed three-level protocol. Accepting an
    // arbitrary usize and mapping every value above 1 to L2 hid misspelled or
    // future values while reporting a different configuration than requested.
    pub(crate) fn parse_trust_verify_level(slot: &mut usize, v: Option<&str>) -> bool {
        let Some(value) = v.and_then(|value| value.parse::<usize>().ok()) else {
            return false;
        };
        if value > 2 {
            return false;
        }
        *slot = value;
        true
    }

    pub(crate) fn parse_trust_cg_output_gate(slot: &mut String, v: Option<&str>) -> bool {
        match v {
            Some(value @ ("allow-unknown" | "strict" | "off")) => {
                *slot = value.to_string();
                true
            }
            _ => false,
        }
    }

    // Trust (F1): the trust-cg backend's per-function INPUT PRODUCER. A typo
    // must fail here rather than silently leave the shipped MIR path selected,
    // because the whole point of the option is to say which producer the
    // emitted object came from.
    pub(crate) fn parse_trust_cg_frontend(slot: &mut String, v: Option<&str>) -> bool {
        match v {
            Some(value @ ("mir" | "trust-ir")) => {
                *slot = value.to_string();
                true
            }
            _ => false,
        }
    }

    // Trust (step 2 increment 5, sub-step 5.4.2): F1's CONSUMER. A typo must fail here rather
    // than silently leave the default `lir` consumer selected: the option says which compiler
    // and which output gate produced the object.
    pub(crate) fn parse_trust_cg_f1_backend(slot: &mut String, v: Option<&str>) -> bool {
        match v {
            Some(value @ ("lir" | "compiler")) => {
                *slot = value.to_string();
                true
            }
            _ => false,
        }
    }

    // Trust: structured transport is a compiler/frontend protocol. A typo must
    // fail during argument parsing, not silently fall back to human output and
    // leave the frontend believing the compiler emitted no evidence.
    pub(crate) fn parse_trust_verify_output(slot: &mut String, v: Option<&str>) -> bool {
        match v {
            Some(value @ ("human" | "json" | "both")) => {
                *slot = value.to_string();
                true
            }
            _ => false,
        }
    }

    // Trust: Targo gives each proof build a fresh session identity. The value is
    // semantically inert but dependency-tracked, forcing Cargo/rustc to execute
    // the actual requested compiler invocation without changing the crate hash
    // exposed to downstream crates. Empty identities would collapse distinct
    // invocations back onto the same fingerprint and are rejected.
    pub(crate) fn parse_trust_verify_session(slot: &mut Option<String>, v: Option<&str>) -> bool {
        let Some(value) = v.map(str::trim).filter(|value| !value.is_empty()) else {
            return false;
        };
        *slot = Some(value.to_string());
        true
    }

    // Trust: unlike an ordinary last-wins option, duplicate resource bindings are ambiguous.
    pub(crate) fn parse_trust_admission_digest(slot: &mut Option<String>, v: Option<&str>) -> bool {
        slot.is_none() && parse_trust_verify_target_spec_sha256(slot, v)
    }

    pub(crate) fn parse_trust_admission_role(slot: &mut Option<String>, v: Option<&str>) -> bool {
        if slot.is_some() {
            return false;
        }
        match v {
            Some(value @ ("primary" | "test-execution" | "dependency")) => {
                *slot = Some(value.to_string());
                true
            }
            _ => false,
        }
    }

    pub(crate) fn parse_trust_admission_target(slot: &mut Option<String>, v: Option<&str>) -> bool {
        let Some(value) = v.filter(|value| !value.is_empty() && value.len() <= 4096) else {
            return false;
        };
        if slot.is_some() {
            return false;
        }
        // This may be a canonical Unicode path. Keep its exact bytes, including
        // spaces; trimming or lossy path conversion changes the Cargo identity.
        *slot = Some(value.to_string());
        true
    }

    /// Cargo-authenticated content binding for a custom JSON target. Keep the
    /// wire form canonical so equality cannot be weakened by case, prefixes,
    /// whitespace, or a non-SHA-256 length.
    pub(crate) fn parse_trust_verify_target_spec_sha256(
        slot: &mut Option<String>,
        v: Option<&str>,
    ) -> bool {
        let Some(value) = v.filter(|value| {
            value.len() == 64
                && value
                    .as_bytes()
                    .iter()
                    .all(|&byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
        }) else {
            return false;
        };
        *slot = Some(value.to_string());
        true
    }

    // Trust (cross-crate composition): the build-declared foreign bundling
    // scope, as ONE comma-separated occurrence. It is a single option rather
    // than a repeated one because Targo's own verified-policy audit rejects a
    // duplicated `-Ztrust-*` authority by name, so a repeat-per-crate spelling
    // would refuse every build with two workspace-internal dependencies.
    //
    // Order-insensitive and deduplicated, so the value cannot perturb the crate
    // hash by dependency-iteration order. An EMPTY value is rejected rather than
    // ignored: a shell that ate the value would otherwise read as "declare
    // nothing", which is silently the pre-change behavior.
    pub(crate) fn parse_trust_bundle_foreign_crate(
        slot: &mut Vec<String>,
        v: Option<&str>,
    ) -> bool {
        let Some(value) = v.map(str::trim).filter(|value| !value.is_empty()) else {
            return false;
        };
        for name in value.split(',').map(str::trim) {
            // A crate name is an identifier; anything else cannot name a crate
            // this compilation loaded, so refuse it instead of carrying a value
            // no comparison can ever match.
            if name.is_empty()
                || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                || name.starts_with(|c: char| c.is_ascii_digit())
            {
                return false;
            }
            if !slot.iter().any(|existing| existing == name) {
                slot.push(name.to_string());
            }
        }
        slot.sort();
        true
    }

    pub(crate) fn parse_trust_verify_package_name(
        slot: &mut Option<String>,
        v: Option<&str>,
    ) -> bool {
        let Some(value) = v.map(str::trim).filter(|value| !value.is_empty()) else {
            return false;
        };
        *slot = Some(value.to_string());
        true
    }

    pub(crate) fn parse_trust_verify_profile(slot: &mut Option<String>, v: Option<&str>) -> bool {
        let Some(value) = v.map(str::trim).filter(|value| !value.is_empty()) else {
            return false;
        };
        *slot = Some(value.to_string());
        true
    }

    // Trust: paths that control proof inputs or requested evidence publication
    // must not accept an empty value and silently fall back to ambient/default
    // behavior. Preserve all non-empty bytes represented by rustc's UTF-8 CLI;
    // surrounding spaces can be a legitimate path component.
    pub(crate) fn parse_trust_nonempty_path(slot: &mut Option<PathBuf>, v: Option<&str>) -> bool {
        let Some(value) = v.filter(|value| !value.trim().is_empty()) else {
            return false;
        };
        *slot = Some(PathBuf::from(value));
        true
    }

    // Trust: one `-Ztrust-dump=<what>:<path>` per occurrence, repeated for more
    // than one sink. No separator list: a path may legitimately contain a comma,
    // and a grammar that can misread one directory as two would publish evidence
    // somewhere the caller never named. Requesting the same sink twice is
    // rejected rather than last-wins, so the pre-typed argv guard that leases the
    // `ir:` directory and this parser can never disagree about which one is live.
    pub(crate) fn parse_trust_dump(slot: &mut TrustDump, v: Option<&str>) -> bool {
        let Some((what, path)) = v.and_then(|value| value.split_once(':')) else {
            return false;
        };
        if path.trim().is_empty() {
            return false;
        }
        let sink = match what {
            "mir" | "mir-only" => &mut slot.mir,
            "native-bundle" => &mut slot.native_bundle,
            "ir" => &mut slot.ir,
            // Trust (v6/D1): the kernel-graded Clean goal ledger read back by
            // `targo trust spec --emit clean`.
            "spec-clean" => &mut slot.spec_clean,
            _ => return false,
        };
        if sink.is_some() {
            return false;
        }
        *sink = Some(PathBuf::from(path));
        if what == "mir-only" {
            slot.mir_only = true;
        }
        true
    }

    // Trust: the verification off-switch is a domain, not a negated boolean.
    // A value is mandatory: `-Ztrust-verify` on its own would be a no-op
    // restatement of the default, and accepting it as a synonym for `on` makes
    // a truncated `-Ztrust-verify=off` (a shell that ate the value) look like a
    // request to keep verifying.
    pub(crate) fn parse_trust_verify(slot: &mut TrustVerify, v: Option<&str>) -> bool {
        *slot = match v {
            Some("on") => TrustVerify::On,
            Some("off") => TrustVerify::Off,
            _ => return false,
        };
        true
    }

    /// Trust: `off` | `on` | `strict`, or bare `-Ztrust-ir-lower` for `on`.
    ///
    /// The bare and boolean spellings are kept because this option shipped as an
    /// `Option<bool>` parsed by `parse_opt_bool`; dropping them would break every existing
    /// invocation for no gain. `None` still means "follow verification" and is expressed by
    /// not passing the option at all, exactly as before.
    pub(crate) fn parse_trust_ir_lower(slot: &mut Option<TrustIrLower>, v: Option<&str>) -> bool {
        *slot = Some(match v {
            Some("y") | Some("yes") | Some("on") | Some("true") | None => TrustIrLower::On,
            Some("n") | Some("no") | Some("off") | Some("false") => TrustIrLower::Off,
            Some("strict") => TrustIrLower::Strict,
            _ => return false,
        });
        true
    }

    pub(crate) fn parse_trust_spawn_census_shadow(
        slot: &mut TrustSpawnCensusShadow,
        v: Option<&str>,
    ) -> bool {
        *slot = match v {
            Some("off") => TrustSpawnCensusShadow::Off,
            Some("report") => TrustSpawnCensusShadow::Report,
            Some("check") => TrustSpawnCensusShadow::Check,
            _ => return false,
        };
        true
    }

    /// Trust (platform protocols, plan L1a; FC-7): one comma-separated list of exact
    /// spellings. Every element must be a property this trustc checks; an unknown spelling, a
    /// property the design names but this trustc cannot check yet (`lock-release`,
    /// `fd-identity`), an empty value and an empty element are all refused, so neither a typo
    /// nor an older compiler can turn a policy off by having it quietly ignored. Duplicates are
    /// harmless and kept once. Repeating the option adds to the set and never removes from it
    /// (union, the monotone rule targo's workspace merge applies, OD-3). The slot is changed
    /// only when the whole value parses.
    pub(crate) fn parse_trust_platform_properties(
        slot: &mut TrustPlatformProperties,
        v: Option<&str>,
    ) -> bool {
        let Some(value) = v.filter(|value| !value.is_empty()) else {
            return false;
        };
        let mut parsed = Vec::new();
        for spelling in value.split(',') {
            match TrustPlatformProperty::from_spelling(spelling) {
                Ok(property) => parsed.push(property),
                Err(_) => return false,
            }
        }
        for property in parsed {
            slot.insert(property);
        }
        true
    }

    pub(crate) fn parse_trust_platform_unanalysed(
        slot: &mut TrustPlatformUnanalysed,
        v: Option<&str>,
    ) -> bool {
        *slot = match v {
            Some("warn") => TrustPlatformUnanalysed::Warn,
            Some("deny") => TrustPlatformUnanalysed::Deny,
            _ => return false,
        };
        true
    }

    /// Trust (platform protocols, plan L1a): the derivation budget, in STATES (D-15(D5)): a
    /// count, never a clock, so a verdict cannot depend on the machine. `0` is refused: a
    /// budget that explores nothing is not a budget, and no value switches the bound off.
    pub(crate) fn parse_trust_platform_budget(slot: &mut usize, v: Option<&str>) -> bool {
        let Some(value) =
            v.and_then(|value| value.parse::<usize>().ok()).filter(|value| *value > 0)
        else {
            return false;
        };
        *slot = value;
        true
    }

    pub(crate) fn parse_trust_platform_report(
        slot: &mut TrustPlatformReport,
        v: Option<&str>,
    ) -> bool {
        *slot = match v {
            Some("summary") => TrustPlatformReport::Summary,
            Some("verbose") => TrustPlatformReport::Verbose,
            _ => return false,
        };
        true
    }

    pub(crate) fn parse_trust_policy(slot: &mut TrustPolicy, v: Option<&str>) -> bool {
        *slot = match v {
            Some("strict") => TrustPolicy::Strict,
            Some("certify") => TrustPolicy::Certify,
            Some("advisory") => TrustPolicy::Advisory,
            Some("memory-safe") => TrustPolicy::MemorySafe,
            _ => return false,
        };
        true
    }

    // Trust: lane and store parse together. `mint`/`replay` without a store are
    // rejected rather than defaulted, because the managed store is only correct
    // for the managed lane — silently pointing an explicit mint at the managed
    // store in `<out-dir>` would overwrite the auto lane's own evidence.
    pub(crate) fn parse_trust_witness(slot: &mut TrustWitness, v: Option<&str>) -> bool {
        *slot = match v {
            Some("auto") => TrustWitness::Auto,
            Some("off") => TrustWitness::Off,
            Some(value) => match value.split_once(':') {
                Some((_, store)) if store.trim().is_empty() => return false,
                Some(("mint", store)) => TrustWitness::Mint(PathBuf::from(store)),
                Some(("replay", store)) => TrustWitness::Replay(PathBuf::from(store)),
                _ => return false,
            },
            None => return false,
        };
        true
    }

    pub(crate) fn parse_trust_verify_timeout_ms(slot: &mut u64, v: Option<&str>) -> bool {
        let Some(value) = v.and_then(|value| value.parse::<u64>().ok()).filter(|value| *value > 0)
        else {
            return false;
        };
        *slot = value;
        true
    }

    /// Trust: the one solver-effort count's SCALE `k` (plan
    /// `docs/design/2026-09-29-incremental-deterministic-trust-results.md` §3.2a):
    /// each ay query gets `min(100000, max(1, k · size))` SAT conflicts per SAT
    /// solve, `size` being its count of distinct terms. `k` is from 1 through
    /// 100,000 — `C`, `trust_types::determinism::EffortScale::CEILING`, P2's
    /// flat per-query count and below ay's own ground allowance, which an
    /// explicit `:rlimit` REPLACES — and nothing else: `0` would give every
    /// query the one-conflict floor, and a list is not a scale. Mirrors
    /// `trust_types::determinism::EffortScale::parse`, which this crate cannot
    /// name.
    pub(crate) fn parse_trust_verify_effort(slot: &mut u64, v: Option<&str>) -> bool {
        let Some(value) = v
            .and_then(|value| value.parse::<u64>().ok())
            .filter(|value| (1..=100_000).contains(value))
        else {
            return false;
        };
        *slot = value;
        true
    }

    /// Trust: the per-function preprocessing STEP budget (plan §3.2). A positive
    /// count, and nothing else: the step budget is the deterministic bound on
    /// preprocessing (a strictly decreasing count every instrumented loop
    /// polls), and there is no value that switches it off. The former `0 =
    /// disabled` arm left the wall clock as the only bound, and a clock stop is
    /// not reproducible (owner direction 2026-09-29: no switch that bypasses an
    /// important check; `trust_types::verify_budget::VerifyBudgetGuard::install`
    /// takes the count literally).
    pub(crate) fn parse_trust_verify_function_budget_steps(
        slot: &mut u64,
        v: Option<&str>,
    ) -> bool {
        let Some(value) = v.and_then(|value| value.parse::<u64>().ok()).filter(|value| *value > 0)
        else {
            return false;
        };
        *slot = value;
        true
    }

    pub(crate) fn parse_trust_verify_crate_role(slot: &mut String, v: Option<&str>) -> bool {
        let Some(value @ ("unscoped" | "primary" | "dependency" | "build-script")) = v else {
            return false;
        };
        *slot = value.to_string();
        true
    }

    // Trust: upstream's shared `MAX_THREADS_CAP` constant is gone in 1.101;
    // the verifier worker cap keeps the same bound locally.
    pub(crate) const MAX_TRUST_VERIFY_WORKER_THREADS_CAP: usize = 256;

    pub(crate) fn parse_trust_verify_worker_threads(slot: &mut usize, v: Option<&str>) -> bool {
        let Some(value) = v
            .and_then(|value| value.parse::<usize>().ok())
            .filter(|value| *value <= MAX_TRUST_VERIFY_WORKER_THREADS_CAP)
        else {
            return false;
        };
        *slot = value;
        true
    }

    pub(crate) fn parse_dump_mono_stats(slot: &mut DumpMonoStatsFormat, v: Option<&str>) -> bool {
        match v {
            None => true,
            Some("json") => {
                *slot = DumpMonoStatsFormat::Json;
                true
            }
            Some("markdown") => {
                *slot = DumpMonoStatsFormat::Markdown;
                true
            }
            Some(_) => false,
        }
    }

    pub(crate) fn parse_offload(slot: &mut Vec<Offload>, v: Option<&str>) -> bool {
        let Some(v) = v else {
            *slot = vec![];
            return true;
        };
        let mut v: Vec<&str> = v.split(",").collect();
        v.sort_unstable();
        for &val in v.iter() {
            // Split each entry on '=' if it has an argument
            let (key, arg) = match val.split_once('=') {
                Some((k, a)) => (k, Some(a)),
                None => (val, None),
            };

            let variant = match key {
                "Host" => {
                    if let Some(p) = arg {
                        Offload::Host(p.to_string())
                    } else {
                        return false;
                    }
                }
                "HostMetadata" => {
                    if let Some(p) = arg {
                        Offload::HostMetadata(p.to_string())
                    } else {
                        return false;
                    }
                }
                "Device" => {
                    // Without an argument, `Device` uses an empty manifest and all kernel
                    // instantiations are discovered via monomorphization.
                    Offload::Device(arg.unwrap_or_default().to_string())
                }
                "Test" => {
                    if let Some(_) = arg {
                        // Test does not accept a value
                        return false;
                    }
                    Offload::Test
                }
                _ => {
                    // FIXME(ZuseAY): print an error saying which value is not recognized
                    return false;
                }
            };
            slot.push(variant);
        }

        true
    }

    pub(crate) fn parse_autodiff(slot: &mut Vec<AutoDiff>, v: Option<&str>) -> bool {
        let Some(v) = v else {
            *slot = vec![];
            return true;
        };
        let mut v: Vec<&str> = v.split(",").collect();
        v.sort_unstable();
        for &val in v.iter() {
            // Split each entry on '=' if it has an argument
            let (key, arg) = match val.split_once('=') {
                Some((k, a)) => (k, Some(a)),
                None => (val, None),
            };

            let variant = match key {
                "Enable" => AutoDiff::Enable,
                "PrintTA" => AutoDiff::PrintTA,
                "PrintTAFn" => {
                    if let Some(fun) = arg {
                        AutoDiff::PrintTAFn(fun.to_string())
                    } else {
                        return false;
                    }
                }
                "PrintAA" => AutoDiff::PrintAA,
                "PrintPerf" => AutoDiff::PrintPerf,
                "PrintSteps" => AutoDiff::PrintSteps,
                "PrintModBefore" => AutoDiff::PrintModBefore,
                "PrintModAfter" => AutoDiff::PrintModAfter,
                "PrintModFinal" => AutoDiff::PrintModFinal,
                "NoPostopt" => AutoDiff::NoPostopt,
                "PrintPasses" => AutoDiff::PrintPasses,
                "LooseTypes" => AutoDiff::LooseTypes,
                "Inline" => AutoDiff::Inline,
                "NoTT" => AutoDiff::NoTT,
                _ => {
                    // FIXME(ZuseAY): print an error saying which value is not recognized
                    return false;
                }
            };
            slot.push(variant);
        }

        true
    }

    pub(crate) fn parse_instrument_coverage(
        slot: &mut InstrumentCoverage,
        v: Option<&str>,
    ) -> bool {
        if v.is_some() {
            let mut bool_arg = false;
            if parse_bool(&mut bool_arg, v) {
                *slot = if bool_arg { InstrumentCoverage::Yes } else { InstrumentCoverage::No };
                return true;
            }
        }

        let Some(v) = v else {
            *slot = InstrumentCoverage::Yes;
            return true;
        };

        // Parse values that have historically been accepted by stable compilers,
        // even though they're currently just aliases for boolean values.
        *slot = match v {
            "all" => InstrumentCoverage::Yes,
            "0" => InstrumentCoverage::No,
            _ => return false,
        };
        true
    }

    pub(crate) fn parse_codegen_retag_options(
        slot: &mut Option<CodegenRetagOptions>,
        v: Option<&str>,
    ) -> bool {
        let mut no_precise_im = false;
        let mut no_precise_pin = false;
        if let Some(opt_list) = v.map(|s| s.split(',')) {
            for opt in opt_list {
                match opt {
                    "no-precise-im" => {
                        no_precise_im = true;
                    }
                    "no-precise-pin" => {
                        no_precise_pin = true;
                    }
                    _ => return false,
                }
            }
        }
        *slot = Some(CodegenRetagOptions { no_precise_im, no_precise_pin });
        true
    }

    pub(crate) fn parse_coverage_options(slot: &mut CoverageOptions, v: Option<&str>) -> bool {
        let Some(v) = v else { return true };

        for option in v.split(',') {
            match option {
                "block" => slot.level = CoverageLevel::Block,
                "branch" => slot.level = CoverageLevel::Branch,
                "condition" => slot.level = CoverageLevel::Condition,
                "discard-all-spans-in-codegen" => slot.discard_all_spans_in_codegen = true,
                _ => return false,
            }
        }
        true
    }

    pub(crate) fn parse_instrument_mcount(slot: &mut InstrumentMcount, v: Option<&str>) -> bool {
        let mut use_mcount = false;
        let mut opts = InstrumentMcountOpts::default();
        if parse_bool(&mut use_mcount, v) {
            *slot = if use_mcount {
                InstrumentMcount::Mcount(opts)
            } else {
                InstrumentMcount::Disabled
            };
            return true;
        }
        match v {
            Some("fentry") => {
                *slot = InstrumentMcount::Fentry(opts);
            }
            Some("fentry-record") => {
                opts.record = true;
                *slot = InstrumentMcount::Fentry(opts);
            }
            Some("fentry-nop-record") => {
                opts.record = true;
                opts.no_call = true;
                *slot = InstrumentMcount::Fentry(opts);
            }
            _ => {
                return false;
            }
        }
        true
    }

    pub(crate) fn parse_instrument_xray(
        slot: &mut Option<InstrumentXRay>,
        v: Option<&str>,
    ) -> bool {
        if v.is_some() {
            let mut bool_arg = None;
            if parse_opt_bool(&mut bool_arg, v) {
                *slot = if bool_arg.unwrap() { Some(InstrumentXRay::default()) } else { None };
                return true;
            }
        }

        let options = slot.get_or_insert_default();
        let mut seen_always = false;
        let mut seen_never = false;
        let mut seen_ignore_loops = false;
        let mut seen_instruction_threshold = false;
        let mut seen_skip_entry = false;
        let mut seen_skip_exit = false;
        for option in v.map(|v| v.split(',')).into_flat_iter() {
            match option {
                "always" if !seen_always && !seen_never => {
                    options.always = true;
                    options.never = false;
                    seen_always = true;
                }
                "never" if !seen_never && !seen_always => {
                    options.never = true;
                    options.always = false;
                    seen_never = true;
                }
                "ignore-loops" if !seen_ignore_loops => {
                    options.ignore_loops = true;
                    seen_ignore_loops = true;
                }
                option
                    if option.starts_with("instruction-threshold")
                        && !seen_instruction_threshold =>
                {
                    let Some(("instruction-threshold", n)) = option.split_once('=') else {
                        return false;
                    };
                    match n.parse() {
                        Ok(n) => options.instruction_threshold = Some(n),
                        Err(_) => return false,
                    }
                    seen_instruction_threshold = true;
                }
                "skip-entry" if !seen_skip_entry => {
                    options.skip_entry = true;
                    seen_skip_entry = true;
                }
                "skip-exit" if !seen_skip_exit => {
                    options.skip_exit = true;
                    seen_skip_exit = true;
                }
                _ => return false,
            }
        }
        true
    }

    pub(crate) fn parse_treat_err_as_bug(
        slot: &mut Option<NonZero<usize>>,
        v: Option<&str>,
    ) -> bool {
        match v {
            Some(s) => match s.parse() {
                Ok(val) => {
                    *slot = Some(val);
                    true
                }
                Err(e) => {
                    *slot = None;
                    e.kind() == &IntErrorKind::Zero
                }
            },
            None => {
                *slot = NonZero::new(1);
                true
            }
        }
    }

    pub(crate) fn parse_next_solver_config(slot: &mut NextSolverConfig, v: Option<&str>) -> bool {
        if let Some(config) = v {
            *slot = match config {
                "no" | "coherence" => NextSolverConfig::Coherence,
                "globally" => NextSolverConfig::Globally,
                _ => return false,
            };
        } else {
            *slot = NextSolverConfig::Globally;
        }

        true
    }

    pub(crate) fn parse_lto(slot: &mut LtoCli, v: Option<&str>) -> bool {
        if v.is_some() {
            let mut bool_arg = None;
            if parse_opt_bool(&mut bool_arg, v) {
                *slot = if bool_arg.unwrap() { LtoCli::Yes } else { LtoCli::No };
                return true;
            }
        }

        *slot = match v {
            None => LtoCli::NoParam,
            Some("thin") => LtoCli::Thin,
            Some("fat") => LtoCli::Fat,
            Some(_) => return false,
        };
        true
    }

    pub(crate) fn parse_linker_plugin_lto(slot: &mut LinkerPluginLto, v: Option<&str>) -> bool {
        if v.is_some() {
            let mut bool_arg = None;
            if parse_opt_bool(&mut bool_arg, v) {
                *slot = if bool_arg.unwrap() {
                    LinkerPluginLto::LinkerPluginAuto
                } else {
                    LinkerPluginLto::Disabled
                };
                return true;
            }
        }

        *slot = match v {
            None => LinkerPluginLto::LinkerPluginAuto,
            Some(path) => LinkerPluginLto::LinkerPlugin(PathBuf::from(path)),
        };
        true
    }

    pub(crate) fn parse_switch_with_opt_path(
        slot: &mut SwitchWithOptPath,
        v: Option<&str>,
    ) -> bool {
        *slot = match v {
            None => SwitchWithOptPath::Enabled(None),
            Some(path) => SwitchWithOptPath::Enabled(Some(PathBuf::from(path))),
        };
        true
    }

    pub(crate) fn parse_merge_functions(
        slot: &mut Option<MergeFunctions>,
        v: Option<&str>,
    ) -> bool {
        match v.and_then(|s| MergeFunctions::from_str(s).ok()) {
            Some(mergefunc) => *slot = Some(mergefunc),
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_relocation_model(slot: &mut Option<RelocModel>, v: Option<&str>) -> bool {
        match v.and_then(|s| RelocModel::from_str(s).ok()) {
            Some(relocation_model) => *slot = Some(relocation_model),
            None if v == Some("default") => *slot = None,
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_code_model(slot: &mut Option<CodeModel>, v: Option<&str>) -> bool {
        match v.and_then(|s| CodeModel::from_str(s).ok()) {
            Some(code_model) => *slot = Some(code_model),
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_tls_model(slot: &mut Option<TlsModel>, v: Option<&str>) -> bool {
        match v.and_then(|s| TlsModel::from_str(s).ok()) {
            Some(tls_model) => *slot = Some(tls_model),
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_terminal_url(slot: &mut TerminalUrl, v: Option<&str>) -> bool {
        *slot = match v {
            Some("on" | "" | "yes" | "y") | None => TerminalUrl::Yes,
            Some("off" | "no" | "n") => TerminalUrl::No,
            Some("auto") => TerminalUrl::Auto,
            _ => return false,
        };
        true
    }

    pub(crate) fn parse_symbol_mangling_version(
        slot: &mut Option<SymbolManglingVersion>,
        v: Option<&str>,
    ) -> bool {
        *slot = match v {
            Some("legacy") => Some(SymbolManglingVersion::Legacy),
            Some("v0") => Some(SymbolManglingVersion::V0),
            Some("hashed") => Some(SymbolManglingVersion::Hashed),
            _ => return false,
        };
        true
    }

    pub(crate) fn parse_src_file_hash(
        slot: &mut Option<SourceFileHashAlgorithm>,
        v: Option<&str>,
    ) -> bool {
        match v.and_then(|s| SourceFileHashAlgorithm::from_str(s).ok()) {
            Some(hash_kind) => *slot = Some(hash_kind),
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_cargo_src_file_hash(
        slot: &mut Option<SourceFileHashAlgorithm>,
        v: Option<&str>,
    ) -> bool {
        match v.and_then(|s| SourceFileHashAlgorithm::from_str(s).ok()) {
            Some(hash_kind) => {
                *slot = Some(hash_kind);
            }
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_target_feature(slot: &mut String, v: Option<&str>) -> bool {
        match v {
            Some(s) => {
                if !slot.is_empty() {
                    slot.push(',');
                }
                slot.push_str(s);
                true
            }
            None => false,
        }
    }

    pub(crate) fn parse_link_self_contained(slot: &mut LinkSelfContained, v: Option<&str>) -> bool {
        // Whenever `-C link-self-contained` is passed without a value, it's an opt-in
        // just like `parse_opt_bool`, the historical value of this flag.
        //
        // 1. Parse historical single bool values
        let s = v.unwrap_or("y");
        match s {
            "y" | "yes" | "on" => {
                slot.set_all_explicitly(true);
                return true;
            }
            "n" | "no" | "off" => {
                slot.set_all_explicitly(false);
                return true;
            }
            _ => {}
        }

        // 2. Parse a list of enabled and disabled components.
        for comp in s.split(',') {
            if slot.handle_cli_component(comp).is_none() {
                return false;
            }
        }

        true
    }

    /// Parse a comma-separated list of enabled and disabled linker features.
    pub(crate) fn parse_linker_features(slot: &mut LinkerFeaturesCli, v: Option<&str>) -> bool {
        match v {
            Some(s) => {
                for feature in s.split(',') {
                    if slot.handle_cli_feature(feature).is_none() {
                        return false;
                    }
                }

                true
            }
            None => false,
        }
    }

    pub(crate) fn parse_wasi_exec_model(slot: &mut Option<WasiExecModel>, v: Option<&str>) -> bool {
        match v {
            Some("command") => *slot = Some(WasiExecModel::Command),
            Some("reactor") => *slot = Some(WasiExecModel::Reactor),
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_split_debuginfo(
        slot: &mut Option<SplitDebuginfo>,
        v: Option<&str>,
    ) -> bool {
        match v.and_then(|s| SplitDebuginfo::from_str(s).ok()) {
            Some(e) => *slot = Some(e),
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_split_dwarf_kind(slot: &mut SplitDwarfKind, v: Option<&str>) -> bool {
        match v.and_then(|s| SplitDwarfKind::from_str(s).ok()) {
            Some(e) => *slot = e,
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_stack_protector(slot: &mut StackProtector, v: Option<&str>) -> bool {
        match v.and_then(|s| StackProtector::from_str(s).ok()) {
            Some(ssp) => *slot = ssp,
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_branch_protection(
        slot: &mut Option<BranchProtection>,
        v: Option<&str>,
    ) -> bool {
        match v {
            Some(s) => {
                let slot = slot.get_or_insert_default();
                for opt in s.split(',') {
                    match opt {
                        "bti" => slot.bti = true,
                        "pac-ret" if slot.pac_ret.is_none() => {
                            // Note: some targets only support certain keys (Windows on Arm only
                            // supports Key B) and this possible discrepancy is handled by the
                            // session's `branch_protection` accessor, when we have both the target
                            // tuple and branch protection information available.
                            slot.pac_ret = Some(PacRet { leaf: false, pc: false, key: PAuthKey::A })
                        }
                        "leaf" => match slot.pac_ret.as_mut() {
                            Some(pac) => pac.leaf = true,
                            _ => return false,
                        },
                        "b-key" => match slot.pac_ret.as_mut() {
                            Some(pac) => pac.key = PAuthKey::B,
                            _ => return false,
                        },
                        "pc" => match slot.pac_ret.as_mut() {
                            Some(pac) => pac.pc = true,
                            _ => return false,
                        },
                        "gcs" => slot.gcs = true,
                        _ => return false,
                    };
                }
            }
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_collapse_macro_debuginfo(
        slot: &mut CollapseMacroDebuginfo,
        v: Option<&str>,
    ) -> bool {
        if v.is_some() {
            let mut bool_arg = None;
            if parse_opt_bool(&mut bool_arg, v) {
                *slot = if bool_arg.unwrap() {
                    CollapseMacroDebuginfo::Yes
                } else {
                    CollapseMacroDebuginfo::No
                };
                return true;
            }
        }

        *slot = match v {
            Some("external") => CollapseMacroDebuginfo::External,
            _ => return false,
        };
        true
    }

    pub(crate) fn parse_proc_macro_execution_strategy(
        slot: &mut ProcMacroExecutionStrategy,
        v: Option<&str>,
    ) -> bool {
        *slot = match v {
            Some("same-thread") => ProcMacroExecutionStrategy::SameThread,
            Some("cross-thread") => ProcMacroExecutionStrategy::CrossThread,
            _ => return false,
        };
        true
    }

    pub(crate) fn parse_inlining_threshold(slot: &mut InliningThreshold, v: Option<&str>) -> bool {
        match v {
            Some("always" | "yes") => {
                *slot = InliningThreshold::Always;
            }
            Some("never") => {
                *slot = InliningThreshold::Never;
            }
            Some(v) => {
                if let Ok(threshold) = v.parse() {
                    *slot = InliningThreshold::Sometimes(threshold);
                } else {
                    return false;
                }
            }
            None => return false,
        }
        true
    }

    pub(crate) fn parse_llvm_module_flag(
        slot: &mut Vec<(String, u32, String)>,
        v: Option<&str>,
    ) -> bool {
        let elements = v.unwrap_or_default().split(':').collect::<Vec<_>>();
        let [key, md_type, value, behavior] = elements.as_slice() else {
            return false;
        };
        if *md_type != "u32" {
            // Currently we only support u32 metadata flags, but require the
            // type for forward-compatibility.
            return false;
        }
        let Ok(value) = value.parse::<u32>() else {
            return false;
        };
        let behavior = behavior.to_lowercase();
        let all_behaviors =
            ["error", "warning", "require", "override", "append", "appendunique", "max", "min"];
        if !all_behaviors.contains(&behavior.as_str()) {
            return false;
        }

        slot.push((key.to_string(), value, behavior));
        true
    }

    pub(crate) fn parse_function_return(slot: &mut FunctionReturn, v: Option<&str>) -> bool {
        match v {
            Some("keep") => *slot = FunctionReturn::Keep,
            Some("thunk-extern") => *slot = FunctionReturn::ThunkExtern,
            _ => return false,
        }
        true
    }

    pub(crate) fn parse_wasm_c_abi(_slot: &mut (), v: Option<&str>) -> bool {
        v == Some("spec")
    }

    pub(crate) fn parse_mir_include_spans(slot: &mut MirIncludeSpans, v: Option<&str>) -> bool {
        *slot = match v {
            Some("on" | "yes" | "y" | "true") | None => MirIncludeSpans::On,
            Some("off" | "no" | "n" | "false") => MirIncludeSpans::Off,
            Some("nll") => MirIncludeSpans::Nll,
            _ => return false,
        };

        true
    }

    pub(crate) fn parse_align(slot: &mut Option<Align>, v: Option<&str>) -> bool {
        let mut bytes = 0u64;
        if !parse_number(&mut bytes, v) {
            return false;
        }

        let Ok(align) = Align::from_bytes(bytes) else {
            return false;
        };

        *slot = Some(align);

        true
    }

    pub(crate) fn parse_assert_incr_state(
        slot: &mut Option<IncrementalStateAssertion>,
        v: Option<&str>,
    ) -> bool {
        *slot = match v {
            Some("loaded") => Some(IncrementalStateAssertion::Loaded),
            Some("not-loaded") => Some(IncrementalStateAssertion::NotLoaded),
            _ => return false,
        };
        true
    }

    pub(crate) fn parse_rust_version(slot: &mut Option<RustcVersion>, v: Option<&str>) -> bool {
        let Some(v) = v else {
            return false;
        };
        if let Some(version) = RustcVersion::parse_str_strict(v) {
            *slot = Some(version);
            true
        } else {
            false
        }
    }
}

options! {
    CodegenOptions, CodegenOptionsTargetModifiers, CG_OPTIONS, cgopts, "C", "codegen",

    // If you add a new option, please update:
    // - compiler/rustc_interface/src/tests.rs
    // - src/doc/rustc/src/codegen-options/index.md

    // tidy-alphabetical-start
    ar: () = ((), parse_ignore, [UNTRACKED],
        "this option has been removed",
        removed: Err),
    #[rustc_lint_opt_deny_field_access("use `Session::code_model` instead of this field")]
    code_model: Option<CodeModel> = (None, parse_code_model, [TRACKED],
        "choose the code model to use (`rustc --print code-models` for details)"),
    codegen_units: Option<usize> = (None, parse_opt_number, [UNTRACKED],
        "divide crate into N units to optimize in parallel"),
    collapse_macro_debuginfo: CollapseMacroDebuginfo = (CollapseMacroDebuginfo::Unspecified,
        parse_collapse_macro_debuginfo, [TRACKED],
        "set option to collapse debuginfo for macros"),
    control_flow_guard: CFGuard = (CFGuard::Disabled, parse_cfguard, [TRACKED] { MITIGATION: ControlFlowGuard },
        "use Windows Control Flow Guard (default: no)"),
    debug_assertions: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "explicitly enable the `cfg(debug_assertions)` directive"),
    debuginfo: DebugInfo = (DebugInfo::None, parse_debuginfo, [TRACKED],
        "debug info emission level (0-2, none, line-directives-only, \
        line-tables-only, limited, or full; default: 0)"),
    default_linker_libraries: bool = (false, parse_bool, [UNTRACKED],
        "allow the linker to link its default libraries (default: no)"),
    dlltool: Option<PathBuf> = (None, parse_opt_pathbuf, [UNTRACKED],
        "import library generation tool (ignored except when targeting windows-gnu)"),
    #[rustc_lint_opt_deny_field_access("use `Session::dwarf_version` instead of this field")]
    dwarf_version: Option<u32> = (None, parse_opt_number, [TRACKED],
        "version of DWARF debug information to emit (default: 2 or 4, depending on platform)"),
    embed_bitcode: bool = (true, parse_bool, [TRACKED],
        "emit bitcode in rlibs (default: yes)"),
    embed_metadata: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "embed metadata in rlibs and dylibs (default: yes)"),
    extra_filename: String = (String::new(), parse_string, [UNTRACKED],
        "extra data to put in each output filename"),
    force_frame_pointers: FramePointer = (FramePointer::MayOmit, parse_frame_pointer, [TRACKED],
        "force use of the frame pointers"),
    #[rustc_lint_opt_deny_field_access("use `Session::must_emit_unwind_tables` instead of this field")]
    force_unwind_tables: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "force use of unwind tables"),
    help: bool = (false, parse_no_value, [UNTRACKED], "Print codegen options"),
    incremental: Option<String> = (None, parse_opt_string, [UNTRACKED],
        "enable incremental compilation"),
    inline_threshold: () = ((), parse_ignore, [UNTRACKED],
        "this option has been removed \
        (consider using `-Cllvm-args=--inline-threshold=...`)",
        removed: Err),
    #[rustc_lint_opt_deny_field_access("use `Session::instrument_coverage` instead of this field")]
    instrument_coverage: InstrumentCoverage = (InstrumentCoverage::No, parse_instrument_coverage, [TRACKED],
        "instrument the generated code to support LLVM source-based code coverage reports \
        (note, the compiler build config must include `profiler = true`); \
        implies `-C symbol-mangling-version=v0`"),
    jump_tables: bool = (true, parse_bool, [TRACKED],
        "allow jump table and lookup table generation from switch case lowering (default: yes)"),
    link_arg: (/* redirected to link_args */) = ((), parse_string_push, [UNTRACKED],
        "a single extra argument to append to the linker invocation (can be used several times)"),
    link_args: Vec<String> = (Vec::new(), parse_list, [UNTRACKED],
        "extra arguments to append to the linker invocation (space separated)"),
    #[rustc_lint_opt_deny_field_access("use `Session::link_dead_code` instead of this field")]
    link_dead_code: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "try to generate and link dead code (default: no)"),
    link_self_contained: LinkSelfContained = (LinkSelfContained::default(), parse_link_self_contained, [UNTRACKED],
        "control whether to link Rust provided C objects/libraries or rely \
        on a C toolchain or linker installed in the system"),
    linker: Option<PathBuf> = (None, parse_opt_pathbuf, [UNTRACKED],
        "system linker to link outputs with"),
    linker_features: LinkerFeaturesCli = (LinkerFeaturesCli::default(), parse_linker_features, [UNTRACKED],
        "a comma-separated list of linker features to enable (+) or disable (-): `lld`"),
    linker_flavor: Option<LinkerFlavorCli> = (None, parse_linker_flavor, [UNTRACKED],
        "linker flavor"),
    linker_plugin_lto: LinkerPluginLto = (LinkerPluginLto::Disabled,
        parse_linker_plugin_lto, [TRACKED],
        "generate build artifacts that are compatible with linker-based LTO"),
    llvm_args: Vec<String> = (Vec::new(), parse_list, [TRACKED],
        "a list of arguments to pass to LLVM (space separated)"),
    #[rustc_lint_opt_deny_field_access("use `Session::lto` instead of this field")]
    lto: LtoCli = (LtoCli::Unspecified, parse_lto, [TRACKED],
        "perform LLVM link-time optimizations"),
    metadata: Vec<String> = (Vec::new(), parse_list, [TRACKED],
        "metadata to mangle symbol names with"),
    no_prepopulate_passes: bool = (false, parse_no_value, [TRACKED],
        "give an empty list of passes to the pass manager"),
    no_redzone: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "disable the use of the redzone"),
    no_stack_check: () = ((), parse_ignore, [UNTRACKED],
        "this option has been removed",
        removed: Err),
    no_vectorize_loops: bool = (false, parse_no_value, [TRACKED],
        "disable loop vectorization optimization passes"),
    no_vectorize_slp: bool = (false, parse_no_value, [TRACKED],
        "disable LLVM's SLP vectorization pass"),
    opt_level: String = ("0".to_string(), parse_string, [TRACKED],
        "optimization level (0-3, s, or z; default: 0)"),
    #[rustc_lint_opt_deny_field_access("use `Session::overflow_checks` instead of this field")]
    overflow_checks: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "use overflow checks for integer arithmetic"),
    #[rustc_lint_opt_deny_field_access("use `Session::panic_strategy` instead of this field")]
    panic: Option<PanicStrategy> = (None, parse_opt_panic_strategy, [TRACKED],
        "panic strategy to compile crate with"),
    passes: Vec<String> = (Vec::new(), parse_list, [TRACKED],
        "a list of extra LLVM passes to run (space separated)"),
    prefer_dynamic: bool = (false, parse_bool, [TRACKED],
        "prefer dynamic linking to static linking (default: no)"),
    profile_generate: SwitchWithOptPath = (SwitchWithOptPath::Disabled,
        parse_switch_with_opt_path, [TRACKED],
        "compile the program with profiling instrumentation"),
    profile_sample_use: Option<PathBuf> = (None, parse_opt_pathbuf, [TRACKED],
        "use the given `.prof` file for sample-based profile-guided optimization"),
    profile_use: Option<PathBuf> = (None, parse_opt_pathbuf, [TRACKED],
        "use the given `.profdata` file for profile-guided optimization"),
    #[rustc_lint_opt_deny_field_access("use `Session::relocation_model` instead of this field")]
    relocation_model: Option<RelocModel> = (None, parse_relocation_model, [TRACKED],
        "control generation of position-independent code (PIC) \
        (`rustc --print relocation-models` for details)"),
    relro_level: Option<RelroLevel> = (None, parse_relro_level, [TRACKED],
        "choose which RELRO level to use"),
    remark: Passes = (Passes::Some(Vec::new()), parse_passes, [UNTRACKED],
        "output remarks for these optimization passes (space separated, or \"all\")"),
    rpath: bool = (false, parse_bool, [UNTRACKED],
        "set rpath values in libs/exes (default: no)"),
    save_temps: bool = (false, parse_bool, [UNTRACKED],
        "save all temporary output files during compilation (default: no)"),
    soft_float: () = ((), parse_ignore, [UNTRACKED],
        "this option has been removed \
        (use a corresponding *eabi target instead)",
        removed: Err),
    #[rustc_lint_opt_deny_field_access("use `Session::split_debuginfo` instead of this field")]
    split_debuginfo: Option<SplitDebuginfo> = (None, parse_split_debuginfo, [TRACKED],
        "how to handle split-debuginfo, a platform-specific option"),
    strip: Strip = (Strip::None, parse_strip, [UNTRACKED],
        "tell the linker which information to strip (`none` (default), `debuginfo` or `symbols`)"),
    symbol_mangling_version: Option<SymbolManglingVersion> = (None,
        parse_symbol_mangling_version, [TRACKED],
        "which mangling version to use for symbol names ('legacy', 'v0' (default), or 'hashed')"),
    target_cpu: Option<String> = (None, parse_opt_string, [TRACKED] { TARGET_MODIFIER: TargetCpu },
        "select target processor (`rustc --print target-cpus` for details) \
        The resulting binary must only be executed on CPUs that have all the features \
        of the given CPU."),
    target_feature: String = (String::new(), parse_target_feature, [TRACKED],
        "target-specific attributes (`rustc --print target-features` for details). \
        The resulting binary must only be executed on CPUs that have all the given features."),
    unsafe_allow_abi_mismatch: Vec<String> = (Vec::new(), parse_comma_list, [UNTRACKED],
        "Allow incompatible target modifiers in dependency crates (comma separated list)"),
    // tidy-alphabetical-end

    // If you add a new option, please update:
    // - compiler/rustc_interface/src/tests.rs
    // - src/doc/rustc/src/codegen-options/index.md
}

const POLONIUS_HELP: &str = match Polonius::DEFAULT {
    Polonius::Off => "enable polonius-based borrow-checker (default: no)",
    Polonius::Next => "enable polonius-based borrow-checker (default: next)",
    Polonius::Legacy => panic!("Polonius::Legacy is not a valid default value"),
};

options! {
    UnstableOptions, UnstableOptionsTargetModifiers, Z_OPTIONS, dbopts, "Z", "unstable",

    // If you add a new option, please update:
    // - compiler/rustc_interface/src/tests.rs
    // - src/doc/unstable-book/src/compiler-flags

    // tidy-alphabetical-start
    allow_features: Option<Vec<String>> = (None, parse_opt_comma_list, [TRACKED],
        "only allow the listed language features to be enabled in code (comma separated)"),
    // the real parser is at the `setter_for` macro, to allow `-Z` and `-C` options to
    // work together.
    allow_partial_mitigations: () = ((), parse_allow_partial_mitigations, [UNTRACKED],
        "Allow mitigations not enabled for all dependency crates (comma separated list)"),
    always_encode_mir: bool = (false, parse_bool, [TRACKED],
        "encode MIR of all functions into the crate metadata (default: no)"),
    annotate_moves: AnnotateMoves = (AnnotateMoves::Disabled, parse_annotate_moves, [TRACKED],
        "emit debug info for compiler-generated move and copy operations \
        to make them visible in profilers. Can be a boolean or a size limit in bytes (default: disabled)"),
    assert_incr_state: Option<IncrementalStateAssertion> = (None, parse_assert_incr_state, [UNTRACKED],
        "assert that the incremental cache is in given state: \
         either `loaded` or `not-loaded`."),
    assume_incomplete_release: bool = (false, parse_bool, [TRACKED],
        "make cfg(version) treat the current version as incomplete (default: no)"),
    assumptions_on_binders: bool = (false, parse_bool, [TRACKED],
        "allow deducing higher-ranked outlives assumptions from all binders (`for<'a>`); \
         implies `-Znext-solver=globally`"),
    async_panic: bool = (true, parse_bool, [TRACKED],
        "let async blocks and functions panic when polled after completion"),
    autodiff: Vec<crate::config::AutoDiff> = (Vec::new(), parse_autodiff, [TRACKED],
        "a list of autodiff flags to enable
        Mandatory setting:
        `=Enable`
        Optional extra settings:
        `=PrintTA`
        `=PrintAA`
        `=PrintPerf`
        `=PrintSteps`
        `=PrintModBefore`
        `=PrintModAfter`
        `=PrintModFinal`
        `=PrintPasses`,
        `=NoPostopt`
        `=LooseTypes`
        `=Inline`
        Multiple options can be combined with commas."),
    autodiff_post_passes: Option<String> = (None, parse_opt_string, [TRACKED],
        "set llvm passes to run after enzyme (no passes run when it is empty)"),
    #[rustc_lint_opt_deny_field_access("use `Session::binary_dep_depinfo` instead of this field")]
    binary_dep_depinfo: bool = (false, parse_bool, [TRACKED],
        "include artifacts (sysroot, crate dependencies) used during compilation in dep-info \
        (default: no)"),
    box_noalias: bool = (true, parse_bool, [TRACKED],
        "emit noalias metadata for box (default: yes)"),
    #[rustc_lint_opt_deny_field_access("use `Session::branch_protection` instead of this field")]
    branch_protection: Option<BranchProtection> = (None, parse_branch_protection, [TRACKED] { TARGET_MODIFIER: BranchProtection },
        "set options for branch target identification and pointer authentication on AArch64"),
    build_sdylib_interface: bool = (false, parse_bool, [UNTRACKED],
        "whether the stable interface is being built"),
    cache_proc_macros: bool = (false, parse_bool, [TRACKED],
        "cache the results of derive proc macro invocations (potentially unsound!) (default: no"),
    cf_protection: CFProtection = (CFProtection::None, parse_cfprotection, [TRACKED],
        "instrument control-flow architecture protection"),
    check_cfg_all_expected: bool = (false, parse_bool, [UNTRACKED],
        "show all expected values in check-cfg diagnostics (default: no)"),
    checksum_hash_algorithm: Option<SourceFileHashAlgorithm> = (None, parse_cargo_src_file_hash, [TRACKED],
        "hash algorithm of source files used to check freshness in cargo (`blake3` or `sha256`)"),
    // Trust: ordinary rustc surface, but once a command line selects a backend
    // that choice is immutable authority — a callback that swapped it would
    // change which machine code the recorded evidence describes.
    codegen_backend: Option<String> = (None, parse_opt_string, [TRACKED]
        { TRUST_AUTHORITY: AuthorityOnly },
        "the backend to use"),
    codegen_emit_retag: Option<CodegenRetagOptions> = (None, parse_codegen_retag_options, [TRACKED],
        "emit retag function calls in generated code"),
    codegen_source_order: bool = (false, parse_bool, [UNTRACKED],
        "emit mono items in the order of spans in source files (default: no)"),
    contract_checks: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "emit runtime checks for contract pre- and post-conditions (default: no)"),
    coverage_options: CoverageOptions = (CoverageOptions::default(), parse_coverage_options, [TRACKED],
        "control details of coverage instrumentation"),
    crate_attr: Vec<String> = (Vec::new(), parse_string_push, [TRACKED],
        "inject the given attribute in the crate"),
    cross_crate_inline_threshold: InliningThreshold = (InliningThreshold::Sometimes(100), parse_inlining_threshold, [TRACKED],
        "threshold to allow cross crate inlining of functions"),
    debug_info_type_line_numbers: bool = (false, parse_bool, [TRACKED],
        "emit type and line information for additional data types (default: no)"),
    debuginfo_compression: DebugInfoCompression = (DebugInfoCompression::None, parse_debuginfo_compression, [TRACKED],
        "compress debug info sections (none, zlib, zstd, default: none)"),
    debuginfo_for_profiling: bool = (false, parse_bool, [TRACKED],
        "emit extra debug info to make sample profile more accurate"),
    deduplicate_diagnostics: bool = (true, parse_bool, [UNTRACKED],
        "deduplicate identical diagnostics (default: yes)"),
    default_visibility: Option<SymbolVisibility> = (None, parse_opt_symbol_visibility, [TRACKED],
        "overrides the `default_visibility` setting of the target"),
    deny_partial_mitigations: () = ((), parse_deny_partial_mitigations, [UNTRACKED],
        "Deny mitigations not enabled for all dependency crates (comma separated list)"),
    dep_info_omit_d_target: bool = (false, parse_bool, [TRACKED],
        "in dep-info output, omit targets for tracking dependencies of the dep-info files \
        themselves (default: no)"),
    direct_access_external_data: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "Direct or use GOT indirect to reference external data symbols"),
    disable_fast_paths: bool = (false, parse_bool, [TRACKED],
        "disable various performance optimizations in trait solving"),
    disable_incr_comp_backend_caching: bool = (false, parse_bool, [TRACKED],
        "disable caching of compiled objects by the codegen backend during incremental compilation"),
    disable_param_env_normalization_hack: bool = (false, parse_bool, [TRACKED],
        "do not treat all aliases in the environment as rigid with `-Znext-solver`"),
    dual_proc_macros: bool = (false, parse_bool, [TRACKED],
        "load proc macros for both target and host, but only link to the target (default: no)"),
    dump_dep_graph: bool = (false, parse_bool, [UNTRACKED],
        "dump the dependency graph to `$RUST_DEP_GRAPH` as both a text file and a GraphViz dot file (default: ./dep_graph.{dot, txt}) \
        (default: no)"),
    dump_mir: Option<String> = (None, parse_opt_string, [UNTRACKED],
        "dump MIR state to file.
        `val` is used to select which passes and functions to dump. For example:
        `all` matches all passes and functions,
        `foo` matches all passes for functions whose name contains 'foo',
        `foo & ConstProp` only the 'ConstProp' pass for function names containing 'foo',
        `foo | bar` all passes for function names containing 'foo' or 'bar'."),
    dump_mir_dataflow: bool = (false, parse_bool, [UNTRACKED],
        "in addition to `.mir` files, create graphviz `.dot` files with dataflow results \
        (default: no)"),
    dump_mir_dir: String = ("mir_dump".to_string(), parse_string, [UNTRACKED],
        "the directory the MIR is dumped into (default: `mir_dump`)"),
    dump_mir_exclude_alloc_bytes: bool = (false, parse_bool, [UNTRACKED],
        "exclude the raw bytes of allocations when dumping MIR (used in tests) (default: no)"),
    dump_mir_exclude_pass_number: bool = (false, parse_bool, [UNTRACKED],
        "exclude the pass number when dumping MIR (used in tests) (default: no)"),
    dump_mir_graphviz: bool = (false, parse_bool, [UNTRACKED],
        "in addition to `.mir` files, create graphviz `.dot` files (default: no)"),
    dump_mono_stats: SwitchWithOptPath = (SwitchWithOptPath::Disabled,
        parse_switch_with_opt_path, [UNTRACKED],
        "output statistics about monomorphization collection"),
    dump_mono_stats_format: DumpMonoStatsFormat = (DumpMonoStatsFormat::Markdown, parse_dump_mono_stats, [UNTRACKED],
        "the format to use for -Z dump-mono-stats (`markdown` (default) or `json`)"),
    #[rustc_lint_opt_deny_field_access("use `Session::dwarf_version` instead of this field")]
    dwarf_version: Option<u32> = (None, parse_opt_number, [TRACKED],
        "version of DWARF debug information to emit (default: 2 or 4, depending on platform)"),
    dylib_lto: bool = (false, parse_bool, [UNTRACKED],
        "enables LTO for dylib crate type"),
    eagerly_emit_delayed_bugs: bool = (false, parse_bool, [UNTRACKED],
        "emit delayed bugs eagerly as errors instead of stashing them and emitting \
        them only if an error has not been emitted"),
    ehcont_guard: bool = (false, parse_bool, [TRACKED],
        "generate Windows EHCont Guard tables"),
    // FIXME(kobzol): remove in 2027
    embed_metadata: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "embed metadata in rlibs and dylibs (default: yes)"),
    embed_source: bool = (false, parse_bool, [TRACKED],
        "embed source text in DWARF debug sections (default: no)"),
    emit_stack_sizes: bool = (false, parse_bool, [UNTRACKED],
        "emit a section containing stack size metadata (default: no)"),
    enforce_type_length_limit: bool = (false, parse_bool, [TRACKED],
        "enforce the type length limit when monomorphizing instances in codegen"),
    experimental_default_bounds: bool = (false, parse_bool, [TRACKED],
        "enable default bounds for experimental group of auto traits"),
    export_executable_symbols: bool = (false, parse_bool, [TRACKED],
        "export symbols from executables, as if they were dynamic libraries"),
    external_clangrt: bool = (false, parse_bool, [UNTRACKED],
        "rely on user specified linker commands to find clangrt"),
    extra_const_ub_checks: bool = (false, parse_bool, [TRACKED],
        "turns on more checks to detect const UB, which can be slow (default: no)"),
    #[rustc_lint_opt_deny_field_access("use `Session::fewer_names` instead of this field")]
    fewer_names: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "reduce memory use by retaining fewer names within compilation artifacts (LLVM-IR) \
        (default: no)"),
    fixed_x18: bool = (false, parse_bool, [TRACKED] { TARGET_MODIFIER: FixedX18 },
        "make the x18 register reserved on AArch64 (default: no)"),
    flatten_format_args: bool = (true, parse_bool, [TRACKED],
        "flatten nested format_args!() and literals into a simplified format_args!() call \
        (default: yes)"),
    fmt_debug: FmtDebug = (FmtDebug::Full, parse_fmt_debug, [TRACKED],
        "how detailed `#[derive(Debug)]` should be. `full` prints types recursively, \
        `shallow` prints only type names, `none` prints nothing and disables `{:?}`. (default: `full`)"),
    force_intrinsic_fallback: bool = (false, parse_bool, [TRACKED],
        "always use the fallback body of an intrinsic, if it has one, instead of lowering \
        the intrinsic in the codegen backend (default: no)."),
    force_unstable_if_unmarked: bool = (false, parse_bool, [TRACKED],
        "force all crates to be `rustc_private` unstable (default: no)"),
    function_return: FunctionReturn = (FunctionReturn::default(), parse_function_return, [TRACKED],
        "replace returns with jumps to `__x86_return_thunk` (default: `keep`)"),
    function_sections: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "whether each function should go in its own section"),
    future_incompat_test: bool = (false, parse_bool, [UNTRACKED],
        "forces all lints to be future incompatible, used for internal testing (default: no)"),
    graphviz_dark_mode: bool = (false, parse_bool, [UNTRACKED],
        "use dark-themed colors in graphviz output (default: no)"),
    graphviz_font: String = ("Courier, monospace".to_string(), parse_string, [UNTRACKED],
        "use the given `fontname` in graphviz output; can be overridden by setting \
        environment variable `RUSTC_GRAPHVIZ_FONT` (default: `Courier, monospace`)"),
    has_thread_local: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "explicitly enable the `cfg(target_thread_local)` directive"),
    help: bool = (false, parse_no_value, [UNTRACKED], "Print unstable compiler options"),
    higher_ranked_assumptions: bool = (false, parse_bool, [TRACKED],
        "allow deducing higher-ranked outlives assumptions from coroutines when proving auto traits"),
    hint_mostly_unused: bool = (false, parse_bool, [TRACKED],
        "hint that most of this crate will go unused, to minimize work for uncalled functions"),
    hint_msrv: Option<RustcVersion> = (None, parse_rust_version, [TRACKED],
        "control the minimum rust version for lints"),
    human_readable_cgu_names: bool = (false, parse_bool, [TRACKED],
        "generate human-readable, predictable names for codegen units (default: no)"),
    identify_regions: bool = (false, parse_bool, [UNTRACKED],
        "display unnamed regions as `'<id>`, using a non-ident unique id (default: no)"),
    ignore_directory_in_diagnostics_source_blocks: Vec<String> = (Vec::new(), parse_string_push, [UNTRACKED],
        "do not display the source code block in diagnostics for files in the directory"),
    implicit_sysroot_deps: bool = (true, parse_bool, [TRACKED],
        "allows rust to search sysroot for a crate's dependencies (default: yes)"),
    incremental_ignore_spans: bool = (false, parse_bool, [TRACKED],
        "ignore spans during ICH computation -- used for testing (default: no)"),
    incremental_info: bool = (false, parse_bool, [UNTRACKED],
        "print high-level information about incremental reuse (or the lack thereof) \
        (default: no)"),
    incremental_verify_ich: bool = (false, parse_bool, [UNTRACKED],
        "verify extended properties for incr. comp. (default: no):
        - hashes of green query instances
        - hash collisions of query keys
        - hash collisions when creating dep-nodes"),
    indirect_branch_cs_prefix: bool = (false, parse_bool, [TRACKED] { TARGET_MODIFIER: IndirectBranchCsPrefix },
        "add `cs` prefix to `call` and `jmp` to indirect thunks (default: no)"),
    inline_llvm: bool = (true, parse_bool, [TRACKED],
        "enable LLVM inlining (default: yes)"),
    inline_mir: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "enable MIR inlining (default: no)"),
    inline_mir_forwarder_threshold: Option<usize> = (None, parse_opt_number, [TRACKED],
        "inlining threshold when the caller is a simple forwarding function (default: 30)"),
    inline_mir_hint_threshold: Option<usize> = (None, parse_opt_number, [TRACKED],
        "inlining threshold for functions with inline hint (default: 100)"),
    inline_mir_preserve_debug: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "when MIR inlining, whether to preserve debug info for callee variables \
        (default: preserve for debuginfo != None, otherwise remove)"),
    inline_mir_threshold: Option<usize> = (None, parse_opt_number, [TRACKED],
        "a default MIR inlining threshold (default: 50)"),
    input_stats: bool = (false, parse_bool, [UNTRACKED],
        "print some statistics about AST and HIR (default: no)"),
    instrument_mcount: InstrumentMcount = (InstrumentMcount::Disabled, parse_instrument_mcount, [TRACKED],
        "insert function instrument code for mcount-based tracing (default: no)"),
    instrument_xray: Option<InstrumentXRay> = (None, parse_instrument_xray, [TRACKED],
        "insert function instrument code for XRay-based tracing (default: no)
         Optional extra settings:
         `=always`
         `=never`
         `=ignore-loops`
         `=instruction-threshold=N`
         `=skip-entry`
         `=skip-exit`
         Multiple options can be combined with commas."),
    // The only purpose of this flag is to act as a deterrent:
    // Marking a feature that's only meant for testing as internal might not preclude somebody from
    // trying to use it in `core` or `std` as both enable various internal features and utilize them
    // throughout. This is intentionally a flag not another internal feature as having to modify the
    // build cfg in `bootstrap` is arguably scarier than just needing to add `#![feature]`. It also
    // stands out a lot more during code review making it easier to get caught.
    internal_testing_features: bool = (false, parse_bool, [TRACKED],
        "allow certain internal language features to be enabled that help exercise & test the compiler"),
    large_data_threshold: Option<u64> = (None, parse_opt_number, [TRACKED],
        "set the threshold for objects to be stored in a \"large data\" section \
         (only effective with -Ccode-model=medium, default: 65536)"),
    layout_seed: Option<u64> = (None, parse_opt_number, [TRACKED],
        "seed layout randomization"),
    link_directives: bool = (true, parse_bool, [TRACKED],
        "honor #[link] directives in the compiled crate (default: yes)"),
    link_native_libraries: bool = (true, parse_bool, [UNTRACKED],
        "link native libraries in the linker invocation (default: yes)"),
    link_only: bool = (false, parse_bool, [TRACKED],
        "link the `.rlink` file generated by `-Z no-link` (default: no)"),
    lint_llvm_ir: bool = (false, parse_bool, [TRACKED],
        "lint LLVM IR (default: no)"),
    lint_mir: bool = (false, parse_bool, [UNTRACKED],
        "lint MIR before and after each transformation"),
    llvm_module_flag: Vec<(String, u32, String)> = (Vec::new(), parse_llvm_module_flag, [TRACKED],
        "a list of module flags to pass to LLVM (space separated)"),
    llvm_plugins: Vec<String> = (Vec::new(), parse_list, [TRACKED],
        "a list LLVM plugins to enable (space separated)"),
    llvm_target_feature: String = (String::new(), parse_target_feature, [TRACKED] { TARGET_MODIFIER: LlvmTargetFeature },
        "enable/disable LLVM-level target features. \
        This feature is unsafe and can cause ABI issues and compiler crashes, \
        because LLVM does not support all target feature combinations."),
    llvm_time_trace: bool = (false, parse_bool, [UNTRACKED],
        "generate JSON tracing data file from LLVM data (default: no)"),
    llvm_writable: bool = (false, parse_bool, [TRACKED],
        "emit the LLVM writable attribute for mutable reference arguments (default: no)"),
    location_detail: LocationDetail = (LocationDetail::all(), parse_location_detail, [TRACKED],
        "what location details should be tracked when using caller_location, either \
        `none`, or a comma separated list of location details, for which \
        valid options are `file`, `line`, and `column` (default: `file,line,column`)"),
    ls: Vec<String> = (Vec::new(), parse_list, [UNTRACKED],
        "decode and print various parts of the crate metadata for a library crate \
        (space separated)"),
    macro_backtrace: bool = (false, parse_bool, [UNTRACKED],
        "show macro backtraces (default: no)"),
    macro_stats: bool = (false, parse_bool, [UNTRACKED],
        "print some statistics about macro expansions (default: no)"),
    maximal_hir_to_mir_coverage: bool = (false, parse_bool, [TRACKED],
        "save as much information as possible about the correspondence between MIR and HIR \
        as source scopes (default: no)"),
    #[rustc_lint_opt_deny_field_access("use `Session::merge_functions` instead of this field")]
    merge_functions: Option<MergeFunctions> = (None, parse_merge_functions, [TRACKED],
        "control the operation of the MergeFunctions LLVM pass, taking \
        the same values as the target option of the same name"),
    meta_stats: bool = (false, parse_bool, [UNTRACKED],
        "gather metadata statistics (default: no)"),
    metadata_crate_hash: bool = (true, parse_bool, [TRACKED],
        "compute the crate hash (SVH) from the encoded crate metadata; set to `no` to \
         revert to computing it from the HIR (default: yes)"),
    metrics_dir: Option<PathBuf> = (None, parse_opt_pathbuf, [UNTRACKED],
        "the directory metrics emitted by rustc are dumped into (implicitly enables default set of metrics)"),
    min_function_alignment: Option<Align> = (None, parse_align, [TRACKED],
        "align all functions to at least this many bytes. Must be a power of 2"),
    min_recursion_limit: Option<usize> = (None, parse_opt_number, [TRACKED],
        "set a minimum recursion limit (final limit = max(this, recursion_limit_from_crate))"),
    mir_enable_passes: Vec<(String, bool)> = (Vec::new(), parse_list_with_polarity, [TRACKED],
        "use like `-Zmir-enable-passes=+DestinationPropagation,-InstSimplify`. Forces the \
        specified passes to be enabled, overriding all other checks. In particular, this will \
        enable unsound (known-buggy and hence usually disabled) passes without further warning! \
        Passes that are not specified are enabled or disabled by other flags as usual."),
    mir_include_spans: MirIncludeSpans = (MirIncludeSpans::default(), parse_mir_include_spans, [UNTRACKED],
        "include extra comments in mir pretty printing, like line numbers and statement indices, \
         details about types, etc. (boolean for all passes, 'nll' to enable in NLL MIR only, default: 'nll')"),
    mir_move_elimination: bool = (false, parse_bool, [TRACKED],
        "enable the experimental MIR semantics for the move elimination optimization (default: no)"),
    mir_opt_bisect_limit: Option<usize> = (None, parse_opt_number, [TRACKED],
        "limit the number of MIR optimization pass executions (global across all bodies). \
        Pass executions after this limit are skipped and reported. (default: no limit)"),
    #[rustc_lint_opt_deny_field_access("use `Session::mir_opt_level` instead of this field")]
    mir_opt_level: Option<usize> = (None, parse_opt_number, [TRACKED],
        "MIR optimization level (0-4; default: 1 in non optimized builds and 2 in optimized builds)"),
    mir_preserve_ub: bool = (false, parse_bool, [TRACKED],
        "keep place mention statements and reads in trivial SwitchInt terminators, which are interpreted \
        e.g., by miri; implies -Zmir-opt-level=0 (default: no)"),
    mir_strip_debuginfo: MirStripDebugInfo = (MirStripDebugInfo::None, parse_mir_strip_debuginfo, [TRACKED],
        "Whether to remove some of the MIR debug info from methods.  Default: None"),
    move_size_limit: Option<usize> = (None, parse_opt_number, [TRACKED],
        "the size at which the `large_assignments` lint starts to be emitted"),
    namespaced_crates: bool = (false, parse_bool, [TRACKED],
        "allow crates to be namespaced by other crates (default: no)"),
    next_solver: NextSolverConfig = (NextSolverConfig::default(), parse_next_solver_config, [TRACKED],
        "enable and configure the next generation trait solver used by rustc"),
    nll_facts: bool = (false, parse_bool, [UNTRACKED],
        "dump facts from NLL analysis into side files (default: no)"),
    nll_facts_dir: String = ("nll-facts".to_string(), parse_string, [UNTRACKED],
        "the directory the NLL facts are dumped into (default: `nll-facts`)"),
    no_analysis: bool = (false, parse_no_value, [UNTRACKED],
        "parse and expand the source, but run no analysis"),
    no_codegen: bool = (false, parse_no_value, [TRACKED_NO_CRATE_HASH],
        "run all passes except codegen; no output"),
    no_generate_arange_section: bool = (false, parse_no_value, [TRACKED],
        "omit DWARF address ranges that give faster lookups"),
    no_implied_bounds_compat: bool = (false, parse_bool, [TRACKED],
        "disable the compatibility version of the `implied_bounds_ty` query"),
    no_leak_check: bool = (false, parse_no_value, [UNTRACKED],
        "disable the 'leak check' for subtyping; unsound, but useful for tests"),
    no_link: bool = (false, parse_no_value, [TRACKED],
        "compile without linking"),
    no_parallel_backend: bool = (false, parse_no_value, [UNTRACKED],
        "use `--jobs-backend=1` instead"),
    no_profiler_runtime: bool = (false, parse_no_value, [TRACKED],
        "prevent automatic injection of the profiler_builtins crate"),
    no_steal_thir: bool = (false, parse_bool, [UNTRACKED],
        "don't steal the THIR when we're done with it; useful for rustc drivers (default: no)"),
    no_trait_vptr: bool = (false, parse_no_value, [TRACKED],
        "disable generation of trait vptr in vtable for upcasting"),
    no_unique_section_names: bool = (false, parse_bool, [TRACKED],
        "do not use unique names for text and data sections when -Z function-sections is used"),
    normalize_docs: bool = (false, parse_bool, [TRACKED],
        "normalize associated items in rustdoc when generating documentation"),
    offload: Vec<crate::config::Offload> = (Vec::new(), parse_offload, [TRACKED],
        "a list of offload flags to enable
        Mandatory setting:
        `=Enable`
        Currently the only option available"),
    on_broken_pipe: OnBrokenPipe = (OnBrokenPipe::Default, parse_on_broken_pipe, [TRACKED],
        "behavior of std::io::ErrorKind::BrokenPipe (SIGPIPE)"),
    osx_rpath_install_name: bool = (false, parse_bool, [TRACKED],
        "pass `-install_name @rpath/...` to the macOS linker (default: no)"),
    packed_bundled_libs: bool = (false, parse_bool, [TRACKED],
        "change rlib format to store native libraries as archives"),
    packed_stack: bool = (false, parse_bool, [TRACKED],
        "use packed stack frames (s390x only) (default: no)"),
    panic_abort_tests: bool = (false, parse_bool, [TRACKED],
        "support compiling tests with panic=abort (default: no)"),
    panic_in_drop: PanicStrategy = (PanicStrategy::Unwind, parse_panic_strategy, [TRACKED],
        "panic strategy for panics in drops"),
    parse_crate_root_only: bool = (false, parse_bool, [UNTRACKED],
        "parse the crate root file only; do not parse other files, compile, assemble, or link \
        (default: no)"),
    patchable_function_entry: PatchableFunctionEntry = (PatchableFunctionEntry::default(), parse_patchable_function_entry, [TRACKED],
        "nop padding at function entry"),
    plt: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "whether to use the PLT when calling into shared libraries;
        only has effect for PIC code on systems with ELF binaries
        (default: PLT is disabled if full relro is enabled on x86_64)"),
    pointer_authentication: Vec<(PointerAuthOption, bool)> = (
        Vec::new(),
        parse_pointer_authentication_list_with_polarity,
        [TRACKED]
        { TARGET_MODIFIER: PointerAuthentication },
        "A comma-separated list of pointer authentication options, each prefixed with `+` (enable) or `-` (disable). Available options:
        `aarch64-jump-table-hardening` - enable hardened lowering for jump-table dispatch
        `auth-traps` - trap immediately on pointer authentication failure
        `calls` - enable signing and authentication of all indirect calls
        `elf-got` - enable authentication of pointers from GOT (ELF only)
        `function-pointer-type-discrimination` - enable type discrimination on C function pointers
        `indirect-gotos` - enable signing and authentication of indirect goto targets
        `init-fini` - enable signing of function pointers in init/fini arrays
        `init-fini-address-discrimination` - enable address discrimination in init/fini arrays
        `intrinsics` - pointer authentication intrinsics
        `return-addresses` - enable signing and authentication of return addresses
        `typeinfo-vt-ptr-discrimination - incorporate type and address discrimination in authenticated vtable pointers for std::type_info
        `vt-ptr-addr-discrimination - incorporate address discrimination in authenticated vtable pointers
        `vt-ptr-type-discrimination - incorporate type discrimination in authenticated vtable pointers
        Example: `-Zpointer-authentication=+calls,-init-fini`."),
    polonius: Polonius = (Polonius::default(), parse_polonius, [TRACKED],
        POLONIUS_HELP),
    pre_link_arg: (/* redirected to pre_link_args */) = ((), parse_string_push, [UNTRACKED],
        "a single extra argument to prepend the linker invocation (can be used several times)"),
    pre_link_args: Vec<String> = (Vec::new(), parse_list, [UNTRACKED],
        "extra arguments to prepend to the linker invocation (space separated)"),
    precise_enum_drop_elaboration: bool = (true, parse_bool, [TRACKED],
        "use a more precise version of drop elaboration for matches on enums (default: yes). \
        This results in better codegen, but has caused miscompilations on some tier 2 platforms. \
        See #77382 and #74551."),
    #[rustc_lint_opt_deny_field_access("use `Session::print_codegen_stats` instead of this field")]
    print_codegen_stats: bool = (false, parse_bool, [UNTRACKED],
        "print codegen statistics (default: no)"),
    #[rustc_lint_opt_deny_field_access("use `Session::print_llvm_stats_json` instead of this field")]
    print_codegen_stats_json: Option<String> = (None, parse_opt_string, [UNTRACKED],
        "print codegen statistics in JSON to a file (default: no)"),
    print_llvm_passes: bool = (false, parse_bool, [UNTRACKED],
        "print the LLVM optimization passes being run (default: no)"),
    print_mono_items: bool = (false, parse_bool, [UNTRACKED],
        "print the result of the monomorphization collection pass (default: no)"),
    print_type_sizes: bool = (false, parse_bool, [UNTRACKED],
        "print layout information for each type encountered (default: no)"),
    proc_macro_backtrace: bool = (false, parse_bool, [UNTRACKED],
         "show backtraces for panics during proc-macro execution (default: no)"),
    proc_macro_execution_strategy: ProcMacroExecutionStrategy = (ProcMacroExecutionStrategy::SameThread,
        parse_proc_macro_execution_strategy, [UNTRACKED],
        "how to run proc-macro code (default: same-thread)"),
    profile_closures: bool = (false, parse_no_value, [UNTRACKED],
        "profile size of closures"),
    profiler_runtime: String = (String::from("profiler_builtins"), parse_string, [TRACKED],
        "name of the profiler runtime crate to automatically inject (default: `profiler_builtins`)"),
    query_dep_graph: bool = (false, parse_bool, [UNTRACKED],
        "enable queries of the dependency graph for regression testing (default: no)"),
    randomize_layout: bool = (false, parse_bool, [TRACKED],
        "randomize the layout of types (default: no)"),
    reg_struct_return: bool = (false, parse_bool, [TRACKED] { TARGET_MODIFIER: RegStructReturn },
        "On x86-32 targets, it overrides the default ABI to return small structs in registers.
        It is UNSOUND to link together crates that use different values for this flag!"),
    regparm: Option<u32> = (None, parse_opt_number, [TRACKED] { TARGET_MODIFIER: Regparm },
        "On x86-32 targets, setting this to N causes the compiler to pass N arguments \
        in registers EAX, EDX, and ECX instead of on the stack for\
        \"C\", \"cdecl\", and \"stdcall\" fn.\
        It is UNSOUND to link together crates that use different values for this flag!"),
    relax_elf_relocations: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "whether ELF relocations can be relaxed (x86 only)"),
    remap_cwd_prefix: Option<PathBuf> = (None, parse_opt_pathbuf, [TRACKED],
        "remap paths under the current working directory to this path prefix"),
    remark_dir: Option<PathBuf> = (None, parse_opt_pathbuf, [UNTRACKED],
        "directory into which to write optimization remarks (if not specified, they will be \
written to standard error output)"),
    renormalize_rigid_aliases: bool = (false, parse_bool, [TRACKED],
        "do not skip rigid aliases in normalization for internal debugging"),
    retpoline: bool = (false, parse_bool, [TRACKED] { TARGET_MODIFIER: Retpoline },
        "enables retpoline-indirect-branches and retpoline-indirect-calls target features (default: no)"),
    retpoline_external_thunk: bool = (false, parse_bool, [TRACKED] { TARGET_MODIFIER: RetpolineExternalThunk },
        "enables retpoline-external-thunk, retpoline-indirect-branches and retpoline-indirect-calls \
        target features (default: no)"),
    #[rustc_lint_opt_deny_field_access("use `Session::sanitizers()` instead of this field")]
    sanitizer: SanitizerSet = (SanitizerSet::empty(), parse_sanitizers, [TRACKED] { TARGET_MODIFIER: Sanitizer },
        "use a sanitizer"),
    sanitizer_ignorelist: Vec<String> = (vec![], parse_list, [TRACKED],
        "list of files providing ignorelists for sanitizers"),
    sanitizer_cfi_canonical_jump_tables: Option<bool> = (Some(true), parse_opt_bool, [TRACKED],
        "enable canonical jump tables (default: yes)"),
    sanitizer_cfi_generalize_pointers: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "enable generalizing pointer types (default: no)"),
    sanitizer_cfi_normalize_integers: Option<bool> = (None, parse_opt_bool, [TRACKED] { TARGET_MODIFIER: SanitizerCfiNormalizeIntegers },
        "enable normalizing integer types (default: no)"),
    sanitizer_cfi_diag: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "enable CFI diagnostics (default: no)"),
    sanitizer_cfi_recover: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "enable CFI recovery (default: no)"),
    sanitizer_cfi_minimal_runtime: Option<bool> = (None, parse_opt_bool, [TRACKED] { TARGET_MODIFIER: SanitizerCfiMinimalRuntime },
        "enable minimal UBSan runtime for CFI (default: no)"),
    sanitizer_dataflow_abilist: Vec<String> = (Vec::new(), parse_comma_list, [TRACKED],
        "additional ABI list files that control how shadow parameters are passed (comma separated)"),
    sanitizer_kcfi_arity: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "enable KCFI arity indicator (default: no)"),
    sanitizer_memory_track_origins: usize = (0, parse_sanitizer_memory_track_origins, [TRACKED],
        "enable origins tracking in MemorySanitizer"),
    sanitizer_recover: SanitizerSet = (SanitizerSet::empty(), parse_sanitizers, [TRACKED],
        "enable recovery for selected sanitizers"),
    self_profile: SwitchWithOptPath = (SwitchWithOptPath::Disabled,
        parse_switch_with_opt_path, [UNTRACKED],
        "run the self profiler and output the raw event data"),
    self_profile_counter: String = ("wall-time".to_string(), parse_string, [UNTRACKED],
        "counter used by the self profiler (default: `wall-time`), one of:
        `wall-time` (monotonic clock, i.e. `std::time::Instant`)
        `instructions:u` (retired instructions, userspace-only)
        `instructions-minus-irqs:u` (subtracting hardware interrupt counts for extra accuracy)"
    ),
    /// keep this in sync with the event filter names and defaults in rustc_data_structures/src/profiling.rs
    self_profile_events: Option<Vec<String>> = (None, parse_opt_comma_list, [UNTRACKED],
        "specify the events recorded by the self profiler;
        for example: `-Z self-profile-events=default,query-keys`
        all option groups: none, all, default, args
          `default` contains: generic-activity, query-provider, query-cache-hit-count, \
                            query-blocked, incr-cache-load, incr-result-hashing, artifact-sizes
             `args` contains: query-keys, function-args
        remaining (ungrouped) options: query-cache-hit, llvm"),
    share_generics: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "make the current crate share its generic instantiations"),
    shell_argfiles: bool = (false, parse_bool, [UNTRACKED],
        "allow argument files to be specified with POSIX \"shell-style\" argument quoting"),
    simulate_remapped_rust_src_base: Option<PathBuf> = (None, parse_opt_pathbuf, [TRACKED],
        "simulate the effect of remap-debuginfo = true at bootstrapping by remapping path \
        to rust's source base directory. only meant for testing purposes"),
    small_data_threshold: Option<usize> = (None, parse_opt_number, [TRACKED],
        "Set the threshold for objects to be stored in a \"small data\" section"),
    span_debug: bool = (false, parse_bool, [UNTRACKED],
        "forward proc_macro::Span's `Debug` impl to `Span`"),
    /// o/w tests have closure@path
    span_free_formats: bool = (false, parse_bool, [UNTRACKED],
        "exclude spans when debug-printing compiler state (default: no)"),
    split_dwarf_inlining: bool = (false, parse_bool, [TRACKED],
        "provide minimal debug info in the object/executable to facilitate online \
         symbolication/stack traces in the absence of .dwo/.dwp files when using Split DWARF"),
    split_dwarf_kind: SplitDwarfKind = (SplitDwarfKind::Split, parse_split_dwarf_kind, [TRACKED],
        "split dwarf variant (only if -Csplit-debuginfo is enabled and on relevant platform)
        (default: `split`)

        `split`: sections which do not require relocation are written into a DWARF object (`.dwo`)
                 file which is ignored by the linker
        `single`: sections which do not require relocation are written into object file but ignored
                  by the linker"),
    split_dwarf_out_dir : Option<PathBuf> = (None, parse_opt_pathbuf, [TRACKED],
        "location for writing split DWARF objects (`.dwo`) if enabled"),
    split_lto_unit: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "enable LTO unit splitting (default: no)"),
    src_hash_algorithm: Option<SourceFileHashAlgorithm> = (None, parse_src_file_hash, [TRACKED],
        "hash algorithm of source files in debug info (`md5`, `sha1`, or `sha256`)"),
    // Trust: rust-lang#100914 — completes the half-adopted `large_stack_frame` lint.
    stack_frame_limit: Option<usize> = (None, parse_opt_number, [TRACKED],
        "the size at which the `large_stack_frame` lint starts to be emitted"),
    #[rustc_lint_opt_deny_field_access("use `Session::stack_protector` instead of this field")]
    stack_protector: StackProtector = (StackProtector::None, parse_stack_protector, [TRACKED] { MITIGATION: StackProtector },
        "control stack smash protection strategy (`rustc --print stack-protector-strategies` for details)"),
    staticlib_allow_rdylib_deps: bool = (false, parse_bool, [TRACKED],
        "allow staticlibs to have rust dylib dependencies"),
    staticlib_hide_internal_symbols: bool = (false, parse_bool, [TRACKED],
        "hide non-exported Rust symbols when building staticlibs by setting STV_HIDDEN"),
    staticlib_rename_internal_symbols: bool = (false, parse_bool, [TRACKED],
        "rename non-exported Rust symbols when building staticlibs to avoid conflicts"),
    staticlib_prefer_dynamic: bool = (false, parse_bool, [TRACKED],
        "prefer dynamic linking to static linking for staticlibs (default: no)"),
    strict_init_checks: bool = (false, parse_bool, [TRACKED],
        "control if mem::uninitialized and mem::zeroed panic on more UB"),
    #[rustc_lint_opt_deny_field_access("use `Session::teach` instead of this field")]
    teach: bool = (false, parse_bool, [TRACKED],
        "show extended diagnostic help (default: no)"),
    temps_dir: Option<String> = (None, parse_opt_string, [UNTRACKED],
        "the directory the intermediate files are written to"),
    terminal_urls: TerminalUrl = (TerminalUrl::No, parse_terminal_url, [UNTRACKED],
        "use the OSC 8 hyperlink terminal specification to print hyperlinks in the compiler output"),
    #[rustc_lint_opt_deny_field_access("use `Session::lto` instead of this field")]
    thinlto: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "enable ThinLTO when possible"),
    /// Trust (T4.3): a proof session runs one front-end thread whatever this
    /// asks (`trust_frontend_threads_by_flags`; DECISION_QUEUE
    /// FRONTEND-THREADS-1), so read it through `Session::threads`.
    threads: Option<String> = (None, parse_opt_string, [UNTRACKED],
        "use `--jobs-frontend` instead (a Trust proof session runs one thread)"),
    time_llvm_passes: bool = (false, parse_bool, [UNTRACKED],
        "measure time of each LLVM pass (default: no)"),
    time_passes: bool = (false, parse_bool, [UNTRACKED],
        "measure time of each rustc pass (default: no)"),
    time_passes_format: TimePassesFormat = (TimePassesFormat::Text, parse_time_passes_format, [UNTRACKED],
        "the format to use for -Z time-passes (`text` (default) or `json`)"),
    tiny_const_eval_limit: bool = (false, parse_bool, [TRACKED],
        "sets a tiny, non-configurable limit for const eval; useful for compiler tests"),
    #[rustc_lint_opt_deny_field_access("use `Session::tls_model` instead of this field")]
    tls_model: Option<TlsModel> = (None, parse_tls_model, [TRACKED],
        "choose the TLS model to use (`rustc --print tls-models` for details)"),
    trace_macros: bool = (false, parse_bool, [UNTRACKED],
        "for every macro invocation, print its name and arguments (default: no)"),
    track_diagnostics: bool = (false, parse_bool, [UNTRACKED],
        "tracks where in rustc a diagnostic was emitted"),
    translate_remapped_path_to_local_path: bool = (true, parse_bool, [TRACKED],
        "translate remapped paths into local paths when possible (default: yes)"),
    trap_unreachable: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "generate trap instructions for unreachable intrinsics (default: use target setting, usually yes)"),
    treat_err_as_bug: Option<NonZero<usize>> = (None, parse_treat_err_as_bug, [TRACKED],
        "treat the `val`th error that occurs as bug (default if not specified: 0 - don't treat errors as bugs. \
        default if specified without a value: 1 - treat the first error as bug)"),
    trim_diagnostic_paths: bool = (true, parse_bool, [UNTRACKED],
        "in diagnostics, use heuristics to shorten paths referring to items"),
    // Trust doctrine: verification is batteries-on. Raw/unscoped and
    // Cargo-authenticated primary crates are strict by default; dependency and
    // build-script roles are scoped explicitly. Flags may loosen policy or use
    // the single `trust_verify` domain, never enable a dormant verifier.
    //
    // Every option below carries a TRUST_AUTHORITY class. The class is what the
    // frontend-authority inventory is built from, so it lives at the
    // declaration and not in a second list somewhere else: a `-Ztrust-*` option
    // without one fails to compile (`trust_authority_classification`).
    // Trust (cross-crate composition): the BUILD-DECLARED foreign bundling
    // scope. Names a crate whose already-compiled bodies the verifier may pull
    // into a caller's lowered bundle and RE-DERIVE obligations from, exactly as
    // it already does for `std`/`core`/`alloc`.
    //
    // This declares a SCOPE, never a verdict. No foreign proof result is
    // readable in this compilation — `trust_proof_results` is `arena_cache`
    // only, with no `separate_provide_extern` and no `cache_on_disk` — so a
    // crate named here gets its MIR read and every obligation over it minted and
    // discharged by THIS compilation's verifier. Admitting a body can therefore
    // only ADD obligations the caller must discharge; a body that fails to lower
    // falls back to the pre-existing fail-closed absent-callee row.
    //
    // It is a CALLER-side declaration on purpose. The 2026-08-25 cross-crate
    // admission hole keyed on `#[automatically_derived]`, a callee SELF-CLAIM
    // that is stable, ungated and user-writable. A scope named by the invoking
    // build (Targo injects the workspace-internal dependency units it compiled
    // itself) is not a claim the callee makes about itself.
    trust_bundle_foreign_crate: Vec<String> = (Vec::<String>::new(), parse_trust_bundle_foreign_crate, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "declare, as one comma-separated list, the crates whose foreign bodies may be bundled \
         into a caller's lowered verification bundle and re-derived there, on the same footing as \
         `std`/`core`/`alloc`. This carries no foreign verdict: every obligation over an admitted \
         body is minted and discharged by this compilation. Only fully non-generic callees are \
         admitted"),
    // Trust (F1): WHICH PRODUCER supplies the trust-cg backend's per-function
    // input. This is a `-Z` option and not a cargo feature (the two earlier
    // trust-ir probes were cargo features) for three reasons that all matter to
    // the evidence:
    //   * it is per-INVOCATION, so ONE compiler binary emits both paths and
    //     "the default path is byte-identical" becomes a diff of two objects
    //     from the same trustc rather than a claim about a differently-built
    //     dylib;
    //   * it is [TRACKED], so the choice enters the crate hash — an option that
    //     changes which machine code is emitted must, or artifacts produced by
    //     the two producers could be confused for each other on a warm cache;
    //   * it lands in the TRUST_AUTHORITY inventory, the existing boundary for
    //     "a caller changed which evidence this compilation produces".
    // `trust-ir` is FAIL-CLOSED end to end: a mono-item the `trust_ir_of` query
    // declines, or a Module the converter refuses, is a compile ERROR. It never
    // falls back to the MIR path, because a silent fallback would make the flag
    // worthless as evidence.
    trust_cg_frontend: String = ("mir".to_string(), parse_trust_cg_frontend, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "which producer supplies the trust-cg backend's per-function input: `mir` (the default \
         and the shipped path — rustc MIR -> VerifiableFunction -> LIR) or `trust-ir` (the \
         source-first F1 path — THIR -> `trust_ir_of` -> trust_ir::Module -> LIR). `trust-ir` \
         requires -Ztrust-ir-lower and fails the build on any item the producer or the converter \
         declines -- it never falls back to the MIR path, so one unsupported item refuses the \
         whole crate. It IS verified by the proven-output gate (the spec is derived from the \
         trust-ir module rather than from MIR) and needs no gate relaxation: it emits under the \
         default `strict`"),
    // Trust (step 2 increment 5, sub-step 5.4.2; docs/design/2026-10-08-step2-inc5-step4-
    // compiler-lane-plan.md §2): WHICH CONSUMER compiles F1's trust-ir. `lir` is today's lane
    // (`lower_module_to_lir` per function, the module-to-LIR gate); `compiler` is the opt-in
    // compiler lane: one codegen module per crate (`codegen_module.rs`), trust-cg's
    // `Compiler::compile`, and the call-event refinement gate over the shipped object, which is
    // F1's only shipping authority on that lane (owner rulings D30-D32). [TRACKED] in the
    // TRUST_AUTHORITY inventory for the same reason as `trust_cg_frontend`: it changes which
    // machine code and which evidence a compilation produces.
    trust_cg_f1_backend: String = ("lir".to_string(), parse_trust_cg_f1_backend, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "with -Ztrust-cg-frontend=trust-ir, which consumer compiles the trust-ir: `lir` (the \
         default — each function lowered to LIR and gated by the module-to-LIR proven-output \
         gate) or `compiler` (opt-in, step 2 increment 5 — one codegen module per crate compiled \
         by trust-cg's `Compiler::compile` with real calls, shipped only when the call-event \
         refinement gate's closure report allows it under the output-gate policy). `compiler` \
         refuses, by name, what it does not yet carry: targets other than aarch64-apple-darwin \
         and aarch64-unknown-linux-gnu, `-Ztrust-cg-output-gate=off`, and -Ztrust-ir-crate-module"),
    trust_ir_crate_module: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "with -Ztrust-cg-frontend=trust-ir, take the lowering context from the crate module the \
         producer PUBLISHES and bind the trust-ir v41 CODEGEN LICENSE \
         (`Function.body_gate`) as a whole-module negative gate, instead of selecting each body \
         through the per-instance assembled handoff. Off by default, and the default is not a \
         weaker gate: the handoff lane selects a body by exact (DefIndex, DefPathHash) identity, \
         while this lane resolves it by the producer's DISPLAY path, so a collision-renamed body \
         is refused here and admitted there. What this lane adds is the license: every body in \
         the lowering context must carry a positive gate from a RECOGNIZED authority, which \
         makes an appended below-tier definition refuse the whole crate rather than be reachable \
         by inlining"),
    trust_cg_output_gate: String = ("strict".to_string(), parse_trust_cg_output_gate, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "set the trust-cg output-preservation gate: `strict` (the default) rejects an unknown \
         output-preservation outcome, `allow-unknown` records it, `off` disables the gate; \
         batteries-on strict verification pins this to `strict` and rejects `off`"),
    // Trust: the ONE channel through which the out-of-tree trust-ir → trust-cg
    // backend (`-Zcodegen-backend=trust-ir-cg`, built from
    // first-party/trust-cg/crates/rustc-codegen-trust-cg by bootstrap) receives
    // its knobs. That backend used to read ~30 `TCG_*` environment variables
    // (proof-certificate opt-out, structured JSON diagnostics, batching and
    // trace switches). trustc refuses every `TCG_*`/`TRUST_CG_*` variable as an
    // untracked codegen control (`UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES`), and
    // rightly so: an environment variable is not part of the crate hash, so a
    // knob that changes emitted code or the evidence attached to it would make
    // incremental reuse and evidence provenance lie. A TRACKED option is what
    // the refusal message tells the user to use instead; this is it. The value
    // is a space-separated list of `key` / `key=value` items the backend parses
    // in its own `init`; rustc assigns them no meaning. EvidenceControl because
    // `no-proof-certs` and friends change what the artifact can claim.
    trust_ir_cg_args: Vec<String> = (Vec::<String>::new(), parse_list, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "a space-separated list of `key` / `key=value` knobs for the trust-ir → trust-cg codegen \
         backend (`-Zcodegen-backend=trust-ir-cg`); the backend parses them, rustc does not. \
         This is the tracked replacement for that backend's former `TCG_*` environment \
         variables, which trustc refuses as untracked codegen controls"),
    trust_certified_test_monitors: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "reserved internal Targo phase-A fingerprint for a non-`--test` monitor subject; it has no independent authority and requires the paired -Ztrust-targo-test-monitor session-consistency selector"),
    trust_body_census: Option<PathBuf> = (None, parse_trust_nonempty_path, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "write a diagnostic HIR body-owner census to a NEW JSONL file, independently of direct \
         lowering; requires -Zchecksum-hash-algorithm=sha256; missing completion footer is \
         incomplete evidence, and HIR owners are not the reachable-instance/runtime census"),
    // Trust: opt-in schema extension; the default body census remains v2.
    trust_body_census_calls: bool = (false, parse_bool, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "include diagnostic post-typecheck HIR call observations in body-census v3; requires \
         -Ztrust-body-census; does not establish complete inputs, runtime calls, or proof authority"),
    trust_instance_census: Option<PathBuf> = (None, parse_trust_nonempty_path, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "write a diagnostic concrete mono-item/root/usage/CGU census to a NEW JSONL file; \
         requires -Zchecksum-hash-algorithm=sha256; observes normal collection without \
         forcing codegen, and explicitly leaves non-collected runtime/linker items unmeasured"),
    trust_lean_census: Option<PathBuf> = (None, parse_trust_nonempty_path, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "write a diagnostic census of actual HIR-admitted Lean island checks to a NEW JSONL file; \
         requires -Zchecksum-hash-algorithm=sha256; preserves sequential and header-first \
         checking semantics, and does not claim a complete runtime-body denominator"),
    // Trust (spawn census P4): the trust-ir lane of the spawn census, in SHADOW. It runs at
    // the analysis seam after whole-crate verification, reads `trust_ir_of` for every fn-like
    // body the MIR lane answers for (unsafety checking keeps THIR for it), and prints the
    // differential; it changes no verdict, row or diagnostic. TRACKED_NO_CRATE_HASH, like
    // `-Ztrust-dump`: evidence production that changes no emitted byte.
    trust_spawn_census_shadow: TrustSpawnCensusShadow = (TrustSpawnCensusShadow::Off,
        parse_trust_spawn_census_shadow, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "MEASUREMENT ONLY: run the spawn census's trust-ir lane in shadow beside the MIR lane that \
         decides every verdict, and print, per fn-like body, both lanes' verdicts, their \
         agreement and what keeps the trust-ir lane from deciding (`report`); `check` also fails \
         the build when the trust-ir lane is QUIET where the MIR lane refuses, or reaches a spawn \
         where it is QUIET, and when the MIR lane's census fell back so nothing was compared. \
         Needs verification (default: off)"),
    // Trust (lane CTFE): a MEASUREMENT probe, never a code path. `mir_built`
    // returns early for a trivial const, so the CTFE flip seam
    // (`try_flip_ctfe`, the single call site of the CTFE flip) is never
    // demanded for one and the whole population is invisible to any
    // log-reading instrument. This flag replays the seam's decision over
    // exactly those bodies and DISCARDS the result, so it can only add log
    // lines. TRACKED_NO_CRATE_HASH, like `-Ztrust-dump`: it is dependency-
    // tracked evidence production that changes no emitted byte.
    trust_ctfe_trivial_probe: bool = (false, parse_bool, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "MEASUREMENT ONLY: replay the CTFE flip seam's decision procedure over every trivial \
         const in the crate (a body `mir_built` fast-paths, so the seam is never demanded for \
         it) and log what it WOULD decide, discarding the derived body; installs nothing and \
         changes no emitted code (default: no)"),
    // Trust: EW18-DROPIN-1 (2026-11-05), the explicit opt-in to EW-18's Darwin rule
    // (`darwin_rlib_objects_are_archive_members` in rustc_codegen_ssa's link.rs). By
    // default an rlib-only compilation with unpacked split debuginfo keeps its objects
    // beside the rlib, as upstream does: which files a compilation leaves is something
    // a valid tool can see, so the drop-in rule keeps upstream's default. UNTRACKED,
    // like `-Csave-temps`: it decides only what is deleted after the link, never a
    // byte of an output. AuthorityOnly: deauthorization resets it to `false`, so an
    // embedded frontend (tippy, trustdoc, a driver that links) given it in shared
    // RUSTFLAGS keeps what upstream's would keep.
    trust_drop_rlib_objects: bool = (false, parse_bool, [UNTRACKED]
        { TRUST_AUTHORITY: AuthorityOnly },
        "on Apple targets with `-Csplit-debuginfo=unpacked`, delete an rlib-only compilation's \
         object files once the rlib holds them as members, which is what a debug map names; \
         upstream keeps them (default: no)"),
    trust_dump: TrustDump = (TrustDump::default(), parse_trust_dump, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "publish one Trust verification artifact to a non-empty directory: `mir:<dir>` writes each \
         extracted MIR verification input, `mir-only:<dir>` writes them and skips solver/certifier \
         dispatch (requires the nonfatal `-Ztrust-policy=advisory`), `native-bundle:<dir>` \
         writes each finalized native TrustIr verification bundle, `ir:<dir>` writes the assembled \
         crate-level TrustIr lowering artifacts under a pre-input publication lease (the \
         user-facing spelling for that last artifact is `--emit=trust-ir`), `spec-clean:<dir>` \
         writes one JSONL row per kernel-graded spec goal exactly as the discharge lane graded it \
         (the `targo trust spec --emit clean` session artifact); repeat the option for \
         more than one sink"),
    // Trust (wall A, the INSTANCE flip seam): like `trust_ir_flip`, this may replace the MIR
    // codegen consumes, so it is TRACKED — two builds that differ here must not share an
    // artifact identity. `=no` is the lane's negative control (the "delete the seam" arm of the
    // mutation matrix): the registry still records nothing, and nothing installs.
    trust_instance_flip: bool = (true, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "allow the Trust-IR flip to install derived MIR PER INSTANCE at the codegen seam, for \
         generic bodies the DefId seam cannot flip, after a per-instance differential proof \
         (default: yes; requires -Ztrust-ir-lower and -Ztrust-ir-flip)"),
    // Trust (wall A): the ADVERSARIAL controls for the instance seam — each corrupts one input
    // of the per-instance evidence chain and must make the flip VANISH, never produce a body.
    // TRACKED because a control that changed emitted code without changing the crate hash would
    // be indistinguishable from the real thing in a cached build.
    trust_instance_flip_mutate: Option<String> = (None, parse_opt_string, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "wall-A mutation control: corrupt one input of the per-instance flip's evidence chain and \
         require the differential to catch it. `abi-anchor` derives at IDENTITY args instead of \
         the instance's; `abi-swap` swaps the first two re-derived ABI anchors (and REFUSES, \
         loudly, where a signature has no two distinct ones to swap); `abi-ret` derives at a \
         wrong return anchor (which bites every signature whose Module HAS a return value); \
         `abi-arg0` derives at a wrong FIRST-ARGUMENT anchor, which bites every signature that \
         takes one; `incumbent-args` instantiates the \
         incumbent at the wrong args; `lineage` corrupts the recorded lineage digest. Only those \
         six spellings are matched: any other value is not rejected and runs the ordinary, \
         un-mutated flip"),
    trust_ir_flip: bool = (true, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "allow the direct Trust-IR frontend to derive compatibility/codegen MIR after an exact differential proof (default: yes)"),
    // Trust (wall A, instance-flip probe): MEASUREMENT ONLY — stashes nothing but
    // Session-local clones, installs no body, changes no emitted code. UNTRACKED for
    // exactly that reason: two compiles differing only in this flag emit identical
    // artifacts. The driver's option-domain gate requires -Ztrust-verify=off
    // -Ztrust-ir-lower and refuses every -Ztrust-dump sink (see
    // trust_thir_lower::instance_probe module docs for the double-count rationale).
    trust_instance_flip_probe: Option<String> = (None, parse_opt_string, [UNTRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "wall-A measurement probe: for generic `agreed` bodies matching the given def-path \
         substring (`*` = all), measure per-instance differential agreement and ABI \
         rederivation at concrete GenericArgs; prints TRUST-WALLA-PROBE lines to stderr; \
         requires -Ztrust-verify=off -Ztrust-ir-lower and no -Ztrust-dump sink"),
    // This is in the crate hash: the TrustIr flip may replace codegen/CTFE MIR,
    // so builds that differ here must not share an artifact identity.
    // Trust (B3-2a): the SAT-perturbation negative control — re-landing the retired
    // TRUST_*_PERTURB env hooks as a tracked -Z flag (env vars are banned ambient
    // inputs; see LEGACY_TRUST_SEMANTIC_ENV_VARS). A perturbed compile deliberately
    // corrupts one shim lowering class so the flip comparator MUST reject it — the
    // control proving the differential gate has teeth. TRACKED with crate-hash for
    // the same reason as trust_ir_flip: an uncaught perturbation changes emitted
    // MIR, so perturbed incremental artifacts must never share identity with clean
    // ones. Accepted only by the explicit direct-TrustIR burn-in lane (see the
    // driver option-domain validation).
    trust_sat_perturb: Option<String> = (None, parse_opt_string, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "burn-in SAT control: deliberately perturb one shim lowering class          (enum-reshape|enum-case-value|enum-ctor|enum-disc-index|switch-map|enum-payload|marker-order|marker-drop|agg-field-order|marker-arm|payload-tramp|dr-tramp|dr-retire|mc-plan|cf-lit-order|chain-ret-order|cf-field-drop|cf-unit-late|cf-pair-order|cf-ret-late|cf-post-late|sw-tramp|swr-tramp|g25-hoist|seq-unit-late|g21-ret-order|uc-unit-late) so the          flip comparator must reject it; requires -Ztrust-verify=off -Ztrust-ir-lower"),
    // Trust: tri-state because no single static default is true of this option.
    // The direct frontend is not optional under verification, so an unset
    // request follows verification; only the explicit `-Ztrust-verify=off`
    // compatibility lane leaves the decision to the caller, and that lane must
    // keep the ordinary Rust path clear unless lowering is asked for. A `bool`
    // could only declare one of those two answers and would be a lie in the
    // other lane. `trust_ir_lower_enabled_by_flags` resolves it; the driver
    // stamps the resolved value back into this field before any hash is taken,
    // so every spelling of one compilation keeps one tracked identity.
    trust_ir_lower: Option<TrustIrLower> = (None, parse_trust_ir_lower, [TRACKED]
        { TRUST_AUTHORITY: AuthorityOnly },
        "how far to run the direct source (THIR) to Trust-IR frontend: off|on|strict (default: \
         unset, meaning follow verification; batteries-on verification always runs it, so an \
         explicit value only takes effect in the -Ztrust-verify=off compatibility lane, where the \
         default is off). `strict` additionally makes a body the producer cannot fully lower a \
         compile error instead of a coverage-only skip, and so is a body whose trust-ir does not \
         carry every effect of its built MIR or models a value by abstraction (the \
         effect-conservation gate, docs/DECISION_QUEUE.md D28) — under verification only: \
         -Ztrust-verify=off is the master off-switch, so there `strict` degrades to `on` and \
         never fails a build"),
    // Trust (memory): the verifier's retained-memory notes — `trust: memory
    // checkpoint` each time the resident size read at a body boundary crosses
    // another 4 GiB, and `trust: memory census` at crate end. OPT-IN, default
    // off, because both report the HOST's resident size: left on by default they
    // made a compile's diagnostics depend on the machine and its allocator (main's
    // 5aa81ac168 measured tests/ui/borrowck/ever-init-many-locals.rs at 4858 MB
    // max RSS, over the first checkpoint), so a ui test's stderr would too. A flag,
    // never an environment variable: a semantic `TRUST_*` variable is refused.
    // TRACKED_NO_CRATE_HASH, like `-Ztrust-verify-output`: it adds diagnostics, so
    // incremental reuse must not replay a session compiled without it, and it
    // changes no emitted byte, so the crate hash stays put.
    // A VerificationSelector: both readers are in the verification pass (the
    // per-body compaction guard and the crate-end census after the
    // -Ztrust-verify=off early return), so an evidence-deauthorized frontend,
    // which runs no verification, accepts it and resets it.
    trust_memory_notes: bool = (false, parse_bool, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: VerificationSelector },
        "MEASUREMENT ONLY: emit the Trust verifier's retained-memory notes — a `trust: memory \
         checkpoint` note each time the resident size read at a body boundary crosses another \
         4 GiB, and a `trust: memory census` note at crate end (artifact slots compacted, \
         compacted slots recomputed, resident sizes); host-dependent by nature, never a verdict \
         (default: no)"),
    // Trust (temporal P3, the send census): for every thread the spawn census
    // finds, a note naming each std channel send the thread can reach, with the
    // message type and a shortest call path (the actors a derived model would
    // have, and what each posts). OPT-IN and diagnostics only, like
    // `-Ztrust-memory-notes`: TRACKED_NO_CRATE_HASH, since it adds notes and
    // changes no emitted byte. It forces the spawn census, which reads only
    // standard MIR queries, so it reports in either lane.
    trust_send_census: bool = (false, parse_bool, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "report, for every spawned thread (and `main`), each std channel send it can reach: \
         the message type and a shortest call path, as notes at the spawn site (either lane; \
         default: no)"),
    // Trust (temporal P3, design 2026-09-29 §3c.2): the writer census. For a
    // field path on a message consumer's `self` (`config.harness` names
    // `App::config.harness` when `App::user_event` consumes the message), a note
    // at every write that may overlap it and the consumer arm or thread that
    // reaches it. Diagnostics only, like `-Ztrust-send-census`, whose censuses it
    // runs (silently unless that flag is set too); either lane.
    trust_writer_census: Option<String> = (None, parse_opt_string, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "report every write that may overlap this field path of a message consumer's `self` \
         (`config.harness`), with the consumer arm or thread that reaches it, as notes (either \
         lane; default: none)"),
    // Trust (D2 tier 1): the negative control for the ADAPTER_YIELD modeled
    // fact. Setting it can only LOSE proofs (no premise is ever installed).
    trust_no_adapter_yield: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "disable the ADAPTER_YIELD modeled fact (a closure handed to a core iterator adapter \
         over a traced std receiver is otherwise verified assuming it only receives items \
         that receiver yields)"),
    // Trust (STR_BYTE_POSITION, 2026-10-04).
    trust_no_str_byte_position: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "disable the STR_BYTE_POSITION modeled fact (the index `s.bytes().position(|b| b == K)` \
         returns for an ASCII `K` is otherwise credited as a char boundary of `s`)"),
    // Trust (TINV step 10.0, 2026-10-07): the inferred type-invariant pre-pass
    // (candidates, census role, Houdini mint). Replaces the untracked
    // `TRUST_TINV=1` env read (decision TINV-10), which was acceptable only while
    // nothing could consume the result. Tracked: the certificates it mints are
    // the premise of the step-10 use-site lane.
    trust_tinv: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "run the inferred type-invariant (TINV) pre-pass: synthesize candidate invariants of \
         eligible private structs and certify them by a whole-crate Houdini induction \
         (docs/design/2026-10-04-type-invariant-tinv.md); the certified conjuncts become \
         use-site premises, and a row proved with one is graded `TypeInvariantComposed`, \
         conditional on the certificate (never kernel-`Certified`) and disclosed as \
         `assumes type_invariant(S)#k`"),
    trust_no_r1: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "disable kernel-certified whole-program R1 caller-propagation strengthening"),
    // Trust: changes the Bool/Unit spelling of declined Option lanes during active Trust-IR
    // lowering, so both incremental reuse and the crate hash must track it. Like
    // trust_ir_flip, it has no effect when verification and direct lowering are off.
    trust_option_flag_lanes: bool = (true, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "represent opaque Option lanes by their discriminant during Trust-IR lowering \
         (default: yes)"),
    // Trust (DC-18a): the check a store needs before it shares a unit across checkouts.
    // It refuses and never rewrites, so a compile it passes writes exactly the bytes the
    // same compile writes without it: TRACKED_NO_CRATE_HASH keeps the crate hash out of
    // it, while incremental reuse is still invalidated, so metadata an earlier session
    // encoded without the check is never copied into a session that has it.
    // EvidenceControl: its whole effect is an observable refusal.
    trust_path_free: bool = (false, parse_bool, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "refuse to write crate metadata that would carry an absolute host path no \
         --remap-path-prefix rule rewrote off this host: a path in an environment value an \
         `env!`, an `option_env!` or a tracked read took, a source-file name or the working \
         directory it was resolved against, a native library's name, or any value written \
         into the metadata under this session's working directory, remap sources, sysroot, \
         output, temporary or incremental directory, or home directory. The compile ends \
         with one error whose note is a `trust-path-free-v1` JSON record naming the path and \
         where it came from, and leaves no rlib or rmeta (`-Csave-temps` included). Nothing \
         is rewritten; a unit that needs its real path is compiled without this option \
         (default: no)"),
    // Trust (platform protocols: design 2026-10-01 Part 3 §3.2, plan L1a = design PR 8).
    // The five controls of the platform-protocol pass. THIS TRUSTC DOES NOT RUN THAT PASS
    // YET (plan L1d wires it): every value below is parsed, validated and tracked, and
    // changes no diagnostic and no emitted byte. Nothing prints a coverage claim for them
    // either; aterm's gate refuses a member whose policy produced no platform summary row
    // (E6, `PLATFORM DID NOT RUN`), which is what keeps an inert flag from passing as a
    // check.
    //
    // FC-7: an unknown spelling is a hard error in every one of them, and a property this
    // trustc cannot check (`lock-release`, `fd-identity`, until plan L4c) is refused rather
    // than accepted inertly.
    //
    // EvidenceControl: each one changes which platform verdicts a compilation can produce.
    // TRACKED_NO_CRATE_HASH, the spawn-census precedent (`-Ztrust-spawn-census-shadow`,
    // `-Ztrust-send-census`): the pass adds diagnostics and changes no emitted byte, so a
    // change invalidates incremental reuse and leaves the crate hash alone.
    trust_platform_properties: TrustPlatformProperties = (TrustPlatformProperties::default(),
        parse_trust_platform_properties, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "the platform protocol properties to check, as a comma-separated list (repeating the \
         option adds to the set): `fd-inherit` (no descriptor other than 0, 1 and 2 reaches a \
         spawned child's image). Refutation-only: a property can fail the build and never proves \
         anything; it applies only with verification on. Not yet checked by this trustc: the \
         pass is not wired, so the policy is validated and nothing is analysed \
         (default: none)"),
    trust_platform_unanalysed: TrustPlatformUnanalysed = (TrustPlatformUnanalysed::Warn,
        parse_trust_platform_unanalysed, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "how the platform pass reports a policy site it cannot analyse: `warn` (the default) \
         names it in a warning, `deny` makes it an error"),
    trust_platform_budget: usize = (1_000_000, parse_trust_platform_budget, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "the platform pass's exploration budget per derived model, counted in states and never \
         in time; a model that exceeds it leaves its sites unanalysed (`PC-BUDGET`), never \
         not refuted (default: 1000000)"),
    trust_platform_report: TrustPlatformReport = (TrustPlatformReport::Summary,
        parse_trust_platform_report, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "how much the platform pass prints: `summary` (the default) is every refutation, every \
         unanalysed site and the crate summary note; `verbose` adds a note per site that is not \
         refuted, with its premises"),
    trust_platform_dump_facts: Option<PathBuf> = (None, parse_trust_nonempty_path,
        [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "TEST AND MEASUREMENT ONLY: write the host facts the platform pass gives the census \
         (effects, drops, bodies, refused and foreign callees, closures) to this file, in the \
         census sidecar grammar (default: none)"),
    // Trust: policy is a single domain because the three settings are mutually
    // exclusive answers to one question. Encoded as separate booleans they were
    // an enum with an invalid state, which only a hand-written cross-check
    // downstream could reject.
    //
    // [TRACKED], the stronger of the two markers the booleans carried: crate
    // hashing is a superset of dep tracking, so the merged option cannot lose
    // an invalidation either of them used to force. It can rotate a crate hash
    // a memory-safe run previously kept stable, which is the correct direction
    // for an option that changes which verdicts a build accepts.
    trust_policy: TrustPolicy = (TrustPolicy::default(), parse_trust_policy, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "set how an active verification run enforces its verdicts: `strict` (the default) fails \
         the build on a refutation and on any unproved obligation that has NO runtime fallback, \
         while reporting — not failing on — a completeness gap whose operation rustc still checks \
         at runtime (bit-for-bit vanilla semantics; see the completeness-gap ruling), `certify` \
         demands FULL static discharge and fails on every unproved obligation including those \
         (the release gate, `targo trust certify`), `advisory` verifies and reports every \
         obligation non-fatally (selected by `targo trust --allow-l0-gaps`), `memory-safe` \
         records reachable Rust panic refutations and supported capability gaps as explicit \
         assumptions in functions with no source or inlined `unsafe` while UB, hardened, \
         contract, functional, and unmarked failures stay strict"),
    trust_audited_proc_macro: Vec<String> = (Vec::<String>::new(), parse_string_push, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "one audited proc-macro dylib path that -Ztrust-proc-macro-boundary admits (repeatable); \
         requires -Ztrust-proc-macro-boundary. Targo passes one per audited provider it resolved"),
    trust_proc_macro_boundary: bool = (false, parse_bool, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "Targo's per-unit in-process proc-macro boundary (PM-1): rustc's crate loader refuses, \
         before loading it, every proc-macro crate whose dylib no -Ztrust-audited-proc-macro \
         names (an advisory-policy session reports it and forfeits instead); requires \
         -Ztrust-verify-session and verification"),
    trust_proc_macro_isolation: bool = (false, parse_bool, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "expand every proc macro loaded from a proc-macro crate in a sandboxed worker process \
         (D21; the compiler's own `proc_macro::quote!` still expands in rustc): the worker is \
         the only process that loads a proc-macro dylib, shares no stdout or stderr with rustc, \
         holds no descriptor but its protocol socket and the null device, and runs under a \
         deny-default policy that denies file writes outside its private temporary directory \
         and the null device. Refused on a host without that sandbox (today every host but \
         macOS); where macOS cannot install the sandbox, each expansion fails; never falls \
         back to in-process expansion"),
    trust_proof_artifact_root: Option<PathBuf> = (None, parse_trust_nonempty_path, [UNTRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "write externalized proof materializations beneath this explicit private root; without it proof bytes remain inline and rustc never writes an ambient working-directory store"),
    trust_clean_origin_mutate_emitter: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "TEST-ONLY (#65/C3): perturb the Clean-origin emitted body post-plan so the \
         faithfulness gate's fatal refusal is exercisable end-to-end from a ui fixture; \
         mutates side A (the emission) only, never the recognizer/admitters/extractor, \
         and can only make a build FAIL that would have passed — never the reverse"),
    // Trust (2026-09-17): the finalization ROUTING probe; see
    // `trust_thir_lower::finalization_probe`.
    trust_ir_lower_mutate_finalization: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "TEST-ONLY: hand the crate finalizer the refusals of a SEPARATE one-declaration \
         Trust-IR module the validator rejects by construction (a `CallingConv::Rust` \
         declaration spelled `params: [] + is_vararg: true`), so the advisory-warning / \
         fail-closed-error routing of an invalid module is exercisable from a ui fixture \
         without riding a live producer gap; the crate's own module is untouched, and the \
         knob can only make a build FAIL that would have passed — never the reverse"),
    // Trust (2026-10-01): the effect-conservation gate's MUTATION probe; see
    // `trust_thir_lower::effect_conservation` and `LowerCx::lower_for_effects`.
    trust_ir_lower_mutate_rhs_effects: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "TEST-ONLY: disable the direct producer's field-store right-hand-side effect lowering \
         (`lower_for_effects` claims success without lowering, the lane as it was before \
         ec8b51bb3b), so that the effect-conservation gate's refusal of a body that lost a call \
         is exercisable from a fixture; the knob can only make a build FAIL that would have \
         passed — never the reverse"),
    // Trust (step 2 increment 6, step 6.5.1; INC6.5-SWITCH in docs/DECISION_QUEUE.md): the
    // level-S template lane; see `trust_thir_lower::template_lowering`. TRACKED for the reason
    // the other controls are: it changes what rmeta's trust-ir header records for a generic
    // definition, so a session with it on must not share an artifact or incremental identity
    // with one without it.
    trust_ir_lower_templates: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        // Trust (PKG-C2d2 slice 1): corrected — the authenticated rows are written since 6.5.4.
        "TEST-ONLY (step 6.5): run the level-S template lowering and write its authenticated \
         rows (since 6.5.4); no consumer admits a level-S row, and the only reader is the \
         diagnostic template-instance TEST-ORACLE; `no` can only make rmeta carry fewer entries, \
         never more"),
    // Trust (R8-SEAM, docs/DECISION_QUEUE.md): the crate-seam differential's CROSS-CHECK hook;
    // see `trust_thir_lower::crate_module::seam_reference`. A tracked option rather than the
    // environment variable it first landed as: env vars are banned ambient inputs (see
    // LEGACY_TRUST_SEMANTIC_ENV_VARS), and a hooked compile can fail finalization where an
    // unhooked one would not, so the two must not share an artifact or incremental identity.
    // Trust: D17-SEAM-1 is a default-off diagnostic oracle, never production input.
    trust_ir_instance_seam_test: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "TEST-ONLY: compare each locally appended generic instance's actual source-produced \
         trust-ir against independently retained built MIR at its concrete args; requires \
         verification off, explicit trust-cg backend with object/link output, and the trust-ir \
         frontend; mismatch or unsupported refuses"),
    trust_test_instance_seam_mutation: Option<String> = (None, parse_opt_string, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "TEST-ONLY negative control for trust-ir-instance-seam-test: bool-constant or \
         undef-constant; mutates only the oracle's private copy and must refuse"),
    // Trust (PKG-C2d2 slice 1; INC6.5-NO-AUTHORITY in docs/DECISION_QUEUE.md): the
    // template-instance equivalence TEST-ORACLE (`trust_thir_lower`'s `template_metadata::oracle`).
    // Default off and fenced by the driver to the D17 seam-test lane it chains to; TRACKED like
    // that lane, since a session with it on can fail where one without it would not.
    trust_ir_template_instance_oracle: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "TEST-ORACLE ONLY: compare each D17 local generic instance whose MIR seam oracle agreed \
         with its construction from this crate's own level-S template; no output, admission or \
         proof authority"),
    trust_test_template_oracle_mutation: Option<String> = (None, parse_opt_string, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "TEST-ONLY negative control for trust-ir-template-instance-oracle: int-constant or \
         envelope-byte; mutates only the oracle's private copy and must fail the session"),
    trust_ir_seam_reference: Option<PathBuf> = (None, parse_trust_nonempty_path, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "TEST-ONLY (R8-SEAM): beside the crate-seam differential, also run the pre-R8-SEAM seam \
         over the pre-R8-SEAM differential (kept verbatim), compare every seam verdict and every \
         row-1 UC probe outcome, write the comparison's report to this path, and fail crate \
         finalization on any difference; the knob can only make a build FAIL that would have \
         passed — never the reverse"),
    trust_targo_test_monitor: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "reserved internal Targo per-unit session-consistency selector (direct use is rejected): \
         install kernel-certified test monitors; requires a matching -Ztrust-verify-session, \
         does not authenticate a direct rustc caller, and never enables static verification"),
    // Trust (2026-09-30): the F3 storage rule's mutation control; see
    // `trust_thir_lower::to_mir::mutate_derived_assert_msg_for_test`. TRACKED for the reason
    // the other controls are: a knob that changes a verdict must change the crate hash.
    trust_test_mutate_derived_assert_msg: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "TEST-ONLY: in the derived MIR the Trust-IR differential builds, repoint one overflow-assert \
         message operand to a same-typed local its block has already retired (`StorageDead`), so \
         the storage rule `compare_derived` applies to the real derived body is exercisable from a \
         test; requires -Ztrust-verify=off -Ztrust-ir-lower -Ztrust-ir-flip=no and refuses every \
         -Ztrust-dump sink (with the flip on it would be inert, so that is refused too), so the \
         mutated body feeds only the differential's report and can never be installed or compiled"),
    // Trust: plain dependency data. This neither enables nor grades verification.
    trust_tool_inputs: bool = (false, parse_bool, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "record bounded local native tool inputs in dep-info after successful compilation (no proof or execution claim)"),
    trust_verify: TrustVerify = (TrustVerify::default(), parse_trust_verify, [TRACKED]
        { TRUST_AUTHORITY: AuthorityOnly },
        "run the batteries-on Trust typed verification pipeline (`on`, the default) or compile as \
         vanilla Rust (`off`); this is the sole verification activation control, used by the \
         vanilla-comparison and bootstrap compiler lanes"),
    trust_verify_crate_role: String = ("unscoped".to_string(), parse_trust_verify_crate_role, [TRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "reserved Targo reporting metadata: record this compiler unit's role (`unscoped`, \
         `primary`, `dependency`, or `build-script`); every non-`unscoped` role requires both \
         `-Ztrust-verify-package-name` and `-Ztrust-verify-session`; this value never changes \
         verifier scope (use the explicit `-Ztrust-verify=off` switch)"),
    // Trust (determinism plan §3.2a, 2026-10-08): the ONE solver-effort count's
    // scale `k`: every ay query is bounded by `min(100000, max(1, k · size))`
    // SAT conflicts per SAT solve, `size` its count of distinct terms, sent as
    // `(set-option :rlimit N)` before each check-sat, the same N on every host
    // at every load. TRACKED because it decides where a search stops (where
    // the count, and not one of ay's residual clocks, ends it). No per-function
    // count stands beside it. The default mirrors
    // `trust_types::determinism::EffortScale::BUILTIN` (rustc_session cannot
    // name that crate); `targo trust` passes the workspace root's
    // `[trust] effort` explicitly.
    trust_verify_effort: u64 = (384, parse_trust_verify_effort, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "set the solver effort scale: each ay query is bounded by min(100000, max(1, k * size)) SAT conflicts per SAT solve (ay `:rlimit`), size being its count of distinct terms; the one deterministic solver count, 1 through 100000"),
    // Trust (determinism plan §3.2/§3.6): the step budget stands in front of
    // this clock for preprocessing and the one effort count for each ay query.
    // The native CHC/PDR engine, kernel certification and the structural
    // promotions have no count yet (plan P4a), so for them this deadline is
    // still the bound, and its value does not move until they do (review rule
    // 2026-09-30: no clock becomes a backstop until a count stands in front of
    // all the work it bounds). `targo trust` derives it from `[trust]
    // backstop`. A function this clock stops is recorded with stop cause
    // `wall-backstop`.
    trust_verify_function_budget_ms: u64 = (120_000, parse_number, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "set the cooperative per-function verification wall-clock budget in milliseconds; no new proof work starts and late proof results are rejected after expiry, recorded as stop cause `wall-backstop`; the step budget and the effort count stand in front of it, and it still bounds the work with no count (0 disables the budget)"),
    trust_verify_function_budget_steps: u64 = (64_000_000, parse_trust_verify_function_budget_steps, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "set the positive DEADLINE-INDEPENDENT per-function preprocessing step budget: every instrumented pre-dispatch loop iteration decrements it, and reaching zero fails the function closed (never Proved). Unlike the wall-clock backstop this is a provable monotone-decreasing bound that guarantees termination even with the clock disabled, and a stop on it is reproducible; it cannot be disabled"),
    trust_verify_include_dependencies: bool = (false, parse_bool, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "include authenticated dependency-crate MIR in the Trust verification scope"),
    trust_verify_level: usize = (2, parse_trust_verify_level, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "set the Trust verification proof level (0 = safety, 1 = functional, 2 = domain)"),
    trust_verify_output: String = ("human".to_string(), parse_trust_verify_output, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: VerificationSelector },
        "set Trust verification output mode (`human`, `json`, or `both`)"),
    trust_verify_package_name: Option<String> = (None, parse_trust_verify_package_name, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "reserved Targo metadata: set the non-empty Cargo package identity recorded in structured \
         verifier transport; requires `-Ztrust-verify-session` and is required by every non-`unscoped` role"),
    // The sole carrier of hardened boundary obligations. A profile is a project
    // property, so it names the obligation set instead of a second boolean that
    // could disagree with it: with two carriers the compiler default and the
    // `targo trust` default were free to diverge, and they had.
    trust_verify_profile: Option<String> = (None, parse_trust_verify_profile, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "set the Trust verification profile that selects proof obligations; the registered \
         hardened profiles (`hardened`, `unix_hardened`, `coreutils_hardened`) additionally emit \
         fail-closed hardened boundary verification conditions; `unix_hardened` and \
         `coreutils_hardened` also DECLARE the Unix process-signal policy (`main` installs \
         SIGPIPE -> SIG_DFL, as `-Zon-broken-pipe=kill`; an explicit `-Zon-broken-pipe` wins), \
         which discharges their `process_semantics` stdout mandate"),
    trust_verify_session: Option<String> = (None, parse_trust_verify_session, [TRACKED_NO_CRATE_HASH]
        { TRUST_AUTHORITY: EvidenceControl },
        "set a non-empty proof-build freshness identity that invalidates incremental reuse without \
         changing the downstream crate hash; Targo pairs it with package metadata for non-`unscoped` \
         roles, while a raw `unscoped` compile may use a session-only nonce"),
    // Trust: launch-only resource correlation, supplied by the resolved Cargo unit.
    trust_admission_run_digest: Option<String> = (None, parse_trust_admission_digest, [UNTRACKED]
        { TRUST_AUTHORITY: EvidenceControl }, "reserved native admission public run digest"),
    trust_admission_unit_digest: Option<String> = (None, parse_trust_admission_digest, [UNTRACKED]
        { TRUST_AUTHORITY: EvidenceControl }, "reserved native admission exact Cargo unit digest"),
    trust_admission_semantics_digest: Option<String> = (None, parse_trust_admission_digest, [UNTRACKED]
        { TRUST_AUTHORITY: EvidenceControl }, "reserved native admission Cargo semantics digest"),
    trust_admission_unit_role: Option<String> = (None, parse_trust_admission_role, [UNTRACKED]
        { TRUST_AUTHORITY: EvidenceControl }, "reserved native admission exact Cargo graph role"),
    trust_admission_compile_target: Option<String> = (None, parse_trust_admission_target, [UNTRACKED]
        { TRUST_AUTHORITY: EvidenceControl }, "reserved native admission exact Cargo compile target"),
    trust_verify_target_spec_sha256: Option<String> = (None, parse_trust_verify_target_spec_sha256, [UNTRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "bind a session-scoped custom JSON target to the exact SHA-256 bytes parsed by rustc; reserved for Targo"),
    // Trust: 2026-09-21 — RAISED 5_000 -> 20_000, and the reason is a measurement,
    // not a preference. The native typed-CHC lane derives its hard wall-clock
    // watchdog as `timeout + 2s`, so 5_000 gave a 7s ceiling. A 64-bit `decreases`
    // ranking VC (`while i < n invariant i <= n decreases n - i`) costs a MEASURED
    // 3.3s of PDR on an idle machine — 47% of that ceiling — so the margin was
    // consumed by ordinary parallel load and the row reported UNKNOWN.
    //
    // MEASURED, and this is the decisive pair: `tests/ui/trust/
    // native_loop_collection_semantics.rs#slice_progress` PASSES when run alone
    // (`2 passed; 0 failed`) and FAILS inside the full `tests/ui/trust` suite,
    // which compiletest runs in parallel. Same compiler, same source, same
    // obligation; only the machine load differs. A budget whose verdict depends on
    // what else is running is not a budget, it is a race — and it fails in the
    // direction that turns a provable obligation into a coverage gap.
    //
    // 20s is 6x the idle cost, chosen so the verdict survives the load a full
    // suite or a busy workstation produces. It is a WALL-CLOCK backstop for phases
    // that ignore ay's internal budget (the 23h orca-core hang this watchdog was
    // built for); raising it costs time only on obligations that were going to
    // fail anyway, and buys back rows that were always provable.
    //
    // `crates/trust-router/.../engines/native_trust_mc.rs`'s
    // `DEFAULT_PER_OBLIGATION_TIMEOUT_MS` mirrors this value for session-less
    // callers and MUST be kept in sync; it is updated in the same commit.
    //
    // Trust (determinism plan §3.2a, 2026-09-30): on the ay lanes a COUNT,
    // `trust_verify_effort`, usually ends an undecided ay search first, at the
    // same point on every host (at most 100,000 conflicts per SAT solve, about
    // 1.6 s idle). Not always: a check-sat can run several SAT solves, and ay's
    // residual clocks spend time no count reaches. The trust-mc CHC/PDR
    // lane has no count of its own yet (plan P4a), so there this clock is
    // still the bound; its value therefore does not move (review rule
    // 2026-09-30: no clock becomes a backstop until a count stands in front of
    // all the work it bounds). `targo trust` passes the value its budget
    // profile's backstop derives (`trust_types::determinism::Backstop::
    // vc_clock_ms`, 5,000 ms at the built-in) explicitly; this default serves
    // a bare `trustc`. A solve this clock ends
    // is recorded with stop cause `wall-backstop`, and the unit that carries it
    // is not reproducible.
    trust_verify_timeout_ms: u64 = (20_000, parse_trust_verify_timeout_ms, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "set the positive per-obligation wall-clock timeout in milliseconds: a backstop behind `-Ztrust-verify-effort` on the ay lanes, and still the bound of the native CHC/PDR engine, which has no count yet"),
    trust_verify_worker_threads: usize = (0, parse_trust_verify_worker_threads, [TRACKED]
        { TRUST_AUTHORITY: VerificationSelector },
        "cap verifier worker threads (1 = serial dispatch; 0, the default, = no cap: engine batches run in parallel; maximum 256)"),
    // Trust (typeck-moonshot P1): the warm-replay witness lane. [UNTRACKED] (like
    // `incremental`), so the crate hash is unperturbed and no-flag lanes are
    // byte-identical to upstream.
    trust_witness: TrustWitness = (TrustWitness::default(), parse_trust_witness, [UNTRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "select the typeck-witness lane: `auto` (the default) mints and replays through \
         a `<StableCrateId>.twit` file in the `--out-dir`, router-gated to bodies where replay \
         beats fresh typeck and inert without an `--out-dir`; `off` disables it; `mint:<dir>` \
         mints every eligible root into an explicit store without replaying; `replay:<dir>` \
         replays every stored root from an explicit store without minting"),
    // Shadow-mint measurement for the PRECISE per-referenced-def key (A1-A3 edit-loop
    // key). Deliberately NOT part of the `trust_witness` lane domain: it selects the
    // witness KEY, not which lane runs, and its own disposition
    // (docs/design/2026-07-23-a1a3-edit-loop-key-disposition.md) requires it to stay
    // an opt-in shadow-mint measurement until the A1-A3 negative-context recorder
    // lands. Mint+replay switch to the precise key (hits without the whole-crate
    // SVH), but a replayed candidate is byte-diffed against real typeck and NEVER
    // trusted — real typeck's result is always returned. Folding it into the lane
    // domain would either delete that parity harness or imply the key is shippable.
    trust_witness_precise: bool = (false, parse_bool, [UNTRACKED]
        { TRUST_AUTHORITY: EvidenceControl },
        "EXPERIMENTAL: shadow-mint parity measurement of the precise edit-loop witness key (never trusted)"),
    tune_cpu: Option<String> = (None, parse_opt_string, [TRACKED],
        "select processor to schedule for (`rustc --print target-cpus` for details)"),
    #[rustc_lint_opt_deny_field_access("use `Session::ub_checks` instead of this field")]
    ub_checks: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "emit runtime checks for Undefined Behavior (default: -Cdebug-assertions)"),
    ui_testing: bool = (false, parse_bool, [UNTRACKED],
        "emit compiler diagnostics in a form suitable for UI testing (default: no)"),
    uninit_const_chunk_threshold: usize = (16, parse_number, [TRACKED],
        "allow generating const initializers with mixed init/uninit chunks, \
        and set the maximum number of chunks for which this is allowed (default: 16)"),
    unleash_the_miri_inside_of_you: bool = (false, parse_bool, [TRACKED],
        "take the brakes off const evaluation. NOTE: this is unsound (default: no)"),
    unpretty: Option<String> = (None, parse_unpretty, [UNTRACKED],
        "present the input source, unstable (and less-pretty) variants;
        `normal`,
        `expanded`, `expanded,identified`,
        `expanded,hygiene` (with internal representations),
        `ast-tree` (raw AST before expansion),
        `ast-tree,expanded` (raw AST after expansion),
        `hir` (the HIR), `hir,identified`,
        `hir,typed` (HIR with types for each node),
        `hir-tree` (dump the raw HIR),
        `thir-tree`, `thir-flat`,
        `mir` (the MIR), or `mir-cfg` (graphviz formatted MIR)"),
    unsound_mir_opts: bool = (false, parse_bool, [TRACKED],
        "enable unsound and buggy MIR optimizations (default: no)"),
    /// This name is kind of confusing: Most unstable options enable something themselves, while
    /// this just allows "normal" options to be feature-gated.
    ///
    /// The main check for `-Zunstable-options` takes place separately from the
    /// usual parsing of `-Z` options (see [`crate::config::nightly_options`]),
    /// so this boolean value is mostly used for enabling unstable _values_ of
    /// stable options. That separate check doesn't handle boolean values, so
    /// to avoid an inconsistent state we also forbid them here.
    // Trust: this also enables internal lint registration. A change must invalidate
    // incremental lint queries, while diagnostics alone do not change the crate hash.
    #[rustc_lint_opt_deny_field_access("use `Session::unstable_options` instead of this field")]
    unstable_options: bool = (false, parse_no_value, [TRACKED_NO_CRATE_HASH],
        "adds unstable command line options to rustc interface (default: no)"),
    use_ctors_section: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "use legacy .ctors section for initializers rather than .init_array"),
    use_sync_unwind: Option<bool> = (None, parse_opt_bool, [TRACKED],
        "Generate sync unwind tables instead of async unwind tables (default: no)"),
    validate_mir: bool = (false, parse_bool, [UNTRACKED],
        "validate MIR after each transformation"),
    verbose_asm: bool = (false, parse_bool, [TRACKED],
        "add descriptive comments from LLVM to the assembly (may change behavior) (default: no)"),
    #[rustc_lint_opt_deny_field_access("use `Session::verbose_internals` instead of this field")]
    verbose_internals: bool = (false, parse_bool, [TRACKED_NO_CRATE_HASH],
        "in general, enable more debug printouts (default: no)"),
    #[rustc_lint_opt_deny_field_access("use `Session::verify_llvm_ir` instead of this field")]
    verify_llvm_ir: bool = (false, parse_bool, [TRACKED],
        "verify LLVM IR (default: no)"),
    virtual_function_elimination: bool = (false, parse_bool, [TRACKED],
        "enables dead virtual function elimination optimization. \
        Requires `-Clto[=[fat,yes]]`"),
    wasi_exec_model: Option<WasiExecModel> = (None, parse_wasi_exec_model, [TRACKED],
        "whether to build a wasi command or reactor"),
    // This option only still exists to provide a more gradual transition path for people who need
    // the spec-complaint C ABI to be used.
    // FIXME remove this after a couple releases
    wasm_c_abi: () = ((), parse_wasm_c_abi, [TRACKED],
        "use spec-compliant C ABI for `wasm32-unknown-unknown` (deprecated, always enabled)"),
    wasm_proc_macros: bool = (false, parse_bool, [TRACKED],
        "enable support for compiling and loading wasm proc macros"),
    write_long_types_to_disk: bool = (true, parse_bool, [UNTRACKED],
        "whether long type names should be written to files instead of being printed in errors"),
    // tidy-alphabetical-end

    // If you add a new option, please update:
    // - compiler/rustc_interface/src/tests.rs
    // - src/doc/unstable-book/src/compiler-flags
}

#[cfg(test)]
#[path = "options/tests.rs"]
mod trust_option_tests;
