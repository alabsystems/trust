use std::any::{Any, TypeId, type_name};
// Trust: retain the original raw compiler-parent PATH for tool-input data.
use std::ffi::OsString;
use std::ops::{Deref, DerefMut};
use std::path::Component::Prefix;
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::atomic::{AtomicBool, AtomicUsize};
use std::sync::{Arc, Mutex};
use std::{env, io};

use rustc_data_structures::flock;
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexSet};
use rustc_data_structures::profiling::{SelfProfiler, SelfProfilerRef};
use rustc_data_structures::sync::{AppendOnlyVec, DynSend, DynSync, IntoDynSyncSend, Lock};
use rustc_errors::annotate_snippet_emitter_writer::AnnotateSnippetEmitter;
use rustc_errors::codes::*;
use rustc_errors::emitter::{DynEmitter, HumanReadableErrorType, OutputTheme, stderr_destination};
use rustc_errors::json::JsonEmitter;
use rustc_errors::timings::TimingSectionHandler;
use rustc_errors::{
    Diag, DiagCtxt, DiagCtxtHandle, DiagMessage, Diagnostic, ErrorGuaranteed, PResult, TerminalUrl,
};
use rustc_feature::UnstableFeatures;
use rustc_macros::StableHash;
pub use rustc_span::def_id::StableCrateId;
use rustc_span::edition::Edition;
use rustc_span::source_map::{FilePathMapping, SourceMap};
use rustc_span::{RealFileName, Span, Symbol};
use rustc_structures::{CrateType, Limit, LintName};
use rustc_target::asm::InlineAsmArch;
use rustc_target::spec::{
    Arch, CfgAbi, CodeModel, DebuginfoKind, MergeFunctions, Os, PanicStrategy, RelocModel,
    RelroLevel, SanitizerSet, SmallDataThresholdSupport, SplitDebuginfo, StackProtector,
    SymbolVisibility, Target, TargetTuple, TlsModel, apple,
};

use crate::code_stats::CodeStats;
pub use crate::code_stats::{DataTypeKind, FieldInfo, FieldKind, SizeKind, VariantInfo};
use crate::config::{
    self, BranchProtection, Cfg, CheckCfg, CoverageLevel, CoverageOptions, DebugInfo,
    ErrorOutputType, FunctionReturn, Input, InstrumentCoverage, InstrumentMcount, LtoCli,
    NATIVE_CPU, OptLevel, OutFileName, OutputType, PAuthKey, PointerAuthOption, SwitchWithOptPath,
    TrustIrLower, TrustPlatformProperties, TrustPolicy, TrustVerify,
};
use crate::filesearch::FileSearch;
use crate::lint::LintId;
use crate::parse::ParseSess;
use crate::search_paths::SearchPath;
use crate::{diagnostics, filesearch, lint};

/// The behavior of the CTFE engine when an error occurs with regards to backtraces.
#[derive(Clone, Copy)]
pub enum CtfeBacktrace {
    /// Do nothing special, return the error as usual without a backtrace.
    Disabled,
    /// Capture a backtrace at the point the error is created and return it in the error
    /// (to be printed later if/when the error ever actually gets shown to the user).
    Capture,
    /// Capture a backtrace at the point the error is created and immediately print it out.
    Immediate,
}

#[derive(Clone, Copy, Debug, StableHash)]
pub struct Limits {
    /// The maximum recursion limit for potentially infinitely recursive
    /// operations such as auto-dereference and monomorphization.
    pub recursion_limit: Limit,
    /// The size at which the `large_assignments` lint starts
    /// being emitted.
    pub move_size_limit: Limit,
    // Trust: rust-lang#100914 — the size at which the `large_stack_frame`
    // lint starts being emitted.
    pub stack_frame_limit: Limit,
    /// The maximum length of types during monomorphization.
    pub type_length_limit: Limit,
    /// The maximum pattern complexity allowed (internal only).
    pub pattern_complexity_limit: Limit,
}

pub struct CompilerIO {
    pub input: Input,
    pub output_dir: Option<PathBuf>,
    pub output_file: Option<OutFileName>,
    pub temps_dir: Option<PathBuf>,
}

pub trait DynLintStore: Any + DynSync + DynSend {
    /// Provides a way to access lint groups without depending on `rustc_lint`
    fn lint_groups_iter(&self) -> Box<dyn Iterator<Item = LintGroup> + '_>;
}

// Trust: one independently locked cell per compiler-extension state type. The
// outer Session map is held only long enough to clone the cell, so unrelated
// proof subsystems do not serialize behind cache I/O.
struct TrustCompilerStateCell<T>(Mutex<T>);

/// Hardware pointer-signing keys in ARM8.3.
/// These values are the same as used in ptrauth.h.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PointerAuthARM8_3Key {
    ASIA = 0,
    ASIB = 1,
    ASDA = 2,
    ASDB = 3,
}

/// Forms of extra discrimination.
pub enum PointerAuthDiscrimination {
    /// No additional discrimination.
    None,
    /// Include a hash of the entity's type.
    Type,
    /// Include a hash of the entity's identity.
    Decl,
    /// Discriminate using a constant value.
    Constant,
}

/// Types of address discrimination.
pub enum PointerAuthAddressDiscriminator {
    /// Enable/disable hardware address discrimination.
    HardwareAddress(bool),
    /// Use a synthetic value. For instance init/fini entries can not the address of the arrays,
    /// they must use a synthetic value of `1`.
    Synthetic(u64),
}

pub struct PointerAuthSchema {
    pub is_address_discriminated: PointerAuthAddressDiscriminator,
    pub discrimination_kind: PointerAuthDiscrimination,
    pub key: PointerAuthARM8_3Key,
    pub constant_discriminator: u16,
}
impl PointerAuthSchema {
    pub fn function_pointers_default(target: &Target) -> Self {
        assert!(target.cfg_abi == CfgAbi::Pauthtest);
        return Self {
            is_address_discriminated: PointerAuthAddressDiscriminator::HardwareAddress(false),
            discrimination_kind: PointerAuthDiscrimination::None,
            key: PointerAuthARM8_3Key::ASIA,
            constant_discriminator: 0,
        };
    }
    pub fn init_fini_default(target: &Target) -> Self {
        assert!(target.cfg_abi == CfgAbi::Pauthtest);
        return Self {
            is_address_discriminated: PointerAuthAddressDiscriminator::Synthetic(1),
            discrimination_kind: PointerAuthDiscrimination::None,
            key: PointerAuthARM8_3Key::ASIA,
            // ptrauth_string_discriminator("init_fini")
            constant_discriminator: 0xd9d4,
        };
    }
}

pub struct PointerAuthConfig {
    /// Should return addresses be authenticated?
    pub return_addresses: bool,
    /// Do authentication failures cause a trap?
    pub auth_traps: bool,
    /// Do indirect goto label addresses need to be authenticated?
    pub indirect_gotos: bool,
    /// Should ELF GOT entries be signed?
    pub elf_got: bool,
    /// Use hardened lowering for jump-table dispatch?
    pub aarch64_jump_table_hardening: bool,
    /// The ABI for C function pointers.
    pub function_pointers: Option<PointerAuthSchema>,
    /// The ABI for function addresses in .init_array and .fini_array
    pub init_fini: Option<PointerAuthSchema>,
    /// Use of pointer authentication intrinsics.
    pub intrinsics: bool,
    /// The following are used only for compatibility with C++ and control over generated abi
    /// version. They do not control Rust code generation.
    pub typeinfo_vt_ptr_discrimination: bool,
    pub vt_ptr_addr_discrimination: bool,
    pub vt_ptr_type_discrimination: bool,
}
impl PointerAuthConfig {
    fn default(target: &Target) -> Self {
        assert!(target.cfg_abi == CfgAbi::Pauthtest);
        return Self {
            return_addresses: true,
            auth_traps: true,
            indirect_gotos: true,
            elf_got: false,
            aarch64_jump_table_hardening: true,
            function_pointers: Some(PointerAuthSchema::function_pointers_default(target)),
            init_fini: Some(PointerAuthSchema::init_fini_default(target)),
            intrinsics: true,
            typeinfo_vt_ptr_discrimination: true,
            vt_ptr_addr_discrimination: true,
            vt_ptr_type_discrimination: true,
        };
    }
    pub fn calculate_pauth_abi_version(&self, target: &Target) -> u32 {
        assert!(target.cfg_abi == CfgAbi::Pauthtest);
        // Bit positions of version flags for AARCH64_PAUTH_PLATFORM_LLVM_LINUX.
        // NOTE: The enum values must stay in sync with clang, see:
        // <llvm_root>/llvm/include/llvm/BinaryFormat/ELF.h
        //
        // We do not expect to use C++ virtual dispatch, but enable these flags
        // for compatibility with C++ code. Intrinsics are also always enabled.
        //
        // Link to PAuth core info documentation:
        // <https://github.com/ARM-software/abi-aa/blob/2025Q4/pauthabielf64/pauthabielf64.rst#core-information>
        const INTRINSICS: u32 = 0;
        const CALLS: u32 = 1;
        const RETURNS: u32 = 2;
        const AUTHTRAPS: u32 = 3;
        const VT_PTR_ADDR_DISCR: u32 = 4;
        const VT_PTR_TYPE_DISCR: u32 = 5;
        const INIT_FINI: u32 = 6;
        const INIT_FINI_ADDR_DISC: u32 = 7;
        const GOT: u32 = 8;
        const GOTOS: u32 = 9;
        const TYPEINFO_VT_PTR_DISCR: u32 = 10;
        // FIXME(jchlanda) We don't yet support function pointer type discrimination.
        // const FPTR_TYPE_DISCR: u32 = 11;

        let pauth_abi_version: u32 = (u32::from(self.intrinsics) << INTRINSICS)
            | (u32::from(self.function_pointers.is_some()) << CALLS)
            | (u32::from(self.return_addresses) << RETURNS)
            | (u32::from(self.auth_traps) << AUTHTRAPS)
            | (u32::from(self.vt_ptr_addr_discrimination) << VT_PTR_ADDR_DISCR)
            | (u32::from(self.vt_ptr_type_discrimination) << VT_PTR_TYPE_DISCR)
            | (u32::from(self.init_fini.is_some()) << INIT_FINI)
            | (u32::from(self.init_fini.as_ref().is_some_and(|schema| {
                matches!(
                    schema.is_address_discriminated,
                    PointerAuthAddressDiscriminator::HardwareAddress(true)
                        | PointerAuthAddressDiscriminator::Synthetic(_)
                )
            })) << INIT_FINI_ADDR_DISC)
            | (u32::from(self.elf_got) << GOT)
            | (u32::from(self.indirect_gotos) << GOTOS)
            | (u32::from(self.typeinfo_vt_ptr_discrimination) << TYPEINFO_VT_PTR_DISCR);

        pauth_abi_version
    }
    pub fn from_raw(raw: &[(PointerAuthOption, bool)], target: &Target) -> Option<Self> {
        if target.cfg_abi != CfgAbi::Pauthtest {
            return None;
        }

        let mut cfg = Self::default(target);
        if raw.is_empty() {
            return Some(cfg);
        }

        for (opt, enabled) in raw {
            match opt {
                PointerAuthOption::Calls => {
                    if *enabled {
                        cfg.function_pointers.get_or_insert_with(|| {
                            PointerAuthSchema::function_pointers_default(target)
                        });
                    } else {
                        cfg.function_pointers = None;
                    }
                }
                PointerAuthOption::FunctionPointerTypeDiscrimination => {
                    if *enabled {
                        let schema = cfg.function_pointers.get_or_insert_with(|| {
                            PointerAuthSchema::function_pointers_default(target)
                        });
                        schema.discrimination_kind = PointerAuthDiscrimination::Type;
                    } else if let Some(schema) = &mut cfg.function_pointers {
                        schema.discrimination_kind = PointerAuthDiscrimination::None;
                    }
                }
                PointerAuthOption::ReturnAddresses => cfg.return_addresses = *enabled,
                PointerAuthOption::AuthTraps => cfg.auth_traps = *enabled,
                PointerAuthOption::IndirectGotos => cfg.indirect_gotos = *enabled,
                PointerAuthOption::ElfGot => cfg.elf_got = *enabled,
                PointerAuthOption::Aarch64JumpTableHardening => {
                    cfg.aarch64_jump_table_hardening = *enabled
                }
                PointerAuthOption::InitFini => {
                    if *enabled {
                        cfg.init_fini
                            .get_or_insert_with(|| PointerAuthSchema::init_fini_default(target));
                    } else {
                        cfg.init_fini = None;
                    }
                }
                PointerAuthOption::InitFiniAddressDiscrimination => {
                    if *enabled {
                        let schema = cfg
                            .init_fini
                            .get_or_insert_with(|| PointerAuthSchema::init_fini_default(target));
                        schema.is_address_discriminated =
                            PointerAuthAddressDiscriminator::HardwareAddress(true);
                    } else if let Some(schema) = &mut cfg.init_fini {
                        schema.is_address_discriminated =
                            PointerAuthAddressDiscriminator::Synthetic(1);
                    }
                }

                PointerAuthOption::Intrinsics => cfg.intrinsics = *enabled,
                PointerAuthOption::TypeInfoVTPtrDisc => {
                    cfg.typeinfo_vt_ptr_discrimination = *enabled
                }
                PointerAuthOption::VTPtrAddrDisc => cfg.vt_ptr_addr_discrimination = *enabled,
                PointerAuthOption::VTPtrTypeDisc => cfg.vt_ptr_type_discrimination = *enabled,
            }
        }

        Some(cfg)
    }
    pub fn fn_attrs(&self) -> Vec<&'static str> {
        // FIXME(jchlanda) This is not an exhaustive list of all `ptrauth`-related attributes, but only
        // those currently supported. The list is expected to grow as additional functionality is
        // implemented, particularly for C++ interoperability.
        let mut attrs = vec![];
        if self.aarch64_jump_table_hardening {
            attrs.push("aarch64-jump-table-hardening");
        }
        if self.auth_traps {
            attrs.push("ptrauth-auth-traps");
        }
        if self.function_pointers.is_some() {
            attrs.push("ptrauth-calls");
        }
        if self.indirect_gotos {
            attrs.push("ptrauth-indirect-gotos");
        }
        if self.return_addresses {
            attrs.push("ptrauth-returns");
        }

        attrs
    }
}

/// Partial session built before the full session. More specifically, `EarlySession` is used to
/// init the codegen backend, and then both pieces are used to build the full `Session`.
pub struct EarlySession {
    pub target: Target,
    pub host: Target,
    pub opts: config::Options,
    pub psess: ParseSess,
}

// JUSTIFICATION: defn of the suggested wrapper fns
#[allow(rustc::bad_opt_access)]
impl EarlySession {
    #[inline]
    pub fn dcx(&self) -> DiagCtxtHandle<'_> {
        self.psess.dcx()
    }

    #[inline]
    pub fn source_map(&self) -> &SourceMap {
        self.psess.source_map()
    }

    /// Note: this is simpler than `Session::lto`, hence the `early_` prefix (to more clearly
    /// distinguish it).
    pub fn early_lto(&self) -> LtoCli {
        self.opts.cg.lto
    }

    pub fn print_llvm_stats(&self) -> bool {
        self.opts.unstable_opts.print_codegen_stats
    }

    pub fn print_llvm_stats_json(&self) -> Option<&String> {
        self.opts.unstable_opts.print_codegen_stats_json.as_ref()
    }

    pub fn relocation_model(&self) -> RelocModel {
        self.opts.cg.relocation_model.unwrap_or(self.target.relocation_model)
    }

    pub fn code_model(&self) -> Option<CodeModel> {
        self.opts.cg.code_model.or(self.target.code_model)
    }

    pub fn tls_model(&self) -> TlsModel {
        self.opts.unstable_opts.tls_model.unwrap_or(self.target.tls_model)
    }

    /// Returns the panic strategy for this compile session. If the user explicitly selected one
    /// using '-C panic', use that, otherwise use the panic strategy defined by the target.
    pub fn panic_strategy(&self) -> PanicStrategy {
        self.opts.cg.panic.unwrap_or(self.target.panic_strategy)
    }

    /// Get the deployment target on Apple platforms based on the standard environment variables,
    /// or fall back to the minimum version supported by `rustc`.
    ///
    /// This should be guarded behind `if sess.target.is_like_darwin`.
    pub fn apple_deployment_target(&self) -> apple::OSVersion {
        let min = apple::OSVersion::minimum_deployment_target(&self.target);
        let env_var = apple::deployment_target_env_var(&self.target.os);

        // FIXME(madsmtm): Track changes to this.
        if let Ok(deployment_target) = env::var(env_var) {
            match apple::OSVersion::from_str(&deployment_target) {
                Ok(version) => {
                    let os_min = apple::OSVersion::os_minimum_deployment_target(&self.target.os);
                    // It is common that the deployment target is set a bit too low, for example on
                    // macOS Aarch64 to also target older x86_64. So we only want to warn when
                    // variable is lower than the minimum OS supported by rustc, not when the
                    // variable is lower than the minimum for a specific target.
                    if version < os_min {
                        self.dcx().emit_warn(diagnostics::AppleDeploymentTarget::TooLow {
                            env_var,
                            version: version.fmt_pretty().to_string(),
                            os_min: os_min.fmt_pretty().to_string(),
                        });
                    }

                    // Raise the deployment target to the minimum supported.
                    version.max(min)
                }
                Err(error) => {
                    self.dcx()
                        .emit_err(diagnostics::AppleDeploymentTarget::Invalid { env_var, error });
                    min
                }
            }
        } else {
            // If no deployment target variable is set, default to the minimum found above.
            min
        }
    }

    pub fn sanitizers(&self) -> SanitizerSet {
        self.opts
            .unstable_opts
            .sanitizer
            .combine_with_defaults(self.target.options.default_sanitizers)
    }

    pub fn merge_functions(&self) -> MergeFunctions {
        self.opts.unstable_opts.merge_functions.unwrap_or(self.target.merge_functions)
    }

    pub fn is_nightly_build(&self) -> bool {
        self.opts.unstable_features.is_nightly_build()
    }
}

/// Some info about the backend, returned by `CodegenBackend::init` and put into the `Session`.
#[derive(Default)]
pub struct CodegenBackendInit {
    /// See `Session::global_backend_features`.
    pub global_backend_features: Vec<String>,

    /// See `Session::replaced_intrinsics`.
    pub replaced_intrinsics: Vec<Symbol>,

    /// See `Session::fallback_intrinsics`.
    pub fallback_intrinsics: Vec<Symbol>,

    /// See `Session::thin_lto_supported`.
    pub thin_lto_supported: bool = true,
}

/// Represents the data associated with a compilation
/// session for a single crate.
pub struct Session {
    /// The `EarlySession` is embedded so it can be passed to functions that need it.
    /// `Session::deref{_,mut}` exist so the fields within can be accessed as if they were direct
    /// fields of `Session`.
    pub early_sess: EarlySession,
    pub wasm_proc_macro_tuple: TargetTuple,
    pub wasm_proc_macro_target: Target,
    pub target_tlib_path: SearchPath,
    pub unstable_features: UnstableFeatures,
    pub config: Cfg,
    pub check_config: CheckCfg,
    /// Spans passed to `proc_macro::quote_span`. Each span has a numerical
    /// identifier represented by its position in the vector.
    proc_macro_quoted_spans: AppendOnlyVec<Span>,

    /// Input, input file path and output file path to this compilation process.
    pub io: CompilerIO,

    /// Used by `-Z self-profile`.
    pub prof: SelfProfilerRef,

    /// Used to emit section timings events (enabled by `--json=timings`).
    pub timings: TimingSectionHandler,

    /// Data about code being compiled, gathered during compilation.
    pub code_stats: CodeStats,

    /// This only ever stores a `LintStore` but we don't want a dependency on that type here.
    pub lint_store: Option<Arc<dyn DynLintStore>>,

    /// Cap lint level specified by a driver specifically.
    pub driver_lint_caps: FxHashMap<lint::LintId, lint::Level>,

    /// Tracks the current behavior of the CTFE engine when an error occurs.
    /// Options range from returning the error without a backtrace to returning an error
    /// and immediately printing the backtrace to stderr.
    /// The `Lock` is only used by miri to allow setting `ctfe_backtrace` after analysis when
    /// `MIRI_BACKTRACE` is set. This makes it only apply to miri's errors and not to all CTFE
    /// errors.
    pub ctfe_backtrace: Lock<CtfeBacktrace>,

    /// This tracks where `-Zunleash-the-miri-inside-of-you` was used to get around a
    /// const check, optionally with the relevant feature gate. We use this to
    /// warn about unleashing, but with a single diagnostic instead of dozens that
    /// drown everything else in noise.
    miri_unleashed_features: Lock<Vec<(Span, Option<Symbol>)>>,

    /// Architecture to use for interpreting asm!.
    pub asm_arch: Option<InlineAsmArch>,

    /// Set of actually enabled features for the current target, including ones that are not
    /// in `cfg(target_feature)` because they are unstable or internal-only.
    /// This is used by the compiler itself when it needs to know which target features are actually
    /// going to be enabled in the backend (e.g. for knowing which registers inline asm can use).
    pub internal_target_features: FxIndexSet<Symbol>,

    /// The list of backend target features for this session. Not used by Rust itself because the
    /// concrete feature names can be backend-specific. This is computed from the target's base
    /// features, `-Ctarget-cpu`, `-Ctarget-feature`, and other flags that the current backend
    /// models as target features (but that are not considered target features in Rust).
    pub global_backend_features: Vec<String>,

    /// The version of the rustc process, possibly including a commit hash and description.
    pub cfg_version: &'static str,

    /// The inner atomic value is set to true when a feature marked as `internal` is
    /// enabled. Makes it so that "please report a bug" is hidden, as ICEs with
    /// internal features are wontfix, and they are usually the cause of the ICEs.
    /// None signifies that this is not tracked.
    pub using_internal_features: &'static AtomicBool,

    /// Environment variables accessed during the build and their values when they exist.
    pub env_depinfo: Lock<FxIndexSet<(Symbol, Option<Symbol>)>>,

    /// File paths accessed during the build.
    pub file_depinfo: Lock<FxIndexSet<Symbol>>,

    // Trust (DC-18a): under `-Ztrust-path-free` only, each host path a check found the
    // unit's metadata would carry, in the order found (`env!`/`option_env!` reads during
    // expansion, then `rustc_metadata`'s checks). `rustc_metadata` reports the first and
    // writes no metadata. Empty without the option.
    pub trust_path_free_refusals: Lock<Vec<rustc_span::trust_path_free::Refusal>>,
    // Trust (DC-18a): this session's host prefixes, built on first use under the option.
    trust_path_free_prefixes: std::sync::OnceLock<rustc_span::trust_path_free::HostPrefixes>,

    // Trust: only the opt-in producer can populate this invocation's collection.
    pub(crate) tool_input_collection: Lock<crate::tool_inputs::Collection>,
    // Trust: bind child observations to the original compiler parent context.
    pub(crate) tool_input_parent_path: Option<OsString>,

    target_filesearch: Arc<FileSearch>,
    host_filesearch: Arc<FileSearch>,
    wasm_proc_macro_filesearch: Option<Arc<FileSearch>>,

    /// A list of all intrinsics that the current codegen backend definitely replaces with its own
    /// implementations, which means their fallback bodies do not need to be monomorphized.
    pub replaced_intrinsics: FxHashSet<Symbol>,

    /// A list of all intrinsics that the current codegen backend definitely does *not* replace
    /// with its own implementations, which means their fallback bodies can be MIR-inlined.
    pub fallback_intrinsics: FxHashSet<Symbol>,

    /// Does the codegen backend support ThinLTO?
    pub thin_lto_supported: bool,

    /// Global per-session counter for MIR optimization pass applications.
    ///
    /// Used by `-Zmir-opt-bisect-limit` to assign an index to each
    /// optimization-pass execution candidate during this compilation.
    pub mir_opt_bisect_eval_count: AtomicUsize,

    /// Whether the test harness removed a user-written `#[rustc_main]` attribute
    /// while generating the synthetic test entry point.
    pub removed_rustc_main_attr: AtomicBool,

    // Trust: type-erased compiler-extension state owned by this invocation.
    // Proof/certificate data must not live in process-global OnceLocks: a
    // rustc_driver process may run sequential or concurrent Sessions, and
    // replaying the first crate's state in another crate can create a false
    // proof. Session ownership also releases large maps when compilation ends.
    trust_compiler_state: Lock<IntoDynSyncSend<FxHashMap<TypeId, Arc<dyn Any + Send + Sync>>>>,

    // Trust (temporal P3): the field bindings this crate's islands declare,
    // set once by the resolver, which elaborates the islands before analysis.
    // Read on a hot path (`trust_reads_pre_steal_mir`), so it is its own
    // field and not a `trust_compiler_state` entry.
    trust_field_bindings: std::sync::OnceLock<Vec<TrustFieldBinding>>,
    // Trust (temporal P3, sealed types): the seals the crate's `clean { }`
    // islands declare, set once by the resolver beside the bindings.
    trust_seals: std::sync::OnceLock<Vec<TrustSeal>>,
    /// Config specifying targets' pointer authentication preference.
    pub pointer_auth_config: Option<PointerAuthConfig>,

    /// Cached sanitizer set. Cached because it is accessed frequently.
    sanitizers: SanitizerSet,
}

impl Deref for Session {
    type Target = EarlySession;

    fn deref(&self) -> &EarlySession {
        &self.early_sess
    }
}

impl DerefMut for Session {
    fn deref_mut(&mut self) -> &mut EarlySession {
        &mut self.early_sess
    }
}

/// Trust (temporal P3, sealed types): a seal a `clean { }` island declares on
/// a type of the crate (a constant of kernel type `Trust.Protocol.Seal`), as
/// the resolver read it out of the kernel term. A field of a value of
/// `type_name` is changed only while one of `writers` runs; a value is built
/// only in `makers`, called only from `made_by`; no value owning one is put
/// over another, except by the fns of other crates in `trusts`. The compiler
/// checks every body of the crate against it and fails the build at `span`.
#[derive(Clone, Debug)]
pub struct TrustSeal {
    /// The seal constant's kernel name (`HarnessPolicy.cell`).
    pub name: String,
    /// The sealed type (`Generational`, `order::Generational`).
    pub type_name: String,
    /// The fns that may change a field of a value of it.
    pub writers: Vec<String>,
    /// The fns that may build a value of it.
    pub makers: Vec<String>,
    /// The fns that may call a maker.
    pub made_by: Vec<String>,
    /// The fns of other crates that may be handed a value holding one.
    pub trusts: Vec<String>,
    /// The seal's definition, in the island.
    pub span: Span,
}

/// Trust (temporal P3): a binding a `clean { }` island declares between a
/// model and the code beside it (a constant of kernel type
/// `Trust.Protocol.Binding`), as the resolver read it out of the kernel term.
/// The Rust field at `path` is written only from the arms for the message
/// variants in `arms`, except by the fns in `carried_by`. The thread census
/// checks every write it finds against it and fails the build at `span`.
#[derive(Clone, Debug)]
pub struct TrustFieldBinding {
    /// The binding constant's kernel name (`HarnessPolicy.policy`).
    pub name: String,
    /// The field path (`config.harness`).
    pub path: String,
    /// The message variants whose arms may write the field.
    pub arms: Vec<String>,
    /// The fns whose writes are declared carry-overs.
    pub carried_by: Vec<String>,
    /// The binding's definition, in the island.
    pub span: Span,
}

#[derive(Clone, Copy)]
pub enum CodegenUnits {
    /// Specified by the user. In this case we try fairly hard to produce the
    /// number of CGUs requested.
    User(usize),

    /// A default value, i.e. not specified by the user. In this case we take
    /// more liberties about CGU formation, e.g. avoid producing very small
    /// CGUs.
    Default(usize),
}

impl CodegenUnits {
    pub fn as_usize(self) -> usize {
        match self {
            CodegenUnits::User(n) => n,
            CodegenUnits::Default(n) => n,
        }
    }
}

pub struct LintGroup {
    pub name: LintName,
    pub lints: Vec<LintId>,
    pub is_externally_loaded: bool,
}

/// Trust: canonical batteries-on activation rule for compiler-integrated
/// verification. `-Ztrust-verify=off` is the only thing that changes
/// activation; `-Ztrust-policy` alters strictness, never activation. Kept pure
/// so option/cfg regression tests can pin both states without a full
/// [`Session`].
pub const fn trust_verification_enabled_by_flags(verify: TrustVerify) -> bool {
    verify.is_on()
}

/// Trust: is a proof CLAIM being made? Only then may a Trust finding FAIL the
/// build.
///
/// Two flags decide it and nothing else. `-Ztrust-verify=off` is the master
/// off-switch: nothing is verified, so nothing is claimed, whatever the policy
/// says. `-Ztrust-policy=advisory` runs verification for its report alone.
/// Everything the compiler would otherwise refuse over — an unproved
/// obligation, a crate module the Trust-IR validator rejects — is in those two
/// lanes a loss of COVERAGE that is reported, never enforced; the strict,
/// certify and memory-safe lanes under verification keep every hard error. There
/// are two deliberate exceptions, both explicit requests honoured whenever
/// verification runs, whatever the policy:
///
/// * `-Ztrust-ir-lower=strict`, a request that a lowering shortfall fail the
///   build ([`trust_ir_lower_strict_by_flags`]);
/// * `-Ztrust-platform-properties=…` (Trust: platform protocols, OD-1): a
///   platform refutation is an ERROR under advisory too
///   ([`trust_platform_errors_enabled_by_flags`]). It fails the build without a
///   proof claim because it is the opposite of one: refutation-only, a
///   replayed counterexample on `Trust.Platform` that never yields `Proved`
///   (OD-8). Advisory demotes what a proof run did not establish; it does not
///   demote a concrete violation the caller asked to be told about.
///
/// Kept pure beside [`trust_verification_enabled_by_flags`] so the rule is
/// pinned without a [`Session`].
pub const fn trust_proof_claimed_by_flags(verify: TrustVerify, policy: TrustPolicy) -> bool {
    trust_verification_enabled_by_flags(verify) && !policy.is_advisory()
}

/// Trust (D21): whether this host has the sandbox the isolated proc-macro worker
/// runs under. Today that is the macOS seatbelt policy and nothing else.
pub const TRUST_PROC_MACRO_ISOLATION_HOST: bool = cfg!(target_os = "macos");

/// Trust (D21): the refusal for `-Ztrust-proc-macro-isolation` on a host without
/// the sandbox. Isolation is containment the host must supply, so the option is
/// refused there rather than honoured by expanding in process: a lane that
/// admits only isolated expansion then keeps refusing proc macros on that host.
/// Kept pure so both hosts' answers are pinned from either.
pub const fn trust_proc_macro_isolation_refusal_by_flags(
    requested: bool,
    host_has_sandbox: bool,
) -> Option<&'static str> {
    if requested && !host_has_sandbox {
        Some(
            "-Ztrust-proc-macro-isolation is refused on this host: the isolated proc-macro \
             worker needs the macOS seatbelt sandbox, and expansion does not fall back to \
             this process",
        )
    } else {
        None
    }
}

/// Trust (platform protocols, plan L1a; OD-1, PD-4): may the platform-protocol
/// pass run and fail the build? Exactly when verification is on and at least
/// one property is requested. `-Ztrust-policy` is deliberately not an input: a
/// platform refutation is an error under every policy, advisory included (the
/// second exception [`trust_proof_claimed_by_flags`] documents), and under
/// `-Ztrust-verify=off` the pass never runs, so it can neither error nor print
/// (PD-4). Kept pure so the rule is pinned without a [`Session`].
pub fn trust_platform_errors_enabled_by_flags(
    verify: TrustVerify,
    properties: &TrustPlatformProperties,
) -> bool {
    trust_verification_enabled_by_flags(verify) && !properties.is_empty()
}

/// Trust: -O parity (ruling R1, 2026-09-25; work item T6, 2026-10-09) — the
/// `-Zmir-opt-level` a session runs ([`Session::mir_opt_level`]).
///
/// Upstream answers 1 at `-Copt-level=0` and 2 at every other opt-level. Every
/// unit of a Trust PROOF SESSION answers 1 at every opt-level: the MIR pipeline
/// `-O0` runs. A unit is in a proof session when it verifies (`verify`) or when
/// it carries a `-Ztrust-verify-session` (`proof_session`) — a
/// verification-off dependency of a proof run, whose encoded MIR a verified
/// dependent re-derives (Targo's foreign-bundle scope). Only a unit that is
/// neither — the vanilla lane: compiletest, bootstrap — keeps upstream's rule.
///
/// WHY. `TrustVerify` is the LAST pass of that pipeline and verifies what the
/// passes before it produced. At level 2 that is what the MIR inliner and GVN made
/// of the program, not what `-O0` verified: `slice::Iter::next` dissolves into
/// `RawPtr -> NonNull` casts and `PtrOffset` the verifier does not model, and a
/// sysroot `unsafe fn`'s call-site row is deleted together with its `Call`.
/// Measured 2026-09-25 (`0.10.0+gab7e41892`): the ordinary-Rust sweep verified
/// 73/80 at `-O0` and 43/80 at `-O`, and `for &v in a { n = n.max(v) }` alone was
/// refused at `-O`. With the cap the verified MIR is still exactly the compiled
/// MIR — nothing is verified on a clone — and the `-O` verdict IS the `-O0`
/// verdict by construction. This is the architecture of record
/// (`docs/design/2026-09-16-trust-core-architecture.md`: rustc's MIR optimization
/// passes are off Trust's chain).
///
/// The dependency channel (T6) is the same rule one hop out: a verified crate
/// re-derives the encoded MIR of a verification-off dependency in its session,
/// so a dependency compiled at level 2 handed its dependents inliner- and
/// GVN-shaped bodies, and a Cargo speed row on the dependency moved its
/// dependents' verdicts.
///
/// WHAT IS NOT CHANGED.
/// * `-Copt-level` itself: LLVM still optimizes a release build and inlines across
///   the calls the MIR inliner no longer touches.
/// * The vanilla lane (`-Ztrust-verify=off` with no proof session): byte-for-byte
///   upstream, which is the lane every upstream compiletest suite runs.
///
/// The MIR-pipeline options that would change the verified MIR —
/// `-Zmir-opt-level`, `-Zinline-mir`, `-Zinline-mir-threshold`,
/// `-Zinline-mir-hint-threshold`, `-Zinline-mir-forwarder-threshold`,
/// `-Zmir-enable-passes`, `-Zmir-opt-bisect-limit`, and a non-default
/// `-Zmir-preserve-ub` (it turns off `RemovePlaceMention`) or
/// `-Zmir-strip-debuginfo` (it turns on `StripDebugInfo`) — are REFUSED in a
/// proof session, by name (`rustc_driver_impl::trust_option_domain_error`), so
/// this function's answer is the only level such a session ever runs, and the
/// passes it runs are the pipeline's own.
///
/// Kept pure beside [`trust_verification_enabled_by_flags`] so the rule is pinned
/// without a [`Session`].
pub const fn trust_default_mir_opt_level_by_flags(
    optimize: OptLevel,
    verify: TrustVerify,
    proof_session: bool,
) -> usize {
    if matches!(optimize, OptLevel::No)
        || trust_verification_enabled_by_flags(verify)
        || proof_session
    {
        1
    } else {
        2
    }
}

/// Trust (T6): whether a compilation is a unit of a Trust proof session — it
/// verifies, or it carries a `-Ztrust-verify-session` (a verification-off
/// dependency whose MIR a verified dependent re-derives). Every such unit runs
/// the `-O0` MIR pipeline ([`trust_default_mir_opt_level_by_flags`]) and refuses
/// the MIR-pipeline options. Kept pure so the rule is pinned without a
/// [`Session`].
pub const fn trust_proof_session_by_flags(verify: TrustVerify, has_session: bool) -> bool {
    trust_verification_enabled_by_flags(verify) || has_session
}

/// Trust (T4.3): the front-end thread count (`-Zthreads`, as parsed) a
/// compilation runs with. A unit of a proof session
/// ([`trust_proof_session_by_flags`]) runs ONE front-end thread with
/// synchronization off (`None`), whatever the caller asked for: the parallel
/// frontend runs per-body work (MIR building, and the verification inside
/// `optimized_mir`) on pool threads that reach per-session and per-process
/// verifier state in an order the scheduler picks, and `-Zthreads` is
/// UNTRACKED, so a verdict must not depend on it. Pinned, not refused (plan
/// §3.5, Threads; DECISION_QUEUE FRONTEND-THREADS-1): unlike a MIR-pipeline
/// option, a thread count does not change the program that is compiled, so the
/// pinned verdict is about the very program the caller built and the pin hides
/// nothing the caller could rely on; and a build profile that sets one still
/// builds (aterm's `cfg(trust_verify)` table carries `-Zthreads=4`, which a
/// build naming no lane reads and verifies under). The vanilla lane keeps the
/// request. Kept pure so the rule is pinned without a [`Session`].
/// `rustc_interface` applies it before the parallel mode and the thread pool
/// exist, and [`build_session`] refuses a proof session it was not applied to,
/// so every reader of [`Session::threads`] sees the pinned value.
pub const fn trust_frontend_threads_by_flags(
    requested: Option<usize>,
    verify: TrustVerify,
    has_session: bool,
) -> Option<usize> {
    if trust_proof_session_by_flags(verify, has_session) { None } else { requested }
}

/// Trust (T6): the refusal of the MIR-pipeline option `unstable` sets, if any —
/// every option that changes which MIR passes run, or what they leave:
/// `-Zmir-opt-level`, `-Zinline-mir`, `-Zinline-mir-threshold`,
/// `-Zinline-mir-hint-threshold`, `-Zinline-mir-forwarder-threshold`,
/// `-Zmir-enable-passes`, `-Zmir-opt-bisect-limit`, and a non-default
/// `-Zmir-preserve-ub` or `-Zmir-strip-debuginfo` (flags with a default rather
/// than an `Option`, so only a non-default value can be seen). The ONE list: the
/// driver refuses it in a proof session (`rustc_driver_impl::trust_option_domain_error`)
/// and [`Session::trust_mir_is_proof_session_pipeline`] reads it for the metadata bit.
#[allow(rustc::bad_opt_access)]
pub fn trust_mir_pipeline_option_refusal(
    unstable: &crate::config::UnstableOptions,
) -> Option<&'static str> {
    macro_rules! refusal {
        ($flag:literal) => {
            concat!(
                "a Trust proof session runs the -O0 MIR pipeline for every unit; ",
                $flag,
                " would make the verified MIR, and so the verdicts, depend on the caller's MIR \
                 options. Remove it."
            )
        };
    }
    if unstable.mir_opt_level.is_some() {
        return Some(refusal!("-Zmir-opt-level"));
    }
    if unstable.inline_mir.is_some() {
        return Some(refusal!("-Zinline-mir"));
    }
    if unstable.inline_mir_threshold.is_some() {
        return Some(refusal!("-Zinline-mir-threshold"));
    }
    if unstable.inline_mir_hint_threshold.is_some() {
        return Some(refusal!("-Zinline-mir-hint-threshold"));
    }
    if unstable.inline_mir_forwarder_threshold.is_some() {
        return Some(refusal!("-Zinline-mir-forwarder-threshold"));
    }
    if !unstable.mir_enable_passes.is_empty() {
        return Some(refusal!("-Zmir-enable-passes"));
    }
    if unstable.mir_opt_bisect_limit.is_some() {
        return Some(refusal!("-Zmir-opt-bisect-limit"));
    }
    // `-Zmir-preserve-ub` turns off `RemovePlaceMention` (a required pass of the
    // -O0 pipeline) and changes `SimplifyCfg`'s handling of switch reads;
    // `-Zmir-strip-debuginfo` turns on `StripDebugInfo`.
    if unstable.mir_preserve_ub {
        return Some(refusal!("-Zmir-preserve-ub"));
    }
    if unstable.mir_strip_debuginfo != crate::config::MirStripDebugInfo::None {
        return Some(refusal!("-Zmir-strip-debuginfo"));
    }
    None
}

/// Trust: -O parity (ruling R2, 2026-09-25) — whether overflow checks are on when
/// `-Coverflow-checks` was not given ([`Session::overflow_checks`]).
///
/// Upstream: exactly `debug_assertions`, so off at `-O`. A VERIFYING session turns
/// them on at every opt-level. Policy B accepts an unproved arithmetic-overflow
/// obligation as `runtime-checked` only because the overflow `Assert` is kept in
/// the binary, and core's `#[rustc_inherit_overflow_checks]` arithmetic (the
/// `&i32 + 1` shape, reached through a foundational bundled member) inherits the
/// setting of the crate that codegens it; with checks off there is nothing for a
/// row to be runtime-checked BY.
///
/// SCOPE, as measured on `0.10.0+g16f58bb7a`. The default `strict` policy and
/// `certify` already force overflow checks AND debug assertions on before the
/// `Session` exists — over an explicit `-Coverflow-checks=off` too
/// (`rustc_driver_impl::canonicalize_trust_options`) — so this default is
/// observable only under `-Ztrust-policy=advisory` and `memory-safe`, where an
/// explicit `-Coverflow-checks=off` is still honored. The vanilla lane keeps
/// upstream's default.
pub const fn trust_default_overflow_checks_by_flags(
    debug_assertions: bool,
    verify: TrustVerify,
) -> bool {
    debug_assertions || trust_verification_enabled_by_flags(verify)
}

/// Trust: canonical resolution of the tri-state `-Ztrust-ir-lower` request.
///
/// The direct source (THIR) -> Trust-IR frontend is not optional under
/// verification, so an unset request follows verification.
/// `-Ztrust-verify=off` is the only lane where the option is a real choice, and
/// there it stays off unless asked for, because bootstrap and the
/// vanilla-comparison lanes depend on the direct frontend not running. Kept
/// pure so the pre-`Session` driver and option tests can pin every combination
/// without building a [`Session`].
pub const fn trust_ir_lower_enabled_by_flags(
    verify: TrustVerify,
    requested: Option<TrustIrLower>,
) -> bool {
    // Faithful translation of the historical `Option<bool>`: `Some(true)` became
    // `Some(On | Strict)`. Verification-on still wins unconditionally — an explicit value only
    // bites in the `-Ztrust-verify=off` compatibility lane, exactly as before. Widening `off` to
    // override verification would be a behaviour change smuggled in beside a new variant.
    trust_verification_enabled_by_flags(verify)
        || matches!(requested, Some(TrustIrLower::On | TrustIrLower::Strict))
}

/// Trust: does an unlowerable body FAIL the build rather than degrade to a coverage-only skip?
///
/// Strict is never implied by verification: it is an explicit request, because turning a silent
/// skip into an error changes which programs compile. Unset means "not strict" in both lanes.
///
/// Strict is also never honoured WITHOUT verification. `-Ztrust-verify=off` is the single
/// master off-switch for everything Trust adds to a compile, and a lowering shortfall is a
/// verification-quality finding: with no verdict being claimed there is nothing for it to fail
/// closed against. So `(Off, Some(Strict))` is `false` — the request degrades to a plain `On`
/// (the frontend still runs for the compat lane's diagnostics, and a body it cannot lower is a
/// coverage-only skip, exactly as under `-Ztrust-ir-lower=on`). Mirrors
/// [`trust_ir_lower_enabled_by_flags`]; the driver stamps the same answer, so the tracked
/// identity and every error site agree by construction.
pub const fn trust_ir_lower_strict_by_flags(
    verify: TrustVerify,
    requested: Option<TrustIrLower>,
) -> bool {
    trust_verification_enabled_by_flags(verify) && matches!(requested, Some(TrustIrLower::Strict))
}

/// Trust (hardened process semantics, 2026-09-14): the SIGPIPE disposition `main`
/// installs, as a pure function of the two options that decide it — the rule
/// [`Session::trust_effective_on_broken_pipe`] documents. It is the ONE effect of
/// `-Ztrust-verify-profile` that does not depend on verification running (it
/// holds under `-Ztrust-verify=off` too), so it is kept pure here for the one
/// other caller that must reproduce it exactly: frontend deauthorization, which
/// materializes this answer into `-Zon-broken-pipe` before it neutralizes the
/// profile, so a deauthorized frontend emits the same entry point the caller's
/// configuration asked for.
pub fn trust_effective_on_broken_pipe_by_flags(
    on_broken_pipe: rustc_target::spec::OnBrokenPipe,
    trust_verify_profile: Option<&str>,
) -> rustc_target::spec::OnBrokenPipe {
    use rustc_target::spec::OnBrokenPipe;
    match on_broken_pipe {
        OnBrokenPipe::Default => {
            // Same normalization as trust-vcgen's profile registry: `-`/`_`
            // and case are not meaningful in a profile label.
            let is_unix_or_coreutils_hardened = trust_verify_profile.is_some_and(|profile| {
                let trimmed = profile.trim();
                trimmed.eq_ignore_ascii_case("unix_hardened")
                    || trimmed.eq_ignore_ascii_case("unix-hardened")
                    || trimmed.eq_ignore_ascii_case("coreutils_hardened")
                    || trimmed.eq_ignore_ascii_case("coreutils-hardened")
            });
            if is_unix_or_coreutils_hardened {
                OnBrokenPipe::Kill
            } else {
                OnBrokenPipe::Default
            }
        }
        explicit => explicit,
    }
}

/// Targo-declared Cargo unit role used only for structured reporting. It is
/// deliberately non-authoritative: raw compiler callers control command-line
/// metadata, so scope may only be weakened by the explicit
/// `-Ztrust-verify=off` switch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustCrateRole {
    Unscoped,
    Primary,
    Dependency,
    BuildScript,
}

impl TrustCrateRole {
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "unscoped" => Some(Self::Unscoped),
            "primary" => Some(Self::Primary),
            "dependency" => Some(Self::Dependency),
            "build-script" => Some(Self::BuildScript),
            _ => None,
        }
    }

    pub fn is_cargo_primary(self) -> bool {
        matches!(self, Self::Primary)
    }
}

impl Session {
    pub fn miri_unleashed_feature(&self, span: Span, feature_gate: Option<Symbol>) {
        self.miri_unleashed_features.lock().push((span, feature_gate));
    }

    /// Trust (DC-18a): the host prefixes `-Ztrust-path-free` refuses in metadata: the local
    /// working directory, every `--remap-path-prefix` source, the sysroot, the output,
    /// temporary and incremental directories, and the home directory (`HOME`, and
    /// `USERPROFILE` on Windows hosts). Each names this checkout or this machine and no
    /// other, so a unit that writes one cannot be shared.
    pub fn trust_path_free_prefixes(&self) -> &rustc_span::trust_path_free::HostPrefixes {
        self.trust_path_free_prefixes.get_or_init(|| {
            let working_dir = self
                .source_map()
                .working_dir()
                .local_path()
                .map(|path| path.to_path_buf())
                .or_else(|| env::current_dir().ok())
                .unwrap_or_default();
            let mut candidates = vec![working_dir.clone()];
            candidates.extend(self.opts.remap_path_prefix.iter().map(|(from, _)| from.clone()));
            candidates.extend(self.opts.sysroot.all_paths().map(|path| path.to_path_buf()));
            candidates.extend(self.io.output_dir.clone());
            candidates.extend(self.io.temps_dir.clone());
            candidates.extend(self.opts.incremental.clone());
            candidates.extend(
                ["HOME", "USERPROFILE"].into_iter().filter_map(env::var_os).map(PathBuf::from),
            );
            rustc_span::trust_path_free::HostPrefixes::new(&working_dir, candidates)
        })
    }

    pub fn local_crate_source_file(&self) -> Option<RealFileName> {
        Some(
            self.source_map()
                .path_mapping()
                .to_real_filename(self.source_map().working_dir(), self.io.input.opt_path()?),
        )
    }

    fn check_miri_unleashed_features(&self) -> Option<ErrorGuaranteed> {
        let mut guar = None;
        let unleashed_features = self.miri_unleashed_features.lock();
        if !unleashed_features.is_empty() {
            let mut must_err = false;
            // Create a diagnostic pointing at where things got unleashed.
            self.dcx().emit_warn(diagnostics::SkippingConstChecks {
                unleashed_features: unleashed_features
                    .iter()
                    .map(|(span, gate)| {
                        gate.map(|gate| {
                            must_err = true;
                            diagnostics::UnleashedFeatureHelp::Named { span: *span, gate }
                        })
                        .unwrap_or(diagnostics::UnleashedFeatureHelp::Unnamed { span: *span })
                    })
                    .collect(),
            });

            // If we should err, make sure we did.
            if must_err && self.dcx().has_errors().is_none() {
                // We have skipped a feature gate, and not run into other errors... reject.
                guar = Some(self.dcx().emit_err(diagnostics::NotCircumventFeature));
            }
        }
        guar
    }

    /// Invoked all the way at the end to finish off diagnostics printing.
    pub fn finish_diagnostics(&self) -> Option<ErrorGuaranteed> {
        let mut guar = None;
        guar = guar.or(self.check_miri_unleashed_features());
        guar = guar.or(self.dcx().emit_stashed_diagnostics());
        self.dcx().print_error_count();
        if self.opts.json_future_incompat {
            self.dcx().emit_future_breakage_report();
        }
        guar
    }

    /// Returns true if the crate is a testing one.
    pub fn is_test_crate(&self) -> bool {
        self.opts.test
    }

    /// `feature` must be a language feature.
    #[track_caller]
    pub fn create_feature_err<'a>(&'a self, err: impl Diagnostic<'a>, feature: Symbol) -> Diag<'a> {
        let mut err = self.dcx().create_err(err);
        if err.code.is_none() {
            err.code(E0658);
        }
        diagnostics::add_feature_diagnostics(&mut err, self, feature);
        err
    }

    /// Record the fact that we called `trimmed_def_paths`, and do some
    /// checking about whether its cost was justified.
    pub fn record_trimmed_def_paths(&self) {
        if self.opts.unstable_opts.print_type_sizes
            || self.opts.unstable_opts.query_dep_graph
            || self.opts.unstable_opts.dump_mir.is_some()
            || self.opts.unstable_opts.unpretty.is_some()
            || self.prof.is_args_recording_enabled()
            || self.opts.output_types.contains_key(&OutputType::Mir)
            || std::env::var_os("RUSTC_LOG").is_some()
        {
            return;
        }

        self.dcx().set_must_produce_diag()
    }

    pub fn proc_macro_quoted_spans(&self) -> impl Iterator<Item = (usize, Span)> {
        // This is equivalent to `.iter().copied().enumerate()`, but that isn't possible for
        // AppendOnlyVec, so we resort to this scheme.
        self.proc_macro_quoted_spans.iter_enumerated()
    }

    pub fn save_proc_macro_span(&self, span: Span) -> usize {
        self.proc_macro_quoted_spans.push(span)
    }

    /// Returns `true` if internal lints should be added to the lint store - i.e. if
    /// `-Zunstable-options` is provided and this isn't rustdoc (internal lints can trigger errors
    /// to be emitted under rustdoc).
    pub fn enable_internal_lints(&self) -> bool {
        self.unstable_options() && !self.opts.actually_rustdoc
    }

    pub fn instrument_coverage(&self) -> bool {
        self.opts.cg.instrument_coverage() != InstrumentCoverage::No
    }

    pub fn instrument_coverage_branch(&self) -> bool {
        self.instrument_coverage()
            && self.opts.unstable_opts.coverage_options.level >= CoverageLevel::Branch
    }

    pub fn instrument_coverage_condition(&self) -> bool {
        self.instrument_coverage()
            && self.opts.unstable_opts.coverage_options.level >= CoverageLevel::Condition
    }

    /// Provides direct access to the `CoverageOptions` struct, so that
    /// individual flags for debugging/testing coverage instrumetation don't
    /// need separate accessors.
    pub fn coverage_options(&self) -> &CoverageOptions {
        &self.opts.unstable_opts.coverage_options
    }

    pub fn is_sanitizer_cfi_enabled(&self) -> bool {
        self.sanitizers().contains(SanitizerSet::CFI)
    }

    pub fn is_sanitizer_cfi_canonical_jump_tables_disabled(&self) -> bool {
        self.opts.unstable_opts.sanitizer_cfi_canonical_jump_tables == Some(false)
    }

    pub fn is_sanitizer_cfi_canonical_jump_tables_enabled(&self) -> bool {
        self.opts.unstable_opts.sanitizer_cfi_canonical_jump_tables == Some(true)
    }

    pub fn is_sanitizer_cfi_generalize_pointers_enabled(&self) -> bool {
        self.opts.unstable_opts.sanitizer_cfi_generalize_pointers == Some(true)
    }

    pub fn is_sanitizer_cfi_normalize_integers_enabled(&self) -> bool {
        self.opts.unstable_opts.sanitizer_cfi_normalize_integers == Some(true)
    }

    pub fn is_sanitizer_cfi_recover_enabled(&self) -> bool {
        self.opts.unstable_opts.sanitizer_cfi_recover == Some(true)
    }

    pub fn is_sanitizer_cfi_diag_enabled(&self) -> bool {
        self.opts.unstable_opts.sanitizer_cfi_diag == Some(true)
    }

    pub fn is_sanitizer_cfi_minimal_runtime_enabled(&self) -> bool {
        self.opts.unstable_opts.sanitizer_cfi_minimal_runtime == Some(true)
    }

    pub fn is_sanitizer_kcfi_arity_enabled(&self) -> bool {
        self.opts.unstable_opts.sanitizer_kcfi_arity == Some(true)
    }

    pub fn is_sanitizer_kcfi_enabled(&self) -> bool {
        self.sanitizers().contains(SanitizerSet::KCFI)
    }

    pub fn is_split_lto_unit_enabled(&self) -> bool {
        self.opts.unstable_opts.split_lto_unit == Some(true)
    }

    /// Check whether this compile session and crate type use static crt.
    pub fn crt_static(&self, crate_type: Option<CrateType>) -> bool {
        if !self.target.crt_static_respected {
            // If the target does not opt in to crt-static support, use its default.
            return self.target.crt_static_default;
        }

        let (found_positive, found_negative) = if self.opts.cg.target_feature.is_empty() {
            (false, false)
        } else {
            let mut pos = false;
            let mut neg = false;
            for r in self.opts.cg.target_feature.split(',') {
                if r == "+crt-static" {
                    pos = true;
                } else if r == "-crt-static" {
                    neg = true;
                }
            }
            (pos, neg)
        };

        // JUSTIFICATION: necessary use of crate_types directly (see FIXME below)
        #[allow(rustc::bad_opt_access)]
        if found_positive || found_negative {
            found_positive
        } else if crate_type == Some(CrateType::ProcMacro)
            || crate_type == None && self.opts.crate_types.contains(&CrateType::ProcMacro)
        {
            // FIXME: When crate_type is not available,
            // we use compiler options to determine the crate_type.
            // We can't check `#![crate_type = "proc-macro"]` here.
            false
        } else {
            self.target.crt_static_default
        }
    }

    pub fn is_wasi_reactor(&self) -> bool {
        self.target.options.os == Os::Wasi
            && matches!(
                self.opts.unstable_opts.wasi_exec_model,
                Some(config::WasiExecModel::Reactor)
            )
    }

    /// Returns `true` if the target can use the current split debuginfo configuration.
    pub fn target_can_use_split_dwarf(&self) -> bool {
        self.target.debuginfo_kind == DebuginfoKind::Dwarf
    }

    pub fn target_filesearch(&self) -> &filesearch::FileSearch {
        &self.target_filesearch
    }
    pub fn host_filesearch(&self) -> &filesearch::FileSearch {
        &self.host_filesearch
    }
    pub fn wasm_proc_macro_filesearch(&self) -> &filesearch::FileSearch {
        self.wasm_proc_macro_filesearch.as_ref().expect("wasm_filesearch not set")
    }

    /// Returns a list of directories where target-specific tool binaries are located. Some fallback
    /// directories are also returned, for example if `--sysroot` is used but tools are missing
    /// (#125246): we also add the bin directories to the sysroot where rustc is located.
    pub fn get_tools_search_paths(&self, self_contained: bool) -> Vec<PathBuf> {
        let search_paths = self
            .opts
            .sysroot
            .all_paths()
            .map(|sysroot| filesearch::make_target_bin_path(&sysroot, config::host_tuple()));

        if self_contained {
            // The self-contained tools are expected to be e.g. in `bin/self-contained` in the
            // sysroot's `rustlib` path, so we add such a subfolder to the bin path, and the
            // fallback paths.
            search_paths.flat_map(|path| [path.clone(), path.join("self-contained")]).collect()
        } else {
            search_paths.collect()
        }
    }

    /// Is this edition 2015?
    pub fn is_rust_2015(&self) -> bool {
        self.edition().is_rust_2015()
    }

    /// Are we allowed to use features from the Rust 2018 edition?
    pub fn at_least_rust_2018(&self) -> bool {
        self.edition().at_least_rust_2018()
    }

    /// Are we allowed to use features from the Rust 2021 edition?
    pub fn at_least_rust_2021(&self) -> bool {
        self.edition().at_least_rust_2021()
    }

    /// Are we allowed to use features from the Rust 2024 edition?
    pub fn at_least_rust_2024(&self) -> bool {
        self.edition().at_least_rust_2024()
    }

    /// Returns `true` if we should use the PLT for shared library calls.
    pub fn needs_plt(&self) -> bool {
        // Check if the current target usually wants PLT to be enabled.
        // The user can use the command line flag to override it.
        let want_plt = self.target.plt_by_default;

        let dbg_opts = &self.opts.unstable_opts;

        let relro_level = self.opts.cg.relro_level.unwrap_or(self.target.relro_level);

        // Only enable this optimization by default if full relro is also enabled.
        // In this case, lazy binding was already unavailable, so nothing is lost.
        // This also ensures `-Wl,-z,now` is supported by the linker.
        let full_relro = RelroLevel::Full == relro_level;

        // If user didn't explicitly forced us to use / skip the PLT,
        // then use it unless the target doesn't want it by default or the full relro forces it on.
        dbg_opts.plt.unwrap_or(want_plt || !full_relro)
    }

    /// Checks if LLVM lifetime markers should be emitted.
    pub fn emit_lifetime_markers(&self) -> bool {
        self.opts.optimize != config::OptLevel::No
        // AddressSanitizer and KernelAddressSanitizer uses lifetimes to detect use after scope bugs.
        //
        // MemorySanitizer uses lifetimes to detect use of uninitialized stack variables.
        //
        // HWAddressSanitizer and KernelHWAddressSanitizer will use lifetimes to detect use after
        // scope bugs in the future.
        || self.sanitizers().intersects(SanitizerSet::ADDRESS | SanitizerSet::KERNELADDRESS | SanitizerSet::MEMORY | SanitizerSet::HWADDRESS | SanitizerSet::KERNELHWADDRESS)
        // Lifetimes are necessary for retagging semantics.
        || self.opts.unstable_opts.codegen_emit_retag.is_some()
    }

    pub fn diagnostic_width(&self) -> usize {
        let default_column_width = 140;
        if let Some(width) = self.opts.diagnostic_width {
            width
        } else if self.opts.unstable_opts.ui_testing {
            default_column_width
        } else {
            termize::dimensions().map_or(default_column_width, |(w, _)| w)
        }
    }

    /// Returns the default symbol visibility.
    pub fn default_visibility(&self) -> SymbolVisibility {
        self.opts
            .unstable_opts
            .default_visibility
            .or(self.target.options.default_visibility)
            .unwrap_or(SymbolVisibility::Interposable)
    }

    pub fn staticlib_components(&self, verbatim: bool) -> (&str, &str) {
        if verbatim {
            ("", "")
        } else {
            (&*self.target.staticlib_prefix, &*self.target.staticlib_suffix)
        }
    }

    pub fn lint_groups_iter(&self) -> Box<dyn Iterator<Item = LintGroup> + '_> {
        match self.lint_store {
            Some(ref lint_store) => lint_store.lint_groups_iter(),
            None => Box::new(std::iter::empty()),
        }
    }

    /// Resolves a `path` mentioned inside Rust code, returning an absolute path.
    ///
    /// This unifies the logic used for resolving `include_*!` and debugger visualizers.
    pub fn resolve_path(&self, path: impl Into<PathBuf>, span: Span) -> PResult<'_, PathBuf> {
        let path = path.into();

        // Relative paths are resolved relative to the file in which they are found
        // after macro expansion (that is, they are unhygienic).
        if !path.is_absolute() {
            let callsite = span.source_callsite();
            let source_map = self.source_map();
            let Some(mut base_path) = source_map.span_to_filename(callsite).into_local_path()
            else {
                return Err(self.dcx().create_err(diagnostics::ResolveRelativePath {
                    span,
                    path: source_map
                        .filename_for_diagnostics(&source_map.span_to_filename(callsite))
                        .to_string(),
                }));
            };
            base_path.pop();
            base_path.push(path);
            Ok(base_path)
        } else {
            // This ensures that Windows verbatim paths are fixed if mixed path separators are used,
            // which can happen when `concat!` is used to join paths.
            match path.components().next() {
                Some(Prefix(prefix)) if prefix.kind().is_verbatim() => {
                    Ok(path.components().collect())
                }
                _ => Ok(path),
            }
        }
    }

    /// Should metadata be embedded within .rlib and .dylib files?
    pub fn embed_metadata(&self) -> bool {
        self.opts.cg.embed_metadata.or(self.opts.unstable_opts.embed_metadata).unwrap_or(true)
    }
}

// JUSTIFICATION: defn of the suggested wrapper fns
#[allow(rustc::bad_opt_access)]
impl Session {
    /// Trust: whether compiler-integrated verification is active.
    ///
    /// Verification is batteries-on for raw and Cargo-driven compiles.
    /// `-Ztrust-verify=off` is the sole off-switch used by vanilla/bootstrap
    /// lanes. Keep every compiler-side hook on this predicate so
    /// `cfg(trust_verify)`, proof-only type checking, and the MIR pass cannot
    /// disagree.
    pub fn trust_verification_enabled(&self) -> bool {
        trust_verification_enabled_by_flags(self.opts.unstable_opts.trust_verify)
    }

    /// Trust: whether this session reads fn, closure and coroutine bodies
    /// before they are stolen. Verification does, and so do the temporal
    /// censuses (`-Ztrust-send-census`, `-Ztrust-writer-census`, and a field
    /// binding an island declares), which force the spawn census in either
    /// lane. A local coroutine's layout must then
    /// come from its pre-steal MIR and never from an `optimized_mir` demanded
    /// inside the type system: that demand forces the census, and the census
    /// may be evaluating the very static whose initializer asked for the
    /// layout (E0391 on valid Rust).
    pub fn trust_reads_pre_steal_mir(&self) -> bool {
        self.trust_runs_spawn_census() || !self.trust_seals().is_empty()
    }

    /// Trust: whether this session runs the spawn census: verification does,
    /// and so do the temporal censuses. NOT a session whose only reader of
    /// pre-steal MIR is the seal check (`Trust.Protocol.Seal`), which reads
    /// each body once at the analysis seam and needs no census: forcing one
    /// there cost a crate with a seal the whole census (25 minutes on a
    /// crate of 48,000 bodies) for a check that takes seconds.
    pub fn trust_runs_spawn_census(&self) -> bool {
        self.trust_verification_enabled()
            || self.opts.unstable_opts.trust_send_census
            || self.opts.unstable_opts.trust_writer_census.is_some()
            || !self.trust_field_bindings().is_empty()
    }

    /// Trust (temporal P3): record the field bindings this crate's islands
    /// declare. The resolver calls it once, when it has elaborated the
    /// islands: before analysis, so that every later reader of
    /// [`Self::trust_reads_pre_steal_mir`] sees one answer. A second call is
    /// ignored.
    pub fn trust_set_field_bindings(&self, bindings: Vec<TrustFieldBinding>) {
        let _ = self.trust_field_bindings.set(bindings);
    }

    /// Trust (temporal P3): the field bindings this crate's islands declare
    /// ([`TrustFieldBinding`]); empty before the resolver has run and for a
    /// crate that declares none. A crate that declares one has its code
    /// checked against it by the thread census, which this forces in either
    /// lane.
    pub fn trust_field_bindings(&self) -> &[TrustFieldBinding] {
        self.trust_field_bindings.get().map_or(&[], Vec::as_slice)
    }

    /// Trust (temporal P3, sealed types): record the seals this crate's
    /// islands declare. Called once by the resolver with the bindings, under
    /// the same terms ([`Self::trust_set_field_bindings`]).
    pub fn trust_set_seals(&self, seals: Vec<TrustSeal>) {
        let _ = self.trust_seals.set(seals);
    }

    /// Trust (temporal P3, sealed types): the seals this crate's islands
    /// declare ([`TrustSeal`]); empty before the resolver has run and for a
    /// crate that declares none. A crate that declares one has every body
    /// checked against it, in either lane, before any body is stolen.
    pub fn trust_seals(&self) -> &[TrustSeal] {
        self.trust_seals.get().map_or(&[], Vec::as_slice)
    }

    /// Trust (hardened process semantics, 2026-09-14): the SIGPIPE disposition
    /// `main` installs at startup, AFTER the verification profile has had its
    /// say. An explicit `-Zon-broken-pipe` always wins. With none, the two
    /// Unix-tool profiles (`unix_hardened`, `coreutils_hardened`) declare `kill`
    /// — a write to a closed pipe terminates the process quietly, as C tools do
    /// — because "model broken-pipe/SIGPIPE compatibility instead of assuming
    /// Rust default process semantics" is the `process_semantics` mandate those
    /// profiles emit on every stdout write, and a mandate with no fix is a
    /// defect (v7/D3). The generic `hardened` profile assumes no platform and
    /// keeps the default, so its mandate stays open until the policy is
    /// declared. Both inputs are `[TRACKED]`, so the answer is in the crate hash.
    pub fn trust_effective_on_broken_pipe(&self) -> rustc_target::spec::OnBrokenPipe {
        trust_effective_on_broken_pipe_by_flags(
            self.opts.unstable_opts.on_broken_pipe,
            self.opts.unstable_opts.trust_verify_profile.as_deref(),
        )
    }

    /// Trust: the process-signal policy this compilation DECLARES, spelled as
    /// the `-Zon-broken-pipe` value, or `None` when it is merely assumed (Rust's
    /// default: SIGPIPE ignored, a write to a closed pipe returns `EPIPE`).
    /// Consumed by the hardened `process_semantics` discharge in trust-vcgen.
    pub fn trust_declared_process_signal_policy(&self) -> Option<&'static str> {
        use rustc_target::spec::OnBrokenPipe;
        match self.trust_effective_on_broken_pipe() {
            OnBrokenPipe::Default => None,
            OnBrokenPipe::Kill => Some("kill"),
            OnBrokenPipe::Error => Some("error"),
            OnBrokenPipe::Inherit => Some("inherit"),
        }
    }

    /// Trust: whether the direct source (THIR) -> Trust-IR frontend runs.
    ///
    /// The driver canonicalizes the request into the tracked field before this
    /// `Session` exists, but resolving here as well keeps custom-driver and
    /// embedded configurations on the same answer as the canonical lane instead
    /// of silently reading an unresolved request as "off".
    pub fn trust_ir_lower_enabled(&self) -> bool {
        trust_ir_lower_enabled_by_flags(
            self.opts.unstable_opts.trust_verify,
            self.opts.unstable_opts.trust_ir_lower,
        )
    }

    /// Trust: is the direct frontend in STRICT mode, where a body it cannot fully lower is a
    /// compile error rather than a coverage-only skip? See [`TrustIrLower`].
    pub fn trust_ir_lower_strict(&self) -> bool {
        trust_ir_lower_strict_by_flags(
            self.opts.unstable_opts.trust_verify,
            self.opts.unstable_opts.trust_ir_lower,
        )
    }

    /// Trust (platform protocols, plan L1a; OD-1): does the platform-protocol pass run, with
    /// the authority to fail the build under every `-Ztrust-policy`? See
    /// [`trust_platform_errors_enabled_by_flags`]. The pass and its errors are one predicate:
    /// there is no lane where it runs but may not error, or errors without running.
    pub fn trust_platform_errors_enabled(&self) -> bool {
        trust_platform_errors_enabled_by_flags(
            self.opts.unstable_opts.trust_verify,
            &self.opts.unstable_opts.trust_platform_properties,
        )
    }

    /// Trust (F1): does the trust-cg backend take its per-function input from the
    /// direct source (THIR) -> trust-ir producer instead of from MIR?
    ///
    /// Lives here because two very distant places need the same answer: the
    /// backend, which routes `trust_ir_of` into LIR, and `mir_built`'s hook,
    /// which must FORCE `trust_ir_of` while THIR is still alive. `check_unsafety`
    /// steals THIR during analysis, and the query's provider fails closed on a
    /// stolen `Thir`, so a consumer that first asks at codegen time would get
    /// `None` for every body in the crate. The backend applies the closed-domain
    /// parse (`trust_cg_frontend_from_name`) that rejects a typo; this predicate
    /// only answers "is the non-default producer selected", for which any value
    /// other than the exact spelling is `false`.
    pub fn trust_cg_frontend_is_trust_ir(&self) -> bool {
        self.opts.unstable_opts.trust_cg_frontend == "trust-ir"
    }

    /// Trust (step 2 increment 5, sub-step 5.4.2): does F1 compile its trust-ir on the opt-in
    /// COMPILER LANE (`-Ztrust-cg-f1-backend=compiler`: one codegen module per crate, trust-cg's
    /// `Compiler::compile`, the call-event gate) instead of the default `lir` lane? Meaningful
    /// only under [`Self::trust_cg_frontend_is_trust_ir`]. Any spelling other than the exact
    /// `compiler` answers `false`; the option parser and the driver's closed domain reject a
    /// typo before this is asked.
    pub fn trust_cg_f1_backend_is_compiler(&self) -> bool {
        self.opts.unstable_opts.trust_cg_f1_backend == "compiler"
    }

    /// Whether the trust-ir frontend takes its lowering context from the
    /// PUBLISHED crate module — and therefore binds the v41 codegen license
    /// (`trust_ir::Function::body_gate`) as a whole-module negative gate —
    /// rather than selecting each body through the per-instance assembled
    /// handoff. Meaningful only under [`Self::trust_cg_frontend_is_trust_ir`];
    /// off by default, because the handoff selects by exact definition
    /// identity and this lane selects by the producer's display path.
    pub fn trust_ir_crate_module(&self) -> bool {
        self.opts.unstable_opts.trust_ir_crate_module
    }

    /// Structured reporting role. Unknown callback-injected values are handled
    /// as `Unscoped`; the driver rejects them before work.
    pub fn trust_crate_role(&self) -> TrustCrateRole {
        TrustCrateRole::from_name(&self.opts.unstable_opts.trust_verify_crate_role)
            .unwrap_or(TrustCrateRole::Unscoped)
    }

    /// Whether this unit uses the fatal strict policy. The advisory and
    /// memory-safe policies keep verification active but stop it from failing
    /// the build on their own classes of unproved obligation.
    pub fn trust_strict_verification_enabled(&self) -> bool {
        self.trust_verification_enabled() && self.opts.unstable_opts.trust_policy.is_strict()
    }

    /// Trust: is this compile making a proof CLAIM — verification on AND a
    /// fail-closed policy? Every Trust finding that fails a build, rather than
    /// being reported, routes through this predicate; see
    /// [`trust_proof_claimed_by_flags`] for the rule and its one exception.
    pub fn trust_proof_claimed(&self) -> bool {
        trust_proof_claimed_by_flags(
            self.opts.unstable_opts.trust_verify,
            self.opts.unstable_opts.trust_policy,
        )
    }

    /// Trust: access invocation-scoped state for a compiler-integrated feature.
    ///
    /// The type itself is the key, so independent compiler subsystems cannot
    /// collide. Keeping the storage on `Session` is load-bearing for soundness:
    /// rustc_driver may create more than one compiler session in a process.
    pub fn with_trust_compiler_state<T, R>(&self, f: impl FnOnce(&mut T) -> R) -> R
    where
        T: Any + Default + Send,
    {
        let erased = {
            let mut states = self.trust_compiler_state.lock();
            states
                .entry(TypeId::of::<T>())
                .or_insert_with(|| Arc::new(TrustCompilerStateCell(Mutex::new(T::default()))))
                .clone()
        };
        let cell = Arc::downcast::<TrustCompilerStateCell<T>>(erased).unwrap_or_else(|_| {
            panic!("Trust compiler state TypeId mismatch for {}", type_name::<T>())
        });
        let mut state = cell.0.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        f(&mut state)
    }

    pub fn verbose_internals(&self) -> bool {
        self.opts.unstable_opts.verbose_internals
    }

    pub fn verify_llvm_ir(&self) -> bool {
        self.opts.unstable_opts.verify_llvm_ir || option_env!("RUSTC_VERIFY_LLVM_IR").is_some()
    }

    pub fn binary_dep_depinfo(&self) -> bool {
        self.opts.unstable_opts.binary_dep_depinfo
    }

    /// Trust (T6): whether this compilation's MIR is built by the proof-session
    /// `-O0` MIR pipeline — `mir-opt-level` 1 with no MIR-pipeline option
    /// ([`trust_mir_pipeline_option_refusal`]). Every unit of a proof session
    /// is; a vanilla build at `-Copt-level=0` with no such option is too, since
    /// it runs the same passes. Encoded into the crate's metadata
    /// (`trust_crate_mir_is_proof_session_pipeline`), so a verified dependent
    /// re-derives a dependency's encoded MIR only when it is that pipeline's —
    /// never a vanilla `-O` rmeta's inliner- and GVN-shaped MIR.
    pub fn trust_mir_is_proof_session_pipeline(&self) -> bool {
        self.mir_opt_level() == 1
            && trust_mir_pipeline_option_refusal(&self.opts.unstable_opts).is_none()
    }

    pub fn mir_opt_level(&self) -> usize {
        // Trust: -O parity (ruling R1, 2026-09-25; T6, 2026-10-09). Every unit of a
        // Trust proof session — a verifying one, or a verification-off dependency
        // carrying `-Ztrust-verify-session` — runs the `-O0` MIR pipeline at every
        // `-Copt-level`, so `TrustVerify` (the last MIR pass) sees the MIR `-O0`
        // verified, and a dependent re-derives `-O0` MIR. An explicit
        // `-Zmir-opt-level` is refused in such a session (the driver's option
        // domain), so it reaches here only for the vanilla lane, which keeps
        // upstream's `if optimize { 2 } else { 1 }` exactly. See
        // `trust_default_mir_opt_level_by_flags`.
        self.opts.unstable_opts.mir_opt_level.unwrap_or_else(|| {
            trust_default_mir_opt_level_by_flags(
                self.opts.optimize,
                self.opts.unstable_opts.trust_verify,
                self.opts.unstable_opts.trust_verify_session.is_some(),
            )
        })
    }

    /// Calculates the flavor of LTO to use for this compilation.
    pub fn lto(&self) -> config::Lto {
        // If our target has codegen requirements ignore the command line
        if self.target.requires_lto {
            return config::Lto::Fat;
        }

        // If the user specified something, return that. If they only said `-C
        // lto` and we've for whatever reason forced off ThinLTO via the CLI,
        // then ensure we can't use a ThinLTO.
        match self.opts.cg.lto {
            config::LtoCli::Unspecified => {
                // The compiler was invoked without the `-Clto` flag. Fall
                // through to the default handling
            }
            config::LtoCli::No => {
                // The user explicitly opted out of any kind of LTO
                return config::Lto::No;
            }
            config::LtoCli::Yes | config::LtoCli::Fat | config::LtoCli::NoParam => {
                // All of these mean fat LTO
                return config::Lto::Fat;
            }
            config::LtoCli::Thin => {
                // The user explicitly asked for ThinLTO
                if !self.thin_lto_supported {
                    // Backend doesn't support ThinLTO, fallback to fat LTO.
                    self.dcx().emit_warn(diagnostics::ThinLtoNotSupportedByBackend);
                    return config::Lto::Fat;
                }
                return config::Lto::Thin;
            }
        }

        if !self.thin_lto_supported {
            return config::Lto::No;
        }

        // Ok at this point the target doesn't require anything and the user
        // hasn't asked for anything. Our next decision is whether or not
        // we enable "auto" ThinLTO where we use multiple codegen units and
        // then do ThinLTO over those codegen units. The logic below will
        // either return `No` or `ThinLocal`.

        // If processing command line options determined that we're incompatible
        // with ThinLTO (e.g., `-C lto --emit llvm-ir`) then return that option.
        if self.opts.cli_forced_local_thinlto_off {
            return config::Lto::No;
        }

        // If `-Z thinlto` specified process that, but note that this is mostly
        // a deprecated option now that `-C lto=thin` exists.
        if let Some(enabled) = self.opts.unstable_opts.thinlto {
            if enabled {
                return config::Lto::ThinLocal;
            } else {
                return config::Lto::No;
            }
        }

        // If there's only one codegen unit and LTO isn't enabled then there's
        // no need for ThinLTO so just return false.
        if self.codegen_units().as_usize() == 1 {
            return config::Lto::No;
        }

        // Now we're in "defaults" territory. By default we enable ThinLTO for
        // optimized compiles (anything greater than O0).
        match self.opts.optimize {
            config::OptLevel::No => config::Lto::No,
            _ => config::Lto::ThinLocal,
        }
    }

    pub fn fewer_names(&self) -> bool {
        if let Some(fewer_names) = self.opts.unstable_opts.fewer_names {
            fewer_names
        } else {
            let more_names = self.opts.output_types.contains_key(&OutputType::LlvmAssembly)
                || self.opts.output_types.contains_key(&OutputType::Bitcode)
                // AddressSanitizer and MemorySanitizer use alloca name when reporting an issue.
                || self.sanitizers().intersects(SanitizerSet::ADDRESS | SanitizerSet::MEMORY);
            !more_names
        }
    }

    pub fn unstable_options(&self) -> bool {
        self.opts.unstable_opts.unstable_options
    }

    pub fn is_nightly_build(&self) -> bool {
        self.opts.unstable_features.is_nightly_build()
    }

    pub fn overflow_checks(&self) -> bool {
        // Trust: -O parity (ruling R2, 2026-09-25). A verifying session defaults overflow
        // checks ON at every opt-level, so a `runtime-checked` overflow row has a
        // check behind it; an explicit `-Coverflow-checks` wins (strict/certify
        // canonicalize it to on before this point). `-Ztrust-verify=off` keeps
        // upstream's `debug_assertions` default. See
        // `trust_default_overflow_checks_by_flags`.
        self.opts.cg.overflow_checks.unwrap_or_else(|| {
            trust_default_overflow_checks_by_flags(
                self.opts.debug_assertions,
                self.opts.unstable_opts.trust_verify,
            )
        })
    }

    pub fn ub_checks(&self) -> bool {
        self.opts.unstable_opts.ub_checks.unwrap_or(self.opts.debug_assertions)
    }

    pub fn contract_checks(&self) -> bool {
        self.opts.unstable_opts.contract_checks.unwrap_or(false)
    }

    pub fn direct_access_external_data(&self) -> Option<bool> {
        self.opts
            .unstable_opts
            .direct_access_external_data
            .or(self.target.direct_access_external_data)
    }

    pub fn split_debuginfo(&self) -> SplitDebuginfo {
        self.opts.cg.split_debuginfo.unwrap_or(self.target.split_debuginfo)
    }

    /// Returns the DWARF version passed on the CLI or the default for the target.
    pub fn dwarf_version(&self) -> u32 {
        self.opts
            .cg
            .dwarf_version
            .or(self.opts.unstable_opts.dwarf_version)
            .unwrap_or(self.target.default_dwarf_version)
    }

    pub fn stack_protector(&self) -> StackProtector {
        if self.target.options.supports_stack_protector {
            self.opts.unstable_opts.stack_protector
        } else {
            StackProtector::None
        }
    }

    /// Returns the `-Zbranch-protection` info. Note that it is adjusted to the current target, e.g.
    /// some targets only support certain Pointer Authentication Code keys.
    ///
    /// Accessing the session's unstable `branch_protection` option fields directly is linted
    /// against.
    pub fn branch_protection(&self) -> Option<BranchProtection> {
        let mut bp = self.opts.unstable_opts.branch_protection;

        if let Some(bp) = bp.as_mut() {
            // Windows on Arm only supports PAC Key B for return address signing, as shown in
            // https://github.com/llvm/llvm-project/pull/203989. We parse the CLI flags for branch
            // protection and target separately though, so we adjust this possible discrepancy here.
            if self.target.os == Os::Windows && self.target.arch == Arch::AArch64 {
                if let Some(pac_ret) = bp.pac_ret.as_mut()
                    && pac_ret.key == PAuthKey::A
                {
                    pac_ret.key = PAuthKey::B;
                }
            }
        }

        bp
    }

    pub fn must_emit_unwind_tables(&self) -> bool {
        // This is used to control the emission of the `uwtable` attribute on
        // LLVM functions. The `uwtable` attribute according to LLVM is:
        //
        //     This attribute indicates that the ABI being targeted requires that an
        //     unwind table entry be produced for this function even if we can show
        //     that no exceptions passes by it. This is normally the case for the
        //     ELF x86-64 abi, but it can be disabled for some compilation units.
        //
        // Typically when we're compiling with `-C panic=abort` we don't need
        // `uwtable` because we can't generate any exceptions! But note that
        // some targets require unwind tables to generate backtraces.
        // Unwind tables are needed when compiling with `-C panic=unwind`, but
        // LLVM won't omit unwind tables unless the function is also marked as
        // `nounwind`, so users are allowed to disable `uwtable` emission.
        // Historically rustc always emits `uwtable` attributes by default, so
        // even they can be disabled, they're still emitted by default.
        //
        // On some targets (including windows), however, exceptions include
        // other events such as illegal instructions, segfaults, etc. This means
        // that on Windows we end up still needing unwind tables even if the `-C
        // panic=abort` flag is passed.
        //
        // You can also find more info on why Windows needs unwind tables in:
        //      https://bugzilla.mozilla.org/show_bug.cgi?id=1302078
        //
        // If a target requires unwind tables, then they must be emitted.
        // Otherwise, we can defer to the `-C force-unwind-tables=<yes/no>`
        // value, if it is provided, or disable them, if not.
        self.target.requires_uwtable
            || self
                .opts
                .cg
                .force_unwind_tables
                .unwrap_or(self.panic_strategy().unwinds() || self.target.default_uwtable)
    }

    /// Returns the number of threads used for the thread pool.
    ///
    /// `None` means thread pool is not used and synchronization is disabled.
    /// `Some(n)` means synchronization is enabled with `n` worker threads.
    ///
    /// Trust (T4.3): `None` in every proof session. `rustc_interface::run_compiler`
    /// pins the option ([`trust_frontend_threads_by_flags`]) before the parallel
    /// mode and the thread pool exist, and [`build_session`], the one `Session`
    /// constructor, refuses (an internal compiler error) a proof session whose
    /// options were not pinned, so no `Session` reads otherwise.
    #[inline]
    pub fn threads(&self) -> Option<usize> {
        // Trust (1.101 port): upstream moved the frontend thread count from
        // `-Zthreads` (`unstable_opts.threads`, now a deprecated string) to
        // `opts.jobs.frontend`; `is_some()` there is exactly the old
        // "synchronization enabled" signal this accessor reported.
        self.opts.jobs.frontend.map(|n| n.get())
    }

    /// Returns the number of codegen units that should be used for this
    /// compilation
    pub fn codegen_units(&self) -> CodegenUnits {
        if let Some(n) = self.opts.cli_forced_codegen_units {
            return CodegenUnits::User(n);
        }
        if let Some(n) = self.target.default_codegen_units {
            return CodegenUnits::Default(n as usize);
        }

        // If incremental compilation is turned on, we default to a high number
        // codegen units in order to reduce the "collateral damage" small
        // changes cause.
        if self.opts.incremental.is_some() {
            return CodegenUnits::Default(256);
        }

        // Why is 16 codegen units the default all the time?
        //
        // The main reason for enabling multiple codegen units by default is to
        // leverage the ability for the codegen backend to do codegen and
        // optimization in parallel. This allows us, especially for large crates, to
        // make good use of all available resources on the machine once we've
        // hit that stage of compilation. Large crates especially then often
        // take a long time in codegen/optimization and this helps us amortize that
        // cost.
        //
        // Note that a high number here doesn't mean that we'll be spawning a
        // large number of threads in parallel. The backend of rustc contains
        // global rate limiting through the `jobserver` crate so we'll never
        // overload the system with too much work, but rather we'll only be
        // optimizing when we're otherwise cooperating with other instances of
        // rustc.
        //
        // Rather a high number here means that we should be able to keep a lot
        // of idle cpus busy. By ensuring that no codegen unit takes *too* long
        // to build we'll be guaranteed that all cpus will finish pretty closely
        // to one another and we should make relatively optimal use of system
        // resources
        //
        // Note that the main cost of codegen units is that it prevents LLVM
        // from inlining across codegen units. Users in general don't have a lot
        // of control over how codegen units are split up so it's our job in the
        // compiler to ensure that undue performance isn't lost when using
        // codegen units (aka we can't require everyone to slap `#[inline]` on
        // everything).
        //
        // If we're compiling at `-O0` then the number doesn't really matter too
        // much because performance doesn't matter and inlining is ok to lose.
        // In debug mode we just want to try to guarantee that no cpu is stuck
        // doing work that could otherwise be farmed to others.
        //
        // In release mode, however (O1 and above) performance does indeed
        // matter! To recover the loss in performance due to inlining we'll be
        // enabling ThinLTO by default (the function for which is just below).
        // This will ensure that we recover any inlining wins we otherwise lost
        // through codegen unit partitioning.
        //
        // ---
        //
        // Ok that's a lot of words but the basic tl;dr; is that we want a high
        // number here -- but not too high. Additionally we're "safe" to have it
        // always at the same number at all optimization levels.
        //
        // As a result 16 was chosen here! Mostly because it was a power of 2
        // and most benchmarks agreed it was roughly a local optimum. Not very
        // scientific.
        CodegenUnits::Default(16)
    }

    pub fn teach(&self, code: ErrCode) -> bool {
        self.opts.unstable_opts.teach && self.dcx().must_teach(code)
    }

    pub fn edition(&self) -> Edition {
        self.opts.edition
    }

    pub fn link_dead_code(&self) -> bool {
        self.opts.cg.link_dead_code.unwrap_or(false)
    }

    pub fn sanitizers(&self) -> SanitizerSet {
        self.sanitizers
    }

    pub fn pointer_authentication(&self) -> bool {
        self.pointer_auth_config.is_some()
    }

    pub fn pointer_authentication_functions(&self) -> Option<&PointerAuthSchema> {
        self.pointer_auth_config.as_ref().and_then(|cfg| cfg.function_pointers.as_ref())
    }

    pub fn pointer_authentication_init_fini(&self) -> Option<&PointerAuthSchema> {
        self.pointer_auth_config.as_ref().and_then(|cfg| cfg.init_fini.as_ref())
    }
}

// JUSTIFICATION: part of session construction
#[allow(rustc::bad_opt_access)]
fn default_emitter(sopts: &config::Options, source_map: Arc<SourceMap>) -> Box<DynEmitter> {
    let macro_backtrace = sopts.unstable_opts.macro_backtrace;
    let track_diagnostics = sopts.unstable_opts.track_diagnostics;
    let terminal_url = match sopts.unstable_opts.terminal_urls {
        TerminalUrl::Auto => {
            match (std::env::var("COLORTERM").as_deref(), std::env::var("TERM").as_deref()) {
                (Ok("truecolor"), Ok("xterm-256color"))
                    if sopts.unstable_features.is_nightly_build() =>
                {
                    TerminalUrl::Yes
                }
                _ => TerminalUrl::No,
            }
        }
        t => t,
    };

    let source_map = if sopts.unstable_opts.link_only { None } else { Some(source_map) };

    match sopts.error_format {
        config::ErrorOutputType::HumanReadable { kind, color_config } => match kind {
            HumanReadableErrorType { short, unicode } => {
                let emitter = AnnotateSnippetEmitter::new(stderr_destination(color_config))
                    .sm(source_map)
                    .short_message(short)
                    .diagnostic_width(sopts.diagnostic_width)
                    .macro_backtrace(macro_backtrace)
                    .track_diagnostics(track_diagnostics)
                    .terminal_url(terminal_url)
                    .theme(if unicode { OutputTheme::Unicode } else { OutputTheme::Ascii })
                    .ignored_directories_in_source_blocks(
                        sopts.unstable_opts.ignore_directory_in_diagnostics_source_blocks.clone(),
                    );
                Box::new(emitter.ui_testing(sopts.unstable_opts.ui_testing))
            }
        },
        config::ErrorOutputType::Json { pretty, json_rendered, color_config } => Box::new(
            JsonEmitter::new(
                Box::new(io::BufWriter::new(io::stderr())),
                source_map,
                pretty,
                json_rendered,
                color_config,
            )
            .ui_testing(sopts.unstable_opts.ui_testing)
            .ignored_directories_in_source_blocks(
                sopts.unstable_opts.ignore_directory_in_diagnostics_source_blocks.clone(),
            )
            .diagnostic_width(sopts.diagnostic_width)
            .macro_backtrace(macro_backtrace)
            .track_diagnostics(track_diagnostics)
            .terminal_url(terminal_url),
        ),
    }
}

// JUSTIFICATION: literally session construction
#[allow(rustc::bad_opt_access)]
pub fn build_early_session(
    sopts: config::Options,
    target: Target,
    ice_file: Option<PathBuf>,
) -> EarlySession {
    // FIXME: This is not general enough to make the warning lint completely override
    // normal diagnostic warnings, since the warning lint can also be denied and changed
    // later via the source code.
    let warnings_allow = sopts
        .lint_opts
        .iter()
        .rfind(|&(key, _)| *key == "warnings")
        .is_some_and(|&(_, level)| level == lint::Allow);
    let cap_lints_allow = sopts.lint_cap.is_some_and(|cap| cap == lint::Allow);
    let can_emit_warnings = !(warnings_allow || cap_lints_allow);

    let source_map = rustc_span::source_map::get_source_map().unwrap();
    let emitter = default_emitter(&sopts, Arc::clone(&source_map));

    let mut dcx =
        DiagCtxt::new(emitter).with_flags(sopts.unstable_opts.dcx_flags(can_emit_warnings));
    if let Some(ice_file) = ice_file {
        dcx = dcx.with_ice_file(ice_file);
    }

    // Trust (T4.3): no proof session's `Session` exists with its front-end
    // thread count unpinned. `rustc_interface` pins the option before the
    // parallel mode and the thread pool exist; a construction path that skipped
    // the pin would hand every `Session::threads` reader (the query system,
    // codegen's first CGU batch, the metadata prefetch) a parallel frontend the
    // verdict must not depend on. That is a compiler bug, never a user error, so
    // it is refused as one rather than repaired here, where the pool already
    // exists at the size the unpinned value chose.
    // Trust (1.101 port): read through `jobs.frontend` like `Session::threads`.
    let requested_threads = sopts.jobs.frontend.map(|n| n.get());
    if trust_frontend_threads_by_flags(
        requested_threads,
        sopts.unstable_opts.trust_verify,
        sopts.unstable_opts.trust_verify_session.is_some(),
    ) != requested_threads
    {
        dcx.handle().bug(format!(
            "Trust (T4.3): a proof session reached `build_session` with `-Zthreads` \
             {requested_threads:?} unpinned; `rustc_interface` pins it to one front-end \
             thread before the thread pool exists"
        ));
    }

    if let Some(msrv) = sopts.unstable_opts.hint_msrv {
        dcx = dcx.with_msrv(msrv);
    }

    let host_triple = TargetTuple::from_tuple(config::host_tuple());
    let (host, target_warnings) =
        Target::search(&host_triple, sopts.sysroot.path(), sopts.unstable_opts.unstable_options)
            .unwrap_or_else(|e| {
                dcx.handle().fatal(format!("Error loading host specification: {e}"))
            });
    for warning in target_warnings.warning_messages() {
        dcx.handle().warn(warning)
    }

    let psess = ParseSess::with_dcx(dcx, source_map);

    EarlySession { target, host, opts: sopts, psess }
}

// JUSTIFICATION: literally session construction
#[allow(rustc::bad_opt_access)]
pub fn build_session(
    early_sess: EarlySession,
    codegen_backend_init: CodegenBackendInit,
    io: CompilerIO,
    driver_lint_caps: FxHashMap<lint::LintId, lint::Level>,
    cfg_version: &'static str,
    using_internal_features: &'static AtomicBool,
) -> Session {
    let EarlySession { target, host, opts: sopts, psess } = &early_sess;
    let dcx = psess.dcx();

    let wasm_proc_macro_tuple = TargetTuple::from_tuple("wasm32-wasip2");
    let (wasm_proc_macro_target, target_warnings) = Target::search(
        &wasm_proc_macro_tuple,
        sopts.sysroot.path(),
        sopts.unstable_opts.unstable_options,
    )
    .unwrap_or_else(|e| {
        dcx.fatal(format!("Error loading wasm proc-macro target specification: {e}"))
    });
    for warning in target_warnings.warning_messages() {
        dcx.warn(warning)
    }

    let self_profiler = if let SwitchWithOptPath::Enabled(ref d) = sopts.unstable_opts.self_profile
    {
        let directory = if let Some(directory) = d { directory } else { std::path::Path::new(".") };

        let profiler = SelfProfiler::new(
            directory,
            sopts.crate_name.as_deref(),
            sopts.unstable_opts.self_profile_events.as_deref(),
            &sopts.unstable_opts.self_profile_counter,
        );
        match profiler {
            Ok(profiler) => Some(Arc::new(profiler)),
            Err(e) => {
                dcx.emit_warn(diagnostics::FailedToCreateProfiler { err: e.to_string() });
                None
            }
        }
    } else {
        None
    };

    let host_triple = config::host_tuple();
    let target_triple = sopts.target_triple.tuple();
    // FIXME use host sysroot?
    let host_tlib_path = SearchPath::from_sysroot_and_triple(sopts.sysroot.path(), host_triple);
    let target_tlib_path = SearchPath::from_sysroot_and_triple(sopts.sysroot.path(), target_triple);
    let wasm_proc_macro_tlib_path =
        SearchPath::from_sysroot_and_triple(sopts.sysroot.path(), wasm_proc_macro_tuple.tuple());

    let prof = SelfProfilerRef::new(
        self_profiler,
        sopts.unstable_opts.time_passes.then(|| sopts.unstable_opts.time_passes_format),
    );

    let ctfe_backtrace = Lock::new(match env::var("RUSTC_CTFE_BACKTRACE") {
        Ok(ref val) if val == "immediate" => CtfeBacktrace::Immediate,
        Ok(ref val) if val != "0" => CtfeBacktrace::Capture,
        _ => CtfeBacktrace::Disabled,
    });

    let asm_arch = if target.allow_asm { InlineAsmArch::from_arch(&target.arch) } else { None };
    let target_filesearch = Arc::new(filesearch::FileSearch::new(
        &sopts.search_paths,
        &target_tlib_path,
        &target,
        sopts.unstable_opts.implicit_sysroot_deps,
    ));
    let host_filesearch = if target == host {
        Arc::clone(&target_filesearch)
    } else {
        Arc::new(filesearch::FileSearch::new(
            &sopts.search_paths,
            &host_tlib_path,
            &host,
            sopts.unstable_opts.implicit_sysroot_deps,
        ))
    };
    let wasm_proc_macro_filesearch = if sopts.unstable_opts.wasm_proc_macros {
        Some(Arc::new(FileSearch::new(
            &sopts.search_paths,
            &wasm_proc_macro_tlib_path,
            &wasm_proc_macro_target,
            sopts.unstable_opts.implicit_sysroot_deps,
        )))
    } else {
        None
    };

    let timings = TimingSectionHandler::new(sopts.json_timings);

    let pointer_auth_config: Option<PointerAuthConfig> =
        PointerAuthConfig::from_raw(&sopts.unstable_opts.pointer_authentication, &target);

    // `EarlySess::sanitizers` does some computation but is called infrequently. `Sess::sanitizers`
    // is called much more often so we cache the value.
    let sanitizers = early_sess.sanitizers();

    let CodegenBackendInit {
        global_backend_features,
        replaced_intrinsics,
        fallback_intrinsics,
        thin_lto_supported,
    } = codegen_backend_init;

    let tool_input_collection =
        Lock::new(crate::tool_inputs::Collection::new(sopts.unstable_opts.trust_tool_inputs));
    // Trust: default compilation does not sample or publish tool observations.
    let tool_input_parent_path =
        sopts.unstable_opts.trust_tool_inputs.then(|| std::env::var_os("PATH")).flatten();
    let sess = Session {
        early_sess,
        wasm_proc_macro_tuple,
        wasm_proc_macro_target,
        target_tlib_path,
        unstable_features: UnstableFeatures::from_environment(None),
        config: Cfg::default(),
        check_config: CheckCfg::default(),
        proc_macro_quoted_spans: Default::default(),
        io,
        prof,
        timings,
        code_stats: Default::default(),
        lint_store: None,
        driver_lint_caps,
        ctfe_backtrace,
        miri_unleashed_features: Lock::new(Default::default()),
        asm_arch,
        internal_target_features: Default::default(),
        global_backend_features,
        cfg_version,
        using_internal_features,
        env_depinfo: Default::default(),
        file_depinfo: Default::default(),
        trust_path_free_refusals: Default::default(),
        trust_path_free_prefixes: Default::default(),
        tool_input_collection,
        tool_input_parent_path,
        target_filesearch,
        host_filesearch,
        wasm_proc_macro_filesearch,
        replaced_intrinsics: FxHashSet::from_iter(replaced_intrinsics),
        fallback_intrinsics: FxHashSet::from_iter(fallback_intrinsics),
        thin_lto_supported,
        mir_opt_bisect_eval_count: AtomicUsize::new(0),
        removed_rustc_main_attr: AtomicBool::new(false),
        trust_compiler_state: Lock::new(IntoDynSyncSend(FxHashMap::default())),
        trust_field_bindings: std::sync::OnceLock::new(),
        trust_seals: std::sync::OnceLock::new(),
        pointer_auth_config,
        sanitizers,
    };

    validate_commandline_args_with_session_available(&sess);

    sess
}

pub fn generate_proc_macro_decls_symbol(stable_crate_id: StableCrateId) -> String {
    format!("__rustc_proc_macro_decls_{:08x}__", stable_crate_id.as_u64())
}

/// Validate command line arguments with a `Session`.
///
/// If it is useful to have a Session available already for validating a commandline argument, you
/// can do so here.
// JUSTIFICATION: needs to access args to validate them
#[allow(rustc::bad_opt_access)]
fn validate_commandline_args_with_session_available(sess: &Session) {
    // Since we don't know if code in an rlib will be linked to statically or
    // dynamically downstream, rustc generates `__imp_` symbols that help linkers
    // on Windows deal with this lack of knowledge (#27438). Unfortunately,
    // these manually generated symbols confuse LLD when it tries to merge
    // bitcode during ThinLTO. Therefore we disallow dynamic linking on Windows
    // when compiling for LLD ThinLTO. This way we can validly just not generate
    // the `dllimport` attributes and `__imp_` symbols in that case.
    if sess.opts.cg.linker_plugin_lto.enabled()
        && sess.opts.cg.prefer_dynamic
        && sess.target.is_like_windows
    {
        sess.dcx().emit_err(diagnostics::LinkerPluginToWindowsNotSupported);
    }

    if sess
        .pointer_auth_config
        .as_ref()
        .and_then(|cfg| cfg.function_pointers.as_ref())
        .is_some_and(|schema| matches!(schema.discrimination_kind, PointerAuthDiscrimination::Type))
    {
        sess.dcx().emit_err(
            diagnostics::PointerAuthenticationTypeDiscriminationNotSupportedForTarget {
                target_triple: &sess.opts.target_triple,
            },
        );
    }

    if sess.target.cfg_abi != CfgAbi::Pauthtest
        && !sess.opts.unstable_opts.pointer_authentication.is_empty()
    {
        sess.dcx().emit_warn(diagnostics::PointerAuthenticationNotSupportedForTarget {
            target_triple: &sess.opts.target_triple,
        });
    }

    // Make sure that any given profiling data actually exists so LLVM can't
    // decide to silently skip PGO.
    if let Some(ref path) = sess.opts.cg.profile_use {
        if !path.exists() {
            sess.dcx().emit_err(diagnostics::ProfileUseFileDoesNotExist { path });
        }
    }

    // Do the same for sample profile data.
    if let Some(ref path) = sess.opts.cg.profile_sample_use {
        if !path.exists() {
            sess.dcx().emit_err(diagnostics::ProfileSampleUseFileDoesNotExist { path });
        }
    }

    // Unwind tables cannot be disabled if the target requires them.
    if let Some(include_uwtables) = sess.opts.cg.force_unwind_tables {
        if sess.target.requires_uwtable && !include_uwtables {
            sess.dcx().emit_err(diagnostics::TargetRequiresUnwindTables);
        }
    }

    // Sanitizers can only be used on platforms that we know have working sanitizer codegen.
    let supported_sanitizers = sess.target.options.supported_sanitizers;
    let mut unsupported_sanitizers = sess.sanitizers() - supported_sanitizers;
    // Niche: if `fixed-x18`, or effectively switching on `reserved-x18` flag, is enabled
    // we should allow Shadow Call Stack sanitizer.
    if sess.opts.unstable_opts.fixed_x18 && sess.target.arch == Arch::AArch64 {
        unsupported_sanitizers -= SanitizerSet::SHADOWCALLSTACK;
    }
    match unsupported_sanitizers.into_iter().count() {
        0 => {}
        1 => {
            sess.dcx().emit_err(diagnostics::SanitizerNotSupported {
                us: unsupported_sanitizers.to_string(),
            });
        }
        _ => {
            sess.dcx().emit_err(diagnostics::SanitizersNotSupported {
                us: unsupported_sanitizers.to_string(),
            });
        }
    }

    // Cannot mix and match mutually-exclusive sanitizers.
    if let Some((first, second)) = sess.sanitizers().mutually_exclusive() {
        sess.dcx().emit_err(diagnostics::CannotMixAndMatchSanitizers {
            first: first.to_string(),
            second: second.to_string(),
        });
    }

    // Cannot enable crt-static with sanitizers on Linux
    if sess.crt_static(None) && !sess.sanitizers().is_empty() && !sess.target.is_like_msvc {
        sess.dcx().emit_err(diagnostics::CannotEnableCrtStaticLinux);
    }

    // FIXME(jchlanda) Pauthtest does not support static linking. It must be dynamically linked,
    // with a dynamic linker acting as the ELF interpreter that can resolve pauth relocations and
    // enforce pointer authentication constraints.
    if sess.crt_static(None) && sess.target.cfg_abi == CfgAbi::Pauthtest {
        sess.dcx().emit_err(diagnostics::CannotEnableCrtStaticPointerAuth);
    }

    // LLVM CFI requires LTO.
    if sess.is_sanitizer_cfi_enabled()
        && !(sess.lto() == config::Lto::Fat || sess.opts.cg.linker_plugin_lto.enabled())
    {
        sess.dcx().emit_err(diagnostics::SanitizerCfiRequiresLto);
    }

    // KCFI requires panic=abort
    if sess.is_sanitizer_kcfi_enabled() && sess.panic_strategy().unwinds() {
        sess.dcx().emit_err(diagnostics::SanitizerKcfiRequiresPanicAbort);
    }

    // LLVM CFI using rustc LTO requires a single codegen unit.
    if sess.is_sanitizer_cfi_enabled()
        && sess.lto() == config::Lto::Fat
        && (sess.codegen_units().as_usize() != 1)
    {
        sess.dcx().emit_err(diagnostics::SanitizerCfiRequiresSingleCodegenUnit);
    }

    // Canonical jump tables requires CFI.
    if sess.is_sanitizer_cfi_canonical_jump_tables_disabled() {
        if !sess.is_sanitizer_cfi_enabled() {
            sess.dcx().emit_err(diagnostics::SanitizerCfiCanonicalJumpTablesRequiresCfi);
        }
    }

    // KCFI arity indicator requires KCFI.
    if sess.is_sanitizer_kcfi_arity_enabled() && !sess.is_sanitizer_kcfi_enabled() {
        sess.dcx().emit_err(diagnostics::SanitizerKcfiArityRequiresKcfi);
    }

    // LLVM CFI pointer generalization requires CFI or KCFI.
    if sess.is_sanitizer_cfi_generalize_pointers_enabled() {
        if !(sess.is_sanitizer_cfi_enabled() || sess.is_sanitizer_kcfi_enabled()) {
            sess.dcx().emit_err(diagnostics::SanitizerCfiGeneralizePointersRequiresCfi);
        }
    }

    // LLVM CFI recovery requires CFI.
    if sess.is_sanitizer_cfi_recover_enabled() {
        if !sess.is_sanitizer_cfi_enabled() {
            sess.dcx().emit_err(diagnostics::SanitizerCfiRecoverRequiresCfi);
        }
    }

    // LLVM CFI diagnostics requires CFI.
    if sess.is_sanitizer_cfi_diag_enabled() {
        if !sess.is_sanitizer_cfi_enabled() {
            sess.dcx().emit_err(diagnostics::SanitizerCfiDiagRequiresCfi);
        }
    }

    // LLVM CFI minimal runtime requires CFI recovery or CFI diagnostics.
    if sess.is_sanitizer_cfi_minimal_runtime_enabled() {
        if !sess.is_sanitizer_cfi_enabled() {
            sess.dcx().emit_err(diagnostics::SanitizerCfiMinimalRuntimeRequiresCfi);
        } else if !(sess.is_sanitizer_cfi_recover_enabled() || sess.is_sanitizer_cfi_diag_enabled())
        {
            sess.dcx().emit_err(diagnostics::SanitizerCfiMinimalRuntimeRequiresCfiRecoverOrDiag);
        }
    }

    // LLVM CFI integer normalization requires CFI or KCFI.
    if sess.is_sanitizer_cfi_normalize_integers_enabled() {
        if !(sess.is_sanitizer_cfi_enabled() || sess.is_sanitizer_kcfi_enabled()) {
            sess.dcx().emit_err(diagnostics::SanitizerCfiNormalizeIntegersRequiresCfi);
        }
    }

    // LTO unit splitting requires LTO.
    if sess.is_split_lto_unit_enabled()
        && !(sess.lto() == config::Lto::Fat
            || sess.lto() == config::Lto::Thin
            || sess.opts.cg.linker_plugin_lto.enabled())
    {
        sess.dcx().emit_err(diagnostics::SplitLtoUnitRequiresLto);
    }

    // VFE requires LTO.
    if sess.lto() != config::Lto::Fat {
        if sess.opts.unstable_opts.virtual_function_elimination {
            sess.dcx().emit_err(diagnostics::UnstableVirtualFunctionElimination);
        }
    }

    if sess.opts.unstable_opts.stack_protector != StackProtector::None {
        if !sess.target.options.supports_stack_protector {
            sess.dcx().emit_warn(diagnostics::StackProtectorNotSupportedForTarget {
                stack_protector: sess.opts.unstable_opts.stack_protector,
                target_triple: &sess.opts.target_triple,
            });
        }
    }

    if sess.opts.unstable_opts.small_data_threshold.is_some() {
        if sess.target.small_data_threshold_support() == SmallDataThresholdSupport::None {
            sess.dcx().emit_warn(diagnostics::SmallDataThresholdNotSupportedForTarget {
                target_triple: &sess.opts.target_triple,
            })
        }
    }

    if sess.opts.unstable_opts.branch_protection.is_some() && sess.target.arch != Arch::AArch64 {
        sess.dcx().emit_err(diagnostics::BranchProtectionRequiresAArch64);
    }

    if let Some(dwarf_version) =
        sess.opts.cg.dwarf_version.or(sess.opts.unstable_opts.dwarf_version)
    {
        // DWARF 1 is not supported by LLVM and DWARF 6 is not yet finalized.
        if dwarf_version < 2 || dwarf_version > 5 {
            sess.dcx().emit_err(diagnostics::UnsupportedDwarfVersion { dwarf_version });
        }
    }

    if !sess.target.options.supported_split_debuginfo.contains(&sess.split_debuginfo())
        && !sess.opts.unstable_opts.unstable_options
    {
        sess.dcx().emit_err(diagnostics::SplitDebugInfoUnstablePlatform {
            debuginfo: sess.split_debuginfo(),
        });
    }

    if sess.opts.unstable_opts.embed_source {
        let dwarf_version = sess.dwarf_version();

        if dwarf_version < 5 {
            sess.dcx()
                .emit_warn(diagnostics::EmbedSourceInsufficientDwarfVersion { dwarf_version });
        }

        if sess.opts.debuginfo == DebugInfo::None {
            sess.dcx().emit_warn(diagnostics::EmbedSourceRequiresDebugInfo);
        }
    }

    if let InstrumentMcount::Fentry(opts) = sess.opts.unstable_opts.instrument_mcount {
        if !sess.target.options.supports_fentry {
            sess.dcx()
                .emit_err(diagnostics::InstrumentationNotSupported { us: "fentry".to_string() });
        }
        if (opts.no_call || opts.record) && sess.target.arch != Arch::S390x {
            sess.dcx()
                .emit_err(diagnostics::InstrumentationNotSupported { us: "fentry-*".to_string() });
        }
    }

    if sess.opts.unstable_opts.instrument_xray.is_some() && !sess.target.options.supports_xray {
        sess.dcx().emit_err(diagnostics::InstrumentationNotSupported { us: "XRay".to_string() });
    }

    if let Some(flavor) = sess.opts.cg.linker_flavor
        && let Some(compatible_list) = sess.target.linker_flavor.check_compatibility(flavor)
    {
        let flavor = flavor.desc();
        sess.dcx().emit_err(diagnostics::IncompatibleLinkerFlavor { flavor, compatible_list });
    }

    if sess.opts.unstable_opts.function_return != FunctionReturn::default() {
        if !matches!(sess.target.arch, Arch::X86 | Arch::X86_64) {
            sess.dcx().emit_err(diagnostics::FunctionReturnRequiresX86OrX8664);
        }
    }

    if sess.opts.unstable_opts.indirect_branch_cs_prefix {
        if !matches!(sess.target.arch, Arch::X86 | Arch::X86_64) {
            sess.dcx().emit_err(diagnostics::IndirectBranchCsPrefixRequiresX86OrX8664);
        }
    }

    if let Some(regparm) = sess.opts.unstable_opts.regparm {
        if regparm > 3 {
            sess.dcx().emit_err(diagnostics::UnsupportedRegparm { regparm });
        }
        if sess.target.arch != Arch::X86 {
            sess.dcx().emit_err(diagnostics::UnsupportedRegparmArch);
        }
    }
    if sess.opts.unstable_opts.reg_struct_return {
        if sess.target.arch != Arch::X86 {
            sess.dcx().emit_err(diagnostics::UnsupportedRegStructReturnArch);
        }
    }

    // The code model check applies to `thunk` and `thunk-extern`, but not `thunk-inline`, so it is
    // kept as a `match` to force a change if new ones are added, even if we currently only support
    // `thunk-extern` like Clang.
    match sess.opts.unstable_opts.function_return {
        FunctionReturn::Keep => (),
        FunctionReturn::ThunkExtern => {
            // FIXME: In principle, the inherited base LLVM target code model could be large,
            // but this only checks whether we were passed one explicitly (like Clang does).
            if let Some(code_model) = sess.code_model()
                && code_model == CodeModel::Large
            {
                sess.dcx()
                    .emit_err(diagnostics::FunctionReturnThunkExternRequiresNonLargeCodeModel);
            }
        }
    }

    if sess.opts.unstable_opts.packed_stack {
        if sess.target.arch != Arch::S390x {
            sess.dcx().emit_err(diagnostics::UnsupportedPackedStack);
        }
    }

    if let Some(ref cpu_name) = sess.opts.cg.target_cpu {
        if cpu_name == NATIVE_CPU && sess.target.requires_consistent_cpu {
            sess.dcx().emit_fatal(diagnostics::NativeTargetCpuNotAllowed {
                target_triple: &sess.opts.target_triple,
                need_explicit_cpu: sess.target.need_explicit_cpu,
            });
        }
    }
}

/// Holds data on the current incremental compilation session, if there is one.
pub struct IncrCompSession {
    /// The directory from which cached data of a previous session can be read.
    pub old_session_directory: Option<flock::LockedDir>,
    /// The directory to which cached data for the current session can be
    /// written to.
    pub new_session_directory: flock::LockedDir,
    borrows: Arc<()>,
}

impl IncrCompSession {
    pub fn new(
        old_session_directory: Option<flock::LockedDir>,
        new_session_directory: flock::LockedDir,
    ) -> Self {
        IncrCompSession { old_session_directory, new_session_directory, borrows: Arc::new(()) }
    }

    pub fn borrow(&self) -> BorrowedIncrCompSession {
        BorrowedIncrCompSession {
            old_session_directory: self.old_session_directory.as_deref().map(ToOwned::to_owned),
            new_session_directory: (&*self.new_session_directory).to_owned(),
            _borrows: Arc::clone(&self.borrows),
        }
    }
}

impl Drop for IncrCompSession {
    fn drop(&mut self) {
        // Check that there are no worker threads remaining that use the incr
        // comp session before we unlock the old and new session dir. If there
        // does exist a worker thread, there is not much we can do, but at
        // least we will unconditionally complain rather than the worker thread
        // sometimes crashing depending on what other rustc instances run.
        assert!(
            Arc::strong_count(&self.borrows) == 1,
            "Incr comp session dropped while there are still references",
        );
    }
}

/// A runtime tracked borrow of the incr comp session. Can be sent to worker threads.
pub struct BorrowedIncrCompSession {
    pub old_session_directory: Option<PathBuf>,
    pub new_session_directory: PathBuf,
    _borrows: Arc<()>,
}

/// A wrapper around an [`DiagCtxt`] that is used for early error emissions.
pub struct EarlyDiagCtxt {
    dcx: DiagCtxt,
}

impl EarlyDiagCtxt {
    pub fn new(output: ErrorOutputType) -> Self {
        let emitter = mk_emitter(output);
        Self { dcx: DiagCtxt::new(emitter) }
    }

    /// Swap out the underlying dcx once we acquire the user's preference on error emission
    /// format. If `early_err` was previously called this will panic.
    pub fn set_error_format(&mut self, output: ErrorOutputType) {
        assert!(self.dcx.handle().has_errors().is_none());

        let emitter = mk_emitter(output);
        self.dcx = DiagCtxt::new(emitter);
    }

    #[must_use = "raise_fatal must be called on the returned ErrorGuaranteed in order to exit with a non-zero status code"]
    pub fn early_err(&self, msg: impl Into<DiagMessage>) -> ErrorGuaranteed {
        self.dcx.handle().err(msg)
    }

    pub fn early_fatal(&self, msg: impl Into<DiagMessage>) -> ! {
        self.dcx.handle().fatal(msg)
    }

    pub fn early_struct_fatal(&self, msg: impl Into<DiagMessage>) -> Diag<'_> {
        self.dcx.handle().struct_fatal(msg)
    }

    pub fn early_warn(&self, msg: impl Into<DiagMessage>) {
        self.dcx.handle().warn(msg)
    }

    pub fn early_struct_warn(&self, msg: impl Into<DiagMessage>) -> Diag<'_> {
        self.dcx.handle().struct_warn(msg)
    }
}

fn mk_emitter(output: ErrorOutputType) -> Box<DynEmitter> {
    let emitter: Box<DynEmitter> = match output {
        config::ErrorOutputType::HumanReadable { kind, color_config } => match kind {
            HumanReadableErrorType { short, unicode } => Box::new(
                AnnotateSnippetEmitter::new(stderr_destination(color_config))
                    .theme(if unicode { OutputTheme::Unicode } else { OutputTheme::Ascii })
                    .short_message(short),
            ),
        },
        config::ErrorOutputType::Json { pretty, json_rendered, color_config } => {
            Box::new(JsonEmitter::new(
                Box::new(io::BufWriter::new(io::stderr())),
                Some(Arc::new(SourceMap::new(FilePathMapping::empty()))),
                pretty,
                json_rendered,
                color_config,
            ))
        }
    };
    emitter
}
