//! Scaffold implementation of `rustc_codegen_ssa::traits::CodegenBackend` for trust_cg.
//!
//! This module defines a trait and types that mirror the real rustc `CodegenBackend`
//! interface from `compiler/rustc_codegen_ssa/src/traits/backend.rs`. The trait
//! cannot directly reference rustc internals (they are not available via Cargo),
//! so we define parallel types that map 1:1 to the rustc structures.
//!
//! When the compiler plugin is wired (via `x.py`), a thin adapter in
//! `compiler/` will delegate from the real rustc trait to this implementation.
//!
//! # Architecture
//!
//! ```text
//! rustc_codegen_ssa::traits::CodegenBackend  (compiler-internal)
//!     │
//!     ▼
//! compiler/rustc_codegen_trust_cg/  (future thin adapter, uses rustc types)
//!     │
//!     ▼
//! trust-cg-bridge::codegen_backend::RustcCodegenBackend  (this module)
//!     │
//!     ▼
//! trust-cg-bridge::lower_to_lir  (existing bridge)
//!     │
//!     ▼
//! trust_cg-lower / trust_cg-codegen  (trust-cg pipeline)
//! ```
//!
//! # Reference
//!
//! The real rustc `CodegenBackend` trait (compiler/rustc_codegen_ssa/src/traits/backend.rs)
//! requires these methods:
//! - `name() -> &'static str`
//! - `init(&self, sess: &Session)`
//! - `target_config(&self, sess: &Session) -> TargetConfig`
//! - `target_cpu(&self, sess: &Session) -> String`
//! - `codegen_crate(&self, tcx: TyCtxt, crate_info: &CrateInfo) -> Box<dyn Any>`
//! - `join_codegen(...) -> (CompiledModules, FxIndexMap<WorkProductId, WorkProduct>)`
//! - `link(&self, ...)`
//!
//! Our trait mirrors these with our own types in place of rustc's.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::any::Any;
use std::path::PathBuf;

use trust_cg_ir::{AArch64Opcode, BlockId as MachBlockId, MachFunction, MachOperand};
use trust_cg_lower::function::{
    BasicBlock as LirBasicBlock, Function as LirFunction, Signature as LirSignature,
};
use trust_cg_lower::instructions::{Block, Instruction as LirInstruction, Opcode, Value};
use trust_cg_lower::types::Type as LirType;
use trust_types::VerifiableFunction;
use trust_types::fx::FxHashSet;

use crate::lower::trust_location_file_global_data;
use crate::{BridgeError, LoweringOptions, PanicRuntimeSymbols, lower_to_lir_with_options};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from the codegen backend.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CodegenBackendError {
    /// Bridge lowering failure.
    #[error("bridge error: {0}")]
    Bridge(#[from] BridgeError),

    /// Backend is not available or not initialized.
    #[error("backend unavailable: {reason}")]
    Unavailable { reason: String },

    /// A codegen unit failed to compile.
    #[error("codegen unit `{unit_name}` failed: {reason}")]
    CodegenUnitFailed { unit_name: String, reason: String },

    /// An optimization pass failed.
    #[error("optimization failed on `{func_name}`: {reason}")]
    OptimizationFailed { func_name: String, reason: String },

    /// Object emission failed.
    #[error("emit_object failed: {reason}")]
    EmitFailed { reason: String },

    /// trust_cg-codegen pipeline failed while compiling a function.
    #[error("trust_cg pipeline failed for `{func_name}`: {reason}")]
    Pipeline { func_name: String, reason: String },

    /// Join/finalization failed.
    #[error("join failed: {reason}")]
    JoinFailed { reason: String },

    /// Link step failed.
    #[error("link failed: {reason}")]
    LinkFailed { reason: String },
}

// ---------------------------------------------------------------------------
// Types mirroring rustc_codegen_ssa structures
// ---------------------------------------------------------------------------

/// Target configuration, mirrors `rustc_codegen_ssa::TargetConfig`.
#[derive(Debug, Clone, Default)]
pub struct TargetConfig {
    /// Target features (e.g., "neon", "sse4.2").
    pub target_features: Vec<String>,
    /// Unstable target features.
    pub unstable_target_features: Vec<String>,
    /// Whether f16 basic arithmetic is reliable.
    pub has_reliable_f16: bool,
    /// Whether f16 math calls are reliable.
    pub has_reliable_f16_math: bool,
    /// Whether f128 basic arithmetic is reliable.
    pub has_reliable_f128: bool,
    /// Whether f128 math calls are reliable.
    pub has_reliable_f128_math: bool,
}

/// Crate-level information, mirrors `rustc_codegen_ssa::CrateInfo`.
///
/// Simplified for Trust's needs: target policy lives on the backend instance,
/// while this value carries crate identity and the functions to compile.
#[derive(Debug, Clone)]
pub struct CrateInfo {
    /// Crate name.
    pub crate_name: String,
    /// Functions to compile (extracted from MIR).
    pub functions: Vec<VerifiableFunction>,
}

/// A single compiled module (one codegen unit).
#[derive(Debug, Clone)]
pub struct CompiledModule {
    /// Module name (typically the codegen unit name).
    pub name: String,
    /// LIR functions produced by bridge lowering.
    pub lir_functions: Vec<LirFunction>,
    /// Object file path (if emitted).
    pub object_path: Option<PathBuf>,
    /// Number of functions in this module.
    pub function_count: usize,
    /// Trust (M-POS): the SOURCE `VerifiableFunction`s that produced
    /// `lir_functions`, captured BEFORE lowering, in 1:1 index correspondence
    /// with `lir_functions` (functions that failed to lower are filtered out of
    /// both). The proven-output gate (`verify_output::emit_objects_verified`)
    /// needs the source IR — not the lowered LIR — to derive intended semantics
    /// and refuse a Refuted (miscompiled) function. `None` when no sources were
    /// captured (e.g. legacy/test construction paths).
    pub source_functions: Option<Vec<VerifiableFunction>>,
}

/// Collection of all compiled modules for a crate.
#[derive(Debug, Clone)]
pub struct CompiledModules {
    /// Regular codegen unit modules.
    pub modules: Vec<CompiledModule>,
    /// Allocator module (if any).
    pub allocator_module: Option<CompiledModule>,
}

/// Allocator argument categories used by rustc shim wrappers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocatorArgKind {
    Layout,
    Ptr,
    Usize,
}

/// Allocator return categories used by rustc shim wrappers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocatorResultKind {
    Never,
    ResultPtr,
    Unit,
}

/// Known allocator shim wrapper kinds expected by rustc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocatorFunctionKind {
    Alloc,
    AllocErrorHandler,
    AllocZeroed,
    Dealloc,
    Realloc,
}

/// Bridge-native description of one allocator shim wrapper.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AllocatorFunctionSpec {
    /// The rustc allocator method name (e.g. `alloc`, `realloc`).
    pub name: String,
    /// Mangled rustc-internal symbol for the wrapper exported by this module.
    pub wrapper_symbol_name: String,
    /// Mangled rustc-internal symbol this wrapper forwards to.
    pub callee_symbol_name: String,
    /// Semantic kind of the wrapper to be emitted.
    pub kind: AllocatorFunctionKind,
    /// Logical input shape before rustc ABI lowering.
    pub inputs: Vec<AllocatorArgKind>,
    /// Logical return shape before rustc ABI lowering.
    pub output: AllocatorResultKind,
}

/// Bridge-native description of a rustc allocator shim module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AllocatorModuleSpec {
    /// Stable name to use for the allocator module artifact.
    pub module_name: String,
    /// Allocator wrappers rustc expects in this module.
    pub functions: Vec<AllocatorFunctionSpec>,
    /// Mangled rustc-internal symbol for `__rust_no_alloc_shim_is_unstable_v2`.
    pub no_alloc_shim_is_unstable_symbol_name: Option<String>,
}

/// Output file names, mirrors `rustc_session::config::OutputFilenames`.
#[derive(Debug, Clone)]
pub struct OutputFilenames {
    /// Directory for output files.
    pub out_dir: PathBuf,
    /// Crate stem name.
    pub crate_stem: String,
}

impl OutputFilenames {
    /// Construct the path for an object file with a given extension.
    #[must_use]
    pub fn object_path(&self, ext: &str) -> PathBuf {
        self.out_dir.join(format!("{}.{ext}", self.crate_stem))
    }
}

/// Opaque ongoing codegen handle, returned by `codegen_crate`.
///
/// This is the `Box<dyn Any>` returned by the rustc trait's `codegen_crate`
/// and consumed by `join_codegen`. We make it typed here for clarity.
#[derive(Debug)]
pub struct OngoingCodegen {
    /// Compiled modules accumulated during codegen.
    pub(crate) modules: Vec<CompiledModule>,
    /// Allocator module lowered separately from regular codegen units.
    pub(crate) allocator_module: Option<CompiledModule>,
    /// Rustc allocator shim intent attached before native lowering exists.
    pub(crate) allocator_module_spec: Option<AllocatorModuleSpec>,
    /// Functions that failed to compile (name + error).
    pub(crate) failures: Vec<(String, String)>,
    /// Crate name being compiled.
    pub(crate) crate_name: String,
}

impl OngoingCodegen {
    /// The name of the crate being compiled.
    #[must_use]
    pub fn crate_name(&self) -> &str {
        &self.crate_name
    }

    /// Number of successfully compiled functions.
    #[must_use]
    pub fn compiled_count(&self) -> usize {
        self.modules.iter().map(|m| m.function_count).sum::<usize>()
            + self.allocator_module.as_ref().map_or(0, |module| module.function_count)
    }

    /// Number of functions that failed to compile.
    #[must_use]
    pub fn failure_count(&self) -> usize {
        self.failures.len()
    }

    /// Allocator module lowered for this crate, if any.
    #[must_use]
    pub fn allocator_module(&self) -> Option<&CompiledModule> {
        self.allocator_module.as_ref()
    }

    /// Allocator module intent attached for later native lowering.
    #[must_use]
    pub fn allocator_module_spec(&self) -> Option<&AllocatorModuleSpec> {
        self.allocator_module_spec.as_ref()
    }
}

/// Work product tracking, mirrors `rustc_middle::dep_graph::WorkProduct`.
#[derive(Debug, Clone)]
pub struct WorkProduct {
    /// Path to the saved work product file.
    pub saved_file: PathBuf,
}

/// One object artifact emitted from a bridge compiled module.
#[derive(Debug, Clone)]
pub struct EmittedObject {
    /// Stable artifact name used for the object file path.
    pub artifact_name: String,
    /// Human-readable function name for diagnostics.
    pub source_name: String,
    /// Serialized object file bytes.
    pub bytes: Vec<u8>,
}

// ---------------------------------------------------------------------------
// The trait (mirrors rustc_codegen_ssa::traits::CodegenBackend)
// ---------------------------------------------------------------------------

/// Trait mirroring `rustc_codegen_ssa::traits::CodegenBackend`.
///
/// This is the interface that a codegen backend must implement to be usable
/// by the rustc compilation pipeline. Our types stand in for rustc's
/// `Session`, `TyCtxt`, etc.
///
/// When the compiler plugin adapter is built (in `compiler/rustc_codegen_trust_cg/`),
/// it will implement the real rustc trait by delegating to this one.
// Trust: CodegenBackend scaffold for trust_cg integration.
pub trait RustcCodegenBackend {
    /// Human-readable name (e.g., "trust-cg").
    fn name(&self) -> &'static str;

    /// Initialize the backend. Called once before codegen.
    fn init(&self) -> Result<(), CodegenBackendError> {
        Ok(())
    }

    /// Return target-specific configuration.
    fn target_config(&self) -> TargetConfig {
        TargetConfig::default()
    }

    /// Return the target CPU string.
    fn target_cpu(&self) -> String;

    /// Whether ThinLTO is supported.
    fn thin_lto_supported(&self) -> bool {
        false // trust_cg does not implement LTO.
    }

    /// Whether zstd compression is available.
    fn has_zstd(&self) -> bool {
        false
    }

    /// Compile all functions in a crate, returning an opaque handle.
    ///
    /// Mirrors `codegen_crate(&self, tcx: TyCtxt, crate_info: &CrateInfo) -> Box<dyn Any>`.
    fn codegen_crate(&self, crate_info: &CrateInfo) -> Result<Box<dyn Any>, CodegenBackendError>;

    /// Finalize codegen: join threads, collect results.
    ///
    /// Mirrors `join_codegen(&self, ongoing: Box<dyn Any>, ...) -> (CompiledModules, ...)`.
    fn join_codegen(
        &self,
        ongoing: Box<dyn Any>,
        outputs: &OutputFilenames,
    ) -> Result<(CompiledModules, Vec<WorkProduct>), CodegenBackendError>;

    /// Link compiled modules into a final binary.
    fn link(
        &self,
        compiled: &CompiledModules,
        outputs: &OutputFilenames,
    ) -> Result<PathBuf, CodegenBackendError>;

    /// Supported crate types.
    fn supported_crate_types(&self) -> Vec<&'static str> {
        vec!["bin", "rlib", "staticlib"]
    }

    /// Print backend version info.
    fn print_version(&self) {}

    /// Print pass timing statistics.
    fn print_pass_timings(&self) {}

    /// Print general statistics.
    fn print_statistics(&self) {}
}

// ---------------------------------------------------------------------------
// trust_cg implementation
// ---------------------------------------------------------------------------

/// trust_cg codegen backend implementing `RustcCodegenBackend`.
///
/// This is the struct that will back the rustc `CodegenBackend` trait
/// implementation when the compiler plugin is wired.
// Trust: CodegenBackend scaffold for trust_cg integration.
#[derive(Debug, Clone)]
pub struct TrustCgCodegenBackend {
    /// Target architecture.
    target_arch: TrustCgTargetArch,
    /// Full rustc target triple used for object format selection.
    target_triple: String,
    /// Runtime-sensitive lowering policy supplied by the rustc adapter.
    lowering_options: LoweringOptions,
    /// rustc-selected optimization level, shared by every target pipeline.
    optimization_level: BridgeOptimizationLevel,
    /// Effective target/CLI frame-pointer policy selected by rustc.
    frame_pointer_policy: BridgeFramePointerPolicy,
}

/// Target-independent optimization levels accepted from rustc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BridgeOptimizationLevel {
    O0,
    O1,
    O2,
    O3,
}

/// Frame-pointer preservation policy after rustc has ratcheted the target
/// baseline with the command-line request.
///
/// Trust-CG's x86-64 pipeline currently emits an RBP frame for every function,
/// which is a permitted strengthening of all three modes. Its AArch64 pipeline
/// naturally preserves X29 for every non-leaf function, but normally uses a
/// zero-frame optimization for eligible leaves; [`Always`](Self::Always)
/// disables that one omission through the bridge's post-preparation promotion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BridgeFramePointerPolicy {
    /// The backend may omit frame pointers.
    MayOmit,
    /// Non-leaf functions must preserve frame pointers.
    NonLeaf,
    /// Every function must preserve frame pointers.
    Always,
}

impl BridgeOptimizationLevel {
    fn aarch64_pipeline_level(self) -> trust_cg_codegen::pipeline::OptLevel {
        match self {
            Self::O0 => trust_cg_codegen::pipeline::OptLevel::O0,
            Self::O1 => trust_cg_codegen::pipeline::OptLevel::O1,
            Self::O2 => trust_cg_codegen::pipeline::OptLevel::O2,
            Self::O3 => trust_cg_codegen::pipeline::OptLevel::O3,
        }
    }

    fn x86_pipeline_level(self) -> trust_cg_opt::OptLevel {
        match self {
            Self::O0 => trust_cg_opt::OptLevel::O0,
            Self::O1 => trust_cg_opt::OptLevel::O1,
            Self::O2 => trust_cg_opt::OptLevel::O2,
            Self::O3 => trust_cg_opt::OptLevel::O3,
        }
    }
}

/// Target architectures supported by trust_cg.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustCgTargetArch {
    /// AArch64 (Apple Silicon, ARM64).
    AArch64,
    /// x86-64.
    X86_64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TargetObjectFamily {
    Elf,
    MachO,
    Coff,
}

fn audited_object_family(
    target_arch: TrustCgTargetArch,
    triple: &str,
) -> Result<TargetObjectFamily, CodegenBackendError> {
    let parts: Vec<_> = triple.split('-').collect();
    let family = match (target_arch, parts.as_slice()) {
        (TrustCgTargetArch::AArch64, ["aarch64", "unknown", "linux", "gnu" | "musl"])
        | (TrustCgTargetArch::X86_64, ["x86_64", "unknown", "linux", "gnu" | "musl"]) => {
            TargetObjectFamily::Elf
        }
        (TrustCgTargetArch::AArch64, ["aarch64", "apple", "darwin"])
        | (TrustCgTargetArch::X86_64, ["x86_64", "apple", "darwin"]) => TargetObjectFamily::MachO,
        (TrustCgTargetArch::X86_64, ["x86_64", "pc", "windows", "msvc" | "gnu" | "gnullvm"]) => {
            TargetObjectFamily::Coff
        }
        _ => {
            return Err(CodegenBackendError::Unavailable {
                reason: format!(
                    "target triple `{triple}` is not an exact audited {:?} target; supported \
                     families are <arch>-unknown-linux-(gnu|musl), <arch>-apple-darwin, and \
                     x86_64-pc-windows-(msvc|gnu|gnullvm)",
                    target_arch
                ),
            });
        }
    };
    Ok(family)
}

impl TrustCgTargetArch {
    /// Map a rustc target architecture string to an trust_cg target.
    #[must_use]
    pub fn from_rustc_arch(target_arch: &str) -> Option<Self> {
        match target_arch {
            "aarch64" => Some(Self::AArch64),
            "x86_64" => Some(Self::X86_64),
            _ => None,
        }
    }

    /// Auto-detect from compile-time target.
    #[must_use]
    pub fn host() -> Self {
        Self::try_host().expect(
            "trust-cg supports only aarch64 and x86_64 hosts; refusing to relabel an unsupported \
             compile-time architecture as x86_64",
        )
    }

    /// Fallible compile-time host detection without an architecture fallback.
    #[must_use]
    pub fn try_host() -> Option<Self> {
        if cfg!(target_arch = "aarch64") {
            Some(Self::AArch64)
        } else if cfg!(target_arch = "x86_64") {
            Some(Self::X86_64)
        } else {
            None
        }
    }

    /// Return the target CPU string for this architecture.
    #[must_use]
    fn cpu_string(self) -> &'static str {
        match self {
            Self::AArch64 => "generic",
            Self::X86_64 => "generic",
        }
    }

    /// Return the target triple.
    #[must_use]
    pub fn triple(self) -> &'static str {
        match self {
            Self::AArch64 => "aarch64-unknown-linux-gnu",
            Self::X86_64 => "x86_64-unknown-linux-gnu",
        }
    }

    /// Source-visible baseline features the generic emitter can actually use.
    ///
    /// The LLVM backend seeds these into `sess.unstable_target_features` (via
    /// `cfg_target_feature`, which expands the base target CPU) so that rustc's
    /// backend-independent ABI check (`rustc_monomorphize::mono_checks::abi_check`)
    /// and `check_abi_required_features` see the features the ABI requires
    /// (aarch64 passes 128-bit vectors in `neon` registers; x86_64's default
    /// hardfloat ABI requires `x87`+`sse2` and passes 128-bit vectors via `sse`).
    /// A non-LLVM backend has no target machine to query, so it must declare the
    /// relevant ABI prerequisites explicitly — otherwise every float-passing function warns
    /// "target feature `neon`/`sse2` must be enabled to ensure that the ABI ...
    /// can be implemented correctly" (issue #116344). Optional CPU features are
    /// deliberately absent: advertising one in `cfg(target_feature)` while the
    /// emitter rejects its instructions would miscompile conditional source.
    #[must_use]
    pub fn baseline_target_features(self) -> &'static [&'static str] {
        match self {
            // These are executable pipeline capabilities and therefore the
            // only names permitted in `cfg(target_feature)`. Backend-internal
            // ABI prerequisite names are added solely to the unstable superset
            // below; optional CPU features must not select source branches the
            // generic emitter will later reject.
            Self::AArch64 => &["neon"],
            Self::X86_64 => &["fxsr", "sse", "sse2"],
        }
    }
}

impl TrustCgCodegenBackend {
    /// Create a new trust_cg codegen backend for the given target.
    #[must_use]
    pub fn new(target_arch: TrustCgTargetArch) -> Self {
        Self::new_for_triple(target_arch, target_arch.triple())
    }

    /// Create a new trust_cg backend for a specific rustc target triple.
    ///
    /// Panics on an unsupported or architecture-mismatched triple. Call
    /// [`Self::try_new_for_triple`] when the triple is external input and the
    /// caller needs a recoverable diagnostic.
    #[must_use]
    pub fn new_for_triple(
        target_arch: TrustCgTargetArch,
        target_triple: impl Into<String>,
    ) -> Self {
        Self::try_new_for_triple(target_arch, target_triple).unwrap_or_else(|error| {
            panic!("refusing unsupported trust-cg target configuration: {error}")
        })
    }

    /// Fallible constructor for an exact audited target triple.
    pub fn try_new_for_triple(
        target_arch: TrustCgTargetArch,
        target_triple: impl Into<String>,
    ) -> Result<Self, CodegenBackendError> {
        let target_triple = target_triple.into();
        audited_object_family(target_arch, &target_triple)?;
        Ok(Self {
            target_arch,
            target_triple,
            lowering_options: LoweringOptions::default(),
            optimization_level: BridgeOptimizationLevel::O0,
            frame_pointer_policy: BridgeFramePointerPolicy::MayOmit,
        })
    }

    /// Use rustc's resolved optimization level for both target pipelines.
    #[must_use]
    pub fn with_optimization_level(mut self, level: BridgeOptimizationLevel) -> Self {
        self.optimization_level = level;
        self
    }

    /// Use rustc's effective target/CLI frame-pointer policy.
    #[must_use]
    pub fn with_frame_pointer_policy(mut self, policy: BridgeFramePointerPolicy) -> Self {
        self.frame_pointer_policy = policy;
        self
    }

    /// Install rust panic lang-item symbols for assertion lowering.
    #[must_use]
    pub fn with_panic_runtime_symbols(mut self, panic_symbols: PanicRuntimeSymbols) -> Self {
        self.lowering_options.panic_symbols = panic_symbols;
        self
    }

    /// Create a backend targeting the host architecture.
    ///
    /// The triple is host-accurate: object-format selection keys off the
    /// `<vendor>-<os>` portion of the triple, so a `host()` backend on
    /// `aarch64-apple-darwin` must emit Mach-O (not the linux-gnu default that
    /// [`TrustCgTargetArch::triple`] hardcodes). Otherwise native object
    /// emission and host linking on macOS would fail (the object would be ELF).
    #[must_use]
    pub fn host() -> Self {
        Self::new_for_triple(TrustCgTargetArch::host(), Self::host_triple())
    }

    /// Return the real host target triple for object-format selection.
    ///
    /// Unlike [`TrustCgTargetArch::triple`] (which always names linux-gnu),
    /// this reflects the compile-time host OS/vendor so the emitted object
    /// matches the platform that will load/link it.
    #[must_use]
    fn host_triple() -> &'static str {
        let arch = TrustCgTargetArch::host();
        if cfg!(all(target_vendor = "apple", target_os = "macos")) {
            return match arch {
                TrustCgTargetArch::AArch64 => "aarch64-apple-darwin",
                TrustCgTargetArch::X86_64 => "x86_64-apple-darwin",
            };
        }
        if cfg!(target_os = "linux") {
            return match arch {
                TrustCgTargetArch::AArch64 => "aarch64-unknown-linux-gnu",
                TrustCgTargetArch::X86_64 => "x86_64-unknown-linux-gnu",
            };
        }
        if cfg!(all(target_os = "windows", target_env = "msvc")) {
            if arch == TrustCgTargetArch::X86_64 {
                return "x86_64-pc-windows-msvc";
            }
        }
        if cfg!(all(target_os = "windows", target_env = "gnu")) {
            if arch == TrustCgTargetArch::X86_64 {
                return "x86_64-pc-windows-gnu";
            }
        }
        panic!(
            "trust-cg has no audited host triple for this compile-time OS/vendor/environment; \
             refusing to silently label it as Linux"
        )
    }

    /// Lower a single function through the bridge, returning the LIR.
    pub fn lower_function(
        &self,
        func: &VerifiableFunction,
    ) -> Result<LirFunction, CodegenBackendError> {
        Ok(lower_to_lir_with_options(func, &self.lowering_options)?)
    }

    /// Lower a batch of `VerifiableFunction`s into LIR, returning one
    /// `LirFunction` per input. Failures are collected per-function so that
    /// a single bad function does not prevent the rest from lowering.
    ///
    /// This is the module-level entry point that `codegen_crate` delegates to
    /// internally. Exposing it separately lets callers operate at the
    /// function-batch granularity without the full crate pipeline.
    pub fn lower_module(
        &self,
        functions: &[VerifiableFunction],
    ) -> Result<Vec<LirFunction>, CodegenBackendError> {
        let mut lir_fns = Vec::with_capacity(functions.len());
        let mut failures: Vec<(String, String)> = Vec::new();

        for func in functions {
            match self.lower_function(func) {
                Ok(lir) => lir_fns.push(lir),
                Err(e) => failures.push((func.name.clone(), e.to_string())),
            }
        }

        if failures.is_empty() {
            Ok(lir_fns)
        } else {
            let summary: String = failures
                .iter()
                .map(|(name, err)| format!("  {name}: {err}"))
                .collect::<Vec<_>>()
                .join("\n");
            Err(CodegenBackendError::CodegenUnitFailed {
                unit_name: "module".to_string(),
                reason: format!("{} function(s) failed to lower:\n{summary}", failures.len()),
            })
        }
    }

    /// Run scaffold optimizations on a single `LirFunction`.
    ///
    /// Currently performs dead-block elimination: removes blocks that are not
    /// reachable from the entry block. When trust-cg's `trust_cg-opt` crate is wired
    /// as a dependency, this will delegate to its full pass pipeline (DCE, GVN,
    /// copy propagation, etc.).
    pub fn optimize(&self, func: &mut LirFunction) -> Result<(), CodegenBackendError> {
        // Scaffold: dead-block elimination.
        // Walk reachable blocks from entry via BFS.
        use std::collections::VecDeque;

        let mut reachable = FxHashSet::default();
        let mut queue = VecDeque::new();
        queue.push_back(func.entry_block);
        reachable.insert(func.entry_block);

        while let Some(block) = queue.pop_front() {
            if let Some(bb) = func.blocks.get(&block) {
                for instr in &bb.instructions {
                    for target in Self::branch_targets(&instr.opcode) {
                        if reachable.insert(target) {
                            queue.push_back(target);
                        }
                    }
                }
            }
        }

        // Remove unreachable blocks without relying on hash-map retain order.
        for block in sorted_lir_block_ids(func) {
            if !reachable.contains(&block) {
                func.blocks.remove(&block);
            }
        }

        Ok(())
    }

    /// Collect all branch target blocks from an opcode.
    fn branch_targets(opcode: &Opcode) -> Vec<Block> {
        match opcode {
            Opcode::Jump { dest } => vec![*dest],
            Opcode::Brif { then_dest, else_dest, .. } => {
                vec![*then_dest, *else_dest]
            }
            Opcode::Switch { cases, default } => {
                let mut targets: Vec<Block> = cases.iter().map(|(_, blk)| *blk).collect();
                targets.push(*default);
                targets
            }
            Opcode::Invoke { normal_dest, unwind_dest, .. } => {
                vec![*normal_dest, *unwind_dest]
            }
            _ => Vec::new(),
        }
    }

    /// Emit a real object file for a single-function module.
    ///
    /// Object format is selected from the configured rustc target triple.
    pub fn emit_object(&self, module: &[LirFunction]) -> Result<Vec<u8>, CodegenBackendError> {
        if module.is_empty() {
            return Err(CodegenBackendError::EmitFailed {
                reason: "empty module: no functions to emit".to_string(),
            });
        }

        if module.len() > 1 {
            return Err(CodegenBackendError::EmitFailed {
                reason: "multi-function modules not yet supported by trust_cg-codegen path; call emit_objects".to_string(),
            });
        }

        let source_name = module[0].name.clone();
        let bytes = self.emit_target_object(module)?;

        Self::require_non_empty_object(bytes, &source_name)
    }

    /// Emit one object file per function.
    ///
    /// Each function is emitted through the same target-triple-aware object path
    /// as [`Self::emit_object`].
    pub fn emit_objects(
        &self,
        module: &[LirFunction],
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenBackendError> {
        if module.is_empty() {
            return Err(CodegenBackendError::EmitFailed {
                reason: "empty module: no functions to emit".to_string(),
            });
        }

        module
            .iter()
            .map(|func| {
                let bytes = self.emit_target_object(std::slice::from_ref(func))?;
                let bytes = Self::require_non_empty_object(bytes, &func.name)?;
                Ok((func.name.clone(), bytes))
            })
            .collect()
    }

    /// Emit the object files required for one compiled module.
    ///
    /// Single-function modules produce a single artifact named after the module.
    /// Multi-function modules are split into one object per function with stable
    /// artifact names derived from the module name and function index.
    pub fn emit_module_objects(
        &self,
        module: &CompiledModule,
    ) -> Result<Vec<EmittedObject>, CodegenBackendError> {
        match module.lir_functions.len() {
            0 => Err(CodegenBackendError::EmitFailed {
                reason: format!(
                    "compiled module `{}` has no functions; refusing objectless output",
                    module.name
                ),
            }),
            1 => {
                let func = &module.lir_functions[0];
                self.emit_object(&module.lir_functions).map(|bytes| {
                    vec![EmittedObject {
                        artifact_name: module.name.clone(),
                        source_name: func.name.clone(),
                        bytes,
                    }]
                })
            }
            _ => self.emit_objects(&module.lir_functions).map(|objects| {
                objects
                    .into_iter()
                    .enumerate()
                    .map(|(index, (func_name, bytes))| EmittedObject {
                        artifact_name: format!("{}.f{index}", module.name),
                        source_name: func_name,
                        bytes,
                    })
                    .collect()
            }),
        }
    }

    fn require_non_empty_object(
        bytes: Vec<u8>,
        source_name: &str,
    ) -> Result<Vec<u8>, CodegenBackendError> {
        if bytes.is_empty() {
            return Err(CodegenBackendError::EmitFailed {
                reason: format!(
                    "object emission for `{source_name}` produced zero bytes; refusing missing output"
                ),
            });
        }

        Ok(bytes)
    }

    fn allocator_arg_types(kind: AllocatorArgKind) -> Vec<LirType> {
        match kind {
            // The bridge targets 64-bit architectures today, so rustc's
            // `(size, align)` layout pair and usize/pointer values lower to I64s.
            AllocatorArgKind::Layout => vec![LirType::I64, LirType::I64],
            AllocatorArgKind::Ptr | AllocatorArgKind::Usize => vec![LirType::I64],
        }
    }

    fn allocator_result_types(kind: AllocatorResultKind) -> Vec<LirType> {
        match kind {
            AllocatorResultKind::Never | AllocatorResultKind::Unit => Vec::new(),
            AllocatorResultKind::ResultPtr => vec![LirType::I64],
        }
    }

    fn allocator_wrapper_from_spec(spec: &AllocatorFunctionSpec) -> LirFunction {
        let param_types =
            spec.inputs.iter().copied().flat_map(Self::allocator_arg_types).collect::<Vec<_>>();
        let result_types = Self::allocator_result_types(spec.output);
        let param_count = param_types.len() as u32;
        let call_result = (!result_types.is_empty()).then_some(Value(param_count));

        let mut function = LirFunction::new(
            spec.wrapper_symbol_name.clone(),
            LirSignature { params: param_types, returns: result_types.clone() },
        );
        if let Some(result) = call_result {
            function.value_types.insert(result, result_types[0].clone());
        }

        let mut entry = LirBasicBlock::default();
        entry.instructions.push(LirInstruction {
            opcode: Opcode::Call { name: spec.callee_symbol_name.clone() },
            args: (0..param_count).map(Value).collect(),
            results: call_result.into_iter().collect(),
        });
        if spec.output != AllocatorResultKind::Never {
            entry.instructions.push(LirInstruction {
                opcode: Opcode::Return,
                args: call_result.into_iter().collect(),
                results: vec![],
            });
        }

        function.blocks.insert(Block(0), entry);
        function
    }

    fn allocator_marker_function(symbol_name: &str) -> LirFunction {
        let mut function = LirFunction::new(symbol_name.to_string(), LirSignature::default());
        let mut entry = LirBasicBlock::default();
        entry.instructions.push(LirInstruction {
            opcode: Opcode::Return,
            args: vec![],
            results: vec![],
        });
        function.blocks.insert(Block(0), entry);
        function
    }

    fn allocator_module_from_spec(
        spec: &AllocatorModuleSpec,
    ) -> Result<CompiledModule, CodegenBackendError> {
        let mut lir_functions =
            spec.functions.iter().map(Self::allocator_wrapper_from_spec).collect::<Vec<_>>();
        if let Some(symbol_name) = &spec.no_alloc_shim_is_unstable_symbol_name {
            lir_functions.push(Self::allocator_marker_function(symbol_name));
        }

        Ok(CompiledModule {
            name: spec.module_name.clone(),
            function_count: lir_functions.len(),
            lir_functions,
            object_path: None,
            // Allocator shim wrappers are synthesized, not lowered from source
            // VerifiableFunctions, so there is nothing for the output gate to
            // verify: None.
            source_functions: None,
        })
    }

    fn aarch64_has_call(func: &MachFunction) -> bool {
        func.insts.iter().any(|inst| {
            matches!(inst.opcode, AArch64Opcode::Bl | AArch64Opcode::Blr)
                || (inst.opcode == AArch64Opcode::B
                    && matches!(inst.operands.as_slice(), [MachOperand::Symbol(_)]))
        })
    }

    /// Recover cross-block targets after the upstream preparation path has
    /// resolved symbolic block operands to PC-relative immediates. Frame
    /// promotion inserts instructions at entry and exit, so those offsets must
    /// be made symbolic again before running the canonical resolver a second
    /// time. Same-block fixed-distance branches (for example a guard skipping a
    /// trap) are intentionally left alone: entry insertion shifts both ends by
    /// the same amount, and the epilogue begins at the old return position.
    fn aarch64_resolved_cross_block_targets(
        func: &MachFunction,
    ) -> Result<Vec<(usize, MachBlockId)>, CodegenBackendError> {
        let mut block_ranges = Vec::with_capacity(func.block_order.len());
        let mut next_offset = 0_i64;
        for &block_id in &func.block_order {
            let start = next_offset;
            for &inst_id in &func.blocks[block_id.0 as usize].insts {
                if !func.insts[inst_id.0 as usize].is_pseudo() {
                    next_offset += 1;
                }
            }
            block_ranges.push((block_id, start, next_offset));
        }

        let mut resolved = Vec::new();
        let mut inst_offset = 0_i64;
        for &(source_block, source_start, source_end) in &block_ranges {
            let block = &func.blocks[source_block.0 as usize];
            for &inst_id in &block.insts {
                let inst = &func.insts[inst_id.0 as usize];
                if inst.is_pseudo() {
                    continue;
                }

                let is_branch = matches!(
                    inst.opcode,
                    AArch64Opcode::B
                        | AArch64Opcode::BCond
                        | AArch64Opcode::Cbz
                        | AArch64Opcode::Cbnz
                        | AArch64Opcode::Tbz
                        | AArch64Opcode::Tbnz
                );
                let Some(MachOperand::Imm(relative)) = inst.operands.last() else {
                    inst_offset += 1;
                    continue;
                };
                if !is_branch {
                    inst_offset += 1;
                    continue;
                }

                let target_offset = inst_offset.checked_add(*relative).ok_or_else(|| {
                    CodegenBackendError::Pipeline {
                        func_name: func.name.clone(),
                        reason: "frame-pointer promotion overflowed a resolved branch offset"
                            .to_string(),
                    }
                })?;

                // Fixed-distance intra-block branches retain their distance.
                if (source_start..source_end).contains(&target_offset) {
                    inst_offset += 1;
                    continue;
                }

                let candidates = block_ranges
                    .iter()
                    .filter(|(_, start, _)| *start == target_offset)
                    .map(|(block_id, _, _)| *block_id)
                    .collect::<Vec<_>>();
                let target = candidates
                    .iter()
                    .copied()
                    .find(|candidate| block.succs.contains(candidate))
                    .or_else(|| (candidates.len() == 1).then_some(candidates[0]))
                    .ok_or_else(|| CodegenBackendError::Pipeline {
                        func_name: func.name.clone(),
                        reason: format!(
                            "cannot recover cross-block target at instruction offset \
                             {inst_offset} (resolved target {target_offset}) while forcing an \
                             AArch64 frame pointer; refusing to emit stale branch offsets"
                        ),
                    })?;
                resolved.push((inst_id.0 as usize, target));
                inst_offset += 1;
            }
        }
        Ok(resolved)
    }

    fn enforce_aarch64_frame_pointer_policy(
        &self,
        func: &mut MachFunction,
        prepared_layout: &trust_cg_codegen::frame::FrameLayout,
    ) -> Result<(), CodegenBackendError> {
        if prepared_layout.uses_frame_pointer {
            return Ok(());
        }

        if self.frame_pointer_policy == BridgeFramePointerPolicy::NonLeaf
            && Self::aarch64_has_call(func)
        {
            return Err(CodegenBackendError::Pipeline {
                func_name: func.name.clone(),
                reason: "AArch64 non-leaf function was prepared without the required frame pointer"
                    .to_string(),
            });
        }
        if self.frame_pointer_policy != BridgeFramePointerPolicy::Always {
            return Ok(());
        }

        let cross_block_targets = Self::aarch64_resolved_cross_block_targets(func)?;
        let outgoing_arg_size = trust_cg_codegen::frame::compute_max_outgoing_arg_size(func);
        let forced_layout =
            trust_cg_codegen::frame::compute_frame_layout(func, outgoing_arg_size, false);
        if !forced_layout.uses_frame_pointer {
            return Err(CodegenBackendError::Pipeline {
                func_name: func.name.clone(),
                reason: "AArch64 `always` frame-pointer policy did not produce an FP/LR frame"
                    .to_string(),
            });
        }

        trust_cg_codegen::frame::insert_prologue_epilogue(func, &forced_layout).map_err(
            |error| CodegenBackendError::Pipeline {
                func_name: func.name.clone(),
                reason: format!("AArch64 frame-pointer promotion failed: {error}"),
            },
        )?;

        for (inst_index, target) in cross_block_targets {
            let Some(target_operand) = func.insts[inst_index].operands.last_mut() else {
                return Err(CodegenBackendError::Pipeline {
                    func_name: func.name.clone(),
                    reason: "branch lost its target during AArch64 frame-pointer promotion"
                        .to_string(),
                });
            };
            *target_operand = MachOperand::Block(target);
        }
        let func_name = func.name.clone();
        trust_cg_codegen::pipeline::resolve_branches(func).map_err(|error| {
            CodegenBackendError::Pipeline {
                func_name,
                reason: format!("AArch64 branch re-resolution failed: {error}"),
            }
        })?;
        Ok(())
    }

    fn trust_cg_pipeline(&self) -> trust_cg_codegen::pipeline::Pipeline {
        let opt_level = self.optimization_level.aarch64_pipeline_level();
        trust_cg_codegen::pipeline::Pipeline::new(trust_cg_codegen::pipeline::PipelineConfig {
            opt_level,
            target_triple: self.target_triple.clone(),
            ..Default::default()
        })
    }

    /// Emit a target-correct object while preserving named-call relocations.
    fn emit_target_object(
        &self,
        functions: &[LirFunction],
    ) -> Result<Vec<u8>, CodegenBackendError> {
        // x86-64 has its OWN backend (`trust_cg_codegen::x86_64::X86Pipeline`); the
        // generic pipeline below is AArch64-only and would silently emit AArch64
        // bytes for an x86 target. Route x86 through its real backend.
        if self.target_arch == TrustCgTargetArch::X86_64 {
            return self.emit_x86_object(functions);
        }
        let pipeline = self.trust_cg_pipeline();

        let mut prepared = Vec::with_capacity(functions.len());
        for func in functions {
            let (mut prepared_func, metrics) = pipeline
                .prepare_function_with_metrics(func, None)
                .map_err(|e| CodegenBackendError::Pipeline {
                func_name: func.name.clone(),
                reason: e.to_string(),
            })?;
            let prepared_layout =
                metrics.frame_layout.as_ref().ok_or_else(|| CodegenBackendError::Pipeline {
                    func_name: func.name.clone(),
                    reason: "AArch64 preparation returned no frame layout".to_string(),
                })?;
            self.enforce_aarch64_frame_pointer_policy(&mut prepared_func, prepared_layout)?;
            prepared.push(prepared_func);
        }

        let globals = collect_trust_location_globals(functions);
        pipeline.compile_module_with_globals(&prepared, &globals).map_err(|e| {
            CodegenBackendError::Pipeline {
                func_name: functions
                    .first()
                    .map(|func| func.name.clone())
                    .unwrap_or_else(|| "<empty>".to_string()),
                reason: e.to_string(),
            }
        })
    }

    /// Emit a genuine x86-64 object via the dedicated `X86Pipeline`, mirroring the
    /// compiler's `compile_x86_64` dispatch (per-function x86 ISel -> X86Pipeline).
    /// This is what `emit_target_object` should have called for the `X86_64` target
    /// all along; the generic pipeline is AArch64-only.
    fn emit_x86_object(&self, functions: &[LirFunction]) -> Result<Vec<u8>, CodegenBackendError> {
        use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
        use trust_cg_lower::function::Signature;
        use trust_cg_lower::x86_64_isel::{X86CallAbi, X86InstructionSelector};

        let isel_err = |name: &str, e: String| CodegenBackendError::Pipeline {
            func_name: name.to_string(),
            reason: format!("x86 isel: {e}"),
        };

        let (call_abi, output_format) =
            match audited_object_family(TrustCgTargetArch::X86_64, &self.target_triple)? {
                TargetObjectFamily::Coff => (X86CallAbi::WindowsX64, X86OutputFormat::Coff),
                TargetObjectFamily::MachO => (X86CallAbi::SystemV, X86OutputFormat::MachO),
                TargetObjectFamily::Elf => (X86CallAbi::SystemV, X86OutputFormat::Elf),
            };

        let mut isel_funcs = Vec::with_capacity(functions.len());
        for f in functions {
            let sig = Signature {
                params: f.signature.params.clone(),
                returns: f.signature.returns.clone(),
            };
            let mut isel = X86InstructionSelector::with_abi(f.name.clone(), sig.clone(), call_abi);
            isel.set_stack_slots(f.stack_slots.clone());
            isel.seed_value_types(&f.value_types);
            isel.seed_function_value_use_counts(f);
            let block_order = f.layout_order();
            for b in &block_order {
                isel.ensure_block(*b);
            }
            isel.lower_formal_arguments(&sig, f.entry_block)
                .map_err(|e| isel_err(&f.name, e.to_string()))?;
            for b in &block_order {
                let bb = &f.blocks[b];
                if *b != f.entry_block && !bb.params.is_empty() {
                    isel.define_block_params(&bb.params);
                }
                isel.select_block(*b, &bb.instructions)
                    .map_err(|e| isel_err(&f.name, e.to_string()))?;
            }
            let isel_func = isel.finalize();
            // The bridge performs instruction selection directly rather than
            // entering trust-cg-codegen's high-level compiler pipeline. Run
            // the same fail-closed gate on the exact pre-pass ISel and LIR
            // pair before X86Pipeline can optimize away provenance stamps.
            trust_cg_codegen::compiler::enforce_x86_dataflow_integrity(&isel_func, f).map_err(
                |error| CodegenBackendError::Pipeline {
                    func_name: f.name.clone(),
                    reason: format!("x86 dataflow-integrity gate: {error}"),
                },
            )?;
            isel_funcs.push(isel_func);
        }

        let globals = collect_trust_location_globals(functions);
        let opt_level = self.optimization_level.x86_pipeline_level();
        X86Pipeline::new(X86PipelineConfig {
            opt_level,
            output_format,
            emit_elf: false,
            call_abi,
            ..X86PipelineConfig::generic_x86_64()
        })
        .compile_module_with_globals(&isel_funcs, &globals)
        .map_err(|e| CodegenBackendError::Pipeline {
            func_name: functions
                .first()
                .map(|f| f.name.clone())
                .unwrap_or_else(|| "<empty>".to_string()),
            reason: e.to_string(),
        })
    }

    /// Emit a single target-correct allocator object, preserving cross-wrapper
    /// and external call relocations in one artifact.
    pub fn emit_allocator_module_object(
        &self,
        module: &CompiledModule,
    ) -> Result<Option<EmittedObject>, CodegenBackendError> {
        if module.lir_functions.is_empty() {
            return Err(CodegenBackendError::EmitFailed {
                reason: format!(
                    "allocator module `{}` has no functions; refusing objectless allocator output",
                    module.name
                ),
            });
        }

        let bytes = self.emit_target_object(&module.lir_functions)?;
        Ok(Some(EmittedObject {
            artifact_name: module.name.clone(),
            source_name: module.name.clone(),
            bytes,
        }))
    }

    /// Stable module name used for allocator shim codegen.
    #[must_use]
    pub fn allocator_module_name(crate_name: &str) -> String {
        format!("{crate_name}.allocator")
    }

    /// Lower allocator functions into a dedicated compiled module.
    ///
    /// This is a bridge-side scaffold for future allocator shim plumbing:
    /// callers can lower allocator functions independently of the main crate
    /// CGU and later attach the resulting module to an `OngoingCodegen`.
    pub fn lower_allocator_module(
        &self,
        crate_name: &str,
        functions: &[VerifiableFunction],
    ) -> Result<Option<CompiledModule>, CodegenBackendError> {
        if functions.is_empty() {
            return Ok(None);
        }

        let module_name = Self::allocator_module_name(crate_name);
        let mut lir_functions = Vec::with_capacity(functions.len());
        let mut failures = Vec::new();

        for func in functions {
            match self.lower_function(func) {
                Ok(lir) => lir_functions.push(lir),
                Err(e) => failures.push((func.name.clone(), e.to_string())),
            }
        }

        if !failures.is_empty() {
            let summary = failures
                .iter()
                .map(|(name, err)| format!("  {name}: {err}"))
                .collect::<Vec<_>>()
                .join("\n");
            return Err(CodegenBackendError::CodegenUnitFailed {
                unit_name: module_name,
                reason: format!(
                    "{} allocator function(s) failed to lower:\n{summary}",
                    failures.len()
                ),
            });
        }

        let function_count = lir_functions.len();
        Ok(Some(CompiledModule {
            name: Self::allocator_module_name(crate_name),
            lir_functions,
            object_path: None,
            function_count,
            // Synthesized allocator shim — no source IR to verify.
            source_functions: None,
        }))
    }

    /// Attach a lowered allocator module to an in-flight codegen result.
    ///
    /// Future callers can use this to preserve allocator shims as a distinct
    /// module without changing the regular crate codegen path.
    pub fn attach_allocator_module(
        &self,
        ongoing: &mut dyn Any,
        allocator_module: CompiledModule,
    ) -> Result<(), CodegenBackendError> {
        let ongoing = ongoing.downcast_mut::<OngoingCodegen>().ok_or_else(|| {
            CodegenBackendError::JoinFailed {
                reason: "ongoing codegen has wrong type (not OngoingCodegen)".to_string(),
            }
        })?;
        ongoing.allocator_module = Some(allocator_module);
        Ok(())
    }

    /// Attach allocator shim intent to an in-flight codegen result.
    ///
    /// This lets rustc-side planning hand bridge-native allocator metadata down
    /// so `join_codegen` can synthesize native allocator wrapper LIR later.
    pub fn attach_allocator_module_spec(
        &self,
        ongoing: &mut dyn Any,
        allocator_module_spec: AllocatorModuleSpec,
    ) -> Result<(), CodegenBackendError> {
        let ongoing = ongoing.downcast_mut::<OngoingCodegen>().ok_or_else(|| {
            CodegenBackendError::JoinFailed {
                reason: "ongoing codegen has wrong type (not OngoingCodegen)".to_string(),
            }
        })?;
        ongoing.allocator_module_spec = Some(allocator_module_spec);
        Ok(())
    }

    /// The target architecture this backend is configured for.
    #[must_use]
    pub fn target_arch(&self) -> TrustCgTargetArch {
        self.target_arch
    }

    /// The full target triple used for object format selection.
    #[must_use]
    pub fn target_triple(&self) -> &str {
        &self.target_triple
    }

    /// Whether this backend emits real machine code objects.
    #[must_use]
    pub fn real_machine_code(&self) -> bool {
        true
    }
}

fn sorted_lir_block_ids(func: &LirFunction) -> Vec<Block> {
    // trust-cg's LIR block map is a std HashMap by API. Sort keys before any
    // structural mutation so optimization remains deterministic.
    #[allow(rustc::potential_query_instability)]
    let mut blocks: Vec<_> = func.blocks.keys().copied().collect();
    blocks.sort_by_key(|block| block.0);
    blocks
}

fn collect_trust_location_globals(
    functions: &[LirFunction],
) -> Vec<trust_cg_codegen::pipeline::ObjectGlobal> {
    let mut names = std::collections::BTreeSet::new();

    for func in functions {
        #[allow(rustc::potential_query_instability)]
        for block in func.blocks.values() {
            for inst in &block.instructions {
                if let Opcode::GlobalRef { name } = &inst.opcode
                    && trust_location_file_global_data(name).is_some()
                {
                    names.insert(name.clone());
                }
            }
        }
    }

    names
        .into_iter()
        .filter_map(|name| {
            trust_location_file_global_data(&name).map(|data| {
                trust_cg_codegen::pipeline::ObjectGlobal {
                    name,
                    data,
                    mutable: false,
                    symbol_refs: vec![],
                    // trust-cg added linkage flags; file-global data is a plain internal
                    // definition — not external, not an import, not thread-local, and a
                    // strong (non-weak) definition. Trust: track the trust-cg
                    // `ObjectGlobal.is_weak` field addition so cg-bridge compiles against
                    // the current pin (a plain internal def is never weak-linkage).
                    is_external: false,
                    is_thread_local: false,
                    is_import: false,
                    is_weak: false,
                    // trust-cg's ObjectGlobal gained explicit storage alignment
                    // (Global.align lane). This synthesized global is a raw
                    // byte-string blob (a location-file path); its natural and
                    // sufficient alignment is 1 — there is no trust-ir Global
                    // to derive a stricter alignment from.
                    align: 1,
                }
            })
        })
        .collect()
}

impl Default for TrustCgCodegenBackend {
    fn default() -> Self {
        Self::host()
    }
}

impl RustcCodegenBackend for TrustCgCodegenBackend {
    fn name(&self) -> &'static str {
        "trust-cg"
    }

    fn target_cpu(&self) -> String {
        self.target_arch.cpu_string().to_string()
    }

    fn target_config(&self) -> TargetConfig {
        // Declare the architecture BASELINE features in BOTH lists. rustc's
        // ABI check (`abi_check::do_check_simd_vector_abi::have_feature`) and
        // `check_abi_required_features` consult `sess.unstable_target_features`
        // — NOT `sess.target_features` — so leaving the unstable list empty made
        // every float/vector-passing function warn "target feature `neon` must
        // be enabled ... (issue #116344)" under trust-cg while the LLVM backend
        // (which seeds the baseline into `unstable_target_features`) does not.
        // `unstable_target_features` is the superset of all enabled features; for
        // the stable baseline both lists carry the same names, matching LLVM.
        let baseline: Vec<String> =
            self.target_arch.baseline_target_features().iter().map(|s| s.to_string()).collect();
        let mut unstable_target_features = baseline.clone();
        unstable_target_features.push(
            match self.target_arch {
                TrustCgTargetArch::AArch64 => "fp-armv8",
                TrustCgTargetArch::X86_64 => "x87",
            }
            .to_string(),
        );
        TargetConfig {
            target_features: baseline,
            unstable_target_features,
            // trust_cg does not yet support extended float types.
            has_reliable_f16: false,
            has_reliable_f16_math: false,
            has_reliable_f128: false,
            has_reliable_f128_math: false,
        }
    }

    fn codegen_crate(&self, crate_info: &CrateInfo) -> Result<Box<dyn Any>, CodegenBackendError> {
        let mut modules = Vec::new();
        let mut failures = Vec::new();

        // Group all functions into a single codegen unit for now.
        // Real implementation will partition by CGU name from TyCtxt.
        let mut lir_functions = Vec::with_capacity(crate_info.functions.len());
        // Trust (M-POS): capture the SOURCE VerifiableFunctions in lockstep with
        // successfully-lowered LIR so the proven-output gate can verify them.
        // Index correspondence with `lir_functions` is preserved: a function is
        // pushed here ONLY when its lowering succeeded (failures are skipped on
        // both sides), so `source_functions[i]` produced `lir_functions[i]`.
        let mut source_functions = Vec::with_capacity(crate_info.functions.len());

        for func in &crate_info.functions {
            match self.lower_function(func) {
                Ok(lir) => {
                    source_functions.push(func.clone());
                    lir_functions.push(lir);
                }
                Err(e) => failures.push((func.name.clone(), e.to_string())),
            }
        }

        let function_count = lir_functions.len();
        modules.push(CompiledModule {
            name: format!("{}.codegen_unit.0", crate_info.crate_name),
            lir_functions,
            object_path: None,
            function_count,
            source_functions: Some(source_functions),
        });

        Ok(Box::new(OngoingCodegen {
            modules,
            allocator_module: None,
            allocator_module_spec: None,
            failures,
            crate_name: crate_info.crate_name.clone(),
        }))
    }

    fn join_codegen(
        &self,
        ongoing: Box<dyn Any>,
        _outputs: &OutputFilenames,
    ) -> Result<(CompiledModules, Vec<WorkProduct>), CodegenBackendError> {
        let ongoing =
            ongoing.downcast::<OngoingCodegen>().map_err(|_| CodegenBackendError::JoinFailed {
                reason: "ongoing codegen has wrong type (not OngoingCodegen)".to_string(),
            })?;

        if !ongoing.failures.is_empty() {
            let failure_summary: Vec<String> =
                ongoing.failures.iter().map(|(name, err)| format!("  {name}: {err}")).collect();
            return Err(CodegenBackendError::JoinFailed {
                reason: format!(
                    "{} function(s) failed to compile:\n{}",
                    ongoing.failures.len(),
                    failure_summary.join("\n")
                ),
            });
        }

        let OngoingCodegen {
            modules,
            allocator_module,
            allocator_module_spec,
            failures: _,
            crate_name: _,
        } = *ongoing;

        let allocator_module = match (allocator_module, allocator_module_spec) {
            (Some(module), _) => Some(module),
            (None, Some(spec)) => Some(Self::allocator_module_from_spec(&spec)?),
            (None, None) => None,
        };

        let compiled = CompiledModules { modules, allocator_module };

        // No incremental work products in the scaffold.
        Ok((compiled, Vec::new()))
    }

    fn link(
        &self,
        compiled: &CompiledModules,
        outputs: &OutputFilenames,
    ) -> Result<PathBuf, CodegenBackendError> {
        // Scaffold: report what would be linked but don't produce a real binary.
        // The real implementation will invoke trust_cg-codegen target pipelines.
        let total_functions: usize = compiled.modules.iter().map(|m| m.function_count).sum();

        let output_path = outputs.object_path("o");

        if total_functions == 0 {
            return Err(CodegenBackendError::LinkFailed {
                reason: "no functions to link".to_string(),
            });
        }

        // In the scaffold, we just return the path that would be produced.
        // Real implementation: trust_cg-codegen emits object files, then we link.
        Ok(output_path)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use trust_types::{
        BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    /// Build `add(a: i32, b: i32) -> i32` for testing.
    fn make_add() -> VerifiableFunction {
        VerifiableFunction {
            name: "add".to_string(),
            def_path: "test::add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build `identity(x: i64) -> i64` -- single arg, single block.
    fn make_identity() -> VerifiableFunction {
        VerifiableFunction {
            name: "identity".to_string(),
            def_path: "test::identity".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i64(), name: None },
                    LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i64(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn make_allocator_spec(module_name: &str) -> AllocatorModuleSpec {
        AllocatorModuleSpec {
            module_name: module_name.to_string(),
            functions: vec![
                AllocatorFunctionSpec {
                    name: "alloc".to_string(),
                    wrapper_symbol_name: "_Rshim_alloc".to_string(),
                    callee_symbol_name: "_Rdefault_alloc".to_string(),
                    kind: AllocatorFunctionKind::Alloc,
                    inputs: vec![AllocatorArgKind::Layout],
                    output: AllocatorResultKind::ResultPtr,
                },
                AllocatorFunctionSpec {
                    name: "alloc_error_handler".to_string(),
                    wrapper_symbol_name: "_Rshim_alloc_error_handler".to_string(),
                    callee_symbol_name: "_Rdefault_alloc_error_handler".to_string(),
                    kind: AllocatorFunctionKind::AllocErrorHandler,
                    inputs: vec![AllocatorArgKind::Layout],
                    output: AllocatorResultKind::Never,
                },
            ],
            no_alloc_shim_is_unstable_symbol_name: Some("_Rshim_no_alloc_marker".to_string()),
        }
    }

    fn make_shared_callee_allocator_spec(module_name: &str) -> AllocatorModuleSpec {
        AllocatorModuleSpec {
            module_name: module_name.to_string(),
            functions: vec![
                AllocatorFunctionSpec {
                    name: "alloc".to_string(),
                    wrapper_symbol_name: "_Rshim_alloc".to_string(),
                    callee_symbol_name: "_Rshared_alloc".to_string(),
                    kind: AllocatorFunctionKind::Alloc,
                    inputs: vec![AllocatorArgKind::Layout],
                    output: AllocatorResultKind::ResultPtr,
                },
                AllocatorFunctionSpec {
                    name: "alloc_zeroed".to_string(),
                    wrapper_symbol_name: "_Rshim_alloc_zeroed".to_string(),
                    callee_symbol_name: "_Rshared_alloc".to_string(),
                    kind: AllocatorFunctionKind::AllocZeroed,
                    inputs: vec![AllocatorArgKind::Layout],
                    output: AllocatorResultKind::ResultPtr,
                },
            ],
            no_alloc_shim_is_unstable_symbol_name: Some("_Rshim_no_alloc_marker".to_string()),
        }
    }

    fn make_internal_call_module(module_name: &str) -> CompiledModule {
        let mut caller = LirFunction::new("_Rshim_caller".to_string(), LirSignature::default());
        let mut caller_entry = LirBasicBlock::default();
        caller_entry.instructions.push(LirInstruction {
            opcode: Opcode::Call { name: "_Rshim_callee".to_string() },
            args: vec![],
            results: vec![],
        });
        caller_entry.instructions.push(LirInstruction {
            opcode: Opcode::Return,
            args: vec![],
            results: vec![],
        });
        caller.blocks.insert(Block(0), caller_entry);

        let mut callee = LirFunction::new("_Rshim_callee".to_string(), LirSignature::default());
        let mut callee_entry = LirBasicBlock::default();
        callee_entry.instructions.push(LirInstruction {
            opcode: Opcode::Return,
            args: vec![],
            results: vec![],
        });
        callee.blocks.insert(Block(0), callee_entry);

        CompiledModule {
            name: module_name.to_string(),
            function_count: 2,
            lir_functions: vec![caller, callee],
            object_path: None,
            source_functions: None,
        }
    }

    fn read_u32(bytes: &[u8], offset: usize) -> u32 {
        u32::from_le_bytes(bytes[offset..offset + 4].try_into().expect("u32 should fit"))
    }

    fn read_u64(bytes: &[u8], offset: usize) -> u64 {
        u64::from_le_bytes(bytes[offset..offset + 8].try_into().expect("u64 should fit"))
    }

    fn mach_o_symbols(bytes: &[u8]) -> Vec<(String, trust_cg_codegen::macho::NList64)> {
        const MACH_HEADER_64_SIZE: usize = 32;
        const LC_SYMTAB: u32 = 0x02;
        const NLIST_64_SIZE: usize = 16;

        let ncmds = read_u32(bytes, 16) as usize;
        let mut command_offset = MACH_HEADER_64_SIZE;
        let mut symtab = None;

        for _ in 0..ncmds {
            let cmd = read_u32(bytes, command_offset);
            let cmdsize = read_u32(bytes, command_offset + 4) as usize;
            if cmd == LC_SYMTAB {
                symtab = Some((
                    read_u32(bytes, command_offset + 8) as usize,
                    read_u32(bytes, command_offset + 12) as usize,
                    read_u32(bytes, command_offset + 16) as usize,
                ));
                break;
            }
            command_offset += cmdsize;
        }

        let (symoff, nsyms, stroff) = symtab.expect("Mach-O object should contain LC_SYMTAB");
        (0..nsyms)
            .map(|index| {
                let entry_offset = symoff + index * NLIST_64_SIZE;
                let entry = trust_cg_codegen::macho::NList64::decode(
                    bytes[entry_offset..entry_offset + NLIST_64_SIZE]
                        .try_into()
                        .expect("nlist_64 entry should be 16 bytes"),
                );
                let name_offset = stroff + entry.strx as usize;
                let name_end = bytes[name_offset..]
                    .iter()
                    .position(|&byte| byte == 0)
                    .expect("symbol name should be NUL-terminated")
                    + name_offset;
                let name = std::str::from_utf8(&bytes[name_offset..name_end])
                    .expect("symbol names should be UTF-8")
                    .to_string();
                (name, entry)
            })
            .collect()
    }

    fn mach_o_name(bytes: &[u8]) -> String {
        let end = bytes.iter().position(|&byte| byte == 0).unwrap_or(bytes.len());
        std::str::from_utf8(&bytes[..end]).expect("Mach-O names should be UTF-8").to_string()
    }

    fn mach_o_text_relocations(bytes: &[u8]) -> Vec<trust_cg_codegen::macho::Relocation> {
        const MACH_HEADER_64_SIZE: usize = 32;
        const LC_SEGMENT_64: u32 = 0x19;
        const SEGMENT_COMMAND_64_SIZE: usize = 72;
        const SECTION_64_SIZE: usize = 80;
        const RELOCATION_SIZE: usize = 8;

        let ncmds = read_u32(bytes, 16) as usize;
        let mut command_offset = MACH_HEADER_64_SIZE;

        for _ in 0..ncmds {
            let cmd = read_u32(bytes, command_offset);
            let cmdsize = read_u32(bytes, command_offset + 4) as usize;
            if cmd == LC_SEGMENT_64 {
                let nsects = read_u32(bytes, command_offset + 64) as usize;
                let mut section_offset = command_offset + SEGMENT_COMMAND_64_SIZE;
                for _ in 0..nsects {
                    let sectname = mach_o_name(&bytes[section_offset..section_offset + 16]);
                    let segname = mach_o_name(&bytes[section_offset + 16..section_offset + 32]);
                    if sectname == "__text" && segname == "__TEXT" {
                        let reloff = read_u32(bytes, section_offset + 56) as usize;
                        let nreloc = read_u32(bytes, section_offset + 60) as usize;
                        return (0..nreloc)
                            .map(|index| {
                                let entry_offset = reloff + index * RELOCATION_SIZE;
                                trust_cg_codegen::macho::reloc::decode_relocation(
                                    bytes[entry_offset..entry_offset + RELOCATION_SIZE]
                                        .try_into()
                                        .expect("relocation entry should be 8 bytes"),
                                )
                                .expect("text relocation should decode")
                            })
                            .collect();
                    }
                    section_offset += SECTION_64_SIZE;
                }
            }
            command_offset += cmdsize;
        }

        panic!("Mach-O object should contain a __TEXT,__text section");
    }

    fn mach_o_text(bytes: &[u8]) -> &[u8] {
        const MACH_HEADER_64_SIZE: usize = 32;
        const LC_SEGMENT_64: u32 = 0x19;
        const SEGMENT_COMMAND_64_SIZE: usize = 72;
        const SECTION_64_SIZE: usize = 80;

        let ncmds = read_u32(bytes, 16) as usize;
        let mut command_offset = MACH_HEADER_64_SIZE;
        for _ in 0..ncmds {
            let cmd = read_u32(bytes, command_offset);
            let cmdsize = read_u32(bytes, command_offset + 4) as usize;
            if cmd == LC_SEGMENT_64 {
                let nsects = read_u32(bytes, command_offset + 64) as usize;
                let mut section_offset = command_offset + SEGMENT_COMMAND_64_SIZE;
                for _ in 0..nsects {
                    let sectname = mach_o_name(&bytes[section_offset..section_offset + 16]);
                    let segname = mach_o_name(&bytes[section_offset + 16..section_offset + 32]);
                    if sectname == "__text" && segname == "__TEXT" {
                        let size = read_u64(bytes, section_offset + 40) as usize;
                        let offset = read_u32(bytes, section_offset + 48) as usize;
                        return &bytes[offset..offset + size];
                    }
                    section_offset += SECTION_64_SIZE;
                }
            }
            command_offset += cmdsize;
        }
        panic!("Mach-O object should contain a __TEXT,__text section");
    }

    fn macho_aarch64_backend() -> TrustCgCodegenBackend {
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
    }

    // -- TrustCgCodegenBackend basic tests --

    #[test]
    fn test_backend_name() {
        let backend = TrustCgCodegenBackend::host();
        assert_eq!(backend.name(), "trust-cg");
    }

    #[test]
    fn test_backend_target_cpu() {
        let backend = TrustCgCodegenBackend::new(TrustCgTargetArch::AArch64);
        assert_eq!(backend.target_cpu(), "generic");
    }

    #[test]
    fn test_backend_target_config() {
        let backend = TrustCgCodegenBackend::new(TrustCgTargetArch::AArch64);
        let config = backend.target_config();
        assert!(config.target_features.contains(&"neon".to_string()));
        assert!(!config.has_reliable_f16);
    }

    #[test]
    fn test_backend_target_config_x86() {
        let backend = TrustCgCodegenBackend::new(TrustCgTargetArch::X86_64);
        let config = backend.target_config();
        assert!(config.target_features.contains(&"sse2".to_string()));
    }

    #[test]
    fn test_backend_thin_lto_not_supported() {
        let backend = TrustCgCodegenBackend::host();
        assert!(!backend.thin_lto_supported());
    }

    #[test]
    fn test_backend_default_is_host() {
        let backend = TrustCgCodegenBackend::default();
        assert_eq!(backend.target_arch(), TrustCgTargetArch::host());
    }

    #[test]
    fn test_backend_emits_real_machine_code() {
        let backend = TrustCgCodegenBackend::host();
        assert!(backend.real_machine_code());
    }

    #[test]
    fn test_target_arch_triple() {
        assert_eq!(TrustCgTargetArch::AArch64.triple(), "aarch64-unknown-linux-gnu");
        assert_eq!(TrustCgTargetArch::X86_64.triple(), "x86_64-unknown-linux-gnu");
    }

    #[test]
    fn test_backend_new_for_triple_preserves_target_triple() {
        let backend = TrustCgCodegenBackend::new_for_triple(
            TrustCgTargetArch::AArch64,
            "aarch64-apple-darwin",
        );
        assert_eq!(backend.target_arch(), TrustCgTargetArch::AArch64);
        assert_eq!(backend.target_triple(), "aarch64-apple-darwin");
    }

    fn emit_x86_add_object(target_triple: &str) -> Vec<u8> {
        let backend =
            TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::X86_64, target_triple);
        let lir = backend.lower_function(&make_add()).expect("add should lower to x86 LIR");
        backend
            .emit_target_object(&[lir])
            .unwrap_or_else(|error| panic!("{target_triple} x86 object emission failed: {error}"))
    }

    #[test]
    fn test_x86_aot_emits_real_target_objects_not_raw_code() {
        let elf = emit_x86_add_object("x86_64-unknown-linux-gnu");
        assert_eq!(&elf[..4], b"\x7fELF");

        let macho = emit_x86_add_object("x86_64-apple-darwin");
        assert_eq!(&macho[..4], &[0xcf, 0xfa, 0xed, 0xfe]);

        let coff = emit_x86_add_object("x86_64-pc-windows-msvc");
        assert_eq!(&coff[..2], &[0x64, 0x86]);
    }

    #[test]
    fn test_x86_aot_rejects_unmapped_object_abi_family() {
        let error = TrustCgCodegenBackend::try_new_for_triple(
            TrustCgTargetArch::X86_64,
            "x86_64-unknown-freebsd",
        )
        .expect_err("unsupported x86 target must be refused at construction");
        assert!(error.to_string().contains("not an exact audited"));
    }

    #[test]
    fn target_triple_family_matching_rejects_spoofed_substrings_and_arch_mismatch() {
        for spoof in [
            "x86_64-evil-windowsish",
            "x86_64-apple-darwin-extra",
            "x86_64-unknown-linux-gnu-injected",
        ] {
            assert!(
                TrustCgCodegenBackend::try_new_for_triple(TrustCgTargetArch::X86_64, spoof)
                    .is_err(),
                "spoofed triple must be rejected: {spoof}"
            );
        }
        assert!(
            TrustCgCodegenBackend::try_new_for_triple(
                TrustCgTargetArch::AArch64,
                "x86_64-unknown-linux-gnu",
            )
            .is_err(),
            "the declared architecture and triple architecture must agree"
        );
    }

    #[test]
    fn test_target_arch_from_rustc_arch() {
        assert_eq!(TrustCgTargetArch::from_rustc_arch("aarch64"), Some(TrustCgTargetArch::AArch64));
        assert_eq!(TrustCgTargetArch::from_rustc_arch("x86_64"), Some(TrustCgTargetArch::X86_64));
        assert_eq!(TrustCgTargetArch::from_rustc_arch("riscv64"), None);
    }

    // -- lower_function tests --

    #[test]
    fn test_lower_function_add() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_add();
        let lir = backend.lower_function(&func).expect("should lower add function");
        assert_eq!(lir.name, "add");
        assert_eq!(lir.signature.params.len(), 2);
        assert_eq!(lir.signature.returns.len(), 1);
    }

    #[test]
    fn test_lower_function_identity() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_identity();
        let lir = backend.lower_function(&func).expect("should lower identity function");
        assert_eq!(lir.name, "identity");
        assert_eq!(lir.signature.params.len(), 1);
    }

    // -- RustcCodegenBackend trait tests --

    // Trust (#116344): the ABI check reads `sess.unstable_target_features`, so
    // `target_config` MUST populate the unstable list (not only the stable one)
    // with the arch baseline, or every float/vector-passing function warns
    // "target feature `neon` must be enabled ...".
    #[test]
    fn test_target_config_aarch64_baseline_in_unstable_features() {
        let backend = TrustCgCodegenBackend::new(TrustCgTargetArch::AArch64);
        let cfg = backend.target_config();
        // The feature the aarch64 fixed-vector ABI check looks up literally.
        assert!(
            cfg.unstable_target_features.iter().any(|f| f == "neon"),
            "aarch64 baseline must expose `neon` in unstable_target_features (the list \
             abi_check consults); got {:?}",
            cfg.unstable_target_features
        );
        // Baseline must appear in BOTH lists (unstable is the superset).
        assert!(cfg.target_features.iter().any(|f| f == "neon"));
        assert!(cfg.unstable_target_features.iter().any(|f| f == "fp-armv8"));
        assert!(!cfg.target_features.iter().any(|f| f == "fp-armv8"));
    }

    #[test]
    fn test_target_config_x86_64_baseline_in_unstable_features() {
        let backend = TrustCgCodegenBackend::new(TrustCgTargetArch::X86_64);
        let cfg = backend.target_config();
        // `sse` is what the 128-bit-vector ABI check looks up; `x87`+`sse2` are
        // the abi-required features for the x86_64 default hardfloat ABI.
        for required in ["sse", "sse2", "x87"] {
            assert!(
                cfg.unstable_target_features.iter().any(|f| f == required),
                "x86_64 baseline must expose `{required}` in unstable_target_features; got {:?}",
                cfg.unstable_target_features
            );
        }
        // Backend-internal x87 is an ABI prerequisite, not a source-level cfg
        // capability. Optional SSE3/SSE4.x features stay disabled in the
        // generic emitter and therefore must not be advertised.
        assert!(cfg.unstable_target_features.iter().any(|f| f == "x87"));
        assert!(!cfg.target_features.iter().any(|f| f == "x87"));
        for optional in ["sse3", "ssse3", "sse4.1", "cmpxchg16b"] {
            assert!(!cfg.target_features.iter().any(|feature| feature == optional));
        }
    }

    #[test]
    fn rustc_optimization_levels_map_identically_to_both_target_pipelines() {
        let cases = [
            (
                BridgeOptimizationLevel::O0,
                trust_cg_codegen::pipeline::OptLevel::O0,
                trust_cg_opt::OptLevel::O0,
            ),
            (
                BridgeOptimizationLevel::O1,
                trust_cg_codegen::pipeline::OptLevel::O1,
                trust_cg_opt::OptLevel::O1,
            ),
            (
                BridgeOptimizationLevel::O2,
                trust_cg_codegen::pipeline::OptLevel::O2,
                trust_cg_opt::OptLevel::O2,
            ),
            (
                BridgeOptimizationLevel::O3,
                trust_cg_codegen::pipeline::OptLevel::O3,
                trust_cg_opt::OptLevel::O3,
            ),
        ];
        for (bridge, aarch64, x86) in cases {
            assert_eq!(bridge.aarch64_pipeline_level(), aarch64);
            assert_eq!(bridge.x86_pipeline_level(), x86);
        }
    }

    #[test]
    fn aarch64_always_frame_pointer_policy_promotes_zero_frame_leaf() {
        const STP_FP_LR_PREINDEX: [u8; 4] = [0xfd, 0x7b, 0xbf, 0xa9];
        const MOV_FP_SP: [u8; 4] = [0xfd, 0x03, 0x00, 0x91];
        const LDP_FP_LR_POSTINDEX: [u8; 4] = [0xfd, 0x7b, 0xc1, 0xa8];

        let default_backend = macho_aarch64_backend();
        let lir =
            default_backend.lower_function(&make_identity()).expect("identity should lower to LIR");
        let default_object = default_backend
            .emit_object(std::slice::from_ref(&lir))
            .expect("default AArch64 identity should emit");
        let default_text = mach_o_text(&default_object);
        assert_ne!(
            default_text.get(..4),
            Some(STP_FP_LR_PREINDEX.as_slice()),
            "the baseline policy should retain Trust-CG's eligible zero-frame leaf"
        );

        let forced_backend =
            macho_aarch64_backend().with_frame_pointer_policy(BridgeFramePointerPolicy::Always);
        let forced_object = forced_backend
            .emit_object(std::slice::from_ref(&lir))
            .expect("`always` frame-pointer policy should emit");
        let forced_text = mach_o_text(&forced_object);
        assert_eq!(forced_text.get(..4), Some(STP_FP_LR_PREINDEX.as_slice()));
        assert_eq!(forced_text.get(4..8), Some(MOV_FP_SP.as_slice()));
        assert!(
            forced_text.windows(4).any(|bytes| bytes == LDP_FP_LR_POSTINDEX),
            "forced frame must restore FP/LR before returning"
        );
        assert!(
            forced_text.len() > default_text.len(),
            "forcing a leaf frame must materially change the emitted function"
        );
    }

    #[test]
    fn test_codegen_crate_single_function() {
        let backend = TrustCgCodegenBackend::host();
        let info = CrateInfo { crate_name: "test_crate".to_string(), functions: vec![make_add()] };

        let ongoing = backend.codegen_crate(&info).expect("codegen_crate should succeed");

        // Verify the ongoing codegen can be downcast.
        let ongoing_ref =
            ongoing.downcast_ref::<OngoingCodegen>().expect("should be OngoingCodegen");
        assert_eq!(ongoing_ref.crate_name, "test_crate");
        assert_eq!(ongoing_ref.modules.len(), 1);
        assert_eq!(ongoing_ref.modules[0].function_count, 1);
        assert!(ongoing_ref.failures.is_empty());
    }

    #[test]
    fn test_codegen_crate_multiple_functions() {
        let backend = TrustCgCodegenBackend::host();
        let info = CrateInfo {
            crate_name: "multi".to_string(),
            functions: vec![make_add(), make_identity()],
        };

        let ongoing = backend.codegen_crate(&info).expect("codegen_crate should succeed");

        let ongoing_ref =
            ongoing.downcast_ref::<OngoingCodegen>().expect("should be OngoingCodegen");
        assert_eq!(ongoing_ref.modules[0].function_count, 2);
        assert_eq!(ongoing_ref.modules[0].lir_functions.len(), 2);
    }

    #[test]
    fn test_codegen_crate_empty() {
        let backend = TrustCgCodegenBackend::host();
        let info = CrateInfo { crate_name: "empty".to_string(), functions: vec![] };

        let ongoing = backend.codegen_crate(&info).expect("empty crate should succeed");

        let ongoing_ref =
            ongoing.downcast_ref::<OngoingCodegen>().expect("should be OngoingCodegen");
        assert_eq!(ongoing_ref.modules[0].function_count, 0);
    }

    #[test]
    fn test_join_codegen_success() {
        let backend = TrustCgCodegenBackend::host();
        let info = CrateInfo { crate_name: "test".to_string(), functions: vec![make_add()] };
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "test".to_string() };

        let ongoing = backend.codegen_crate(&info).expect("codegen should succeed");
        let (compiled, work_products) =
            backend.join_codegen(ongoing, &outputs).expect("join should succeed");

        assert_eq!(compiled.modules.len(), 1);
        assert_eq!(compiled.modules[0].function_count, 1);
        assert!(compiled.allocator_module.is_none());
        assert!(work_products.is_empty());
    }

    #[test]
    fn test_emit_module_objects_rejects_empty_regular_module() {
        let backend = TrustCgCodegenBackend::host();
        let module = CompiledModule {
            name: "empty.codegen_unit.0".to_string(),
            lir_functions: vec![],
            object_path: None,
            function_count: 0,
            source_functions: None,
        };

        let err = backend
            .emit_module_objects(&module)
            .expect_err("empty regular module must not become objectless output");
        assert!(matches!(
            err,
            CodegenBackendError::EmitFailed { reason }
                if reason.contains("refusing objectless output")
        ));
    }

    #[test]
    fn test_emit_allocator_module_object_rejects_empty_allocator_module() {
        let backend = TrustCgCodegenBackend::host();
        let module = CompiledModule {
            name: "empty.allocator".to_string(),
            lir_functions: vec![],
            object_path: None,
            function_count: 0,
            source_functions: None,
        };

        let err = backend
            .emit_allocator_module_object(&module)
            .expect_err("empty allocator module must not become objectless output");
        assert!(matches!(
            err,
            CodegenBackendError::EmitFailed { reason }
                if reason.contains("refusing objectless allocator output")
        ));
    }

    #[test]
    fn test_join_codegen_preserves_attached_allocator_module() {
        let backend = TrustCgCodegenBackend::host();
        let info = CrateInfo { crate_name: "test".to_string(), functions: vec![make_add()] };
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "test".to_string() };

        let mut ongoing = backend.codegen_crate(&info).expect("codegen should succeed");
        let allocator_module = backend
            .lower_allocator_module("test", &[make_identity()])
            .expect("allocator lowering should succeed")
            .expect("allocator module should be produced");
        let allocator_module_name = TrustCgCodegenBackend::allocator_module_name("test");

        backend
            .attach_allocator_module(ongoing.as_mut(), allocator_module)
            .expect("attach_allocator_module should accept OngoingCodegen");

        let ongoing_ref = ongoing.downcast_ref::<OngoingCodegen>().expect("should downcast");
        assert_eq!(ongoing_ref.compiled_count(), 2);
        assert_eq!(
            ongoing_ref.allocator_module().expect("allocator module should be attached").name,
            allocator_module_name
        );

        let (compiled, work_products) =
            backend.join_codegen(ongoing, &outputs).expect("join should succeed");

        let allocator_module =
            compiled.allocator_module.as_ref().expect("join should preserve allocator module");
        assert_eq!(allocator_module.name, allocator_module_name);
        assert_eq!(allocator_module.function_count, 1);
        assert!(work_products.is_empty());

        let emitted = backend
            .emit_module_objects(allocator_module)
            .expect("attached allocator module should emit object artifacts");
        assert_eq!(emitted.len(), 1);
        assert_eq!(emitted[0].artifact_name, allocator_module_name);
    }

    #[test]
    fn test_allocator_module_from_spec_builds_wrapper_lir_and_marker() {
        let module = TrustCgCodegenBackend::allocator_module_from_spec(&make_allocator_spec(
            "test.allocator",
        ))
        .expect("allocator spec lowering should succeed");

        assert_eq!(module.name, "test.allocator");
        assert_eq!(module.function_count, 3);
        assert_eq!(module.lir_functions.len(), 3);

        let alloc = &module.lir_functions[0];
        assert_eq!(alloc.name, "_Rshim_alloc");
        assert_eq!(alloc.signature.params, vec![LirType::I64, LirType::I64]);
        assert_eq!(alloc.signature.returns, vec![LirType::I64]);
        assert_eq!(alloc.value_types.get(&Value(2)), Some(&LirType::I64));
        let alloc_entry = alloc.blocks.get(&Block(0)).expect("wrapper should have an entry block");
        assert_eq!(alloc_entry.instructions.len(), 2);
        assert_eq!(
            alloc_entry.instructions[0],
            LirInstruction {
                opcode: Opcode::Call { name: "_Rdefault_alloc".to_string() },
                args: vec![Value(0), Value(1)],
                results: vec![Value(2)],
            }
        );
        assert_eq!(
            alloc_entry.instructions[1],
            LirInstruction { opcode: Opcode::Return, args: vec![Value(2)], results: vec![] }
        );

        let oom = &module.lir_functions[1];
        assert_eq!(oom.name, "_Rshim_alloc_error_handler");
        assert!(oom.signature.returns.is_empty());
        let oom_entry = oom.blocks.get(&Block(0)).expect("noreturn wrapper should have an entry");
        assert_eq!(oom_entry.instructions.len(), 1);
        assert_eq!(
            oom_entry.instructions[0],
            LirInstruction {
                opcode: Opcode::Call { name: "_Rdefault_alloc_error_handler".to_string() },
                args: vec![Value(0), Value(1)],
                results: vec![],
            }
        );

        let marker = &module.lir_functions[2];
        assert_eq!(marker.name, "_Rshim_no_alloc_marker");
        assert_eq!(marker.signature.params, Vec::<LirType>::new());
        assert_eq!(marker.signature.returns, Vec::<LirType>::new());
        let marker_entry =
            marker.blocks.get(&Block(0)).expect("marker function should have an entry");
        assert_eq!(
            marker_entry.instructions,
            vec![LirInstruction { opcode: Opcode::Return, args: vec![], results: vec![] }]
        );
    }

    #[test]
    fn test_emit_allocator_module_object_produces_target_object() {
        let backend = TrustCgCodegenBackend::host();
        let module = TrustCgCodegenBackend::allocator_module_from_spec(&make_allocator_spec(
            "test.allocator",
        ))
        .expect("allocator spec lowering should succeed");

        let emitted = backend
            .emit_allocator_module_object(&module)
            .expect("allocator emission should succeed")
            .expect("allocator module should produce one object");

        assert_eq!(emitted.artifact_name, "test.allocator");
        assert_eq!(emitted.source_name, "test.allocator");
        assert!(!emitted.bytes.is_empty());
        assert_object_magic(&emitted.bytes);
    }

    #[test]
    fn test_emit_allocator_module_object_keeps_allocator_wrappers_in_one_macho_artifact() {
        let backend = macho_aarch64_backend();
        let module = TrustCgCodegenBackend::allocator_module_from_spec(&make_allocator_spec(
            "test.allocator",
        ))
        .expect("allocator spec lowering should succeed");

        let emitted = backend
            .emit_allocator_module_object(&module)
            .expect("allocator emission should succeed")
            .expect("allocator module should produce one object");

        assert_eq!(emitted.artifact_name, "test.allocator");
        assert_eq!(emitted.source_name, "test.allocator");
        assert!(!emitted.bytes.is_empty());

        let symbols = mach_o_symbols(&emitted.bytes);
        let branch26_relocations = mach_o_text_relocations(&emitted.bytes)
            .into_iter()
            .filter_map(|reloc| {
                matches!(reloc.kind, trust_cg_codegen::macho::AArch64RelocKind::Branch26)
                    .then_some((reloc.pc_relative, reloc.is_extern))
            })
            .collect::<Vec<_>>();
        let defined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_defined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        let undefined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_undefined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();

        assert_eq!(
            defined,
            BTreeSet::from([
                "__Rshim_alloc".to_string(),
                "__Rshim_alloc_error_handler".to_string(),
                "__Rshim_no_alloc_marker".to_string(),
            ])
        );
        assert_eq!(
            undefined,
            BTreeSet::from([
                "__Rdefault_alloc".to_string(),
                "__Rdefault_alloc_error_handler".to_string(),
            ])
        );
        assert_eq!(branch26_relocations, vec![(true, true), (true, true)]);
    }

    #[test]
    fn test_emit_allocator_module_object_deduplicates_shared_external_callee_symbol() {
        let backend = macho_aarch64_backend();
        let module = TrustCgCodegenBackend::allocator_module_from_spec(
            &make_shared_callee_allocator_spec("test.shared_allocator"),
        )
        .expect("allocator spec lowering should succeed");

        let emitted = backend
            .emit_allocator_module_object(&module)
            .expect("allocator emission should succeed")
            .expect("allocator module should produce one object");

        assert_eq!(emitted.artifact_name, "test.shared_allocator");
        assert_eq!(emitted.source_name, "test.shared_allocator");

        let symbols = mach_o_symbols(&emitted.bytes);
        let branch26_relocations = mach_o_text_relocations(&emitted.bytes)
            .into_iter()
            .filter_map(|reloc| {
                matches!(reloc.kind, trust_cg_codegen::macho::AArch64RelocKind::Branch26)
                    .then_some(reloc)
            })
            .collect::<Vec<_>>();
        let defined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_defined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        let undefined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_undefined())
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();

        assert_eq!(
            defined,
            BTreeSet::from([
                "__Rshim_alloc".to_string(),
                "__Rshim_alloc_zeroed".to_string(),
                "__Rshim_no_alloc_marker".to_string(),
            ])
        );
        assert_eq!(undefined, vec!["__Rshared_alloc".to_string()]);
        let branch26_symbol_indices = branch26_relocations
            .iter()
            .map(|reloc| {
                assert!(reloc.pc_relative);
                assert!(reloc.is_extern);
                reloc.symbol_index as usize
            })
            .collect::<Vec<_>>();
        assert_eq!(branch26_symbol_indices.len(), 2);

        let unique_branch26_symbol_indices =
            branch26_symbol_indices.iter().copied().collect::<BTreeSet<_>>();
        assert_eq!(unique_branch26_symbol_indices.len(), 1);

        let branch26_symbol_names = unique_branch26_symbol_indices
            .into_iter()
            .map(|index| {
                symbols
                    .get(index)
                    .map(|(name, _)| name.clone())
                    .expect("branch relocation symbol index should resolve in the symtab")
            })
            .collect::<Vec<_>>();
        assert_eq!(branch26_symbol_names, vec!["__Rshared_alloc".to_string()]);
    }

    #[test]
    fn test_emit_allocator_module_object_preserves_defined_internal_call_relocation() {
        let backend = macho_aarch64_backend();
        let module = make_internal_call_module("test.internal_allocator");

        let emitted = backend
            .emit_allocator_module_object(&module)
            .expect("allocator emission should succeed")
            .expect("internal-call module should produce one object");

        assert_eq!(emitted.artifact_name, "test.internal_allocator");
        assert_eq!(emitted.source_name, "test.internal_allocator");

        let symbols = mach_o_symbols(&emitted.bytes);
        let branch26_relocations = mach_o_text_relocations(&emitted.bytes)
            .into_iter()
            .filter_map(|reloc| {
                matches!(reloc.kind, trust_cg_codegen::macho::AArch64RelocKind::Branch26)
                    .then_some(reloc)
            })
            .collect::<Vec<_>>();
        let defined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_defined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        let undefined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_undefined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();

        assert_eq!(
            defined,
            BTreeSet::from(["__Rshim_callee".to_string(), "__Rshim_caller".to_string(),])
        );
        assert!(undefined.is_empty());
        assert_eq!(branch26_relocations.len(), 1);
        assert!(branch26_relocations[0].pc_relative);
        assert!(branch26_relocations[0].is_extern);
        assert_eq!(
            symbols
                .get(branch26_relocations[0].symbol_index as usize)
                .map(|(name, _)| name.clone()),
            Some("__Rshim_callee".to_string())
        );
    }

    #[test]
    fn test_emit_object_preserves_undefined_external_call_symbol() {
        let backend = macho_aarch64_backend();
        let module = TrustCgCodegenBackend::allocator_module_from_spec(&make_allocator_spec(
            "test.allocator",
        ))
        .expect("allocator spec lowering should succeed");
        let wrapper = module.lir_functions[0].clone();

        let emitted = backend.emit_object(&[wrapper]).expect("single wrapper object should emit");
        let symbols = mach_o_symbols(&emitted);
        let defined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_defined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        let undefined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_undefined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();

        assert_eq!(defined, BTreeSet::from(["__Rshim_alloc".to_string()]));
        assert_eq!(undefined, BTreeSet::from(["__Rdefault_alloc".to_string()]));
    }

    #[test]
    fn test_emit_module_objects_single_function_preserves_undefined_external_call_symbol() {
        let backend = macho_aarch64_backend();
        let module = TrustCgCodegenBackend::allocator_module_from_spec(&make_allocator_spec(
            "test.allocator",
        ))
        .expect("allocator spec lowering should succeed");
        let wrapper = module.lir_functions[0].clone();
        let compiled_module = CompiledModule {
            name: "single_wrapper.codegen_unit.0".to_string(),
            lir_functions: vec![wrapper],
            object_path: None,
            function_count: 1,
            source_functions: None,
        };

        let emitted = backend
            .emit_module_objects(&compiled_module)
            .expect("single wrapper module should emit")
            .into_iter()
            .next()
            .expect("single wrapper module should emit one object");

        assert_eq!(emitted.artifact_name, "single_wrapper.codegen_unit.0");
        assert_eq!(emitted.source_name, "_Rshim_alloc");

        let symbols = mach_o_symbols(&emitted.bytes);
        let branch26_relocations = mach_o_text_relocations(&emitted.bytes)
            .into_iter()
            .filter_map(|reloc| {
                matches!(reloc.kind, trust_cg_codegen::macho::AArch64RelocKind::Branch26)
                    .then_some((reloc.pc_relative, reloc.is_extern))
            })
            .collect::<Vec<_>>();
        let undefined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_undefined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        assert_eq!(branch26_relocations, vec![(true, true)]);
        assert_eq!(undefined, BTreeSet::from(["__Rdefault_alloc".to_string()]));
    }

    #[test]
    fn test_join_codegen_preserves_attached_allocator_module_spec() {
        let backend = TrustCgCodegenBackend::host();
        let info = CrateInfo { crate_name: "test".to_string(), functions: vec![make_add()] };
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "test".to_string() };
        let mut ongoing = backend.codegen_crate(&info).expect("codegen should succeed");
        let allocator_module_name = TrustCgCodegenBackend::allocator_module_name("test");

        backend
            .attach_allocator_module_spec(
                ongoing.as_mut(),
                make_allocator_spec(&allocator_module_name),
            )
            .expect("attach_allocator_module_spec should accept OngoingCodegen");

        let ongoing_ref = ongoing.downcast_ref::<OngoingCodegen>().expect("should downcast");
        assert_eq!(
            ongoing_ref
                .allocator_module_spec()
                .expect("allocator module spec should be attached")
                .module_name,
            allocator_module_name
        );

        let (compiled, work_products) =
            backend.join_codegen(ongoing, &outputs).expect("join should succeed");
        let allocator_module =
            compiled.allocator_module.as_ref().expect("join should preserve allocator module");

        assert_eq!(allocator_module.name, allocator_module_name);
        assert_eq!(allocator_module.function_count, 3);
        assert_eq!(allocator_module.lir_functions.len(), 3);
        assert!(work_products.is_empty());

        let emitted = backend
            .emit_allocator_module_object(allocator_module)
            .expect("spec-backed allocator module should emit")
            .expect("spec-backed allocator module should produce one object");
        assert_eq!(emitted.artifact_name, allocator_module_name);
        assert!(!emitted.bytes.is_empty());
    }

    #[test]
    fn test_join_codegen_wrong_type_fails() {
        let backend = TrustCgCodegenBackend::host();
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "test".to_string() };

        // Pass a wrong type to join_codegen.
        let wrong: Box<dyn Any> = Box::new(42_u32);
        let err = backend.join_codegen(wrong, &outputs).unwrap_err();
        assert!(matches!(err, CodegenBackendError::JoinFailed { .. }));
    }

    #[test]
    fn test_full_pipeline_codegen_join_link() {
        let backend = TrustCgCodegenBackend::host();
        let info = CrateInfo {
            crate_name: "pipeline_test".to_string(),
            functions: vec![make_add(), make_identity()],
        };
        let outputs = OutputFilenames {
            out_dir: PathBuf::from("/tmp"),
            crate_stem: "pipeline_test".to_string(),
        };

        // Step 1: codegen_crate
        let ongoing = backend.codegen_crate(&info).expect("codegen should succeed");

        // Step 2: join_codegen
        let (compiled, _) = backend.join_codegen(ongoing, &outputs).expect("join should succeed");

        // Step 3: link
        let output_path = backend.link(&compiled, &outputs).expect("link should succeed");
        assert_eq!(output_path, PathBuf::from("/tmp/pipeline_test.o"));
    }

    #[test]
    fn test_link_empty_crate_fails() {
        let backend = TrustCgCodegenBackend::host();
        let compiled = CompiledModules {
            modules: vec![CompiledModule {
                name: "empty".to_string(),
                lir_functions: vec![],
                object_path: None,
                function_count: 0,
                source_functions: None,
            }],
            allocator_module: None,
        };
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "empty".to_string() };

        let err = backend.link(&compiled, &outputs).unwrap_err();
        assert!(matches!(err, CodegenBackendError::LinkFailed { .. }));
    }

    #[test]
    fn test_output_filenames_object_path() {
        let outputs = OutputFilenames {
            out_dir: PathBuf::from("/build/out"),
            crate_stem: "my_crate".to_string(),
        };
        assert_eq!(outputs.object_path("o"), PathBuf::from("/build/out/my_crate.o"));
        assert_eq!(outputs.object_path("rlib"), PathBuf::from("/build/out/my_crate.rlib"));
    }

    #[test]
    fn test_supported_crate_types() {
        let backend = TrustCgCodegenBackend::host();
        let types = backend.supported_crate_types();
        assert!(types.contains(&"bin"));
        assert!(types.contains(&"rlib"));
        assert!(types.contains(&"staticlib"));
    }

    #[test]
    fn test_init_succeeds() {
        let backend = TrustCgCodegenBackend::host();
        backend.init().expect("init should succeed");
    }

    // -- Verify LIR output structure through the backend --

    #[test]
    fn test_codegen_produces_valid_lir_blocks() {
        let backend = TrustCgCodegenBackend::host();
        let info = CrateInfo { crate_name: "lir_check".to_string(), functions: vec![make_add()] };

        let ongoing = backend.codegen_crate(&info).expect("codegen should succeed");
        let ongoing_ref = ongoing.downcast_ref::<OngoingCodegen>().expect("downcast");

        let lir = &ongoing_ref.modules[0].lir_functions[0];
        assert_eq!(lir.name, "add");
        // The entry block should have instructions (Iadd at minimum).
        let entry = &lir.blocks[&lir.entry_block];
        assert!(!entry.instructions.is_empty(), "entry block should have instructions");
    }

    // -- lower_module tests --

    #[test]
    fn test_lower_module_single_function() {
        let backend = TrustCgCodegenBackend::host();
        let funcs = vec![make_add()];
        let lir_fns =
            backend.lower_module(&funcs).expect("lower_module should succeed for single function");
        assert_eq!(lir_fns.len(), 1);
        assert_eq!(lir_fns[0].name, "add");
    }

    #[test]
    fn test_lower_module_multiple_functions() {
        let backend = TrustCgCodegenBackend::host();
        let funcs = vec![make_add(), make_identity()];
        let lir_fns = backend
            .lower_module(&funcs)
            .expect("lower_module should succeed for multiple functions");
        assert_eq!(lir_fns.len(), 2);
        assert_eq!(lir_fns[0].name, "add");
        assert_eq!(lir_fns[1].name, "identity");
    }

    #[test]
    fn test_lower_module_empty() {
        let backend = TrustCgCodegenBackend::host();
        let lir_fns =
            backend.lower_module(&[]).expect("lower_module should succeed for empty slice");
        assert!(lir_fns.is_empty());
    }

    // -- optimize tests --

    #[test]
    fn test_optimize_preserves_reachable_blocks() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_add();
        let mut lir = backend.lower_function(&func).expect("should lower add function");
        let blocks_before = lir.blocks.len();

        backend.optimize(&mut lir).expect("optimize should succeed");

        // All blocks in a simple add function are reachable from entry.
        assert_eq!(lir.blocks.len(), blocks_before);
        assert!(lir.blocks.contains_key(&lir.entry_block));
    }

    #[test]
    fn test_optimize_removes_unreachable_block() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_add();
        let mut lir = backend.lower_function(&func).expect("should lower add function");

        // Inject an unreachable block.
        use trust_cg_lower::function::BasicBlock as LirBlock;
        let dead_block = Block(999);
        lir.blocks.insert(dead_block, LirBlock::default());
        let blocks_before = lir.blocks.len();

        backend.optimize(&mut lir).expect("optimize should succeed");

        // The dead block should be removed.
        assert_eq!(lir.blocks.len(), blocks_before - 1);
        assert!(!lir.blocks.contains_key(&dead_block));
        assert!(lir.blocks.contains_key(&lir.entry_block));
    }

    #[test]
    fn test_optimize_identity_function() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_identity();
        let mut lir = backend.lower_function(&func).expect("should lower identity function");

        backend.optimize(&mut lir).expect("optimize should succeed on identity function");

        // Entry block should still exist with instructions.
        let entry = &lir.blocks[&lir.entry_block];
        assert!(!entry.instructions.is_empty());
    }

    fn assert_object_magic(bytes: &[u8]) {
        assert!(bytes.len() >= 4, "object must be at least 4 bytes");
        let magic = &bytes[..4];
        let is_macho = magic == [0xCF, 0xFA, 0xED, 0xFE];
        let is_elf = magic == [0x7F, b'E', b'L', b'F'];
        assert!(is_macho || is_elf, "expected Mach-O or ELF magic, got {magic:02X?}",);
    }

    fn assert_elf_magic(bytes: &[u8]) {
        assert!(bytes.starts_with(&[0x7F, b'E', b'L', b'F']), "expected ELF magic");
    }

    // -- emit_object tests --

    #[test]
    fn test_emit_object_single_function_produces_target_object() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_add();
        let lir = backend.lower_function(&func).expect("should lower add function");

        let bytes = backend.emit_object(&[lir]).expect("emit_object should succeed");
        assert!(!bytes.is_empty());
        assert!(bytes.len() > 32, "object should have a real header/body");
        assert_object_magic(&bytes);
    }

    #[test]
    fn test_emit_object_uses_explicit_linux_target_triple_for_elf() {
        let backend = TrustCgCodegenBackend::new_for_triple(
            TrustCgTargetArch::AArch64,
            "aarch64-unknown-linux-gnu",
        );
        let func = make_add();
        let lir = backend.lower_function(&func).expect("should lower add function");

        let bytes = backend.emit_object(&[lir]).expect("emit_object should succeed");
        assert_elf_magic(&bytes);
    }

    #[test]
    fn test_emit_object_multi_function_rejected() {
        let backend = TrustCgCodegenBackend::host();
        let funcs = vec![make_add(), make_identity()];
        let lir_fns = backend.lower_module(&funcs).expect("lower_module should succeed");

        let err = backend.emit_object(&lir_fns).unwrap_err();
        assert!(matches!(err, CodegenBackendError::EmitFailed { .. }));
    }

    #[test]
    fn test_emit_object_empty_module_fails() {
        let backend = TrustCgCodegenBackend::host();
        let err = backend.emit_object(&[]).unwrap_err();
        assert!(matches!(err, CodegenBackendError::EmitFailed { .. }));
    }

    #[test]
    fn test_emit_objects_multi_function() {
        let backend = TrustCgCodegenBackend::host();
        let funcs = vec![make_add(), make_identity()];
        let lir_fns = backend.lower_module(&funcs).expect("lower_module should succeed");

        let objects = backend.emit_objects(&lir_fns).expect("emit_objects should succeed");
        assert_eq!(objects.len(), 2);
        assert_eq!(objects[0].0, "add");
        assert!(!objects[0].1.is_empty());
        assert_eq!(objects[1].0, "identity");
        assert!(!objects[1].1.is_empty());
    }

    #[test]
    fn test_emit_module_objects_multi_function_splits_module() {
        let backend = TrustCgCodegenBackend::host();
        let funcs = vec![make_add(), make_identity()];
        let lir_functions = backend.lower_module(&funcs).expect("lower_module should succeed");
        let module = CompiledModule {
            name: "multi.codegen_unit.0".to_string(),
            lir_functions,
            object_path: None,
            function_count: 2,
            source_functions: None,
        };

        let objects =
            backend.emit_module_objects(&module).expect("emit_module_objects should succeed");
        assert_eq!(objects.len(), 2);
        assert_eq!(objects[0].artifact_name, "multi.codegen_unit.0.f0");
        assert_eq!(objects[0].source_name, "add");
        assert_object_magic(&objects[0].bytes);
        assert_eq!(objects[1].artifact_name, "multi.codegen_unit.0.f1");
        assert_eq!(objects[1].source_name, "identity");
        assert_object_magic(&objects[1].bytes);
    }

    // -- Many-block function tests --

    /// Build a linear chain of `n` basic blocks: bb0 -> bb1 -> ... -> bb(n-1) Return.
    /// Each block assigns to a temp, then gotos next.
    fn make_chain_function(n: usize) -> VerifiableFunction {
        assert!(n >= 1, "need at least 1 block");
        let mut locals = vec![
            LocalDecl { index: 0, ty: Ty::i64(), name: None }, // return
            LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) }, // arg
        ];
        // Temps for intermediate results: locals[2..2+n-1]
        for i in 0..n {
            locals.push(LocalDecl { index: 2 + i, ty: Ty::i64(), name: None });
        }

        let mut blocks = Vec::with_capacity(n);
        for i in 0..n {
            let stmt = Statement::Assign {
                place: Place::local(2 + i),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            };
            let terminator = if i == n - 1 {
                // Last block: assign return and return.
                Terminator::Return
            } else {
                Terminator::Goto(BlockId(i + 1))
            };
            blocks.push(BasicBlock { id: BlockId(i), stmts: vec![stmt], terminator });
        }

        // Override last block to assign to return local.
        if let Some(last) = blocks.last_mut() {
            last.stmts = vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            }];
        }

        VerifiableFunction {
            name: format!("chain_{n}"),
            def_path: format!("test::chain_{n}"),
            span: SourceSpan::default(),
            body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: Ty::i64() },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_lower_module_many_blocks_10() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_chain_function(10);
        let lir_fns =
            backend.lower_module(&[func]).expect("lower_module should succeed for 10-block chain");
        assert_eq!(lir_fns.len(), 1);
        // Should have at least 10 blocks (may have an extra panic block).
        assert!(
            lir_fns[0].blocks.len() >= 10,
            "expected >= 10 blocks, got {}",
            lir_fns[0].blocks.len()
        );
    }

    #[test]
    fn test_lower_module_many_blocks_20() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_chain_function(20);
        let lir_fns =
            backend.lower_module(&[func]).expect("lower_module should succeed for 20-block chain");
        assert_eq!(lir_fns.len(), 1);
        assert!(
            lir_fns[0].blocks.len() >= 20,
            "expected >= 20 blocks, got {}",
            lir_fns[0].blocks.len()
        );
    }

    #[test]
    fn test_optimize_many_blocks_all_reachable() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_chain_function(15);
        let mut lir = backend.lower_function(&func).expect("should lower 15-block chain");
        let blocks_before = lir.blocks.len();

        backend.optimize(&mut lir).expect("optimize should succeed on 15-block chain");

        // All blocks in a linear chain are reachable, so none removed.
        assert_eq!(lir.blocks.len(), blocks_before);
    }

    #[test]
    fn test_optimize_removes_multiple_dead_blocks() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_add();
        let mut lir = backend.lower_function(&func).expect("should lower add function");

        // Inject 5 unreachable blocks.
        use trust_cg_lower::function::BasicBlock as LirBlock;
        for i in 900..905 {
            lir.blocks.insert(Block(i), LirBlock::default());
        }
        let blocks_before = lir.blocks.len();

        backend.optimize(&mut lir).expect("optimize should succeed");

        assert_eq!(lir.blocks.len(), blocks_before - 5, "should remove exactly 5 dead blocks");
        for i in 900..905 {
            assert!(!lir.blocks.contains_key(&Block(i)));
        }
    }

    // -- Complex control flow: nested SwitchInt --

    /// Build a function with a multi-way SwitchInt (simulating a match on i32).
    /// match x { 0 => bb1, 1 => bb2, 2 => bb3, _ => bb4 }
    /// Each arm block returns.
    fn make_switch_function() -> VerifiableFunction {
        let locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
        ];
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(1)),
                    targets: vec![(0, BlockId(1)), (1, BlockId(2)), (2, BlockId(3))],
                    otherwise: BlockId(4),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(30))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ];

        VerifiableFunction {
            name: "switch_fn".to_string(),
            def_path: "test::switch_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: Ty::i32() },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_lower_switch_multi_way() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_switch_function();
        let lir = backend.lower_function(&func).expect("should lower switch function");

        // Should have at least 5 blocks (bb0-bb4, possibly a panic block).
        assert!(lir.blocks.len() >= 5, "expected >= 5 blocks, got {}", lir.blocks.len());

        // Entry block should contain a Switch opcode (3 targets = multi-way).
        let entry = &lir.blocks[&lir.entry_block];
        let has_switch =
            entry.instructions.iter().any(|i| matches!(i.opcode, Opcode::Switch { .. }));
        assert!(has_switch, "entry block should have a Switch opcode for multi-way SwitchInt");
    }

    #[test]
    fn test_optimize_switch_preserves_all_arms() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_switch_function();
        let mut lir = backend.lower_function(&func).expect("should lower switch function");
        let blocks_before = lir.blocks.len();

        backend.optimize(&mut lir).expect("optimize should succeed");

        // All arms are reachable via the switch, so no blocks removed.
        assert_eq!(lir.blocks.len(), blocks_before);
    }

    // -- Nested SwitchInt + loop-like structure --

    /// Build a function with a back-edge (loop-like):
    /// bb0: if x == 0 goto bb2 else bb1
    /// bb1: x = x - 1; goto bb0   (back-edge)
    /// bb2: return x
    fn make_loop_function() -> VerifiableFunction {
        let locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
        ];
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(1)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(1)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(0)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ];

        VerifiableFunction {
            name: "loop_fn".to_string(),
            def_path: "test::loop_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: Ty::i32() },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_lower_loop_function() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_loop_function();
        let lir = backend.lower_function(&func).expect("should lower loop function");

        assert!(
            lir.blocks.len() >= 3,
            "expected >= 3 blocks for loop function, got {}",
            lir.blocks.len()
        );
    }

    #[test]
    fn aarch64_always_frame_pointer_policy_reresolves_cross_block_branches() {
        const STP_FP_LR_PREINDEX: [u8; 4] = [0xfd, 0x7b, 0xbf, 0xa9];

        let backend =
            macho_aarch64_backend().with_frame_pointer_policy(BridgeFramePointerPolicy::Always);
        let lir = backend.lower_function(&make_loop_function()).expect("loop should lower to LIR");
        let object = backend
            .emit_object(&[lir])
            .expect("forcing a frame must retain valid cross-block branch offsets");
        assert_eq!(
            mach_o_text(&object).get(..4),
            Some(STP_FP_LR_PREINDEX.as_slice()),
            "the multi-block leaf must receive the requested frame"
        );
    }

    #[test]
    fn test_optimize_loop_preserves_back_edge() {
        let backend = TrustCgCodegenBackend::host();
        let func = make_loop_function();
        let mut lir = backend.lower_function(&func).expect("should lower loop function");

        // Add a dead block that is NOT part of the loop.
        use trust_cg_lower::function::BasicBlock as LirBlock;
        lir.blocks.insert(Block(888), LirBlock::default());

        backend.optimize(&mut lir).expect("optimize should succeed");

        // Dead block removed, but loop blocks (with back-edge) preserved.
        assert!(!lir.blocks.contains_key(&Block(888)));
        assert!(lir.blocks.len() >= 3, "loop blocks should be preserved after optimize");
    }

    // -- Error case tests --

    #[test]
    fn test_codegen_backend_error_display() {
        let e = CodegenBackendError::Unavailable { reason: "not initialized".to_string() };
        assert_eq!(e.to_string(), "backend unavailable: not initialized");

        let e = CodegenBackendError::CodegenUnitFailed {
            unit_name: "foo".to_string(),
            reason: "bad type".to_string(),
        };
        assert_eq!(e.to_string(), "codegen unit `foo` failed: bad type");

        let e = CodegenBackendError::OptimizationFailed {
            func_name: "bar".to_string(),
            reason: "loop detected".to_string(),
        };
        assert_eq!(e.to_string(), "optimization failed on `bar`: loop detected");

        let e = CodegenBackendError::EmitFailed { reason: "no functions".to_string() };
        assert_eq!(e.to_string(), "emit_object failed: no functions");

        let e = CodegenBackendError::Pipeline {
            func_name: "baz".to_string(),
            reason: "bad instruction".to_string(),
        };
        assert_eq!(e.to_string(), "trust_cg pipeline failed for `baz`: bad instruction");

        let e = CodegenBackendError::JoinFailed { reason: "wrong type".to_string() };
        assert_eq!(e.to_string(), "join failed: wrong type");

        let e = CodegenBackendError::LinkFailed { reason: "missing symbols".to_string() };
        assert_eq!(e.to_string(), "link failed: missing symbols");
    }

    #[test]
    fn test_ongoing_codegen_accessors() {
        let ongoing = OngoingCodegen {
            modules: vec![
                CompiledModule {
                    name: "m1".to_string(),
                    lir_functions: vec![],
                    object_path: None,
                    function_count: 3,
                    source_functions: None,
                },
                CompiledModule {
                    name: "m2".to_string(),
                    lir_functions: vec![],
                    object_path: None,
                    function_count: 2,
                    source_functions: None,
                },
            ],
            allocator_module: Some(CompiledModule {
                name: "alloc".to_string(),
                lir_functions: vec![],
                object_path: None,
                function_count: 1,
                source_functions: None,
            }),
            allocator_module_spec: Some(AllocatorModuleSpec {
                module_name: "alloc.spec".to_string(),
                functions: vec![AllocatorFunctionSpec {
                    name: "alloc".to_string(),
                    wrapper_symbol_name: "_Rshim_alloc".to_string(),
                    callee_symbol_name: "_Rdefault_alloc".to_string(),
                    kind: AllocatorFunctionKind::Alloc,
                    inputs: vec![AllocatorArgKind::Layout],
                    output: AllocatorResultKind::ResultPtr,
                }],
                no_alloc_shim_is_unstable_symbol_name: Some("_Rshim_no_alloc_marker".to_string()),
            }),
            failures: vec![("bad_fn".to_string(), "type error".to_string())],
            crate_name: "my_crate".to_string(),
        };

        assert_eq!(ongoing.crate_name(), "my_crate");
        assert_eq!(ongoing.compiled_count(), 6);
        assert_eq!(ongoing.failure_count(), 1);
        assert_eq!(
            ongoing.allocator_module().expect("allocator module should exist").name,
            "alloc"
        );
        assert_eq!(
            ongoing
                .allocator_module_spec()
                .expect("allocator module spec should exist")
                .module_name,
            "alloc.spec"
        );
    }

    #[test]
    fn test_join_codegen_with_failures_reports_error() {
        let backend = TrustCgCodegenBackend::host();
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "test".to_string() };

        // Manually construct OngoingCodegen with failures.
        let ongoing: Box<dyn Any> = Box::new(OngoingCodegen {
            modules: vec![],
            allocator_module: None,
            allocator_module_spec: None,
            failures: vec![("broken_fn".to_string(), "bad IR".to_string())],
            crate_name: "test".to_string(),
        });

        let err = backend.join_codegen(ongoing, &outputs).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("broken_fn"), "error should mention the failing function");
        assert!(msg.contains("bad IR"), "error should include the error reason");
    }

    #[test]
    fn test_bridge_error_converts_to_codegen_backend_error() {
        let bridge_err = crate::BridgeError::UnsupportedType("Fn".to_string());
        let codegen_err: CodegenBackendError = bridge_err.into();
        assert!(
            matches!(codegen_err, CodegenBackendError::Bridge(_)),
            "BridgeError should convert to CodegenBackendError::Bridge"
        );
        assert!(codegen_err.to_string().contains("unsupported type: Fn"));
    }
}
