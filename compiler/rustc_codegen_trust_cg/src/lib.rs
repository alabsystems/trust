//! rustc_codegen_trust_cg: trust-cg codegen backend for rustc.
//!
//! This crate implements `rustc_codegen_ssa::traits::CodegenBackend` for the
//! trust-cg verified codegen pipeline. It is a thin adapter that delegates the
//! actual MIR-to-LIR lowering to `trust-trust_cg-bridge`.
//!
//! # Architecture
//!
//! ```text
//! rustc driver (-Z codegen-backend=trust_cg)
//!     |
//!     v
//! rustc_codegen_trust_cg::TrustCgCodegenBackend  (this crate)
//!     |  implements rustc_codegen_ssa::traits::CodegenBackend
//!     |  converts rustc types <-> bridge types
//!     v
//! trust_cg_bridge::codegen_backend::TrustCgCodegenBackend
//!     |  MIR lowering, optimization, emission
//!     v
//! trust_cg-lower / trust_cg-codegen
//! ```
//!
//! # Usage
//!
//! Select this builtin backend via `-Z codegen-backend=trust-cg` (the legacy
//! underscore alias is also accepted) when invoking rustc built with the
//! `trust-cg` feature enabled in `rustc_interface`.
//!
//! Part of #829 (CodegenBackend for trust-cg).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: We need rustc_private to access compiler-internal crates.
#![feature(rustc_private)]

// Trust (Step 1, trust-ir-emission): feature-gated EMISSION ADAPTER. Compiled
// into the builtin backend only behind the off-by-default `trust-ir-emission`
// cargo feature. With the feature OFF this module — and its optional
// `trust-ir` / `serde_json` dependencies — is not compiled or linked, so the
// default codegen path is byte-for-byte unchanged.
#[cfg(feature = "trust-ir-emission")]
mod trust_ir_emission;

// Trust (Step 2, trust-ir-codegen): feature-gated OBSERVATIONAL CODEGEN PROBE.
// Compiled into the builtin backend only behind the off-by-default
// `trust-ir-codegen` cargo feature (which implies `trust-ir-emission`). It runs
// the proven `trust_ir::Module` -> LIR converter over every compiled function
// and LOGS handled-vs-fail-closed coverage, WITHOUT changing the shipped
// production path (VF -> LIR -> object). With the feature OFF this module is not
// compiled, so codegen is byte-for-byte unchanged.
#[cfg(feature = "trust-ir-codegen")]
mod trust_ir_codegen;

use std::any::Any;
use std::fs;

use rustc_abi::{CanonAbi, ExternAbi};
use rustc_ast::expand::allocator::{NO_ALLOC_SHIM_IS_UNSTABLE, default_fn_name, global_fn_name};
use rustc_codegen_ssa::back::archive::ArArchiveBuilderBuilder;
use rustc_codegen_ssa::back::link::link_binary;
use rustc_codegen_ssa::base::{allocator_kind_for_codegen, allocator_shim_contents};
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CompiledModule, CompiledModules, CrateInfo, ModuleKind, TargetConfig};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::LangItem;
use rustc_hir::attrs::Linkage;
use rustc_metadata::EncodedMetadata;
use rustc_middle::dep_graph::WorkProductMap;
use rustc_middle::middle::codegen_fn_attrs::{
    CodegenFnAttrFlags, CodegenFnAttrs, InstrumentFnAttr,
};
use rustc_middle::mir;
use rustc_middle::mono::Visibility;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_middle::util::Providers;
use rustc_session::Session;
use rustc_session::config::{
    CFGuard, CFProtection, CrateType, DebugInfo, FunctionReturn, InstrumentCoverage,
    InstrumentMcount, Lto, OptLevel as RustcOptLevel, OutputFilenames, OutputType, PrintKind,
};
use rustc_span::{Symbol, sym};
use rustc_symbol_mangling::mangle_internal_symbol;
use rustc_target::callconv::{ArgAbi, ArgAttribute, ArgExtension, PassMode};
use rustc_target::spec::{FramePointer, StackProtector};
use trust_cg_bridge::PanicRuntimeSymbols;
use trust_cg_bridge::codegen_backend::{
    self as bridge_backend, BridgeFramePointerPolicy, BridgeOptimizationLevel,
    RustcCodegenBackend as BridgeCodegenBackend, TrustCgCodegenBackend as BridgeBackend,
    TrustCgTargetArch,
};
use trust_types::{Terminator as VerifiableTerminator, VerifiableFunction};

// ---------------------------------------------------------------------------
// The rustc adapter
// ---------------------------------------------------------------------------

/// trust-cg codegen backend for rustc.
///
/// Implements the real `rustc_codegen_ssa::traits::CodegenBackend` trait by
/// delegating to the bridge crate's `TrustCgCodegenBackend`.
// Trust: CodegenBackend adapter for trust-cg integration (#829).
pub struct TrustCgCodegenBackend;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TrustCgTargetCapability {
    Aarch64Native,
    X86_64Native,
    /// The backend can answer target queries and participate in analysis/MIR
    /// emission, but it cannot yet perform a Rust Wasm link.
    Wasm32AnalysisOnly,
}

impl TrustCgTargetCapability {
    fn rustc_arch(self) -> &'static str {
        match self {
            Self::Aarch64Native => "aarch64",
            Self::X86_64Native => "x86_64",
            Self::Wasm32AnalysisOnly => "wasm32",
        }
    }

    fn supports_linked_output(self) -> bool {
        !matches!(self, Self::Wasm32AnalysisOnly)
    }
}

/// Exact built-in targets for which the bridge's scalar-register ABI fragment,
/// object format, pointer width, endianness, and baseline feature policy have
/// been reviewed. Custom JSON targets are rejected separately even if their
/// file stem matches one of these names.
fn target_capability(triple: &str) -> Option<TrustCgTargetCapability> {
    match triple {
        "aarch64-apple-darwin" | "aarch64-unknown-linux-gnu" | "aarch64-unknown-linux-musl" => {
            Some(TrustCgTargetCapability::Aarch64Native)
        }
        "x86_64-apple-darwin"
        | "x86_64-unknown-linux-gnu"
        | "x86_64-unknown-linux-musl"
        | "x86_64-pc-windows-msvc"
        | "x86_64-pc-windows-gnu" => Some(TrustCgTargetCapability::X86_64Native),
        "wasm32-unknown-unknown" => Some(TrustCgTargetCapability::Wasm32AnalysisOnly),
        _ => None,
    }
}

fn target_is_builtin(sess: &Session) -> bool {
    sess.opts.target_triple.debug_tuple() == sess.opts.target_triple.tuple()
}

fn target_is_exact_builtin_host(sess: &Session) -> bool {
    target_is_builtin(sess)
        && sess.opts.target_triple.tuple() == rustc_session::config::host_tuple()
}

fn supported_crate_types_for_outputs(should_link: bool) -> Vec<CrateType> {
    if should_link {
        // The only end-to-end artifact lane currently audited is an rlib whose
        // exported scalar functions are consumed by a production backend.
        // Executables need rustc's synthesized process-entry wrapper; dynamic
        // libraries and proc macros need visibility/PIC/loader contracts; and
        // static libraries need a complete archive/linkage audit. Advertising
        // any of those here makes Cargo treat an unavailable path as usable.
        return vec![CrateType::Rlib];
    }

    // Backend-independent MIR/metadata/dep-info emission does not construct or
    // link trust-cg objects. Preserve frontend analysis for every rustc crate
    // type without claiming that its linked artifact is supported.
    vec![
        CrateType::Executable,
        CrateType::Dylib,
        CrateType::Rlib,
        CrateType::StaticLib,
        CrateType::Cdylib,
        CrateType::ProcMacro,
        CrateType::Sdylib,
    ]
}

fn supported_link_crate_types() -> Vec<CrateType> {
    supported_crate_types_for_outputs(true)
}

/// Mirrors the driver's `print_crate_info` stop/continue contract. Ordinary
/// print requests are answered before codegen, while `native-static-libs` and
/// `link-args` require a completed link and therefore must retain all
/// production-session validation.
fn print_requests_stop_before_codegen(print_kinds: impl IntoIterator<Item = PrintKind>) -> bool {
    for kind in print_kinds {
        if !matches!(kind, PrintKind::NativeStaticLibs | PrintKind::LinkArgs) {
            return true;
        }
    }
    false
}

/// `rustbuild` passes the target's split-debuginfo default even when it has
/// disabled debuginfo for the crate. In that case the option cannot affect
/// either the object or the link, so accepting it is not silently dropping a
/// requested artifact. Every mode remains unsupported as soon as any
/// debuginfo is requested.
fn explicit_split_debuginfo_is_inert(debuginfo: DebugInfo) -> bool {
    debuginfo == DebugInfo::None
}

#[allow(rustc::bad_opt_access)]
fn unsupported_explicit_codegen_model(sess: &Session) -> Option<&'static str> {
    let cg = &sess.opts.cg;
    let unstable = &sess.opts.unstable_opts;
    if cg.code_model.is_some() {
        return Some("-Ccode-model");
    }
    if cg.relocation_model.is_some() {
        return Some("-Crelocation-model");
    }
    if cg.force_unwind_tables.is_some() {
        return Some("-Cforce-unwind-tables");
    }
    if cg.no_redzone.is_some() {
        return Some("-Cno-redzone");
    }
    if cg.dwarf_version.is_some() || unstable.dwarf_version.is_some() {
        return Some("DWARF-version override");
    }
    if cg.split_debuginfo.is_some() && !explicit_split_debuginfo_is_inert(cg.debuginfo) {
        return Some("-Csplit-debuginfo");
    }
    if !cg.jump_tables {
        return Some("-Cno-jump-tables");
    }
    if unstable.tls_model.is_some() {
        return Some("-Ztls-model");
    }
    if unstable.function_sections.is_some() {
        return Some("-Zfunction-sections");
    }
    if unstable.small_data_threshold.is_some() {
        return Some("-Zsmall-data-threshold");
    }
    if unstable.fixed_x18 {
        return Some("-Zfixed-x18");
    }
    if unstable.instrument_mcount != InstrumentMcount::Disabled {
        return Some("-Zinstrument-mcount");
    }
    if unstable.instrument_xray.is_some() {
        return Some("-Zinstrument-xray");
    }
    if unstable.emit_stack_sizes {
        return Some("-Zemit-stack-sizes");
    }
    if unstable.function_return != FunctionReturn::Keep {
        return Some("-Zfunction-return");
    }
    None
}

fn effective_frame_pointer_policy(
    target: FramePointer,
    requested: FramePointer,
) -> BridgeFramePointerPolicy {
    let mut effective = target;
    effective.ratchet(requested);
    match effective {
        FramePointer::MayOmit => BridgeFramePointerPolicy::MayOmit,
        FramePointer::NonLeaf => BridgeFramePointerPolicy::NonLeaf,
        FramePointer::Always => BridgeFramePointerPolicy::Always,
    }
}

impl TrustCgCodegenBackend {
    /// Create a new trust-cg backend adapter.
    pub fn new() -> Box<dyn CodegenBackend> {
        Box::new(Self)
    }

    fn bridge_for_target_arch(
        &self,
        target_arch: &str,
        target_triple: &str,
    ) -> Option<BridgeBackend> {
        TrustCgTargetArch::from_rustc_arch(target_arch)
            .map(|arch| BridgeBackend::new_for_triple(arch, target_triple))
    }

    fn bridge_for_session(&self, sess: &Session) -> BridgeBackend {
        let target_arch = sess.target.arch.desc();
        // The requested rustc tuple is the ABI/object contract. LLVM's target
        // spelling may contain aliases or deployment-version decoration and is
        // not authoritative for a non-LLVM emitter.
        let target_triple = sess.opts.target_triple.tuple();
        let optimization_level = match sess.opts.optimize {
            RustcOptLevel::No => BridgeOptimizationLevel::O0,
            RustcOptLevel::Less => BridgeOptimizationLevel::O1,
            RustcOptLevel::More => BridgeOptimizationLevel::O2,
            RustcOptLevel::Aggressive => BridgeOptimizationLevel::O3,
            RustcOptLevel::Size | RustcOptLevel::SizeMin => sess.dcx().fatal(
                "trust-cg does not yet implement size-specific optimization for -Copt-level=s/z",
            ),
        };
        let frame_pointer_policy = effective_frame_pointer_policy(
            sess.target.frame_pointer,
            sess.opts.cg.force_frame_pointers,
        );
        match self.bridge_for_target_arch(target_arch, target_triple) {
            Some(bridge) => bridge
                .with_optimization_level(optimization_level)
                .with_frame_pointer_policy(frame_pointer_policy),
            None => sess.dcx().fatal(format!(
                "trust-cg backend does not support target architecture `{target_arch}`"
            )),
        }
    }

    fn bridge_for_tcx<'tcx>(&self, tcx: TyCtxt<'tcx>) -> BridgeBackend {
        let bridge = self.bridge_for_session(tcx.sess);
        match panic_runtime_symbols_for_tcx(tcx) {
            Ok(symbols) => bridge.with_panic_runtime_symbols(symbols),
            Err(e) => {
                tcx.dcx().fatal(format!("trust-cg panic runtime symbol planning failed: {e}"))
            }
        }
    }

    fn is_wasm_session(sess: &Session) -> bool {
        sess.target.arch.desc() == "wasm32"
    }

    fn wasm_target_config() -> TargetConfig {
        // Analysis-only wasm32 sessions still need target queries. Do not
        // borrow the native bridge's ABI features here: that bridge supports
        // only AArch64/x86-64, and linked Wasm is rejected during `init`.
        TargetConfig {
            target_features: Vec::new(),
            unstable_target_features: Vec::new(),
            has_reliable_f16: false,
            has_reliable_f16_math: false,
            has_reliable_f128: false,
            has_reliable_f128_math: false,
        }
    }

    fn output_type_supported(target_arch: &str, output: OutputType) -> bool {
        if target_arch == "wasm32" {
            // Rustc-independent outputs remain usable for analysis. Linked
            // Wasm is deliberately unavailable until the backend emits
            // relocatable objects and participates in rustc's real link step.
            return matches!(output, OutputType::Metadata | OutputType::DepInfo | OutputType::Mir);
        }

        // The native bridge produces internal object files for rustc's normal
        // link/archive path. User-facing `--emit=obj` is excluded because the
        // adapter does not yet implement rustc's final-object artifact naming
        // and JSON notification protocol.
        matches!(
            output,
            OutputType::Exe | OutputType::Metadata | OutputType::DepInfo | OutputType::Mir
        )
    }

    fn emit_rustc_modules_for_bridge_module(
        &self,
        bridge: &BridgeBackend,
        bridge_module: &bridge_backend::CompiledModule,
        sess: &Session,
        outputs: &OutputFilenames,
    ) -> Vec<CompiledModule> {
        // Trust (M-POS): the PROVEN-OUTPUT GATE, IN THE COMPILER. Before emitting
        // any object for this module, run the byte-level output-preservation gate
        // (`trust_cg_bridge::verify_output::emit_objects_verified`) over the SOURCE
        // VerifiableFunctions captured during lowering. A function whose emitted
        // machine code is REFUTED (ay found a concrete input for which the bytes
        // compute the wrong value — a miscompile) makes codegen FAIL here, via
        // `sess.dcx().fatal`, and NO object is written. This is the rung that makes
        // the proved region load-bearing in trustc itself.
        //
        // Trust (RUNG 2 — shipped == verified): the gate now RETURNS the exact
        // object bytes it verified, keyed by source function name. We SHIP those
        // gate-verified bytes (below), instead of discarding them and re-emitting
        // a separate artifact. This closes the emit-time TOCTOU: the bytes the
        // gate VERIFIED are byte-for-byte the bytes trustc ships.
        let gate_mode = output_gate_mode(sess);
        let exact_builtin_host = target_is_exact_builtin_host(sess);
        if !output_gate_allows_unreconciled_target(gate_mode, exact_builtin_host) {
            sess.dcx().fatal(format!(
                "trust-cg: strict/full output preservation is calibrated only for the exact \
                 built-in host target `{}`; refusing unreconciled bytes for `{}`",
                rustc_session::config::host_tuple(),
                sess.opts.target_triple,
            ));
        }
        let mut gate_captured =
            run_output_preservation_gate(bridge, bridge_module, sess, gate_mode);

        let emitted_objects = match bridge.emit_module_objects(bridge_module) {
            Ok(objects) => objects,
            Err(e) => sess.dcx().fatal(format!(
                "trust-cg: failed to emit object(s) for `{}`: {e}",
                bridge_module.name
            )),
        };

        // Trust (RUNG 2): reconcile the freshly-emitted artifacts against the
        // gate-verified bytes. For every object whose source function the gate
        // VERIFIED, the shipped bytes MUST equal the verified bytes — assert this
        // per function and fail closed (fatal, no object written) on any
        // divergence. Then SHIP the verified bytes themselves, so the artifact on
        // disk is provably the artifact the gate checked. Under advisory
        // AllowUnknown/Off, functions the gate did not cover may still ship the
        // backend bytes unchanged. Under Strict/full, every emitted object must
        // consume exactly one matching verified entry; missing, extra, or
        // duplicate names fail closed.
        // The gate now receives this exact configured bridge, including target,
        // lowering policy, and optimization level. Even when a cross-target
        // decoder is unavailable under AllowUnknown, the uncertified bytes it
        // captures are the same candidate bytes reconciled and shipped here.
        let emitted_objects: Vec<bridge_backend::EmittedObject> = emitted_objects
            .into_iter()
            .map(|mut emitted| {
                if let Some(captured_bytes) = gate_captured.remove(&emitted.source_name) {
                    if emitted.bytes != captured_bytes {
                        sess.dcx().fatal(format!(
                            "trust-cg: RUNG 2 violation — the shipped object for `{}` diverged \
                             from the bytes the proven-output gate captured (captured {} bytes, \
                             re-emitted {} bytes). Refusing to ship unverified bytes.",
                            emitted.source_name,
                            captured_bytes.len(),
                            emitted.bytes.len()
                        ));
                    }
                    // Ship the gate-captured bytes (single source of truth). In
                    // AllowUnknown they may be explicitly uncertified, but the
                    // report says so and these remain the exact evaluated bytes.
                    emitted.bytes = captured_bytes;
                } else if gate_mode == OutputGateMode::Strict {
                    sess.dcx().fatal(format!(
                        "trust-cg: strict/full output preservation produced no exact-byte proof \
                         for emitted function `{}`; refusing an unverified artifact",
                        emitted.source_name
                    ));
                }
                emitted
            })
            .collect();

        if gate_mode == OutputGateMode::Strict && !gate_captured.is_empty() {
            // Hash iteration only feeds this vector; sorting below owns the
            // diagnostic order before it becomes observable.
            #[allow(rustc::potential_query_instability)]
            let mut unmatched = gate_captured.keys().cloned().collect::<Vec<_>>();
            unmatched.sort();
            sess.dcx().fatal(format!(
                "trust-cg: strict/full output preservation proved artifact(s) with no matching \
                 emitted function: {}; refusing name/cardinality drift",
                unmatched.join(", ")
            ));
        }

        if emitted_objects.is_empty() {
            sess.dcx().fatal(format!(
                "trust-cg: object emission for `{}` produced no artifacts",
                bridge_module.name
            ));
        }

        emitted_objects
            .into_iter()
            .map(|emitted| {
                if emitted.bytes.is_empty() {
                    sess.dcx().fatal(format!(
                        "trust-cg: object emission for `{}` produced an empty artifact `{}`",
                        emitted.source_name, emitted.artifact_name
                    ));
                }

                let object_path =
                    outputs.temp_path_for_cgu(OutputType::Object, &emitted.artifact_name);

                if let Err(e) = fs::write(&object_path, &emitted.bytes) {
                    sess.dcx().fatal(format!(
                        "trust-cg: failed to write object `{}` for `{}`: {e}",
                        emitted.artifact_name, emitted.source_name
                    ));
                }

                CompiledModule {
                    name: emitted.artifact_name,
                    kind: ModuleKind::Regular,
                    object: Some(object_path),
                    global_asm_object: None,
                    dwarf_object: None,
                    bytecode: None,
                    assembly: None,
                    llvm_ir: None,
                    links_from_incr_cache: Vec::new(),
                }
            })
            .collect()
    }

    fn emit_rustc_allocator_module_for_bridge_module(
        &self,
        bridge: &BridgeBackend,
        bridge_module: &bridge_backend::CompiledModule,
        sess: &Session,
        outputs: &OutputFilenames,
    ) -> CompiledModule {
        let emitted_object = match bridge.emit_allocator_module_object(bridge_module) {
            Ok(object) => object,
            Err(e) => sess.dcx().fatal(format!(
                "trust-cg: failed to emit allocator object(s) for `{}`: {e}",
                bridge_module.name
            )),
        };

        match emitted_object {
            None => CompiledModule {
                name: bridge_module.name.clone(),
                kind: ModuleKind::Allocator,
                object: None,
                global_asm_object: None,
                dwarf_object: None,
                bytecode: None,
                assembly: None,
                llvm_ir: None,
                links_from_incr_cache: Vec::new(),
            },
            Some(emitted) => {
                if !output_gate_allows_unverified_artifact(output_gate_mode(sess)) {
                    sess.dcx().fatal(format!(
                        "trust-cg: strict/full output preservation has no machine-checked proof \
                         over the exact allocator object bytes for `{}`; refusing emission",
                        emitted.source_name
                    ));
                }
                if emitted.bytes.is_empty() {
                    sess.dcx().fatal(format!(
                        "trust-cg: allocator object emission for `{}` produced an empty artifact `{}`",
                        emitted.source_name, emitted.artifact_name
                    ));
                }

                let object_path =
                    outputs.temp_path_for_cgu(OutputType::Object, &emitted.artifact_name);

                if let Err(e) = fs::write(&object_path, &emitted.bytes) {
                    sess.dcx().fatal(format!(
                        "trust-cg: failed to write allocator object `{}` for `{}`: {e}",
                        emitted.artifact_name, emitted.source_name
                    ));
                }

                CompiledModule {
                    name: bridge_module.name.clone(),
                    kind: ModuleKind::Allocator,
                    object: Some(object_path),
                    global_asm_object: None,
                    dwarf_object: None,
                    bytecode: None,
                    assembly: None,
                    llvm_ir: None,
                    links_from_incr_cache: Vec::new(),
                }
            }
        }
    }
}

// Trust (M-POS): the in-compiler proven-output gate policy + driver.
//
// Policy selection is dependency-tracked through `-Z trust-cg-output-gate`
// plus the batteries-on verifier policy:
//   - `off`           : disable the gate entirely (NOT recommended; this is the
//                       only setting that lets a Refuted function be emitted).
//   - `strict`        : EmitPolicy::StrictProvenOnly — every emitted function
//                       must carry a machine-checked output-preservation proof;
//                       Unknown is fail-closed (refused).
//   - `allow-unknown` : EmitPolicy::AllowUnknown — refuse only KNOWN miscompiles
//                       (Refuted), let unsupported-but-not-refuted shapes through,
//                       so unsupported proof shapes inside the separately admitted
//                       executable fragment can still compile.
//
// The DEFAULT is `strict` (rustc_session/src/options.rs). It used to be declared
// `allow-unknown` and then rewritten to `strict` by the driver under any strict
// policy, which meant `-Z help` advertised a default the compiler never used.
//
// `Refuted` is ALWAYS fatal under `strict` and `allow-unknown` alike (the gate's
// core guarantee); only `off` bypasses it. That is what makes allow-unknown a
// coverage setting rather than a soundness one — exactly the
// M-POS invariant. An in-scope
// strict verification session strengthens the effective policy to Strict and
// rejects `off`; raw/unscoped trustc is strict without needing an enable flag.
//
// Ambient environment is deliberately not consulted: this policy changes which
// machine code may be emitted and therefore must participate in rustc's hash.
#[derive(Clone, Copy, PartialEq, Eq)]
enum OutputGateMode {
    Off,
    Strict,
    AllowUnknown,
}

#[allow(rustc::bad_opt_access)]
fn output_gate_mode(sess: &Session) -> OutputGateMode {
    match output_gate_mode_for_verification(
        sess.trust_strict_verification_enabled(),
        &sess.opts.unstable_opts.trust_cg_output_gate,
    ) {
        Ok(mode) => mode,
        Err(reason) => sess.dcx().fatal(reason),
    }
}

fn output_gate_mode_for_verification(
    strict_verification: bool,
    configured_mode: &str,
) -> Result<OutputGateMode, &'static str> {
    let configured_mode = output_gate_mode_from_name(configured_mode)?;
    if strict_verification {
        if configured_mode == OutputGateMode::Off {
            return Err("-Ztrust-cg-output-gate=off is incompatible with batteries-on strict \
                 Trust verification; use -Ztrust-verify=off for a vanilla compile");
        }
        return Ok(OutputGateMode::Strict);
    }
    Ok(configured_mode)
}

fn output_gate_mode_from_name(mode: &str) -> Result<OutputGateMode, &'static str> {
    match mode {
        "off" => Ok(OutputGateMode::Off),
        "strict" => Ok(OutputGateMode::Strict),
        "allow-unknown" => Ok(OutputGateMode::AllowUnknown),
        _ => Err("invalid -Ztrust-cg-output-gate value reached the trust-cg backend"),
    }
}

fn output_gate_allows_unverified_artifact(mode: OutputGateMode) -> bool {
    // An emission path with no exact-byte proof is an honest Unknown:
    // admissible only under AllowUnknown or explicit Off, never strict mode.
    mode != OutputGateMode::Strict
}

fn output_gate_allows_unreconciled_target(mode: OutputGateMode, exact_builtin_host: bool) -> bool {
    exact_builtin_host || output_gate_allows_unverified_artifact(mode)
}

/// Run the proven-output gate over a bridge module's source functions. On a
/// Refuted (miscompile) or policy-refused Unknown verdict, this calls
/// `sess.dcx().fatal(..)` and codegen aborts — no object is emitted. Returns
/// (allowing emission to proceed) only when the gate clears the module.
///
/// Trust (RUNG 2): returns a map from source function name to the exact candidate
/// bytes the gate evaluated and captured. Strict mode returns only verified
/// bytes; AllowUnknown may also return explicitly reported uncertified bytes.
/// The caller reconciles and ships this single source of truth. An empty map
/// means the gate was off or the module had no source functions.
fn run_output_preservation_gate(
    bridge: &BridgeBackend,
    bridge_module: &bridge_backend::CompiledModule,
    sess: &Session,
    mode: OutputGateMode,
) -> FxHashMap<String, Vec<u8>> {
    use trust_cg_bridge::verify_output::{EmitPolicy, emit_objects_verified_reported_with_backend};

    if mode == OutputGateMode::Off {
        return FxHashMap::default();
    }

    // Only regular modules carry source functions; synthesized modules (e.g. the
    // allocator shim) have `source_functions == None` and nothing to verify.
    let Some(sources) = bridge_module.source_functions.as_ref() else {
        return FxHashMap::default();
    };
    if sources.is_empty() {
        return FxHashMap::default();
    }

    let policy = match mode {
        OutputGateMode::Strict => EmitPolicy::StrictProvenOnly,
        // AllowUnknown is the default; Off returned above.
        _ => EmitPolicy::AllowUnknown,
    };

    // The gate emits each function to bytes ONCE, discharges output-preservation
    // against the auto-derived IR semantics over THOSE bytes, and (RUNG 2) returns
    // the verified bytes. A Refuted function is rejected under every policy; an
    // Unknown one only under StrictProvenOnly. We KEEP the returned bytes and
    // ship them, instead of discarding and re-emitting a separate artifact.
    //
    // Trust (RUNG 3 — CERTIFICATION REPORT): the gate also returns a per-module
    // tally of the output-preservation GRADE assigned each emitted function
    // ([PROVED] / [VALIDATED] / uncertified). We surface it as a stderr note so
    // the UNCERTIFIED surface is VISIBLE — a function that ships without a
    // kernel-re-checkable proof is COUNTED and reported, never silently treated
    // as if covered. (Under StrictProvenOnly only kernel-[PROVED] functions ship;
    // [VALIDATED] and Unknown are refused, landing in the Err arm below.)
    match emit_objects_verified_reported_with_backend(sources, policy, bridge) {
        Ok((verified, report)) => {
            sess.dcx().note(format!(
                "trust-cg certification report for module `{}`: {} ({})",
                bridge_module.name,
                report,
                policy_label(policy)
            ));
            verified.into_iter().collect()
        }
        Err(e) => {
            sess.dcx().fatal(format!(
                "trust-cg: REFUSING to emit module `{}` — the in-compiler proven-output \
                 gate rejected it: {e}",
                bridge_module.name
            ));
        }
    }
}

/// Human-readable label for the active gate policy, for the certification note.
fn policy_label(policy: trust_cg_bridge::verify_output::EmitPolicy) -> &'static str {
    use trust_cg_bridge::verify_output::EmitPolicy;
    match policy {
        EmitPolicy::StrictProvenOnly => "policy: strict (certified-fragment: only [PROVED] ships)",
        EmitPolicy::AllowUnknown => {
            "policy: allow-unknown (default: emits unproven, Refuted fatal)"
        }
    }
}

fn scalar_register_abi_ty_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    let PassMode::Direct(attrs) = &arg.mode else {
        return false;
    };
    // InReg and integer extension are observable caller/callee contracts. The
    // current bridge carries neither attribute into LIR/object emission.
    if attrs.contains(ArgAttribute::InReg) || attrs.arg_ext != ArgExtension::None {
        return false;
    }
    if arg.layout.size.bits() == 0 || arg.layout.size.bits() > 64 {
        return false;
    }
    matches!(arg.layout.ty.kind(), ty::Bool | ty::Int(_) | ty::Uint(_))
}

fn ignored_return_abi_ty_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    matches!(arg.mode, PassMode::Ignore)
        && match arg.layout.ty.kind() {
            ty::Never => true,
            ty::Tuple(fields) => fields.is_empty(),
            _ => false,
        }
}

fn codegen_attrs_issue(attrs: &CodegenFnAttrs) -> Option<String> {
    if attrs.flags.intersects(
        CodegenFnAttrFlags::TRACK_CALLER
            | CodegenFnAttrFlags::NAKED
            | CodegenFnAttrFlags::OFFLOAD_KERNEL
            | CodegenFnAttrFlags::FOREIGN_ITEM
            | CodegenFnAttrFlags::EXTERNALLY_IMPLEMENTABLE_ITEM,
    ) {
        return Some(format!("unsupported codegen attribute flags {:?}", attrs.flags));
    }
    if !attrs.target_features.is_empty() || attrs.safe_target_features {
        return Some("per-function target features are not represented by trust-cg".to_string());
    }
    if attrs.instruction_set.is_some() {
        return Some(
            "per-function instruction-set selection is not represented by trust-cg".to_string(),
        );
    }
    if !attrs.foreign_item_symbol_aliases.is_empty() {
        return Some("foreign symbol aliases are not emitted by trust-cg".to_string());
    }
    if attrs.link_ordinal.is_some() || attrs.import_linkage.is_some() {
        return Some("import linkage/ordinal metadata is not emitted by trust-cg".to_string());
    }
    if attrs.link_section.is_some() || attrs.alignment.is_some() {
        return Some(
            "function section/alignment overrides are not emitted by trust-cg".to_string(),
        );
    }
    if attrs.patchable_function_entry.is_some() {
        return Some("per-function patchable entries are not emitted by trust-cg".to_string());
    }
    if attrs.objc_class.is_some() || attrs.objc_selector.is_some() {
        return Some("Objective-C function metadata is not emitted by trust-cg".to_string());
    }
    if !matches!(attrs.instrument_fn, InstrumentFnAttr::Default) {
        return Some(
            "per-function instrumentation policy is not implemented by trust-cg".to_string(),
        );
    }
    None
}

fn supported_canonical_abi(extern_abi: ExternAbi) -> Option<CanonAbi> {
    match extern_abi {
        ExternAbi::Rust => Some(CanonAbi::Rust),
        ExternAbi::C { unwind: false } => Some(CanonAbi::C),
        _ => None,
    }
}

/// Maximum number of scalar integer arguments that remain register-resident
/// in the exact ABI lane selected by `target_capability`.
///
/// `ArgAbi::mode == Direct` is not sufficient evidence that an argument is in
/// a register: overflow arguments are also `Direct` and are assigned stack
/// locations later by the target ABI. The adapter does not transport rustc's
/// per-argument locations into bridge LIR, so accepting an overflow argument
/// would silently substitute the bridge's independently implemented stack
/// layout. Keep the production lane register-only until that contract is
/// represented and checked end to end.
fn scalar_register_argument_limit(target_triple: &str) -> Option<usize> {
    match target_triple {
        "aarch64-apple-darwin"
        | "aarch64-unknown-linux-gnu"
        | "aarch64-unknown-linux-musl" => Some(8),
        "x86_64-apple-darwin"
        | "x86_64-unknown-linux-gnu"
        | "x86_64-unknown-linux-musl" => Some(6),
        "x86_64-pc-windows-msvc" | "x86_64-pc-windows-gnu" => Some(4),
        _ => None,
    }
}

/// Admit only the exact ABI fragment the bridge materializes today: Rust or C,
/// non-variadic/non-unwinding functions whose explicit arguments and result are
/// single integer registers of at most 64 bits (or a unit/never result). This is
/// checked for definitions and every direct callee, so an LLVM-built dependency
/// cannot silently introduce an incompatible hidden/pass-mode contract.
fn validate_codegen_instance_abi<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    mir_arg_count: usize,
) -> Result<(), String> {
    let attrs = tcx.codegen_instance_attrs(instance.def);
    if let Some(reason) = codegen_attrs_issue(&attrs) {
        return Err(reason);
    }

    let typing_env = ty::TypingEnv::fully_monomorphized();
    let instance_ty = instance.ty(tcx, typing_env);
    if !instance_ty.is_fn() {
        return Err(format!("instance type `{instance_ty}` is not a callable function"));
    }
    let extern_abi = instance_ty.fn_sig(tcx).abi();
    let Some(expected_canon_abi) = supported_canonical_abi(extern_abi) else {
        return Err(format!(
            "calling convention `{extern_abi}` is not in the audited Rust/C ABI lane"
        ));
    };

    let fn_abi = tcx
        .fn_abi_of_instance(typing_env.as_query_input((instance, ty::List::empty())))
        .map_err(|error| format!("rustc FnAbi computation failed: {error:?}"))?;
    if fn_abi.conv != expected_canon_abi {
        return Err(format!(
            "canonical calling convention drift: source `{extern_abi}` resolved to `{}`",
            fn_abi.conv
        ));
    }
    if fn_abi.c_variadic || fn_abi.fixed_count as usize != fn_abi.args.len() {
        return Err(
            "variadic or implicit ABI arguments are not represented by trust-cg".to_string()
        );
    }
    if fn_abi.can_unwind {
        return Err(
            "a potentially-unwinding function ABI is not represented by trust-cg".to_string()
        );
    }
    if fn_abi.args.len() != mir_arg_count {
        return Err(format!(
            "rustc FnAbi carries {} argument(s), but executable MIR exposes {mir_arg_count}; hidden/spread arguments are unsupported",
            fn_abi.args.len()
        ));
    }
    let target_triple = tcx.sess.opts.target_triple.tuple();
    let Some(register_arg_limit) = scalar_register_argument_limit(target_triple) else {
        return Err(format!(
            "target `{target_triple}` has no audited scalar-register argument assignment"
        ));
    };
    if fn_abi.args.len() > register_arg_limit {
        return Err(format!(
            "{} arguments exceed target `{target_triple}`'s {register_arg_limit} scalar integer argument registers; stack-argument placement is not represented by trust-cg",
            fn_abi.args.len()
        ));
    }
    for (index, arg) in fn_abi.args.iter().enumerate() {
        if !scalar_register_abi_ty_supported(arg) {
            return Err(format!(
                "argument {index} uses unsupported ABI type/pass mode `{}` / {:?}",
                arg.layout.ty, arg.mode
            ));
        }
    }
    if !scalar_register_abi_ty_supported(&fn_abi.ret)
        && !ignored_return_abi_ty_supported(&fn_abi.ret)
    {
        return Err(format!(
            "return value uses unsupported ABI type/pass mode `{}` / {:?}",
            fn_abi.ret.layout.ty, fn_abi.ret.mode
        ));
    }
    Ok(())
}

/// Resolve a direct call in an already-monomorphized body to the exact symbol
/// rustc assigned its concrete instance. Non-direct calls return `Ok(None)`;
/// an unresolved `FnDef` is a hard error because retaining its generic display
/// name would emit a call to a symbol that cannot exist.
fn mono_direct_call_name_override<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &mir::Terminator<'tcx>,
) -> Result<Option<String>, String> {
    let mir::TerminatorKind::Call { func, args: call_args, .. } = &terminator.kind else {
        return Ok(None);
    };
    let mir::Operand::Constant(const_op) = func else {
        return Ok(None);
    };
    let ty::FnDef(def_id, args) = *const_op.const_.ty().kind() else {
        return Ok(None);
    };

    match ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), def_id, args) {
        Ok(Some(instance)) => {
            validate_codegen_instance_abi(tcx, instance, call_args.len()).map_err(|reason| {
                format!(
                    "direct callee `{}` has unsupported ABI: {reason}",
                    tcx.def_path_str(def_id)
                )
            })?;
            Ok(Some(tcx.symbol_name(instance).name.to_string()))
        }
        Ok(None) => Err(format!(
            "could not resolve concrete direct-call instance `{}`",
            tcx.def_path_str(def_id)
        )),
        Err(error) => Err(format!(
            "failed to resolve concrete direct-call instance `{}`: {error:?}",
            tcx.def_path_str(def_id)
        )),
    }
}

fn apply_direct_call_name_overrides(
    func: &mut VerifiableFunction,
    overrides: &[Option<String>],
) -> Result<(), String> {
    if func.body.blocks.len() != overrides.len() {
        return Err(format!(
            "MIR/extracted block-count drift while binding direct-call symbols: MIR={} extracted={}",
            overrides.len(),
            func.body.blocks.len()
        ));
    }
    for (extracted_block, override_name) in func.body.blocks.iter_mut().zip(overrides.iter()) {
        let Some(symbol_name) = override_name else {
            continue;
        };
        if let VerifiableTerminator::Call { func: callee, .. } = &mut extracted_block.terminator {
            *callee = symbol_name.clone();
        }
    }
    Ok(())
}

// A codegen backend must consume rustc's reachable `MonoItem` inventory. Using
// `mir_keys()` instead compiles unreachable generic definitions, loses concrete
// substitutions, collides distinct instantiations, and ignores statics/global
// assembly. The adapter therefore materializes each concrete instance and
// rejects every reachable item it cannot faithfully emit.
fn production_function_symbol_contract_supported(
    linkage: Linkage,
    visibility: Visibility,
) -> bool {
    // The current object emitter creates one strong definition per function.
    // Internal is not safe to promote: rustc may create CGU-local copies, and
    // splitting every function into its own object prevents us from preserving
    // local visibility across direct calls. Weak/link-once/common semantics are
    // likewise not strong definitions. Its object writers also mark every
    // function globally visible/default; silently promoting a Hidden symbol or
    // making a Protected symbol interposable changes dynamic-link behavior.
    // Admit only the exact emitted contract until both properties travel
    // through LIR/object emission.
    linkage == Linkage::External && visibility == Visibility::Default
}

fn extract_mono_verifiable_function<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<VerifiableFunction, String> {
    let symbol_name = tcx.symbol_name(instance).name.to_string();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
        || -> Result<VerifiableFunction, String> {
            let generic_body = tcx.instance_mir(instance.def);
            let mono_body: mir::Body<'tcx> = instance
                .try_instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(tcx, generic_body.clone()),
                )
                .map_err(|error| format!("MIR monomorphization failed: {error:?}"))?;

            validate_codegen_instance_abi(tcx, instance, mono_body.arg_count)
                .map_err(|reason| format!("unsupported definition ABI: {reason}"))?;

            let mut func = trust_mir_extract::extract_function_for_codegen(tcx, &mono_body)
                .map_err(|error| error.to_string())?;
            let overrides = mono_body
                .basic_blocks
                .iter()
                .map(|mir_block| mono_direct_call_name_override(tcx, mir_block.terminator()))
                .collect::<Result<Vec<_>, _>>()?;
            apply_direct_call_name_overrides(&mut func, &overrides)?;
            func.name = symbol_name.clone();
            Ok(func)
        },
    ));

    match result {
        Ok(result) => result.map_err(|reason| format!("instance `{symbol_name}`: {reason}")),
        Err(_) => Err(format!(
            "panic (fail-closed) while extracting monomorphic instance `{symbol_name}`"
        )),
    }
}

/// Build the single deterministic production inventory used by every output
/// path. No reachable item may be skipped: omission would produce a linkable
/// artifact whose behavior differs from rustc's mono-item graph.
fn build_production_mono_functions<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> Result<Vec<VerifiableFunction>, String> {
    use rustc_middle::mono::MonoItem;

    let mut instances = Vec::new();
    let mut symbols = FxHashMap::default();
    let partitions = tcx.collect_and_partition_mono_items(());

    for cgu in partitions.codegen_units {
        for (item, data) in cgu.items() {
            match *item {
                MonoItem::Fn(instance) => {
                    if !production_function_symbol_contract_supported(
                        data.linkage,
                        data.visibility,
                    ) {
                        return Err(format!(
                            "reachable function `{}` requires unsupported {:?} linkage / {:?} visibility",
                            tcx.symbol_name(instance).name,
                            data.linkage,
                            data.visibility,
                        ));
                    }
                    let symbol = tcx.symbol_name(instance).name.to_string();
                    if let Some(previous) = symbols.insert(symbol.clone(), instance) {
                        if previous != instance {
                            return Err(format!(
                                "distinct monomorphic instances collide on output symbol `{symbol}`: \
                                 `{previous}` versus `{instance}`"
                            ));
                        }
                        continue;
                    }
                    instances.push((symbol, instance));
                }
                MonoItem::Static(def_id) => {
                    return Err(format!(
                        "reachable static `{}` is not wired into trust-cg object emission",
                        tcx.def_path_str(def_id)
                    ));
                }
                MonoItem::GlobalAsm(item_id) => {
                    return Err(format!(
                        "reachable global assembly item `{item_id:?}` is not supported by trust-cg"
                    ));
                }
            }
        }
    }

    instances.sort_by(|(left, _), (right, _)| left.cmp(right));
    let functions = instances
        .into_iter()
        .map(|(_, instance)| extract_mono_verifiable_function(tcx, instance))
        .collect::<Result<Vec<_>, _>>()?;

    tracing::info!(
        extracted = functions.len(),
        "[trust_cg] reachable monomorphic extraction complete"
    );
    Ok(functions)
}

fn lang_item_symbol<'tcx>(tcx: TyCtxt<'tcx>, lang_item: LangItem) -> Result<String, String> {
    let def_id = tcx
        .lang_items()
        .get(lang_item)
        .ok_or_else(|| format!("missing required lang item `{}`", lang_item.name()))?;
    let instance = ty::Instance::mono(tcx, def_id);
    Ok(tcx.symbol_name(instance).name.to_string())
}

fn panic_runtime_symbols_for_tcx<'tcx>(tcx: TyCtxt<'tcx>) -> Result<PanicRuntimeSymbols, String> {
    Ok(PanicRuntimeSymbols {
        add_overflow: Some(lang_item_symbol(tcx, LangItem::PanicAddOverflow)?),
        sub_overflow: Some(lang_item_symbol(tcx, LangItem::PanicSubOverflow)?),
        mul_overflow: Some(lang_item_symbol(tcx, LangItem::PanicMulOverflow)?),
        div_overflow: Some(lang_item_symbol(tcx, LangItem::PanicDivOverflow)?),
        rem_overflow: Some(lang_item_symbol(tcx, LangItem::PanicRemOverflow)?),
        neg_overflow: Some(lang_item_symbol(tcx, LangItem::PanicNegOverflow)?),
        shl_overflow: Some(lang_item_symbol(tcx, LangItem::PanicShlOverflow)?),
        shr_overflow: Some(lang_item_symbol(tcx, LangItem::PanicShrOverflow)?),
        div_by_zero: Some(lang_item_symbol(tcx, LangItem::PanicDivZero)?),
        rem_by_zero: Some(lang_item_symbol(tcx, LangItem::PanicRemZero)?),
        null_pointer_dereference: Some(lang_item_symbol(
            tcx,
            LangItem::PanicNullPointerDereference,
        )?),
    })
}

fn allocator_function_spec_from_name<M>(
    mangle: &mut M,
    name: Symbol,
) -> Option<bridge_backend::AllocatorFunctionSpec>
where
    M: FnMut(&str) -> String,
{
    let (kind, inputs, output) = match name {
        sym::alloc => (
            bridge_backend::AllocatorFunctionKind::Alloc,
            vec![bridge_backend::AllocatorArgKind::Layout],
            bridge_backend::AllocatorResultKind::ResultPtr,
        ),
        sym::dealloc => (
            bridge_backend::AllocatorFunctionKind::Dealloc,
            vec![bridge_backend::AllocatorArgKind::Ptr, bridge_backend::AllocatorArgKind::Layout],
            bridge_backend::AllocatorResultKind::Unit,
        ),
        sym::realloc => (
            bridge_backend::AllocatorFunctionKind::Realloc,
            vec![
                bridge_backend::AllocatorArgKind::Ptr,
                bridge_backend::AllocatorArgKind::Layout,
                bridge_backend::AllocatorArgKind::Usize,
            ],
            bridge_backend::AllocatorResultKind::ResultPtr,
        ),
        sym::alloc_zeroed => (
            bridge_backend::AllocatorFunctionKind::AllocZeroed,
            vec![bridge_backend::AllocatorArgKind::Layout],
            bridge_backend::AllocatorResultKind::ResultPtr,
        ),
        sym::alloc_error_handler => (
            bridge_backend::AllocatorFunctionKind::AllocErrorHandler,
            vec![bridge_backend::AllocatorArgKind::Layout],
            bridge_backend::AllocatorResultKind::Never,
        ),
        _ => return None,
    };

    let wrapper_symbol_name = mangle(&global_fn_name(name));
    let callee_symbol_name = mangle(&default_fn_name(name));

    Some(bridge_backend::AllocatorFunctionSpec {
        name: name.to_string(),
        wrapper_symbol_name,
        callee_symbol_name,
        kind,
        inputs,
        output,
    })
}

fn allocator_module_spec_from_names_with_mangler<I, M>(
    crate_name: &str,
    names: I,
    mut mangle: M,
) -> Result<bridge_backend::AllocatorModuleSpec, String>
where
    I: IntoIterator<Item = Symbol>,
    M: FnMut(&str) -> String,
{
    let functions = names
        .into_iter()
        .map(|name| {
            allocator_function_spec_from_name(&mut mangle, name)
                .ok_or_else(|| format!("unsupported allocator shim method `{name}`"))
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(bridge_backend::AllocatorModuleSpec {
        module_name: BridgeBackend::allocator_module_name(crate_name),
        functions,
        no_alloc_shim_is_unstable_symbol_name: Some(mangle(NO_ALLOC_SHIM_IS_UNSTABLE)),
    })
}

fn allocator_module_spec_for_tcx<'tcx>(
    tcx: TyCtxt<'tcx>,
    crate_name: &str,
) -> Result<Option<bridge_backend::AllocatorModuleSpec>, String> {
    let Some(kind) = allocator_kind_for_codegen(tcx) else {
        return Ok(None);
    };
    let method_names = allocator_shim_contents(tcx, kind).into_iter().map(|method| method.name);
    allocator_module_spec_from_names_with_mangler(crate_name, method_names, |item_name| {
        mangle_internal_symbol(tcx, item_name)
    })
    .map(Some)
}

// ---------------------------------------------------------------------------
// Ongoing codegen handle
// ---------------------------------------------------------------------------

/// Opaque handle returned by `codegen_crate`, consumed by `join_codegen`.
///
/// Wraps the bridge's `OngoingCodegen` plus any rustc-specific metadata
/// we need to carry through the pipeline.
// Trust: CodegenBackend adapter for trust-cg integration (#829).
struct OngoingTrustCgCodegen {
    /// Bridge-level ongoing codegen result. `None` when rustc requested only
    /// backend-independent outputs such as MIR/metadata.
    bridge_ongoing: Option<Box<dyn Any>>,
    /// Crate name for diagnostics.
    crate_name: String,
    /// Number of functions extracted from MIR (for diagnostics).
    function_count: usize,
}

// ---------------------------------------------------------------------------
// CodegenBackend impl
// ---------------------------------------------------------------------------

// Trust: CodegenBackend adapter for trust-cg integration (#829, #959).
impl CodegenBackend for TrustCgCodegenBackend {
    fn name(&self) -> &'static str {
        "trust-cg"
    }

    fn init(&self, sess: &Session) {
        if !target_is_builtin(sess) {
            sess.dcx().fatal(
                "trust-cg accepts only audited built-in target definitions; custom JSON targets \
                 are rejected even when their file stem resembles a supported target",
            );
        }
        let requested_triple = sess.opts.target_triple.tuple();
        let Some(capability) = target_capability(requested_triple) else {
            sess.dcx().fatal(format!(
                "trust-cg does not support target `{requested_triple}`; supported native targets: \
                 aarch64-apple-darwin, aarch64-unknown-linux-gnu/musl, \
                 x86_64-apple-darwin, x86_64-unknown-linux-gnu/musl, and \
                 x86_64-pc-windows-msvc/gnu; wasm32-unknown-unknown is analysis-only"
            ));
        };
        if sess.target.arch.desc() != capability.rustc_arch() {
            sess.dcx().fatal(format!(
                "trust-cg target contract mismatch: tuple `{requested_triple}` requires arch `{}`, \
                 but rustc loaded `{}`",
                capability.rustc_arch(),
                sess.target.arch.desc(),
            ));
        }

        // The driver stops after answering any ordinary print request. Its
        // default executable output and panic strategy are placeholders in
        // that case, not a request for trust-cg to emit a linked artifact.
        // Keep the target checks above so backend target queries remain
        // honest, but do not reject codegen settings that will never run.
        if print_requests_stop_before_codegen(sess.opts.prints.iter().map(|request| request.kind)) {
            return;
        }

        // Neither backend implements whole-program LTO. `thin_lto_supported`
        // alone only changes rustc's fallback choice; it does not make fat LTO
        // or linker-plugin LTO sound for a backend that emits no bitcode.
        match sess.lto() {
            Lto::No | Lto::ThinLocal => {}
            Lto::Thin | Lto::Fat => {
                sess.dcx().fatal("LTO is not supported by the trust-cg codegen backend")
            }
        }
        if sess.opts.cg.linker_plugin_lto.enabled() {
            sess.dcx().fatal("linker-plugin LTO is not supported by the trust-cg codegen backend");
        }
        if sess.opts.cg.instrument_coverage() != InstrumentCoverage::No {
            sess.dcx().fatal(
                "-Cinstrument-coverage is not supported by the trust-cg codegen backend; \
                 use Trust's verifier coverage reporting instead",
            );
        }

        if sess.opts.unstable_opts.no_link || sess.opts.unstable_opts.link_only {
            sess.dcx().fatal(
                "-Zno-link/-Zlink-only artifact serialization is not implemented by trust-cg; \
                 the backend will not emit or consume an rlink with an unverified object inventory",
            );
        }

        if sess.opts.output_types.should_link() {
            if let Some(option) = unsupported_explicit_codegen_model(sess) {
                sess.dcx().fatal(format!(
                    "{option} is not implemented by trust-cg and cannot be silently ignored"
                ));
            }
            if !capability.supports_linked_output() {
                sess.dcx().fatal(
                    "trust-cg cannot link wasm32 Rust crates: its Wasm lowering does not yet emit \
                     relocatable objects or participate in rustc's dependency/native-library/linker \
                     pipeline; use --emit=mir for analysis or a production Wasm backend",
                );
            }
            if sess.panic_strategy().unwinds() {
                sess.dcx().fatal(
                    "panic=unwind is not supported by trust-cg until invoke, cleanup, personality, \
                     LSDA, and resume semantics are emitted; compile with -Cpanic=abort",
                );
            }
            if sess.opts.cg.target_cpu.is_some() {
                sess.dcx().fatal(
                    "-Ctarget-cpu is not supported by trust-cg; target tuning must not be silently ignored",
                );
            }
            if !sess.opts.cg.target_feature.is_empty() {
                sess.dcx().fatal(
                    "-Ctarget-feature is not supported by trust-cg; feature-dependent ABI/codegen is unwired",
                );
            }
            if sess.opts.cg.debuginfo != DebugInfo::None {
                sess.dcx().fatal(
                    "-Cdebuginfo is not supported by trust-cg; the emitted objects contain no faithful debug information",
                );
            }
            if sess.opts.cg.profile_generate.enabled() || sess.opts.cg.profile_use.is_some() {
                sess.dcx().fatal(
                    "profile-guided instrumentation/optimization is not supported by trust-cg",
                );
            }
            if sess.opts.cg.control_flow_guard != CFGuard::Disabled
                || sess.opts.unstable_opts.cf_protection != CFProtection::None
                || sess.opts.unstable_opts.branch_protection.is_some()
                || sess.opts.unstable_opts.ehcont_guard
                || sess.opts.unstable_opts.retpoline
                || sess.opts.unstable_opts.retpoline_external_thunk
                || sess.opts.unstable_opts.indirect_branch_cs_prefix
            {
                sess.dcx().fatal(
                    "requested control-flow/branch/return mitigation is not implemented by trust-cg",
                );
            }
            if !sess.sanitizers().is_empty() {
                sess.dcx().fatal("sanitizers are not implemented by trust-cg");
            }
            if sess.stack_protector() != StackProtector::None {
                sess.dcx().fatal("stack protection is not implemented by trust-cg");
            }
            if sess.opts.unstable_opts.direct_access_external_data.is_some()
                || sess.opts.unstable_opts.plt.is_some()
            {
                sess.dcx().fatal(
                    "external-data/PLT code-model overrides are not implemented by trust-cg",
                );
            }
            let patchable = &sess.opts.unstable_opts.patchable_function_entry;
            if patchable.prefix() != 0 || patchable.entry() != 0 || patchable.section().is_some() {
                sess.dcx().fatal("patchable function entries are not implemented by trust-cg");
            }
            if sess.opts.incremental.is_some() || sess.opts.cg.incremental.is_some() {
                sess.dcx().fatal(
                    "incremental object reuse is not implemented by trust-cg; disable -Cincremental",
                );
            }
            if sess.opts.cg.codegen_units.is_some_and(|units| units != 1) {
                sess.dcx().fatal(
                    "trust-cg currently emits one codegen unit; explicit -Ccodegen-units values other than 1 are unsupported",
                );
            }
            if !sess.opts.cg.llvm_args.is_empty()
                || !sess.opts.cg.passes.is_empty()
                || sess.opts.cg.no_prepopulate_passes
                || sess.opts.unstable_opts.print_llvm_passes
                || sess.opts.unstable_opts.time_llvm_passes
                || sess.print_llvm_stats()
                || sess.print_llvm_stats_json().is_some()
            {
                sess.dcx().fatal(
                    "LLVM pass controls and codegen statistics are not implemented by the trust-cg backend",
                );
            }
        }

        let target_arch = sess.target.arch.desc();
        if let Some(unsupported) = sess
            .opts
            .output_types
            .keys()
            .find(|&&output| !Self::output_type_supported(target_arch, output))
        {
            sess.dcx().fatal(format!(
                "trust-cg does not support --emit={} for target architecture `{target_arch}`",
                unsupported.shorthand(),
            ));
        }

        // Analysis-only Wasm requests need target queries but must not construct
        // the native register-machine bridge.
        if Self::is_wasm_session(sess) {
            return;
        }

        let bridge = self.bridge_for_session(sess);
        if let Err(e) = bridge.init() {
            sess.dcx().fatal(format!("trust-cg backend initialization failed: {e}"));
        }
    }

    fn supported_crate_types(&self, sess: &Session) -> Vec<CrateType> {
        supported_crate_types_for_outputs(sess.opts.output_types.should_link())
    }

    fn supported_link_crate_types(&self, _sess: &Session) -> Vec<CrateType> {
        supported_link_crate_types()
    }

    // Trust: #959 -- register queries needed by the trust-cg backend.
    fn provide(&self, _providers: &mut Providers) {
        // trust-cg does not currently inject custom queries into the rustc
        // query system. When we add incremental compilation support or
        // custom optimization queries, they will be registered here.
        //
        // The standard rustc_codegen_ssa queries (symbol_export, etc.)
        // are already registered by the driver before calling into
        // the backend.
    }

    fn target_config(&self, sess: &Session) -> TargetConfig {
        if Self::is_wasm_session(sess) {
            return Self::wasm_target_config();
        }

        let bridge = self.bridge_for_session(sess);
        let bridge_config = BridgeCodegenBackend::target_config(&bridge);
        TargetConfig {
            target_features: bridge_config
                .target_features
                .iter()
                .map(|s| Symbol::intern(s))
                .collect(),
            unstable_target_features: bridge_config
                .unstable_target_features
                .iter()
                .map(|s| Symbol::intern(s))
                .collect(),
            has_reliable_f16: bridge_config.has_reliable_f16,
            has_reliable_f16_math: bridge_config.has_reliable_f16_math,
            has_reliable_f128: bridge_config.has_reliable_f128,
            has_reliable_f128_math: bridge_config.has_reliable_f128_math,
        }
    }

    fn target_cpu(&self, sess: &Session) -> String {
        if Self::is_wasm_session(sess) {
            return sess
                .opts
                .cg
                .target_cpu
                .clone()
                .unwrap_or_else(|| sess.target.cpu.as_ref().to_owned());
        }

        let bridge = self.bridge_for_session(sess);
        BridgeCodegenBackend::target_cpu(&bridge)
    }

    fn thin_lto_supported(&self) -> bool {
        // trust-cg does not implement LTO.
        false
    }

    fn has_zstd(&self) -> bool {
        false
    }

    fn print_version(&self) {
        eprintln!("trust-cg codegen backend (conservative verified fragment)");
        eprintln!("  Linked artifact: rlib with External scalar-register Rust/C functions only");
        eprintln!("  Object formats: audited AArch64/x86-64 built-in target tuples");
        eprintln!("  Analysis-only target: wasm32-unknown-unknown (--emit=mir; no Rust linker)");
    }

    fn print_passes(&self) {
        println!(
            "Trust-CG uses a fixed audited lowering and optimization pipeline; no configurable LLVM passes are available."
        );
    }

    fn replaced_intrinsics(&self) -> Vec<Symbol> {
        // trust-cg does not currently replace any intrinsics.
        vec![]
    }

    fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Box<dyn Any> {
        let crate_name = tcx.crate_name(rustc_span::def_id::LOCAL_CRATE).to_string();

        if !tcx.sess.opts.output_types.should_link() {
            // MIR is emitted by the common driver. Avoid mono collection,
            // verification, and lowering for metadata/dep-info/MIR-only work.
            return Box::new(OngoingTrustCgCodegen {
                bridge_ongoing: None,
                crate_name,
                function_count: 0,
            });
        }

        if Self::is_wasm_session(tcx.sess) {
            tcx.dcx().fatal(
                "internal trust-cg invariant violated: linked Wasm codegen passed initialization",
            );
        }

        if let Some(crate_type) =
            tcx.crate_types().iter().copied().find(|&kind| kind != CrateType::Rlib)
        {
            tcx.dcx().fatal(format!(
                "trust-cg cannot link crate type `{crate_type:?}`; the only audited linked artifact is an rlib of External scalar-register functions. Executables additionally require rustc's process-entry wrapper, and dynamic/static/proc-macro outputs require unwired linkage/visibility contracts"
            ));
        }

        let functions = build_production_mono_functions(tcx).unwrap_or_else(|reason| {
            tcx.dcx().fatal(format!(
                "trust-cg cannot faithfully materialize rustc's reachable mono-item graph: {reason}"
            ))
        });

        let function_count = functions.len();

        // Trust: #961 -- structured tracing for smoke test observability.
        tracing::info!(
            crate_name = %crate_name,
            extracted = function_count,
            "[trust_cg] MIR extraction complete"
        );

        // Trust (Step 1, trust-ir-emission): feature-gated EMISSION ADAPTER hook
        // point. The CGU's `VerifiableFunction`s are fully built here (with
        // direct-call name overrides applied), exactly the slice the bridge's
        // multi-function entry expects. Behind the off-by-default feature we
        // compose the two proven passes — MIR->VerifiableFunction (already done
        // above) and VerifiableFunction->trust_ir::Module — to materialize a
        // Module for this CGU, log the function count / any EmitError, and run
        // the fidelity oracle. This produces NO codegen output and is unreachable
        // with the feature off, so default codegen is untouched.
        #[cfg(feature = "trust-ir-emission")]
        {
            // The observational seam consumes the exact same concrete function
            // inventory as production output; maintaining a second polymorphic
            // or best-effort universe would make its fidelity result irrelevant.
            match trust_ir_emission::emit_trust_ir_module(tcx, &crate_name, &functions) {
                Ok(module) => {
                    tracing::debug!(
                        crate_name = %crate_name,
                        trust_ir_functions = module.functions.len(),
                        "[trust_cg] trust-ir emission adapter produced a Module"
                    );
                    trust_ir_emission::validate_emitted_module(&crate_name, &functions, &module);

                    // Trust (Step 2, trust-ir-codegen): OBSERVATIONAL probe of
                    // the proven Module->LIR converter on the REAL compiled
                    // functions. Log-only; never alters emission. Reachable only
                    // when the `trust-ir-codegen` feature is also enabled (it
                    // implies `trust-ir-emission`, so `module` is in hand here).
                    #[cfg(feature = "trust-ir-codegen")]
                    {
                        trust_ir_codegen::probe_module_to_lir(&crate_name, &module);
                    }
                }
                Err(e) => {
                    tracing::debug!(
                        crate_name = %crate_name,
                        error = %e,
                        "[trust_cg] trust-ir emission adapter failed (log-only; codegen unaffected)"
                    );
                }
            }
        }

        let bridge = self.bridge_for_tcx(tcx);
        let allocator_module_spec = match allocator_module_spec_for_tcx(tcx, &crate_name) {
            Ok(spec) => spec,
            Err(e) => tcx.dcx().fatal(format!("trust-cg allocator shim planning failed: {e}")),
        };

        let bridge_crate_info =
            bridge_backend::CrateInfo { crate_name: crate_name.clone(), functions };

        let mut bridge_ongoing =
            match BridgeCodegenBackend::codegen_crate(&bridge, &bridge_crate_info) {
                Ok(ongoing) => ongoing,
                Err(e) => {
                    tcx.dcx().fatal(format!("trust-cg codegen_crate failed: {e}"));
                }
            };

        if let Some(spec) = allocator_module_spec {
            if let Err(e) = bridge.attach_allocator_module_spec(bridge_ongoing.as_mut(), spec) {
                tcx.dcx().fatal(format!("trust-cg allocator shim planning failed: {e}"));
            }
        }

        // Trust: #961 -- downcast to get lowered/failure counts for diagnostics.
        if let Some(oc) = bridge_ongoing.downcast_ref::<bridge_backend::OngoingCodegen>() {
            tracing::info!(
                crate_name = %crate_name,
                lowered = oc.compiled_count(),
                failures = oc.failure_count(),
                allocator_planned = oc.allocator_module().is_some() || oc.allocator_module_spec().is_some(),
                "[trust_cg] bridge lowering complete"
            );
        }

        Box::new(OngoingTrustCgCodegen {
            bridge_ongoing: Some(bridge_ongoing),
            crate_name,
            function_count,
        })
    }

    // Trust: #959 -- join_codegen now produces meaningful CompiledModules
    // by converting bridge results and emitting LIR object artifacts to disk.
    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        sess: &Session,
        outputs: &OutputFilenames,
        _crate_info: &CrateInfo,
    ) -> (CompiledModules, WorkProductMap) {
        let ongoing = ongoing_codegen.downcast::<OngoingTrustCgCodegen>().unwrap();

        let Some(bridge_ongoing) = ongoing.bridge_ongoing else {
            return (
                CompiledModules { modules: vec![], allocator_module: None },
                WorkProductMap::default(),
            );
        };

        // Derive output directory from rustc's OutputFilenames.
        let output_path = outputs.with_extension("o");
        let out_dir =
            output_path.parent().unwrap_or_else(|| std::path::Path::new(".")).to_path_buf();

        let bridge_outputs = bridge_backend::OutputFilenames {
            out_dir: out_dir.clone(),
            crate_stem: ongoing.crate_name.clone(),
        };
        let bridge = self.bridge_for_session(sess);

        match BridgeCodegenBackend::join_codegen(&bridge, bridge_ongoing, &bridge_outputs) {
            Ok((bridge_compiled, _bridge_work_products)) => {
                // Convert bridge CompiledModules -> rustc CompiledModules.
                // Multi-function bridge modules are split into one rustc object
                // artifact per function because rustc CompiledModule carries a
                // single object path.
                let mut rustc_modules = Vec::new();

                for bridge_module in &bridge_compiled.modules {
                    if bridge_module.lir_functions.is_empty() {
                        if bridge_module.function_count != 0 {
                            sess.dcx().fatal(format!(
                                "trust-cg internal error: module `{}` reports {} functions but carries no LIR",
                                bridge_module.name, bridge_module.function_count
                            ));
                        }
                        // Type-only/empty libraries require metadata/archive
                        // handling but no fabricated machine-code object.
                        continue;
                    }
                    rustc_modules.extend(self.emit_rustc_modules_for_bridge_module(
                        &bridge,
                        bridge_module,
                        sess,
                        outputs,
                    ));
                }

                // Convert allocator module if present.
                let allocator_module = bridge_compiled.allocator_module.as_ref().map(|alloc_mod| {
                    self.emit_rustc_allocator_module_for_bridge_module(
                        &bridge, alloc_mod, sess, outputs,
                    )
                });

                let compiled = CompiledModules { modules: rustc_modules, allocator_module };

                sess.dcx().note(format!(
                    "trust-cg: compiled {} function(s) in {} module(s)",
                    ongoing.function_count,
                    compiled.modules.len()
                ));

                (compiled, WorkProductMap::default())
            }
            Err(e) => {
                sess.dcx().fatal(format!("trust-cg join_codegen failed: {e}"));
            }
        }
    }

    // Trust: #959 -- the audited rlib lane delegates archive construction and
    // metadata packaging to rustc's standard link_binary(). Other linked crate
    // types are rejected before codegen. The compiled modules carry object file
    // paths from join_codegen.
    fn link(
        &self,
        sess: &Session,
        compiled_modules: CompiledModules,
        crate_info: CrateInfo,
        metadata: EncodedMetadata,
        outputs: &OutputFilenames,
    ) {
        link_binary(
            sess,
            &ArArchiveBuilderBuilder,
            compiled_modules,
            crate_info,
            metadata,
            outputs,
            self.name(),
        );
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
