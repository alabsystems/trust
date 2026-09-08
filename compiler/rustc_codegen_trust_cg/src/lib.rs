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

// Trust (F1, trust-ir-frontend): the CONSUMER of `trust_ir_of`. Unlike the two
// modules above it is NOT feature-gated — it is selected at run time by
// `-Ztrust-cg-frontend=trust-ir`, off by default. A cargo feature could not be
// varied per invocation, so it could not support the one claim this work has to
// make good on: that the DEFAULT path is byte-identical, proved by diffing two
// objects out of the SAME compiler binary.
mod trust_ir_frontend;

use std::any::Any;
use std::fs;

use rustc_abi::{BackendRepr, CanonAbi, ExternAbi};
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
        //
        // ONE OBJECT PER CGU. Emission is per codegen unit, not per function: an
        // `Internal`-linkage mono-item is a LOCAL symbol, unreachable from any
        // other object, so a per-function split cannot represent it (and every
        // program that calls `core` has such items). The per-function PROOF is
        // untouched — the gate still verifies each function in isolation — and
        // the merge carries one additional, checked obligation: each verified
        // function's bytes appear VERBATIM in the shipped object at the offset
        // that object's own symbol table assigns it. A violation is a REFUSAL.
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
        let module_object =
            run_module_output_preservation_gate(bridge, bridge_module, sess, gate_mode);

        // The bytes written below are, per function, the exact bytes the gate
        // verified: `emit_module_object_verified_reported_with_backend` refuses
        // the whole module unless every verified function's machine code appears
        // VERBATIM in this artifact at the offset the artifact's own symbol table
        // assigns it. There is no separate re-emission to reconcile.
        if module_object.bytes.is_empty() {
            sess.dcx().fatal(format!(
                "trust-cg: object emission for `{}` produced an empty artifact",
                bridge_module.name
            ));
        }

        let object_path = outputs.temp_path_for_cgu(OutputType::Object, &bridge_module.name);
        if let Err(e) = fs::write(&object_path, &module_object.bytes) {
            sess.dcx().fatal(format!(
                "trust-cg: failed to write object for `{}`: {e}",
                bridge_module.name
            ));
        }

        vec![CompiledModule {
            name: bridge_module.name.clone(),
            kind: ModuleKind::Regular,
            object: Some(object_path),
            global_asm_object: None,
            dwarf_object: None,
            bytecode: None,
            assembly: None,
            llvm_ir: None,
            links_from_incr_cache: Vec::new(),
        }]
    }

    /// Trust (F1): `codegen_crate` for `-Ztrust-cg-frontend=trust-ir`.
    ///
    /// The shipped path builds `VerifiableFunction`s from MIR and never asks
    /// for the trust-ir the producer already makes. This one does the opposite:
    /// it forces `tcx.trust_ir_of` for every reachable mono-item and routes each
    /// resulting `trust_ir::Module` through `trust_cg_bridge::lower_module_to_lir`,
    /// into the SAME object emitter. That is the whole of F1's missing consumer.
    ///
    /// It is FAIL-CLOSED at every joint and there is no MIR fallback anywhere in
    /// it. Refusals are ACCUMULATED rather than short-circuited — one run then
    /// reports the complete per-item work list, which is the measurement this
    /// path exists to produce — but the compilation still ERRORS. A flag that
    /// quietly fell back to MIR would tell you nothing, which is exactly why the
    /// earlier log-only probe never measured F1.
    fn codegen_crate_from_trust_ir<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        crate_name: String,
    ) -> Box<dyn Any> {
        let sess = tcx.sess;

        // (1) The PRODUCER has to be running. `trust_ir_of` returns `None` for
        // every body unless the direct frontend is enabled, and `None` is a
        // refusal here — so without this check the flag's only observable effect
        // would be "everything is refused", which reads like a coverage result
        // and is actually a missing flag.
        if !sess.trust_ir_lower_enabled() {
            tcx.dcx().fatal(
                "-Ztrust-cg-frontend=trust-ir requires the direct source (THIR) -> trust-ir \
                 producer: pass -Ztrust-ir-lower, or leave batteries-on verification on. \
                 Without it `trust_ir_of` declines every body and this frontend, which never \
                 falls back to MIR, has nothing to compile",
            );
        }

        // (2) THE M-POS PROVEN-OUTPUT GATE NOW RUNS ON THIS PATH. It used to be
        // structurally impossible: the gate derived a function's intended
        // semantics from a `VerifiableFunction`, which this frontend never
        // builds, so any non-`off` gate mode was a hard error here.
        //
        // `trust_cg_bridge::verify_output_trust_ir` supplies the missing half —
        // a specification derived from the PRODUCER's `trust_ir::Function`,
        // discharged against the EMITTED BYTES by the same machine-side
        // executor. The refusal is therefore gone, and the emission path
        // (`emit_rustc_module_for_trust_ir_module`) runs the gate.
        //
        // WHAT IS NOT RELAXED: `source_functions` is still `None` on this
        // module, and that `None` must never again read as "nothing to verify".
        // The trust-ir work list is carried SEPARATELY and the emission path
        // FATALS if it is absent or not 1:1 with the LIR — a module cannot reach
        // the linker by having no spec.
        let gate_mode = output_gate_mode(sess);

        // (3) THE SAME INVENTORY the production path compiles — same collection,
        // same linkage/visibility gate, same ordering.
        let (instances, reachable_statics) =
            collect_production_mono_instances(tcx).unwrap_or_else(|reason| {
                tcx.dcx().fatal(format!(
                    "trust-cg cannot faithfully materialize rustc's reachable mono-item graph: \
                     {reason}"
                ))
            });
        let reachable = instances.len();

        // (4) The allocator shim is SYNTHESIZED by the backend from a rustc
        // spec, not lowered from any source body, so there is no `trust_ir_of`
        // artifact for it. Refuse rather than emit a MIR-path shim beside
        // trust-ir functions and call the result an F1 artifact.
        match allocator_module_spec_for_tcx(tcx, &crate_name) {
            Ok(None) => {}
            Ok(Some(_)) => tcx.dcx().fatal(
                "-Ztrust-cg-frontend=trust-ir does not build the rustc allocator shim: the shim \
                 is synthesized from a rustc spec rather than lowered from a source body, so no \
                 `trust_ir_of` artifact exists for it",
            ),
            Err(e) => tcx.dcx().fatal(format!("trust-cg allocator shim planning failed: {e}")),
        }

        // (5) SOURCE -> `trust_ir_of` -> LIR, per reachable item.
        let mut lowered = Vec::with_capacity(reachable);
        let mut linkage = Vec::with_capacity(reachable);
        let mut refusals: Vec<String> = Vec::new();
        for (_symbol, instance, item_linkage) in instances {
            match trust_ir_frontend::lower_instance(
                tcx,
                instance,
                validate_codegen_instance_abi_trust_ir,
            ) {
                Ok(function) => {
                    lowered.push(function);
                    linkage.push(item_linkage);
                }
                Err(refusal) => refusals.push(refusal.to_string()),
            }
        }

        tracing::info!(
            crate_name = %crate_name,
            reachable,
            completed = lowered.len(),
            refused = refusals.len(),
            "[trust_cg] trust-ir frontend: source -> trust_ir_of -> lower_module_to_lir"
        );
        sess.dcx().note(format!(
            "trust-cg trust-ir frontend: {}/{reachable} reachable function(s) completed \
             source -> trust_ir_of -> lower_module_to_lir",
            lowered.len()
        ));

        if !refusals.is_empty() {
            let listed = refusals.iter().map(|r| format!("  {r}")).collect::<Vec<_>>().join("\n");
            tcx.dcx().fatal(format!(
                "-Ztrust-cg-frontend=trust-ir refused {} of {reachable} reachable function(s); \
                 this frontend never falls back to the MIR path:\n{listed}",
                refusals.len()
            ));
        }

        if lowered.is_empty() {
            // A linking compilation with no functions is the MIR path's
            // "type-only library" case, which it handles by emitting no object.
            return Box::new(OngoingTrustCgCodegen {
                bridge_ongoing: None,
                trust_ir_module: None,
                trust_ir_gate_sources: Vec::new(),
                crate_name,
                function_count: 0,
            });
        }

        let function_count = lowered.len();
        let (module, gate_sources) =
            trust_ir_frontend::compiled_module(
                &crate_name,
                lowered,
                linkage,
                reachable_statics
                    .into_iter()
                    .map(ProductionStatic::into_object_global)
                    .collect(),
            )
            .unwrap_or_else(
                |reason| {
                    tcx.dcx().fatal(format!(
                        "trust-cg: refusing to emit a trust-ir codegen unit for `{crate_name}`: \
                         {reason}"
                    ))
                },
            );
        let _ = gate_mode;
        Box::new(OngoingTrustCgCodegen {
            bridge_ongoing: None,
            trust_ir_module: Some(module),
            trust_ir_gate_sources: gate_sources,
            crate_name,
            function_count,
        })
    }

    /// Trust (F1): emit the object for a codegen unit the trust-ir frontend
    /// produced.
    ///
    /// THE GATE RUNS HERE. `sources` is the trust-ir work list the frontend
    /// carried alongside the LIR; `verify_output_trust_ir` derives each
    /// function's specification from it and discharges that specification
    /// against the EMITTED BYTES. The bytes written below are, per function, the
    /// exact bytes the gate verified: the module gate refuses unless every
    /// verified function's machine code appears VERBATIM in this artifact at the
    /// offset the artifact's own symbol table assigns it.
    ///
    /// FAIL-CLOSED, and specifically NOT in the shape the old
    /// `source_functions: None` hole had: an absent or mis-sized work list is a
    /// FATAL error, never an "ungated" emission. The only way to emit here
    /// without a proof is the explicit `-Ztrust-cg-output-gate=off`
    /// acknowledgement, which prints that the bytes are unverified.
    fn emit_rustc_module_for_trust_ir_module(
        &self,
        bridge: &BridgeBackend,
        bridge_module: &bridge_backend::CompiledModule,
        sources: &[trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource],
        sess: &Session,
        outputs: &OutputFilenames,
    ) -> CompiledModule {
        use trust_cg_bridge::verify_output::EmitPolicy;
        use trust_cg_bridge::verify_output_trust_ir::{
            emit_trust_ir_module_object_unverified, emit_trust_ir_module_object_verified,
        };

        let gate_mode = output_gate_mode(sess);

        // THE WORK LIST IS NOT OPTIONAL. A trust-ir module whose spec list is
        // missing or not 1:1 with its LIR cannot be gated, and "cannot be gated"
        // is a compile error on this path — never a quiet ungated emission.
        if sources.len() != bridge_module.lir_functions.len() {
            sess.dcx().fatal(format!(
                "trust-cg internal error: trust-ir module `{}` carries {} LIR function(s) but \
                 {} gate specification(s); refusing to emit bytes the gate cannot be matched to",
                bridge_module.name,
                bridge_module.lir_functions.len(),
                sources.len()
            ));
        }
        for (index, source) in sources.iter().enumerate() {
            if source.symbol != bridge_module.lir_functions[index].name {
                sess.dcx().fatal(format!(
                    "trust-cg internal error: trust-ir module `{}` position {index} ships LIR \
                     for `{}` but carries a specification for `{}`; refusing to verify one \
                     function and emit another",
                    bridge_module.name, bridge_module.lir_functions[index].name, source.symbol
                ));
            }
        }

        let bytes = if gate_mode == OutputGateMode::Off {
            // EXPLICIT acknowledgement. `-Ztrust-cg-output-gate=off` (which
            // itself refuses to combine with batteries-on strict verification)
            // is the only way to get bytes out of this path unproven, and it
            // says so on every such compilation.
            let emitted =
                match emit_trust_ir_module_object_unverified(sources, bridge_module, bridge) {
                    Ok(emitted) => emitted,
                    Err(e) => sess.dcx().fatal(format!(
                        "trust-cg: failed to emit object for trust-ir module `{}`: {e}",
                        bridge_module.name
                    )),
                };
            sess.dcx().note(format!(
                "trust-cg: module `{}` was emitted by the TRUST-IR FRONTEND with the \
                 proven-output gate explicitly DISABLED (-Ztrust-cg-output-gate=off) — its {} \
                 function(s) carry NO output-preservation proof",
                bridge_module.name, bridge_module.function_count
            ));
            emitted.bytes
        } else {
            let policy = match gate_mode {
                OutputGateMode::Strict => EmitPolicy::StrictProvenOnly,
                // This arm is an explicit allow-unknown opt-in; Off returned above.
                _ => EmitPolicy::AllowUnknown,
            };
            match emit_trust_ir_module_object_verified(
                sources,
                &bridge_module.linkage,
                &bridge_module.statics,
                policy,
                bridge,
            ) {
                Ok((module_object, report)) => {
                    sess.dcx().note(format!(
                        "trust-cg TRUST-IR certification report for module `{}`: {} ({}); \
                         {} function(s) byte-preserved into one object",
                        bridge_module.name,
                        report,
                        policy_label(policy),
                        module_object.preserved.len()
                    ));
                    module_object.bytes
                }
                Err(e) => sess.dcx().fatal(format!(
                    "trust-cg: REFUSING to emit trust-ir module `{}` — the in-compiler \
                     proven-output gate rejected it: {e}",
                    bridge_module.name
                )),
            }
        };

        if bytes.is_empty() {
            sess.dcx().fatal(format!(
                "trust-cg: object emission for `{}` produced an empty artifact",
                bridge_module.name
            ));
        }

        let object_path = outputs.temp_path_for_cgu(OutputType::Object, &bridge_module.name);
        if let Err(e) = fs::write(&object_path, &bytes) {
            sess.dcx().fatal(format!(
                "trust-cg: failed to write object for `{}`: {e}",
                bridge_module.name
            ));
        }

        CompiledModule {
            name: bridge_module.name.clone(),
            kind: ModuleKind::Regular,
            object: Some(object_path),
            global_asm_object: None,
            dwarf_object: None,
            bytecode: None,
            assembly: None,
            llvm_ir: None,
            links_from_incr_cache: Vec::new(),
        }
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

/// Trust (F1): which producer supplies the backend's per-function input.
///
/// `Mir` is the shipped path and the default. `TrustIr` is the source-first F1
/// path: `trust_ir_of` -> `trust_cg_bridge::lower_module_to_lir` -> object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TrustCgFrontend {
    Mir,
    TrustIr,
}

#[allow(rustc::bad_opt_access)]
fn trust_cg_frontend(sess: &Session) -> TrustCgFrontend {
    match trust_cg_frontend_from_name(&sess.opts.unstable_opts.trust_cg_frontend) {
        Ok(frontend) => frontend,
        Err(reason) => sess.dcx().fatal(reason),
    }
}

fn trust_cg_frontend_from_name(frontend: &str) -> Result<TrustCgFrontend, &'static str> {
    match frontend {
        "mir" => Ok(TrustCgFrontend::Mir),
        "trust-ir" => Ok(TrustCgFrontend::TrustIr),
        _ => Err("invalid -Ztrust-cg-frontend value reached the trust-cg backend"),
    }
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

/// Run the proven-output gate over a bridge module's source functions and
/// return THE ONE OBJECT this codegen unit ships.
///
/// On a Refuted (miscompile) verdict, a policy-refused Unknown, or a violated
/// merge obligation, this calls `sess.dcx().fatal(..)` and codegen aborts — no
/// object is written.
///
/// Trust (RUNG 2, module form): the returned bytes ARE the bytes the gate
/// verified. Each function is still proved in ISOLATION, exactly as before; what
/// the module form adds is the discharged claim that this artifact carries each
/// of those verified instruction streams verbatim, at the offset its own symbol
/// table assigns. There is no second emission to reconcile against.
fn run_module_output_preservation_gate(
    bridge: &BridgeBackend,
    bridge_module: &bridge_backend::CompiledModule,
    sess: &Session,
    mode: OutputGateMode,
) -> trust_cg_bridge::verify_output::VerifiedModuleObject {
    use trust_cg_bridge::verify_output::{
        EmitPolicy, VerifiedModuleObject, emit_module_object_verified_reported_with_backend,
    };

    // Emit WITHOUT the gate. Reachable only when the gate is explicitly `off`,
    // or for a synthesized module that carries no source functions to verify
    // (e.g. an allocator shim); both already refuse strict mode elsewhere.
    let ungated = |reason: &str| -> VerifiedModuleObject {
        match bridge.emit_module_object(bridge_module) {
            Ok(emitted) => {
                tracing::debug!(
                    module = %bridge_module.name,
                    reason,
                    "[trust_cg] module object emitted without the proven-output gate"
                );
                VerifiedModuleObject { bytes: emitted.bytes, preserved: Vec::new() }
            }
            Err(e) => sess.dcx().fatal(format!(
                "trust-cg: failed to emit object for `{}`: {e}",
                bridge_module.name
            )),
        }
    };

    if mode == OutputGateMode::Off {
        return ungated("gate disabled");
    }
    let Some(sources) = bridge_module.source_functions.as_ref() else {
        return ungated("module carries no source functions");
    };
    if sources.is_empty() {
        return ungated("module carries no source functions");
    }

    let policy = match mode {
        OutputGateMode::Strict => EmitPolicy::StrictProvenOnly,
        // This arm is an explicit allow-unknown opt-in; Off returned above.
        _ => EmitPolicy::AllowUnknown,
    };

    // The gate emits each function to bytes ONCE, discharges output-preservation
    // against the auto-derived IR semantics over THOSE bytes, and returns them.
    // A Refuted function is rejected under every policy; an Unknown one only
    // under StrictProvenOnly. It then merges the CGU into one object and REFUSES
    // unless every verified function's bytes survived the merge unchanged.
    //
    // Trust (RUNG 3 — CERTIFICATION REPORT): the gate also returns a per-module
    // tally of the output-preservation GRADE assigned each emitted function
    // ([PROVED] / [VALIDATED] / uncertified). We surface it as a stderr note so
    // the UNCERTIFIED surface is VISIBLE — a function that ships without a
    // kernel-re-checkable proof is COUNTED and reported, never silently treated
    // as if covered. (Under StrictProvenOnly only kernel-[PROVED] functions ship;
    // [VALIDATED] and Unknown are refused, landing in the Err arm below.)
    match emit_module_object_verified_reported_with_backend(
        sources,
        &bridge_module.linkage,
        &bridge_module.statics,
        policy,
        bridge,
    ) {
        Ok((module_object, report)) => {
            sess.dcx().note(format!(
                "trust-cg certification report for module `{}`: {} ({}); \
                 {} function(s) byte-preserved into one object",
                bridge_module.name,
                report,
                policy_label(policy),
                module_object.preserved.len()
            ));
            module_object
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
            "policy: allow-unknown (explicit opt-in: emits unproven, Refuted fatal)"
        }
    }
}

/// Whether the caller's frontend models a fieldless enum's carrier width.
///
/// This is NOT a policy knob. It records a measured asymmetry between the two
/// frontends, and it exists because `scalar_register_abi_ty_supported` is
/// SHARED by both: widening it widens admission on the default MIR path too.
///
/// * `Admit` — the trust-ir (F1) frontend. Its converter and its gate both read
///   the carrier width from ONE function, `module_to_lir::fieldless_enum_carrier`,
///   which takes it from the producer's `EnumLayoutDescriptor` — filled by
///   `trust_thir_lower` from rustc's own layout query and emitted as `Direct`
///   only when the def's canonical tag repr equals rustc's tag scalar.
/// * `Refuse` — the MIR frontend, which has NO access to that descriptor.
///   Measured: `ty_convert::lower_enum_adt` hardcodes the `__tag` field as
///   `Int { width: pointer_width(tcx), signed: true }` (64-bit signed on
///   aarch64), `mapping::map_type` discards `enum_layout` into
///   `LirType::Struct`, and `verify_output::reg_width` has no ADT arm and
///   falls through to 32. For `enum Three { X, Y, Z }` that is three live
///   widths — rustc 8, LIR 64, gate 32 — against rustc's `i8` tag.
///
/// Today `trust_mir_extract::codegen_ty_issue` rejects `Ty::Adt` unconditionally,
/// so the MIR path never reaches those three consumers. That barrier lives in
/// another crate and is maintained for layout fidelity, not for this: it makes
/// the widening unreachable, not sound. This enum makes the boundary explicit
/// where the risk is, rather than depending on a distant invariant holding.
///
/// Measured cost of refusing on the MIR path: ZERO. Across 35 enum shapes and a
/// 2,293-crate registry sweep, the MIR path ships no fieldless enum either way.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EnumAbi {
    Admit,
    Refuse,
}

fn scalar_register_abi_ty_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>, enum_abi: EnumAbi) -> bool {
    let PassMode::Direct(attrs) = &arg.mode else {
        return false;
    };
    // InReg and integer extension are observable caller/callee contracts. The
    // current bridge carries neither attribute into LIR/object emission.
    //
    // These two are the COMPLETE set of `ArgAttributes` that change how a value
    // is passed, and that is rustc's own statement, not an inference: `ArgAttributes::eq_abi`
    // (compiler/rustc_target/src/callconv/mod.rs) compares exactly `InReg` and
    // `arg_ext` and says of the rest "Everything else is things like noalias,
    // dereferenceable, nonnull, ...". So `NonNull | NoUndef` — the attributes a
    // `&T` argument carries, and the ones that made the refusal message for a
    // reference look ABI-shaped — are UB/optimization metadata about a value
    // already placed by the mode, not placement or representation contracts.
    if attrs.contains(ArgAttribute::InReg) || attrs.arg_ext != ArgExtension::None {
        return false;
    }
    if arg.layout.size.bits() == 0 || arg.layout.size.bits() > 64 {
        return false;
    }
    match arg.layout.ty.kind() {
        ty::Bool | ty::Int(_) | ty::Uint(_) => true,
        // A THIN SHARED REFERENCE is one pointer-sized integer register, passed
        // exactly like a `usize`.
        //
        // A wide reference never reaches this arm, but NOT for the reason it is
        // tempting to write down. MEASURED on aarch64-apple-darwin (stage1
        // trustc, `fn f(e: &[u64]) -> usize`): `&[u64]` arrives as
        // `PassMode::Cast { cast: CastTarget { rest: Uniform { unit: Integer(8),
        // total: Size(16) } } }` — NOT `PassMode::Pair`. So what excludes it is
        // the `let PassMode::Direct(attrs) = &arg.mode` guard at the top of this
        // function, which the target-specific `Pair`-vs-`Cast` choice cannot get
        // past either way. The `BackendRepr::Scalar` test below is therefore a
        // defence-in-depth CHECK of thinness, not the thing doing the excluding;
        // it is kept so a future `Direct`-mode aggregate cannot slip through.
        //
        // Deliberately NOT widened to `&mut T` or `*mut T`: those admit writes
        // through the pointer, and the verification fragment on the other side of
        // this gate covers reads of caller memory only (`Clean.BVC.selectAddrCong`
        // under a no-store body). Keeping the two boundaries aligned means a
        // program this gate admits is one the verifier can still speak about.
        ty::Ref(_, _, mir::Mutability::Not) => {
            matches!(arg.layout.backend_repr, BackendRepr::Scalar(_))
        }
        // A `char` IS one 32-bit unsigned integer register. It reaches this arm
        // with `PassMode::Direct` and `arg_ext: None` — MEASURED on
        // aarch64-apple-darwin: `fn f(a: char)` yields
        // `Direct(ArgAttributes { regular: NoUndef, arg_ext: None, .. })` — so
        // the caller owes nothing above the declared 32 bits and nothing below
        // them is re-encoded. The `Size(32 bits)` test is not decoration: it
        // PINS rustc's side of the width to the 32 the two consumers hardcode
        // (`module_to_lir::map_scalar_int_ty` maps `Ty::Char` to `LirType::I32`,
        // and `verify_output_trust_ir::scalar_reg_width` reads it at 32), so the
        // slot the emitter writes and the slot the gate models are the same slot
        // by construction rather than by coincidence.
        //
        // `NoUndef` plus char's validity range (a scalar Unicode value) is a
        // property of the VALUE, not of its placement — the same category as the
        // `NonNull | NoUndef` on the `&T` arm above, which this backend has
        // always admitted for exactly that reason.
        ty::Char => {
            matches!(arg.layout.backend_repr, BackendRepr::Scalar(_))
                && arg.layout.size.bits() == 32
        }
        // A FIELDLESS (C-like) enum: every variant carries zero fields, so the
        // value IS its discriminant tag and rustc lays the whole type out as ONE
        // integer scalar. `#[derive]`-free `enum Round { Up, Down }`-shaped types
        // are the largest admissible family in the refusal census of real crates.
        //
        // What makes this exact rather than hopeful:
        //
        // * `BackendRepr::Scalar(Int)` is checked here, so rustc itself says the
        //   whole value is one integer register — a payload-carrying or
        //   niche-spread enum has a different `BackendRepr` and never gets here.
        // * `arg_ext == None` was already required above. That is what excludes
        //   the 2-variant 0/1 tag, which rustc classifies `Scalar::is_bool()` and
        //   marks `Zext` (MEASURED on `hashbrown::raw::Fallibility`): its caller
        //   contract is an extension promise this backend does not carry into
        //   LIR, so it stays refused, exactly like `bool`.
        // * The size bound above (`> 64` refused) keeps it inside one register.
        // * The consumers do NOT guess the tag's width. `module_to_lir::
        //   fieldless_enum_carrier` derives it from the producer's
        //   `EnumLayoutDescriptor`, which `trust_thir_lower` fills from rustc's
        //   OWN layout query and only emits as `Direct` when the def's canonical
        //   tag repr equals rustc's tag scalar — so the LIR carrier and the gate's
        //   read width are rustc's tag type. The SAME function is the gate's
        //   width rule, so there is one derivation, not two. THAT IS TRUE OF THE
        //   TRUST-IR FRONTEND ONLY, which is why this arm is gated on `EnumAbi`:
        //   the MIR path has three other derivations and reads none of them from
        //   the descriptor. See `EnumAbi` above.
        // * VALUE validity (`NoUndef` over the discriminant range) is discharged
        //   downstream, not assumed: the converter admits an enum type at only
        //   four sites — signature, block parameters and `Inst::Const` — and
        //   refuses an enum-typed constant whose tag is not a DECLARED
        //   discriminant, so a function that gets past it can only ever return a
        //   declared tag or a tag its own caller supplied.
        ty::Adt(def, _)
            if enum_abi == EnumAbi::Admit
                && def.is_enum()
                && def.variants().iter().all(|v| v.fields.is_empty()) =>
        {
            matches!(
                arg.layout.backend_repr,
                BackendRepr::Scalar(rustc_abi::Scalar::Initialized {
                    value: rustc_abi::Primitive::Int(..),
                    ..
                })
            )
        }
        _ => false,
    }
}

fn ignored_return_abi_ty_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    matches!(arg.mode, PassMode::Ignore)
        && match arg.layout.ty.kind() {
            ty::Never => true,
            ty::Tuple(fields) => fields.is_empty(),
            _ => false,
        }
}

/// A `bool` RETURN, admitted with its `Zext` extension contract — RETURN
/// POSITION ONLY.
///
/// `scalar_register_abi_ty_supported` refuses every `arg_ext != None` because
/// the extension is an observable caller/callee contract the bridge does not
/// carry as an attribute. For a `bool` RETURN specifically, the contract is
/// DISCHARGED BY PROOF rather than carried: the trust-ir gate models a `Bool`
/// return at 32 bits (`verify_output_trust_ir::scalar_reg_width` — "cset
/// writes exactly 0 or 1 into the whole register, so reading it at 32 bits is
/// exact"), so the byte-level equality obligation REQUIRES the emitted
/// function to leave 0/1 zero-extended in w0 — an emission that violated the
/// Zext contract would be Refuted, not shipped. The converter's side of the
/// slot is pinned too (`module_to_lir::map_scalar_int_ty` maps `Ty::Bool` to
/// the byte-wide `LirType::I8` whose value-production set — cset, movz 0/1,
/// csel of 0/1, byte ldrb — is zero-extended by construction on AArch64).
///
/// Bool PARAMETERS stay refused: the gate's spec side deliberately rejects
/// `Bool` in parameter position (`sig_position_width`), so admitting them here
/// would create an admission the prover cannot speak about — the exact
/// mismatch this validator exists to prevent.
/// A SHARED SLICE REFERENCE argument (`&[T]`), admitted in ARGUMENT position
/// on the trust-ir lane only.
///
/// MEASURED on aarch64-apple-darwin (stage1 trustc, trust-index
/// `capped_len(&[u8], ..)`): `&[u8]` arrives as `PassMode::Pair(ArgAttributes
/// { regular: NonNull | NoUndef, arg_ext: None, .. }, ..)` — a ScalarPair of
/// (data pointer, length) in two consecutive GPR slots, bit-for-bit the
/// (data, len) split the trust-ir converter emits for a `FatPtr(Slice)`
/// formal. (An older note on the `&T` arm records `&[u64]` arriving as
/// `PassMode::Cast`/Uniform — the mode rustc picks has drifted; this helper
/// matches what THIS tree emits.) The NonNull/NoUndef attributes are value
/// metadata, not placement contracts, exactly as the admitted `&T` arm
/// argues; `InReg` or any integer extension refuses. `&mut [T]` is
/// deliberately NOT admitted (writes through the pointer are outside the
/// read-only incoming-root memory lane), and `&str` waits for its own
/// measurement.
fn slice_ref_arg_abi_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    let ty::Ref(_, inner, mir::Mutability::Not) = arg.layout.ty.kind() else {
        return false;
    };
    if !matches!(inner.kind(), ty::Slice(_)) {
        return false;
    }
    let PassMode::Pair(a, b) = &arg.mode else {
        return false;
    };
    let attrs_ok = |attrs: &rustc_target::callconv::ArgAttributes| {
        !attrs.contains(ArgAttribute::InReg) && attrs.arg_ext == ArgExtension::None
    };
    attrs_ok(a) && attrs_ok(b) && arg.layout.size.bits() == 128
}

/// A BY-VALUE struct argument passed INDIRECTLY (rustc's hidden pointer),
/// as the trust-ir converter's >16-byte struct-formal lane expects: the
/// formal is one I64 (the pointer), and field reads go through it at the
/// producer-recorded offsets. Admitted only when rustc's mode is a plain
/// non-stack `Indirect` with no metadata — the exact shape whose machine
/// calling convention IS "one pointer in the next GPR". The converter
/// independently refuses any instance whose struct lacks the full recorded
/// layout, so admission here can never outrun the layout evidence.
fn indirect_by_value_struct_arg_abi_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    let ty::Adt(adt, _) = arg.layout.ty.kind() else {
        return false;
    };
    if !adt.is_struct() {
        return false;
    }
    let PassMode::Indirect { attrs, meta_attrs: None, on_stack: false } = &arg.mode else {
        return false;
    };
    !attrs.contains(ArgAttribute::InReg)
        && attrs.arg_ext == ArgExtension::None
        && arg.layout.size.bytes() > 16
}

/// A BY-VALUE 2-scalar-field struct argument riding `PassMode::Pair` — the
/// `Range<usize>` shape. The converter emits two register formals in layout
/// order and maps extracts by declaration index; admission here mirrors the
/// slice pair's plain-attribute checks and additionally demands a genuine
/// ScalarPair repr, so the two register scalars ARE the two fields.
fn pair_struct_arg_abi_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    let ty::Adt(adt, _) = arg.layout.ty.kind() else {
        return false;
    };
    if !adt.is_struct() {
        return false;
    }
    let PassMode::Pair(a, b) = &arg.mode else {
        return false;
    };
    let attrs_ok = |attrs: &rustc_target::callconv::ArgAttributes| {
        !attrs.contains(ArgAttribute::InReg) && attrs.arg_ext == ArgExtension::None
    };
    attrs_ok(a)
        && attrs_ok(b)
        && matches!(arg.layout.backend_repr, BackendRepr::ScalarPair(..))
        && arg.layout.size.bytes() <= 16
}

/// A BY-VALUE single-field newtype struct riding `PassMode::Direct` as its
/// field scalar — the `RangeFrom<usize>`/`RangeTo<usize>` argument shape. The
/// converter binds one formal of the field's type; a genuine Scalar repr with
/// plain attributes is demanded so the register value IS the field.
fn direct_newtype_struct_arg_abi_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    let ty::Adt(adt, _) = arg.layout.ty.kind() else {
        return false;
    };
    if !adt.is_struct() {
        return false;
    }
    let PassMode::Direct(attrs) = &arg.mode else {
        return false;
    };
    !attrs.contains(ArgAttribute::InReg)
        && attrs.arg_ext == ArgExtension::None
        && matches!(arg.layout.backend_repr, BackendRepr::Scalar(_))
}

/// A small Direct-tagged enum riding `PassMode::Pair` — `Option<u64>`-class
/// values as (tag, payload) register pairs, argument or return. The converter
/// splits the value into two lanes with the producer-recorded Direct{0}
/// descriptor; a genuine ScalarPair repr with plain attributes is demanded so
/// the two register scalars ARE (tag, payload) in that order. Niche-encoded
/// Options (`Option<&T>`) are NOT ScalarPair-with-a-tag — their single-scalar
/// or niched pair modes fail these checks and stay refused.
fn pair_enum_abi_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    let ty::Adt(adt, _) = arg.layout.ty.kind() else {
        return false;
    };
    if !adt.is_enum() {
        return false;
    }
    let PassMode::Pair(a, b) = &arg.mode else {
        return false;
    };
    let attrs_ok = |attrs: &rustc_target::callconv::ArgAttributes| {
        !attrs.contains(ArgAttribute::InReg) && attrs.arg_ext == ArgExtension::None
    };
    // A niche encoding never yields `Variants::Multiple` with a plain
    // ScalarPair(Initialized tag, payload); require an INITIALIZED first
    // scalar so a niched pair (whose "tag" lane is the payload itself) is
    // refused. The converter's own Direct{tag_offset:0} descriptor check is
    // the second, independent guard.
    let tag_initialized = match arg.layout.backend_repr {
        BackendRepr::ScalarPair(t, _) => {
            matches!(t, rustc_abi::Scalar::Initialized { .. })
        }
        _ => false,
    };
    attrs_ok(a) && attrs_ok(b) && tag_initialized && arg.layout.size.bytes() <= 16
}

fn zext_bool_return_abi_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    let PassMode::Direct(attrs) = &arg.mode else {
        return false;
    };
    matches!(arg.layout.ty.kind(), ty::Bool)
        && !attrs.contains(ArgAttribute::InReg)
        && attrs.arg_ext == ArgExtension::Zext
        && arg.layout.size.bits() == 8
        && matches!(arg.layout.backend_repr, BackendRepr::Scalar(_))
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
        "aarch64-apple-darwin" | "aarch64-unknown-linux-gnu" | "aarch64-unknown-linux-musl" => {
            Some(8)
        }
        "x86_64-apple-darwin" | "x86_64-unknown-linux-gnu" | "x86_64-unknown-linux-musl" => Some(6),
        "x86_64-pc-windows-msvc" | "x86_64-pc-windows-gnu" => Some(4),
        _ => None,
    }
}

/// Admit only the exact ABI fragment the bridge materializes today: Rust or C,
/// non-variadic/non-unwinding functions whose explicit arguments and result are
/// single integer registers of at most 64 bits (or a unit/never result). This is
/// checked for definitions and every direct callee, so an LLVM-built dependency
/// cannot silently introduce an incompatible hidden/pass-mode contract.
fn validate_codegen_instance_abi_with<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    mir_arg_count: usize,
    enum_abi: EnumAbi,
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
    // The register-count cap is a MIR-lane boundary only. The AArch64 ISel
    // implements incoming AND outgoing stack-argument placement for scalars
    // (`AppleAArch64ABI::classify_params_with` -> `ArgLocation::Stack`, with
    // the Darwin natural-packing vs AAPCS64 8-byte-slot rule localized in
    // `place_scalar_stack_arg`, and the formal side loading via
    // `IncomingArg(offset)`), so on the F1 lane a 9th scalar argument is a
    // represented placement, not a guess. The trust-ir gate's argument binding
    // still models the 8-register fragment only and fail-closes (Unknown) on
    // more — so a stack-arg function is emitted UNCERTIFIED under
    // allow-unknown and refused under strict until the gate learns to bind
    // spec parameters 9+ to the machine's initial memory at the classifier's
    // own offsets. Completeness now, proof coverage next; never a silent
    // wrong-ABI emission (the MIR lane keeps its cap — its evidence lanes
    // never measured stack placement).
    if fn_abi.args.len() > register_arg_limit && !matches!(enum_abi, EnumAbi::Admit) {
        return Err(format!(
            "{} arguments exceed target `{target_triple}`'s {register_arg_limit} scalar integer argument registers; stack-argument placement is not represented on this lane",
            fn_abi.args.len()
        ));
    }
    for (index, arg) in fn_abi.args.iter().enumerate() {
        // The `&[T]` widening rides the trust-ir lane only: the converter
        // splits a slice formal into (data, len) I64 params at the same two
        // GPR slots the Cast/Uniform ABI assigns, and reads through the data
        // pointer are the read-only incoming-root memory lane. The MIR lane
        // keeps refusing (its converter has no fat-param story).
        let slice_ok = matches!(enum_abi, EnumAbi::Admit) && slice_ref_arg_abi_supported(arg);
        // The by-value indirect struct formal rides the trust-ir lane only,
        // like the slice split: the converter binds the hidden pointer as one
        // I64 formal and reads fields at recorded offsets.
        let indirect_struct_ok = matches!(enum_abi, EnumAbi::Admit)
            && indirect_by_value_struct_arg_abi_supported(arg);
        let pair_struct_ok =
            matches!(enum_abi, EnumAbi::Admit) && pair_struct_arg_abi_supported(arg);
        let newtype_struct_ok =
            matches!(enum_abi, EnumAbi::Admit) && direct_newtype_struct_arg_abi_supported(arg);
        let pair_enum_ok = matches!(enum_abi, EnumAbi::Admit) && pair_enum_abi_supported(arg);
        if !scalar_register_abi_ty_supported(arg, enum_abi)
            && !slice_ok
            && !indirect_struct_ok
            && !pair_struct_ok
            && !newtype_struct_ok
            && !pair_enum_ok
        {
            return Err(format!(
                "argument {index} uses unsupported ABI type/pass mode `{}` / {:?}",
                arg.layout.ty, arg.mode
            ));
        }
    }
    // The `bool` RETURN widening rides the trust-ir lane only (`EnumAbi::Admit`
    // is that lane's selector): its Zext contract is discharged by the trust-ir
    // gate's 32-bit byte-proof (see `zext_bool_return_abi_supported`), and the
    // MIR path's gate carries no such model, so admitting it there would be an
    // unproven ABI claim.
    let bool_ret_ok =
        matches!(enum_abi, EnumAbi::Admit) && zext_bool_return_abi_supported(&fn_abi.ret);
    // The pair-enum RETURN rides x0/x1 exactly as the converter's two-lane
    // signature declares.
    let pair_enum_ret_ok =
        matches!(enum_abi, EnumAbi::Admit) && pair_enum_abi_supported(&fn_abi.ret);
    if !scalar_register_abi_ty_supported(&fn_abi.ret, enum_abi)
        && !ignored_return_abi_ty_supported(&fn_abi.ret)
        && !bool_ret_ok
        && !pair_enum_ret_ok
    {
        return Err(format!(
            "return value uses unsupported ABI type/pass mode `{}` / {:?}",
            fn_abi.ret.layout.ty, fn_abi.ret.mode
        ));
    }
    Ok(())
}

/// The MIR frontend's ABI admission. Fieldless enums are REFUSED here: this path
/// does not read the producer's declared enum layout. See `EnumAbi`.
fn validate_codegen_instance_abi<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    mir_arg_count: usize,
) -> Result<(), String> {
    validate_codegen_instance_abi_with(tcx, instance, mir_arg_count, EnumAbi::Refuse)
}

/// The trust-ir (F1) frontend's ABI admission. Fieldless enums are admitted:
/// converter and gate share one producer-derived carrier width. See `EnumAbi`.
fn validate_codegen_instance_abi_trust_ir<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    mir_arg_count: usize,
) -> Result<(), String> {
    validate_codegen_instance_abi_with(tcx, instance, mir_arg_count, EnumAbi::Admit)
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
fn production_function_symbol_contract_supported(linkage: Linkage, visibility: Visibility) -> bool {
    // LINKAGE. `External` and `Internal` are the two definitions the object
    // emitters can now express: the function-symbol path carries a per-function
    // `FunctionSymbolBinding` (Mach-O `N_EXT` / ELF `STB_GLOBAL` vs a local
    // definition), and the CGU is emitted as ONE object, so a local callee is
    // reachable from every caller rustc placed beside it. Internalization is
    // exactly what `u64::from(u8)`, `wrapping_add`, and `rotate_left` hit, so
    // refusing it refused every program that calls `core`.
    //
    // rustc assigns linkage at CGU granularity and PROMOTES a symbol to
    // `External` whenever it is needed across CGUs, so `Internal` is sound
    // precisely when the CGU is the object boundary — which trust-cg enforces
    // twice over: `-Ccodegen-units != 1` is refused outright, and the CGU is
    // emitted as a single object.
    //
    // Weak/link-once/common are still refused: they are not strong definitions.
    //
    // VISIBILITY. `Default` is always expressible. `Hidden` is expressible for
    // an `External` DEFINITION on the Mach-O path (private extern,
    // `N_EXT | N_PEXT`: external for static linking, demoted to a local by the
    // final link) — the exact quadrant rustc assigns a `pub(crate)` definition
    // promoted for cross-CGU reachability. `Hidden` on an `Internal` symbol
    // would be redundant (a local is already invisible) and rustc does not
    // emit it; `Protected` stays refused — making a symbol non-interposable
    // has dynamic-link semantics the writers do not model. The ELF emission
    // path refuses any non-global binding wholesale, so an admitted Hidden
    // item still fails closed there rather than silently exporting.
    match (linkage, visibility) {
        (Linkage::External | Linkage::Internal, Visibility::Default) => true,
        (Linkage::External, Visibility::Hidden) => true,
        _ => false,
    }
}

/// Map rustc's `Linkage` onto the two definition shapes trust-cg emits.
///
/// Only linkages the gate above admits reach this function; anything else is a
/// bug in the gate and fails closed rather than being silently exported.
fn bridge_function_linkage(
    linkage: Linkage,
    visibility: Visibility,
) -> Result<bridge_backend::FunctionLinkage, String> {
    match (linkage, visibility) {
        (Linkage::External, Visibility::Default) => Ok(bridge_backend::FunctionLinkage::External),
        (Linkage::External, Visibility::Hidden) => Ok(bridge_backend::FunctionLinkage::Hidden),
        (Linkage::Internal, Visibility::Default) => Ok(bridge_backend::FunctionLinkage::Internal),
        other => Err(format!(
            "{other:?} linkage/visibility reached symbol emission despite the mono-item gate              (fail-closed)"
        )),
    }
}

pub(crate) fn extract_mono_verifiable_function<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<VerifiableFunction, String> {
    extract_mono_verifiable_function_with_abi(tcx, instance, false, &|tcx, instance, arg_count| {
        validate_codegen_instance_abi(tcx, instance, arg_count)
    })
}

/// [`extract_mono_verifiable_function`] with a caller-supplied ABI validator.
///
/// The MIR path validates against its own emission constraints
/// (`validate_codegen_instance_abi`); the trust-ir frontend's upstream lane
/// validates against the F1 fragment's admission
/// (`validate_codegen_instance_abi_trust_ir`) — the same validator every
/// source-first artifact passes — so an upstream body is not refused by
/// constraints belonging to the path it does not take.
pub(crate) fn extract_mono_verifiable_function_with_abi<'tcx, V>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    trust_ir_upstream: bool,
    validate_abi: &V,
) -> Result<VerifiableFunction, String>
where
    V: Fn(TyCtxt<'tcx>, ty::Instance<'tcx>, usize) -> Result<(), String>,
{
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

            validate_abi(tcx, instance, mono_body.arg_count)
                .map_err(|reason| format!("unsupported definition ABI: {reason}"))?;

            // The trust-ir upstream lane extracts under the faithful-scalars
            // guard with the faithful-ADT ty policy — the differential
            // oracle's spellings, which the trust-ir bridge and the
            // converter's pair-enum/recorded-layout lanes consume. The MIR
            // lane keeps the strict extraction.
            let mut func = if trust_ir_upstream {
                trust_mir_extract::extract_function_for_trust_ir_upstream(tcx, &mono_body)
                    .map_err(|error| error.to_string())?
            } else {
                trust_mir_extract::extract_function_for_codegen(tcx, &mono_body)
                    .map_err(|error| error.to_string())?
            };
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

/// Collect the single deterministic production INVENTORY: every reachable
/// monomorphic function rustc's mono-item graph names, with its output symbol
/// and admitted linkage, in a stable order.
///
/// This is the shared front half of `build_production_mono_functions`. It is
/// factored out so the trust-ir codegen frontend (`-Ztrust-cg-frontend=trust-ir`)
/// compiles THE SAME SYMBOL SET as the shipped MIR path — same collection, same
/// linkage/visibility gate, same collision check, same ordering — and the two
/// paths differ ONLY in where each function's IR comes from. A second inventory
/// would make any comparison between them meaningless.
/// A reachable `MonoItem::Static`, evaluated to its concrete byte image and
/// carried to object emission as a plain data definition. Only the
/// fail-closed slice is admitted at collection: non-thread-local,
/// default-visibility, relocation-free, fully-initialized allocations.
struct ProductionStatic {
    symbol: String,
    bytes: Vec<u8>,
    mutable: bool,
    is_external: bool,
    align: u32,
}

impl ProductionStatic {
    fn into_object_global(self) -> trust_cg_bridge::codegen_backend::ObjectGlobal {
        trust_cg_bridge::codegen_backend::ObjectGlobal {
            name: self.symbol,
            data: self.bytes,
            mutable: self.mutable,
            symbol_refs: vec![],
            is_external: self.is_external,
            is_thread_local: false,
            is_import: false,
            is_weak: false,
            align: self.align,
        }
    }
}

fn collect_production_mono_instances<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> Result<
    (Vec<(String, ty::Instance<'tcx>, bridge_backend::FunctionLinkage)>, Vec<ProductionStatic>),
    String,
> {
    use rustc_middle::mono::MonoItem;

    let mut instances = Vec::new();
    let mut statics = Vec::new();
    let mut symbols = FxHashMap::default();
    let partitions = tcx.collect_and_partition_mono_items(());

    for cgu in partitions.codegen_units {
        for (item, data) in cgu.items() {
            match *item {
                MonoItem::Fn(instance) => {
                    if !production_function_symbol_contract_supported(data.linkage, data.visibility)
                    {
                        return Err(format!(
                            "reachable function `{}` requires unsupported {:?} linkage / {:?} visibility",
                            tcx.symbol_name(instance).name,
                            data.linkage,
                            data.visibility,
                        ));
                    }
                    let linkage = bridge_function_linkage(data.linkage, data.visibility)?;
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
                    instances.push((symbol, instance, linkage));
                }
                MonoItem::Static(def_id) => {
                    // Admit the fail-closed data slice: a non-thread-local,
                    // default-visibility static whose evaluated allocation is
                    // fully initialized and carries NO relocations (no embedded
                    // pointers). Everything else is refused with its own name.
                    let path = tcx.def_path_str(def_id);
                    let attrs = tcx.codegen_fn_attrs(def_id);
                    if attrs.flags.contains(CodegenFnAttrFlags::THREAD_LOCAL) {
                        return Err(format!(
                            "reachable static `{path}` is #[thread_local]; TLS data is not                              wired into trust-cg object emission"
                        ));
                    }
                    if data.visibility != Visibility::Default {
                        return Err(format!(
                            "reachable static `{path}` requires {:?} visibility; data symbols                              carry no hidden/protected channel",
                            data.visibility,
                        ));
                    }
                    let is_external = match data.linkage {
                        Linkage::External => true,
                        Linkage::Internal => false,
                        other => {
                            return Err(format!(
                                "reachable static `{path}` requires unsupported {other:?} linkage"
                            ));
                        }
                    };
                    let alloc = tcx.eval_static_initializer(def_id).map_err(|e| {
                        format!("reachable static `{path}` failed to evaluate: {e:?}")
                    })?;
                    let alloc = alloc.inner();
                    if !alloc.provenance().ptrs().is_empty() {
                        return Err(format!(
                            "reachable static `{path}` embeds {} pointer(s); relocated static                              data is not wired into trust-cg object emission",
                            alloc.provenance().ptrs().len()
                        ));
                    }
                    let len = alloc.len();
                    let range = rustc_middle::mir::interpret::AllocRange {
                        start: rustc_abi::Size::ZERO,
                        size: rustc_abi::Size::from_bytes(len as u64),
                    };
                    let mut bytes =
                        alloc.inspect_with_uninit_and_ptr_outside_interpreter(0..len).to_vec();
                    // UNINITIALIZED ranges (enum payload padding, struct
                    // padding) are materialized as ZERO. Sound: a Rust program
                    // cannot rely on the contents of padding, and rustc's own
                    // backends pick an arbitrary concrete image for them; zero
                    // is the deterministic choice.
                    for chunk in alloc.init_mask().range_as_init_chunks(range) {
                        if !chunk.is_init() {
                            let r = chunk.range();
                            let (start, end) = (r.start.bytes() as usize, r.end.bytes() as usize);
                            bytes[start..end].fill(0);
                        }
                    }
                    let align = u32::try_from(alloc.align.bytes()).map_err(|_| {
                        format!("reachable static `{path}` alignment exceeds u32")
                    })?;
                    let symbol = tcx
                        .symbol_name(ty::Instance::mono(tcx, def_id))
                        .name
                        .to_string();
                    statics.push(ProductionStatic {
                        symbol,
                        bytes,
                        mutable: alloc.mutability.is_mut(),
                        is_external,
                        align,
                    });
                }
                MonoItem::GlobalAsm(item_id) => {
                    return Err(format!(
                        "reachable global assembly item `{item_id:?}` is not supported by trust-cg"
                    ));
                }
            }
        }
    }

    instances.sort_by(|(left, _, _), (right, _, _)| left.cmp(right));
    statics.sort_by(|a: &ProductionStatic, b: &ProductionStatic| a.symbol.cmp(&b.symbol));
    Ok((instances, statics))
}

/// Build the single deterministic production inventory used by every output
/// path. No reachable item may be skipped: omission would produce a linkable
/// artifact whose behavior differs from rustc's mono-item graph.
fn build_production_mono_functions<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> Result<
    (
        Vec<VerifiableFunction>,
        Vec<bridge_backend::FunctionLinkage>,
        Vec<bridge_backend::ObjectGlobal>,
    ),
    String,
> {
    let (instances, statics) = collect_production_mono_instances(tcx)?;
    // The linkage vector is built in the SAME order as the function vector and
    // returned beside it; the two are consumed strictly index-aligned.
    let linkage = instances.iter().map(|(_, _, linkage)| *linkage).collect::<Vec<_>>();
    let functions = instances
        .into_iter()
        .map(|(_, instance, _)| extract_mono_verifiable_function(tcx, instance))
        .collect::<Result<Vec<_>, _>>()?;

    let internal = linkage
        .iter()
        .filter(|linkage| **linkage == bridge_backend::FunctionLinkage::Internal)
        .count();
    tracing::info!(
        extracted = functions.len(),
        internal_linkage = internal,
        "[trust_cg] reachable monomorphic extraction complete"
    );
    let statics =
        statics.into_iter().map(ProductionStatic::into_object_global).collect::<Vec<_>>();
    Ok((functions, linkage, statics))
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
    /// backend-independent outputs such as MIR/metadata, and on the trust-ir
    /// frontend path (which never enters the bridge's MIR-fed `codegen_crate`).
    bridge_ongoing: Option<Box<dyn Any>>,
    /// Trust (F1): the codegen unit assembled by the trust-ir frontend
    /// (`-Ztrust-cg-frontend=trust-ir`), carrying LIR produced from
    /// `trust_ir_of` rather than from MIR.
    ///
    /// EXACTLY ONE of this and `bridge_ongoing` is `Some` on a linking
    /// compilation; both are `None` for metadata/MIR-only work. It is a separate
    /// field rather than a synthesized `bridge_backend::OngoingCodegen` because
    /// that type's fields are `pub(crate)` to the bridge, and — more to the
    /// point — because a module with no `source_functions` must not be able to
    /// masquerade as one the MIR path produced.
    trust_ir_module: Option<bridge_backend::CompiledModule>,
    /// Trust (F1 gate): the trust-ir specification work list for
    /// `trust_ir_module`, 1:1 and in the same order as its `lir_functions`.
    ///
    /// This is what makes the F1 path GATEABLE. It is deliberately a SEPARATE,
    /// non-optional vector rather than a field on `CompiledModule`: a missing or
    /// mis-sized work list must be a compile error at emission time, not a
    /// `None` that some caller could read as "nothing to verify" — which is
    /// exactly the laundering shape `source_functions: None` used to have.
    trust_ir_gate_sources: Vec<trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource>,
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
            // The refusal is UNCHANGED; only its stated reason is corrected, because
            // the old one ("until invoke, cleanup, personality, LSDA, and resume
            // semantics are emitted") is measurably stale and sent readers to the
            // wrong layer. trust-cg's BACKEND already emits those semantics and they
            // link and RUN: `trust_cg_codegen::exception_handling` builds the LSDA
            // call-site/action tables and resolves the personality symbol, and the
            // e2e tests `e2e_aarch64_eh_invoke_trust_ir` / `e2e_aarch64_eh_resume_trust_ir`
            // drive `Inst::Invoke` / `Inst::LandingPad` / `Inst::Resume` through the
            // real compiler pipeline, link with c++, and execute the catch/resume.
            //
            // The two blockers are UPSTREAM of codegen and IN THE PROOF:
            //   * PRODUCER — no production path constructs `Inst::Invoke` /
            //     `LandingPad` / `Resume` (only tests do), and
            //     `trust_mir_extract::extract_function_for_codegen` refuses every
            //     unwind-carrying MIR terminator (any non-`Unreachable` call unwind
            //     action, and every `Assert` / `Drop` / `UnwindResume` /
            //     `UnwindTerminate`) before codegen sees it. `-Cpanic=unwind` and
            //     `-Cpanic=abort` produce byte-identical `--emit=trust-ir`.
            //   * PROOF — the M-POS proven-output gate's obligation is
            //     `forall args. machine_ret(args) == ir_ret(args)`: ONE value, over
            //     the paths its executor can walk from the entry PC. An unwind edge
            //     is a second exit reached by the unwinder from the LSDA, so cleanup
            //     bytes are never decoded and never enter the obligation — they would
            //     ship unverified inside a `[PROVED]` object. See the measurements
            //     pinned by `verify_output::tests::unwind_scope_*`.
            //
            // Lifting this therefore means extending the gate's obligation to an
            // exit-tagged relation FIRST, then teaching the producer to emit the
            // edges — not adding backend EH support, which exists.
            if sess.panic_strategy().unwinds() {
                sess.dcx().fatal(
                    "panic=unwind is not supported by trust-cg: unwind edges are dropped before \
                     codegen (MIR extraction refuses cleanup/Assert/Drop/UnwindResume terminators, \
                     and no producer emits invoke/landing-pad/resume), and the proven-output gate \
                     proves only the normal-return path, so cleanup code could not be verified; \
                     compile with -Cpanic=abort",
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
                trust_ir_module: None,
                trust_ir_gate_sources: Vec::new(),
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

        // Trust (F1): the source-first frontend. `-Ztrust-cg-frontend=trust-ir`
        // routes every reachable mono-item through the ALREADY-SHIPPING
        // `trust_ir_of` query and the Module->LIR converter instead of through
        // MIR extraction, so "source -> TrustIR -> object" exists as an executed
        // path rather than an offline measurement. It is off by default and this
        // branch is the ONLY thing the option changes: with `mir` (the default)
        // control falls straight through to the code below, untouched.
        if trust_cg_frontend(tcx.sess) == TrustCgFrontend::TrustIr {
            return self.codegen_crate_from_trust_ir(tcx, crate_name);
        }

        let (functions, linkage, statics) = build_production_mono_functions(tcx).unwrap_or_else(|reason| {
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
            bridge_backend::CrateInfo { crate_name: crate_name.clone(), functions, linkage, statics };

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
            trust_ir_module: None,
            trust_ir_gate_sources: Vec::new(),
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

        // Trust (F1): the trust-ir frontend's codegen unit. It never entered the
        // bridge's MIR-fed `codegen_crate`, so there is no bridge `OngoingCodegen`
        // to join — the LIR is already in hand and only needs emission.
        if let Some(trust_ir_module) = &ongoing.trust_ir_module {
            let bridge = self.bridge_for_session(sess);
            let module = self.emit_rustc_module_for_trust_ir_module(
                &bridge,
                trust_ir_module,
                &ongoing.trust_ir_gate_sources,
                sess,
                outputs,
            );
            sess.dcx().note(format!(
                "trust-cg: compiled {} function(s) in 1 module(s) via the trust-ir frontend",
                ongoing.function_count
            ));
            return (
                CompiledModules { modules: vec![module], allocator_module: None },
                WorkProductMap::default(),
            );
        }

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
