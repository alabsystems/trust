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
// Trust: compare actual Windows file identities before copying a final object.
#![cfg_attr(windows, feature(windows_by_handle))]

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

// Trust: opt-in retained object-gate diagnostics; no admission authority.
mod clean_admission;
mod compiler_input_capture;
mod object_replay;

// Trust: rustc's final native artifact naming, cleanup, and notification protocol.
mod archive_output;
mod output_artifacts;

// Trust: exact source-to-native ABI agreement; legacy bridge admission is unchanged.
mod source_abi;
// Trust: typed source dependencies remain code even when the MIR inventory omits them.
mod native_source_residue;

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
use rustc_attr_ir::lang_items::LangItem;
use rustc_attr_ir::{InstrumentFnAttr, Linkage};
use rustc_codegen_ssa::back::archive::ArArchiveBuilderBuilder;
use rustc_codegen_ssa::back::link::link_binary;
use rustc_codegen_ssa::base::{allocator_kind_for_codegen, allocator_shim_contents};
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CompiledModule, CompiledModules, CrateInfo, ModuleKind, TargetConfig};
use rustc_data_structures::fx::FxHashMap;
use rustc_metadata::EncodedMetadata;
use rustc_middle::dep_graph::WorkProductMap;
use rustc_middle::middle::codegen_fn_attrs::{CodegenFnAttrFlags, CodegenFnAttrs};
use rustc_middle::mir;
use rustc_middle::mono::Visibility;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_middle::util::Providers;
use rustc_session::config::{
    CFGuard, CFProtection, DebugInfo, FunctionReturn, InstrumentCoverage, InstrumentMcount, LtoCli,
    OptLevel as RustcOptLevel, OutputFilenames, OutputType, PrintKind,
};
use rustc_session::{CodegenBackendInit, EarlySession, Session};
use rustc_span::{Symbol, sym};
use rustc_structures::CrateType;
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

use self::output_artifacts::native_machine_output_requested;

// ---------------------------------------------------------------------------
// The rustc adapter
// ---------------------------------------------------------------------------

/// trust-cg codegen backend for rustc.
///
/// Implements the real `rustc_codegen_ssa::traits::CodegenBackend` trait by
/// delegating to the bridge crate's `TrustCgCodegenBackend`.
// Trust: CodegenBackend adapter for trust-cg integration (#829).
#[derive(Default)]
pub struct TrustCgCodegenBackend {
    // Private live gated bytes, consumed once by the matching archive link.
    compiler_archive_object: std::sync::Mutex<Option<archive_output::CompilerArchiveObject>>,
}

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

fn target_is_builtin(sess: &EarlySession) -> bool {
    sess.opts.target_triple.debug_tuple() == sess.opts.target_triple.tuple()
}

fn target_is_exact_builtin_host(sess: &EarlySession) -> bool {
    target_is_builtin(sess)
        && sess.opts.target_triple.tuple() == rustc_session::config::host_tuple()
}

fn supported_crate_types_for_outputs(native_machine_output: bool) -> Vec<CrateType> {
    if native_machine_output {
        // Both rlib archives and standalone objects use the same bounded
        // rlib compilation lane, with exported scalar-register functions.
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

/// Trust (WS7.10 / F-114): a crate type outside `supported_crate_types` is a
/// hard error exactly when this session requests native machine output AND the
/// driver will actually run codegen. A print-only invocation — Cargo's
/// capability probe, `rustc - --crate-name ___ --print=file-names
/// --crate-type bin --crate-type rlib …` — stops before codegen, and Cargo reads
/// a missing `file-names` line as "unsupported"; erroring there would fail every
/// Cargo build under trust-cg, rlib-only ones included. Frontend-only output
/// (metadata, MIR, dep-info) advertises every crate type and never reaches the
/// fatal path. A driver mode that builds the global context (so
/// `collect_crate_types` runs) but exits before codegen and link
/// (`exits_before_codegen`, see [`session_exits_before_codegen`]) produces no
/// artifact of ANY crate type, so a dropped type there loses nothing and the
/// upstream warning stands.
fn unsupported_crate_type_is_fatal_for(
    native_machine_output: bool,
    exits_before_codegen: bool,
    print_kinds: impl IntoIterator<Item = PrintKind>,
) -> bool {
    native_machine_output
        && !exits_before_codegen
        && !print_requests_stop_before_codegen(print_kinds)
}

/// Trust (WS7.10 review): driver modes that create the global context — so
/// `collect_crate_types` and the crate-type hook DO run — and then return
/// before `codegen_and_build_linker`, emitting nothing: `-Zunpretty=<mode>`
/// (the tcx-needing modes such as `mir`, `hir`, `thir-tree`) and
/// `-Zno-analysis`. Refusing a `bin` crate type there would turn a pure
/// pretty-print of a `main.rs` into an error for an artifact nobody asked for.
///
/// `-Zno-codegen` is deliberately NOT listed: it skips `codegen_crate` but still
/// runs the link step, which publishes the other requested crate types (an rlib,
/// or rustc's object-less staticlib archive), so a dropped type there is still a
/// requested artifact silently missing. It stays refused (fail closed).
#[allow(rustc::bad_opt_access)]
fn session_exits_before_codegen(sess: &Session) -> bool {
    sess.opts.pretty.is_some() || sess.opts.unstable_opts.no_analysis
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
fn unsupported_explicit_codegen_model(sess: &EarlySession) -> Option<&'static str> {
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
        Box::new(Self::default())
    }

    fn bridge_for_target_arch(
        &self,
        target_arch: &str,
        target_triple: &str,
    ) -> Option<BridgeBackend> {
        TrustCgTargetArch::from_rustc_arch(target_arch)
            .map(|arch| BridgeBackend::new_for_triple(arch, target_triple))
    }

    fn bridge_for_session(&self, sess: &EarlySession) -> BridgeBackend {
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

    fn is_wasm_session(sess: &EarlySession) -> bool {
        sess.target.arch.desc() == "wasm32"
    }

    /// The backend-init facts upstream 1.101 moved out of the
    /// `CodegenBackend` trait methods (`thin_lto_supported`,
    /// `replaced_intrinsics`) into `CodegenBackendInit`.
    fn backend_init() -> CodegenBackendInit {
        CodegenBackendInit {
            global_backend_features: Vec::new(),
            // trust-cg does not currently replace any intrinsics.
            replaced_intrinsics: Vec::new(),
            fallback_intrinsics: Vec::new(),
            // trust-cg does not implement LTO.
            thin_lto_supported: false,
        }
    }

    fn wasm_target_config() -> TargetConfig {
        // Analysis-only wasm32 sessions still need target queries. Do not
        // borrow the native bridge's ABI features here: that bridge supports
        // only AArch64/x86-64, and linked Wasm is rejected during `init`.
        TargetConfig {
            internal_target_features: Default::default(),
            has_reliable_f16: false,
            has_reliable_f16_math: false,
            has_reliable_f16b: false,
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

        // Native objects use the same safety and proven-output gates as the
        // archive lane. join_codegen publishes requested final objects through
        // rustc's shared naming, cleanup, stdout, and notification protocol.
        matches!(
            output,
            OutputType::Exe
                | OutputType::Object
                | OutputType::Metadata
                | OutputType::DepInfo
                | OutputType::Mir
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
        // Trust (plan step 3.5, design §5.7): a Clean-origin body built while F1 codegen runs is
        // charged to the reach counter's `codegen` lane (the inventory's fallback asks under its
        // own lane, `clean_inventory::neighbours`). The step-3 exit requires it to be zero.
        let _clean_origin_reach = trust_thir_lower::clean_origin_reach::within(
            trust_thir_lower::clean_origin_reach::ReachLane::Codegen,
        );

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

        // Trust (step 2 increment 5, sub-step 5.4.2): the opt-in COMPILER LANE
        // (`-Ztrust-cg-f1-backend=compiler`). It consumes the SAME inventory and the same
        // instance-assembly plan, and builds ONE codegen module for trust-cg's
        // `Compiler::compile`, shipped only through the call-event gate. The default `lir`
        // lane below is untouched.
        if sess.trust_cg_f1_backend_is_compiler() {
            return self.codegen_crate_via_compiler_lane(
                tcx,
                crate_name,
                instances,
                reachable_statics,
            );
        }

        // (5) SOURCE -> `trust_ir_of` -> LIR, per reachable item.
        // Every refusal is recorded into one `RefusalCensus` instead of an
        // unaggregated string list, so one compile shows the SHAPE of the gap.
        // The census only reports: it admits nothing, and the `fatal` below
        // stays a `fatal`.
        //
        // TWO MODES, and the selector is `-Ztrust-ir-crate-module`:
        //
        // * DEFAULT (`lower_instance`): each item is selected by EXACT IDENTITY
        //   — `(DefIndex, DefPathHash)` — from the finalize-assembled crate
        //   module.
        // * CRATE-MODULE (`lower_crate_module`): the lowering context is the
        //   module the producer PUBLISHES, and the trust-ir v41 CODEGEN LICENSE
        //   (`Function::body_gate`) binds as a whole-module NEGATIVE gate. This
        //   mode was unselectable until the producer stamped that field — every
        //   body carried no licensing claim, so it refused all of them — and
        //   `trust_thir_lower::crate_module::stamp_codegen_license` is what
        //   changed.
        //
        // The default stays the handoff lane because the two differ in
        // SELECTION, not in gate strength: the crate-module lane resolves a
        // body by the producer's DISPLAY path, which is explicitly not identity,
        // so a collision-renamed body (two macro-expanded definitions sharing
        // one `def_path_str`) is refused there and admitted here. Flipping the
        // default would trade a soundness-neutral selection mechanism for a
        // weaker one; the license is available on request instead.
        let (lowered, linkage, census, instance_coverage) = if sess.trust_ir_crate_module() {
            let outcome = trust_ir_frontend::lower_crate_module(
                tcx,
                instances.into_iter().map(|(_s, i, l)| (i, l)).collect(),
                validate_codegen_instance_abi_trust_ir,
            );
            (outcome.lowered, outcome.linkage, outcome.census, None)
        } else {
            let mut lowered = Vec::with_capacity(reachable);
            let mut linkage = Vec::with_capacity(reachable);
            let mut census = trust_ir_frontend::RefusalCensus::default();
            // Trust (step 2 increment 3): every item's lane is decided ONCE, up
            // front, over the whole inventory. A concrete generic local instance,
            // or a monomorphic item whose assembled body reaches a bodyless
            // declaration, lowers from the instance-keyed codegen module; every
            // other item lowers from the finalize-assembled module exactly as
            // before (and when no item takes the instance lane, no such module is
            // built at all).
            // Owner ruling D17 admits a GENERIC instance body only under the
            // strict proven-output gate; the frozen plan reads the policy from
            // the session itself.
            let mut plan = trust_ir_frontend::instance_assembly::plan(tcx, &instances);
            // Trust (step 2 increment 4c): the drop-glue lane — synthesized glue, and every
            // `Inst::Drop` resolved to a call of it — active only under the strict output gate
            // (owner ruling D18 OD-2, under D17's rule); the frozen lane reads the policy itself.
            let mut glue = trust_ir_frontend::drop_glue_lane::GlueLane::new(tcx, &instances);
            // The instance-lane items that LOWERED, for the D17 coverage
            // disclosure, which is printed and written only after the gate.
            let mut emitted_instance_items = Vec::new();
            for (index, (_symbol, instance, item_linkage)) in instances.into_iter().enumerate() {
                match trust_ir_frontend::lower_instance(
                    tcx,
                    instance,
                    &mut plan,
                    &mut glue,
                    index,
                    validate_codegen_instance_abi_trust_ir,
                ) {
                    Ok(function) => {
                        if plan.is_instance_item(index) {
                            emitted_instance_items
                                .push((function.symbol.clone(), function.gate_source.func_id));
                        }
                        lowered.push(function);
                        linkage.push(item_linkage);
                    }
                    // Trust (plan step 3.0): every refusal F1 makes because of a Clean-origin
                    // body is named `[clean-below-gate]`; every other refusal is recorded as is.
                    Err(refusal) => census
                        .record(trust_ir_frontend::clean_below_gate::name(tcx, instance, refusal)),
                }
            }
            let glue_rows = if glue.active() {
                trust_ir_frontend::glue_coverage_rows(&lowered)
            } else {
                Vec::new()
            };
            let coverage =
                trust_ir_frontend::instance_coverage(&plan, &emitted_instance_items, glue_rows);
            (lowered, linkage, census, coverage)
        };

        tracing::info!(
            crate_name = %crate_name,
            reachable,
            completed = lowered.len(),
            refused = census.len(),
            "[trust_cg] trust-ir frontend: source -> trust_ir_of -> lower_module_to_lir"
        );
        sess.dcx().note(format!(
            "trust-cg trust-ir frontend: {}/{reachable} reachable function(s) completed \
             source -> trust_ir_of -> lower_module_to_lir",
            lowered.len()
        ));
        if let Some(note) = trust_ir_frontend::clean_origin_reach_note(tcx) {
            sess.dcx().note(note);
        }

        if !census.is_empty() {
            // The census reports counts per refusal class with a bounded
            // sample, so one compile shows the SHAPE of the gap instead of one
            // item at a time. The no-fallback property is deliberate and the
            // report says so.
            tcx.dcx().fatal(census.report(reachable));
        }

        if lowered.is_empty() {
            // A linking compilation with no functions is the MIR path's
            // "type-only library" case, which it handles by emitting no object.
            // Trust (owner ruling D17): and it has no instance-lane rows.
            clear_instance_coverage(sess, tcx.output_filenames(()));
            // Trust (step 2 increment 5, sub-step 5.4.2): nor compiler-lane certificates.
            clear_trust_cg_certificates(sess, tcx.output_filenames(()));
            return Box::new(OngoingTrustCgCodegen {
                bridge_ongoing: None,
                trust_ir_module: None,
                trust_ir_gate_sources: Vec::new(),
                crate_name,
                function_count: 0,
                instance_coverage: None,
                compiler_lane: None,
            });
        }

        let function_count = lowered.len();
        let (module, gate_sources) = trust_ir_frontend::compiled_module(
            &crate_name,
            lowered,
            linkage,
            reachable_statics.into_iter().map(ProductionStatic::into_object_global).collect(),
        )
        .unwrap_or_else(|reason| {
            tcx.dcx().fatal(format!(
                "trust-cg: refusing to emit a trust-ir codegen unit for `{crate_name}`: \
                         {reason}"
            ))
        });
        let _ = gate_mode;
        Box::new(OngoingTrustCgCodegen {
            bridge_ongoing: None,
            trust_ir_module: Some(module),
            trust_ir_gate_sources: gate_sources,
            crate_name,
            function_count,
            instance_coverage,
            compiler_lane: None,
        })
    }

    /// Trust (step 2 increment 5, sub-step 5.4.2): `codegen_crate_from_trust_ir` on the opt-in
    /// COMPILER LANE, `-Ztrust-cg-f1-backend=compiler`
    /// (docs/design/2026-10-08-step2-inc5-step4-compiler-lane-plan.md §2; design
    /// docs/design/2026-10-01-step2-inc5-real-calls-retarget.md §3).
    ///
    /// The same inventory, the same instance-assembly plan and drop-glue lane as the default
    /// lane; each item's body is SELECTED (`select_for_codegen_module`), rustc's `FnAbi` read
    /// into plain data (`abi_shape`), and ONE codegen module built for the crate
    /// (`codegen_module`, pure). trust-cg's `Compiler::compile` compiles it, and the bytes ship
    /// only through `trust_cg_bridge::f1_compile::compile_and_verify_trust_ir_module`: the
    /// call-event gate over the object, on its own 16 MiB thread (INC5.4-STACK), with
    /// `CerReport::ships` under `f1_emit_policy` as the only shipping decision.
    ///
    /// FAIL-CLOSED like the default lane: every refusal is recorded into ONE census, the
    /// frontend's, the codegen module's and trust-cg's own preflight rows together, and the
    /// compilation fails; nothing falls back to the default lane or to MIR. What 5.4 does not
    /// carry yet is refused by name (INC5.4-SCOPE).
    fn codegen_crate_via_compiler_lane<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        crate_name: String,
        instances: Vec<(String, ty::Instance<'tcx>, bridge_backend::FunctionLinkage)>,
        reachable_statics: Vec<ProductionStatic>,
    ) -> Box<dyn Any> {
        use std::collections::{BTreeMap, BTreeSet};
        use std::sync::Arc;

        use rustc_target::spec::RelocModel;
        use trust_cg_bridge::call_event::{CallSiteKind, ProducerBody, ProducerModule};
        use trust_cg_bridge::compiled_object::RelocationModel as CerRelocation;
        use trust_cg_bridge::f1_compile::{
            F1CompileConfig, F1CompileInput, F1OptLevel, F1Refusal, F1Target,
            census_trust_ir_module, compile_and_verify_trust_ir_module_with_clean,
        };
        use trust_ir_frontend::codegen_module::{
            self, CodegenModuleInput, CollectorStatic, ExpectedTarget, WorkItem, WorkState,
        };
        use trust_ir_frontend::{FrontendRefusal, InstanceCoverage, InstanceCoverageRow};

        let sess = tcx.sess;

        // ---- INC5.4-SCOPE: what 5.4.2 does not carry, refused by name ------------------
        if sess.trust_ir_crate_module() {
            tcx.dcx().fatal(
                "-Ztrust-cg-f1-backend=compiler does not take -Ztrust-ir-crate-module until step \
                 5.4.4 moves the crate-module lane onto the compiler lane's consumer \
                 (INC5.4-SCOPE); drop one of the two flags",
            );
        }
        let gate_mode = output_gate_mode(sess);
        if gate_mode == OutputGateMode::Off {
            tcx.dcx().fatal(
                "-Ztrust-cg-f1-backend=compiler refuses -Ztrust-cg-output-gate=off: the \
                 call-event gate is the compiler lane's only shipping authority (owner ruling \
                 D31), so the lane never ships an ungated object (INC5.4-SCOPE)",
            );
        }
        let policy = f1_emit_policy(gate_mode);
        let tuple = sess.opts.target_triple.tuple();
        let Some(target) = F1Target::from_rustc_tuple(tuple) else {
            tcx.dcx().fatal(format!(
                "-Ztrust-cg-f1-backend=compiler compiles for aarch64-apple-darwin and \
                 aarch64-unknown-linux-gnu only, not `{tuple}` (INC5.4-SCOPE): the call-event \
                 gate models AArch64 Mach-O and ELF, and the lane's placement table is AAPCS64"
            ));
        };
        let relocation = match sess.relocation_model() {
            RelocModel::Static => CerRelocation::Static,
            RelocModel::Pie => CerRelocation::Pie,
            RelocModel::Pic => CerRelocation::Pic,
            other => tcx.dcx().fatal(format!(
                "-Ztrust-cg-f1-backend=compiler has no `{other:?}` relocation model; the gate and \
                 trust-cg model static, pie and pic only (INC5.4-SCOPE)"
            )),
        };
        let opt_level = match sess.opts.optimize {
            RustcOptLevel::No => F1OptLevel::O0,
            RustcOptLevel::Less => F1OptLevel::O1,
            RustcOptLevel::More => F1OptLevel::O2,
            RustcOptLevel::Aggressive => F1OptLevel::O3,
            RustcOptLevel::Size | RustcOptLevel::SizeMin => tcx.dcx().fatal(
                "trust-cg does not yet implement size-specific optimization for -Copt-level=s/z",
            ),
        };
        // Trust: the effective target/CLI Always policy is a real AArch64
        // object-codegen request. The Compiler path forces an entry FP/LR frame,
        // including storage-free leaves; the same output gate still judges bytes.
        let force_frame_pointers = matches!(
            effective_frame_pointer_policy(
                sess.target.frame_pointer,
                sess.opts.cg.force_frame_pointers
            ),
            BridgeFramePointerPolicy::Always
        );

        // ---- the empty crate: no function and no static, no object ----------------------
        if instances.is_empty() && reachable_statics.is_empty() {
            clear_instance_coverage(sess, tcx.output_filenames(()));
            clear_trust_cg_certificates(sess, tcx.output_filenames(()));
            return Box::new(OngoingTrustCgCodegen {
                bridge_ongoing: None,
                trust_ir_module: None,
                trust_ir_gate_sources: Vec::new(),
                crate_name,
                function_count: 0,
                instance_coverage: None,
                compiler_lane: None,
            });
        }

        // ---- selection: the SAME plan and glue lane as the default lane ----------------
        let reachable = instances.len();
        let mut census = trust_ir_frontend::RefusalCensus::default();
        let mut plan = trust_ir_frontend::instance_assembly::plan(tcx, &instances);
        let mut glue = trust_ir_frontend::drop_glue_lane::GlueLane::new(tcx, &instances);
        let mut selected = Vec::with_capacity(reachable);
        for (index, (_symbol, instance, linkage)) in instances.iter().enumerate() {
            match trust_ir_frontend::select_for_codegen_module(
                tcx, *instance, &mut plan, &mut glue, index,
            ) {
                Ok((func, symbol)) => selected.push((index, *instance, symbol, func, *linkage)),
                // Trust (plan step 3.0): a refusal because of a Clean-origin body is named
                // `[clean-below-gate]`, exactly as on the default lane.
                Err(refusal) => census
                    .record(trust_ir_frontend::clean_below_gate::name(tcx, *instance, refusal)),
            }
        }

        // ---- the producer: `star` if built (one clone per crate), else `base` -----------
        let base = sess
            .with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
                |handoff| handoff.assembled_module(),
            )
            .ok();
        let star = plan.instance_module().map(|star| Arc::new(star.clone()));
        // Rule 1 compares every handoff body of `star` with `base`; without `base` it cannot
        // run, so the lane refuses rather than skip it (unreachable today: `plan()` builds
        // `star` from the same handoff).
        if star.is_some() && base.is_none() {
            tcx.dcx().fatal(
                "trust-cg compiler lane: the instance-keyed module was built but the \
                 finalize-assembled handoff module is unavailable, so design §3.1 rule 1 (every \
                 handoff body equal in base and star) cannot be checked; refusing the crate",
            );
        }
        let producer: Arc<trust_ir::Module> = match (&star, &base) {
            (Some(star), _) => Arc::clone(star),
            (None, Some(base)) => Arc::clone(base),
            (None, None) => Arc::new(trust_ir::Module::new(crate_name.clone())),
        };
        let clean_candidates = match clean_admission::candidates(tcx, &producer) {
            Ok(ids) => ids,
            Err(detail) => {
                census.record(FrontendRefusal::CodegenModule {
                    symbol: crate_name.clone(),
                    detail: format!("current-Session Clean admission refused: {detail}"),
                });
                BTreeSet::new()
            }
        };

        // Trust: source-only primitive modules use the same identity-preserving native
        // transport as logical closures. Route selection grants no ABI or body authority:
        // every retained source instance still needs its exact FnAbi, handoff identity and
        // conservation check. Unsupported signature shapes keep the checked rule-9 lane.
        let source_definitions = if base.is_some() {
            sess.with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
                |handoff| handoff.codegen_body_ids(),
            )
        } else {
            Vec::new()
        };
        let source_ids = source_definitions.iter().map(|(_, func)| *func).collect();
        let route_roots = selected.iter().map(|(_, _, _, func, _)| *func).collect();
        let expected = ExpectedTarget {
            triple: sess.target.llvm_target.to_string(),
            pointer_size: u32::from(sess.target.pointer_width / 8),
        };
        let native_source = trust_ir_frontend::native_source_module::uses_native_source(
            &trust_ir_frontend::native_source_module::NativeRouteInput {
                producer: &producer,
                base: base.as_deref(),
                source_ids: &source_ids,
                roots: &route_roots,
                has_statics: !reachable_statics.is_empty(),
                target_triple: &expected.triple,
                pointer_size: expected.pointer_size,
            },
        );
        let mut native_items = Vec::new();
        let mut native_abi = Vec::new();
        // ---- the work list ---------------------------------------------------------------
        let mut items = Vec::with_capacity(selected.len());
        for (index, instance, symbol, func, linkage) in selected {
            if native_source {
                match source_abi::validate_module_instance(tcx, instance, &producer, func) {
                    Ok(agreement) => {
                        // P records rustc's actual placement and extensions; producer attrs
                        // and logical ABI slots remain unchanged for the native adapter.
                        native_items.push(
                            trust_ir_frontend::native_source_module::NativeWorkItem {
                                symbol,
                                func,
                                linkage,
                                never_inline: instance_is_never_inline(tcx, instance),
                                placement: agreement.placement.clone(),
                                inventory_residue: false,
                                adapter_identity: agreement.adapter_identity(),
                            },
                        );
                        native_abi.push(agreement);
                    }
                    Err(detail) => {
                        census.record(FrontendRefusal::UnsupportedAbi { symbol, detail })
                    }
                }
                continue;
            }
            let ir_param_count = producer
                .function_by_id(func)
                .and_then(|f| producer.func_types.get(f.ty.as_usize()))
                .map(|ty| ty.params.len());
            let state = match ir_param_count {
                None => {
                    census.record(FrontendRefusal::SelectedFunctionMissing {
                        symbol: symbol.clone(),
                        func_id: func.index(),
                        functions: producer.functions.len(),
                    });
                    WorkState::Refused
                }
                Some(count) => {
                    match trust_ir_frontend::abi_shape::abi_shape_of(tcx, instance, count) {
                        Ok(abi) => WorkState::Admitted { abi },
                        Err(detail) => {
                            census.record(FrontendRefusal::UnsupportedAbi {
                                symbol: symbol.clone(),
                                detail,
                            });
                            WorkState::Refused
                        }
                    }
                }
            };
            items.push(WorkItem {
                symbol,
                func,
                linkage,
                never_inline: instance_is_never_inline(tcx, instance),
                handoff: !plan.is_instance_item(index),
                state,
            });
        }

        // Trust: the optimized MIR inventory is not the source IR's dependency graph.
        // Recover real local source instances through the exact published handoff and
        // HIR type-checker, then apply the same identity and actual FnAbi checks.
        if native_source {
            for (def_index, func) in source_definitions {
                if producer.function_by_id(func).is_none_or(|f| f.is_declaration())
                    || native_items.iter().any(|item| item.func == func)
                {
                    continue;
                }
                let symbol =
                    producer.function_by_id(func).map(|f| f.name.clone()).unwrap_or_default();
                let recovery =
                    native_source_residue::recover_instance(tcx, &producer, func, def_index);
                let instance = match recovery {
                    Ok(instance) => instance,
                    Err(detail) => {
                        census.record(FrontendRefusal::CodegenModule { symbol, detail });
                        continue;
                    }
                };
                if let Err(refusal) = trust_ir_frontend::validate_native_source_dependency(
                    tcx, instance, &symbol, &producer, func,
                ) {
                    census.record(refusal);
                    continue;
                }
                match source_abi::validate_module_instance(tcx, instance, &producer, func) {
                    Ok(agreement) => {
                        native_items.push(
                            trust_ir_frontend::native_source_module::NativeWorkItem {
                                func,
                                symbol,
                                linkage: bridge_backend::FunctionLinkage::Internal,
                                never_inline: instance_is_never_inline(tcx, instance),
                                placement: agreement.placement.clone(),
                                inventory_residue: true,
                                adapter_identity: agreement.adapter_identity(),
                            },
                        );
                        native_abi.push(agreement);
                    }
                    Err(detail) => {
                        census.record(FrontendRefusal::UnsupportedAbi { symbol, detail })
                    }
                }
            }
        }

        // ---- residue identities (rule 2) ------------------------------------------------
        let roots: BTreeSet<trust_ir::value::FuncId> = items
            .iter()
            .filter(|item| matches!(item.state, WorkState::Admitted { .. }))
            .map(|item| item.func)
            .collect();
        let spliced = plan.spliced();
        let residue = trust_ir_frontend::residue_identities(
            tcx,
            &producer,
            &codegen_module::residue_candidates(&producer, &roots),
            &spliced,
        );
        let statics: Vec<CollectorStatic> = reachable_statics
            .iter()
            .map(|s| CollectorStatic {
                symbol: s.symbol.clone(),
                mutable: s.mutable,
                is_external: s.is_external,
            })
            .collect();
        let declarations = BTreeMap::new();
        let foreign_declarations = if native_source {
            match source_abi::check_foreign_declarations(tcx, &producer) {
                Ok(checked) => checked,
                Err(detail) => {
                    census.record(FrontendRefusal::CodegenModule {
                        symbol: crate_name.clone(),
                        detail,
                    });
                    BTreeSet::new()
                }
            }
        } else {
            BTreeSet::new()
        };
        let mut clean_placements = BTreeMap::new();
        for item in &items {
            clean_placements.insert(item.func, codegen_module::linkage_of(item.linkage));
        }
        for (id, identity) in &residue {
            if matches!(identity, codegen_module::ResidueIdentity::Local { .. }) {
                clean_placements
                    .entry(*id)
                    .or_insert((trust_ir::Linkage::Internal, trust_ir::Visibility::Default));
            }
        }
        let mut out = if native_source {
            let conserved =
                match trust_thir_lower::effect_conservation::conserved_function_ids(sess) {
                    Ok(ids) => ids,
                    Err(detail) => {
                        census.record(FrontendRefusal::CodegenModule {
                            symbol: crate_name.clone(),
                            detail,
                        });
                        BTreeSet::new()
                    }
                };
            trust_ir_frontend::native_source_module::build(
                &trust_ir_frontend::native_source_module::NativeModuleInput {
                    producer: &producer,
                    base: base.as_deref(),
                    items: &native_items,
                    conserved: &conserved,
                    source_ids: &source_ids,
                    foreign_declarations: &foreign_declarations,
                    target: &expected,
                    has_statics: !statics.is_empty(),
                },
            )
        } else {
            let handoff_extensions = plan.handoff_declaration_extensions();
            let input = CodegenModuleInput {
                handoff_extensions: handoff_extensions.as_ref(),
                producer: &producer,
                base: if star.is_some() { base.as_deref() } else { None },
                items: &items,
                residue: &residue,
                declarations: &declarations,
                statics: &statics,
                target: &expected,
            };
            if clean_candidates.is_empty() {
                codegen_module::build(&input)
            } else {
                codegen_module::build_with_clean_candidates(&input, &clean_candidates)
            }
        };
        // Trust: aggregate classification requires actual source ABI witnesses for
        // this exact image. The source producer remains unclassified for the gate.
        if native_source && out.refusals.is_empty() {
            if let Err(detail) =
                source_abi::classify_native_module(&producer, &mut out.m_cg, &native_abi)
            {
                out.refusals
                    .push(FrontendRefusal::CodegenModule { symbol: crate_name.clone(), detail });
            }
        }
        // Trust (PKG-CP, R-8 item P): fold each constant-true check of M_cg and site every other
        // check of an admitted kind at rustc's panic entry and `Location` record; a function
        // holding a check that cannot be sited is refused by name. Only M_cg changes: the gate
        // still reads the unmodified producer bodies. Run last, over a module with no refusal.
        if out.refusals.is_empty() {
            let sited = trust_ir_frontend::panic_sites::rustc_half::site_codegen_module(
                tcx,
                &mut out.m_cg,
            );
            if sited.folded + sited.sited > 0 {
                sess.dcx().note(format!(
                    "trust-cg compiler lane: {} runtime check(s) folded (constant true), {} \
                     sited at rustc's panic entry and location (PKG-CP)",
                    sited.folded, sited.sited
                ));
            }
            out.refusals.extend(sited.refusals);
        }
        let codegen_module::CodegenModuleOutput {
            m_cg,
            symbols,
            bodies,
            placements,
            never_inline,
            residue: residue_rows,
            refusals,
        } = out;
        for refusal in refusals {
            census.record(refusal);
        }
        let completed = if native_source {
            native_items
                .iter()
                .filter(|item| !item.inventory_residue && bodies.contains_key(&item.symbol))
                .count()
        } else {
            items.iter().filter(|item| bodies.contains_key(&item.symbol)).count()
        };
        sess.dcx().note(format!(
            "trust-cg trust-ir frontend: {completed}/{reachable} reachable function(s) completed \
             source -> trust_ir_of -> codegen_module (the compiler lane, \
             -Ztrust-cg-f1-backend=compiler)"
        ));
        if let Some(note) = trust_ir_frontend::clean_origin_reach_note(tcx) {
            sess.dcx().note(note);
        }

        let config = F1CompileConfig {
            target,
            force_frame_pointers, // Trust: effective target/CLI Always policy.
            opt_level,
            relocation,
            never_inline,
            upstream_mir_lane: false,
        };
        let name = format!("{crate_name}.codegen_unit.0");
        // A row that names no function (trust-cg's residual compile error, a module-level
        // refusal) is attributed to the codegen unit, never to an empty symbol.
        let trust_cg_rows =
            |census: &mut trust_ir_frontend::RefusalCensus,
             rows: Vec<trust_cg_bridge::f1_compile::CensusRow>| {
                for row in rows {
                    census.record(FrontendRefusal::TrustCgRefused {
                        symbol: if row.symbol.is_empty() {
                            format!("<module {name}>")
                        } else {
                            row.symbol
                        },
                        variant: row.variant,
                        detail: row.detail,
                    });
                }
            };
        // The census counts refusal ROWS. On this lane a row can name inventory residue, a
        // caller dropped with a refused callee, or a trust-cg refusal over the admitted subset,
        // so the count can exceed the reachable items; say so beside every fatal.
        let rows_note = || {
            sess.dcx().note(
                "trust-cg compiler lane: the census below counts refusal ROWS — besides refused \
                 inventory items, inventory residue, callers dropped with a refused callee, and \
                 trust-cg's own rows over the admitted subset (`[trust-cg-refused:<variant>]`) — \
                 so its count can exceed the reachable function count",
            )
        };

        // ---- refusals: ONE fatal, with trust-cg's census over the admitted subset --------
        if !census.is_empty() {
            match census_trust_ir_module(&m_cg, &config) {
                Ok(rows) => trust_cg_rows(&mut census, rows),
                Err(refusal) => census.record(FrontendRefusal::TrustCgRefused {
                    symbol: format!("<module {name}>"),
                    variant: "census".to_string(),
                    detail: refusal.to_string(),
                }),
            }
            rows_note();
            tcx.dcx().fatal(census.report(reachable));
        }

        // ---- compile, gate, ship -------------------------------------------------------
        let producers = [ProducerModule { module: Arc::clone(&producer), symbols }];
        let bodies: BTreeMap<String, ProducerBody> = bodies;
        let compiler_input = F1CompileInput {
            m_cg: &m_cg,
            producers: &producers,
            bodies: &bodies,
            placements: &placements,
            policy,
            config: &config,
        };
        let outcome = clean_admission::with_admissions(
            tcx,
            &compiler_input,
            &clean_placements,
            |admissions| {
                if let Some(directory) = sess.opts.unstable_opts.trust_dump.ir.as_deref() {
                    let captured = trust_cg_bridge::f1_compile::compile_and_verify_trust_ir_module_with_clean_captured(
                        &compiler_input,
                        admissions,
                    );
                    // Optional retention precedes a possible ordinary Strict refusal.
                    // Its I/O/capacity outcome never grants or changes any admission.
                    match compiler_input_capture::persist(directory, &name, &captured.capture) {
                        Ok(path) => {
                            let status = match &captured.capture {
                                Ok(_) => "complete non-authorizing input data".to_string(),
                                Err(reason) => format!("capture incomplete: {}", reason.reason),
                            };
                            sess.dcx().note(format!(
                                "trust-cg Compiler CER input data: {} ({status}; independent current inputs required for replay)", path.display()));
                        }
                        Err(reason) => sess.dcx().note(format!(
                            "trust-cg Compiler CER input capture incomplete: {reason}"
                        )),
                    }
                    captured.outcome
                } else {
                    compile_and_verify_trust_ir_module_with_clean(&compiler_input, admissions)
                }
            },
        )
        .unwrap_or_else(|detail| Err(F1Refusal::Binding(detail)));
        let shipped = match outcome {
            Ok(shipped) => shipped,
            Err(F1Refusal::Census(rows)) => {
                trust_cg_rows(&mut census, rows);
                rows_note();
                tcx.dcx().fatal(census.report(reachable));
            }
            Err(F1Refusal::Compile(row)) => {
                trust_cg_rows(&mut census, vec![row]);
                rows_note();
                tcx.dcx().fatal(census.report(reachable));
            }
            Err(refusal) => tcx.dcx().fatal(format!(
                "trust-cg: REFUSING to emit trust-ir module `{name}` on the compiler lane \
                 ({}): {refusal}",
                policy_label(policy)
            )),
        };

        // ---- disclosure: the closure, never a per-function grade -------------------------
        let report = &shipped.report;
        sess.dcx().note(format!(
            "trust-cg compiler-lane certification report for module `{name}`: {} function(s), {} \
             closed-[PROVED], {} not closed, 0 refuted ({}); object sha256 {}",
            report.certificates.len(),
            report.closure.closed_kernel.len(),
            shipped.unclosed.len(),
            policy_label(policy),
            report.object_sha256
        ));
        for line in &shipped.unclosed {
            sess.dcx().note(format!("trust-cg compiler lane: not closed-[PROVED]: {line}"));
        }

        // ---- coverage: D17's instance-lane rows and the inventory residue ----------------
        // WHERE each body's code ships is read off the certificates, never assumed: trust-cg's
        // OPT-4 inlines co-emitted bodies into their callers at -O1 and above, and the object
        // defines a body under its own symbol exactly when the gate certified one there. A row
        // is written for a body whose code reaches the object at all, as on the default lane.
        let certified: Vec<(String, Vec<String>)> = report
            .certificates
            .iter()
            .map(|c| {
                let inlined = c
                    .call_sites
                    .iter()
                    .filter(|site| site.kind == CallSiteKind::InterpretedInline)
                    .map(|site| site.symbol.clone())
                    .collect();
                (c.symbol.clone(), inlined)
            })
            .collect();
        let placed = trust_ir_frontend::compiler_lane_code_placement(&m_cg, &certified);
        let row_of = |symbol: String, func_id: u32, kind: trust_ir_frontend::CoverageKind| {
            let place = placed.get(&symbol).cloned().unwrap_or_default();
            (place.emitted_as_own_symbol || !place.inlined_into.is_empty()).then(|| {
                InstanceCoverageRow {
                    symbol,
                    func_id,
                    kind,
                    emitted_as_own_symbol: place.emitted_as_own_symbol,
                    inlined_into: place.inlined_into,
                }
            })
        };
        let mut rows: Vec<InstanceCoverageRow> = spliced
            .into_iter()
            .filter(|(symbol, _, _)| bodies.contains_key(symbol))
            .filter_map(|(symbol, func_id, kind)| {
                row_of(symbol, func_id.index(), trust_ir_frontend::CoverageKind::Instance(kind))
            })
            .collect();
        rows.extend(residue_rows.iter().filter_map(|row| {
            row_of(
                row.symbol.clone(),
                row.producer_func.index(),
                trust_ir_frontend::CoverageKind::InventoryResidueLocal,
            )
        }));
        let coverage = (star.is_some() || !rows.is_empty()).then(|| InstanceCoverage { rows });

        let function_count = report.certificates.len();
        Box::new(OngoingTrustCgCodegen {
            bridge_ongoing: None,
            trust_ir_module: None,
            trust_ir_gate_sources: Vec::new(),
            crate_name,
            function_count,
            instance_coverage: None,
            compiler_lane: Some(CompilerLaneUnit {
                name,
                object: shipped.object,
                report: shipped.report,
                coverage,
                function_count,
            }),
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
            emit_trust_ir_module_object_with_replay,
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
            let dump = sess.opts.unstable_opts.trust_dump.ir.as_deref();
            let result = if dump.is_some() {
                emit_trust_ir_module_object_with_replay(
                    sources,
                    &bridge_module.linkage,
                    &bridge_module.statics,
                    policy,
                    bridge,
                )
                .map(|(object, report, replay)| (object, report, Some(replay)))
            } else {
                emit_trust_ir_module_object_verified(
                    sources,
                    &bridge_module.linkage,
                    &bridge_module.statics,
                    policy,
                    bridge,
                )
                .map(|(object, report)| (object, report, None))
            };
            match result {
                Ok((module_object, report, replay)) => {
                    if let (Some(directory), Some(replay)) = (dump, replay) {
                        let captured = replay.is_ok();
                        let path = object_replay::persist(
                            directory,
                            &bridge_module.name,
                            &module_object.bytes,
                            sources.len(),
                            replay.as_ref().map_err(String::as_str),
                        )
                        .unwrap_or_else(|error| {
                            sess.dcx().fatal(format!("trust-cg object replay diagnostic: {error}"))
                        });
                        sess.dcx().note(format!("trust-cg retained object replay diagnostic at {} (capture_complete={captured}; not source refinement or executable admission)", path.display()));
                    }
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
    let configured = output_gate_mode_from_name(configured_mode)?;
    if strict_verification && configured == OutputGateMode::Off {
        return Err("-Ztrust-cg-output-gate=off is incompatible with batteries-on strict \
             Trust verification; use -Ztrust-verify=off for a vanilla compile");
    }
    // Trust (owner ruling D17): whether the gate is STRICT is decided by ONE
    // function, the frozen instance assembler's `strict_gate_from`, which both
    // this emission path and the assembler's generic-append condition call.
    if trust_ir_frontend::instance_assembly::strict_gate_from(strict_verification, configured_mode)
    {
        return Ok(OutputGateMode::Strict);
    }
    Ok(configured)
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

/// Trust (owner ruling D17): the per-function coverage artifact's path,
/// `<out-dir>/<output filestem>.trust-instance-coverage.json` — rustc's output
/// filestem, which carries `-Cextra-filename` and follows `-o`.
fn instance_coverage_path(outputs: &OutputFilenames) -> std::path::PathBuf {
    outputs.with_extension("trust-instance-coverage.json")
}

/// Trust (owner ruling D17): the artifact's LIFECYCLE, owned by the trust-ir
/// frontend alone (the MIR-frontend trust-cg path and the LLVM backend never
/// touch it):
///
/// * it lives at `<out-dir>/<output filestem>`, not necessarily beside the rlib
///   (`--emit link=PATH` puts the rlib elsewhere);
/// * a trust-ir compile with instance-lane rows replaces it atomically (written
///   beside, renamed over) as soon as the gate accepts the object
///   ([`disclose_instance_coverage`]), so a compile that fails LATER (at link or
///   archive) has already replaced it;
/// * a SUCCESSFUL trust-ir compile with no instance-keyed module removes the
///   artifact under ITS OWN output filestem (this function); one an earlier
///   compile left under another stem (e.g. via `-o`) stays;
/// * a compile REFUSED by trust-cg or the frontend touches nothing: rustc keeps
///   the previous rlib too, so the previous artifact stays beside the object it
///   is bound to;
/// * a rebuild by another backend (LLVM, or the MIR frontend) cannot remove it.
///
/// In every case where artifact and rlib can disagree, the object binding no
/// longer matches the rlib, which is the consumer rule's job to see
/// (`trust_ir_frontend::InstanceCoverage::to_json`).
fn clear_instance_coverage(sess: &Session, outputs: &OutputFilenames) {
    let path = instance_coverage_path(outputs);
    match fs::remove_file(&path) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => sess.dcx().fatal(format!(
            "trust-cg: failed to remove the stale instance-lane coverage artifact `{}`: {error}",
            path.display()
        )),
    }
}

/// Trust (owner ruling D17): print the instance lane's per-function coverage
/// and write `<out-dir>/<output filestem>.trust-instance-coverage.json`, the
/// per-function coverage artifact, bound to the compiler that wrote it and to
/// the SHA-256 of the object(s) it describes. Called only after the
/// proven-output gate accepted the object, so every row is emitted code. A
/// GENERIC row exists only under the strict policy (the plan refuses the append
/// otherwise); if one ever appears under another policy, the claim it would
/// carry is false, so that is fatal.
fn disclose_instance_coverage(
    sess: &Session,
    outputs: &OutputFilenames,
    crate_name: &str,
    coverage: &trust_ir_frontend::InstanceCoverage,
    object_paths: &[&std::path::Path],
) {
    let mode = output_gate_mode(sess);
    let (policy, verdict) = match mode {
        OutputGateMode::Strict => ("strict", "[PROVED] (strict: only [PROVED] ships)"),
        OutputGateMode::AllowUnknown => (
            "allow-unknown",
            "not individually reported (allow-unknown ships [PROVED], [VALIDATED] and \
             uncertified functions; see the certification report)",
        ),
        OutputGateMode::Off => ("off", "none (the proven-output gate is off)"),
    };
    if mode != OutputGateMode::Strict && coverage.has_strict_only_rows() {
        sess.dcx().fatal(format!(
            "trust-cg internal error: the instance lane appended a GENERIC instance body, or the \
             drop-glue lane spliced synthesized glue, under the `{policy}` output-gate policy; \
             owner rulings D17 and D18 OD-2 admit one only under the strict gate"
        ));
    }
    for note in coverage.notes(verdict) {
        sess.dcx().note(note);
    }
    let mut objects = Vec::with_capacity(object_paths.len());
    for object in object_paths {
        let bytes = fs::read(object).unwrap_or_else(|error| {
            sess.dcx().fatal(format!(
                "trust-cg: failed to read the emitted object `{}` to bind the instance-lane \
                 coverage artifact to it: {error}",
                object.display()
            ))
        });
        let digest = rustc_span::SourceFileHash::new_in_memory(
            rustc_span::SourceFileHashAlgorithm::Sha256,
            &bytes,
        );
        let hex: String = digest.hash_bytes().iter().map(|b| format!("{b:02x}")).collect();
        let name = object
            .file_name()
            .map_or_else(|| object.display().to_string(), |n| n.to_string_lossy().into_owned());
        objects.push((name, bytes.len(), hex));
    }
    let path = instance_coverage_path(outputs);
    let json = coverage.to_json(crate_name, policy, verdict, sess.cfg_version, &objects);
    // Written beside and RENAMED over, so a reader never sees a half-written
    // artifact and a failure leaves the previous one whole.
    let staged = outputs.with_extension("trust-instance-coverage.json.tmp");
    if let Err(error) = fs::write(&staged, json).and_then(|()| fs::rename(&staged, &path)) {
        sess.dcx().fatal(format!(
            "trust-cg: failed to write the instance-lane coverage artifact `{}`: {error}",
            path.display()
        ));
    }
}

/// Trust (step 2 increment 5, sub-step 5.4.2): the compiler lane's shipping policy, the one
/// `CerReport::ships` reads (`trust_cg_bridge::f1_compile`). The same mapping as the two
/// module-to-LIR gate sites (`emit_rustc_module_for_trust_ir_module` and
/// `run_module_output_preservation_gate`), which keep their own literals; `tests.rs` asserts the
/// three agree. `Off` never reaches it — the compiler lane refuses `off` by name (INC5.4-SCOPE)
/// — and if it ever did it would get the STRICT policy, not a permissive one.
fn f1_emit_policy(mode: OutputGateMode) -> trust_cg_bridge::verify_output::EmitPolicy {
    use trust_cg_bridge::verify_output::EmitPolicy;
    match mode {
        OutputGateMode::Strict => EmitPolicy::StrictProvenOnly,
        OutputGateMode::AllowUnknown => EmitPolicy::AllowUnknown,
        OutputGateMode::Off => EmitPolicy::StrictProvenOnly,
    }
}

/// Trust (step 2 increment 5, sub-step 5.4.2): the compiler lane's certificates file,
/// `<out-dir>/<output filestem>.trust-cg-certificates.json` — one
/// `trust-cg-bridge.call-refinement.v1` record per function, bound to the object's SHA-256
/// (design §5), beside the coverage artifact.
fn trust_cg_certificates_path(outputs: &OutputFilenames) -> std::path::PathBuf {
    outputs.with_extension("trust-cg-certificates.json")
}

/// Write the certificates file through a staged file renamed over, so a reader never sees a
/// half-written file and a failure leaves the previous one whole (the coverage artifact's
/// lifecycle, [`clear_instance_coverage`]). An empty rendering is refused, never written.
fn write_trust_cg_certificates(
    sess: &Session,
    outputs: &OutputFilenames,
    report: &trust_cg_bridge::call_event::CerReport,
) {
    let path = trust_cg_certificates_path(outputs);
    let json = report.to_json();
    if json.is_empty() {
        sess.dcx().fatal(format!(
            "trust-cg: the call-event report for `{}` rendered to nothing; refusing to write an \
             empty certificates file",
            path.display()
        ));
    }
    let staged = outputs.with_extension("trust-cg-certificates.json.tmp");
    if let Err(error) = fs::write(&staged, json).and_then(|()| fs::rename(&staged, &path)) {
        sess.dcx().fatal(format!(
            "trust-cg: failed to write the certificates file `{}`: {error}",
            path.display()
        ));
    }
}

/// Remove the certificates file under this compilation's output filestem: run by every
/// successful trust-ir compile that did not take the compiler lane, so a file left by an
/// earlier compiler-lane compile never stands beside an object it does not describe. Mirrors
/// [`clear_instance_coverage`]; a refused compile touches nothing.
fn clear_trust_cg_certificates(sess: &Session, outputs: &OutputFilenames) {
    let path = trust_cg_certificates_path(outputs);
    match fs::remove_file(&path) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => sess.dcx().fatal(format!(
            "trust-cg: failed to remove the stale certificates file `{}`: {error}",
            path.display()
        )),
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
/// Bool PARAMETERS are admitted separately, and later (WS7.13,
/// `zext_bool_param_abi_supported`): the gate's spec side models `Bool` in
/// parameter position only under the caller-owed extension precondition the
/// cross-check attests, so the admission here is exactly as wide as what the
/// prover can speak about — the alignment this validator exists to keep.
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
    let PassMode::Indirect {
        attrs,
        address_space: None,
        mode: rustc_target::callconv::IndirectMode::Pointer,
    } = &arg.mode
    else {
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
        && matches!(arg.layout.backend_repr, BackendRepr::ScalarPair { .. })
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
        BackendRepr::ScalarPair { a: t, .. } => {
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

/// A `bool` PARAMETER, admitted with its `Zext` extension contract — the
/// trust-ir (F1) lane only (WS7.13).
///
/// The same `Zext` promise that a bool RETURN discharges BY PROOF (the callee
/// owes it, and the gate's 32-bit obligation holds the emitted bytes to it) is,
/// for a bool PARAMETER, a promise the CALLER owes — one the gate cannot see
/// any caller keep. The gate therefore models a bool parameter only as a
/// CONDITIONAL obligation under the ambient precondition `W{k}[31:1] == 0`,
/// and only when the facts that license it are ATTESTED on the
/// `AbiPassModeCrossCheck` this frontend mints ([`instance_param_extensions`]):
/// rustc's `arg_ext: Zext` for that slot, and a target whose ABI makes the
/// caller extend a small argument to 32 bits (Apple AArch64). The verdict is
/// capped at `AyValidated` (never kernel-`PROVED`), and StrictProvenOnly
/// refuses that grade; under `allow-unknown` the function ships VALIDATED with
/// the precondition in its assumption list. Without the facts the gate stays
/// `Unknown`, so admitting the slot here can never outrun the proof: the
/// pre-WS7.13 refusal merely moved from the ABI filter to the gate, by name.
///
/// The shape admitted is EXACTLY the bool-return one: `Direct`, `Zext`, no
/// `InReg`, 8 bits, `BackendRepr::Scalar`. The converter's side of the slot is
/// the same byte-wide `LirType::I8` carrier a bool return uses.
fn zext_bool_param_abi_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    zext_bool_return_abi_supported(arg)
}

/// The width, in bits, to which `target`'s ABI makes the CALLER extend a
/// `Zext`/`Sext` small (sub-32-bit) integer argument — `None` when the target
/// makes no such promise and the callee owns the extension.
///
/// This is the target-side half of the bool-parameter precondition (WS7.13).
/// It is deliberately a closed, MEASURED table rather than a rule read off
/// `arg_ext`: rustc records `Zext` on every bool slot on every target, but
/// whether the CALLER performs the extension is a platform ABI fact. Apple's
/// ARM64 ABI states it — "The caller of a function is responsible for signing
/// or zero-extending any argument with fewer than 32 bits. The standard ABI
/// expects the callee to sign or zero-extend those arguments." — so Apple
/// AArch64 is `Some(32)` and generic AAPCS64 (every non-Apple AArch64 target)
/// is `None`. Everything else is `None` until measured, which keeps a bool
/// parameter `Unknown` there rather than modeled under a promise nobody made.
fn caller_small_arg_extension_bits(target: &rustc_target::spec::Target) -> Option<u32> {
    if target.arch == rustc_target::spec::Arch::AArch64 && target.is_like_darwin {
        return Some(32);
    }
    None
}

/// Mint the CALLER-OWED EXTENSION facts of `instance`'s parameter slots
/// (WS7.13) from rustc's own `FnAbi` and the session target, for the
/// `AbiPassModeCrossCheck` the trust-ir frontend attaches. Only a
/// `PassMode::Direct` slot has a single `arg_ext`; any other mode is recorded
/// as `None` ("not recorded"), which the gate never reads as
/// `ArgExtension::None`.
///
/// Called only AFTER `validate_codegen_instance_abi_trust_ir` has accepted the
/// instance with `ir_param_count` (the produced `FuncTy`'s parameter count), so
/// the entries line up with the trust-ir parameters by index. The `FnAbi` is
/// read through [`fn_abi_preconditions`] with that same count, the one site
/// that asks rustc for it: the validator's preconditions are re-asked and
/// cannot disagree with what the validator saw (a cached query over the same
/// instance), and `fn_abi.args.len() == ir_param_count` is checked again there.
pub(crate) fn instance_param_extensions<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    ir_param_count: usize,
) -> Result<trust_cg_bridge::AbiParamExtensions, String> {
    let fn_abi = fn_abi_preconditions(tcx, instance, ir_param_count)?;
    let per_param = fn_abi
        .args
        .iter()
        .map(|arg| match &arg.mode {
            PassMode::Direct(attrs) => Some(match attrs.arg_ext {
                ArgExtension::None => trust_cg_bridge::AbiArgExtension::None,
                ArgExtension::Zext => trust_cg_bridge::AbiArgExtension::Zext,
                ArgExtension::Sext => trust_cg_bridge::AbiArgExtension::Sext,
            }),
            _ => None,
        })
        .collect();
    Ok(trust_cg_bridge::AbiParamExtensions {
        per_param,
        caller_extends_to_bits: caller_small_arg_extension_bits(&tcx.sess.target),
    })
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
    if attrs.instrument_fn.is_some() {
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

/// Trust (step 2 increment 5, sub-step 5.4.2; plan critique H3(a)): the PRECONDITIONS of
/// [`validate_codegen_instance_abi_with`], extracted verbatim so the compiler lane
/// (`trust_ir_frontend::abi_shape::abi_shape_of`) asks rustc's `FnAbi` after exactly the
/// checks the old lane makes, with byte-identical messages: the codegen attributes, the
/// audited Rust/C convention, convention drift, no variadic or implicit argument, no
/// unwinding, and `mir_arg_count` arguments. The old lane's register cap and per-`PassMode`
/// loop stay in [`validate_codegen_instance_abi_with`], unchanged; the compiler lane imposes
/// no cap (its placement table gives a function with a stack argument no entry, which the
/// call-event gate grades Unknown).
fn fn_abi_preconditions<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    mir_arg_count: usize,
) -> Result<&'tcx rustc_target::callconv::FnAbi<'tcx, Ty<'tcx>>, String> {
    fn_abi_preconditions_with_source(tcx, instance, mir_arg_count, false)
}

/// Trust: the full native source consumer can additionally check a concrete
/// FnOnce environment. Keep the legacy entry point above closure-refusing.
fn fn_abi_preconditions_with_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    mir_arg_count: usize,
    source_closure: bool,
) -> Result<&'tcx rustc_target::callconv::FnAbi<'tcx, Ty<'tcx>>, String> {
    let attrs = tcx.codegen_instance_attrs(instance.def);
    if let Some(reason) = codegen_attrs_issue(&attrs) {
        return Err(reason);
    }

    let typing_env = ty::TypingEnv::fully_monomorphized();
    let instance_ty = instance.ty(tcx, typing_env);
    let (extern_abi, closure_args) = match instance_ty.kind() {
        ty::Closure(def_id, args) if source_closure => {
            let closure = args.as_closure();
            let borrowed_empty = closure.kind() == ty::ClosureKind::Fn
                && closure.upvar_tys().is_empty();
            if instance.def != ty::InstanceKind::Item(*def_id)
                || (closure.kind() != ty::ClosureKind::FnOnce && !borrowed_empty)
            {
                return Err("the native source ABI requires an ordinary FnOnce or borrowed empty Fn closure".into());
            }
            let sig = tcx.instantiate_bound_regions_with_erased(args.as_closure().sig());
            let [tuple] = sig.inputs() else {
                return Err("source closure signature does not contain its argument tuple".into());
            };
            let ty::Tuple(fields) = tuple.kind() else {
                return Err("source closure arguments are not a concrete tuple".into());
            };
            if sig.abi() != ExternAbi::RustCall || sig.c_variadic() {
                return Err("source closure does not have the non-variadic RustCall ABI".into());
            }
            (sig.abi(), Some(fields.len()))
        }
        _ if instance_ty.is_fn() => (instance_ty.fn_sig(tcx).abi(), None),
        _ => return Err(format!("instance type `{instance_ty}` is not a callable function")),
    };
    let expected_canon_abi = if closure_args.is_some() {
        Some(CanonAbi::Rust)
    } else {
        supported_canonical_abi(extern_abi)
    };
    let Some(expected_canon_abi) = expected_canon_abi else {
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
    let fixed_args_match = match closure_args {
        // rustc spreads the RustCall tuple after the one fixed environment.
        Some(args) => fn_abi.fixed_count == 1 && fn_abi.args.len() == args + 1,
        None => fn_abi.fixed_count as usize == fn_abi.args.len(),
    };
    if fn_abi.c_variadic || !fixed_args_match {
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
    Ok(fn_abi)
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
    let fn_abi = fn_abi_preconditions(tcx, instance, mir_arg_count)?;
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
        let indirect_struct_ok =
            matches!(enum_abi, EnumAbi::Admit) && indirect_by_value_struct_arg_abi_supported(arg);
        let pair_struct_ok =
            matches!(enum_abi, EnumAbi::Admit) && pair_struct_arg_abi_supported(arg);
        let newtype_struct_ok =
            matches!(enum_abi, EnumAbi::Admit) && direct_newtype_struct_arg_abi_supported(arg);
        let pair_enum_ok = matches!(enum_abi, EnumAbi::Admit) && pair_enum_abi_supported(arg);
        // The `bool` PARAMETER widening rides the trust-ir lane only (WS7.13):
        // its caller-owed Zext contract is modeled by the trust-ir gate as an
        // attested ambient precondition (`zext_bool_param_abi_supported`), and
        // the MIR path's gate carries no such model.
        let bool_param_ok =
            matches!(enum_abi, EnumAbi::Admit) && zext_bool_param_abi_supported(arg);
        if !scalar_register_abi_ty_supported(arg, enum_abi)
            && !slice_ok
            && !indirect_struct_ok
            && !pair_struct_ok
            && !newtype_struct_ok
            && !pair_enum_ok
            && !bool_param_ok
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

    match ty::Instance::try_resolve(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        def_id,
        args.skip_binder(),
    ) {
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

/// Trust (step 2 increment 5, sub-step 5.4.2; design §3.1 rule 11): rustc's
/// `#[inline(never)]`, which the compiler lane hands trust-cg as its never-inline set.
fn instance_is_never_inline<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> bool {
    matches!(tcx.codegen_instance_attrs(instance.def).inline, rustc_attr_ir::InlineAttr::Never)
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
    extract_mono_verifiable_function_with_abi(tcx, instance, &|tcx, instance, arg_count| {
        validate_codegen_instance_abi(tcx, instance, arg_count)
    })
}

/// [`extract_mono_verifiable_function`] with a caller-supplied ABI validator.
///
/// Only the retained MIR backend calls this extractor. F1 imports dependency Trust-IR through
/// the sealed metadata route and never calls a MIR-to-Trust-IR producer.
pub(crate) fn extract_mono_verifiable_function_with_abi<'tcx, V>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
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
    /// `#[used]` (either flavour): the static must survive with no reference
    /// in its object. trust-ir v41 carries this to the object writer as
    /// `ObjectGlobal::retained`; emitting it `false` would let a linker drop
    /// exactly the registration a `#[used]` static exists to keep.
    retained: bool,
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
            // Admission refuses every non-default visibility, so the default is
            // the static's actual visibility, not a placeholder.
            visibility: trust_ir::Visibility::Default,
            retained: self.retained,
            // trust-ir v45. Both are provably right here rather than
            // conventionally right, which is the only reason they may be
            // constants: admission REFUSES `#[link_section]` by name (see the
            // options it prints), so no static reaching this constructor has a
            // section to carry; and it admits only `External` / `Internal`
            // linkage, while COMDAT is exactly the one-definition-rule forms
            // (`LinkOnceOdr` / `WeakOdr`), both of which are refused above.
            section: None,
            comdat: false,
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
                    // `#[link_section]` places the static in a named section.
                    // Emitting it without one would put its bytes in the default
                    // data section and silently drop the placement (a
                    // linker-registration array would simply vanish from the
                    // section its reader walks). Refuse by name, with the options.
                    //
                    // The reason this refusal used to give — "`ObjectGlobal` has
                    // no section channel" — went STALE at trust-ir v45, which
                    // added `ObjectGlobal.section`. The refusal still stands
                    // because THIS lane does not populate it (see
                    // `into_object_global`, which passes `None`), not because the
                    // channel is missing. Wiring `attrs.link_section` through
                    // `ProductionStatic` is what retires this arm; until then a
                    // reader must not conclude from the old sentence that the
                    // capability is absent downstream.
                    if let Some(section) = attrs.link_section {
                        return Err(format!(
                            "reachable static `{path}` has #[link_section = \"{section}\"]; \
                             trust-cg object emission has no named-section channel for data \
                             and would place it in the default data section. Options: build \
                             this crate with the LLVM backend (`-Zcodegen-backend=llvm`), or \
                             use trust-ir-cg, whose trust-ir `Global.section` carries it"
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
                    let align = u32::try_from(alloc.align.bytes())
                        .map_err(|_| format!("reachable static `{path}` alignment exceeds u32"))?;
                    let symbol = tcx.symbol_name(ty::Instance::mono(tcx, def_id)).name.to_string();
                    statics.push(ProductionStatic {
                        symbol,
                        bytes,
                        mutable: alloc.mutability.is_mut(),
                        is_external,
                        align,
                        retained: attrs.flags.intersects(
                            CodegenFnAttrFlags::USED_COMPILER | CodegenFnAttrFlags::USED_LINKER,
                        ),
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
    let statics = statics.into_iter().map(ProductionStatic::into_object_global).collect::<Vec<_>>();
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
    /// Trust (owner ruling D17): the instance lane's per-function coverage
    /// rows, disclosed after the gate accepts the object. `None` when no
    /// instance-keyed module was built.
    instance_coverage: Option<trust_ir_frontend::InstanceCoverage>,
    /// Trust (step 2 increment 5, sub-step 5.4.2): the COMPILER LANE's codegen unit
    /// (`-Ztrust-cg-f1-backend=compiler`): the object `CerReport::ships` already allowed, its
    /// call-event report and its coverage rows. When `Some`, every other field is empty.
    compiler_lane: Option<CompilerLaneUnit>,
}

/// Trust (step 2 increment 5, sub-step 5.4.2): one crate's compiler-lane output, joined by
/// `join_codegen`, which writes the object, the certificates file and the coverage artifact.
struct CompilerLaneUnit {
    /// The codegen unit's name (`<crate>.codegen_unit.0`).
    name: String,
    /// Exactly the bytes the call-event gate verified (`F1Shipped::object`).
    object: Vec<u8>,
    /// The gate's report over `object`.
    report: trust_cg_bridge::call_event::CerReport,
    /// The per-function coverage rows (D17 instance-lane rows and inventory residue).
    coverage: Option<trust_ir_frontend::InstanceCoverage>,
    /// Functions defined in the object.
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

    fn init(&mut self, sess: &EarlySession) -> CodegenBackendInit {
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
            return Self::backend_init();
        }

        // Neither backend implements whole-program LTO. `thin_lto_supported`
        // alone only changes rustc's fallback choice; it does not make fat LTO
        // or linker-plugin LTO sound for a backend that emits no bitcode.
        // Upstream 1.101: `init` runs before the Session exists, so the old
        // `sess.lto()` is reconstructed from its inputs. With
        // `thin_lto_supported: false` (see `backend_init`), `Session::lto`
        // yields Fat exactly when the target requires LTO or the CLI asked
        // for any LTO flavor, and No/ThinLocal otherwise — the same refusal.
        if sess.target.requires_lto
            || matches!(
                sess.early_lto(),
                LtoCli::Yes | LtoCli::Fat | LtoCli::NoParam | LtoCli::Thin
            )
        {
            sess.dcx().fatal("LTO is not supported by the trust-cg codegen backend")
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

        // Object-only builds execute native codegen too: they must not bypass
        // any of the restrictions applied to the rlib archive lane below.
        if native_machine_output_requested(&sess.opts.output_types) {
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
            // `Session::stack_protector` on the EarlySession inputs.
            let stack_protector = if sess.target.options.supports_stack_protector {
                sess.opts.unstable_opts.stack_protector
            } else {
                StackProtector::None
            };
            if stack_protector != StackProtector::None {
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
            return Self::backend_init();
        }

        let bridge = self.bridge_for_session(sess);
        if let Err(e) = bridge.init() {
            sess.dcx().fatal(format!("trust-cg backend initialization failed: {e}"));
        }
        Self::backend_init()
    }

    fn supported_crate_types(&self, sess: &Session) -> Vec<CrateType> {
        supported_crate_types_for_outputs(native_machine_output_requested(&sess.opts.output_types))
    }

    fn supported_link_crate_types(&self, _sess: &Session) -> Vec<CrateType> {
        supported_link_crate_types()
    }

    // Trust (WS7.10 / F-114): with native output requested, `supported_crate_types`
    // advertises `[Rlib]` only, and rustc's default response to any other
    // requested type is to DROP it with a warning. A plain `rustc main.rs`
    // (default crate type `bin`) then exited 0 having produced nothing, and the
    // `codegen_crate` refusal below never ran because `tcx.crate_types()` was
    // already filtered. Turn the drop into an error for every compilation that
    // will run native codegen; keep the warning for Cargo's print-only probe
    // and for `-Zunpretty` / `-Zno-analysis`, which exit before codegen.
    fn unsupported_crate_type_is_fatal(&self, sess: &Session) -> bool {
        unsupported_crate_type_is_fatal_for(
            native_machine_output_requested(&sess.opts.output_types),
            session_exits_before_codegen(sess),
            sess.opts.prints.iter().map(|request| request.kind),
        )
    }

    // Trust: #959 -- register queries needed by the trust-cg backend.
    fn provide(&self, providers: &mut Providers) {
        // trust-cg does not currently inject custom queries into the rustc
        // query system. When we add incremental compilation support or
        // custom optimization queries, they will be registered here.
        //
        // The standard rustc_codegen_ssa queries (symbol_export, etc.)
        // are already registered by the driver before calling into
        // the backend.
        //
        // Trust (plan step 3.3): one HOOK, no query. On the F1 lane the collector takes a
        // Clean-origin item's neighbours from its published trust-ir row, not from
        // `clean_origin_mir`'s MIR; the provider answers `None` (walk the MIR) everywhere else.
        providers.hooks.trust_f1_clean_origin_neighbours =
            trust_ir_frontend::clean_inventory::neighbours;
    }

    fn target_config(&self, sess: &EarlySession) -> TargetConfig {
        if Self::is_wasm_session(sess) {
            return Self::wasm_target_config();
        }

        let bridge = self.bridge_for_session(sess);
        let bridge_config = BridgeCodegenBackend::target_config(&bridge);
        TargetConfig {
            // Upstream 1.101 merged the stable/unstable feature lists into
            // one internal set the session splits by stability itself.
            internal_target_features: bridge_config
                .target_features
                .iter()
                .chain(bridge_config.unstable_target_features.iter())
                .map(|s| Symbol::intern(s))
                .collect(),
            has_reliable_f16: bridge_config.has_reliable_f16,
            has_reliable_f16_math: bridge_config.has_reliable_f16_math,
            // The bridge makes no f16b claim; do not invent one.
            has_reliable_f16b: false,
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

    fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Box<dyn Any> {
        let crate_name = tcx.crate_name(rustc_span::def_id::LOCAL_CRATE).to_string();

        if !native_machine_output_requested(&tcx.sess.opts.output_types) {
            // MIR is emitted by the common driver. Avoid mono collection,
            // verification, and lowering for metadata/dep-info/MIR-only work.
            return Box::new(OngoingTrustCgCodegen {
                bridge_ongoing: None,
                trust_ir_module: None,
                trust_ir_gate_sources: Vec::new(),
                crate_name,
                function_count: 0,
                instance_coverage: None,
                compiler_lane: None,
            });
        }

        // Trust (R-8 fail-open item 3, 2026-10-01): `-Zcodegen-emit-retag` asks the
        // backend to emit Tree Borrows retag calls (R-7 instrumentation). trust-cg
        // emits none, on either frontend, and used to ship the object without them
        // and without a word (docs/audits/2026-09-29-r8-trust-ir-vs-mir.md, "Fails
        // OPEN" item 3). Until it emits them it refuses the flag, so no build can
        // believe it is instrumented when it is not.
        if tcx.sess.opts.unstable_opts.codegen_emit_retag.is_some() {
            tcx.dcx().fatal(
                "trust-cg does not emit the retag calls `-Zcodegen-emit-retag` asks for \
                 (Tree Borrows instrumentation), so it refuses the flag rather than ship an \
                 object without them; build without it, or with the LLVM backend",
            );
        }

        if Self::is_wasm_session(tcx.sess) {
            tcx.dcx().fatal(
                "internal trust-cg invariant violated: native Wasm codegen passed initialization",
            );
        }

        // Trust (WS7.10): belt and braces behind the `collect_crate_types`
        // refusal. Native output with NO crate type left would compile nothing
        // and exit 0; no path should reach here that way, and if one does it
        // must fail loudly rather than succeed empty-handed.
        if tcx.crate_types().is_empty() {
            tcx.dcx().fatal(
                "trust-cg was asked for native machine output but no crate type remains to \
                 emit; every requested crate type was dropped before codegen, and trust-cg \
                 refuses to exit successfully without producing the requested artifact",
            );
        }

        if let Some(crate_type) =
            tcx.crate_types().iter().copied().find(|&kind| kind != CrateType::Rlib)
        {
            tcx.dcx().fatal(format!(
                "trust-cg cannot emit native code for crate type `{crate_type:?}`; the supported machine-output lane is an rlib compilation of External scalar-register functions, as an archive or object. Executables additionally require rustc's process-entry wrapper, and dynamic/static/proc-macro outputs require unwired linkage/visibility contracts"
            ));
        }

        // Trust (step 2 increment 5, sub-step 5.4.2): the compiler lane is a consumer of F1's
        // trust-ir; on the MIR frontend there is none to consume (INC5.4-SCOPE).
        if tcx.sess.trust_cg_f1_backend_is_compiler()
            && trust_cg_frontend(tcx.sess) != TrustCgFrontend::TrustIr
        {
            tcx.dcx().fatal(
                "-Ztrust-cg-f1-backend=compiler selects the consumer of F1's trust-ir and \
                 requires -Ztrust-cg-frontend=trust-ir; the MIR frontend has no compiler lane \
                 (INC5.4-SCOPE)",
            );
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

        let (functions, linkage, statics) =
            build_production_mono_functions(tcx).unwrap_or_else(|reason| {
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

        let bridge_crate_info = bridge_backend::CrateInfo {
            crate_name: crate_name.clone(),
            functions,
            linkage,
            statics,
        };

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
            instance_coverage: None,
            compiler_lane: None,
        })
    }

    // Trust: #959 -- join_codegen now produces meaningful CompiledModules
    // by converting bridge results and emitting LIR object artifacts to disk.
    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        sess: &Session,
        _incr_comp_session: Option<&rustc_session::IncrCompSession>,
        outputs: &OutputFilenames,
        _crate_info: &CrateInfo,
    ) -> (CompiledModules, WorkProductMap) {
        let mut ongoing = ongoing_codegen.downcast::<OngoingTrustCgCodegen>().unwrap();

        // Trust (step 2 increment 5, sub-step 5.4.2): the COMPILER LANE's unit. Its object is
        // the one `CerReport::ships` already allowed; it is written as is, then the
        // certificates file and the coverage artifact that describe it.
        if let Some(unit) = ongoing.compiler_lane.take() {
            let object_path = outputs.temp_path_for_cgu(OutputType::Object, &unit.name);
            if let Err(e) = fs::write(&object_path, &unit.object) {
                sess.dcx()
                    .fatal(format!("trust-cg: failed to write object for `{}`: {e}", unit.name));
            }
            write_trust_cg_certificates(sess, outputs, &unit.report);
            match &unit.coverage {
                Some(coverage) => disclose_instance_coverage(
                    sess,
                    outputs,
                    &ongoing.crate_name,
                    coverage,
                    &[object_path.as_path()],
                ),
                None => clear_instance_coverage(sess, outputs),
            }
            sess.dcx().note(format!(
                "trust-cg: compiled {} function(s) in 1 module(s) via the trust-ir frontend's \
                 compiler lane",
                unit.function_count
            ));
            let module = CompiledModule {
                name: unit.name.clone(),
                kind: ModuleKind::Regular,
                object: Some(object_path.clone()),
                global_asm_object: None,
                dwarf_object: None,
                bytecode: None,
                assembly: None,
                llvm_ir: None,
            };
            if outputs.outputs.should_link() {
                let expected =
                    archive_output::CompilerArchiveObject::new(unit.name, object_path, unit.object)
                        .unwrap_or_else(|reason| sess.dcx().fatal(reason));
                let mut pending = self
                    .compiler_archive_object
                    .lock()
                    .unwrap_or_else(|_| sess.dcx().fatal("Compiler archive handoff lock poisoned"));
                if pending.is_some() {
                    sess.dcx()
                        .fatal("Compiler archive handoff would overwrite unconsumed live bytes");
                }
                *pending = Some(expected);
            }
            return output_artifacts::finish_codegen(
                sess,
                CompiledModules { modules: vec![module], allocator_module: None },
                outputs,
            );
        }

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
            // Trust (owner ruling D17): the per-function coverage disclosure,
            // AFTER the gate accepted the object (emission fatals otherwise), with
            // the verdict every emitted function got under the active policy.
            match &ongoing.instance_coverage {
                Some(coverage) => {
                    let objects: Vec<&std::path::Path> =
                        module.object.iter().map(|p| p.as_path()).collect();
                    disclose_instance_coverage(
                        sess,
                        outputs,
                        &ongoing.crate_name,
                        coverage,
                        &objects,
                    );
                }
                None => clear_instance_coverage(sess, outputs),
            }
            // Trust (step 2 increment 5, sub-step 5.4.2): this compile did not take the
            // compiler lane, so no certificates file describes its object.
            clear_trust_cg_certificates(sess, outputs);
            sess.dcx().note(format!(
                "trust-cg: compiled {} function(s) in 1 module(s) via the trust-ir frontend",
                ongoing.function_count
            ));
            return output_artifacts::finish_codegen(
                sess,
                CompiledModules { modules: vec![module], allocator_module: None },
                outputs,
            );
        }

        let Some(bridge_ongoing) = ongoing.bridge_ongoing else {
            return output_artifacts::finish_codegen(
                sess,
                CompiledModules { modules: vec![], allocator_module: None },
                outputs,
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
                // Each complete bridge CGU contributes one object; internal
                // function symbols must remain in the same object as callers.
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

                output_artifacts::finish_codegen(sess, compiled, outputs)
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
        let expected = self
            .compiler_archive_object
            .lock()
            .unwrap_or_else(|_| sess.dcx().fatal("Compiler archive handoff lock poisoned"))
            .take();
        if let Some(expected) = expected {
            expected
                .require_modules(&compiled_modules)
                .unwrap_or_else(|reason| sess.dcx().fatal(reason));
            let builder = archive_output::CheckedArchiveBuilderBuilder {
                expected: std::sync::Arc::new(expected),
            };
            link_binary(
                sess,
                &builder,
                compiled_modules,
                crate_info,
                metadata,
                outputs,
                self.name(),
            );
            return;
        }
        if outputs.outputs.should_link()
            && sess.trust_cg_f1_backend_is_compiler()
            && trust_cg_frontend(sess) == TrustCgFrontend::TrustIr
            && compiled_modules.modules.iter().any(|module| module.object.is_some())
        {
            sess.dcx().fatal("Compiler archive link lacks its live gated object handoff");
        }
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
