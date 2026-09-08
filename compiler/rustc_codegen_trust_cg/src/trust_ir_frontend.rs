//! trust_ir_frontend: the F1 consumer of finalized direct Trust-IR
//! (`-Ztrust-cg-frontend=trust-ir`).
//!
//! # What this is, and what it is not
//!
//! The source -> TrustIR PRODUCER already ships and is on: `trust_ir_of` is a
//! registered rustc query (`rustc_mir_build::provide`) with a first-class
//! `--emit=trust-ir` artifact lane. What did not exist was a CONSUMER: nothing
//! in codegen ever asked for it, so the trust-cg backend built its
//! `VerifiableFunction`s from MIR and the "source -> TrustIR -> object" path
//! (F1) had never been executed end to end, only measured offline on dumped
//! modules.
//!
//! `trust_ir_of` still creates the per-body inputs during analysis. Crate
//! finalization validates, collision-renames and call-links those bodies, then
//! stores the resulting Module together with an exact definition-to-FuncId
//! handoff. This module is the codegen consumer. For each reachable monomorphic
//! function it:
//!
//! 1. resolves the item's non-generic local `LocalDefId`,
//! 2. selects its assembled FuncId through the conjunctive
//!    `(DefIndex, DefPathHash)` handoff — never through `def_path_str`,
//! 3. renames that selected function to the item's MANGLED SYMBOL NAME, and
//! 4. routes the module through `trust_cg_bridge::lower_module_to_lir`, whose
//!    LIR feeds the SAME object emitter the MIR path uses.
//!
//! It is NOT a second inventory. The mono-item collection, the linkage /
//! visibility gate and the instance ABI validation are the exact functions the
//! production path calls, so the two paths compile the same set of symbols and
//! differ only in where each function's IR came from.
//!
//! # Fail-closed contract
//!
//! Every step above is a REFUSAL, never a fallback:
//!
//! * an instance whose definition is not a local, non-generic body — refused;
//! * an absent assembled handoff or absent exact definition entry — refused;
//! * a handoff whose selected function or function type is absent — refused;
//! * `lower_module_to_lir` returning any `ModuleLirError` — refused.
//!
//! A refusal is `Err` here and `sess.dcx().fatal` at the call site. There is
//! deliberately no fallback to MIR or to the per-body artifact. The latter has
//! local callees only as bodyless declarations, and retrying it used to hide an
//! assembled-selection miss until conversion happened to fail later.
//!
//! # How this path IS verified
//!
//! The M-POS proven-output gate now has a trust-ir entry point:
//! `trust_cg_bridge::verify_output_trust_ir`. Its spec side is derived from the
//! selected function in the producer's finalized assembled Module, BEFORE any
//! LIR lowering, while its machine side is the unchanged
//! `PathMergingExecutor` over the EMITTED BYTES. So this module carries the
//! producer Module alongside the LIR ([`TrustIrLoweredFunction::gate_source`])
//! and hands it to the gate at emission time.
//!
//! `source_functions` on the assembled `CompiledModule` stays `None` and that is
//! still the honest value: there is no `VerifiableFunction` behind these bytes.
//! What changed is that the trust-ir gate does not need one, and `lib.rs` no
//! longer treats `None` as "nothing to check" — the F1 emission path refuses
//! outright unless it has a 1:1 trust-ir work list to verify.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_middle::ty::{self, TyCtxt};
use trust_cg_bridge::codegen_backend as bridge_backend;
use trust_ir::value::FuncId;

/// Why the trust-ir frontend refused a reachable mono-item.
///
/// Every variant is a compile error at the call site. None of them is a reason
/// to compile the item some other way.
#[derive(Debug)]
pub(crate) enum FrontendRefusal {
    /// The instance is not a plain local item body, so no `LocalDefId` keys the
    /// `trust_ir_of` query for it (shims, drop glue, foreign definitions).
    NotALocalItem { symbol: String, detail: String },
    /// The instance carries generic arguments. `trust_ir_of` is keyed on
    /// `LocalDefId` and lowers the body PRE-MONOMORPHIZATION, so its Module is
    /// not this instance's IR and must not be emitted under this symbol.
    GenericInstance { symbol: String, args: String },
    /// The item's ABI is outside the fragment the backend emits. This is the
    /// same check the production path runs; it is a property of the instance,
    /// not of the IR, so both frontends must apply it.
    UnsupportedAbi { symbol: String, detail: String },
    /// Finalization did not install the assembled crate-module handoff.
    AssembledHandoffUnavailable { symbol: String },
    /// The handoff exists but carries no entry for the exact local definition.
    ExactAssembledBodyAbsent { symbol: String, def_index: u32, definition: String },
    /// The checked handoff selected a FuncId the Module no longer carries.
    SelectedFunctionMissing { symbol: String, func_id: u32, functions: usize },
    /// The body function references a `FuncTy` the Module does not carry, so
    /// its parameter count — which the ABI cross-check needs — is unknowable.
    MissingFuncType { symbol: String, ty: u32 },
    /// `lower_module_to_lir` refused the module.
    ConverterRefused { symbol: String, detail: String },
}

impl std::fmt::Display for FrontendRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotALocalItem { symbol, detail } => write!(
                f,
                "`{symbol}`: the trust-ir frontend has no artifact for this instance ({detail}); \
                 `trust_ir_of` is keyed on a local body's `LocalDefId`"
            ),
            Self::GenericInstance { symbol, args } => write!(
                f,
                "`{symbol}`: instance carries generic arguments `{args}`, but `trust_ir_of` \
                 lowers the body pre-monomorphization; emitting that Module under this symbol \
                 would ship IR that was never instantiated"
            ),
            Self::UnsupportedAbi { symbol, detail } => {
                write!(f, "`{symbol}`: unsupported definition ABI: {detail}")
            }
            Self::AssembledHandoffUnavailable { symbol } => write!(
                f,
                "`{symbol}`: finalization installed no validated assembled Trust-IR module; \
                 refusing to retry a per-body artifact"
            ),
            Self::ExactAssembledBodyAbsent { symbol, def_index, definition } => write!(
                f,
                "`{symbol}`: the assembled Trust-IR handoff has no body for exact identity \
                 (DefIndex({def_index}), {definition}); refusing display-name selection and \
                 per-body fallback"
            ),
            Self::SelectedFunctionMissing { symbol, func_id, functions } => write!(
                f,
                "`{symbol}`: the assembled Trust-IR handoff selected missing FuncId({func_id}); \
                 the Module carries {functions} function(s)"
            ),
            Self::MissingFuncType { symbol, ty } => write!(
                f,
                "`{symbol}`: the body function names `FuncTyId({ty})`, which the produced Module \
                 does not carry"
            ),
            Self::ConverterRefused { symbol, detail } => write!(
                f,
                "`{symbol}`: `lower_module_to_lir` refused the source-derived Module: {detail}"
            ),
        }
    }
}

/// Resolve the `LocalDefId` whose `trust_ir_of` artifact IS this instance's
/// body, or say precisely why there is none.
fn local_body_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    symbol: &str,
) -> Result<rustc_span::def_id::LocalDefId, FrontendRefusal> {
    // Only a plain item body has a THIR the producer lowers. Every other
    // `InstanceKind` (drop glue, vtable/fn-ptr shims, `#[no_mangle]` re-exports
    // of foreign definitions, intrinsics) is compiler-synthesized: it has no
    // source body at all, so there is nothing for `trust_ir_of` to have
    // produced and nothing to fall back to.
    let ty::InstanceKind::Item(def_id) = instance.def else {
        return Err(FrontendRefusal::NotALocalItem {
            symbol: symbol.to_string(),
            detail: format!("compiler-synthesized instance kind {:?}", instance.def),
        });
    };
    let Some(local) = def_id.as_local() else {
        return Err(FrontendRefusal::NotALocalItem {
            symbol: symbol.to_string(),
            detail: format!("body lives in an upstream crate (`{}`)", tcx.def_path_str(def_id)),
        });
    };
    // A CONSTRUCTOR used as a function value (`map(Value::Number)`) is a
    // compiler-synthesized shim: the variant/struct declaration owns no THIR
    // body, so forcing `trust_ir_of` on it ICEs inside `thir_body`
    // (`has no associated body`). Refuse it by name instead — it is the same
    // no-source-body class as the InstanceKind shims above.
    if matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::Ctor(..)) {
        return Err(FrontendRefusal::NotALocalItem {
            symbol: symbol.to_string(),
            detail: format!(
                "constructor shim `{}` has no source body (compiler-synthesized)",
                tcx.def_path_str(def_id)
            ),
        });
    }
    // A LIFETIME-ONLY instantiation is not a monomorphization.
    //
    // The refusal below exists because `trust_ir_of` lowers a body BEFORE
    // monomorphization, so its Module is not the IR of an instance that
    // substituted types or consts. A region argument substitutes neither: regions
    // have no runtime representation at all, codegen erases them (every arg here
    // is `'{erased}` by the time an `Instance` reaches codegen), and rustc mangles
    // ONE symbol for the whole family — which is why `<Input<'_> as Debug>::fmt`
    // arrives with `args = ['{erased}]` and a single mangled name. For such an
    // instance the pre-monomorphization body IS this instance's body, so admitting
    // it does not emit IR that was never instantiated; it emits the only IR there
    // is.
    //
    // Kept as narrow as the claim: EVERY argument must be a region. One type or
    // const argument and this is a real monomorphization again, refused as before.
    // MEASURED: 526 of the 1,677 generic refusals across the 277 real crates that
    // reach this frontend are lifetime-only.
    if !instance.args.is_empty() && !instance.args.iter().all(|arg| arg.as_region().is_some()) {
        return Err(FrontendRefusal::GenericInstance {
            symbol: symbol.to_string(),
            args: format!("{:?}", instance.args),
        });
    }
    Ok(local)
}

/// Lower ONE reachable mono-item through source -> assembled Trust-IR -> LIR.
///
/// `validate_abi` is the production path's instance-ABI check
/// (`validate_codegen_instance_abi`), threaded in so the two frontends admit
/// exactly the same symbols. Its third argument is "how many arguments the
/// executable IR exposes", which rustc's `FnAbi` is cross-checked against; on
/// the MIR path that is `mir::Body::arg_count`, and here it is the produced
/// `FuncTy`'s parameter count — the same question asked of the IR that will
/// actually be emitted, which is what makes the check meaningful on this path
/// rather than decorative.
///
/// Returns the LIR function on success. `Err` is a compile error; it is never a
/// reason to lower this item from MIR instead.
pub(crate) fn lower_instance<'tcx, V>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    validate_abi: V,
) -> Result<TrustIrLoweredFunction, FrontendRefusal>
where
    V: Fn(TyCtxt<'tcx>, ty::Instance<'tcx>, usize) -> Result<(), String>,
{
    let symbol = tcx.symbol_name(instance).name.to_string();
    // UPSTREAM-INSTANCE lane (-Ztrust-ir-upstream-mir): a body that lives in an
    // upstream crate can never have a source-first `trust_ir_of` artifact (the
    // producer is THIR-based and THIR is local-only). Under the explicit flag,
    // bridge its monomorphized MIR into trust-ir and feed the SAME converter
    // and proven-output gate; without the flag the refusal below stands. Local
    // items are NEVER routed here — a local body still comes only from
    // `trust_ir_of`, so this is not a fallback, it is the only IR there is.
    if tcx.sess.trust_ir_upstream_mir()
        && let ty::InstanceKind::Item(item_def_id) = instance.def
        && !item_def_id.is_local()
    {
        return lower_upstream_instance(tcx, instance, &symbol, &validate_abi);
    }
    let def = local_body_def(tcx, instance, &symbol)?;

    // The assembled module is the only artifact whose local call edges name
    // real bodies. Selection is by the producer's exact identity handoff, not
    // by `Function.name`: collision-renamed macro definitions intentionally no
    // longer equal `tcx.def_path_str(def)`. Any missing handoff/identity or any
    // lowering failure is final. Retrying the single-body artifact would both
    // reintroduce display-name ambiguity and turn its local callees back into
    // bodyless declarations.
    let selected = match assembled_crate_body(tcx, def) {
        Ok(selected) => selected,
        Err(trust_thir_lower::AssembledBodyLookupError::HandoffUnavailable) => {
            return Err(FrontendRefusal::AssembledHandoffUnavailable { symbol });
        }
        Err(trust_thir_lower::AssembledBodyLookupError::ExactBodyAbsent {
            def_index,
            definition,
        }) => {
            return Err(FrontendRefusal::ExactAssembledBodyAbsent {
                symbol,
                def_index,
                definition,
            });
        }
    };
    lower_from_module(tcx, instance, &symbol, &selected.module, selected.func_id, &validate_abi)
}

/// Select the exact finalize-assembled body stored for this frontend.
fn assembled_crate_body(
    tcx: TyCtxt<'_>,
    def: rustc_span::def_id::LocalDefId,
) -> Result<
    trust_thir_lower::ExactAssembledBodyForCodegen,
    trust_thir_lower::AssembledBodyLookupError,
> {
    tcx.sess.with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
        |slot| slot.exact_body(tcx, def),
    )
}

/// The assembled lowering tail: ABI cross-check, symbol stamping on a private
/// clone, `lower_module_to_lir`, and the gate source.
fn lower_from_module<'tcx, V>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    symbol: &str,
    produced: &trust_ir::Module,
    func_id: FuncId,
    validate_abi: &V,
) -> Result<TrustIrLoweredFunction, FrontendRefusal>
where
    V: Fn(TyCtxt<'tcx>, ty::Instance<'tcx>, usize) -> Result<(), String>,
{
    let ir_param_count = {
        let function =
            produced.function_by_id(func_id).ok_or(FrontendRefusal::SelectedFunctionMissing {
                symbol: symbol.to_string(),
                func_id: func_id.index(),
                functions: produced.functions.len(),
            })?;
        produced
            .func_types
            .get(function.ty.as_usize())
            .ok_or(FrontendRefusal::MissingFuncType {
                symbol: symbol.to_string(),
                ty: function.ty.index(),
            })?
            .params
            .len()
    };

    validate_abi(tcx, instance, ir_param_count)
        .map_err(|detail| FrontendRefusal::UnsupportedAbi { symbol: symbol.to_string(), detail })?;

    // The assembled function still carries a producer operational name: the
    // display path when unique, or a stable collision name when it is not. The
    // object's symbol table needs rustc's actual link-time identity, so stamp
    // the selected FuncId on a private clone exactly where the MIR path stamps
    // it (`func.name = symbol_name`). The shared crate module is never mutated.
    let mut module = produced.clone();
    if let Some(function) = module.function_by_id_mut(func_id) {
        function.name = symbol.to_string();
    }

    let lir = trust_cg_bridge::lower_module_to_lir(&module, func_id).map_err(|e| {
        FrontendRefusal::ConverterRefused { symbol: symbol.to_string(), detail: e.to_string() }
    })?;

    let instructions: usize = lir.blocks.values().map(|block| block.instructions.len()).sum();
    tracing::debug!(
        symbol = %symbol,
        lir_instructions = instructions,
        "[trust_cg] trust-ir frontend lowered a function assembled Trust-IR -> LIR"
    );

    // The gate's SPEC INPUT: the renamed producer Module, carried whole. This is
    // the same value `lower_module_to_lir` was just handed, so the specification
    // and the shipped bytes provably describe one function — the gate re-lowers
    // from it and refuses if the resulting symbol is not `symbol`.
    let gate_source = trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource {
        symbol: symbol.to_string(),
        module,
        func_id,
    };

    Ok(TrustIrLoweredFunction { symbol: symbol.to_string(), lir, gate_source })
}

/// The UPSTREAM-INSTANCE lane: bridge a monomorphized upstream body's MIR into
/// trust-ir and hand it to the shared converter/gate tail.
///
/// PROVENANCE IS THE ONLY DIFFERENCE from the local path: the Module here is
/// derived from rustc MIR (`extract_mono_verifiable_function` — the exact
/// extraction the shipped MIR path performs — then
/// `trust_ir_bridge::lower_to_trust_ir`, the same spine the THIR/MIR
/// differential's oracle side uses), not from the source-first producer. The
/// converter and the proven-output gate downstream are byte-for-byte the same
/// code; a shape either refuses honestly or is verified against this Module.
fn lower_upstream_instance<'tcx, V>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    symbol: &str,
    validate_abi: &V,
) -> Result<TrustIrLoweredFunction, FrontendRefusal>
where
    V: Fn(TyCtxt<'tcx>, ty::Instance<'tcx>, usize) -> Result<(), String>,
{
    let vf = crate::extract_mono_verifiable_function_with_abi(tcx, instance, true, validate_abi)
        .map_err(|detail| FrontendRefusal::NotALocalItem {
            symbol: symbol.to_string(),
            detail: format!("upstream MIR extraction refused: {detail}"),
        })?;
    let module = trust_ir_bridge::lower_mir_compat_to_trust_ir(&vf).map_err(|e| {
        FrontendRefusal::NotALocalItem {
            symbol: symbol.to_string(),
            detail: format!("upstream MIR -> trust-ir bridge refused: {e}"),
        }
    })?;
    // `lower_to_trust_ir` builds a SINGLE-function Module registered at
    // FuncId 0; `lower_from_module` re-checks existence and stamps the mangled
    // symbol on a private clone exactly as the local path does.
    let func_id = FuncId::new(0);
    lower_from_module(tcx, instance, symbol, &module, func_id, validate_abi)
}

/// One function that completed assembled Trust-IR -> `lower_module_to_lir`.
pub(crate) struct TrustIrLoweredFunction {
    /// The mangled symbol this function is emitted under.
    pub(crate) symbol: String,
    /// The LIR the shared object emitter consumes.
    pub(crate) lir: trust_cg_bridge::codegen_backend::LirFunction,
    /// The producer's trust-ir, kept so the proven-output gate has a
    /// specification for these bytes that was NOT derived from the lowering.
    pub(crate) gate_source: trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource,
}

/// Assemble the codegen unit's LIR into the bridge module shape the object
/// emitter consumes.
///
/// `source_functions` is `None` BY CONSTRUCTION and that is still the honest
/// value: there is no `VerifiableFunction` behind these bytes. The gate work
/// list is returned SEPARATELY, as `Vec<TrustIrGateSource>`, 1:1 and in the same
/// order as `lir_functions`. The caller must not let a `None` here read as
/// "nothing to check": on this path the thing to check is the trust-ir list.
///
/// Two tripwires are CHECKED here rather than assumed, because both would be
/// silent corruptions of the emitted symbol table:
///
/// * `linkage` is consumed index-aligned with `lir_functions` by
///   `emit_module_object`, so a length mismatch would bind symbols against a
///   mis-indexed vector;
/// * each LIR function must carry the MANGLED SYMBOL the item is emitted under.
///   The converter takes the name from the trust-ir function, and the rename
///   that puts the mangled name there is the only thing standing between this
///   object and a symbol table full of producer operational labels.
pub(crate) fn compiled_module(
    crate_name: &str,
    lowered: Vec<TrustIrLoweredFunction>,
    linkage: Vec<bridge_backend::FunctionLinkage>,
    statics: Vec<bridge_backend::ObjectGlobal>,
) -> Result<
    (
        bridge_backend::CompiledModule,
        Vec<trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource>,
    ),
    String,
> {
    let function_count = lowered.len();
    if linkage.len() != function_count {
        return Err(format!(
            "{function_count} trust-ir function(s) carry {} linkage entries",
            linkage.len()
        ));
    }
    for function in &lowered {
        if function.lir.name != function.symbol {
            return Err(format!(
                "lowered LIR for `{}` carries the name `{}`; the mangled symbol did not survive \
                 conversion",
                function.symbol, function.lir.name
            ));
        }
        if function.gate_source.symbol != function.symbol {
            return Err(format!(
                "gate source for `{}` is labelled `{}`; refusing to verify one function and \
                 ship another",
                function.symbol, function.gate_source.symbol
            ));
        }
    }
    let mut lir_functions = Vec::with_capacity(function_count);
    let mut gate_sources = Vec::with_capacity(function_count);
    for function in lowered {
        lir_functions.push(function.lir);
        gate_sources.push(function.gate_source);
    }
    Ok((
        bridge_backend::CompiledModule {
            name: format!("{crate_name}.codegen_unit.0"),
            lir_functions,
            object_path: None,
            function_count,
            source_functions: None,
            linkage,
            statics,
        },
        gate_sources,
    ))
}
