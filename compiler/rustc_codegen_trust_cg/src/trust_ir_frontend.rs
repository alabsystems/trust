//! trust_ir_frontend: the F1 CONSUMER of `trust_ir_of` (`-Ztrust-cg-frontend=trust-ir`).
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
//! This module is that consumer. For each reachable monomorphic function it:
//!
//! 1. resolves the item's `LocalDefId` and forces `tcx.trust_ir_of(def)`,
//! 2. renames the body function (`FuncId(0)`) to the item's MANGLED SYMBOL
//!    NAME — the producer labels it with `def_path_str`, which is a human label
//!    and not a link-time identity, and
//! 3. routes the module through `trust_cg_bridge::lower_module_to_lir`, whose
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
//! * `trust_ir_of` returning `None` (the producer declined the body, or
//!   `-Ztrust-ir-lower` is not on) — refused;
//! * a module whose body function is missing or whose id layout is not the
//!   producer's `FuncId(0)` convention — refused;
//! * `lower_module_to_lir` returning any `ModuleLirError` — refused.
//!
//! A refusal is `Err` here and `sess.dcx().fatal` at the call site. There is
//! deliberately no "fall back to MIR for this one item" arm: an earlier probe in
//! this program (`trust_ir_codegen::probe_module_to_lir`) was log-only and never
//! altered emission, which is exactly why F1 was never actually measured. A flag
//! that silently degrades to the shipped path is not evidence of anything.
//!
//! # How this path IS verified
//!
//! The M-POS proven-output gate now has a trust-ir entry point:
//! `trust_cg_bridge::verify_output_trust_ir`. Its spec side is derived from the
//! PRODUCER's `trust_ir::Function` — the artifact `trust_ir_of` returned, BEFORE
//! any lowering — while its machine side is the unchanged
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

/// The producer's body-function id convention.
///
/// `trust_thir_lower::finish_body` mints the body as `Function::new(FuncId(0),
/// ..)` and any producer-synthesized fn-pointer adapters are appended AFTER it
/// (that ordering is load-bearing for `crate_module::record`, which takes
/// `functions.remove(0)` as the body). We depend on the same convention, and we
/// CHECK it rather than assume it: see `body_function_id`.
const BODY_FUNC_ID: FuncId = FuncId::new(0);

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
    /// `trust_ir_of` returned `None`: the producer declined this body (or the
    /// direct frontend is not enabled).
    ProducerDeclined { symbol: String, def_path: String },
    /// The Module does not carry a body function under the producer's id
    /// convention.
    NoBodyFunction { symbol: String, functions: usize },
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
            Self::ProducerDeclined { symbol, def_path } => write!(
                f,
                "`{symbol}` (`{def_path}`): the direct THIR -> trust-ir producer declined this \
                 body, so no source-derived Module exists for it (`trust_ir_of` returned None)"
            ),
            Self::NoBodyFunction { symbol, functions } => write!(
                f,
                "`{symbol}`: the produced Module carries {functions} function(s) but none under \
                 the producer's body id `FuncId(0)`"
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

/// The body function of a producer Module, checked against the producer's id
/// convention rather than assumed from position.
fn body_function_id(module: &trust_ir::Module, symbol: &str) -> Result<FuncId, FrontendRefusal> {
    if module.function_by_id(BODY_FUNC_ID).is_some() {
        return Ok(BODY_FUNC_ID);
    }
    Err(FrontendRefusal::NoBodyFunction {
        symbol: symbol.to_string(),
        functions: module.functions.len(),
    })
}

/// Lower ONE reachable mono-item through source -> `trust_ir_of` -> LIR.
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
    V: FnOnce(TyCtxt<'tcx>, ty::Instance<'tcx>, usize) -> Result<(), String>,
{
    let symbol = tcx.symbol_name(instance).name.to_string();
    let def = local_body_def(tcx, instance, &symbol)?;

    // THE CONSUMPTION. This is the call that did not exist anywhere in codegen
    // before: the backend asking the source-first producer for its artifact.
    let Some(produced) = tcx.trust_ir_of(def) else {
        return Err(FrontendRefusal::ProducerDeclined {
            symbol,
            def_path: tcx.def_path_str(def.to_def_id()),
        });
    };

    let func_id = body_function_id(produced, &symbol)?;
    let ir_param_count = {
        // `body_function_id` just proved this resolves.
        let function = produced.function_by_id(func_id).ok_or(FrontendRefusal::NoBodyFunction {
            symbol: symbol.clone(),
            functions: produced.functions.len(),
        })?;
        produced
            .func_types
            .get(function.ty.as_usize())
            .ok_or(FrontendRefusal::MissingFuncType {
                symbol: symbol.clone(),
                ty: function.ty.index(),
            })?
            .params
            .len()
    };

    validate_abi(tcx, instance, ir_param_count)
        .map_err(|detail| FrontendRefusal::UnsupportedAbi { symbol: symbol.clone(), detail })?;

    // The producer names the body `def_path_str` — deliberately, since that is
    // "only a label on this single-function module". The object's symbol table
    // is not a label, so the LINK-TIME identity is stamped here, on a private
    // clone, exactly where the MIR path stamps it (`func.name = symbol_name`).
    // The arena-allocated query result is never mutated.
    let mut module = produced.clone();
    if let Some(function) = module.function_by_id_mut(func_id) {
        function.name = symbol.clone();
    }

    let lir = trust_cg_bridge::lower_module_to_lir(&module, func_id).map_err(|e| {
        FrontendRefusal::ConverterRefused { symbol: symbol.clone(), detail: e.to_string() }
    })?;

    let instructions: usize = lir.blocks.values().map(|block| block.instructions.len()).sum();
    tracing::debug!(
        symbol = %symbol,
        lir_instructions = instructions,
        "[trust_cg] trust-ir frontend lowered a function source -> trust_ir_of -> LIR"
    );

    // The gate's SPEC INPUT: the renamed producer Module, carried whole. This is
    // the same value `lower_module_to_lir` was just handed, so the specification
    // and the shipped bytes provably describe one function — the gate re-lowers
    // from it and refuses if the resulting symbol is not `symbol`.
    let gate_source = trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource {
        symbol: symbol.clone(),
        module,
        func_id,
    };

    Ok(TrustIrLoweredFunction { symbol, lir, gate_source })
}

/// One function that completed source -> `trust_ir_of` -> `lower_module_to_lir`.
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
///   object and a symbol table full of `def_path_str` labels.
pub(crate) fn compiled_module(
    crate_name: &str,
    lowered: Vec<TrustIrLoweredFunction>,
    linkage: Vec<bridge_backend::FunctionLinkage>,
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
        },
        gate_sources,
    ))
}
