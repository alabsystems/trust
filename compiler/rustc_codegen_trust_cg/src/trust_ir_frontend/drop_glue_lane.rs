//! Trust (step 2 increment 4c of `docs/plans/2026-09-29-trust-ir-sole-compile-path.md`, design
//! `docs/design/2026-09-29-step2-inc4-drops.md` §4): THE DROP-GLUE LANE — which synthesized drop
//! glue enters the codegen module, and the RESOLUTION of every `Inst::Drop` the producer emitted
//! (increment 4b) into a call of that glue, on the opt-in `-Ztrust-cg-frontend=trust-ir` lane.
//!
//! # What this file decides
//!
//! It computes a SPLICE DECISION, so under the manifest's rule (`scripts/frozen-files.txt`) it is
//! FROZEN, BYTE-IDENTICAL, joining at landing as D17 ruled for `instance_assembly.rs` (owner
//! ruling D18 OD-2: synthesized glue splices under D17's rule — structural checks plus the
//! test-oracle differential, NO per-instance MIR seam differential, disclosed per function):
//!
//! * the LANE CONDITION: glue is spliced, and drops resolved, only when the session's output-gate
//!   policy is the strict one (`instance_assembly::strict_gate_from`, D17's condition for a body
//!   with no source). Under any other policy this lane does nothing and every consumer refuses
//!   `Inst::Drop` by name, exactly as before this increment;
//! * for every drop-bearing function of a codegen module: which rustc type each `Inst::Drop`
//!   drops (the producer's `DropSite` for its pointer — `drops.rs` — recovered from the body's
//!   own typeck results by `type_id_hash`), and which glue instance that is
//!   (`Instance::resolve_drop_glue`);
//! * which glue bodies enter the module: [`glue_plan`]'s plan, admitted only when every callee
//!   it names is present — the destructor as its admitted handoff body (a monomorphic LOCAL
//!   `Drop` impl), every child glue admitted by this same lane — and when the glue is one the
//!   collector lists as a LOCAL item of this crate (work-list agreement, design §4.2);
//! * the REWRITE (`drop_glue::rewrite_drops`, all or nothing per function), and its
//!   POSTCONDITION on the whole resolved module: no `Inst::Drop` survives
//!   (`drop_glue::first_surviving_drop`), every rewritten call names a function whose name is
//!   `symbol_name(resolve_drop_glue(T))`, the global and type tables are the base module's, and
//!   the finalize validator accepts it. A failed postcondition refuses EVERY item that would
//!   lower from that module;
//! * a function whose drops do not resolve is STRIPPED to a declaration in the resolved module
//!   (never lowered with a drop left in it) and refused with the reason, and so is every item
//!   whose call census reaches it.
//!
//! NOT decided here (unfrozen inputs, listed as residuals in `scripts/frozen-files.txt`): the glue
//! PRODUCER (`trust_thir_lower::drop_glue`: the plan from layout, the synthesis, the rewrite
//! primitive), which the frozen oracle `drop_glue_oracle.rs` checks over a corpus
//! (`tests/run-make/trust-cg-f1-drop-glue`); the producer's drop sites (`drops.rs`, carried by
//! `effect_conservation.rs`); the frontend's ROUTING (`trust_ir_frontend::lower_instance` takes a
//! glue item's IR from [`GlueLane::glue_item`] and every drop-bearing item's from
//! [`GlueLane::resolve_for`]).
//!
//! # What the resolved module is
//!
//! A private copy of the module an item lowers from (the finalize-assembled handoff module, or
//! the instance lane's `star`) with the glue bodies APPENDED (table-free: they add functions and
//! function types only) and every `Inst::Drop` rewritten to `Inst::Call { glue, [ptr] }`. The
//! base module is never mutated. A module with no `Inst::Drop` reachable from the item is not
//! touched at all: such an item lowers exactly as before.
//!
//! # The v55 drop-glue table (D20) — what this choice commits
//!
//! Trust's trust-ir pin is v47. The lane resolves drops to DIRECT CALLS, which needs no format
//! change. When the pin moves to v55, rule S3 refuses a direct call of a glue function that the
//! module's drop-glue table REGISTERS (`docs/first-party-pin-ledger.md` entry (g)): this lane
//! must then either keep rewriting and register no row, or stop rewriting and register every
//! glue body. It registers none today.
//!
//! What it does NOT make true: that a glue call executes. `module_to_lir` runs with
//! `real_calls=false` and inlines only a callee that flattens to pure scalar code, so a glue call
//! that does not inline is `[converter-refused]` until increment 5.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::ty::{self, Ty as RustcTy, TyCtxt, TypeVisitableExt};
use trust_cg_bridge::codegen_backend as bridge_backend;
use trust_ir::function_dependencies::{DependencyNode, inspect_function_dependencies};
use trust_ir::value::{BlockId, FuncId, TyId};
use trust_ir::{BodyGate, FatPtrKind, Inst, Module, Ty};
use trust_thir_lower::drop_glue::{self, GlueRefusalClass, GlueShape};

use super::{FrontendRefusal, RefusalClass};

/// Why a function or a glue body is refused by this lane.
#[derive(Clone, Debug)]
pub(crate) struct LaneRefusal {
    pub(crate) class: RefusalClass,
    pub(crate) detail: String,
}

fn lane_refusal(class: RefusalClass, detail: impl Into<String>) -> LaneRefusal {
    LaneRefusal { class, detail: detail.into() }
}

impl LaneRefusal {
    fn into_frontend(self, symbol: &str) -> FrontendRefusal {
        FrontendRefusal::DropGlue {
            symbol: symbol.to_string(),
            class: self.class,
            detail: self.detail,
        }
    }
}

/// The frontend class of a producer refusal.
fn class_of(class: GlueRefusalClass) -> RefusalClass {
    match class {
        GlueRefusalClass::UpstreamBody => RefusalClass::UpstreamBody,
        GlueRefusalClass::Shape => RefusalClass::SynthesizedInstance,
    }
}

/// Is `instance` a drop-glue item of a type (`Shim(DropGlue(_, Some(T)))`)?
pub(crate) fn is_glue_item(instance: ty::Instance<'_>) -> bool {
    drop_glue::glue_instance_ty(instance).is_some()
}

/// D17's condition, applied to glue (D18 OD-2): is the session's output-gate policy the strict
/// one? The same function the emission path and the instance assembler call.
#[allow(rustc::bad_opt_access)]
fn session_gate_is_strict(sess: &rustc_session::Session) -> bool {
    super::instance_assembly::strict_gate_from(
        sess.trust_strict_verification_enabled(),
        &sess.opts.unstable_opts.trust_cg_output_gate,
    )
}

/// The functions `root` reaches through DIRECT CALLS, `root` first: what the converter's leaf
/// inliner can splice into the item's code. A function only NAMED (a function-pointer value) is
/// not reached: it is lowered as its own item, against its own resolution. PURE.
pub(crate) fn call_closure(module: &Module, root: FuncId) -> Vec<FuncId> {
    let mut out = vec![root];
    let mut i = 0;
    while i < out.len() {
        if let Some(function) = module.function_by_id(out[i]) {
            for node in function.blocks.iter().flat_map(|b| b.body.iter()) {
                if let Inst::Call { callee, .. } = &node.inst {
                    if !out.contains(callee) {
                        out.push(*callee);
                    }
                }
            }
        }
        i += 1;
    }
    out
}

/// Does any function `root` reaches through direct calls carry an `Inst::Drop`? PURE.
pub(crate) fn reaches_drop(module: &Module, root: FuncId) -> bool {
    call_closure(module, root)
        .into_iter()
        .any(|id| module.function_by_id(id).is_some_and(|f| !drop_glue::drop_nodes(f).is_empty()))
}

/// The functions the census from `root` reaches, `root` included. PURE.
fn reached_functions(module: &Module, root: FuncId) -> Vec<FuncId> {
    inspect_function_dependencies(module, root)
        .nodes()
        .iter()
        .filter_map(|node| match node {
            DependencyNode::Function(id) => Some(*id),
            _ => None,
        })
        .collect()
}

/// THE TABLE TRIPWIRE: the resolved module carries exactly the base's global and type tables.
/// PURE.
pub(crate) fn tables_unchanged(base: &Module, resolved: &Module) -> Result<(), String> {
    let same = [
        ("globals", base.globals == resolved.globals),
        ("types", base.types == resolved.types),
        ("structs", base.structs == resolved.structs),
        ("enums", base.enums == resolved.enums),
        ("records", base.records == resolved.records),
        ("closure_types", base.closure_types == resolved.closure_types),
        ("closure_layouts", base.closure_layouts == resolved.closure_layouts),
        ("target_info", base.target_info == resolved.target_info),
        ("tuple_layouts", base.tuple_layouts == resolved.tuple_layouts),
    ];
    match same.iter().find(|(_, equal)| !equal) {
        Some((table, _)) => Err(format!(
            "the drop-resolved codegen module's `{table}` table differs from its base's"
        )),
        None => Ok(()),
    }
}

/// One resolved module.
struct Resolution<'tcx> {
    module: Arc<Module>,
    /// Functions whose drops did not resolve (stripped to declarations in `module`).
    refused_functions: BTreeMap<FuncId, LaneRefusal>,
    /// The slot of every glue instance asked for.
    glue: FxHashMap<ty::Instance<'tcx>, Result<FuncId, LaneRefusal>>,
    /// The whole-module postcondition's refusal: nothing lowers from `module` then.
    module_refused: Option<String>,
}

/// The per-codegen-unit state of the lane: its condition, the collector's glue items, and the
/// resolved copy of every base module an item lowered from.
pub(crate) struct GlueLane<'tcx> {
    strict_gate: bool,
    /// The collector's drop-glue items with a type, in inventory order.
    inventory: Vec<ty::Instance<'tcx>>,
    inventory_set: FxHashSet<ty::Instance<'tcx>>,
    /// `(address of the base module, its resolution)`.
    contexts: Vec<(usize, Resolution<'tcx>)>,
}

impl<'tcx> GlueLane<'tcx> {
    /// The lane for this inventory (`collect_production_mono_instances`).
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        instances: &[(String, ty::Instance<'tcx>, bridge_backend::FunctionLinkage)],
    ) -> Self {
        let inventory: Vec<ty::Instance<'tcx>> =
            instances.iter().map(|(_, i, _)| *i).filter(|i| is_glue_item(*i)).collect();
        let inventory_set = inventory.iter().copied().collect();
        GlueLane {
            strict_gate: session_gate_is_strict(tcx.sess),
            inventory,
            inventory_set,
            contexts: Vec::new(),
        }
    }

    /// Whether the lane splices anything in this session (D17's strict condition).
    pub(crate) fn active(&self) -> bool {
        self.strict_gate
    }

    fn resolution(&mut self, tcx: TyCtxt<'tcx>, base: &Module) -> &Resolution<'tcx> {
        let key = std::ptr::from_ref(base) as usize;
        let index = match self.contexts.iter().position(|(k, _)| *k == key) {
            Some(i) => i,
            None => {
                // Types and paths in full: trimmed paths may be computed only for an emitted
                // diagnostic, and a refusal's detail is built here whether or not it is printed.
                let resolution = rustc_middle::ty::print::with_no_trimmed_paths!(resolve(
                    tcx,
                    base,
                    &self.inventory,
                    &self.inventory_set
                ));
                self.contexts.push((key, resolution));
                self.contexts.len() - 1
            }
        };
        &self.contexts[index].1
    }

    /// The module item `func_id` of `base` lowers from: `Ok(None)` when nothing the item reaches
    /// carries a drop (lower from `base`, exactly as before this increment) or the lane is not
    /// active (the converter then refuses a reached `Inst::Drop` by name); `Ok(Some(resolved))`
    /// with every reached drop resolved to glue; `Err` naming the drop that did not resolve.
    pub(crate) fn resolve_for(
        &mut self,
        tcx: TyCtxt<'tcx>,
        base: &Module,
        func_id: FuncId,
        symbol: &str,
    ) -> Result<Option<Arc<Module>>, FrontendRefusal> {
        if !self.strict_gate || !reaches_drop(base, func_id) {
            return Ok(None);
        }
        let resolution = self.resolution(tcx, base);
        if let Some(why) = &resolution.module_refused {
            return Err(lane_refusal(RefusalClass::MalformedProducerModule, why.clone())
                .into_frontend(symbol));
        }
        // A function whose drops did not resolve is a declaration in the resolved module, so no
        // drop of it can be spliced; the item is refused here, naming it, only when it CALLS it
        // (the converter would refuse that call to a declaration anyway, without the reason).
        if let Some(refusal) = refused_callee(resolution, func_id) {
            return Err(refusal.into_frontend(symbol));
        }
        Ok(Some(resolution.module.clone()))
    }

    /// The module and function a drop-glue ITEM lowers from: its synthesized body in the
    /// resolution of the finalize-assembled module. `None` when the lane is not active (the item
    /// then takes its old route, and is refused there as a synthesized instance).
    pub(crate) fn glue_item(
        &mut self,
        tcx: TyCtxt<'tcx>,
        instance: ty::Instance<'tcx>,
        symbol: &str,
    ) -> Option<Result<(Arc<Module>, FuncId), FrontendRefusal>> {
        if !self.strict_gate || !is_glue_item(instance) {
            return None;
        }
        let base = match tcx
            .sess
            .with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
                |handoff| handoff.assembled_module(),
            ) {
            Ok(base) => base,
            Err(_) => {
                return Some(Err(FrontendRefusal::AssembledHandoffUnavailable {
                    symbol: symbol.to_string(),
                }));
            }
        };
        let resolution = self.resolution(tcx, &base);
        if let Some(why) = &resolution.module_refused {
            return Some(Err(lane_refusal(RefusalClass::MalformedProducerModule, why.clone())
                .into_frontend(symbol)));
        }
        Some(match resolution.glue.get(&instance) {
            Some(Ok(id)) => match refused_callee(resolution, *id) {
                // A destructor the glue calls whose own drops did not resolve.
                Some(refusal) => Err(refusal.into_frontend(symbol)),
                None => Ok((resolution.module.clone(), *id)),
            },
            Some(Err(refusal)) => Err(refusal.clone().into_frontend(symbol)),
            None => Err(lane_refusal(
                RefusalClass::MalformedProducerModule,
                "internal: the glue item was not planned by the lane",
            )
            .into_frontend(symbol)),
        })
    }
}

/// The refusal of the first function `root` reaches through direct calls (itself included)
/// whose drops did not resolve, naming it when it is not `root`.
fn refused_callee(resolution: &Resolution<'_>, root: FuncId) -> Option<LaneRefusal> {
    for id in call_closure(&resolution.module, root) {
        if let Some(refusal) = resolution.refused_functions.get(&id) {
            let mut refusal = refusal.clone();
            if id != root {
                let name = resolution
                    .module
                    .function_by_id(id)
                    .map_or_else(|| format!("FuncId({})", id.index()), |f| f.name.clone());
                refusal.detail = format!("it reaches `{name}`, whose {}", refusal.detail);
            }
            return Some(refusal);
        }
    }
    None
}

/// The rustc type a drop site drops, recovered from the body's own typeck results by the
/// `type_id_hash` the producer recorded. `None` when no type of the body hashes to it.
fn recover_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    cache: &mut FxHashMap<u32, FxHashMap<u128, RustcTy<'tcx>>>,
    def_index: u32,
    hash: u128,
) -> Option<RustcTy<'tcx>> {
    let types = cache.entry(def_index).or_insert_with(|| {
        let def = rustc_span::def_id::LocalDefId {
            local_def_index: rustc_span::def_id::DefIndex::from_u32(def_index),
        };
        let mut types = FxHashMap::default();
        if !tcx.has_typeck_results(def) {
            return types;
        }
        let results = tcx.typeck(def);
        for (_, t) in results.node_types().items_in_stable_order() {
            let t = *t;
            if t.has_infer()
                || t.has_escaping_bound_vars()
                || t.references_error()
                || t.has_non_region_param()
            {
                continue;
            }
            types.entry(tcx.type_id_hash(t).as_u128()).or_insert(t);
        }
        types
    });
    types.get(&hash).copied()
}

/// THE RESOLUTION of one base module. Deterministic: functions in module order, glue in the order
/// it is first asked for (children before parents).
fn resolve<'tcx>(
    tcx: TyCtxt<'tcx>,
    base: &Module,
    inventory: &[ty::Instance<'tcx>],
    inventory_set: &FxHashSet<ty::Instance<'tcx>>,
) -> Resolution<'tcx> {
    let env = ty::TypingEnv::fully_monomorphized();
    let mut module = base.clone();
    let handoff_ids: BTreeMap<FuncId, u32> = tcx
        .sess
        .with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
            |handoff| handoff.codegen_body_ids(),
        )
        .into_iter()
        .map(|(def_index, func_id)| (func_id, def_index))
        .collect();
    let mut refused_functions: BTreeMap<FuncId, LaneRefusal> = BTreeMap::new();
    let mut typeck_cache = FxHashMap::default();
    // Per function: each drop node's glue instance.
    let mut planned: Vec<(FuncId, Vec<(BlockId, usize, ty::Instance<'tcx>)>)> = Vec::new();
    // The module's own row for an array/slice element type, read off a dropped array's spelling.
    let mut element_rows: FxHashMap<RustcTy<'tcx>, TyId> = FxHashMap::default();

    for function in &base.functions {
        let nodes = drop_glue::drop_nodes(function);
        if nodes.is_empty() {
            continue;
        }
        let refuse = |detail: String| lane_refusal(RefusalClass::MalformedProducerModule, detail);
        let Some(&def_index) = handoff_ids.get(&function.id) else {
            refused_functions.insert(
                function.id,
                refuse("drops are in a function with no handoff identity".to_string()),
            );
            continue;
        };
        let sites = match trust_thir_lower::effect_conservation::drop_sites_for_codegen(
            tcx.sess, def_index,
        ) {
            Ok(sites) => sites,
            Err(why) => {
                refused_functions.insert(
                    function.id,
                    lane_refusal(
                        RefusalClass::EffectNotConserved,
                        format!("drops have no checked producer sites: {why}"),
                    ),
                );
                continue;
            }
        };
        let mut drops = Vec::with_capacity(nodes.len());
        let mut failure = None;
        for node in &nodes {
            let Some(site) = sites.iter().find(|s| s.ptr == node.ptr.index()) else {
                failure = Some(refuse(format!(
                    "drop through %{} at {:?}:{} has no producer drop site",
                    node.ptr.index(),
                    node.block,
                    node.index
                )));
                break;
            };
            let Some(t) = recover_type(tcx, &mut typeck_cache, def_index, site.ty) else {
                failure = Some(refuse(format!(
                    "no type of the body hashes to the dropped type of %{} ({:?})",
                    node.ptr.index(),
                    site.identity
                )));
                break;
            };
            let t = tcx.normalize_erasing_regions(env, ty::Unnormalized::new_wip(t));
            if !t.needs_drop(tcx, env) {
                failure = Some(refuse(format!("the producer drops `{t}`, which needs no drop")));
                break;
            }
            if let (Ty::Array(row, _), ty::Array(elem, _)) = (&node.ty, t.kind()) {
                element_rows.entry(*elem).or_insert(*row);
            }
            drops.push((node.block, node.index, ty::Instance::resolve_drop_glue(tcx, t)));
        }
        match failure {
            Some(refusal) => {
                refused_functions.insert(function.id, refusal);
            }
            None => planned.push((function.id, drops)),
        }
    }

    // The glue: every type a planned drop names, then every glue item of the inventory.
    let mut builder = GlueBuilder {
        tcx,
        base,
        inventory_set,
        element_rows,
        slots: FxHashMap::default(),
        in_progress: FxHashSet::default(),
        spliced: 0,
    };
    for (_, drops) in &planned {
        for (_, _, glue) in drops {
            let _ = builder.slot(&mut module, *glue);
        }
    }
    for glue in inventory {
        let _ = builder.slot(&mut module, *glue);
    }

    // The rewrite, all or nothing per function.
    let mut rewritten: Vec<(FuncId, BlockId, usize, ty::Instance<'tcx>)> = Vec::new();
    for (func_id, drops) in &planned {
        let slot_of = |glue: &ty::Instance<'tcx>| builder.slots.get(glue).cloned();
        let mut failure = None;
        for (_, _, glue) in drops {
            match slot_of(glue) {
                Some(Ok(_)) => {}
                Some(Err(refusal)) => {
                    failure = Some(LaneRefusal {
                        class: refusal.class,
                        detail: format!(
                            "drop of `{}` does not resolve: {}",
                            drop_glue::glue_instance_ty(*glue)
                                .map_or_else(String::new, |t| t.to_string()),
                            refusal.detail
                        ),
                    });
                    break;
                }
                None => {
                    failure = Some(lane_refusal(
                        RefusalClass::MalformedProducerModule,
                        "internal: a drop's glue was never planned",
                    ));
                    break;
                }
            }
        }
        if let Some(refusal) = failure {
            refused_functions.insert(*func_id, refusal);
            continue;
        }
        let Some(function) = module.function_by_id_mut(*func_id) else {
            refused_functions.insert(
                *func_id,
                lane_refusal(
                    RefusalClass::MalformedProducerModule,
                    "internal: the function vanished",
                ),
            );
            continue;
        };
        let by_site: BTreeMap<(BlockId, usize), ty::Instance<'tcx>> =
            drops.iter().map(|(b, i, g)| ((*b, *i), *g)).collect();
        let outcome = drop_glue::rewrite_drops(function, |node| {
            let glue = by_site
                .get(&(node.block, node.index))
                .ok_or_else(|| "internal: a drop the plan does not list".to_string())?;
            match builder.slots.get(glue) {
                Some(Ok(id)) => Ok(*id),
                _ => Err("internal: an unresolved glue".to_string()),
            }
        });
        match outcome {
            Ok(_) => rewritten.extend(drops.iter().map(|(b, i, g)| (*func_id, *b, *i, *g))),
            Err(why) => {
                refused_functions
                    .insert(*func_id, lane_refusal(RefusalClass::MalformedProducerModule, why));
            }
        }
    }

    // A function whose drops did not resolve keeps no body in the resolved module: it can never
    // be lowered, or inlined, with a drop left in it.
    for id in refused_functions.keys() {
        if let Some(function) = module.function_by_id_mut(*id) {
            // A bodyless declaration: nothing that names the body's values survives.
            function.blocks.clear();
            function.value_names = None;
            function.scopes = None;
            function.body_gate = None;
        }
    }

    // THE POSTCONDITION.
    let mut module_refused = None;
    if let Some((f, b, i)) = drop_glue::first_surviving_drop(&module) {
        module_refused = Some(format!(
            "the drop resolution's postcondition failed: an `Inst::Drop` survives in FuncId({}) at \
             {b:?}:{i}",
            f.index()
        ));
    }
    if module_refused.is_none() {
        for (func_id, block, index, glue) in &rewritten {
            let expected = drop_glue::glue_symbol(tcx, *glue);
            let callee = module
                .function_by_id(*func_id)
                .and_then(|f| f.blocks.iter().find(|b| b.id == *block))
                .and_then(|b| b.body.get(*index))
                .and_then(|n| match &n.inst {
                    Inst::Call { callee, .. } => Some(*callee),
                    _ => None,
                })
                .and_then(|c| module.function_by_id(c));
            let named = callee.is_some_and(|f| {
                f.name == expected
                    && f.body_gate
                        == Some(BodyGate::Gated {
                            authority: drop_glue::TRUST_DROP_GLUE_AUTHORITY.to_string(),
                            evidence: None,
                        })
            });
            if !named {
                module_refused = Some(format!(
                    "the drop resolution's postcondition failed: the drop at FuncId({}) \
                     {block:?}:{index} does not call the glue `{expected}`",
                    func_id.index()
                ));
                break;
            }
        }
    }
    if module_refused.is_none() {
        if let Err(why) = tables_unchanged(base, &module) {
            module_refused = Some(why);
        }
    }
    if module_refused.is_none() && (builder.spliced > 0 || !rewritten.is_empty()) {
        let errors =
            trust_thir_lower::instance_admission::assembled_codegen_validation_errors(&module);
        if !errors.is_empty() {
            module_refused = Some(format!(
                "the drop-resolved codegen module fails the finalize validator ({} error(s)): \
                 {}",
                errors.len(),
                errors.iter().take(3).cloned().collect::<Vec<_>>().join("; ")
            ));
        }
    }
    Resolution { module: Arc::new(module), refused_functions, glue: builder.slots, module_refused }
}

/// The glue half of [`resolve`]: one slot per glue instance, synthesized on first ask.
struct GlueBuilder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    base: &'a Module,
    inventory_set: &'a FxHashSet<ty::Instance<'tcx>>,
    element_rows: FxHashMap<RustcTy<'tcx>, TyId>,
    slots: FxHashMap<ty::Instance<'tcx>, Result<FuncId, LaneRefusal>>,
    in_progress: FxHashSet<ty::Instance<'tcx>>,
    /// How many glue bodies were appended.
    spliced: usize,
}

impl<'a, 'tcx> GlueBuilder<'a, 'tcx> {
    fn slot(
        &mut self,
        module: &mut Module,
        glue: ty::Instance<'tcx>,
    ) -> Result<FuncId, LaneRefusal> {
        if let Some(slot) = self.slots.get(&glue) {
            return slot.clone();
        }
        if !self.in_progress.insert(glue) {
            return Err(lane_refusal(RefusalClass::SynthesizedInstance, "a drop-glue cycle"));
        }
        let result = self.synthesize(module, glue);
        self.in_progress.remove(&glue);
        self.slots.insert(glue, result.clone());
        result
    }

    fn synthesize(
        &mut self,
        module: &mut Module,
        glue: ty::Instance<'tcx>,
    ) -> Result<FuncId, LaneRefusal> {
        let tcx = self.tcx;
        let symbol = drop_glue::glue_symbol(tcx, glue);
        let Some(dropped) = drop_glue::glue_instance_ty(glue) else {
            return Err(lane_refusal(
                RefusalClass::SynthesizedInstance,
                format!("`{symbol}` is not the drop glue of a type ({:?})", glue.def),
            ));
        };
        // WORK-LIST AGREEMENT (design §4.2): a glue body is spliced only for a glue the collector
        // lists as a LOCAL item. One an upstream crate exports (share-generics) links to that
        // crate's symbol and is never re-emitted.
        if !self.inventory_set.contains(&glue) {
            if let Some(krate) = glue.upstream_monomorphization(tcx) {
                return Err(lane_refusal(
                    RefusalClass::UpstreamBody,
                    format!(
                        "the glue of `{dropped}` is exported by crate `{}` (share-generics); \
                         linking to it needs real calls (increment 5)",
                        tcx.crate_name(krate)
                    ),
                ));
            }
            return Err(lane_refusal(
                RefusalClass::SynthesizedInstance,
                format!("the collector does not list the glue of `{dropped}` as a local item"),
            ));
        }
        let plan = drop_glue::glue_plan(tcx, dropped)
            .map_err(|r| lane_refusal(class_of(r.class), r.detail))?;
        // The destructor: a monomorphic local `Drop` impl's ADMITTED handoff body.
        let dtor = match plan.destructor() {
            None => None,
            Some(d) => {
                let selected = tcx
                    .sess
                    .with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
                        |handoff| handoff.exact_instance_body(tcx, *d),
                    )
                    .map_err(|error| {
                        lane_refusal(
                            RefusalClass::ProducerDeclined,
                            format!(
                                "its destructor `{}` has no admitted handoff body ({error:?})",
                                tcx.def_path_str(d.def_id())
                            ),
                        )
                    })?;
                let present =
                    module.function_by_id(selected.func_id).is_some_and(|f| !f.blocks.is_empty())
                        && self.base.function_by_id(selected.func_id).is_some();
                if !present {
                    return Err(lane_refusal(
                        RefusalClass::ProducerDeclined,
                        format!(
                            "its destructor `{}` is not a body of this codegen module",
                            tcx.def_path_str(d.def_id())
                        ),
                    ));
                }
                // The glue passes the destructor its own pointer: `(ptr) -> ()` exactly.
                let signature = module
                    .function_by_id(selected.func_id)
                    .and_then(|f| module.func_types.get(f.ty.as_usize()));
                let takes_one_pointer = signature.is_some_and(|sig| {
                    sig.params == [Ty::Ptr] && sig.returns.is_empty() && !sig.is_vararg
                });
                if !takes_one_pointer {
                    return Err(lane_refusal(
                        RefusalClass::SynthesizedInstance,
                        format!(
                            "its destructor `{}` is not signed `(ptr) -> ()` in this codegen \
                             module ({signature:?})",
                            tcx.def_path_str(d.def_id())
                        ),
                    ));
                }
                Some((*d, selected.func_id))
            }
        };
        let mut children: FxHashMap<ty::Instance<'tcx>, FuncId> = FxHashMap::default();
        for child in plan.child_glue() {
            let id = self.slot(module, *child).map_err(|refusal| LaneRefusal {
                class: refusal.class,
                detail: format!(
                    "its field's glue `{}` is refused: {}",
                    drop_glue::glue_instance_ty(*child).map_or_else(String::new, |t| t.to_string()),
                    refusal.detail
                ),
            })?;
            children.insert(*child, id);
        }
        let fat = if plan.takes_fat_pointer() || plan.passes_fat_pointer() {
            let elem = match dropped.kind() {
                ty::Array(elem, _) | ty::Slice(elem) => *elem,
                _ => {
                    return Err(lane_refusal(
                        RefusalClass::SynthesizedInstance,
                        format!("`{dropped}` is not an array or slice"),
                    ));
                }
            };
            let Some(row) = self.element_rows.get(&elem) else {
                return Err(lane_refusal(
                    RefusalClass::SynthesizedInstance,
                    format!(
                        "the glue of `{dropped}` passes a `*mut [{elem}]`, and no row of the \
                         module's type table spells `{elem}` (the crate module's table remap is \
                         not available at the codegen seam)"
                    ),
                ));
            };
            Some(Ty::FatPtr(FatPtrKind::Slice(*row)))
        } else {
            None
        };
        let shape: GlueShape<FuncId> = plan
            .try_map(|callee| match dtor {
                Some((d, id)) if d == *callee => Ok(id),
                _ => children.get(callee).copied().ok_or(()),
            })
            .map_err(|()| {
                lane_refusal(
                    RefusalClass::MalformedProducerModule,
                    "internal: an unmapped glue callee",
                )
            })?;
        if module.functions.iter().any(|f| f.name == symbol) {
            return Err(lane_refusal(
                RefusalClass::MalformedProducerModule,
                format!("the codegen module already holds a function named `{symbol}`"),
            ));
        }
        if module.functions.iter().enumerate().any(|(i, f)| f.id.as_usize() != i) {
            return Err(lane_refusal(
                RefusalClass::MalformedProducerModule,
                "the codegen module's function ids are not dense",
            ));
        }
        let id = FuncId::new(u32::try_from(module.functions.len()).map_err(|_| {
            lane_refusal(RefusalClass::MalformedProducerModule, "the function table exceeds u32")
        })?);
        let signature = drop_glue::glue_signature(&shape, fat.as_ref())
            .map_err(|why| lane_refusal(RefusalClass::SynthesizedInstance, why))?;
        let func_ty = module.intern_func_type(signature).map_err(|refusal| {
            lane_refusal(RefusalClass::MalformedProducerModule, refusal.to_string())
        })?;
        let function = drop_glue::synthesize_glue(id, &symbol, func_ty, &shape, fat.as_ref())
            .map_err(|why| lane_refusal(RefusalClass::SynthesizedInstance, why))?;
        module.try_add_function(function).map_err(|refusal| {
            lane_refusal(RefusalClass::MalformedProducerModule, refusal.to_string())
        })?;
        self.spliced += 1;
        Ok(id)
    }
}

/// The glue bodies that `module` (an item's lowering context) reaches from `root`, for the
/// coverage disclosure: functions carrying this lane's body gate. PURE.
pub(crate) fn reached_glue(module: &Module, root: FuncId) -> BTreeSet<FuncId> {
    reached_functions(module, root)
        .into_iter()
        .filter(|id| {
            module.function_by_id(*id).is_some_and(|f| {
                f.body_gate
                    == Some(BodyGate::Gated {
                        authority: drop_glue::TRUST_DROP_GLUE_AUTHORITY.to_string(),
                        evidence: None,
                    })
            })
        })
        .collect()
}

#[cfg(test)]
mod tests;
