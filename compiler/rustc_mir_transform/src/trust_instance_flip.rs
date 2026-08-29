//! Trust: the WALL-A INSTANCE FLIP — the consumer half, at the `codegen_mir` seam.
//!
//! # Why this seam, and not `optimized_mir`
//!
//! The ordinary flip ([`crate::trust_ir_flip`]) installs at `inner_optimized_mir`, keyed by
//! `LocalDefId`. That seam compiles ONE body per definition, PRE-monomorphisation, so a GENERIC
//! body has no concrete ABI there and `to_mir::rederive_abi_sig` refuses it — loudly, once per
//! compile, for the whole wall-A population. `codegen_mir` is the first place rustc holds a
//! concrete `(DefId, GenericArgs)` pair together with MIR demand, and it is a seam rustc itself
//! already swaps a whole instantiated `Body` at (the `ergonomic_clones` branch, which builds
//! `instantiate_mir_and_normalize_erasing_regions(...)` and `tcx.arena.alloc`s it as the codegen
//! root). This module derives the trust-ir body at that pair and hands it back through a query,
//! because `rustc_codegen_ssa` cannot link `rustc_mir_transform` directly.
//!
//! # What is added to the trusted chain, and what is done about it
//!
//! Exactly one thing: INSTANTIATION. The `agreed` verdict was minted against the generic built
//! sibling, so this lane re-mints it per instance —
//! `trust_thir_lower::instance_flip::derive_instance_flip_body` runs the FROZEN comparator over
//! (rustc's own instantiation of its own retained built body) vs (the recorded Module lowered at
//! independently re-derived concrete anchors) and admits only `DerivedAgreed`.
//!
//! # Two hazards this seam has that the `optimized_mir` seam does not
//!
//! Installing AFTER monomorphic item collection and AFTER the ABI's parameter deductions means
//! two facts about the body were already published from the INCUMBENT:
//!
//! * **Collected items.** `collect_and_partition_mono_items` walked the generic `optimized_mir`.
//!   A derived body that referenced an item the collector never scheduled would reach the linker
//!   as an undefined symbol. [`item_refs_contained`] refuses any derived body whose
//!   item-producing constructs are not a SUBSET of the incumbent instantiated body's.
//! * **Deduced parameter attributes.** `fn_abi_of_instance` reads `deduced_param_attrs(def_id)`,
//!   computed from the generic `optimized_mir`; codegen then tells LLVM the argument is
//!   `readonly`/`captures(none)`. A derived body that used a parameter more strongly would make
//!   that claim a lie. [`param_attrs_agree`] re-runs the SAME deduction on the derived body and
//!   requires equality.
//!
//! Neither hazard is hypothetical-only and neither is named in the design; both are gated here,
//! fail-closed, and both refusals are logged with a distinguishable `stage`.
//!
//! Observability: `info!` per flipped INSTANCE on this module's own target
//! (`rustc_mir_transform::trust_instance_flip`), message `"trust-ir-instance-flip: INSTANCE
//! INSTALLED"`, carrying the per-BODY `lineage` digest — unchanged by instantiation, so it still
//! joins to the registry object and the published coverage row — plus the NEW `args_digest` axis
//! that tells two events of one body apart. `warn!` per refusal, same target, message
//! `"trust-ir-instance-flip: INSTANCE FALLBACK"`.
//!
//! The message strings deliberately do NOT contain the `DefId`-seam event's
//! `"compiled from trust-ir"` phrase: every instrument that counts body flips by grepping that
//! phrase must keep counting BODIES, and instance events must not silently inflate it.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: Apache-2.0

use std::collections::BTreeSet;
use std::panic::AssertUnwindSafe;

use rustc_hir::def_id::DefId;
use rustc_middle::mir::interpret::{AllocId, GlobalAlloc, Scalar};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{
    self, Body, CastKind, ConstValue, Location, MirPhase, RuntimePhase, Rvalue, TerminatorKind,
};
use rustc_middle::ty::{self, GenericArgsRef, TyCtxt, TypeVisitableExt};
use rustc_session::Session;
use tracing::{info, warn};

use crate::pass_manager::MirPass;
use crate::{deduce_param_attrs, mentioned_items, trust_ir_flip};

/// Per-Session instance-flip tallies, for the event log. Kept apart from the `DefId`-seam
/// telemetry so `flipped_so_far` on an ordinary flip event keeps meaning what it always meant.
#[derive(Default)]
struct SessionInstanceFlipTelemetry {
    flipped: usize,
    refused: usize,
}

fn note_flipped(sess: &Session) -> usize {
    sess.with_trust_compiler_state::<SessionInstanceFlipTelemetry, _>(|t| {
        t.flipped = t.flipped.saturating_add(1);
        t.flipped
    })
}

fn note_refused(sess: &Session) -> usize {
    sess.with_trust_compiler_state::<SessionInstanceFlipTelemetry, _>(|t| {
        t.refused = t.refused.saturating_add(1);
        t.refused
    })
}

/// The query provider. `Some(body)` is a `Runtime(Optimized)` body derived from the trust-ir
/// Module at THIS instance's args, ready to be the codegen root; `None` means "use rustc's own
/// body" — silently for non-candidates, loudly for refusals.
pub(crate) fn trust_instance_flip_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    key: (DefId, GenericArgsRef<'tcx>),
) -> Option<&'tcx Body<'tcx>> {
    let (def_id, args) = key;
    // Cheap exits first: they run for every codegen'd instance in the crate.
    if !trust_thir_lower::instance_flip::instance_flip_session_enabled(tcx) {
        return None;
    }
    let def = def_id.as_local()?;
    if args.has_infer() || args.has_non_region_param() {
        return None;
    }
    let inst = ty::Instance::new_raw(def_id, args);

    // Defense in depth: the derivation re-runs the FROZEN comparator at a seam it has never run
    // at before (post-codegen-start rather than at the `mir_built` hook). A panic here must lose
    // a flip, not a compile. Same stance as `trust_ir_flip::try_flip`'s pipeline `catch_unwind`.
    let attempt = match std::panic::catch_unwind(AssertUnwindSafe(|| {
        trust_thir_lower::instance_flip::derive_instance_flip_body(tcx, def, inst)
    })) {
        Ok(a) => a,
        Err(_panic) => {
            let refused = note_refused(tcx.sess);
            trust_thir_lower::instance_flip::note_instance_outcome(tcx, def, false);
            warn!(
                ?def,
                reason = "per-instance derivation PANICKED (caught); no derived code emitted",
                stage = "derive-panic",
                refused,
                "trust-ir-instance-flip: INSTANCE FALLBACK"
            );
            return None;
        }
    };
    let (body, asserts, lineage, args_digest, markers_exact, def_path) = match attempt {
        trust_thir_lower::instance_flip::InstanceFlipAttempt::NotCandidate => return None,
        trust_thir_lower::instance_flip::InstanceFlipAttempt::Rejected { reason } => {
            let refused = note_refused(tcx.sess);
            trust_thir_lower::instance_flip::note_instance_outcome(tcx, def, false);
            warn!(
                ?def,
                reason,
                stage = "gate",
                refused,
                "trust-ir-instance-flip: INSTANCE FALLBACK"
            );
            return None;
        }
        trust_thir_lower::instance_flip::InstanceFlipAttempt::Derived {
            body,
            asserts,
            lineage,
            args_digest,
            markers_exact,
            def_path,
        } => (body, asserts, lineage, args_digest, markers_exact, def_path),
    };

    // The incumbent, exactly as codegen would have consumed it: rustc's own instantiation of its
    // own optimized body. It is the reference for BOTH post-pipeline gates below.
    let incumbent = match inst.try_instantiate_mir_and_normalize_erasing_regions(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(tcx, tcx.optimized_mir(def_id).clone()),
    ) {
        Ok(b) => b,
        Err(e) => {
            let refused = note_refused(tcx.sess);
            trust_thir_lower::instance_flip::note_instance_outcome(tcx, def, false);
            warn!(
                ?def,
                reason = format!("incumbent optimized_mir would not instantiate: {e:?}"),
                stage = "incumbent",
                refused,
                "trust-ir-instance-flip: INSTANCE FALLBACK"
            );
            return None;
        }
    };

    // Replay the pipeline the incumbent went through, then the two seam-specific gates.
    // `catch_unwind` is defense in depth only, exactly as on the `DefId` seam: the structural
    // gate is what makes the pipeline total over the admitted fragment.
    let advanced = std::panic::catch_unwind(AssertUnwindSafe(move || {
        let mut body = body;
        trust_ir_flip::advance_built_to_runtime(tcx, &mut body)?;
        // Parity with `inner_optimized_mir`: record mentioned items before optimizing. The
        // collector has already run, so this is not a collection input any more — it is the
        // ledger `item_refs_contained` compares.
        mentioned_items::MentionedItems.run_pass(tcx, &mut body);
        crate::run_optimization_passes(tcx, &mut body);
        if body.phase != MirPhase::Runtime(RuntimePhase::Optimized) {
            return Err(format!("derived instance body ended at {:?}", body.phase));
        }
        Ok(body)
    }));
    let body = match advanced {
        Ok(Ok(body)) => body,
        Ok(Err(reason)) => {
            let refused = note_refused(tcx.sess);
            trust_thir_lower::instance_flip::note_instance_outcome(tcx, def, false);
            warn!(
                ?def,
                reason,
                stage = "pipeline",
                refused,
                "trust-ir-instance-flip: INSTANCE FALLBACK"
            );
            return None;
        }
        Err(_panic) => {
            let refused = note_refused(tcx.sess);
            trust_thir_lower::instance_flip::note_instance_outcome(tcx, def, false);
            warn!(
                ?def,
                reason = "derived instance body pass PANICKED (caught); no derived code emitted",
                stage = "pipeline-panic",
                refused,
                "trust-ir-instance-flip: INSTANCE FALLBACK"
            );
            return None;
        }
    };

    if let Err(reason) = item_refs_contained(tcx, &body, &incumbent) {
        let refused = note_refused(tcx.sess);
        trust_thir_lower::instance_flip::note_instance_outcome(tcx, def, false);
        warn!(
            ?def,
            reason,
            stage = "collected-items",
            refused,
            "trust-ir-instance-flip: INSTANCE FALLBACK"
        );
        return None;
    }
    if let Err(reason) = param_attrs_agree(tcx, def_id, &body) {
        let refused = note_refused(tcx.sess);
        trust_thir_lower::instance_flip::note_instance_outcome(tcx, def, false);
        warn!(
            ?def,
            reason,
            stage = "deduced-param-attrs",
            refused,
            "trust-ir-instance-flip: INSTANCE FALLBACK"
        );
        return None;
    }

    let flipped = note_flipped(tcx.sess);
    trust_thir_lower::instance_flip::note_instance_outcome(tcx, def, true);
    info!(
        ?def,
        def_path = %def_path,
        asserts,
        markers_exact,
        lineage = %lineage,
        args_digest = %args_digest,
        args = ?args,
        instances_flipped_so_far = flipped,
        "trust-ir-instance-flip: INSTANCE INSTALLED"
    );
    Some(tcx.arena.alloc(body))
}

/// Every construct in a body from which monomorphic item collection can schedule work, rendered
/// as a canonical string. Both sides are fully monomorphic here, so the spellings are directly
/// comparable.
struct ItemRefs<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    out: BTreeSet<String>,
    /// Cycle guard for the allocation walk; an allocation may point at itself transitively.
    seen: rustc_data_structures::fx::FxHashSet<AllocId>,
}

impl<'a, 'tcx> Visitor<'tcx> for ItemRefs<'a, 'tcx> {
    fn visit_const_operand(
        &mut self,
        constant: &rustc_middle::mir::ConstOperand<'tcx>,
        _location: Location,
    ) {
        let ty = constant.const_.ty();
        if let ty::FnDef(did, args) = ty.kind() {
            self.out.insert(format!("fn:{did:?}:{args:?}"));
        }
        match constant.const_ {
            // An unevaluated constant NAMES an item outright.
            mir::Const::Unevaluated(uv, _) => {
                self.out.insert(format!("unevaluated:{:?}:{:?}", uv.def, uv.args));
            }
            // A value constant names items only through its POINTER PROVENANCE, and that is
            // what this walks -- a mirror of `rustc_monomorphize::collector::collect_const_value`
            // / `collect_alloc`, rendering the item the collector would have SCHEDULED instead
            // of scheduling it.
            //
            // MEASURED REASON THIS IS NOT THE CONSTANT'S OWN SPELLING (which is what the first
            // version of this gate compared): at `-O3` the derived body and the incumbent both
            // const-fold `LimitedSeqAccess::size_hint`'s `Option<usize>` return, INDEPENDENTLY,
            // so the two allocations hold identical bytes under DIFFERENT `AllocId`s. Comparing
            // spellings refused all 6 instances of that body for a difference that names no item
            // at all. Provenance is the property the hazard is actually about: an anonymous
            // byte allocation with no pointers in it schedules nothing, however it is spelled.
            mir::Const::Val(value, _) => self.collect_const_value(value),
            mir::Const::Ty(_, c) => {
                self.out.insert(format!("tyconst:{c:?}"));
            }
        }
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        match rvalue {
            Rvalue::Cast(CastKind::PointerCoercion(coercion, _), operand, target) => {
                let src = operand.ty(&self.body.local_decls, self.tcx);
                self.out.insert(format!("coerce:{coercion:?}:{src:?}->{target:?}"));
            }
            Rvalue::ThreadLocalRef(did) => {
                self.out.insert(format!("tls:{did:?}"));
            }
            _ => {}
        }
        self.super_rvalue(rvalue, location);
    }

    fn visit_terminator(
        &mut self,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        if let TerminatorKind::Drop { place, .. } = &terminator.kind {
            let ty = place.ty(&self.body.local_decls, self.tcx).ty;
            self.out.insert(format!("drop:{ty:?}"));
        }
        self.super_terminator(terminator, location);
    }
}

impl<'tcx> ItemRefs<'_, 'tcx> {
    /// The collector's own `collect_const_value`, rendering instead of scheduling.
    fn collect_const_value(&mut self, value: ConstValue) {
        match value {
            ConstValue::Scalar(Scalar::Ptr(ptr, _size)) => {
                self.collect_alloc(ptr.provenance.alloc_id())
            }
            ConstValue::Indirect { alloc_id, .. } | ConstValue::Slice { alloc_id, meta: _ } => {
                self.collect_alloc(alloc_id)
            }
            _ => {}
        }
    }

    /// The collector's own `collect_alloc`, rendering instead of scheduling. The `seen` set is
    /// the same cycle guard the collector's `ensure_sufficient_stack` recursion needs.
    fn collect_alloc(&mut self, alloc_id: AllocId) {
        if !self.seen.insert(alloc_id) {
            return;
        }
        match self.tcx.global_alloc(alloc_id) {
            GlobalAlloc::Static(def_id) => {
                self.out.insert(format!("static:{def_id:?}"));
            }
            GlobalAlloc::Memory(alloc) => {
                for &prov in alloc.inner().provenance().ptrs().values() {
                    self.collect_alloc(prov.alloc_id());
                }
            }
            GlobalAlloc::Function { instance, .. } => {
                self.out.insert(format!("fnalloc:{instance:?}"));
            }
            GlobalAlloc::VTable(ty, dyn_ty) => {
                self.out.insert(format!("vtable:{ty:?}:{dyn_ty:?}"));
            }
            GlobalAlloc::TypeId { .. } => {}
        }
    }
}

fn item_refs<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> BTreeSet<String> {
    let mut v = ItemRefs { tcx, body, out: BTreeSet::new(), seen: Default::default() };
    v.visit_body(body);
    for mi in body.mentioned_items.iter().flatten() {
        v.out.insert(format!("mentioned:{:?}", mi.node));
    }
    v.out
}

/// Trust (wall A, seam hazard 1): the derived body must not reference anything the incumbent does
/// not. Mono item collection already ran, from the incumbent; an item this body names and that
/// body does not was never scheduled for codegen.
fn item_refs_contained<'tcx>(
    tcx: TyCtxt<'tcx>,
    derived: &Body<'tcx>,
    incumbent: &Body<'tcx>,
) -> Result<(), String> {
    let d = item_refs(tcx, derived);
    let i = item_refs(tcx, incumbent);
    let extra: Vec<&String> = d.difference(&i).collect();
    if extra.is_empty() {
        return Ok(());
    }
    Err(format!(
        "derived instance body references {} item(s) the collector never saw: {}",
        extra.len(),
        extra.iter().take(4).map(|s| s.as_str()).collect::<Vec<_>>().join(", ")
    ))
}

/// Trust (wall A, seam hazard 2): `fn_abi_of_instance` has already published parameter
/// deductions computed from the INCUMBENT. Re-run the very same deduction on the derived body
/// and require agreement, so codegen's `readonly`/`captures(none)` claims stay true of the code
/// actually emitted.
///
/// Vacuous at `-Copt-level=0`, where `deduced_param_attrs` returns `&[]` by its own first line —
/// which is honest, not a hole: at `-O0` no such claim is published either.
fn param_attrs_agree<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    derived: &Body<'tcx>,
) -> Result<(), String> {
    let published = tcx.deduced_param_attrs(def_id);
    if published.is_empty() {
        return Ok(());
    }
    let ours = deduce_param_attrs::deduce_for_body(derived);
    for (i, want) in published.iter().enumerate() {
        let got = ours.get(i).copied();
        match got {
            Some(got) if got == *want => {}
            Some(got) => {
                return Err(format!(
                    "param {i}: incumbent published {want:?} but the derived body deduces {got:?}"
                ));
            }
            None => {
                return Err(format!(
                    "param {i}: incumbent published {want:?} but the derived body has no such \
                     parameter"
                ));
            }
        }
    }
    Ok(())
}

/// Trust: emit the end-of-session instance census (the population fact, measured by the
/// production seam itself). Called from the same post-codegen seam the probe's channel B uses.
pub fn emit_census(tcx: TyCtxt<'_>) {
    if !trust_thir_lower::instance_flip::instance_flip_session_enabled(tcx) {
        return;
    }
    // Trust: the census is MEASUREMENT output, and `-Ztrust-instance-flip` defaults
    // to ON — so emitting unconditionally printed these lines from every ordinary
    // compilation, which put them in the pinned stderr of 45 unrelated ui fixtures
    // (measured 2026-08-24; zero fixtures opt into the flag). Blessing those
    // baselines would have chained 45 tests to instance COUNTS, so that every later
    // codegen change re-breaks all of them for reasons none of them are about.
    // The census is therefore emitted only when a measurement harness asks for it,
    // by the same `-Ztrust-instance-flip-probe` channel this seam already serves;
    // the population fact is unchanged when requested, and silent otherwise.
    if tcx.sess.opts.unstable_opts.trust_instance_flip_probe.is_none() {
        return;
    }
    for line in trust_thir_lower::instance_flip::census(tcx) {
        // Deliberately `eprintln!`, like the probe's own lines: the census is a population fact
        // a measurement harness must be able to read without a tracing filter.
        eprintln!("{line}");
    }
    let (flipped, refused) = tcx
        .sess
        .with_trust_compiler_state::<SessionInstanceFlipTelemetry, _>(|t| (t.flipped, t.refused));
    eprintln!(
        "TRUST-INSTANCE-FLIP summary instances_installed={flipped} instances_refused={refused}"
    );
}
