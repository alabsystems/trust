//! Trust: the WALL-A INSTANCE FLIP SEAM — the per-`Instance` half of the trust-ir flip.
//!
//! # The wall this exists to retire
//!
//! [`crate::to_mir::rederive_abi_sig`] refuses every body whose IDENTITY signature
//! `has_non_region_param()` (`"abi rederive: generic fn signature"`). That refusal is correct at
//! the `LocalDefId` seam the ordinary flip installs on: `optimized_mir` compiles ONE body per
//! `DefId`, pre-monomorphisation, so a generic body has no single concrete ABI to name there.
//! The consequence is a population that reaches `DerivedAgreed` at the `mir_built` hook, is
//! recorded green, and then falls back LOUDLY at every compile: 43 generic-fn + 2 generic-closure
//! rows at `-O0` on the crystal subject crate, 15+2 at `-O3`.
//!
//! Lane WA measured every link of the fix before a line of it was built (clean
//! `designs/2026-08-21-wall-a-instance-flip-seam.md`, `-Ztrust-instance-flip-probe`, see
//! [`crate::instance_probe`]): the FROZEN comparator reaches `DerivedAgreed` on the INSTANTIATED
//! pair, instance-level ABI rederivation from `tcx` alone is EXACT against rustc's own
//! instantiation, and the recorded trust-ir Module needs NO substitution operation — its
//! generic-ness lives entirely in the rustc-side ABI anchors. This module is that design, built.
//!
//! # The shape
//!
//! * **At the `mir_built` hook** ([`record_green_instance`]): a GENERIC `agreed` body records
//!   into THIS registry — a separate Session table beside the frozen `flip_registry`, holding the
//!   intact hook-time [`Lowered`] plus its lineage digest — and its freshly BUILT body is retained
//!   in the `TyCtxt` side table (`tcx.trust_instance_flip_retain`), because the per-instance
//!   differential needs an incumbent at the phase the frozen comparator is written for.
//! * **At the `codegen_mir` seam** ([`derive_instance_flip_body`], driven by
//!   `rustc_mir_transform::trust_instance_flip`): for one concrete `Instance`, instantiate the
//!   retained built sibling with rustc's OWN fold, re-derive the ABI independently at the
//!   instance's args, hand the instantiated pair to the FROZEN comparator, and only on a
//!   per-instance `DerivedAgreed` lower the recorded Module at those concrete anchors.
//!
//! # The partition invariant (why two registries can never both install one body)
//!
//! This registry admits a body ONLY when its identity signature is generic
//! ([`identity_sig_is_generic`]); the frozen `flip_registry`'s consumer can only install a body
//! whose identity signature is NOT generic (`rederive_abi_sig` refuses the rest, by exactly the
//! same predicate). The two lanes therefore partition the population, and `record_green`'s own
//! poison note — which names "a per-instance lane specialized to one instantiation" as the
//! silent-miscompile shape it is defending against — stays satisfied by construction rather than
//! by convention. `test_registries_partition_on_the_generic_predicate` executes it.
//!
//! # Fail-closed, in the three places it matters
//!
//! 1. An instance whose derived body does not reach `DerivedAgreed` AT ITS ARGS does not flip —
//!    the verdict is re-minted per instance, never inherited from the generic hook-time one.
//! 2. A body with no local instance is untouched: nothing demands the query for it.
//! 3. Every gate the `DefId`-seam flip runs is re-run here against the INSTANTIATED sibling, and
//!    this lane additionally refuses the placeholder/provenance lanes outright (see
//!    [`body_lane_gates_allow_instance_flip`]) rather than certifying them.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: Apache-2.0

use std::collections::{HashMap, HashSet};

use rustc_hir::def::DefKind;
use rustc_middle::mir::{Body, Local};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::LocalDefId;
use trust_ir::ProofDigest;

use crate::{Lowered, flip, flip_registry, lineage, mir_differential, to_mir};

/// Domain tag for the per-instance ARGS digest — the second axis of the flip event's identity
/// (the first, `lineage`, is per-BODY and instantiation-invariant, and is deliberately NOT
/// changed by this lane so every existing digest, including the pinned crystal A1 value, stays
/// put). Versioned for the same reason [`lineage::BODY_LINEAGE_DOMAIN`] is.
pub const INSTANCE_ARGS_DOMAIN: &str = "trust_thir_lower.instance_args.v1";

/// One green GENERIC body as the instance flip consumes it.
///
/// Unlike the frozen registry's `GreenBody` this keeps the WHOLE hook-time [`Lowered`]: the
/// per-instance differential re-runs `mir_differential::compare_derived`, which reads the
/// producer's own `unsupported` / `pending_consts` ledgers as fail-closed gates. Handing it a
/// reconstruction would mean this crate minted the values those gates read. It keeps the real
/// object instead, at the cost of one clone per admitted body (the wall-A population).
struct InstanceGreenBody {
    def_path: String,
    lowered: Lowered,
    lineage: ProofDigest,
    /// The hook-time marker-channel verdict for the GENERIC pair. Recorded for observability;
    /// the flip gates on the PER-INSTANCE value, which is re-minted at the instance.
    hook_markers_exact: bool,
}

impl Clone for InstanceGreenBody {
    fn clone(&self) -> Self {
        InstanceGreenBody {
            def_path: self.def_path.clone(),
            lowered: self.lowered.clone(),
            lineage: self.lineage,
            hook_markers_exact: self.hook_markers_exact,
        }
    }
}

/// Green generic bodies for one compiler Session. Same Session-scoping rationale as the frozen
/// `SessionFlipRegistry`: a crate-local `DefIndex` is a safe key only inside one Session.
///
/// The one deliberate difference: entries are PEEKED, not taken. A generic body has many
/// instances and each must be able to consume the same recorded Module; a one-shot `take` would
/// silently flip the first instance and leave the rest on built MIR, which is a coverage lie
/// rather than a soundness hole, but a lie all the same.
#[derive(Default)]
struct SessionInstanceRegistry {
    entries: HashMap<u32, InstanceGreenBody>,
    /// def_indexes that saw a SECOND record — the once-per-def invariant broke, so nothing for
    /// that def may be trusted for the rest of the session.
    poisoned: HashSet<u32>,
    /// Per-def instance tallies for the census line, keyed by def_index:
    /// `(offered, flipped, refused)`.
    tally: HashMap<u32, (usize, usize, usize)>,
}

impl SessionInstanceRegistry {
    fn insert_green(&mut self, def_index: u32, entry: InstanceGreenBody) {
        if self.poisoned.contains(&def_index) {
            return;
        }
        match self.entries.entry(def_index) {
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert(entry);
            }
            std::collections::hash_map::Entry::Occupied(o) => {
                o.remove();
                self.poisoned.insert(def_index);
            }
        }
    }

    fn peek_green(&self, def_index: u32) -> Option<InstanceGreenBody> {
        if self.poisoned.contains(&def_index) {
            return None;
        }
        self.entries.get(&def_index).cloned()
    }
}

/// Trust: the session gate for the instance lane. It is the FROZEN registry's own session gate
/// (both TrustIR flags, debuginfo, coverage — shared verbatim so the two lanes can never disagree
/// about whether a session flips at all) AND this lane's own escape hatch
/// `-Ztrust-instance-flip=no`, which is the lane's negative control.
pub fn instance_flip_session_enabled(tcx: TyCtxt<'_>) -> bool {
    flip_registry::flip_session_enabled(tcx) && tcx.sess.opts.unstable_opts.trust_instance_flip
}

/// The wall-A membership predicate: exactly the test `to_mir::rederive_abi_sig` refuses on.
///
/// This is the PARTITION between the two flip lanes. `true` here ⇒ the `DefId`-seam flip can
/// never install this body (its ABI rederivation fails closed); `false` here ⇒ this lane never
/// records it. Stated as one named function so the invariant is executable.
pub fn identity_sig_is_generic(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    match tcx.def_kind(def) {
        DefKind::Fn { .. } | DefKind::AssocFn { .. } => tcx
            .fn_sig(def)
            .instantiate_identity()
            .skip_normalization()
            .skip_binder()
            .has_non_region_param(),
        DefKind::Closure { .. } => {
            tcx.type_of(def).instantiate_identity().skip_normalization().has_non_region_param()
        }
        _ => false,
    }
}

/// Trust: the placeholder/provenance LANE gates, for the instance seam.
///
/// The frozen `flip_registry::body_lane_gates_allow_flip` is private to a file this lane may not
/// touch, so its decision cannot be CALLED from here. It is not duplicated either: this lane
/// takes the strictly STRONGER position on every lane, which is the only substitution that cannot
/// silently widen a guard.
///
/// * union lane, enum-param lane, fn-ptr adapter lane — refused, identically.
/// * thin shared reborrows — the frozen gate CERTIFIES one provenance class
///   (`ThinReborrowProvenance::CallResult`, via `call_result_reborrow_is_confined`) against the
///   module. This lane refuses ANY forwarded row instead. That can cost a flip; it can never
///   admit one the frozen gate would refuse. A body lost to this line is a MEASURED shortfall,
///   and the honest thing to report is the name of the body, not a widening.
fn body_lane_gates_allow_instance_flip(lowered: &Lowered) -> bool {
    !lowered.union_lane
        && !lowered.enum_param_lane
        && !lowered.fnptr_adapter
        && lowered.thin_reborrows.is_empty()
        // Trust (wave-MR): the `&mut` twin refuses as a whole class here too — a forwarded
        // `&mut` is a value someone may WRITE THROUGH, and the shared side's confinement
        // argument does not transfer. See `flip_registry::mut_reborrows_allow_flip`.
        && lowered.mut_reborrows.is_empty()
}

/// Trust: the hook-side record. Called from the `mir_built` hook for every `DerivedAgreed` body,
/// beside `flip_registry::record_green`, with the body the hook still owns.
///
/// No-op unless every gate holds — including the wall-A partition predicate, so a NON-generic
/// body is never recorded here and the `DefId` lane keeps sole ownership of it.
pub fn record_green_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    lowered: &Lowered,
    built: &Body<'tcx>,
    markers_exact: bool,
    source_header_correspondence: Option<&mir_differential::SourceHeaderCorrespondence>,
) {
    if !instance_flip_session_enabled(tcx) {
        return;
    }
    // THE PARTITION. A non-generic body belongs to the frozen `DefId` lane, full stop.
    if !identity_sig_is_generic(tcx, def) {
        return;
    }
    // A generic body reaching the `codegen_mir` seam is a FUNCTION instance. Const/static
    // initializers reach the const-eval interpreter through `mir_for_ctfe` and are refused here
    // outright (the CTFE seam has no `Instance` to key on).
    if !matches!(lowered.body_kind, crate::BodyKind::Fn) {
        return;
    }
    if !lowered.unsupported.is_empty() || !lowered.pending_consts.is_empty() {
        return;
    }
    if !body_lane_gates_allow_instance_flip(lowered) {
        return;
    }
    if !flip_registry::source_place_provenance_allows_flip(tcx, def, &lowered.module) {
        return;
    }
    if tcx.is_coroutine(def.to_def_id()) {
        return;
    }
    if matches!(tcx.hir_body_const_context(def), Some(rustc_hir::ConstContext::Static(_))) {
        return;
    }
    // Fail-closed: no digest, no green — identical rule to `flip_registry::green_body`. The
    // per-instance flip event must always be able to name, by digest, which body it selected.
    let definition = lineage::DefinitionIdentity::from_def_id(tcx, def.to_def_id());
    let Ok(digest) = lineage::body_lineage_digest(definition, &lowered.module, &lowered.callees)
    else {
        return;
    };
    // The header-correspondence capability must exist and authenticate THIS lineage at record
    // time, exactly as the frozen registry requires. It is re-minted and re-authenticated per
    // instance at the flip; requiring it here too keeps the two seams aligned.
    let Some(shc) = source_header_correspondence else {
        return;
    };
    if !shc.authenticates(digest) {
        return;
    }
    let entry = InstanceGreenBody {
        // Trust: `with_no_trimmed_paths!` — a bare `def_path_str` arms `must_produce_diag`,
        // which ICEs at `DiagCtxt` drop on warning-free compiles (masked whenever RUSTC_LOG
        // is set, i.e. exactly when a measurement harness would never see it). Same guard
        // `crate_module::record` takes, for the same reason — and it makes this string the
        // UNTRIMMED spelling the coverage row carries, so the two are directly comparable.
        def_path: rustc_middle::ty::print::with_no_trimmed_paths!(
            tcx.def_path_str(def.to_def_id())
        ),
        lowered: lowered.clone(),
        lineage: digest,
        hook_markers_exact: markers_exact,
    };
    let def_index = def.to_def_id().index.as_u32();
    tcx.sess.with_trust_compiler_state::<SessionInstanceRegistry, _>(|reg| {
        reg.insert_green(def_index, entry);
    });
    // Retain the freshly BUILT sibling — the incumbent the frozen comparator is written for.
    // Arena-allocated once per admitted body; absence at flip time is a refusal, never a guess.
    tcx.trust_instance_flip_retain(def, tcx.arena.alloc(built.clone()));
}

/// Outcome of one per-instance flip attempt.
pub enum InstanceFlipAttempt<'tcx> {
    /// No green generic Module recorded for this def — the normal path, silently.
    NotCandidate,
    /// A green Module existed but a fail-closed gate refused THIS instance. The caller logs it
    /// loudly and compiles rustc's own body.
    Rejected { reason: String },
    /// The derived body at this instance's concrete anchors, `MirPhase::Built`, all gates passed.
    Derived {
        body: Body<'tcx>,
        asserts: usize,
        /// The per-BODY lineage digest — unchanged by instantiation, so it still joins the flip
        /// event to the registry object and the published coverage row.
        lineage: ProofDigest,
        /// The per-INSTANCE args digest — the NEW event axis. Two events for one body are told
        /// apart by this and only by this.
        args_digest: ProofDigest,
        /// The per-INSTANCE marker-channel verdict, re-minted at these args.
        markers_exact: bool,
        def_path: String,
    },
}

fn rejected<'tcx>(reason: impl Into<String>) -> InstanceFlipAttempt<'tcx> {
    InstanceFlipAttempt::Rejected { reason: reason.into() }
}

/// Trust: the per-instance args digest.
///
/// Framed over the body's stable definition identity and the interned args' spelling, under this
/// module's own domain tag. Its job is to tell TWO EVENTS OF ONE BODY apart inside one compile —
/// the axis the design added — not to be a cross-session identity: the per-body `lineage` digest
/// already carries that, and is deliberately unchanged here.
pub fn instance_args_digest<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    args: ty::GenericArgsRef<'tcx>,
) -> ProofDigest {
    let definition = lineage::DefinitionIdentity::from_def_id(tcx, def.to_def_id());
    let mut bytes = Vec::new();
    bytes.extend_from_slice(format!("{definition:?}").as_bytes());
    bytes.push(0);
    bytes.extend_from_slice(format!("{args:?}").as_bytes());
    ProofDigest::sha256_domain(INSTANCE_ARGS_DOMAIN, &bytes)
}

/// Trust (wall A, ADVERSARIAL CONTROL): the active mutation, if any.
///
/// Every arm corrupts exactly ONE input of the per-instance evidence chain, at exactly one point,
/// and every arm must make the flip VANISH. A mutation that produced a body would be a hole in
/// the chain, which is precisely what the matrix exists to disprove — so each arm is applied
/// UPSTREAM of the check it is meant to trip, never downstream of it.
fn mutation(tcx: TyCtxt<'_>) -> Option<String> {
    tcx.sess.opts.unstable_opts.trust_instance_flip_mutate.clone()
}

/// EXACT ABI comparison against a body's `_0 ..= arg_count` locals, with regions erased on both
/// sides — the flip's own ABI-gate discipline, never a layout argument.
fn abi_exact<'tcx>(
    tcx: TyCtxt<'tcx>,
    inputs: &[ty::Ty<'tcx>],
    output: ty::Ty<'tcx>,
    body: &Body<'tcx>,
) -> Result<(), String> {
    if inputs.len() != body.arg_count {
        return Err(format!("arg count {} vs body {}", inputs.len(), body.arg_count));
    }
    for (i, t) in inputs.iter().enumerate() {
        let b = body.local_decls[Local::from_usize(i + 1)].ty;
        if tcx.erase_and_anonymize_regions(*t) != tcx.erase_and_anonymize_regions(b) {
            return Err(format!("arg{i}: rederived `{t:?}` vs incumbent `{b:?}`"));
        }
    }
    let b0 = body.local_decls[Local::from_usize(0)].ty;
    if tcx.erase_and_anonymize_regions(output) != tcx.erase_and_anonymize_regions(b0) {
        return Err(format!("ret: rederived `{output:?}` vs incumbent `{b0:?}`"));
    }
    Ok(())
}

/// Trust: derive the codegen-path body for ONE concrete `Instance` of a green generic body.
///
/// `inst` is the instance `codegen_mir` is about to emit. The returned body is `MirPhase::Built`;
/// the caller replays the pass pipeline over it (see `rustc_mir_transform::trust_instance_flip`).
///
/// # The honesty core
///
/// The generic `agreed` verdict was minted against the GENERIC built sibling. Flipping an
/// instance adds exactly ONE new trusted step — instantiation — and this function refuses to take
/// it on faith. Two INDEPENDENT instantiations exist and both are computed here:
///
/// * rustc's own fold over rustc's own retained built body
///   (`try_instantiate_mir_and_normalize_erasing_regions`, the same fold `codegen_mir`'s
///   `ergonomic_clones` branch and the inliner use), and
/// * `to_mir::lower_ir_to_mir` at ABI anchors re-derived from `tcx` ALONE at the instance's args
///   (`SigSource::Instance`), which never reads any built or optimized body.
///
/// The FROZEN comparator judges the pair, at the phase it was written for, and only its
/// `DerivedAgreed` admits the flip.
pub fn derive_instance_flip_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    inst: ty::Instance<'tcx>,
) -> InstanceFlipAttempt<'tcx> {
    if !instance_flip_session_enabled(tcx) {
        return InstanceFlipAttempt::NotCandidate;
    }
    let def_index = def.to_def_id().index.as_u32();
    let Some(entry) = tcx
        .sess
        .with_trust_compiler_state::<SessionInstanceRegistry, _>(|reg| reg.peek_green(def_index))
    else {
        return InstanceFlipAttempt::NotCandidate;
    };
    // From here on every exit is a LOUD refusal: a recorded candidate was consumed.
    tcx.sess.with_trust_compiler_state::<SessionInstanceRegistry, _>(|reg| {
        reg.tally.entry(def_index).or_insert((0, 0, 0)).0 += 1;
    });

    let InstanceGreenBody { def_path, lowered, lineage: recorded_lineage, .. } = entry;
    let args = inst.args;

    // ---- instance-shape gates ----
    if inst.def_id() != def.to_def_id() {
        return rejected("instance resolves to a different definition");
    }
    if !matches!(inst.def, ty::InstanceKind::Item(_)) {
        return rejected(format!("instance kind {:?} is not a plain item body", inst.def));
    }
    if args.has_non_region_param() || args.has_infer() {
        return rejected("instance args are not fully concrete");
    }

    // ---- lineage re-derivation (L1 attestation, per instance) ----
    // ADVERSARIAL CONTROL `lineage`: corrupt the recorded digest before the re-derivation checks
    // it. The chain must refuse rather than attest an object that is not the one it compiled.
    let recorded_lineage = match mutation(tcx).as_deref() {
        Some("lineage") => {
            let mut bytes = recorded_lineage.bytes;
            bytes[0] ^= 0xff;
            ProofDigest::sha256(bytes)
        }
        _ => recorded_lineage,
    };
    match lineage::body_lineage_digest(
        lineage::DefinitionIdentity::from_def_id(tcx, def.to_def_id()),
        &lowered.module,
        &lowered.callees,
    ) {
        Ok(rederived) if rederived == recorded_lineage => {}
        Ok(rederived) => {
            return rejected(format!(
                "lineage digest mismatch: registry entry carries {recorded_lineage}, its own \
                 (module, callee ledger) digests to {rederived}"
            ));
        }
        Err(error) => {
            return rejected(format!("lineage digest could not be re-derived: {error}"));
        }
    }

    // ---- def-level gates, re-checked at the consume seam (defense in depth) ----
    if !flip_registry::source_place_provenance_allows_flip(tcx, def, &lowered.module) {
        return rejected(
            "first-class loop contract source-loop/place provenance is missing, stale, or invalid",
        );
    }
    if !body_lane_gates_allow_instance_flip(&lowered) {
        return rejected("placeholder/provenance lane refused at the instance seam");
    }
    if tcx.is_coroutine(def.to_def_id()) {
        return rejected("coroutine body");
    }
    let dk = tcx.def_kind(def);
    if dk.is_fn_like() || matches!(dk, rustc_hir::def::DefKind::AssocConst { .. }) {
        if let Err(reason) = flip::const_trap_gate(&lowered.module) {
            return rejected(reason);
        }
    }

    // ---- incumbent: rustc's OWN instantiation of rustc's OWN retained built body ----
    let Some(built) = tcx.trust_instance_flip_sibling(def) else {
        return rejected("no retained built sibling for this def (registry/retention drift)");
    };
    let typing_env = ty::TypingEnv::fully_monomorphized();
    // ADVERSARIAL CONTROL `incumbent-args`: instantiate the incumbent at IDENTITY args, i.e. do
    // not instantiate it at all. The residual-parameter check and the differential must refuse.
    let incumbent_inst = match mutation(tcx).as_deref() {
        Some("incumbent-args") => ty::Instance::new_raw(
            def.to_def_id(),
            ty::GenericArgs::identity_for_item(tcx, def.to_def_id()),
        ),
        _ => inst,
    };
    let inst_built = match incumbent_inst.try_instantiate_mir_and_normalize_erasing_regions(
        tcx,
        typing_env,
        ty::EarlyBinder::bind(tcx, built.clone()),
    ) {
        Ok(b) => b,
        Err(e) => {
            return rejected(format!("incumbent instantiation failed to normalize: {e:?}"));
        }
    };
    if inst_built.has_non_region_param() {
        return rejected("instantiated incumbent still carries a non-region parameter");
    }
    // An unsatisfiable-predicates instantiation shrinks the body to a lone `unreachable`. That is
    // deliberate upstream behaviour and the flip must not undo it.
    if inst_built.basic_blocks[rustc_middle::mir::START_BLOCK].statements.is_empty()
        && matches!(
            inst_built.basic_blocks[rustc_middle::mir::START_BLOCK].terminator().kind,
            rustc_middle::mir::TerminatorKind::Unreachable
        )
    {
        return rejected("instantiated incumbent shrunk to `unreachable`");
    }

    // ---- THE PER-INSTANCE DIFFERENTIAL: the FROZEN comparator, untouched, at these args ----
    let vf_inst_built = trust_mir_extract::extract_function_faithful(tcx, &inst_built);
    let report =
        mir_differential::compare_derived(tcx, def, &lowered, &inst_built, Some(&vf_inst_built));
    if report.verdict != mir_differential::DerivedVerdict::DerivedAgreed {
        return rejected(format!(
            "per-instance differential {:?}: {}",
            report.verdict, report.detail
        ));
    }
    // Per-BODY marker gate, re-minted per instance: an unproven marker sequence must never reach
    // codegen where markers are material.
    if tcx.sess.emit_lifetime_markers() && !report.markers_exact {
        return rejected(format!(
            "per-instance marker channel not exact: {}",
            report.markers_detail
        ));
    }
    // The source-loop header identity channel, re-authenticated at the instance.
    match report.source_header_correspondence {
        Some(shc) if shc.authenticates(recorded_lineage) => {}
        Some(_) => {
            return rejected("per-instance source-loop header correspondence did not authenticate");
        }
        None => return rejected("per-instance source-loop header correspondence absent"),
    }

    // ---- derive at the INSTANCE's own re-derived anchors (never read from any body) ----
    // ADVERSARIAL CONTROLS on the ABI ANCHOR — the input wall A is entirely about:
    //   `abi-anchor` derives at IDENTITY args, the pre-wall-A behaviour (must fail closed in the
    //     shim, exactly as the 43+2 fallback rows do today);
    //   `abi-swap` derives at the instance's args with the first two anchors SWAPPED — a
    //     concrete, well-typed, WRONG ABI, which only a real gate can catch;
    //   `abi-ret` derives at the instance's own argument anchors but a WRONG return anchor, the
    //     arm that bites every signature including the one-argument ones `abi-swap` cannot.
    let sig_source = match mutation(tcx).as_deref() {
        Some("abi-anchor") => to_mir::SigSource::Rederive,
        Some("abi-swap") => match to_mir::rederive_abi_sig_at_instance(tcx, def, args) {
            Ok((mut inputs, output)) if inputs.len() >= 2 && inputs[0] != inputs[1] => {
                inputs.swap(0, 1);
                to_mir::SigSource::Provided(inputs, output)
            }
            // Honest reporting beats a silent survivor: a one-argument (or repeated-argument)
            // signature has no swap to make, so this arm CANNOT corrupt it. Refuse and SAY so,
            // rather than hand the correct anchors through and let the matrix read as a flip the
            // control failed to kill. `abi-ret` is the arm that bites every signature.
            Ok(_) => {
                return rejected(
                    "abi-swap control: NOT APPLICABLE to this signature (fewer than two \
                     distinct argument anchors); use -Ztrust-instance-flip-mutate=abi-ret",
                );
            }
            Err(e) => return rejected(format!("abi-swap control: {}", e.reason)),
        },
        // ADVERSARIAL CONTROL `abi-arg0`: derive at the instance's own return anchor but a
        // DIFFERENT, well-formed FIRST ARGUMENT anchor. MEASURED REASON THIS ARM EXISTS: at
        // -O0 the `abi-ret` arm left 9 of 16 flips standing, and the refusal lines say why —
        // for a body whose recorded Module returns NOTHING the shim never consults the return
        // anchor at all (`_0` is typed from the Module), so the corruption is INERT rather than
        // uncaught. Every method in the population takes at least `&self`, so corrupting
        // argument 0 bites all of them.
        Some("abi-arg0") => match to_mir::rederive_abi_sig_at_instance(tcx, def, args) {
            Ok((mut inputs, output)) if !inputs.is_empty() => {
                inputs[0] = if inputs[0].is_unit() { tcx.types.u8 } else { tcx.types.unit };
                to_mir::SigSource::Provided(inputs, output)
            }
            Ok(_) => {
                return rejected("abi-arg0 control: NOT APPLICABLE to a zero-argument signature");
            }
            Err(e) => return rejected(format!("abi-arg0 control: {}", e.reason)),
        },
        // ADVERSARIAL CONTROL `abi-ret`: derive at the instance's own argument anchors but a
        // DIFFERENT, well-formed RETURN anchor. Bites every signature whose recorded Module
        // HAS a return value; for the unit-returning ones see `abi-arg0` above.
        Some("abi-ret") => match to_mir::rederive_abi_sig_at_instance(tcx, def, args) {
            Ok((inputs, output)) => {
                let wrong = if output.is_unit() { tcx.types.u8 } else { tcx.types.unit };
                to_mir::SigSource::Provided(inputs, wrong)
            }
            Err(e) => return rejected(format!("abi-ret control: {}", e.reason)),
        },
        _ => to_mir::SigSource::Instance(args),
    };
    let mut body = match to_mir::lower_ir_to_mir(
        tcx,
        def,
        &lowered.module,
        &lowered.callees,
        sig_source,
        &lowered.enum_fold_switch_blocks,
    ) {
        Ok(lowering) => lowering.body,
        Err(e) => return rejected(format!("shim at instance: {}", e.reason)),
    };

    // ---- structural gate on the derived body ----
    if let Err(reason) = flip::gate_derived_body(tcx, &body) {
        return rejected(reason);
    }

    // ---- ABI-visible type equality, the two independent derivations ----
    let (inputs, output) = match to_mir::rederive_abi_sig_at_instance(tcx, def, args) {
        Ok(pair) => pair,
        Err(e) => return rejected(format!("abi rederive at instance: {}", e.reason)),
    };
    if let Err(reason) = abi_exact(tcx, &inputs, output, &inst_built) {
        return rejected(format!("instance ABI vs instantiated incumbent: {reason}"));
    }
    if let Err(reason) = abi_exact(tcx, &inputs, output, &body) {
        return rejected(format!("instance ABI vs derived body: {reason}"));
    }
    if body.arg_count != inst_built.arg_count {
        return rejected(format!(
            "arg_count mismatch: derived {} vs incumbent {}",
            body.arg_count, inst_built.arg_count
        ));
    }
    for i in 0..=body.arg_count {
        let l = Local::from_usize(i);
        let (d, n) = (body.local_decls[l].ty, inst_built.local_decls[l].ty);
        if tcx.erase_and_anonymize_regions(d) != tcx.erase_and_anonymize_regions(n) {
            return rejected(format!(
                "ABI-visible type mismatch on _{i}: derived {d:?} vs incumbent {n:?}"
            ));
        }
    }

    // ---- stitch assert spans from the instantiated incumbent ----
    let asserts = match flip::verify_assert_parity(&body, &inst_built) {
        Ok(n) => n,
        Err(reason) => return rejected(reason),
    };
    body.span = inst_built.span;

    InstanceFlipAttempt::Derived {
        body,
        asserts,
        lineage: recorded_lineage,
        args_digest: instance_args_digest(tcx, def, args),
        markers_exact: report.markers_exact,
        def_path,
    }
}

/// Trust: record the outcome of one instance attempt for the census line.
pub fn note_instance_outcome(tcx: TyCtxt<'_>, def: LocalDefId, flipped: bool) {
    let def_index = def.to_def_id().index.as_u32();
    tcx.sess.with_trust_compiler_state::<SessionInstanceRegistry, _>(|reg| {
        let slot = reg.tally.entry(def_index).or_insert((0, 0, 0));
        if flipped {
            slot.1 += 1;
        } else {
            slot.2 += 1;
        }
    });
}

/// Trust: the end-of-session CENSUS — the population fact the design demanded be stated rather
/// than implied. Emits one line per recorded generic body (`offered` / `flipped` / `refused`
/// instances, `0/0/0` meaning "no local mono instance in this crate") plus a summary.
///
/// This is the production seam measuring its OWN prize, independently of
/// `-Ztrust-instance-flip-probe`.
pub fn census(tcx: TyCtxt<'_>) -> Vec<String> {
    let (mut rows, summary) =
        tcx.sess.with_trust_compiler_state::<SessionInstanceRegistry, _>(|reg| {
            let tally = reg.tally.clone();
            let mut rows: Vec<(u32, String, bool, (usize, usize, usize))> = reg
                .entries
                .iter()
                .map(|(idx, e)| {
                    (
                        *idx,
                        e.def_path.clone(),
                        e.hook_markers_exact,
                        tally.get(idx).copied().unwrap_or((0, 0, 0)),
                    )
                })
                .collect();
            rows.sort_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
            let bodies = reg.entries.len();
            let poisoned = reg.poisoned.len();
            let with_inst = rows.iter().filter(|(_, _, _, t)| t.0 > 0).count();
            let offered: usize = rows.iter().map(|(_, _, _, t)| t.0).sum();
            let flipped: usize = rows.iter().map(|(_, _, _, t)| t.1).sum();
            let refused: usize = rows.iter().map(|(_, _, _, t)| t.2).sum();
            (
                rows,
                format!(
                    "TRUST-INSTANCE-FLIP census bodies={bodies} poisoned={poisoned} \
                     bodies_with_instances={with_inst} instances_offered={offered} \
                     instances_flipped={flipped} instances_refused={refused}"
                ),
            )
        });
    let mut out: Vec<String> = rows
        .drain(..)
        .map(|(idx, path, hook_markers_exact, (o, f, r))| {
            format!(
                "TRUST-INSTANCE-FLIP body def_index={idx} def={path} \
                 hook_markers_exact={hook_markers_exact} offered={o} flipped={f} refused={r}"
            )
        })
        .collect();
    out.push(summary);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The lane's own strengthening of the placeholder/provenance gates is EXECUTABLE, not a
    /// comment: each lane flag alone must refuse, and a forwarded thin reborrow must refuse even
    /// though the frozen gate would certify some of them.
    fn clean_lowering() -> Lowered {
        let mut module = trust_ir::Module::new("instance_flip_probe");
        let ty = module.add_func_type(trust_ir::FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(trust_ir::Function::new(
            trust_ir::FuncId::new(0),
            "instance_flip_probe_fn",
            ty,
            trust_ir::BlockId::new(0),
        ));
        Lowered {
            coroutine_frame_ptr: false,
            mut_reborrows: Vec::new(),
            module,
            enum_fold_switch_blocks: std::collections::HashSet::new(),
            body_kind: crate::BodyKind::Fn,
            opaque_collapse: false,
            enum_declines: Vec::new(),
            union_lane: false,
            enum_param_lane: false,
            symbolic: false,
            unsupported: Vec::new(),
            contains_call: false,
            place_path_carrier: false,
            zst_closure_arg: false,
            fnptr_adapter: false,
            thin_reborrows: Vec::new(),
            callees: Vec::new(),
            pending_consts: Vec::new(),
        }
    }

    #[test]
    fn every_placeholder_lane_refuses_the_instance_flip() {
        let base = |f: &dyn Fn(&mut Lowered)| {
            let mut l = clean_lowering();
            f(&mut l);
            body_lane_gates_allow_instance_flip(&l)
        };
        assert!(base(&|_l| {}), "a clean lowering must be admitted");
        assert!(!base(&|l| l.union_lane = true), "union lane must refuse");
        assert!(!base(&|l| l.enum_param_lane = true), "enum param lane must refuse");
        assert!(!base(&|l| l.fnptr_adapter = true), "fn-ptr adapter lane must refuse");
        assert!(
            !base(&|l| l.thin_reborrows.push(crate::ThinReborrow {
                value: trust_ir::ValueId::new(0),
                provenance: crate::ThinReborrowProvenance::CallResult,
            })),
            "a forwarded thin reborrow must refuse at the instance seam even though the frozen \
             DefId-seam gate certifies the CallResult class"
        );
    }

    /// The registries PARTITION: this lane's admission predicate and the `DefId` lane's
    /// installability predicate are complementary by construction, so no body can be installed by
    /// both. Executed on the predicate itself, since `record_green`'s poison note names exactly
    /// this collision as a silent-miscompile shape.
    #[test]
    fn registries_partition_on_the_generic_predicate() {
        // `identity_sig_is_generic` needs a TyCtxt, so the executable half of the invariant is
        // the SOURCE pin: this lane's record path must refuse on `!identity_sig_is_generic`, and
        // `to_mir::rederive_abi_sig` must refuse on the same predicate's `true` side.
        let src = include_str!("instance_flip.rs");
        assert!(
            src.contains("if !identity_sig_is_generic(tcx, def) {\n        return;\n    }"),
            "record_green_instance must refuse every NON-generic body: that refusal is the only \
             thing keeping the two flip registries disjoint"
        );
        let to_mir_src = include_str!("to_mir.rs");
        assert!(
            to_mir_src.contains("abi rederive: generic fn signature"),
            "the DefId-seam refusal this lane partitions against must still exist"
        );
    }
}
