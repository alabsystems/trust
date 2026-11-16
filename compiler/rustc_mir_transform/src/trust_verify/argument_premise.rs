//! Trust (2026-10-08): LANGUAGE PREMISES about a body's reference ARGUMENTS that
//! nothing in this compiler proves, decided by the agent under the owner's
//! delegation (docs/DECISION_QUEUE.md D14, D15) and graded by owner ruling R1's rule.
//!
//! # NOALIAS_MUT_ARGS (D15)
//!
//! Two `&mut` arguments live for the whole call never overlap: rustc marks them
//! `noalias`, and a program in which they overlap has already hit UB (both are
//! protected for the call under Stacked and Tree Borrows). vcgen therefore keeps
//! the facts about one such argument's pointee across a store through another
//! (`trust_vcgen` `path_defs::deref_store_havoc_names`).
//!
//! Scope, each limit load-bearing:
//!  * a POINTER-FREE `T` (no reference, raw or heap pointer inside it): `noalias`
//!    covers `*arg`, not memory reached through a pointer stored in it, and vcgen
//!    spares the other argument's whole name tree (review round 83);
//!  * an ARGUMENT local of type `&mut T` with `T: Unpin` (rustc emits no `noalias`
//!    for a `!Unpin` pointee, and a self-referential pinned value may legally be
//!    reached through a second argument); a generic `T` not provably `Unpin` is
//!    out;
//!  * vcgen's structural gate on top: the argument is never reassigned, never a
//!    call destination, never borrowed as a whole local, and the store goes
//!    through it with exactly ONE leading `Deref` (a reborrow, a raw pointer, a
//!    pointer reached through a field or produced by a call is not the argument);
//!  * a body of THIS crate only (a re-derived dependency body gets no premise);
//!  * INSTALLED only where it changes a havoc list (`noalias_premise_would_fire`),
//!    so every body whose havoc lists it cannot change keeps byte-identical
//!    obligations and grades. That test is coarser than "some fact needed it", so
//!    an installed premise does not demote the whole body: each row is graded on
//!    its own (# Grading below).
//!
//! # REFERENCE_ARG_BOX_VALID (D14)
//!
//! A `&`/`&mut` argument's pointee is a valid value of its type for the whole
//! call, so a `Box` stored in it is non-null, aligned and LIVE, and nothing
//! outside the body frees or reseats it while the argument is live (its
//! protector). vcgen then treats the compiler-synthesized `*box` of a box copied
//! out of `(*arg).path` like the `&T` deref it is and mints no `[unsafe:sep:*]`
//! rows for it (`trust_vcgen` `sep_engine::reference_param_pointee_box_root`).
//! Reference deep validity is not settled language semantics and nothing here
//! proves it, so this is a premise exactly like D15.
//!
//! Scope: an ARGUMENT local of reference type, a body of THIS crate, and vcgen's
//! fence on top — exactly one leading `Deref`, a validity-preserving
//! struct/tuple/variant path (no union), the argument CONFINED (only reads of its
//! pointee and shared borrows of parts DISJOINT from the box: a shared hand-out of
//! the box slot lets a callee `ptr::read` a duplicate and drop it), and every
//! copy of the box used only by its synthesized pointer cast. Installed only for
//! the arguments for which it roots a deref that is not rooted without it
//! (`trust_vcgen::reference_box_root_would_fire`).
//!
//! Trust (2026-10-14, DECISION_QUEUE D100): the same premise roots every box
//! that main's 13c reference lane reaches THROUGH a reference argument (`&Box`,
//! `&mut Box`, `&S.b`, `&Option<Box>`, `&&Box`, `eval(e: &Expr)`), under that
//! lane's own fences (docs/TCB.md, "A `Box` reached THROUGH a validity-rooted
//! reference"). vcgen admits such a root only for an argument installed here, and
//! `reference_box_root_would_fire` re-runs that walk, so the install, demotion and
//! disclosure below cover it with no change on this side. A dependency body gets
//! no premise, so it keeps those rows (fail-closed).
//!
//! Unlike D15, the premise REMOVES rows instead of discharging them, so a body
//! left with ZERO rows still rests on it: its marker is never cleared (a caller
//! under `certify` stays refused rather than spend a verdict built on it).
//!
//! # Grading (R1's rule, per row)
//!
//! A row whose VC the premise shaped is NOT `Certified`: the kernel checked that
//! VC, but the VC is faithful to the program only under the premise. Its
//! `KernelCertified` token becomes `ArgumentPremiseKernelDischarge`
//! (`Trusted`/`Constructive`, no kernel evidence, so the authenticated publication
//! boundary withholds the row).
//!
//! Trust (2026-10-17, gate RCA "premise"): which rows the premise shaped is decided
//! per ROW, not per body. Until then every `KernelCertified` token of a
//! premise-carrying body was demoted, and the 2026-10-16 candidate gate lost 76
//! rows the seal proved in such bodies, rows that mostly never touched the premise
//! (`aterm_gpu::renderer::clip_textured_quad_x`: 17 rows, the bounds rows of
//! constant indices into a `&mut [f32; 4]` among them, all withheld). Now the
//! compiler generates the body a second time with NO premise installed
//! (`premise_free_generation`, held by [`PremiseFreeRows`]: the same context,
//! summaries, nominations, SAFETY-comment declarations, TINV scope and level filter
//! as the consumed generation, under its own fresh budget) and records the exact VC
//! payload of every row it produces. A kernel token whose certified VC payload is
//! among them stays `KernelCertified`: that exact VC is one the compiler emits for
//! this body without the premise, so its certificate proves a premise-free
//! obligation. Every other token is demoted: a row the premise shaped (D15 spared a
//! name its VC reads; D95/D100 left a deref unrowed that its VC depends on), a
//! grounded catch-all (its residual is faithful only under sibling verdicts), a
//! row the E5 feedback strengthened, and every token of a body whose premise-free
//! generation tripped its budget. A coincidental payload match is still sound:
//! the payload names the kind, location and formula, and the premise-free
//! generation emitting it is the claim the token stands on.
//!
//! A premise only where a row needs it: before dispatch, a row whose VC the
//! premise changed but whose premise-free TWIN (the same obligation generated
//! without the premise, `adopt_premise_free_twins`) the interval lane proves
//! dispatches the twin instead. The premise added facts that row did not need (in
//! `clip_textured_quad_x`, the definitions of `old_x` and `old_w` kept across the
//! stores through `uv` by the bounds rows of later constant indices); without
//! them the row is exactly a premise-free body's row, and is graded like one. A
//! twin the interval lane does not prove (the `*n += 1` of a guarded update, whose
//! twin is the false refutation the premise exists to stop) is never dispatched.
//!
//! The BODY stays graded under the premise, whatever its rows: it licenses no
//! check elision, its verdict is never spent by a caller
//! (`verdict_rests_on_user_axiom`), it is never registered panic-free, and the
//! premise is disclosed beside the report, in the JSON `modeled_facts` and as the
//! unproved `argument-premise` transport row. A D95/D100 body owes the rows the
//! premise removed to it, and those exist only as that disclosure.

use super::*;

/// The disclosure key of the D15 premise.
pub(super) const NOALIAS_MUT_ARGS: &str = "NOALIAS_MUT_ARGS";

/// The disclosure key of the D14 premise.
pub(super) const REFERENCE_ARG_BOX_VALID: &str = "REFERENCE_ARG_BOX_VALID";

/// The MIR locals of `body`'s ARGUMENTS, the D14 candidates (vcgen's install gate
/// decides which of them root anything). Empty for a dependency body, a promoted
/// body or a shim, for the reason [`noalias_candidate_args`] gives.
///
/// Trust (2026-10-15, DECISION_QUEUE D100): EVERY argument, not only `ty::Ref` ones.
/// Main's 13c lane also roots a box reached through a reference stored INSIDE a
/// by-value argument (`Option<&Box<T>>`, `W { h: &Box<T> }`), on the same premise;
/// vcgen now roots those only under the installed premise, so the gate must be
/// offered them. A type walk cannot pre-filter (a struct's reference fields are not
/// among its generic arguments), and the gate fires only where the premise roots a
/// nominated box deref, so offering every argument installs nothing extra.
pub(super) fn reference_box_candidate_args<'tcx>(body: &Body<'tcx>) -> Vec<usize> {
    if !body.source.def_id().is_local()
        || body.source.promoted.is_some()
        || !matches!(body.source.instance, ty::InstanceKind::Item(_))
    {
        return Vec::new();
    }
    body.args_iter().map(|local| local.as_usize()).collect()
}

/// The MIR locals of `body`'s `&mut T` ARGUMENTS with `T: Unpin`, the D15
/// candidates. Empty for a promoted body or a shim.
pub(super) fn noalias_candidate_args<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<usize> {
    // LOCAL bodies only (review round 81): the marker is recorded per local
    // `DefId`, so a premise installed for a re-derived DEPENDENCY body would rest
    // its verdict on the premise with nothing demoting or disclosing it, and a
    // caller then reported kernel-certified rows built on it.
    if !body.source.def_id().is_local()
        || body.source.promoted.is_some()
        || !matches!(body.source.instance, ty::InstanceKind::Item(_))
    {
        return Vec::new();
    }
    // Trust (2026-10-15): `Ty::is_unpin` asks `require_lang_item(Unpin)`, which is a hard
    // error ("requires `unpin` lang_item") when the crate graph's `core` defines none — a
    // whole-`core` substitute (`tests/ui/trust/static_str_write_fmt_fmtwrite_core_
    // substitution_impostor_refuted.rs`, `fmt_writer_relative_..._impostor_refuted.rs`)
    // failed to build there instead of reaching the refusals it pins. With no `Unpin`
    // nothing is provably `Unpin`, so no argument is a candidate (no premise: fail-closed).
    if tcx.lang_items().unpin_trait().is_none() {
        return Vec::new();
    }
    let typing_env = body.typing_env(tcx);
    body.args_iter()
        .filter(|&local| {
            matches!(
                body.local_decls[local].ty.kind(),
                ty::Ref(_, inner, ty::Mutability::Mut)
                    if !inner.has_non_region_param()
                        && inner.is_unpin(tcx, typing_env)
                        && pointee_is_pointer_free(tcx, typing_env, *inner, 32)
            )
        })
        .map(|local| local.as_usize())
        .collect()
}

/// Does a value of `ty` own NO pointer of any kind (no reference, raw pointer,
/// `Box`/`Vec`/`Rc` heap pointer, `dyn`, union, closure capture)? `noalias` on a
/// `&mut T` argument covers `*arg` itself, not memory reached through a pointer
/// STORED in it (review round 83: `b.p = a as *mut u8` is based on `a`, so a store
/// through `*a` may change `*b.p`). vcgen spares the other argument's whole name
/// tree, so the premise is admitted only when that tree is exactly `*arg`'s own
/// bytes: scalars, arrays/slices/tuples of them, and structs or enums of them.
/// Fuel exhaustion, a generic or an unknown shape declines.
fn pointee_is_pointer_free<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    fuel: u32,
) -> bool {
    if fuel == 0 {
        return false;
    }
    match ty.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str | ty::Never => true,
        ty::Array(elem, _) | ty::Slice(elem) => {
            pointee_is_pointer_free(tcx, typing_env, *elem, fuel - 1)
        }
        ty::Tuple(elems) => {
            elems.iter().all(|elem| pointee_is_pointer_free(tcx, typing_env, elem, fuel - 1))
        }
        ty::Adt(def, args) if !def.is_union() && !def.is_box() => def.all_fields().all(|field| {
            tcx.try_normalize_erasing_regions(typing_env, field.ty(tcx, *args))
                .is_ok_and(|field_ty| pointee_is_pointer_free(tcx, typing_env, field_ty, fuel - 1))
        }),
        _ => false,
    }
}

/// The source name of argument local `local`, or `_N`.
fn argument_name(body: &Body<'_>, local: usize) -> String {
    body.var_debug_info
        .iter()
        .find_map(|info| match &info.value {
            VarDebugInfoContents::Place(place)
                if place.local.as_usize() == local && place.projection.is_empty() =>
            {
                Some(format!("`{}`", info.name))
            }
            _ => None,
        })
        .unwrap_or_else(|| format!("`_{local}`"))
}

/// Record the premises installed for `body` (or clear a stale record). Called
/// where the vcgen context is built, BEFORE generation, so every later reader
/// (the demotion, the spending gate, the disclosure) sees it.
pub(super) fn record(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    noalias_params: &[usize],
    reference_box_params: &[usize],
) {
    let Some(local) = body.source.def_id().as_local() else { return };
    if body.source.promoted.is_some() {
        return;
    }
    let mut premises = Vec::new();
    if !noalias_params.is_empty() {
        let names: Vec<String> =
            noalias_params.iter().map(|&param| argument_name(body, param)).collect();
        premises.push(format!(
            "{NOALIAS_MUT_ARGS}: the `&mut` arguments {} are assumed pairwise disjoint for the \
             whole call (Rust's `noalias`: two overlapping live `&mut` arguments are UB)",
            names.join(", ")
        ));
    }
    if !reference_box_params.is_empty() {
        let names: Vec<String> =
            reference_box_params.iter().map(|&param| argument_name(body, param)).collect();
        premises.push(format!(
            "{REFERENCE_ARG_BOX_VALID}: the `Box` reached through a reference in the arguments {} \
             is assumed valid and live for the whole call (a valid reference points to a valid \
             value, and nothing outside the body frees it while the argument is live)",
            names.join(", ")
        ));
    }
    with_crate_verification_state(tcx.sess, |state| {
        if premises.is_empty() {
            state.argument_premises.remove(&local);
        } else {
            state.argument_premises.insert(local, premises);
        }
    });
}

/// Drop the D15 premise from `body`'s record, keeping any other. For a body with
/// NO rows (review round 82): D15 only changes which facts discharge minted rows,
/// so no verdict of a zero-row body rests on it. D14 REMOVES rows, so it stays.
pub(super) fn clear_noalias_premise(tcx: TyCtxt<'_>, body: &Body<'_>) {
    let Some(local) = body.source.def_id().as_local() else { return };
    with_crate_verification_state(tcx.sess, |state| {
        if let Some(premises) = state.argument_premises.get_mut(&local) {
            premises.retain(|fact| !fact.starts_with(NOALIAS_MUT_ARGS));
            if premises.is_empty() {
                state.argument_premises.remove(&local);
            }
        }
    });
}

/// The disclosure strings of the premises installed for `def` (empty when none).
pub(super) fn premises_for(sess: &Session, def: DefId) -> Vec<String> {
    let Some(local) = def.as_local() else { return Vec::new() };
    with_crate_verification_state(sess, |state| {
        state.argument_premises.get(&local).cloned().unwrap_or_default()
    })
}

/// Whether a `modeled_facts` entry is an argument premise's disclosure.
pub(super) fn is_argument_premise_fact(fact: &str) -> bool {
    fact.starts_with(NOALIAS_MUT_ARGS) || fact.starts_with(REFERENCE_ARG_BOX_VALID)
}

/// Whether any premise was installed for `def`.
pub(super) fn body_carries_premise(sess: &Session, def: DefId) -> bool {
    !premises_for(sess, def).is_empty()
}

/// The premise name a demoted row carries: the first installed premise's key.
pub(super) fn demotion_premise(sess: &Session, def: DefId) -> Option<&'static str> {
    premises_for(sess, def).first().map(|fact| {
        if fact.starts_with(NOALIAS_MUT_ARGS) {
            NOALIAS_MUT_ARGS
        } else if fact.starts_with(REFERENCE_ARG_BOX_VALID) {
            REFERENCE_ARG_BOX_VALID
        } else {
            "ARGUMENT_PREMISE"
        }
    })
}

/// What the body's generation produces with NO argument premise installed (module
/// doc, # Grading; built by `premise_free_generation`).
pub(super) struct PremiseFreeGeneration {
    /// The exact key of every VC that generation produced (a [`RowKey`], T3 L4 C09:
    /// its canonical string, `canonical_exact_vc_payload`, decides): solver and
    /// preclassified, before and after the level filter and both spine flips.
    pub(super) payloads: FxHashSet<RowKey>,
    /// Its dispatched VC list after the level filter, the dedupe and both spine
    /// flips: the list `adopt_premise_free_twins` takes a twin from.
    pub(super) solver_vcs: Vec<VerificationCondition>,
}

/// The body's premise-free generation, built EAGERLY for every body the compiler
/// installed a premise for (it costs one more VC generation, measured at 1-19 ms on
/// the gate's bodies) and shared by both feedback passes. `None` (no premise, or a
/// generation that could not complete) answers "not premise-free" for every row, so
/// every kernel token of a premise-carrying body stays demoted and no twin is
/// adopted.
pub(super) struct PremiseFreeRows {
    generation: Option<PremiseFreeGeneration>,
}

impl PremiseFreeRows {
    /// No premise-free generation: every question answers `false` (fail closed).
    pub(super) fn unavailable() -> Self {
        PremiseFreeRows { generation: None }
    }

    pub(super) fn new(generation: Option<PremiseFreeGeneration>) -> Self {
        PremiseFreeRows { generation }
    }

    /// Does the premise-free generation produce a row whose exact key is `key`?
    pub(super) fn produces(&self, key: &RowKey) -> bool {
        self.generation.as_ref().is_some_and(|generation| generation.payloads.contains(key))
    }

    /// The premise-free generation's dispatched VCs (empty when there is none).
    pub(super) fn solver_vcs(&self) -> &[VerificationCondition] {
        match &self.generation {
            Some(generation) => &generation.solver_vcs,
            None => &[],
        }
    }
}

/// The exact identity of a row apart from the facts its generation conjoined: the
/// exact key ([`RowKey`]) of the VC with the formula blanked and the obligation
/// record's `wrappers` cleared. What stays is the kind, function, location, contract
/// metadata, and the record's `body`, `subject` and `width`: WHICH obligation this
/// is. The wrappers go because they are exactly the facts and path guards the
/// emitter wrapped around the body (`ConjoinFactsLast`, `PathGuardOr`), so they
/// carry what the premise changes: `clip_textured_quad_x`'s premised bounds rows
/// conjoin `old_x = rect[0]` in a `ConjoinFactsLast` their twins do not (measured
/// 2026-10-18: keyed with the wrappers, no row of it, of `guarded_index` or of the
/// `touched` ui revision had a twin). Two VCs with equal keys are the same
/// obligation generated two ways; pairing is only ever by a key unique on both
/// sides, and an adopted twin is the whole premise-free VC, record included.
fn twin_key(vc: &VerificationCondition) -> Option<RowKey> {
    let mut key = vc.clone();
    key.formula = Formula::Bool(true);
    if let Some(record) = key.obligation.as_mut() {
        record.wrappers.clear();
    }
    RowKey::of(&key)
}

/// Trust (2026-10-17, gate RCA "premise", second half): a premise only where a row
/// needs it. A dispatched row whose VC the premise changed (its payload is not one
/// the premise-free generation produces) is replaced by its premise-free TWIN — the
/// one premise-free VC that is the same obligation (`twin_key`: equal apart from the
/// formula and the record's wrappers), itself not produced by the premised
/// generation — when `twin_is_decided` proves
/// the twin. The row then carries exactly the VC a premise-free body carries, so it
/// is graded like one (its kernel token is kept, `demote_argument_premise_authorities`).
/// A row with no unique twin, a twin `twin_is_decided` does not prove (`guarded`'s
/// `*n += 1`, whose twin is the false refutation the premise exists to stop), or a VC
/// carrying a type-invariant tag keeps its premised VC and is demoted as before.
///
/// `aterm_gpu::renderer::clip_textured_quad_x`: the bounds rows of `uv[2] *= kept`,
/// `rect[0] = x0` and `rect[2] = x1 - x0` (constant indices into `&mut [f32; 4]`)
/// carry `old_x = rect[0]`, `old_w = rect[2]` only because the premise kept them
/// across the stores through `uv`; their twins drop those two equations and are
/// proved by the interval lane exactly like the premised rows.
///
/// Trust (T3 L4, C09): every key here is a [`RowKey`], so each lookup compares the
/// canonical strings inside a key, and each hashed table counts the keys it was built
/// from against the identity oracle (`row_key::count_partition`).
///
/// Returns how many rows adopted their twin.
pub(super) fn adopt_premise_free_twins(
    solver_vcs: &mut [VerificationCondition],
    premise_free: &PremiseFreeRows,
    mut twin_is_decided: impl FnMut(&VerificationCondition) -> bool,
) -> usize {
    let free = premise_free.solver_vcs();
    if free.is_empty() {
        return 0;
    }
    let premised: Vec<RowKey> = solver_vcs.iter().filter_map(RowKey::of).collect();
    row_key::count_partition(&premised);
    let premised_payloads: FxHashSet<RowKey> = premised.into_iter().collect();
    // Twins: premise-free VCs the premised generation does not produce, by key; a
    // key held by more than one of them pairs nothing.
    let mut twins: FxHashMap<RowKey, Option<usize>> = FxHashMap::default();
    let mut twin_keys: Vec<RowKey> = Vec::new();
    for (index, vc) in free.iter().enumerate() {
        let Some(payload) = RowKey::of(vc) else { continue };
        if premised_payloads.contains(&payload) {
            continue;
        }
        let Some(key) = twin_key(vc) else { continue };
        if row_key::oracle_runs() {
            twin_keys.push(key.clone());
        }
        twins.entry(key).and_modify(|slot| *slot = None).or_insert(Some(index));
    }
    row_key::count_partition(&twin_keys);
    // Rows the premise changed, in row order, with their keys; a key held by more
    // than one of them pairs nothing.
    let mut shaped: Vec<(usize, RowKey)> = Vec::new();
    let mut shaped_per_key: FxHashMap<RowKey, usize> = FxHashMap::default();
    for (index, vc) in solver_vcs.iter().enumerate() {
        let Some(payload) = RowKey::of(vc) else { continue };
        if premise_free.produces(&payload) {
            continue;
        }
        let Some(key) = twin_key(vc) else { continue };
        *shaped_per_key.entry(key.clone()).or_insert(0) += 1;
        shaped.push((index, key));
    }
    row_key::count_partition(shaped.iter().map(|(_, key)| key));
    let mut adopted = 0;
    for (row, key) in shaped {
        if shaped_per_key.get(&key) != Some(&1) {
            continue;
        }
        let Some(Some(twin)) = twins.get(&key) else { continue };
        let twin = &free[*twin];
        if !matches!(solver_vcs[row].type_invariant_tags(), trust_types::TinvTagScan::None)
            || !matches!(twin.type_invariant_tags(), trust_types::TinvTagScan::None)
            || !twin_is_decided(twin)
        {
            continue;
        }
        solver_vcs[row] = twin.clone();
        adopted += 1;
    }
    adopted
}

/// The human disclosure, one note per premise on the body's span.
pub(super) fn note_premise_disclosure<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
    for note in prepare_premise_disclosures(tcx, body) {
        note.emit(tcx);
    }
}

pub(super) fn prepare_premise_disclosures<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<PreparedLocatedNote> {
    let mut notes = Vec::new();
    for fact in premises_for(tcx.sess, body.source.def_id()) {
        // Trust (2026-10-15): the decisions as numbered since the merge of 2026-10-14
        // (the soundness line's D14/D15 are D95/D96; D100 widened D95 to 13c's roots).
        let (kind, decision) = if fact.starts_with(REFERENCE_ARG_BOX_VALID) {
            ("argument-validity", "D95, D100")
        } else {
            ("aliasing", "D96")
        };
        notes.push(PreparedLocatedNote {
            span: body.span,
            report: PreparedHumanReport {
                summary: format!(
                    "Trust {kind} premise {fact}. Assumed for this body, not proved: a row \
                     whose verification condition differs from the one generated without the \
                     premise is not kernel-certified (it reports `Trusted`, and the \
                     authenticated `targo trust` lane withholds it), no runtime check is \
                     removed, and no caller spends this verdict (docs/TCB.md \
                     `ArgumentPremiseKernelDischarge`; DECISION_QUEUE {decision})"
                ),
                notes: Vec::new(),
            },
        });
    }
    notes
}
