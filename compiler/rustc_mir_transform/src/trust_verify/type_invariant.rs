//! Trust (TINV steps 5 and 9, 2026-10-06): the compiler side of the inferred
//! type-invariant lane (`docs/design/2026-10-04-type-invariant-tinv.md` §2 P0-P2,
//! P5, P7; §3 G1-G16; §6 steps 5, 6, 9).
//!
//! * [`compute_invariant_candidate_types`] (step 5) decides which local structs are
//!   CANDIDATES, from `TyCtxt` alone: the type gates G1 (privacy), G1b-a (the name
//!   the extractor renders is owned by one local ADT), G4 (deep `Freeze`), G10
//!   (no interposable method), G12 (no type or const generics) and disjointness from
//!   the backing lane, and the crate-wide gates G2 (`forbid(unsafe_code)` plus a HIR
//!   scan of every body and item), G11 (no def-site macro) and P0 (no
//!   `#[trust::skip]`/`#[trust::assume_total]`). A candidate is then SEALED in the
//!   escape census (`SealedRole::TypeInvariant`, step 6b: D1-D5 on top of the
//!   shared denials).
//! * [`trust_init_type_invariant_certificates`] (step 9) mints, over the complete
//!   body inventory `trust_init_backing_certificates` extracts: the extractor
//!   cross-check (G1b-b), the UNTRUSTED candidate synthesis
//!   (`trust_vcgen::type_invariant::candidate::synthesize`), the Houdini fixpoint
//!   with `trust_certify::certify_vc` restricted to Clean-CIC evidence (and replayed)
//!   as the only mint, and a SAT-MODEL gate on the surviving invariant itself.
//!
//! AUTHORITY. Step 9 publishes the certificates into `CrateVerificationState` and
//! NOTHING reads them to assume anything: no VC, summary, hypothesis or proof
//! authority row consumes a certificate until step 10's use-site lane and its TCB
//! row. Step 10.0 also builds the run's USE SET ([`TinvMinted::use_set`]) from the
//! same outcome; step 10.5 installs `Arc::clone` of the stored set into the session's
//! callee-summary context ([`installable_use_set`], [`installed_use_set_is_live`]). The
//! whole lane is opt-in (the tracked `-Ztrust-tinv`, which
//! replaced the untracked `TRUST_TINV=1` env read of decision TINV-10 at step 10.0):
//! with the flag unset nothing here runs and the compilation is unchanged.
//!
//! PUBLICATION IS ALL-OR-NOTHING PER RUN (step 10.0, decision TINV-22): if the ∧I
//! gate fails for ANY certificate, nothing from the run is published. Houdini's rows
//! are one simultaneous induction over the alive set, so a subset would not break
//! the induction; the reason is that an ∧I failure (a construction-site constant
//! witness violating a kernel-certified conjunct, or an unsatisfiable conjunction) is
//! evidence that the run's certified rows are unfaithful to the program (an extractor
//! gap), and then no row of that run is trusted.

use std::sync::Arc;

use rustc_abi::FieldIdx;
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap};
use rustc_hir::def::DefKind;
use rustc_hir::intravisit::{self, Visitor};
use rustc_middle::mir::{self, Body};
use rustc_middle::ty::{self, Ty, TyCtxt, TypingEnv};
use rustc_span::def_id::DefId;
use rustc_span::{Span, Symbol, sym};
use trust_types::{CalleeIdentity, Formula, VerifiableFunction, VerificationCondition};
use trust_vcgen::type_invariant::candidate::{self, CandidateSet, FieldShape, FieldValuation};
use trust_vcgen::type_invariant::houdini::{
    self, TinvBody, TinvBudget, TinvModel, TinvModelValue, TinvOracle, TypeInvariantCertificate,
};
use trust_vcgen::type_invariant::unwind::SysrootExactModels;
use trust_vcgen::type_invariant::{Sigma, TinvBodyFacts, TinvType, TinvUseSet};

use super::{PreparedDiagnostic, PreparedDiagnosticChild, PreparedLocatedDiagnostic};
use super::backing_escape_census::{Census, SealedType};

/// The certificate type the state holds: evidence is kernel-checked `CleanCic` only.
pub(super) type TinvCertificate = TypeInvariantCertificate<trust_ir::ProofEvidence>;

/// One candidate type: the name the extractor renders for it (the key every row,
/// conjunct and certificate uses) and its fields in declaration order.
pub(super) struct TinvCandidate {
    pub(super) name: String,
    pub(super) fields: Vec<(Symbol, FieldIdx)>,
}

/// A refusal at a gate: the type, the gate, what failed, and what would repair it
/// (design P7). A crate-wide gate is reported on every candidate it refuses.
pub(super) struct TinvGateNote {
    pub(super) def_id: DefId,
    pub(super) gate: &'static str,
    pub(super) text: String,
    pub(super) repair: &'static str,
}

impl TinvGateNote {
    fn render(&self) -> String {
        format!("withheld at {}: {}; repair: {}", self.gate, self.text, self.repair)
    }
}

/// What the inventory loop records beside each extracted body, from THE SAME rustc
/// `&Body` it extracted (step 9 (d)).
pub(super) struct InventoryMeta {
    pub(super) def_id: DefId,
    /// `Some(i)` for the `i`-th promoted body of `def_id`.
    pub(super) promoted: Option<usize>,
    pub(super) facts: TinvBodyFacts,
    /// Per candidate: the rustc `Rvalue::Aggregate(Adt S)` count of the body.
    pub(super) aggregates: FxHashMap<DefId, usize>,
    /// Per rustc local (by index): the candidates the census says its type reaches.
    pub(super) reaching_locals: Vec<(usize, Vec<DefId>)>,
}

/// The pre-pass's published result.
#[derive(Default)]
pub(super) struct TinvMinted {
    pub(super) certificates: FxHashMap<DefId, Arc<TinvCertificate>>,
    /// Per type, sorted by the type's rendered name: the notes (design P7).
    pub(super) notes: Vec<(DefId, Vec<String>)>,
    /// Step 10.0: what a use site of this run may assume — built from the SAME Houdini
    /// outcome the certificates came from, over exactly the published certificates.
    /// `None` when nothing was published. STORED ONLY: step 10.5 installs it.
    pub(super) use_set: Option<Arc<TinvUseSet>>,
    /// Step 10.7: the rendered disclosure line of every published `(type, conjunct)`
    /// (`assumes type_invariant(S)#k `text` [certificate provenance]`), built beside the
    /// use set from the same certificates; empty when nothing was published.
    pub(super) disclosures: std::collections::BTreeMap<(String, u32), String>,
}

/// Step 10.7: the one rendering of a published premise: the label
/// ([`trust_types::type_invariant_assumes_label`]), the conjunct's text, and the
/// certificate it comes from (its Clean-kernel-checked row count and arm lemmas).
pub(super) fn render_type_invariant_disclosure(
    def_path: &str,
    conjunct: u32,
    text: &str,
    certified_rows: usize,
    lemma_summary: &str,
) -> String {
    format!(
        "{} `{text}` [certificate: this crate's TINV Houdini induction, {certified_rows} row(s) \
         re-checked by the Clean kernel, {lemma_summary}]",
        trust_types::type_invariant_assumes_label(def_path, conjunct),
    )
}

/// Step 10.0 (decision TINV-22): the run-level ∧I verdict. `verdicts` holds, per
/// certificate of one Houdini run, its ∧I gate result; the run publishes only when every
/// one passed. Otherwise the first failure is returned, and nothing is published.
pub(super) fn run_level_and_i_gate<K>(
    verdicts: &[(K, Result<(), String>)],
) -> Result<(), (&K, &str)> {
    match verdicts.iter().find_map(|(k, r)| r.as_ref().err().map(|why| (k, why.as_str()))) {
        Some(failed) => Err(failed),
        None => Ok(()),
    }
}

// ---------------------------------------------------------------------------------
// Step 5: candidate types
// ---------------------------------------------------------------------------------

/// Bounds of the deep-`Freeze` walk (G4); exhausting either refuses the type.
const FREEZE_DEPTH: u32 = 24;
const FREEZE_NODES: usize = 4096;

/// The local structs that are TINV candidates, keyed by `DefId` in HIR order, and a
/// note for every struct a gate refused. `backing` is the sealed backing set: a
/// struct in both lanes is refused for TINV (disjointness).
pub(super) fn compute_invariant_candidate_types(
    tcx: TyCtxt<'_>,
    backing: &FxIndexMap<DefId, SealedType>,
) -> (FxIndexMap<DefId, TinvCandidate>, Vec<TinvGateNote>) {
    let items = tcx.hir_crate_items(());
    let mut notes: Vec<TinvGateNote> = Vec::new();

    // G1b-a: the extractor names a value of `S` by this string alone, so any other
    // local ADT that renders to the same string would have its constructions and
    // writes attributed to `S`. Counted over EVERY local struct, enum and union.
    let mut rendered: FxHashMap<String, usize> = FxHashMap::default();
    for item in items.free_items() {
        let did = item.owner_id.to_def_id();
        if matches!(tcx.def_kind(did), DefKind::Struct | DefKind::Enum | DefKind::Union) {
            *rendered
                .entry(trust_mir_extract::sysroot_authenticated_def_path_str(tcx, did))
                .or_default() += 1;
        }
    }

    let mut candidates: FxIndexMap<DefId, TinvCandidate> = FxIndexMap::default();
    for item in items.free_items() {
        let did = item.owner_id.to_def_id();
        if !matches!(tcx.def_kind(did), DefKind::Struct) {
            continue;
        }
        let name = trust_mir_extract::sysroot_authenticated_def_path_str(tcx, did);
        let mut refuse = |gate, text: String, repair| {
            notes.push(TinvGateNote { def_id: did, gate, text, repair });
        };
        if tcx.generics_of(did).requires_monomorphization(tcx) {
            refuse(
                "G12",
                "it has type or const generic parameters (v1 covers monomorphic structs)".into(),
                "make the struct monomorphic",
            );
            continue;
        }
        if backing.contains_key(&did) {
            refuse(
                "disjointness",
                "it is a sealed `#[trust::backing]` struct, certified by the backing lane".into(),
                "none: the backing certificate covers it",
            );
            continue;
        }
        let variant = tcx.adt_def(did).non_enum_variant();
        if let Some(field) = variant.fields.iter().find(|f| f.vis.is_public()) {
            refuse(
                "G1",
                format!("field `{}` is `pub`, so code outside this crate can write it", field.name),
                "make every field private or `pub(crate)`",
            );
            continue;
        }
        if rendered.get(&name).copied().unwrap_or(0) != 1 {
            refuse(
                "G1b",
                format!("another local type also renders as `{name}`"),
                "rename one of the types",
            );
            continue;
        }
        if let Err(why) = deep_freeze(tcx, did) {
            refuse("G4", why, "remove the interior mutability, `&mut`, raw pointer or `dyn` field");
            continue;
        }
        let fields = variant.fields.iter_enumerated().map(|(i, f)| (f.name, i)).collect();
        candidates.insert(did, TinvCandidate { name, fields });
    }

    // G10: a method of `S` whose symbol can be interposed at link time need not be
    // the body a call runs.
    for &local in tcx.mir_keys(()) {
        let did = local.to_def_id();
        if !matches!(tcx.def_kind(did), DefKind::AssocFn) {
            continue;
        }
        let Some(impl_did) = tcx.impl_of_assoc(did) else { continue };
        let self_ty = tcx.type_of(impl_did).instantiate_identity().skip_normalization();
        let Some(adt) = self_ty.ty_adt_def() else { continue };
        if candidates.contains_key(&adt.did()) && super::body_summary_identity_refused(tcx, did) {
            candidates.shift_remove(&adt.did());
            notes.push(TinvGateNote {
                def_id: adt.did(),
                gate: "G10",
                text: format!(
                    "its method `{}` is exported, interposable or not an ordinary local body",
                    tcx.def_path_str(did)
                ),
                repair: "remove `#[no_mangle]`/`#[export_name]`/`#[linkage]` from its methods",
            });
        }
    }

    // Crate-wide gates: each refuses every candidate.
    let mut crate_wide: Vec<(&'static str, String, &'static str)> = Vec::new();
    if super::crate_defines_def_site_macro(tcx) {
        crate_wide.push((
            "G11",
            "the crate defines a def-site-hygienic (`macro` 2.0) macro, which can name private \
             fields from another crate"
                .into(),
            "replace the `macro` item with `macro_rules!`",
        ));
    }
    let unsafe_level = tcx
        .lint_level_spec_at_node(rustc_lint_defs::builtin::UNSAFE_CODE, rustc_hir::CRATE_HIR_ID)
        .level();
    if unsafe_level != rustc_lint_defs::Level::Forbid {
        crate_wide.push((
            "G2a",
            format!(
                "`unsafe_code` is `{}` at the crate root, not `forbid` (after `--cap-lints`)",
                unsafe_level.as_str()
            ),
            "add `#![forbid(unsafe_code)]` to the crate root",
        ));
    }
    if let Some(why) = unsafe_outside_sysroot_macros(tcx) {
        crate_wide.push(("G2b", why, "remove the `unsafe` (or the macro that emits it)"));
    }
    for &local in tcx.mir_keys(()) {
        let did = local.to_def_id();
        let skip = super::item_has_trust_skip_attr(tcx, did);
        if skip || super::item_has_trust_attr(tcx, did, "assume_total") {
            crate_wide.push((
                "P0",
                format!(
                    "`{}` carries `#[trust::{}]`, so a body of the crate is not checked",
                    tcx.def_path_str(did),
                    if skip { "skip" } else { "assume_total" }
                ),
                "remove the attribute",
            ));
            break;
        }
    }
    if !crate_wide.is_empty() {
        for (did, _) in candidates.drain(..) {
            for (gate, text, repair) in &crate_wide {
                notes.push(TinvGateNote { def_id: did, gate, text: text.clone(), repair });
            }
        }
    }
    (candidates, notes)
}

/// G4: `S` has no interior mutability at any depth reachable by ownership or a
/// shared reference, and no `&mut`, raw pointer, `NonNull`, `dyn`, parameter,
/// foreign type or unnormalizable alias. Every ADT's type arguments are walked
/// (this refuses `Rc<RefCell<..>>` and, conservatively, `PhantomData<Cell<..>>`);
/// a local ADT's fields too. The walk is bounded; exhausting it refuses.
fn deep_freeze<'tcx>(tcx: TyCtxt<'tcx>, did: DefId) -> Result<(), String> {
    let env = TypingEnv::post_analysis(tcx, did);
    let args = ty::GenericArgs::identity_for_item(tcx, did);
    let mut stack: Vec<(Ty<'tcx>, u32)> =
        tcx.adt_def(did).all_fields().map(|f| (f.ty(tcx, args).skip_normalization(), 0)).collect();
    let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
    while let Some((ty, depth)) = stack.pop() {
        if depth > FREEZE_DEPTH || seen.len() > FREEZE_NODES {
            return Err("the deep-`Freeze` walk ran out of fuel".into());
        }
        let ty = tcx
            .try_normalize_erasing_regions(env, ty::Unnormalized::new(ty))
            .map_err(|_| format!("`{ty}` does not normalize"))?;
        if !seen.insert(ty) {
            continue;
        }
        if !ty.is_freeze(tcx, env) {
            return Err(format!("`{ty}` is not `Freeze` (interior mutability)"));
        }
        let next = depth + 1;
        match *ty.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::FnDef(..)
            | ty::FnPtr(..) => {}
            ty::Ref(_, inner, ty::Mutability::Not) => stack.push((inner, next)),
            ty::Ref(_, _, ty::Mutability::Mut) => {
                return Err(format!("`{ty}` is a mutable reference"));
            }
            ty::RawPtr(..) => return Err(format!("`{ty}` is a raw pointer")),
            ty::Adt(adt, _)
                if tcx.is_lang_item(adt.did(), rustc_attr_ir::lang_items::LangItem::NonNull) =>
            {
                return Err(format!("`{ty}` is a raw pointer"));
            }
            ty::Adt(adt, adt_args) => {
                stack.extend(adt_args.types().map(|t| (t, next)));
                if adt.did().is_local() {
                    stack.extend(
                        adt.all_fields().map(|f| (f.ty(tcx, adt_args).skip_normalization(), next)),
                    );
                }
            }
            ty::Tuple(tys) => stack.extend(tys.iter().map(|t| (t, next))),
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => stack.push((inner, next)),
            ty::Dynamic(..) => return Err(format!("`{ty}` is a trait object")),
            _ => return Err(format!("`{ty}` is a type the walk does not classify")),
        }
    }
    Ok(())
}

/// Whether `span` comes from a macro defined in the authenticated sysroot.
fn from_sysroot_macro(tcx: TyCtxt<'_>, span: Span) -> bool {
    span.ctxt()
        .outer_expn_data()
        .macro_def_id
        .is_some_and(|def| trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def))
}

/// G2b: the first `unsafe` this crate's HIR holds outside a sysroot expansion, or
/// `None`. `unsafe_code` is an early lint that is not `report_in_external_macro`,
/// so `forbid` (G2a) misses `unsafe` emitted by a THIRD-PARTY `macro_rules!` or
/// proc macro (a derive emitting `unsafe impl`); this walks every HIR body and
/// every item instead.
///
/// * An `unsafe` block is admitted only when the compiler generated it inside a
///   desugaring or a sysroot macro (`format_args!`, the builtin derives — no source
///   syntax can produce a `CompilerGenerated` block), or the user-provided block is
///   inside a sysroot macro marked `#[allow_internal_unsafe]`.
/// * An `unsafe impl`, `unsafe trait`, `unsafe fn`, `extern` block or `global_asm!`
///   item is refused unless its span is a sysroot macro's.
/// * A Clean-origin body has no HIR body, and `unsafe` is unrepresentable in its
///   emission (`def_uses_unsafe_source_impl`), so it is skipped.
fn unsafe_outside_sysroot_macros(tcx: TyCtxt<'_>) -> Option<String> {
    struct Finder<'tcx> {
        tcx: TyCtxt<'tcx>,
        found: Option<Span>,
    }
    impl<'v> Visitor<'v> for Finder<'_> {
        fn visit_block(&mut self, block: &'v rustc_hir::Block<'v>) {
            if self.found.is_none()
                && let rustc_hir::BlockCheckMode::UnsafeBlock(source) = block.rules
            {
                let admitted = match source {
                    rustc_hir::UnsafeSource::CompilerGenerated => {
                        block.span.desugaring_kind().is_some()
                            || from_sysroot_macro(self.tcx, block.span)
                    }
                    rustc_hir::UnsafeSource::UserProvided => {
                        block.span.allows_unsafe() && from_sysroot_macro(self.tcx, block.span)
                    }
                };
                if !admitted {
                    self.found = Some(block.span);
                }
            }
            intravisit::walk_block(self, block);
        }
    }
    for owner in tcx.hir_body_owners() {
        if crate::clean_origin_mir::is_clean_origin(tcx, owner) {
            continue;
        }
        let mut finder = Finder { tcx, found: None };
        finder.visit_body(tcx.hir_body_owned_by(owner));
        if finder.found.is_some() {
            return Some(format!(
                "`{}` holds an `unsafe` block outside a sysroot macro",
                tcx.def_path_str(owner.to_def_id())
            ));
        }
    }
    let items = tcx.hir_crate_items(());
    let unsafe_item = |did: DefId| -> Option<&'static str> {
        if from_sysroot_macro(tcx, tcx.def_span(did)) {
            return None;
        }
        match tcx.def_kind(did) {
            DefKind::Impl { of_trait: true }
                if matches!(tcx.impl_trait_header(did).safety, rustc_hir::Safety::Unsafe) =>
            {
                Some("an `unsafe impl`")
            }
            DefKind::Trait if matches!(tcx.trait_def(did).safety, rustc_hir::Safety::Unsafe) => {
                Some("an `unsafe trait`")
            }
            DefKind::Fn | DefKind::AssocFn
                if matches!(
                    tcx.fn_sig(did)
                        .instantiate_identity()
                        .skip_normalization()
                        .skip_binder()
                        .safety(),
                    rustc_hir::Safety::Unsafe
                ) =>
            {
                Some("an `unsafe fn`")
            }
            DefKind::ForeignMod => Some("an `extern` block"),
            DefKind::GlobalAsm => match tcx.hir_expect_item(did.expect_local()).kind {
                rustc_hir::ItemKind::CleanIsland { .. } => None,
                _ => Some("`global_asm!`"),
            },
            _ => None,
        }
    };
    let dids = items
        .free_items()
        .map(|i| i.owner_id.to_def_id())
        .chain(items.impl_items().map(|i| i.owner_id.to_def_id()))
        .chain(items.trait_items().map(|i| i.owner_id.to_def_id()))
        .chain(items.foreign_items().map(|i| i.owner_id.to_def_id()));
    for did in dids {
        if tcx.is_foreign_item(did) {
            return Some(format!("the foreign item `{}` is declared", tcx.def_path_str(did)));
        }
        if let Some(what) = unsafe_item(did) {
            return Some(format!("{what} is declared at `{}`", tcx.def_path_str(did)));
        }
    }
    None
}

// ---------------------------------------------------------------------------------
// Step 9: the inventory metadata
// ---------------------------------------------------------------------------------

/// The metadata of one inventoried body, from the rustc `body` that was extracted.
pub(super) fn inventory_meta<'tcx>(
    body: &Body<'tcx>,
    def_id: DefId,
    promoted: Option<usize>,
    candidates: &FxIndexMap<DefId, TinvCandidate>,
    census: Option<&mut Census<'_, 'tcx>>,
) -> InventoryMeta {
    let mut facts = TinvBodyFacts { block_count: body.basic_blocks.len(), ..Default::default() };
    let mut aggregates: FxHashMap<DefId, usize> = FxHashMap::default();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let id = trust_types::BlockId(bb.as_usize());
        if data.is_cleanup {
            facts.cleanup_blocks.insert(id);
        }
        if let mir::TerminatorKind::Drop { replace: true, .. } = data.terminator().kind {
            facts.replace_drops.insert(id);
        }
        for stmt in &data.statements {
            if let mir::StatementKind::Assign(assign) = &stmt.kind
                && let mir::Rvalue::Aggregate(kind, _) = &assign.1
                && let mir::AggregateKind::Adt(did, ..) = **kind
                && candidates.contains_key(&did)
            {
                *aggregates.entry(did).or_default() += 1;
            }
        }
    }
    let mut reaching_locals = Vec::new();
    if let Some(census) = census {
        for (local, decl) in body.local_decls.iter_enumerated() {
            let reached = census.tinv_reached(decl.ty);
            if !reached.is_empty() {
                reaching_locals.push((local.as_usize(), reached));
            }
        }
        // Decision TINV-32: by candidate NAME, the key synthesis and the mint read.
        facts.constants_may_hold = constants_reached(body, census).map(|dids| {
            dids.iter().filter_map(|did| candidates.get(did)).map(|c| c.name.clone()).collect()
        });
    }
    InventoryMeta { def_id, promoted, facts, aggregates, reaching_locals }
}

/// Decision TINV-32: the union, over EVERY constant operand of `body` (statements,
/// terminators, call arguments, casts, intrinsics, switch discriminants, debug info), of
/// the candidates its rustc type may hold; `None` as soon as one constant is no evidence
/// ([`Census::tinv_const_reached`]). Whole-body granularity on purpose: the extracted
/// statement indices can drift from rustc's (`with_tail_calls_expanded`), so per-site
/// evidence could clear the wrong operand.
fn constants_reached<'tcx>(body: &Body<'tcx>, census: &mut Census<'_, 'tcx>) -> Option<Vec<DefId>> {
    struct Consts<'b, 'c, 'a, 'tcx> {
        body: &'b Body<'tcx>,
        census: &'c mut Census<'a, 'tcx>,
        reached: Option<FxHashSet<DefId>>,
    }
    impl<'b, 'c, 'a, 'tcx> mir::visit::Visitor<'tcx> for Consts<'b, 'c, 'a, 'tcx> {
        fn visit_const_operand(&mut self, c: &mir::ConstOperand<'tcx>, _: mir::Location) {
            let Some(set) = self.reached.as_mut() else { return };
            match self.census.tinv_const_reached(self.body, c.ty()) {
                Some(dids) => set.extend(dids),
                None => self.reached = None,
            }
        }
    }
    let mut v = Consts { body, census, reached: Some(FxHashSet::default()) };
    mir::visit::Visitor::visit_body(&mut v, body);
    // Sorted before it is returned.
    #[allow(rustc::potential_query_instability)]
    let mut out: Vec<DefId> = v.reached?.into_iter().collect();
    out.sort_by_key(|did| (did.krate.as_u32(), did.index.as_u32()));
    Some(out)
}

/// Decision TINV-33: per TINV candidate, `(dyn, param)` — whether no `dyn`, and no type
/// parameter of a polymorphic body, of this crate can reach a value of it. Read from a
/// FINISHED census ([`Census::tinv_opaque_reach`]), and only for a candidate that is
/// crate-private (no effective visibility outside the crate: no downstream code can name
/// it, so only this crate's bodies and the code they hand it to can erase it into a `dyn`
/// or instantiate a parameter with it), that no effectively public ADT of the crate
/// reaches through its fields (downstream code could hold that wrapper and erase it), and
/// that no opaque type of the crate may hide
/// (an `impl Trait` whose hidden type reaches it, or whose hidden type the census walk
/// cannot see through, would let downstream code erase it unseen).
pub(super) fn opaque_reach_evidence<'tcx>(
    tcx: TyCtxt<'tcx>,
    candidates: &FxIndexMap<DefId, TinvCandidate>,
    census: &mut Census<'_, 'tcx>,
) -> FxHashMap<DefId, (bool, bool)> {
    use rustc_middle::middle::privacy::Level;
    let visibilities = tcx.effective_visibilities(());
    // Every candidate an opaque type of the crate may hide; `None`: any of them.
    let mut hidden: Option<FxHashSet<DefId>> = Some(FxHashSet::default());
    for opaque in tcx.hir_crate_items(()).opaques() {
        let hidden_ty = tcx.type_of(opaque).instantiate_identity().skip_normalization();
        match census.tinv_reached_closed(opaque.to_def_id(), hidden_ty) {
            Some(reached) => {
                if let Some(set) = hidden.as_mut() {
                    set.extend(reached);
                }
            }
            None => hidden = None,
        }
    }
    // Every candidate an effectively public ADT of the crate reaches through its fields:
    // downstream code can hold that ADT and erase it into a `dyn` this crate later sees.
    let mut exposed: FxHashSet<DefId> = FxHashSet::default();
    for item in tcx.hir_crate_items(()).free_items() {
        let local = item.owner_id.def_id;
        if !matches!(tcx.def_kind(local), DefKind::Struct | DefKind::Enum | DefKind::Union)
            || !visibilities.is_public_at_level(local, Level::ReachableThroughImplTrait)
        {
            continue;
        }
        let adt_ty = tcx.type_of(local).instantiate_identity().skip_normalization();
        exposed.extend(census.tinv_reached(adt_ty));
    }
    let mut out = FxHashMap::default();
    for did in candidates.keys() {
        let private = did.as_local().is_some_and(|local| {
            !visibilities.is_public_at_level(local, Level::ReachableThroughImplTrait)
        });
        let unhidden =
            hidden.as_ref().is_some_and(|set| !set.contains(did)) && !exposed.contains(did);
        let (dyn_clear, param_clear) = census.tinv_opaque_reach(*did);
        let ok = private && unhidden && dyn_clear;
        out.insert(*did, (ok, ok && param_clear));
    }
    out
}

// ---------------------------------------------------------------------------------
// Step 9: the mint
// ---------------------------------------------------------------------------------

/// The in-process ay router as Houdini's oracle: a FILTER, never authority.
///
/// `VcKind::TypeInvariant` is not an in-process ay kind (its `can_handle` lists the
/// L0 kinds), so each question is asked as an `Assertion` of the SAME formula, as
/// the vcgen tests do; the kind does not change what the formula says.
struct AyOracle {
    router: trust_router::Router,
    /// Trust (T3 L4, C07p; design D-VC-1): the run's own VC context. Every probe the
    /// oracle is asked is interned into it through the row oracle before it is solved; it
    /// drops with the oracle, and its count is the run's `PARITY crate:tinv` row. Behind a
    /// lock because the oracle answers through `&self`.
    rows: std::sync::Mutex<trust_types::vc_context::VcContext>,
}

impl AyOracle {
    fn solve(&self, vc: &VerificationCondition) -> trust_types::VerificationResult {
        // Interned before it is solved, and solved as asked; the lock is released here. The
        // plan asks a probe that fans out to intern before it fans out: this keeps the
        // walk's row order only while Houdini asks one probe at a time. A parallel walk
        // interns its probes before it fans them out (L4-C07p-4).
        trust_vcgen::intern_eager_rows(
            &mut self.rows.lock().unwrap_or_else(std::sync::PoisonError::into_inner),
            std::iter::once(vc),
        );
        let asked = VerificationCondition {
            kind: trust_types::VcKind::Assertion { message: "tinv houdini oracle".into() },
            function: vc.function,
            location: vc.location.clone(),
            formula: vc.formula.clone(),
            contract_metadata: None,
            obligation: None,
        };
        self.router.verify_one(&asked)
    }
}

/// Trust (T3 L4, C07p): the row oracle's count over the run's probes (`AyOracle::rows`),
/// as one `PARITY crate:tinv` row per oracle.
fn record_probe_parity(tcx: TyCtxt<'_>, oracle: &AyOracle) {
    let mut parity = trust_types::vc_context::ParityTally::default();
    parity.fold(&oracle.rows.lock().unwrap_or_else(std::sync::PoisonError::into_inner));
    super::elide_audit::record_crate_parity(
        tcx,
        "crate:tinv",
        &parity,
        &[trust_types::vc_context::Oracle::Row],
    );
}

/// Houdini's reading of a verdict (TINV-16): `Proved` holds; only a `Failed` WITH a
/// counterexample refutes; a `Failed` without one (a fallback), `Unknown`,
/// `Timeout` and anything else is unknown.
fn oracle_verdict(result: &trust_types::VerificationResult) -> Option<bool> {
    match result {
        trust_types::VerificationResult::Proved { .. } => Some(true),
        trust_types::VerificationResult::Failed { counterexample: Some(_), .. } => Some(false),
        _ => None,
    }
}

/// The counterexample of a refuted result as a [`TinvModel`]: `Int` and `Bool`
/// bindings only; any other value is left out, so a formula reading it is not
/// confirmed by the ground evaluator.
fn oracle_model(result: &trust_types::VerificationResult) -> Option<TinvModel> {
    let trust_types::VerificationResult::Failed { counterexample: Some(cex), .. } = result else {
        return None;
    };
    Some(
        cex.assignments
            .iter()
            .filter_map(|(name, value)| {
                let value = match value {
                    trust_types::CounterexampleValue::Int(i) => TinvModelValue::Int(*i),
                    trust_types::CounterexampleValue::Bool(b) => TinvModelValue::Bool(*b),
                    _ => return None,
                };
                Some((name.clone(), value))
            })
            .collect(),
    )
}

impl TinvOracle for AyOracle {
    fn proves(&self, vc: &VerificationCondition) -> Option<bool> {
        oracle_verdict(&self.solve(vc))
    }

    fn model(&self, vc: &VerificationCondition) -> Option<TinvModel> {
        oracle_model(&self.solve(vc))
    }
}

/// Whether dropping a value of `ty` may run user code (the M/Drop points, G8). Only
/// the extraction-certified drop-totality stamp (`AdtAuth::TotalDrop`, written from
/// `TyCtxt` by `tcx_drop_is_total` and `#[serde(skip)]`) or a type that owns nothing
/// answers `false`. `TotalStdMap`, an absent stamp, and every other type answer
/// `true` (fail closed).
fn may_run_user_drop(ty: &trust_types::Ty) -> bool {
    use trust_types::{AdtAuth, Ty as T};
    match ty {
        T::Bool
        | T::Int { .. }
        | T::PtrSizedInt { .. }
        | T::Char
        | T::Float { .. }
        | T::Str
        | T::Bv(_)
        | T::Unit
        | T::Never
        | T::Ref { .. }
        | T::RawPtr { .. }
        | T::FnDef { .. }
        | T::FnPtr { .. } => false,
        T::Tuple(tys) => tys.iter().any(may_run_user_drop),
        T::Array { elem, .. } => may_run_user_drop(elem),
        T::Seq { drop_auth: Some(AdtAuth::TotalDrop(_)), .. } => false,
        T::Adt { arbitrary_precision: Some(AdtAuth::TotalDrop(_)), .. } => false,
        _ => true,
    }
}

/// The re-keyed `def_path` of the `index`-th promoted body of `parent`. Injective
/// (one parent path, one index), and never a path rustc renders for an item: `{` is
/// not an identifier character, and the extractor renders no `promoted#` segment.
fn promoted_key(parent: &str, index: usize) -> String {
    format!("{parent}::{{promoted#{index}}}")
}

/// The Houdini walk budget: every non-final round drops at least one conjunct or
/// refuses at least one type, and so does every failed mint pass, so the rounds are
/// at most `2·Σconjuncts + #types + 1`; one more is allowed, times one walk per body.
fn walk_budget(bodies: usize, conjuncts: usize, types: usize) -> u32 {
    let rounds = conjuncts.saturating_mul(2).saturating_add(types).saturating_add(2);
    u32::try_from(bodies.saturating_mul(rounds)).unwrap_or(u32::MAX)
}

/// The placeholder name the non-vacuity gate gives field term `t`.
fn gate_var(prefix: &str, i: usize) -> Formula {
    Formula::var_owned(format!("tinv_gate_{prefix}{i}"), trust_types::Sort::Int)
}

/// THE ∧I GATE (non-vacuity of the invariant itself). At step 10 the conjunction of
/// the surviving conjuncts is ASSUMED at entry, so an unsatisfiable one would make
/// every use-site row vacuous. The oracle must return a MODEL of
/// `∧surviving ∧ range(shapes)`, and that model is re-checked here with no solver
/// trust: it must be complete and in range, and the exact evaluator
/// (`candidate::eval`) must give `Some(true)` for every surviving conjunct. Every
/// construction-site constant witness must also satisfy every surviving conjunct.
fn invariant_has_checked_model(
    oracle: &AyOracle,
    set: &CandidateSet,
    cert: &TinvCertificate,
) -> Result<(), String> {
    let n = set.shapes.len();
    let mut sigma = Sigma { value: vec![None; n], len: vec![None; n] };
    let mut parts: Vec<Formula> = Vec::new();
    for (i, shape) in set.shapes.iter().enumerate() {
        match shape {
            FieldShape::Int { min, max } => {
                let v = gate_var("v", i);
                parts.push(Formula::Le(Box::new(Formula::Int(*min)), Box::new(v.clone())));
                if let Some(max) = max {
                    parts.push(Formula::Le(Box::new(v.clone()), Box::new(Formula::Int(*max))));
                }
                sigma.value[i] = Some(v);
            }
            FieldShape::Len(_) => {
                let l = gate_var("l", i);
                parts.push(Formula::Le(Box::new(Formula::Int(0)), Box::new(l.clone())));
                sigma.len[i] = Some(l);
            }
            FieldShape::Bool | FieldShape::NoTerm => {}
        }
    }
    for c in cert.conjuncts() {
        let Some(f) = trust_vcgen::type_invariant::instantiate(c, &sigma) else {
            return Err(format!("conjunct #{} does not instantiate over the field ranges", c.id));
        };
        parts.push(f);
    }
    let vc = VerificationCondition {
        kind: trust_types::VcKind::Assertion { message: "tinv invariant satisfiability".into() },
        function: trust_types::Symbol::intern(cert.def_path()),
        location: trust_types::SourceSpan::default(),
        formula: Formula::And(parts),
        contract_metadata: None,
        obligation: None,
    };
    let Some(model) = oracle_model(&oracle.router.verify_one(&vc)) else {
        return Err("the oracle returned no model of the surviving invariant".into());
    };
    let int = |name: String| match model.get(&name) {
        Some(TinvModelValue::Int(i)) => Some(*i),
        _ => None,
    };
    let mut valuation = FieldValuation { value: vec![None; n], len: vec![None; n] };
    for i in 0..n {
        if sigma.value[i].is_some() {
            valuation.value[i] = int(format!("tinv_gate_v{i}"));
        }
        if sigma.len[i].is_some() {
            valuation.len[i] = int(format!("tinv_gate_l{i}"));
        }
    }
    if !valuation.is_complete_and_in_range(&set.shapes) {
        return Err("the oracle's model is incomplete or out of range".into());
    }
    for c in cert.conjuncts() {
        if candidate::eval(&c.formula, &valuation) != Some(true) {
            return Err(format!("the oracle's model does not satisfy conjunct #{}", c.id));
        }
        for (site, witness) in &set.const_witnesses {
            if candidate::eval(&c.formula, witness) != Some(true) {
                return Err(format!(
                    "conjunct #{} is false at the constant construction in `{}`",
                    c.id, site.function
                ));
            }
        }
    }
    Ok(())
}

/// Under `-Ztrust-dump=mir:<dir>` (and `-Ztrust-tinv`, which is what runs the mint),
/// write the EXACT bodies Houdini walks, re-keyed, with their identities, to
/// `<dir>/tinv-inventory.json`: a JSON array of `{ "identity", "func" }` sorted by
/// `def_path`. The ordinary per-function dump is the TrustVerify pass input, a later
/// MIR than the `mir_drops_elaborated_and_const_checked` bodies inventoried here and
/// without the promoted bodies, so vcgen's real-MIR TINV fixtures are captured from
/// this file instead (`trust-vcgen/src/type_invariant/p1_realmir_tests.rs`). Evidence
/// only: nothing reads it back.
fn dump_inventory(
    tcx: TyCtxt<'_>,
    bodies: &[VerifiableFunction],
    identities: &[Option<CalleeIdentity>],
) {
    let Some(dir) = tcx.sess.opts.unstable_opts.trust_dump.mir.as_deref() else { return };
    let mut rows: Vec<serde_json::Value> = bodies
        .iter()
        .zip(identities)
        .map(|(func, identity)| serde_json::json!({ "identity": identity, "func": func }))
        .collect();
    rows.sort_by(|a, b| a["func"]["def_path"].as_str().cmp(&b["func"]["def_path"].as_str()));
    let written = std::fs::create_dir_all(dir).and_then(|()| {
        let json = serde_json::to_string_pretty(&rows).map_err(std::io::Error::other)?;
        std::fs::write(dir.join("tinv-inventory.json"), json)
    });
    if let Err(error) = written {
        tcx.dcx().fatal(format!(
            "failed to write the TINV inventory dump to `{}`: {error}",
            dir.display()
        ));
    }
}

/// The mint (design §6 step 9; modelled on `inferred_return::mint_inferred_returns`).
/// `funcs`/`meta` are the complete inventory and its parallel metadata;
/// `complete` is the inventory's completeness AND the scan/body/meta parity;
/// `denied` holds the census denials of TINV types. `use_set_visible` is whether a TINV
/// use set is already visible in the session's callee-summary context (step 10.0: the
/// mint must never run where its own facts could be assumed; checked at RUNTIME).
#[allow(clippy::too_many_arguments)]
pub(super) fn trust_init_type_invariant_certificates(
    tcx: TyCtxt<'_>,
    candidates: &FxIndexMap<DefId, TinvCandidate>,
    gate_notes: Vec<TinvGateNote>,
    funcs: &[VerifiableFunction],
    meta: &[InventoryMeta],
    complete: bool,
    denied: &FxIndexMap<DefId, Vec<String>>,
    opaque: &FxHashMap<DefId, (bool, bool)>,
    use_set_visible: bool,
) -> TinvMinted {
    let mut notes: FxIndexMap<DefId, Vec<String>> = FxIndexMap::default();
    for note in gate_notes {
        notes.entry(note.def_id).or_default().push(note.render());
    }
    let mut out = TinvMinted::default();
    let finish = |notes: FxIndexMap<DefId, Vec<String>>, mut out: TinvMinted| {
        let mut sorted: Vec<(String, DefId, Vec<String>)> = notes
            .into_iter()
            .map(|(did, n)| {
                (trust_mir_extract::sysroot_authenticated_def_path_str(tcx, did), did, n)
            })
            .collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        out.notes = sorted.into_iter().map(|(_, did, n)| (did, n)).collect();
        out
    };

    // (0) Step 10.0: no use set may be visible while the mint runs (circularity: a
    // row of the induction must never assume the invariant through a use-site fact).
    // A runtime check, not a `debug_assert!`; vcgen's `houdini` checks it again on
    // its own thread-local context.
    if use_set_visible {
        for did in candidates.keys() {
            notes.entry(*did).or_default().push(
                "withheld: a type-invariant use set is already visible in the callee-summary \
                 context, so the mint would run under its own facts; repair: none at the type \
                 (a compiler ordering defect)"
                    .into(),
            );
        }
        return finish(notes, out);
    }

    // (1) The inventory gate (G1 completeness).
    if !complete || funcs.len() != meta.len() {
        for did in candidates.keys() {
            notes.entry(*did).or_default().push(format!(
                "withheld at G1: the body inventory is incomplete or its census and metadata \
                 are not parallel to it ({} bodies, {} metadata); repair: none at the type",
                funcs.len(),
                meta.len()
            ));
        }
        return finish(notes, out);
    }

    // (2) The census (G3, D1-D5).
    let mut alive: FxIndexMap<DefId, &TinvCandidate> = FxIndexMap::default();
    for (did, cand) in candidates {
        if let Some(reasons) = denied.get(did) {
            let entry = notes.entry(*did).or_default();
            for reason in reasons {
                entry.push(format!(
                    "withheld by the escape census: {reason}; repair: remove the escape path"
                ));
            }
        } else {
            alive.insert(*did, cand);
        }
    }
    if alive.is_empty() {
        return finish(notes, out);
    }

    // (3) The bodies: promoted bodies re-keyed, identities from `TyCtxt` (TINV-11).
    let mut bodies: Vec<VerifiableFunction> = funcs.to_vec();
    let mut identities: Vec<Option<CalleeIdentity>> = Vec::with_capacity(meta.len());
    for (func, m) in bodies.iter_mut().zip(meta) {
        if let Some(index) = m.promoted {
            func.def_path = promoted_key(&func.def_path, index);
        }
        let callable =
            matches!(tcx.def_kind(m.def_id), DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(..));
        identities.push(
            if m.promoted.is_some()
                || !callable
                || super::body_summary_identity_refused(tcx, m.def_id)
            {
                None
            } else {
                trust_mir_extract::item_identity(tcx, m.def_id)
            },
        );
    }

    dump_inventory(tcx, &bodies, &identities);

    // (4) G1b-b: the extraction agrees with rustc on every construction of `S`, and
    // on every local whose type reaches `S`.
    let mut cross_refused: FxHashSet<DefId> = FxHashSet::default();
    for (func, m) in bodies.iter().zip(meta) {
        for (did, cand) in &alive {
            if cross_refused.contains(did) {
                continue;
            }
            let rustc_count = m.aggregates.get(did).copied().unwrap_or(0);
            let why = match candidate::construction_sites(func, &cand.name) {
                Ok(sites) if sites.len() != rustc_count => Some(format!(
                    "rustc counts {rustc_count} construction(s) in `{}`, the extraction {}",
                    func.def_path,
                    sites.len()
                )),
                // A refusal here is synthesis's to report.
                _ => None,
            }
            .or_else(|| {
                m.reaching_locals.iter().find_map(|(local, reached)| {
                    if !reached.contains(did) {
                        return None;
                    }
                    let extracted = func.body.locals.iter().find(|l| l.index == *local);
                    let reaches = extracted.map(|l| {
                        trust_vcgen::place_write::type_reaches(
                            &l.ty,
                            &cand.name,
                            &func.body.datatype_defs,
                        )
                    });
                    (reaches.is_none() || reaches == Some(trust_vcgen::place_write::Reach::No))
                        .then(|| {
                            format!(
                                "local _{local} of `{}` reaches it in rustc but not in the extraction",
                                func.def_path
                            )
                        })
                })
            });
            if let Some(why) = why {
                cross_refused.insert(*did);
                notes.entry(*did).or_default().push(format!(
                    "withheld at G1b: {why}; repair: none at the type (an extractor gap)"
                ));
            }
        }
    }

    // (5) The UNTRUSTED candidate synthesis. Decision TINV-32: per body, whether the
    // census proves that no constant of the body can hold the candidate (the evidence
    // that clears an opaque constant for it; `None` keeps every constant refusing).
    // Parallel to `bodies`: gate (1) refused the run unless `funcs.len() == meta.len()`.
    let mut sets: FxIndexMap<DefId, CandidateSet> = FxIndexMap::default();
    for (did, cand) in &alive {
        if cross_refused.contains(did) {
            continue;
        }
        let constants_clear: Vec<bool> =
            meta.iter().map(|m| m.facts.constants_clear(&cand.name)).collect();
        match candidate::synthesize_with_constant_evidence(&cand.name, &bodies, &constants_clear) {
            Err(refusal) => {
                notes.entry(*did).or_default().push(format!(
                    "withheld at synthesis: {refusal:?}; repair: construct it with a struct \
                     literal in an ordinary body"
                ));
            }
            Ok(set) => {
                let agrees = set.ty.fields.len() == cand.fields.len()
                    && set
                        .ty
                        .fields
                        .iter()
                        .zip(&cand.fields)
                        .all(|((n, _), (s, _))| n == s.as_str());
                if !agrees {
                    notes.entry(*did).or_default().push(
                        "withheld at G1b: the extracted fields differ from rustc's (names or \
                         order); repair: none at the type (an extractor gap)"
                            .into(),
                    );
                } else if set.ty.conjuncts.is_empty() {
                    notes.entry(*did).or_default().push(
                        "no candidate conjunct: the templates found nothing to propose".into(),
                    );
                } else {
                    let described = candidate::describe(&set);
                    let listed: Vec<String> =
                        described.iter().map(|(id, text)| format!("#{id} `{text}`")).collect();
                    notes
                        .entry(*did)
                        .or_default()
                        .push(format!("candidate conjuncts (untrusted): {}", listed.join(", ")));
                    sets.insert(*did, set);
                }
            }
        }
    }
    if sets.is_empty() {
        return finish(notes, out);
    }

    // (6) Houdini, with the certify mint.
    let types: Vec<TinvType> = sets.values().map(|s| s.ty.clone()).collect();
    // Decision TINV-33: every body's facts carry the crate-wide `dyn`/parameter evidence
    // for the synthesized candidates (by name, the key the mint reads).
    let (dyn_unreachable, param_unreachable) = {
        let mut d = std::collections::BTreeSet::new();
        let mut p = std::collections::BTreeSet::new();
        for (did, set) in &sets {
            if let Some(&(dyn_clear, param_clear)) = opaque.get(did) {
                if dyn_clear {
                    d.insert(set.ty.def_path.clone());
                    if param_clear {
                        p.insert(set.ty.def_path.clone());
                    }
                }
            }
        }
        (d, p)
    };
    let facts: Vec<TinvBodyFacts> = meta
        .iter()
        .map(|m| TinvBodyFacts {
            dyn_unreachable: dyn_unreachable.clone(),
            param_unreachable: param_unreachable.clone(),
            ..m.facts.clone()
        })
        .collect();
    let tinv_bodies: Vec<TinvBody<'_>> = bodies
        .iter()
        .zip(&facts)
        .zip(&identities)
        .map(|((func, f), identity)| TinvBody { identity: *identity, func, facts: Some(f) })
        .collect();
    let oracle = AyOracle {
        router: trust_router::Router::deterministic_in_process_ay(
            super::vc_timeout_ms(tcx.sess),
            super::effort_scale(tcx.sess),
        ),
        rows: std::sync::Mutex::new(trust_types::vc_context::VcContext::new()),
    };
    let certify = |vc: &VerificationCondition| {
        let evidence = trust_certify::certify_vc(vc)?;
        (matches!(evidence, trust_ir::ProofEvidence::CleanCic { .. })
            && trust_certify::replay_vc_evidence(vc, &evidence))
        .then_some(evidence)
    };
    let conjuncts: usize = types.iter().map(|t| t.conjuncts.len()).sum();
    let budget = TinvBudget {
        steps_per_walk: tcx.sess.opts.unstable_opts.trust_verify_function_budget_steps,
        total_walks: walk_budget(tinv_bodies.len(), conjuncts, types.len()),
    };
    let outcome = houdini::houdini(
        &types,
        &tinv_bodies,
        &SysrootExactModels,
        &may_run_user_drop,
        &oracle,
        &certify,
        budget,
    );
    let by_name: FxHashMap<&str, DefId> =
        sets.iter().map(|(did, set)| (set.ty.def_path.as_str(), *did)).collect();
    for note in &outcome.notes {
        if let Some(did) = by_name.get(note.ty.as_str()) {
            notes.entry(*did).or_default().push(note.text.clone());
        }
    }

    // (7) The ∧I gate, ALL-OR-NOTHING per run (step 10.0, decision TINV-22), then
    // publication. A certificate whose type is not a synthesized candidate is an
    // inconsistent outcome and fails the run the same way.
    let verdicts: Vec<(String, Result<(), String>)> = outcome
        .certificates
        .iter()
        .map(|(name, cert)| {
            let verdict = match by_name.get(name.as_str()) {
                Some(did) => invariant_has_checked_model(&oracle, &sets[did], cert),
                None => Err("the certificate names no synthesized candidate".into()),
            };
            (name.clone(), verdict)
        })
        .collect();
    // Trust (T3 L4, C07p): every probe of the run has been asked; the row oracle's count
    // over them is one crate-level PARITY row.
    record_probe_parity(tcx, &oracle);
    let gate = run_level_and_i_gate(&verdicts).map_err(|(n, why)| (n.clone(), why.to_owned()));
    // The use set is built from the SAME outcome, over exactly the certificates about to
    // be published; a refusal there withholds the whole run too.
    let use_set = match &gate {
        Ok(()) if !outcome.certificates.is_empty() => {
            match TinvUseSet::from_outcome(&outcome, |name| by_name.contains_key(name)) {
                Ok(set) => Ok(Some(Arc::new(set))),
                Err(refusal) => Err(format!("the use set refused the run: {refusal:?}")),
            }
        }
        Ok(()) => Ok(None),
        Err(_) => Ok(None),
    };
    match (gate, use_set) {
        (Err((failed, why)), _) => {
            for (name, verdict) in &verdicts {
                let Some(&did) = by_name.get(name.as_str()) else { continue };
                let text = match verdict {
                    Err(own) => format!(
                        "withheld at the invariant satisfiability gate: {own}; repair: none at \
                         the type"
                    ),
                    _ => format!(
                        "withheld: run-level ∧I failure on `{failed}` ({why}): a certified \
                         conjunct is violated by a construction witness or the conjunction is \
                         unsatisfiable, so the run's certified rows are suspect (TINV-22); \
                         repair: none at the type"
                    ),
                };
                notes.entry(did).or_default().push(text);
            }
        }
        (Ok(()), Err(why)) => {
            for name in outcome.certificates.keys() {
                if let Some(&did) = by_name.get(name.as_str()) {
                    notes.entry(did).or_default().push(format!("withheld: {why}"));
                }
            }
        }
        (Ok(()), Ok(use_set)) => {
            for (name, cert) in outcome.certificates {
                let Some(&did) = by_name.get(name.as_str()) else { continue };
                let set = &sets[&did];
                let described = candidate::describe(set);
                let conjuncts: Vec<String> = cert
                    .conjuncts()
                    .iter()
                    .map(|c| {
                        format!(
                            "#{} `{}`",
                            c.id,
                            described.get(&c.id).cloned().unwrap_or_else(|| "?".into())
                        )
                    })
                    .collect();
                // Trust (TINV-21): the arm lemmas the rows assumed travel with the
                // certificate; the note names them (a row's evidence is valid only under them).
                notes.entry(did).or_default().push(format!(
                    "certified: {} ({} kernel-certified row(s), {})",
                    conjuncts.join(", "),
                    cert.rows().len(),
                    cert.lemma_summary()
                ));
                // Step 10.7: the disclosure line of each published conjunct.
                if use_set.is_some() {
                    for c in cert.conjuncts() {
                        out.disclosures.insert(
                            (name.clone(), c.id),
                            render_type_invariant_disclosure(
                                &name,
                                c.id,
                                described.get(&c.id).map_or("?", String::as_str),
                                cert.rows().len(),
                                &cert.lemma_summary(),
                            ),
                        );
                    }
                }
                out.certificates.insert(did, Arc::new(cert));
            }
            out.use_set = use_set;
        }
    }
    finish(notes, out)
}

// ---------------------------------------------------------------------------------
// Step 10.5: installing the use set
// ---------------------------------------------------------------------------------

/// Step 10.5: the use set to INSTALL in the callee-summary context: `Arc::clone` of the
/// run's published set when `-Ztrust-tinv` is on, else nothing. Never a copy: the grading
/// accepts tags only against the stored allocation ([`installed_use_set_is_live`]).
pub(super) fn installable_use_set(
    enabled: bool,
    published: Option<&Arc<TinvUseSet>>,
) -> Option<Arc<TinvUseSet>> {
    if !enabled {
        return None;
    }
    published.map(Arc::clone)
}

/// Step 10.5 (LIVENESS, KNOWN_HAZARDS 10.5 (a)): whether the installed set is the stored
/// published one — the SAME allocation. Nothing installed is trivially live; a set
/// installed with nothing stored, or a rebuilt or deep-cloned set, is not (its facts
/// would be conjoined and then every tagged row refused).
pub(super) fn installed_use_set_is_live<T>(
    installed: Option<&Arc<T>>,
    stored: Option<&Arc<T>>,
) -> bool {
    match (installed, stored) {
        (None, _) => true,
        (Some(installed), Some(stored)) => Arc::ptr_eq(installed, stored),
        (Some(_), None) => false,
    }
}

// ---------------------------------------------------------------------------------
// Step 10.4: grading a row that carries a type-invariant premise
// ---------------------------------------------------------------------------------

/// Step 10.4: what grading reads about the TINV premises of ONE body's rows — the record
/// of every row a use-site fact was conjoined into during the body's CONSUMED generation
/// (`trust_vcgen::type_invariant::with_tinv_assumed_rows_scope`, passed down with
/// `solver_vcs` as a local), and the tags of the set that generation drew from, accepted
/// only when it is the stored published set ([`TinvRowDisclosure::for_generation`]). The
/// comparison rule is the record's: per row key, the formula's tag set must equal the
/// UNION of the recorded tag sets. Both empty, the default and the only state a real
/// compile reaches until step 10.5 installs a set: then a TAGGED row still has no
/// authority (fail closed), and every other row is graded exactly as before.
#[derive(Default, Clone)]
pub(super) struct TinvRowDisclosure {
    /// The installed use set's tag map (tag -> `(type, conjunct)`), copied off the set;
    /// `None` when no set is installed.
    published: Option<std::collections::BTreeMap<String, (String, u32)>>,
    rows: Vec<trust_vcgen::type_invariant::TinvAssumedRow>,
    /// Step 10.7: the rendered disclosure line of every published `(type, conjunct)`
    /// (`assumes type_invariant(S)#k ...`), copied off the session state together with
    /// `published`; empty whenever `published` is `None`.
    rendered: std::collections::BTreeMap<(String, u32), String>,
    /// Step 10.5 (liveness): the generation drew its facts from a set that is NOT the
    /// stored published one (a rebuilt or deep-cloned set) or from two sets. Every
    /// tagged row is then refused with a reason that names this, never silently.
    mismatched_set: bool,
}

/// Step 10.4: the TINV reading of one row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum TinvRowStatus {
    /// The row's formula carries no tag and no installed fact is recorded for it.
    Clear,
    /// The two disclosure channels AGREE on a non-empty tag set, every tag of which names
    /// a conjunct the installed use set publishes: the row may be minted
    /// `TypeInvariantComposed`, disclosing these `(type, conjunct)` premises.
    Composable(std::collections::BTreeSet<(String, u32)>),
    /// The row carries a premise that cannot be disclosed: a tag scan past its bound, a
    /// formula tag with no generation record (or the reverse: a recorded installation
    /// whose tag the formula lost), the two channels disagreeing, or a tag that names no
    /// published conjunct. No authority at all.
    Refused(&'static str),
}

impl TinvRowDisclosure {
    /// The disclosure of ONE generation (review fold-in 2/4): its own record, and the
    /// tags of the set ITS facts came from — accepted only when that set is exactly the
    /// session's stored, published use set (`type_invariant_use_set`, pointer identity)
    /// and the generation drew from no other set. Anything else leaves `published`
    /// `None`, so every tagged row of the generation is refused (fail closed).
    pub(super) fn for_generation(
        sess: &rustc_session::Session,
        record: &trust_vcgen::type_invariant::TinvGenerationRecord,
    ) -> Self {
        let (stored, rendered) = super::with_crate_verification_state(sess, |state| {
            (state.type_invariant_use_set.clone(), state.type_invariant_disclosures.clone())
        });
        Self::from_record(stored.as_ref(), record, &rendered)
    }

    /// [`Self::for_generation`] over an explicit stored set and its rendered premise lines
    /// (the pure half).
    pub(super) fn from_record(
        stored: Option<&Arc<TinvUseSet>>,
        record: &trust_vcgen::type_invariant::TinvGenerationRecord,
        rendered: &std::collections::BTreeMap<(String, u32), String>,
    ) -> Self {
        let live = match (stored, record.use_set.as_ref()) {
            (Some(stored), Some(used)) => !record.conflicting_sets && Arc::ptr_eq(stored, used),
            _ => false,
        };
        let published =
            live.then(|| record.use_set.as_ref().map(|used| used.tags().clone())).flatten();
        // Facts were drawn (a set is recorded) but not from the stored published set: a
        // liveness defect at the install point (KNOWN_HAZARDS 10.5 (a)), named, not silent.
        let mismatched_set = record.use_set.is_some() && !live;
        let rendered = if published.is_some() { rendered.clone() } else { Default::default() };
        Self { published, rows: record.rows.clone(), rendered, mismatched_set }
    }

    #[cfg(test)]
    pub(super) fn from_parts(
        published: Option<std::collections::BTreeMap<String, (String, u32)>>,
        rows: Vec<trust_vcgen::type_invariant::TinvAssumedRow>,
    ) -> Self {
        // Test rows render the bare label (no provenance), so the mint can be exercised
        // without a pre-pass.
        let rendered = published
            .iter()
            .flat_map(|tags| tags.values())
            .map(|(ty, k)| ((ty.clone(), *k), trust_types::type_invariant_assumes_label(ty, *k)))
            .collect();
        Self { published, rows, rendered, mismatched_set: false }
    }

    /// Step 10.7: the disclosure lines of `assumes`, in its order, or `None` when any
    /// premise has no rendering (then nothing is minted: fail closed).
    pub(super) fn render(
        &self,
        assumes: &std::collections::BTreeSet<(String, u32)>,
    ) -> Option<Vec<String>> {
        assumes.iter().map(|key| self.rendered.get(key).cloned()).collect()
    }

    /// Whether a use-site fact was conjoined into ANY row of the body (installation, not
    /// use: whether a solver needed the fact is irrelevant).
    pub(super) fn body_carries_premise(&self) -> bool {
        self.rows.iter().any(|row| !row.tags.is_empty())
    }

    /// The union of the recorded tags of every generation record whose key matches
    /// `vc` (`kind`, `location`), or `None` when no record matches. A key shared by rows
    /// with different tag sets makes every one of them disagree with this union (fail
    /// closed, a precision cost).
    fn side_tags(&self, vc: &VerificationCondition) -> Option<std::collections::BTreeSet<String>> {
        let mut matched = false;
        let mut tags = std::collections::BTreeSet::new();
        for row in self.rows.iter().filter(|r| r.kind == vc.kind && r.location == vc.location) {
            matched = true;
            tags.extend(row.tags.iter().cloned());
        }
        matched.then_some(tags)
    }

    /// The TINV reading of `vc` (see [`TinvRowStatus`]).
    pub(super) fn row_status(&self, vc: &VerificationCondition) -> TinvRowStatus {
        let side = self.side_tags(vc);
        match vc.type_invariant_tags() {
            trust_types::TinvTagScan::Unbounded => {
                TinvRowStatus::Refused("the tag scan passed its bound")
            }
            trust_types::TinvTagScan::None => {
                if side.is_some_and(|tags| !tags.is_empty()) {
                    TinvRowStatus::Refused(
                        "an installed type-invariant fact is recorded for the row but its formula \
                         carries no tag",
                    )
                } else {
                    TinvRowStatus::Clear
                }
            }
            trust_types::TinvTagScan::Tags(tags) => {
                let Some(side) = side else {
                    return TinvRowStatus::Refused(
                        "the formula carries a type-invariant tag with no generation record",
                    );
                };
                if side != tags {
                    return TinvRowStatus::Refused(
                        "the formula's type-invariant tags differ from the generation record",
                    );
                }
                let Some(published) = self.published.as_ref() else {
                    return TinvRowStatus::Refused(if self.mismatched_set {
                        "the generation's type-invariant facts came from a set that is not the \
                         session's stored published set (a rebuilt or deep-cloned set, or two \
                         sets)"
                    } else {
                        "no type-invariant use set is installed"
                    });
                };
                let mut assumes = std::collections::BTreeSet::new();
                for tag in &tags {
                    let Some((ty, id)) = published.get(tag).map(|(ty, id)| (ty.as_str(), *id))
                    else {
                        return TinvRowStatus::Refused(
                            "a type-invariant tag names no conjunct the use set publishes",
                        );
                    };
                    assumes.insert((ty.to_owned(), id));
                }
                if assumes.is_empty() {
                    return TinvRowStatus::Refused("an empty type-invariant tag set");
                }
                TinvRowStatus::Composable(assumes)
            }
        }
    }
}

/// Step 10.4: whether the body `def` carries a TINV premise — keyed on INSTALLATION: a
/// use-site fact was conjoined into a row of its consumed generation (recorded by
/// `DefId` right after that generation, so every instance of the item counts: an
/// over-approximation, fail closed). Such a body is never check-elided and never
/// registered as proven panic-free (TINV-27).
pub(super) fn body_carries_premise(tcx: TyCtxt<'_>, def: DefId) -> bool {
    super::with_crate_verification_state(tcx.sess, |state| {
        state.tinv_premised_verdicts.contains(&def)
    })
}

/// TINV-29 (review fold-in): `-Ztrust-policy=certify` refuses a function whose rows carry a
/// type-invariant premise, exactly as it refuses an instance hypothesis
/// (`instance_hypothesis::abort_on_instance_hypotheses`) and as `targo trust check
/// --certify` refuses the `assumed` row: a `TypeInvariantComposed` proof is conditional on
/// the crate's TINV certificate, never an all-input proof.
pub(super) fn abort_on_type_invariant_premise(tcx: TyCtxt<'_>, def: DefId, func_path: &str) {
    if let Some(prepared) = prepare_type_invariant_refusal(tcx, def, func_path) {
        prepared.emit(tcx);
    }
}

pub(super) fn prepare_type_invariant_refusal(
    tcx: TyCtxt<'_>, def: DefId, func_path: &str,
) -> Option<PreparedLocatedDiagnostic> {
    if !body_carries_premise(tcx, def) {
        return None;
    }
    Some(PreparedLocatedDiagnostic {
        span: tcx.def_span(def),
        diagnostic: PreparedDiagnostic {
            aborting: true,
            header: format!(
                "Trust certify verification failed for `{func_path}`: its rows carry a \
                 type-invariant premise (`assumes type_invariant(S)#k`) — a \
                 `TypeInvariantComposed` proof is conditional on the crate's TINV certificate, \
                 not proved for all inputs"
            ),
            children: vec![PreparedDiagnosticChild::Note(
                "under `-Ztrust-policy=certify` a type-invariant premise is fatal (TINV-29); the \
                 default lane discloses it and counts the row `Trusted`".into(),
            )],
        },
    })
}

/// TINV-29: the per-function disclosure on every non-`certify` lane (mirrors
/// `instance_hypothesis::warn_instance_hypotheses`).
pub(super) fn warn_type_invariant_premise(tcx: TyCtxt<'_>, def: DefId, func_path: &str) {
    if let Some(prepared) = prepare_type_invariant_warning(tcx, def, func_path) {
        prepared.emit(tcx);
    }
}

pub(super) fn prepare_type_invariant_warning(
    tcx: TyCtxt<'_>, def: DefId, func_path: &str,
) -> Option<PreparedLocatedDiagnostic> {
    if !body_carries_premise(tcx, def) {
        return None;
    }
    Some(PreparedLocatedDiagnostic {
        span: tcx.def_span(def),
        diagnostic: PreparedDiagnostic {
            aborting: false,
            header: format!(
                "Trust verification advisory for `{func_path}`: its rows carry a type-invariant \
                 premise — rows proved under it are `TypeInvariantComposed` (`Trusted`), \
                 conditional on the crate's TINV certificate"
            ),
            children: vec![PreparedDiagnosticChild::Note(
                "each such row discloses `assumes type_invariant(S)#k`; `-Ztrust-policy=certify` and \
                 `targo trust check --certify` refuse it".into(),
            )],
        },
    })
}

#[cfg(test)]
mod tests;
