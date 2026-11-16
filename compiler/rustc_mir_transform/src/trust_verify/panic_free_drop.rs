//! Trust §5 step 6 (verified-sysroot plan, `docs/design/2026-08-19-verified-sysroot-scoping.md`)
//! — the ATTRIBUTE SURFACE of opt-in `Drop` panic-freedom for user trait objects.
//!
//! The plan of record, quoted:
//!
//! > `#[trust::panic_free_drop]` on a **user's own** trait, C-FLOW where the
//! > coercion is bundle-local, C-UNIVERSAL-with-cross-crate-receipt only if
//! > steps 4-5 have demonstrated the receipt machinery works. Blanket Φ on
//! > `core::ops::Drop::drop` is rejected: it turns every `impl Drop` in the
//! > dependency graph into a hard error.
//!
//! This module is deliberately the SKELETON of that step: the attribute is
//! recognized and its PLACEMENT is validated, and it charges NOTHING. Before
//! this module existed, `#[trust::panic_free_drop]` on any item compiled clean
//! with zero diagnostics (measured, stage1 2026-08-30) — the silent-reads-as-
//! enforced defect every contract fixture header warns about. Recognition
//! without enforcement must therefore be LOUD: acceptance emits a warning that
//! names the attribute inert, and every misplacement is a hard error carrying
//! the fix (the D3 rule: a refusal must enumerate repairs, because the reader
//! is an AI programmer).
//!
//! ## What is validated today
//!
//! * **Accepted** — a trait DEFINITION in this crate. The declaration site is
//!   forced by the same quantifier inversion as `#[trust::panic_free]` (Φ):
//!   a crate cannot write `impl T for X` without naming `T`, and cannot name
//!   `T` without loading `T`'s metadata, which carries the contract. Accepted
//!   means INERT: a warning says so, and nothing anywhere may rely on it.
//! * **Refused, `impl Drop`** — the blanket-`Drop` shape §4.3 rejected. Φ-style
//!   inheritance on `core::ops::Drop::drop` would conscript every `impl Drop`
//!   in the dependency graph into a hard per-impl discharge error (§(b) is a
//!   hard error by design). The refusal names the affordable variant.
//! * **Refused, any other impl** — an impl-site opt-in cannot support reliance:
//!   a call site would have to re-derive "every impl opted in", the enumeration
//!   problem the definition-site rule exists to remove. A FOREIGN trait gets
//!   the ownership reason: only the crate that owns a trait definition can make
//!   every downstream impl inherit the obligation.
//! * **Refused, everything else** (trait method, free fn, ADT, …) — the
//!   contract governs the drop glue of a `dyn Trait` OBJECT, so only a trait
//!   definition can carry it.
//!
//! ## Implementation map — what fills this skeleton, and what it waits on
//!
//! Anchors are by NAME; line numbers drift under concurrent lanes.
//!
//! 1. **Needs step 3 (pointer-provenance model) — the C-FLOW half.** Today a
//!    user-body `Unsize` coercion is refused by `is_modeled_identity_cast`
//!    (`crates/trust-vcgen/src/lib.rs`): "pointer cast changes or depends on
//!    fat-pointer metadata/provenance". Until that models fat pointers, no user
//!    body can even HOLD a `dyn` value (§4.2 Blocker 2), so there is no
//!    coercion to enumerate and nothing for this attribute to certify. Once it
//!    lands: `DynDispatchFacts::observe_bundle_body`
//!    (`trust_verify/dyn_dispatch_reliance.rs`) already enumerates bundle-local
//!    `Unsize` coercions per trait with the poison discipline; the drop case
//!    split additionally needs a `Ty::Dynamic` arm in `is_trivially_no_drop_ty`
//!    and `is_panic_free_drop_node_shallow` (`crates/trust-ir-bridge/src/lower.rs`,
//!    §4.2 Blocker 3), wired so each enumerated `Self`'s drop glue must hold an
//!    INDEPENDENT proved verdict — the "bundled-but-unproved may NOT serve the
//!    case split" rule in `dyn_dispatch_reliance`'s module doc applies verbatim.
//! 2. **Needs step 5's rehearsal — the charge seam.** The contract form (a
//!    receiver whose coercion is NOT bundle-local) must publish a
//!    `contract:panic-free-drop` row as conditional evidence (`Outcome::
//!    Skipped`), charge the relying caller a `PanicFreedom` row in NO demotion
//!    allowlist (`transport_row_is_unproved_assumption_panic` must not absorb
//!    it), and block `register_proven_panic_free` so the conditional verdict
//!    never leaks into the interprocedural registry — the three properties that
//!    made the coroutine-resume premise a contract rather than an assumption
//!    (§4.1), plus its anti-vacuity belt (per-case PROVED marker rows, never an
//!    aggregate). Step 5 (`GlobalAlloc::dealloc`) is the small-scale rehearsal
//!    of exactly that machinery; those seams live in `trust_verify.rs` and are
//!    owned by the step-5 lane today — this module must not touch them.
//! 3. **C-UNIVERSAL needs step 4's receipt.** For reliance without a bundle-
//!    local coercion the impl set must be closed: Φ's gate is local trait +
//!    whole-program artifact (`crate_types_are_whole_program`). The cross-crate
//!    variant — a DEPENDENCY's impl of the user's contracted trait — requires
//!    the upstream §(b) discharge to arrive as an rmeta-carried, authenticated
//!    receipt (§4.2 Blocker 1: "today's Φ has no cross-crate receipt"). Step
//!    4's separately-named verification lane + ratchet is where that receipt
//!    machinery is demonstrated; per the plan, C-UNIVERSAL here is admissible
//!    "only if steps 4-5 have demonstrated the receipt machinery works".
//!
//! Until item 1 lands, the ONLY behavior this attribute has is the placement
//! validation below. Fail-closed is preserved by construction: drop-glue
//! obligations for `dyn` objects keep failing closed exactly as if the
//! attribute were absent.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_ast::attr::AttributeExt;
use rustc_attr_ir::lang_items::LangItem;
use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use rustc_span::def_id::DefId;

/// The tool-attribute spelling. `#[trust::panic_free_drop]`.
pub(crate) const PANIC_FREE_DROP: &str = "panic_free_drop";

/// Does this def carry `#[trust::panic_free_drop]` DIRECTLY?
///
/// Deliberately NOT the ancestor-walking `item_has_trust_attr`, for the same
/// reason `trait_panic_free::carries_panic_free_attr` is not: the attribute
/// will create proof obligations for every impl of the annotated trait, so
/// inheriting it from an enclosing module or crate would silently conscript
/// traits their author never annotated.
fn carries_panic_free_drop_attr(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !super::attrs_queryable(tcx, def_id) {
        return false;
    }
    #[allow(deprecated)]
    tcx.get_all_attrs(def_id).iter().any(|attr| {
        matches!(
            attr.path().as_slice(),
            [tool, name] if tool.as_str() == "trust" && name.as_str() == PANIC_FREE_DROP
        )
    })
}

fn item_span(tcx: TyCtxt<'_>, def_id: DefId) -> Span {
    tcx.def_ident_span(def_id).unwrap_or_else(|| tcx.def_span(def_id))
}

/// The one fix that is always on the table, worded once so every refusal
/// enumerates the same repair (D3).
const DECLARE_ON_OWN_TRAIT_HELP: &str = "declare `#[trust::panic_free_drop]` on a trait THIS crate owns (`trait MyTrait { .. }`) and \
     hold the value as `Box<dyn MyTrait>`/`&dyn MyTrait`; the contract then charges only the \
     author who asked for it, and every impl of that trait inherits the obligation at the point \
     it is written";

/// Placement validation for `#[trust::panic_free_drop]` — the whole of step 6
/// that exists today. Charges nothing; see the module doc.
///
/// Runs from `trust_ensure_whole_crate_verification` beside
/// `trait_panic_free::discharge_trait_panic_free_contracts`, so it is active
/// exactly when verification is (`-Ztrust-verify=off` keeps the vanilla
/// tool-attribute behavior, matching `#[trust::panic_free]`).
pub(crate) fn validate_panic_free_drop_declarations(tcx: TyCtxt<'_>) {
    for local in tcx.hir_crate_items(()).definitions() {
        let def_id = local.to_def_id();
        if !carries_panic_free_drop_attr(tcx, def_id) {
            continue;
        }
        let span = item_span(tcx, def_id);
        match tcx.def_kind(def_id) {
            // ---- Accepted: a trait definition in this crate. Loudly inert. --
            DefKind::Trait => {
                let mut diag = tcx.dcx().struct_span_warn(
                    span,
                    "Trust: `#[trust::panic_free_drop]` is recognized but NOT YET ENFORCED: it \
                     verifies nothing, charges no caller, and no verdict may rely on it",
                );
                diag.note(
                    "drop-glue obligations for `dyn` objects of this trait keep failing closed \
                     exactly as if the attribute were absent; enforcement is step 6 of the \
                     verified-sysroot plan and is gated on the pointer-provenance model (step 3) \
                     that lets a user body hold a `dyn` value at all",
                );
                diag.emit();
            }
            // ---- Refused: the blanket-`Drop` shape §4.3 rejected. ----------
            DefKind::Impl { of_trait: true }
                if tcx.is_lang_item(tcx.impl_trait_id(def_id), LangItem::Drop) =>
            {
                let mut diag = tcx.dcx().struct_span_err(
                    span,
                    "Trust: `#[trust::panic_free_drop]` may not target `core::ops::Drop`",
                );
                diag.note(
                    "a blanket `Drop` panic-freedom contract inherits onto every `impl Drop` in \
                     the dependency graph, and a non-discharging impl is a hard error by design \
                     — hundreds of impls in code nobody here wrote; the verified-sysroot plan \
                     rejects that shape outright (§4.3)",
                );
                diag.help(DECLARE_ON_OWN_TRAIT_HELP);
                diag.help(
                    "if the object is built and dropped inside one function, no contract is \
                     needed at all: bundle-local coercion enumeration (C-FLOW) is the certificate \
                     for that shape once fat-pointer coercions are modeled",
                );
                diag.emit();
            }
            // ---- Refused: any other impl (foreign or local trait). ---------
            DefKind::Impl { of_trait } => {
                let mut diag = tcx.dcx().struct_span_err(
                    span,
                    "Trust: `#[trust::panic_free_drop]` must be declared on a trait DEFINITION, \
                     not an implementation",
                );
                if of_trait {
                    let trait_def_id = tcx.impl_trait_id(def_id);
                    let trait_path = trust_mir_extract::safe_def_path_str(tcx, trait_def_id);
                    if trait_def_id.is_local() {
                        diag.note(
                            "an implementation-site opt-in cannot support reliance: a call site \
                             would have to enumerate every implementation to know they all opted \
                             in; declaring on the definition inverts that quantifier",
                        );
                        diag.help(format!(
                            "move the attribute onto `trait {trait_path}`, which is defined in \
                             this crate; every implementation then inherits the obligation at \
                             the point it is written"
                        ));
                    } else {
                        diag.note(format!(
                            "`{trait_path}` is defined in another crate ({}); only the crate \
                             that owns a trait definition can declare its drop contract, because \
                             the declaration must ride the trait's own metadata so every \
                             downstream implementation inherits it",
                            tcx.crate_name(trait_def_id.krate),
                        ));
                        diag.help(DECLARE_ON_OWN_TRAIT_HELP);
                    }
                } else {
                    diag.note(
                        "found on an inherent impl; the contract governs the drop glue of a \
                         `dyn Trait` object, so only a trait definition can carry it",
                    );
                    diag.help(DECLARE_ON_OWN_TRAIT_HELP);
                }
                diag.emit();
            }
            // ---- Refused: everything else. ---------------------------------
            other => {
                let mut diag = tcx.dcx().struct_span_err(
                    span,
                    "Trust: `#[trust::panic_free_drop]` must be declared on a trait definition \
                     owned by this crate",
                );
                diag.note(format!(
                    "found on {} {}; the contract governs the drop glue of a `dyn Trait` object \
                     — a per-method panic-freedom contract is `#[trust::panic_free]` on a trait \
                     method definition instead",
                    other.article(),
                    other.descr(def_id),
                ));
                diag.help(DECLARE_ON_OWN_TRAIT_HELP);
                diag.emit();
            }
        }
    }
}
