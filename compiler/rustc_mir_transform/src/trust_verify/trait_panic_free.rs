//! Trust rung 1 of the discharge lattice: a PANIC-FREEDOM contract declared on a
//! trait method DEFINITION, inherited by every impl, discharged per impl.
//!
//! `#[trust::panic_free]` (Φ) is not a predicate over values, so it is not a
//! `Formula`, not a `ContractPredicate`, and never reaches the typed-CHC
//! obligation channel. It is a VERDICT declaration over a body's obligation
//! set: *no execution of this method's body raises a panic*. Three parts:
//!
//! * **(a) inheritance** — Φ on `T::m` binds every impl of `m`. The declaration
//!   must sit on the trait DEFINITION. That is forced, not stylistic: an
//!   impl-site opt-in would make a caller re-derive "every impl opted in",
//!   which is the enumeration problem the rule exists to remove. Declaring at
//!   the definition inverts the quantifier — a crate cannot write `impl T for X`
//!   without naming `T`, and cannot name `T` without loading `T`'s metadata,
//!   which carries Φ. The language enforces that, not Trust.
//! * **(b) discharge** — for every impl `i` of `T::m` in this crate, `D(i)` =
//!   "`i`'s body is fully verified panic-free" is an obligation reported AT THE
//!   IMPL. A crate holding a non-discharging impl does not compile, and the
//!   diagnostic names the trait method whose contract failed. A distant
//!   call-site error would be useless to the author of the body.
//! * **(c) reliance** — see `generic_call_relies_on_panic_free_contract`. Only
//!   sound when the impl set that can reach the call is closed; the gate is
//!   local trait + whole-program artifact, the `dyn_trait_sealedness` precedent.
//!
//! **Safety only, deliberately.** Φ must NOT include termination. Soundness of
//! (c) given (a)+(b) is the innermost-frame argument: a panic is raised by an
//! instruction in the innermost stack frame, Φ-reliance discharges CALL
//! obligations only, and a call instruction is not a panic instruction — so the
//! raising frame's own body proof already covered it, with no appeal to Φ. That
//! argument takes the innermost frame in one step and never inducts on call
//! depth, which is exactly why the forwarding impl `impl<T: Tr> Tr for W<T>`
//! may rely on Φ while proving Φ without circularity. It also fails outright
//! for total correctness: an infinite descent has no innermost frame. Divergence
//! satisfies a safety property vacuously, so panic-freedom survives; termination
//! would not. Termination stays with `#[trust::decreases]`, which is
//! well-founded and does not participate in reliance.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_middle::mir::trust_proof::{TrustObligationKind, TrustProofStrength, TrustStatus};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;
use rustc_span::def_id::DefId;

use super::{
    artifacts_have_unproved_assumption_panic, artifacts_spend_a_user_assumed_total_axiom,
    collect_verification_artifacts_cached_after_decision, crate_types_are_whole_program,
    item_has_trust_attr, item_has_trust_skip_attr, verdict_rests_on_user_axiom,
};

/// The tool-attribute spelling of Φ. `#[trust::panic_free]`.
pub(crate) const PANIC_FREE: &str = "panic_free";

/// Does this def carry `#[trust::panic_free]` DIRECTLY?
///
/// Deliberately NOT the ancestor-walking `item_has_trust_attr`: Φ creates a
/// proof obligation for every impl of the annotated method, so inheriting it
/// from an enclosing trait/module/crate would silently conscript items their
/// author never annotated. The attribute binds exactly the item it is written on.
fn carries_panic_free_attr(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !super::attrs_queryable(tcx, def_id) {
        return false;
    }
    #[allow(deprecated)]
    tcx.get_all_attrs(def_id).iter().any(|attr| {
        matches!(
            attr.path().as_slice(),
            [tool, name] if tool.as_str() == "trust" && name.as_str() == PANIC_FREE
        )
    })
}

/// Is `def_id` a trait-method DECLARATION that carries Φ?
///
/// Cross-crate safe: tool attributes are encoded in rmeta, so a Φ declared in a
/// dependency is visible here. Reliance is gated separately (§(c)); this
/// predicate answers only "is the obligation declared".
pub(crate) fn trait_method_declares_panic_free(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !matches!(tcx.def_kind(def_id), DefKind::AssocFn) {
        return false;
    }
    let Some(item) = tcx.opt_associated_item(def_id) else {
        return false;
    };
    // §(a): only a TRAIT-container assoc fn may declare it.
    if item.trait_container(tcx).is_none() {
        return false;
    }
    carries_panic_free_attr(tcx, def_id)
}

/// If `impl_method` implements a Φ-contracted trait method, return that trait
/// method — the inherited obligation, and the name the diagnostic must carry.
pub(crate) fn inherited_panic_free_obligation(
    tcx: TyCtxt<'_>,
    impl_method: DefId,
) -> Option<DefId> {
    let trait_method = tcx.opt_associated_item(impl_method)?.trait_item_def_id()?;
    trait_method_declares_panic_free(tcx, trait_method).then_some(trait_method)
}

/// Rendered `Trait::method` for diagnostics.
fn trait_method_path(tcx: TyCtxt<'_>, trait_method: DefId) -> String {
    trust_mir_extract::safe_def_path_str(tcx, trait_method)
}

/// Best span to hang an impl-method diagnostic on: the method's own name.
fn item_span(tcx: TyCtxt<'_>, def_id: DefId) -> Span {
    tcx.def_ident_span(def_id).unwrap_or_else(|| tcx.def_span(def_id))
}

/// Is this obligation part of the SAFETY property Φ declares?
///
/// Everything except the two liveness classes. `NonTermination` and `Liveness`
/// are deliberately excluded, and that exclusion is the load-bearing restriction
/// of the whole rule, not a convenience:
///
/// Φ's soundness argument takes the innermost frame on the stack at the moment
/// of the panic and finishes in one step. An infinite descent has NO innermost
/// frame — so if Φ promised termination, reliance-inside-discharge would become
/// circular in the bad way, and unsound. Panic-freedom survives precisely
/// because safety properties are satisfied vacuously by divergence: a program
/// that never returns also never panics.
///
/// The practical consequence is visible in the forwarding impl
/// `impl<S: Tr> Tr for W<S> { fn m(&mut self) { self.0.m() } }`. Its own
/// termination obligation is REFUTED — the verifier cannot bound a call whose
/// target is not pinned until monomorphization — while its panic freedom is
/// genuinely discharged. Demanding termination here would blame that impl for
/// failing a promise the contract never made, and would make every forwarding
/// and blanket impl unimplementable under a contract.
///
/// Termination remains the business of `#[trust::decreases]`, which is
/// well-founded and does not participate in reliance. A Φ-discharged impl may
/// diverge, and its own termination verdict is reported by its own lane —
/// unchanged, unsuppressed, and still fatal under strict policy.
fn obligation_is_safety(kind: TrustObligationKind) -> bool {
    !matches!(kind, TrustObligationKind::NonTermination | TrustObligationKind::Liveness)
}

/// `D(i)` — is this body's PANIC FREEDOM fully discharged?
///
/// FIVE conjuncts, all required. Conjunct 5 is the ASSUMPTION-ROOT gate and is the
/// only one that cannot be answered from this body's own rows; the rest read the
/// ledger. This is the ONE evidence bar for every premise lane — Φ's per-impl
/// discharge, the `dyn` C-FLOW case split, the `write_fmt` reduction and the
/// drop-glue premise all end up here — so a conjunct added anywhere else would
/// cover a subset of them.
///
/// 1. the body produced proof results AND verification artifacts. Missing
///    either means the verifier was skipped, cycled, or never ran; a contract
///    premise is never credited by default.
/// 2. the disposition arrays are aligned and the summary is genuinely derived
///    from the rows (`recompute_summary`), so a malformed or tampered result
///    cannot present itself as discharged.
/// 3. no unproved absent-callee / drop-glue `PanicFreedom` row. The aggregate
///    summary is not guaranteed to surface those (see the fail-closed backstop
///    in `report_full_verification_failure`), and Φ is the premise a `dyn` or
///    generic call site will lean on — so it is checked directly rather than
///    inherited from a summary that may fold it away.
/// 4. every SAFETY obligation (see `obligation_is_safety`) is statically
///    discharged with a real proof strength. `Trusted + None` is the
///    contract-assumed bookkeeping disposition: it preserves modular
///    verification under `requires`, but it is not an independently discharged
///    proof and must never seed a contract premise.
/// 5. the verdict does not REST ON a user-written axiom the bundle SPENT — no
///    `#[trust::assume_total]` / `#[trust::skip]` callee whose call key reached
///    the bridge's assumption sets (`verdict_rests_on_user_axiom`). Conjuncts 1-4
///    cannot see this: the axiom is consumed at bundle-lowering time and the
///    resulting ledger is byte-identical to a genuinely obligation-free body's,
///    which is MEASURED, not assumed. Absence of a census DECLINES.
///
///    Conjuncts 1-4 and conjunct 5 OVERLAP, and neither covers the other. An axiom
///    the bundle did not spend usually leaves its call site an unproved absent
///    callee that conjunct 1 refuses (MEASURED: programs Z1/Z2) — but not always: a
///    reified `fn` pointer to an axiom leaves NO row for conjunct 1 to see and no
///    key in the bridge sets, and it is conjunct 5, reading the census's
///    value-mention half, that refuses it (MEASURED: X2/X7/X8, `axiom_free=true`
///    before that half existed). `verdict_rests_on_user_axiom` lists what the
///    census covers and the one spelling MEASURED to escape it. Do not "simplify"
///    conjunct 5 away on the belief that conjuncts 1-4 already carry it.
///
/// A body with no safety rows at all is credited only when the verifier
/// demonstrably ran — it emitted some row, or the NATIVE run independently
/// reports nothing outstanding (`native_run_is_vacuously_clean`, which also
/// refuses a run whose typed-TrustIr lowering failed). That is the compiler's
/// own "genuinely obligation-free vs. never verified" test, generalized from
/// `summary.total` to the safety subset. It has to exist: a forwarding impl
/// whose only call is discharged FROM the contract emits no safety obligation
/// at all, and refusing it would make `impl<S: Tr> Tr for W<S>` unprovable —
/// the exact case §(b2) is about.
///
/// Every failure mode — unverified, skipped, cycling, missing MIR — yields an
/// `Err`. Fail-closed is the only correct default for a premise.
// `pub(crate)` for `dyn_dispatch_reliance`: C-FLOW's case split needs the SAME
// evidence bar as Φ's per-impl discharge. Re-deriving it there would let the
// two lanes drift.
pub(crate) fn body_discharges_panic_freedom(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> Result<(), String> {
    instance_discharges_panic_freedom(tcx, ty::InstanceKind::Item(def_id))
}

/// The evidence bar of [`body_discharges_panic_freedom`], for ANY `InstanceKind`
/// rather than only `Item`.
///
/// Drop glue is an `InstanceKind::DropGlue`, not an `Item`, so the structural-drop
/// lane cannot reach this bar through the `DefId` wrapper. It is the SAME function
/// so the two lanes cannot drift: hand-copying this ledger is exactly how a
/// soundness conjunct gets silently dropped.
pub(crate) fn instance_discharges_panic_freedom<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::InstanceKind<'tcx>,
) -> Result<(), String> {
    let Some(results) = tcx.trust_proof_results(instance) else {
        return Err(
            "the verifier produced no proof results for this body (it was skipped, cycled, or \
             never ran); a contract premise is never credited by default"
                .to_string(),
        );
    };
    if !results.has_aligned_obligation_arrays() || results.recompute_summary() != results.summary {
        return Err(
            "the body's proof result arrays are malformed or its summary is not derived from its \
             per-obligation rows; no premise is credited from an unreconcilable verdict"
                .to_string(),
        );
    }
    let body = tcx.instance_mir(instance);
    let Some(artifacts) = collect_verification_artifacts_cached_after_decision(tcx, body) else {
        return Err(
            "the body produced no verification artifacts, so its obligation ledger could not be \
             inspected"
                .to_string(),
        );
    };
    if artifacts_have_unproved_assumption_panic(&artifacts) {
        return Err(
            "the body carries an unproved absent-callee/drop-glue panic obligation; a call it \
             cannot prove panic-free keeps the whole body unable to discharge the contract"
                .to_string(),
        );
    }

    let mut safety_rows = 0usize;
    let mut undischarged = 0usize;
    // Name the rows that refused, not just how many. A bare count says a premise
    // failed; the kinds say WHAT would have to be proved to make it succeed, which
    // is the difference between a dead end and a work-list. This message is the
    // only view a caller gets of a body it does not own — for a dependency body it
    // is never surfaced as its own diagnostic.
    let mut blockers: Vec<String> = Vec::new();
    for disposition in results.dispositions.iter() {
        if !obligation_is_safety(disposition.kind) {
            continue;
        }
        safety_rows += 1;
        let proved = matches!(disposition.status, TrustStatus::Trusted | TrustStatus::Certified)
            && disposition.strength != TrustProofStrength::None;
        if !proved {
            undischarged += 1;
            // `TrustDisposition` carries kind/status/strength only — no description
            // (compiler/rustc_middle/src/mir/trust_proof.rs:128). The kind IS the
            // finest granularity this channel has, so `HardenedBoundary(UnsafeOperation)`
            // is as specific as a premise-query refusal can be reported. Naming the
            // exact unsafe op would mean carrying the artifact's ObligationReport
            // (which does have `description`) out of the premise path.
            let entry = format!("{:?}/{:?}", disposition.kind, disposition.status);
            if !blockers.contains(&entry) {
                blockers.push(entry);
            }
        }
    }
    if undischarged > 0 {
        // `TrustDisposition` has no description, so the kind alone cannot say WHICH
        // unsafe operation was refused. `artifacts.results` does carry it: a
        // `VcKind::HardenedBoundary { category, callee, detail }` names the callee and
        // the detail. Pull those through so a DEPENDENCY body's refusal is actionable —
        // such a body is verified as a premise query and never surfaces its own
        // diagnostic, so this string is the only channel out.
        let mut detail: Vec<String> = Vec::new();
        for (vc, _) in artifacts.results.iter() {
            if matches!(
                vc.kind,
                trust_types::VcKind::HardenedBoundary { .. } | trust_types::VcKind::UnsupportedMir { .. }
            ) {
                let d: String = format!("{:?}", vc.kind).chars().take(120).collect();
                if !detail.contains(&d) {
                    detail.push(d);
                }
            }
        }
        return Err(format!(
            "the body's panic freedom is not fully discharged: {undischarged} of {safety_rows} \
             safety obligation(s) were refuted, left unknown, or kept a runtime check [{}]{}",
            blockers.join(", "),
            if detail.is_empty() { String::new() } else { format!(" detail: {}", detail.join(" | ")) }
        ));
    }
    if safety_rows == 0
        && results.dispositions.is_empty()
        && !artifacts.full_verification.as_ref().is_some_and(super::native_run_is_vacuously_clean)
    {
        return Err(
            "the body produced no obligation rows at all and the native run did not independently \
             report a clean, fully-lowered verification; that is indistinguishable from a \
             verification that never happened"
                .to_string(),
        );
    }
    // (5) THE VERDICT MAY NOT REST ON A USER AXIOM. Conjuncts 1-4 read the body's
    // own ledger, and MEASURED on pristine main that ledger is EMPTY for exactly
    // this case: a `write_str` whose only gap is a call to a
    // `#[trust::assume_total]` callee publishes `no_obligations`/`proved`, an empty
    // disposition list, no transport rows, and a native run reporting
    // `requested_obligations: 0` — byte-identical to a genuinely obligation-free
    // body. The axiom is consumed at bundle-lowering time and leaves nothing here
    // to read, so the census is consulted instead (see
    // `verdict_rests_on_user_axiom`).
    //
    // LAST, deliberately: this whole function is what FORCES the verdict, and the
    // census is written during that forcing. Asking before the reads above would
    // decline every body. Ordering it after conjunct 4 also keeps an unproved body
    // reporting "not fully discharged" rather than the axiom reason, so a
    // falsification run can tell which conjunct fired.
    // `InstanceKind::def_id()` is the one accessor every variant carries, so the
    // structural-drop lane's resolved destructor keys the census exactly as an
    // ordinary `Item` does.
    let axiom_reason = verdict_rests_on_user_axiom(tcx.sess, instance.def_id()).or_else(|| {
        // The IN-BAND witness of the same fact: an axiom that did leave a row is
        // refused from this body's own ledger, without relying on the census.
        artifacts_spend_a_user_assumed_total_axiom(&artifacts).then_some(
            "its own ledger records a `#[trust::assume_total]` axiom being spent, so the verdict \
             is conditional on a declaration nobody proved",
        )
    });
    if let Some(reason) = axiom_reason {
        return Err(format!(
            "the body is proved only CONDITIONALLY: {reason}. A conditional verdict may not \
             discharge another body's obligation — the reduction would mint a positive discharge \
             from an axiom and the caller would end up carrying no obligation at all"
        ));
    }
    Ok(())
}

/// One impl (or default) body that inherited Φ. Emits the failure AT THE IMPL.
fn discharge_one_body(
    tcx: TyCtxt<'_>,
    body_def_id: DefId,
    trait_method: DefId,
    inherited_by_default_body: bool,
) {
    let contract = trait_method_path(tcx, trait_method);
    let span = item_span(tcx, body_def_id);

    // (b3) A skipped or assumed-total body has NO proof, so it can be the
    // innermost frame in the soundness argument and collapse it. Refuse the
    // opt-out outright — a demotion here would be the whole rule laundered.
    for opt_out in ["skip", "assume_total"] {
        let present = if opt_out == "skip" {
            item_has_trust_skip_attr(tcx, body_def_id)
        } else {
            item_has_trust_attr(tcx, body_def_id, opt_out)
        };
        if present {
            tcx.dcx()
                .struct_span_err(
                    span,
                    format!(
                        "Trust: `#[trust::{opt_out}]` cannot be applied to an implementation of \
                         `#[trust::panic_free]` trait method `{contract}`"
                    ),
                )
                .with_note(
                    "a skipped or assumed body carries no proof, so a `dyn`/generic call site \
                     relying on this trait method's contract would be relying on nothing",
                )
                .with_note(format!(
                    "prove this body, or remove `#[trust::panic_free]` from `{contract}`"
                ))
                .emit();
            return;
        }
    }

    if let Err(reason) = body_discharges_panic_freedom(tcx, body_def_id) {
        let header = if inherited_by_default_body {
            format!(
                "Trust: the default body of `#[trust::panic_free]` trait method `{contract}` is \
                 not proved panic-free"
            )
        } else {
            format!(
                "Trust: this implementation of `#[trust::panic_free]` trait method `{contract}` \
                 is not proved panic-free"
            )
        };
        let mut diag = tcx.dcx().struct_span_err(span, header);
        diag.note(reason);
        let declaration_span = item_span(tcx, trait_method);
        if declaration_span != span {
            diag.span_note(
                declaration_span,
                format!("`{contract}` declares `#[trust::panic_free]` here"),
            );
        }
        diag.note(
            "a panic-freedom contract on a trait method is inherited by EVERY implementation of \
             it, and each implementation must discharge it where its body is written — that is \
             what lets a `dyn`/generic call site rely on the contract without enumerating impls",
        );
        if inherited_by_default_body {
            diag.note(
                "an implementation that does not override this method dispatches to this default \
                 body, so the default body is itself a target the contract must cover",
            );
        }
        diag.emit();
    }
}

/// Validate a Φ DECLARATION and warn on vacuity.
fn check_declaration(tcx: TyCtxt<'_>, trait_method: DefId, impl_count: usize) {
    let contract = trait_method_path(tcx, trait_method);
    let span = item_span(tcx, trait_method);

    // v1 refuses CONDITIONAL panic-freedom. Discharging a precondition over an
    // erased receiver at a `dyn` site is unsolved, so a trait method that also
    // carries a precondition is not Φ-eligible — loudly, not silently. Checked
    // on the attribute written on THIS method (not the ancestor walk, which
    // would misread an enclosing item's annotation as this method's).
    let declares_precondition = super::attrs_queryable(tcx, trait_method) && {
        #[allow(deprecated)]
        tcx.get_all_attrs(trait_method).iter().any(|attr| {
            matches!(
                attr.path().as_slice(),
                [tool, name]
                    if tool.as_str() == "trust"
                        && matches!(name.as_str(), "requires" | "invariant")
            )
        })
    };
    if declares_precondition {
        tcx.dcx()
            .struct_span_err(
                span,
                format!(
                    "Trust: `#[trust::panic_free]` and a precondition cannot both apply to \
                     `{contract}`"
                ),
            )
            .with_note(
                "v1 refuses a CONDITIONAL panic-freedom contract: a `dyn` call site would have to \
                 discharge a predicate over a receiver whose type has been erased, which this \
                 rule does not solve",
            )
            .emit();
    }

    // Vacuity must stay visible. Zero impls is not a silent green.
    if impl_count == 0 {
        tcx.dcx()
            .struct_span_warn(
                span,
                format!(
                    "Trust: `#[trust::panic_free]` on `{contract}` is vacuous in this crate: \
                     0 implementations"
                ),
            )
            .with_note(
                "no implementation was discharged here, so nothing in this crate is evidence for \
                 the contract",
            )
            .emit();
    }
}

/// §(a)+(b): inherit every Φ declaration onto every impl in this crate, and
/// discharge each one. Runs after the whole-crate body walk, so every
/// `trust_proof_results` this reads is already computed.
pub(crate) fn discharge_trait_panic_free_contracts(tcx: TyCtxt<'_>) {
    let crate_items = tcx.hir_crate_items(());

    // ---- Enforce the DECLARATION SITE. -----------------------------------
    // Φ anywhere but a trait method definition is an error, not a no-op. An
    // impl-site or free-function Φ that silently did nothing would read to its
    // author exactly like a contract that was being enforced.
    for local in crate_items.definitions() {
        let def_id = local.to_def_id();
        if !carries_panic_free_attr(tcx, def_id) {
            continue;
        }
        if trait_method_declares_panic_free(tcx, def_id) {
            continue;
        }
        let mut diag = tcx.dcx().struct_span_err(
            item_span(tcx, def_id),
            "Trust: `#[trust::panic_free]` must be declared on a trait method DEFINITION",
        );
        if let Some(trait_method) = tcx.opt_associated_item(def_id).and_then(|i| i.trait_item_def_id())
        {
            diag.note(format!(
                "found on an implementation of `{}`; declare the contract there instead",
                trait_method_path(tcx, trait_method)
            ));
        } else {
            diag.note(
                "found on an item that is not a trait method declaration; an ordinary function's \
                 panic-freedom is already the subject of its own verification verdict",
            );
        }
        diag.note(
            "the contract is declared once, on the trait, so that every implementation anywhere \
             inherits it at the point it is written; an implementation-site opt-in cannot make a \
             `dyn` call site's reliance complete, because the call site would still have to \
             enumerate the implementations to know they all opted in",
        );
        diag.emit();
    }

    // ---- Collect the Φ trait methods this crate must discharge against. ---
    let mut contracted_methods: Vec<DefId> = Vec::new();
    for trait_item in crate_items.trait_items() {
        let def_id = trait_item.owner_id.to_def_id();
        if trait_method_declares_panic_free(tcx, def_id) {
            contracted_methods.push(def_id);
        }
    }

    // A LOCAL impl may implement a FOREIGN Φ trait method. Inheritance is not
    // limited to locally-declared traits: the obligation travels with the trait
    // in metadata, which is the whole point of declaring it at the definition.
    let mut impl_bodies: Vec<(DefId, DefId)> = Vec::new();
    for impl_item in crate_items.impl_items() {
        let def_id = impl_item.owner_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::AssocFn) {
            continue;
        }
        if let Some(trait_method) = inherited_panic_free_obligation(tcx, def_id) {
            impl_bodies.push((def_id, trait_method));
        }
    }

    // ---- (b1) Non-overriding impls dispatch to the trait default body. ----
    // Discharge it ONCE, and only when some local impl actually inherits it.
    let mut default_bodies: Vec<DefId> = Vec::new();
    let mut impl_counts: FxHashMap<DefId, usize> = FxHashMap::default();
    for &trait_method in &contracted_methods {
        let Some(trait_def_id) = tcx.opt_associated_item(trait_method).and_then(|i| i.trait_container(tcx))
        else {
            continue;
        };
        let impls = tcx.local_trait_impls(trait_def_id);
        impl_counts.insert(trait_method, impls.len());
        for impl_local in impls {
            let impl_def_id = impl_local.to_def_id();
            if tcx.impl_item_implementor_ids(impl_def_id).get(&trait_method).is_none()
                && tcx.def_kind(trait_method) == DefKind::AssocFn
                && tcx.hir_maybe_body_owned_by(trait_method.expect_local()).is_some()
            {
                default_bodies.push(trait_method);
            }
        }
    }

    for &trait_method in &contracted_methods {
        check_declaration(tcx, trait_method, impl_counts.get(&trait_method).copied().unwrap_or(0));
    }

    // ---- (b) DISCHARGE. Report at the impl, name the trait method. -------
    for (impl_method, trait_method) in impl_bodies {
        discharge_one_body(tcx, impl_method, trait_method, false);
    }
    default_bodies.sort_by_key(|def_id| (def_id.krate, def_id.index));
    default_bodies.dedup();
    for trait_method in default_bodies {
        discharge_one_body(tcx, trait_method, trait_method, true);
    }
}

/// §(c) RELIANCE for a statically-unresolvable `<S as T>::m` (`S` a type
/// parameter, `Instance::try_resolve` = `Ok(None)`).
///
/// Sound iff the impl set that can reach this call is CLOSED under the
/// discharge enforced above. The gate:
///
/// * `T::m` carries Φ, so every impl of it was written against a trait whose
///   metadata declares the obligation; and
/// * `T` is LOCAL, so the enforcement in `discharge_trait_panic_free_contracts`
///   ran over the crate that owns the trait, and no dependency could have
///   supplied an impl (an impl needs the trait, and the trait is defined here);
///   and
/// * this artifact is WHOLE-PROGRAM, so no crate compiled later can add an impl.
///
/// The last two are the `dyn_trait_sealedness` U6 route, reused verbatim rather
/// than reinvented. An rlib fails this gate today and keeps its obligation:
/// closing that needs the per-crate discharge seal plus the deferred
/// link-closure obligation, which is not built here and must not be assumed.
///
/// UNLIKE rung 2 this does NOT enumerate the impls at the call site, and it
/// therefore accepts blanket and generic impls — each of those discharged
/// polymorphically at its own definition, which is exactly what makes the
/// forwarding impl `impl<S: T> T for W<S>` provable at all.
pub(crate) fn generic_call_relies_on_panic_free_contract(
    tcx: TyCtxt<'_>,
    callee_def_id: DefId,
) -> bool {
    if !trait_method_declares_panic_free(tcx, callee_def_id) {
        return false;
    }
    let Some(trait_def_id) = tcx.trait_of_assoc(callee_def_id) else {
        return false;
    };
    // Completeness: only a locally-declared trait has had EVERY impl that can
    // exist checked by this compilation.
    if !trait_def_id.is_local() {
        return false;
    }
    if !crate_types_are_whole_program(tcx) {
        return false;
    }
    // Completeness, specialization: with a specializing `default fn` in an IMPL
    // the body that runs is not necessarily the impl method
    // `impl_item_implementor_ids` names, so the discharge above does not cover
    // the dispatch target. Refuse rather than reason about the specialization
    // graph. Cheap: only reached for a trait that declares the contract.
    //
    // Note the asymmetry: `defaultness` on a TRAIT item is
    // `Default { has_value }` for every provided method — it means "has a
    // default body", NOT "is specializable" — so checking it there would refuse
    // every contract. Only the impl side carries the specialization meaning.
    for impl_local in tcx.local_trait_impls(trait_def_id) {
        let impl_def_id = impl_local.to_def_id();
        if let Some(&impl_method) =
            tcx.impl_item_implementor_ids(impl_def_id).get(&callee_def_id)
            && tcx.defaultness(impl_method).is_default()
        {
            return false;
        }
    }
    true
}
