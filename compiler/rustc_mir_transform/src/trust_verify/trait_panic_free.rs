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
//!   A FOREIGN trait (D4 increment B) is closed by enumeration instead:
//!   `foreign_trait_closure` re-derives every foreign impl in a whole-program
//!   artifact, generic call shape only.
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

use rustc_ast::attr::AttributeExt;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::mir::trust_proof::{TrustObligationKind, TrustProofStrength, TrustStatus};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;
use rustc_span::def_id::DefId;

use super::{
    PremiseArtifacts, collect_premise_artifacts_cached, crate_types_are_whole_program,
    item_has_trust_attr, item_has_trust_skip_attr, transport_rows_have_unproved_assumption_panic,
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
    // Trust (TINV, 2026-10-05): `TypeInvariant` deliberately stays on the safety side,
    // fail-closed: an undischarged TINV row withholds D(i). Step 7 decided that a dropped
    // Houdini conjunct is a note, never a row (TINV-9(c)), and since step 7.7 the kernel
    // kind gate admits a situated TINV row; no TINV row reaches this pass until step 9
    // wires the pre-pass into the compiler.
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
pub(crate) fn body_discharges_panic_freedom(tcx: TyCtxt<'_>, def_id: DefId) -> Result<(), String> {
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
    instance_discharges_panic_freedom_modulo(tcx, instance, &NoExcuse)
}

/// Trust (D1 increment 1, 2026-09-25): which unproved rows a caller of the evidence
/// bar may EXCUSE. The absolute bar passes [`NoExcuse`] and is byte-for-byte the
/// bar it always was; the writer-relative bar (`fmt_writer_relative`) passes an
/// excuse for its formatter's writer edges and nothing else.
///
/// ONE implementation of the bar, with the excuse plugged in — never a copy. A
/// hand-copied ledger is exactly how a conjunct gets silently dropped, and the
/// writer-relative bar must keep every conjunct but the one it relaxes.
///
/// An excuse may only EXCUSE rows; it cannot grant anything else. Every other
/// conjunct (results present, arrays aligned, summary derived, no-row vacuity,
/// the assumption-root gate) is evaluated identically under every excuse.
pub(crate) trait RowExcuse {
    /// Conjunct 3: is every unproved assumption-panic row of this body's transport
    /// rows excused? The implementation decides how folded sites are judged;
    /// [`NoExcuse`] answers exactly `!transport_rows_have_unproved_assumption_panic`.
    fn assumption_panic_rows_excused(
        &self,
        transport_results: &[trust_types::TransportObligationResult],
    ) -> bool;
    /// Conjunct 4: may this UNPROVED safety disposition be excused? `vc_kind` is
    /// the kind of its row-aligned verification condition, or `None` when the
    /// disposition array is not aligned with the artifact rows (an excuse must
    /// then refuse). The kind, not the VC: an already-verified body's artifact
    /// slot keeps no VC formulas (`super::CachedArtifacts`).
    fn disposition_excused(
        &self,
        vc_kind: Option<&trust_types::VcKind>,
        disposition: &rustc_middle::mir::trust_proof::TrustDisposition,
    ) -> bool;
    /// Trust (OD-1, 2026-10-04, open shapes): conjunct 5 — may the verdict be one
    /// that is CONDITIONAL on this body's own instance hypotheses
    /// (`instance_hypothesis_verdicts`)? Only the instance-RELATIVE bar
    /// ([`InstanceRelative`]) answers yes; every other excuse keeps the default, so
    /// no absolute premise lane can ever spend a hypothesis-carrying verdict. The
    /// user-axiom census and the runtime-checked std member decline are NOT relaxed
    /// by this answer.
    fn admits_instance_hypothesis_verdict(&self) -> bool {
        false
    }
}

/// Trust (OD-1, 2026-10-04, open shapes): the instance-RELATIVE bar. Every row
/// conjunct is [`NoExcuse`]'s; only conjunct 5's instance-hypothesis decline is
/// relaxed, because the one consumer (`instance_hypothesis::record_root_hypotheses`,
/// admitting a still-generic call to a hypothesis-carrying local body) publishes
/// that body's hypotheses, substituted, as its OWN `assumption:instance-hypothesis`
/// rows: the premise is spent only as a named premise of a body that is itself
/// conditional (design §2.2, "still generic → the substituted hypothesis joins
/// H_g"), never as a panic-freedom fact.
pub(crate) struct InstanceRelative;

impl RowExcuse for InstanceRelative {
    fn assumption_panic_rows_excused(
        &self,
        transport_results: &[trust_types::TransportObligationResult],
    ) -> bool {
        NoExcuse.assumption_panic_rows_excused(transport_results)
    }

    fn disposition_excused(
        &self,
        vc_kind: Option<&trust_types::VcKind>,
        disposition: &rustc_middle::mir::trust_proof::TrustDisposition,
    ) -> bool {
        NoExcuse.disposition_excused(vc_kind, disposition)
    }

    fn admits_instance_hypothesis_verdict(&self) -> bool {
        true
    }
}

/// The absolute bar: nothing is excused.
pub(crate) struct NoExcuse;

impl RowExcuse for NoExcuse {
    fn assumption_panic_rows_excused(
        &self,
        transport_results: &[trust_types::TransportObligationResult],
    ) -> bool {
        !transport_rows_have_unproved_assumption_panic(transport_results)
    }

    fn disposition_excused(
        &self,
        _vc_kind: Option<&trust_types::VcKind>,
        _disposition: &rustc_middle::mir::trust_proof::TrustDisposition,
    ) -> bool {
        false
    }
}

/// [`instance_discharges_panic_freedom`] with `excuse` plugged into conjuncts 3
/// and 4. See [`RowExcuse`].
pub(crate) fn instance_discharges_panic_freedom_modulo<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::InstanceKind<'tcx>,
    excuse: &dyn RowExcuse,
) -> Result<(), String> {
    // Trust (2026-09-08, MEASURED on first-party/ty's vendored `rowan`): this
    // premise is asked from INSIDE a body's own verification — the structural-drop
    // lane asks it for every `Drop` terminator — and a `Drop` edge is invisible to
    // the Call-only callgraph that `trust_mir_mutually_recursive_functions` walks.
    // rowan's `impl Drop for ThinArc { fn drop { let _ = Arc::from_thin(ThinArc{..}) } }`
    // is the shape: `drop`'s pass asks for `from_thin`'s optimized MIR (a callee
    // summary; no Call-graph cycle, so allowed), `from_thin`'s cleanup path DROPS a
    // `ThinArc`, this lane asked `trust_proof_results(Item(drop))` while `drop`'s
    // `optimized_mir` was still on the query stack, and rustc answered with
    // `error[E0391]: cycle detected` — a hard error under every policy, in a
    // dependency crate the user does not own. The in-progress ancestor set already
    // knows `drop` is live; consult it BEFORE the query, exactly as the callee-summary
    // lanes do, and DECLINE: the drop keeps its obligation (a completeness cost),
    // the crate compiles. Pinned by
    // `tests/ui/trust/drop_reenters_its_own_conversion_no_query_cycle.rs`.
    if let ty::InstanceKind::Item(def_id) = instance {
        if super::optimized_mir_query_would_cycle(tcx, def_id) {
            return Err("the body's optimized MIR is being computed up this very stack (its own \
                 verification reached a callee whose drop re-enters it); asking for its proof \
                 results here would be an E0391 query cycle, so the premise is declined and \
                 the drop keeps its obligation"
                .to_string());
        }
    }
    // The same protection for every other `InstanceKind` (drop glue and the other
    // shims carry no `DefId` the ancestor set could hold): this lane never asks for
    // an instance it is already asking about further up the stack.
    let key = format!("{instance:?}");
    let reentrant = PANIC_FREEDOM_PREMISE_IN_PROGRESS.with(|s| !s.borrow_mut().insert(key.clone()));
    if reentrant {
        return Err(
            "the premise for this instance is already being evaluated up this stack (its own \
             verification reached a drop of the same type); a re-entrant answer would be a \
             query cycle, so the premise is declined"
                .to_string(),
        );
    }
    let out = instance_discharges_panic_freedom_inner(tcx, instance, excuse);
    if let Err(reason) = &out
        && std::env::var_os("TRUST_PF_BAR_TRACE").is_some()
    {
        eprintln!("[PF_BAR] declined instance={instance:?}: {reason}");
    }
    PANIC_FREEDOM_PREMISE_IN_PROGRESS.with(|s| {
        s.borrow_mut().remove(&key);
    });
    out
}

thread_local! {
    /// `InstanceKind`s whose panic-freedom premise is being evaluated up this
    /// thread's stack, keyed by their `Debug` rendering (an `InstanceKind<'tcx>`
    /// cannot live in a `'static` cell). See `instance_discharges_panic_freedom`.
    static PANIC_FREEDOM_PREMISE_IN_PROGRESS: std::cell::RefCell<FxHashSet<String>> =
        std::cell::RefCell::new(FxHashSet::default());
}

fn instance_discharges_panic_freedom_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::InstanceKind<'tcx>,
    excuse: &dyn RowExcuse,
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
    // The premise view, not the full artifact: an already-verified callee answers
    // from its compact slot instead of re-running its whole verification.
    let Some(artifacts): Option<PremiseArtifacts> = collect_premise_artifacts_cached(tcx, body)
    else {
        return Err(
            "the body produced no verification artifacts, so its obligation ledger could not be \
             inspected"
                .to_string(),
        );
    };
    // Trust (D1 increment 1): conjunct 3 through the excuse. `NoExcuse` answers
    // exactly `!transport_rows_have_unproved_assumption_panic(..)`.
    if !excuse.assumption_panic_rows_excused(artifacts.transport_results()) {
        return Err(
            "the body carries an unproved absent-callee/drop-glue panic obligation; a call it \
             cannot prove panic-free keeps the whole body unable to discharge the contract"
                .to_string(),
        );
    }
    // Trust (2026-09-29): NOT excusable by any `RowExcuse`. A body whose native
    // bundle kept a bundled std member under the runtime-checked disposition owes a
    // `runtime_checked` row for that member's internal Asserts — rows that live in
    // the published transport set, not in `dispositions`, so the row loop below
    // cannot see them. Read off the artifacts directly (conjunct 5's census says
    // the same thing keyed by `DefId`; this also covers a non-`Item` instance).
    if artifacts.has_runtime_checked_std_member() {
        return Err(
            "the body's verdict is conditional on a bundled std/core/alloc member's own runtime \
             check (a member Assert no row discharged, published as `runtime_checked`), so it \
             is not panic-free on its own"
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
    // Trust (D1 increment 1): the dispositions are built one per `artifacts.results`
    // row (`build_proof_results`); an excuse is offered the row's VC kind only when the
    // two arrays are the same length, and must refuse otherwise.
    let rows_aligned = results.dispositions.len() == artifacts.row_count();
    for (index, disposition) in results.dispositions.iter().enumerate() {
        if !obligation_is_safety(disposition.kind) {
            continue;
        }
        safety_rows += 1;
        let proved = matches!(disposition.status, TrustStatus::Trusted | TrustStatus::Certified)
            && disposition.strength != TrustProofStrength::None;
        let row_kind = if rows_aligned { artifacts.row_kind(index) } else { None };
        if !proved && excuse.disposition_excused(row_kind, disposition) {
            continue;
        }
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
        for kind in (0..artifacts.row_count()).filter_map(|index| artifacts.row_kind(index)) {
            if matches!(
                kind,
                trust_types::VcKind::HardenedBoundary { .. }
                    | trust_types::VcKind::UnsupportedMir { .. }
            ) {
                let d: String = format!("{kind:?}").chars().take(120).collect();
                if !detail.contains(&d) {
                    detail.push(d);
                }
            }
        }
        return Err(format!(
            "the body's panic freedom is not fully discharged: {undischarged} of {safety_rows} \
             safety obligation(s) were refuted, left unknown, or kept a runtime check [{}]{}",
            blockers.join(", "),
            if detail.is_empty() {
                String::new()
            } else {
                format!(" detail: {}", detail.join(" | "))
            }
        ));
    }
    if std::env::var_os("TRUST_PF_BAR_TRACE").is_some() {
        eprintln!(
            "[PF_BAR] instance={instance:?} safety_rows={safety_rows} dispositions={:?} \
             transport_rows={} native_vacuously_clean={}",
            results.dispositions.iter().map(|d| (d.kind, d.status, d.strength)).collect::<Vec<_>>(),
            artifacts.transport_results().len(),
            artifacts.native_run_is_vacuously_clean(),
        );
    }
    // Trust (2026-10-09, review round 93): an unresolved INDIRECT call (a `fn`
    // pointer or other open dispatch) has no transport row and no disposition, so
    // no conjunct above sees it, while strict verification refuses the body for it
    // (`function_has_unresolved_indirect_call`, the same test the reporter uses).
    // Measured: the closure `|c: char| p(c)` over `p: fn(char) -> bool` has an
    // empty ledger and a vacuously clean native run, and this bar credited it, so
    // three compiler-total grants treated the call that runs it as total.
    if super::function_has_unresolved_indirect_call(tcx, body) {
        return Err(
            "the body makes an unresolved indirect call, whose callee nothing verified".to_string()
        );
    }
    if safety_rows == 0
        && results.dispositions.is_empty()
        && !artifacts.native_run_is_vacuously_clean()
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
    let axiom_reason = super::verdict_rests_on_user_axiom_for(
        tcx.sess,
        instance.def_id(),
        excuse.admits_instance_hypothesis_verdict(),
    )
    .or_else(|| {
        // The IN-BAND witness of the same fact: an axiom that did leave a row is
        // refused from this body's own ledger, without relying on the census.
        artifacts.spends_a_user_assumed_total_axiom().then_some(
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
    // (6) Trust (OD-1 open-shapes adversarial review, 2026-10-05): THE BODY TRIPS NO
    // INDIRECT-CALL GATE. That gate (`function_has_unresolved_indirect_call`) is a
    // refusal, not a row: a body calling through a fn pointer to code nobody here
    // verified publishes only a `native-verification-gap` `unknown` row, which is not
    // a safety disposition, so conjuncts 1-4 read its ledger as clean. MEASURED on
    // stage 1 of 1177c327fa (probe p5): `impl Tr for Boom { fn m(&self) -> u32 { let
    // p: fn(u32, u32) -> u32 = u32::div_euclid; p(100, self.0) } }` was refused by
    // strict as its own root, yet `helper::<Boom>`'s instance-discharge row for it
    // read `proved`; a closure of that shape discharged `apply::<{closure}>` the
    // same way. Every premise lane ends here, so the conjunct is stated once, for
    // every excuse: a body its own gate refuses is not panic-free on its own.
    if super::function_has_unresolved_indirect_call(tcx, body) {
        return Err("the body calls through a fn pointer or callable whose target nobody in \
             this compilation verified (it trips the indirect-call gate), so its own \
             verification is refused and its ledger cannot stand for the call"
            .to_string());
    }
    Ok(())
}

/// Trust (2026-10-19, DISCHARGE-NO-EVIDENCE-1): after [`instance_discharges_panic_freedom`]
/// REFUSED `instance`, does that refusal rest on nothing but what this compilation did
/// not model? `true` only when the body's own ledger holds no evidence that it can
/// panic: no refuted safety row, no unproved safety row of a kind that could hide a
/// violation (an assertion, overflow, bounds or panic-freedom VC left undecided, a
/// held refutation included), no Level-0 refutation class by kind
/// (`L0RefutationClass::of_kind`), no recorded open-dispatch refutation, no drop-glue,
/// expected-absent or extern-call assumption-panic row, no conditional verdict (a user
/// axiom, an argument premise, a type-invariant premise, an instance hypothesis, a
/// `requires` the body is verified under: `row_kind_carries_no_violation_evidence`)
/// and no runtime-checked std member. What is left is the honest "not proved": generic absent
/// callees and unsupported MIR, an unsafe block declared sound on its `// SAFETY:`
/// comment (its own `assumption:safety-comment` row discloses it), and the gates that
/// refuse a body for what nobody verified (an unresolved indirect call, an empty
/// ledger).
///
/// WHY. The instance discharge (`instance_hypothesis::discharge_instance`) published
/// every refusal of a LOCAL callee as `failed`, with the bare `trust-classifier`
/// solver, so `FailureBasis` read it `refuted` — a found violation — and the advisory
/// `--allow-l0-gaps` gate failed on it, although the callee's own rows were
/// `unknown`/`runtime_checked` gaps the same gate tolerates. MEASURED on the aterm
/// consumer check of the Trust 0.11.0 cut (`20565c3255a`, 2026-10-19, `targo trust
/// build --allow-l0-gaps -p aterm`): `Gate: FAIL` on two such rows, the closures
/// `|| { unsafe { adopt_startup_bridge_lanes() }? .. }` and `|why| aterm_log::info!("{why}")`,
/// whose own Level 0 summaries read `0 failed, 1 unknown, 1 runtime-checked` and
/// `0 failed, 3 unknown, 1 runtime-checked`. The design (docs/design/
/// 2026-10-03-open-generic-dispatch-obligations.md §2.2) says the discharge row takes
/// the callee instance's existing verdict, `unknown` included.
///
/// DIRECTION. This only lets the caller publish `unknown` (not established) in place
/// of `failed` for such a refusal; every fail-closed lane errors on both
/// (`report_unestablished_discharges`), no row gains credit, and every answer this
/// function cannot give with certainty is `false` (the refusal stays `failed`). It
/// never re-enters: the bar's own guards are asked first. It is not a second copy of
/// the bar: whether a premise is credited is still decided only by
/// [`instance_discharges_panic_freedom`].
pub(crate) fn refusal_carries_no_violation_evidence<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::InstanceKind<'tcx>,
) -> bool {
    if let ty::InstanceKind::Item(def_id) = instance
        && super::optimized_mir_query_would_cycle(tcx, def_id)
    {
        return false;
    }
    let key = format!("{instance:?}");
    if PANIC_FREEDOM_PREMISE_IN_PROGRESS.with(|s| s.borrow().contains(&key)) {
        return false;
    }
    let Some(results) = tcx.trust_proof_results(instance) else {
        return false;
    };
    if !results.has_aligned_obligation_arrays() || results.recompute_summary() != results.summary {
        return false;
    }
    let body = tcx.instance_mir(instance);
    let Some(artifacts): Option<PremiseArtifacts> = collect_premise_artifacts_cached(tcx, body)
    else {
        return false;
    };
    if artifacts.has_runtime_checked_std_member() || artifacts.spends_a_user_assumed_total_axiom() {
        return false;
    }
    // Every conditional verdict but a `// SAFETY:` declaration keeps `failed`. A declared
    // block's premise is disclosed by the body's own `assumption:safety-comment` row
    // (SAFETY-ASSUME-1), which the gate counts `assumed`; its unmodeled operations
    // published no row an engine could refute.
    let conditional =
        super::verdict_rests_on_user_axiom_admitting(tcx.sess, instance.def_id(), false, true);
    if conditional.is_some() {
        return false;
    }
    // A class (c) row (open, uncontracted dispatch) is an absent-callee row by its text;
    // the body's recorded refutations are what tell it apart.
    let def_id = instance.def_id();
    let refuted_open_dispatch = super::with_crate_verification_state(tcx.sess, |state| {
        state.open_dispatch_refuted_callees.get(&def_id).is_some_and(|set| !set.is_empty())
    });
    if refuted_open_dispatch {
        return false;
    }
    if artifacts.transport_results().iter().any(|row| {
        super::transport_row_is_unproved_assumption_panic(row)
            && !super::transport_row_is_unproved_absent_callee(row)
    }) {
        return false;
    }
    if results.dispositions.len() != artifacts.row_count() {
        return false;
    }
    results.dispositions.iter().enumerate().all(|(index, disposition)| {
        if !obligation_is_safety(disposition.kind) {
            return true;
        }
        let proved = matches!(disposition.status, TrustStatus::Trusted | TrustStatus::Certified)
            && disposition.strength != TrustProofStrength::None;
        proved
            || (!matches!(disposition.status, TrustStatus::Failed)
                && artifacts.row_kind(index).is_some_and(row_kind_carries_no_violation_evidence))
    })
}

/// An unproved row of this kind says only that something was not modeled: a generic
/// absent callee (`[trust-absent-callee-assumption]`, either spelling), or an
/// `UnsupportedMir` row that is no Level-0 refutation class and no round-tripped
/// full-verification obligation. Every other kind is a formula some engine could refute,
/// so leaving it unproved is not evidence-free.
///
/// A `FullVerification::<ApiKind>` row (`VcKind::FULL_VERIFICATION_KIND_PREFIX`, minted
/// by `legacy_unsupported_kind_detail`) is the native lane's own obligation carried as
/// `UnsupportedMir` only because the legacy lane has no kind for it: an assertion, a
/// postcondition, a temporal claim, or the `requires` the body is verified under
/// (`FullVerification::Precondition` with a `contract_id`, the `assumption:requires`
/// entry row). That is a claim or a premise, not unmodeled MIR. A callee proved only
/// under its own `requires` is conditional on a clause the instance's caller never
/// established: `f<T: Td>(t: &T) { t.m(0) }` at `<Bad as Td>::m`, `requires x != 0 {
/// 100 / x }`, divides by zero, and that discharge is the only `failed` row on the
/// `f::<Bad>` path (`instance_hypothesis/trait_impl_requires_reached_through_instance.rs`,
/// ADVISORY-REQUIRES-INSTANCE), so it stays `failed`. Only the lane's own unmodeled-MIR
/// kind, `FullVerification::trust.vc::unsupported_mir`, says nothing was modeled.
fn row_kind_carries_no_violation_evidence(kind: &trust_types::VcKind) -> bool {
    if trust_types::l0_refutation::L0RefutationClass::of_kind(kind, |_| false).is_some() {
        return false;
    }
    if trust_types::l0_refutation::absent_callee_name(kind).is_some() {
        return true;
    }
    match kind {
        trust_types::VcKind::UnsupportedMir { kind: api_kind, .. } => {
            !api_kind.starts_with(trust_types::VcKind::FULL_VERIFICATION_KIND_PREFIX)
                || api_kind == "FullVerification::trust.vc::unsupported_mir"
        }
        _ => false,
    }
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
        if let Some(trait_method) =
            tcx.opt_associated_item(def_id).and_then(|i| i.trait_item_def_id())
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
        let Some(trait_def_id) =
            tcx.opt_associated_item(trait_method).and_then(|i| i.trait_container(tcx))
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
/// Trust (2026-10-04): the WHOLE-PROGRAM bullet is one route of three since
/// 2026-09-20 (`local_trait_certificate`); an rlib passes when `T` is not
/// exported or `super::private_supertrait_seals` holds (DEP-SEAL-1 narrowed
/// the latter to supertraits no downstream type can satisfy), and neither route
/// is taken in a crate that defines a def-site-hygienic macro
/// (`super::crate_defines_def_site_macro`, 2026-10-05).
///
/// UNLIKE rung 2 this does NOT enumerate the impls at the call site, and it
/// therefore accepts blanket and generic impls — each of those discharged
/// polymorphically at its own definition, which is exactly what makes the
/// forwarding impl `impl<S: T> T for W<S>` provable at all.
///
/// Trust (D4 increment B, 2026-09-25): a FOREIGN trait is served by a different
/// argument — `foreign_trait_closure`, which DOES enumerate: in a whole-program
/// artifact, at a generic call whose `Self` is `Sized`, it re-derives every
/// foreign dispatch target in this compilation and relies on this crate's own
/// discharge for its local impls. `shape` is what that arm reads; the
/// local-trait certificate below ignores it and is byte-for-byte unchanged.
pub(crate) fn generic_call_relies_on_panic_free_contract(
    tcx: TyCtxt<'_>,
    callee_def_id: DefId,
    shape: super::foreign_trait_closure::RelianceShape,
) -> bool {
    if !trait_method_declares_panic_free(tcx, callee_def_id) {
        return false;
    }
    let Some(trait_def_id) = tcx.trait_of_assoc(callee_def_id) else {
        return false;
    };
    // Completeness: only a locally-declared trait has had EVERY impl that can
    // exist checked by this compilation. A foreign one must have them ENUMERATED
    // and re-derived instead (D4 increment B) — never taken on the dependency's
    // word, which rmeta does not carry and this compilation would not believe.
    if !trait_def_id.is_local() {
        return super::foreign_trait_closure::foreign_impl_set_rederived_panic_free(
            tcx,
            trait_def_id,
            callee_def_id,
            shape,
            super::foreign_trait_closure::ClosureRung::PanicFreeContract,
        );
    }
    local_trait_certificate(tcx, callee_def_id, trait_def_id)
}

/// The LOCAL-trait half of [`generic_call_relies_on_panic_free_contract`], for a
/// caller that must not enumerate or force anything: the adversarial-refutation
/// LABEL (`adversarially_refutable_open_dispatch_callees`) reads it. `false` for
/// every foreign trait — exactly the answer the whole predicate gave one before
/// D4 increment B.
pub(crate) fn local_trait_relies_on_panic_free_contract(
    tcx: TyCtxt<'_>,
    callee_def_id: DefId,
) -> bool {
    if !trait_method_declares_panic_free(tcx, callee_def_id) {
        return false;
    }
    let Some(trait_def_id) = tcx.trait_of_assoc(callee_def_id) else {
        return false;
    };
    trait_def_id.is_local() && local_trait_certificate(tcx, callee_def_id, trait_def_id)
}

/// The local-trait certificate: closed world, no specializing override. The body
/// of [`generic_call_relies_on_panic_free_contract`] before D4 increment B, moved
/// verbatim; its callers have already established that `callee_def_id` declares
/// Φ and belongs to `trait_def_id`.
fn local_trait_certificate(tcx: TyCtxt<'_>, callee_def_id: DefId, trait_def_id: DefId) -> bool {
    // Trust (2026-09-20): the CLOSED-WORLD question, all three routes.
    //
    // This gated on `crate_types_are_whole_program` alone while the doc above
    // said it reuses `dyn_trait_sealedness`'s route "verbatim rather than
    // reinvented". It is not verbatim: that is a three-way disjunction
    // (`whole_program || not_exported || private_supertrait_seals`) and two
    // routes were dropped in the reuse. Both dropped routes are closed-world by
    // LANGUAGE VISIBILITY — a downstream crate cannot name a non-exported trait
    // to implement it, nor satisfy a CLOSED private supertrait — so they hold in
    // an rlib exactly as in an executable, and `w8` already rails the
    // non-exported route green for the `dyn` lane in a library.
    //
    // Trust (2026-10-04, DEP-SEAL-1): "cannot satisfy a private supertrait" was
    // false as the third disjunct asked it (`has_private_supertrait`: the
    // supertrait is merely not exported). A private `Sealed` with
    // `impl<X: ?Sized> Sealed for X` (or `for Box<X>`, `for &X`), a private
    // trait alias or auto trait, or a generic `T<P>` (`impl a::T<Local> for
    // a::Good`) all let a downstream crate implement `T`, and this rung
    // certified `f<K: T>` over Φ in an rlib whose downstream impl panicked. The
    // shared helper now asks `private_supertrait_seals`, rules (a)–(d), so this
    // rung inherits the fix; `tests/open-dispatch-ladder/w14_*_phi_*` rail it.
    //
    // Trust (2026-10-05, DEP-SEAL-1 macro-2.0 residual): "cannot name" is false too
    // when the crate defines a def-site-hygienic macro (`pub macro seal($t:ty) {
    // impl private::Sealed for $t {} }`): a downstream invocation resolves the
    // macro's paths here, with this crate's privacy. The shared helper drops both
    // language-visibility routes then (`crate_defines_def_site_macro`), so this rung
    // inherits that as well; `tests/open-dispatch-ladder/w14_macro2_*` rail it.
    //
    // The blanket-impl refusal stays OUT of the shared helper on purpose: it is
    // rung 2's enumerability premise, and this rung does not enumerate (see the
    // doc above), which is exactly what lets it accept the forwarding impl.
    let Some(trait_local) = trait_def_id.as_local() else {
        return false;
    };
    if !super::trait_impl_set_is_closed_world(tcx, trait_def_id, trait_local) {
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
        if let Some(&impl_method) = tcx.impl_item_implementor_ids(impl_def_id).get(&callee_def_id)
            && tcx.defaultness(impl_method).is_default()
        {
            return false;
        }
    }
    true
}
