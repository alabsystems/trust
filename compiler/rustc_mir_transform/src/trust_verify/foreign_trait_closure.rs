//! Trust (D4 increment B, 2026-09-25): rung 1 (`#[trust::panic_free]`, Φ) and
//! rung 2 (sealed enumeration) of the open-dispatch lattice for a FOREIGN trait,
//! at a GENERIC call site, in a WHOLE-PROGRAM artifact — by enumerating the
//! trait's impl set in the loaded crate graph and RE-DERIVING every foreign
//! dispatch target in this compilation.
//!
//! # What this closes
//!
//! Both rungs used to refuse every non-local trait outright:
//! `generic_call_relies_on_panic_free_contract` returned `false` at
//! `!trait_def_id.is_local()`, and `dyn_trait_sealedness` answered `Open` for any
//! foreign trait. So `fn f<X: dep::T>(x: &X) -> u32 { x.m() }` in a binary was
//! refused even when every impl of `dep::T::m` that exists anywhere was provable
//! — measured on the stage-1 snapshot at `43b8fe6ab`: every generic row of
//! `tests/ui/trust/xcrate_foreign_trait_closure_phi.rs` and
//! `…_sealed.rs` refused with "Trust strict verification failed for `f`" on the
//! fatal generic absent-callee row, while a LOCAL copy of each program (trait and
//! impls in one crate) built rc=0.
//!
//! # Why the enumeration is complete
//!
//! At an `ImplSource::Param` call `<X as T>::m` whose `Self` is `Sized` in the
//! caller's typing environment, every monomorphization selects a USER impl of `T`
//! (a sysroot or lang-item trait is refused below, and those are the only traits
//! with compiler-provided impls apart from the object candidate, which needs an
//! unsized `Self`). In a whole-program artifact (`Executable` / `StaticLib` /
//! `Cdylib`) every monomorphization that can reach this call is made from THIS
//! crate graph — no crate compiled later can link against the artifact and add
//! an impl — and trait selection can only resolve to an impl of a crate in that
//! graph, which `tcx.all_impls(T)` (= `trait_impls_of`) enumerates: the local
//! crate plus every crate this compilation loaded. The trait's own crate is
//! loaded by definition (the call names it), and so is every crate that can
//! implement it.
//!
//! # The discharge, per dispatch target
//!
//! The dispatch target of an impl is its override of `m`, or the trait's default
//! body when it does not override (a specializing `default fn` or `default impl`,
//! a negative or reservation impl, or a missing default body declines — the
//! specialization graph is not reasoned about). Then:
//!
//! * a FOREIGN target is judged by the shared evidence bar,
//!   `dyn_dispatch_reliance::dyn_target_is_verified_panic_free`, which first
//!   ADMITS it to re-derivation (`foreign_rederivation`: declared by identity,
//!   statically linked, non-sysroot, encoded MIR, no interposable symbol, no user
//!   `unsafe` source, within the cost bound) and then requires the verdict THIS
//!   compilation computes over its encoded MIR to clear all five conjuncts.
//!   Nothing about the dependency's own verification is read;
//! * a LOCAL target of rung 1 (Φ) is an impl method this crate's
//!   `discharge_trait_panic_free_contracts` holds to Φ as a hard error at the
//!   impl — the same premise the local-trait rung relies on, never forced here;
//! * every other LOCAL target (rung 2) is judged by the same shared bar.
//!
//! # Self-reliance is declined
//!
//! While the closure for `T::m` is being computed, a reliance asked for `T::m`
//! from inside it — a foreign impl body whose own verification reaches a generic
//! `<S as T>::m`, the forwarding impl `impl<S: T> T for W<S>` — answers `false`
//! ([`FOREIGN_CLOSURE_IN_PROGRESS`]). The innermost-frame argument would make an
//! optimistic `true` sound for the PROGRAM, but not for the query cache: that
//! body's `trust_proof_results` would be memoized as proved under a pending
//! premise, and read later by a lane (C-FLOW, the `write_fmt` reduction) that
//! never re-checks the premise — and the premise can still fail on a sibling
//! impl. Declining can only fail a verdict (every discharge is monotone), so
//! every `true` this function returns is unconditional, in every evaluation
//! order. The cost is recorded: a FOREIGN forwarding impl never re-derives
//! (`fwd_foreign`), while a LOCAL one relies on local enforcement like any other
//! local impl (`fwd_local`).
//!
//! # What stays refused, and why
//!
//! * A `dyn` call over a foreign trait (C-UNIVERSAL and C-SEALED at an
//!   `InstanceKind::Virtual` site) — and a generic call whose `Self` may be
//!   unsized, which a monomorphization at `dyn T` turns into the same virtual
//!   call. A monomorphization cannot be forged; a vtable can, and for a foreign
//!   trait it can be minted in dependency bodies no forge-poison walk of this
//!   compilation ever sees.
//! * Any artifact a downstream crate can link (`rlib`, `dylib`, proc-macro) —
//!   including the exported Φ trait of `w10`, which is local and untouched here.
//! * Every sysroot or unclassified trait (D1), every lang-item or auto trait.
//! * A blanket impl, for rung 2 (its enumerability premise; rung 1 verifies a
//!   blanket impl's body polymorphically like any other target).
//! * Any enumerated impl the pre-pass cannot pin to a re-derivable target, and
//!   an empty impl set (vacuity stays visible as the fatal row).
//! * A set whose FOREIGN targets do not fit the re-derivation cost bound — see
//!   "Cost" below. Local impls cost nothing here and are not counted.
//!
//! # Cost: decided before anything is forced
//!
//! Every foreign target is a full nested verification (3–4 s measured per body
//! for D4-A), and the budget that bounds them (`foreign_rederivation`'s
//! per-crate and per-compilation caps on DISTINCT re-derived bodies) is shared
//! with every other D4-A lane. So the closure settles its cost BEFORE it forces
//! a single verdict, in three steps, and a closure that declines on cost charges
//! nothing:
//!
//! 1. **From the impl set alone** ([`dispatch_targets`]): more distinct foreign
//!    targets in one crate, or in total, than the caps allow can never fit, in
//!    any query order — declined during the enumeration, which stops there.
//! 2. **Every non-forcing conjunct of the bar, for every target**
//!    (`dyn_dispatch_reliance::target_pre_conjuncts_hold_budget_free`):
//!    self-discharge, `#[trust::skip]` / `assume_total`, re-derivability, an
//!    authored clause, a cycle or an in-progress computation. A set that would
//!    fail one of those fails before any verdict is forced.
//! 3. **The whole set's budget, all or nothing**
//!    (`foreign_rederivation::reserve_foreign_rederivations`): every foreign
//!    target not yet admitted is RESERVED against both caps, or none is and the
//!    closure declines. Reserved bodies count against the caps while the set is
//!    forced, so a nested verification's own admissions cannot exhaust the
//!    budget half-way through the set.
//!
//! Only then are verdicts forced — first every target whose re-derivation is
//! already paid for (local targets, bodies admitted earlier), then the newly
//! reserved ones — and the first failure stops the loop. A reserved body the
//! loop never reached is released on the way out; a body it did force stays
//! charged, because it WAS re-derived (releasing it would let a compilation with
//! many failing sets re-derive without bound, which is what the budget exists
//! to prevent).
//!
//! What remains order-dependent is inherent to one shared, first-come budget:
//! whether step 3 fits depends on what earlier asks admitted. It no longer
//! depends on how far a closure got before discovering it could not finish.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::{CrateNum, DefId};

use super::{
    crate_types_are_whole_program, dyn_dispatch_reliance, foreign_rederivation, probe_label,
    trait_panic_free,
};

/// Where a reliance on a trait method's impl set is being asked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RelianceShape {
    /// An `ImplSource::Param` call (`Instance::try_resolve` = `Ok(None)`) being
    /// DISCHARGED in `scanned_body`. `self_is_sized`: the call's `Self` type is
    /// `Sized` in that body's typing environment, so no monomorphization can
    /// instantiate it at `dyn T` and turn the call into a virtual one.
    Generic { scanned_body: DefId, self_is_sized: bool },
    /// An `InstanceKind::Virtual` call. The foreign arm never serves it.
    Virtual,
}

impl RelianceShape {
    /// The shape of an `ImplSource::Param` call with `gen_args`, found in
    /// `scanned_body` under `typing_env`. A call whose `Self` argument is missing
    /// or not a type is recorded as possibly unsized (fail-closed).
    pub(crate) fn of_param_call<'tcx>(
        tcx: TyCtxt<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        gen_args: ty::GenericArgs<'tcx>,
        scanned_body: DefId,
    ) -> Self {
        let self_is_sized = gen_args
            .first()
            .and_then(|arg| arg.as_type())
            .is_some_and(|self_ty| self_ty.is_sized(tcx, typing_env));
        RelianceShape::Generic { scanned_body, self_is_sized }
    }
}

/// Which rung is asking. They share the enumeration and differ in two places.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ClosureRung {
    /// Rung 1: the trait method declares Φ. Blanket impls are admitted (each is a
    /// target verified polymorphically), and a LOCAL target relies on this
    /// crate's hard-error per-impl discharge.
    PanicFreeContract,
    /// Rung 2: no declaration. A blanket impl refuses (the enumerability
    /// premise), and every target, local or foreign, goes through the shared bar.
    Sealed,
}

thread_local! {
    /// Trait METHODS whose foreign closure is being computed up this thread's
    /// stack. Shared by both rungs: they enumerate the same impl set, so a nested
    /// ask for the same method under either rung is the same self-reliance.
    static FOREIGN_CLOSURE_IN_PROGRESS: std::cell::RefCell<FxHashSet<DefId>> =
        std::cell::RefCell::new(FxHashSet::default());
}

/// RAII ownership of one [`FOREIGN_CLOSURE_IN_PROGRESS`] entry.
struct ClosureGuard(DefId);

impl ClosureGuard {
    fn enter(method_def_id: DefId) -> Option<Self> {
        FOREIGN_CLOSURE_IN_PROGRESS
            .with(|set| set.borrow_mut().insert(method_def_id))
            .then_some(Self(method_def_id))
    }
}

impl Drop for ClosureGuard {
    fn drop(&mut self) {
        FOREIGN_CLOSURE_IN_PROGRESS.with(|set| {
            set.borrow_mut().remove(&self.0);
        });
    }
}

/// The SHAPE conjuncts: the foreign arm serves only an `ImplSource::Param` call
/// whose `Self` is `Sized`, and then names the body the call is discharged in
/// (which is never credited as its own dispatch target). A pure function, so the
/// gate that keeps every `dyn` shape out is unit-tested without a `TyCtxt`
/// (`trust_verify/tests.rs`).
pub(super) fn shape_scanned_body(shape: RelianceShape) -> Result<DefId, &'static str> {
    match shape {
        RelianceShape::Virtual => Err(
            "a virtual (`dyn`) call site: a vtable, unlike a monomorphization, can be forged in \
             dependency bodies no walk of this compilation sees",
        ),
        RelianceShape::Generic { self_is_sized: false, .. } => Err(
            "the call's `Self` may be unsized, so a monomorphization at `dyn T` would make it a \
             virtual call",
        ),
        RelianceShape::Generic { scanned_body, self_is_sized: true } => Ok(scanned_body),
    }
}

/// RAII: restores the thread's `ADMITTED_DESTRUCTOR_ADTS` record — the ADTs whose
/// destructor body the CURRENT bundle admitted, which the bundle builder reads
/// back only after collecting its absent callees — to what it was on entry.
///
/// That record is "cleared at the start of every bundle closure", so a nested
/// verification forced from inside an enclosing bundle's absent-callee
/// collection replaces the enclosing bundle's record with its own. MEASURED on
/// the stage-1 snapshot `43b8fe6ab`, through the pre-existing C-FLOW lane (D4-A):
/// `pub fn f(v: Vec<u8>) -> u32` that also calls `area` through `&dyn Shape` on a
/// declared dependency's `Sq` printed `[DROP_DERIVE] fn=f ... destructor_adts={}`,
/// while the same `f` without the `dyn` call printed
/// `destructor_adts={"alloc::vec::Vec", "alloc::raw_vec::RawVec"}` — the nested
/// verification of `Sq::area` emptied it (a lost discharge there; the record
/// feeds the bridge's drop-glue discharge, so a nested record carrying an ADT the
/// enclosing bundle never admitted would be the unsound direction). The
/// foreign-trait closure forces first-time foreign verdicts at exactly that
/// point, so it leaves the record as it found it.
///
/// Trust (2026-10-02): the bundle builder
/// (`build_native_trust_ir_bundle_for_verifier_api`) now snapshots its record when
/// its closure returns and restores the enclosing one, which covers every forcing
/// site. This guard stays as a local, redundant restore.
struct AdmittedDestructorRecordPreserved(FxHashSet<(String, String)>);

impl AdmittedDestructorRecordPreserved {
    fn enter() -> Self {
        Self(super::ADMITTED_DESTRUCTOR_ADTS.with(|set| set.borrow().clone()))
    }
}

impl Drop for AdmittedDestructorRecordPreserved {
    fn drop(&mut self) {
        let saved = std::mem::take(&mut self.0);
        super::ADMITTED_DESTRUCTOR_ADTS.with(|set| *set.borrow_mut() = saved);
    }
}

/// The conjuncts decidable from the trait, the method, the rung and the artifact
/// alone — no enumeration, no forcing. `Some(reason)` is the first that failed.
fn structural_decline(
    tcx: TyCtxt<'_>,
    trait_def_id: DefId,
    method_def_id: DefId,
    rung: ClosureRung,
) -> Option<&'static str> {
    if trait_def_id.is_local() {
        return Some("the trait is local; the local-trait arm of the rung decides it");
    }
    if tcx.trait_of_assoc(method_def_id) != Some(trait_def_id) {
        return Some("the method is not an associated fn of this trait");
    }
    if !crate_types_are_whole_program(tcx) {
        return Some(
            "this artifact is not whole-program (an rlib, dylib or proc-macro): a crate \
             compiled later can add an impl this compilation never sees",
        );
    }
    if foreign_rederivation::crate_is_sysroot(tcx, trait_def_id.krate)
        || !foreign_rederivation::declared_scope_bucket_is_rederivable(
            trust_mir_extract::policy::classify_def(tcx, trait_def_id, super::step4_library_lane()),
        )
    {
        return Some("a sysroot (or unclassified) trait; its impl set is never enumerated here");
    }
    if tcx.as_lang_item(trait_def_id).is_some() || tcx.trait_is_auto(trait_def_id) {
        return Some(
            "a lang-item or auto trait, which has compiler-provided impls no enumeration lists",
        );
    }
    match rung {
        ClosureRung::PanicFreeContract => {
            if !trait_panic_free::trait_method_declares_panic_free(tcx, method_def_id) {
                return Some("the method declares no `#[trust::panic_free]` contract");
            }
        }
        ClosureRung::Sealed => {
            if !tcx.trait_impls_of(trait_def_id).blanket_impls().is_empty() {
                return Some(
                    "the trait has a blanket impl, which rung 2's enumeration does not cover",
                );
            }
        }
    }
    None
}

/// The DISTINCT dispatch targets of `method_def_id` over every impl of
/// `trait_def_id` in the loaded crate graph. Decision-free and non-forcing: it
/// reads impl headers, defaultness and `foreign_rederivation_decline` (which
/// consumes no budget). `Err((reason, at))` names the first impl or target that
/// cannot be pinned.
///
/// Also the first COST step (module docs, "Cost"): the distinct FOREIGN targets
/// are counted per crate and in total against the re-derivation caps, and the
/// enumeration stops at the first one over either. That is decided from the
/// impl set alone — a set needing more distinct bodies than the ledger can ever
/// hold can never be discharged, whatever was admitted before — so it is the
/// same in every query order. LOCAL targets are not counted: rung 1 never forces
/// one, and rung 2 reads a verdict this compilation computes anyway.
fn dispatch_targets(
    tcx: TyCtxt<'_>,
    trait_def_id: DefId,
    method_def_id: DefId,
) -> Result<Vec<DefId>, (&'static str, Option<DefId>)> {
    let (per_crate_cap, total_cap) = foreign_rederivation::budget_caps();
    let mut targets: Vec<DefId> = Vec::new();
    let mut seen: FxHashSet<DefId> = FxHashSet::default();
    let mut foreign_total = 0usize;
    let mut foreign_per_crate: FxHashMap<CrateNum, usize> = FxHashMap::default();
    let mut any_impl = false;
    for impl_def_id in tcx.all_impls(trait_def_id) {
        any_impl = true;
        if tcx.impl_polarity(impl_def_id) != ty::ImplPolarity::Positive {
            return Err(("a negative or reservation impl", Some(impl_def_id)));
        }
        if tcx.defaultness(impl_def_id).is_default() {
            return Err(("a `default impl` (specialization)", Some(impl_def_id)));
        }
        let target = match tcx.impl_item_implementor_ids(impl_def_id).get(&method_def_id) {
            Some(&impl_method) => {
                // A specializing `default fn`: the body that runs need not be the
                // one named here. The same refusal the local-trait rung makes.
                if tcx.defaultness(impl_method).is_default() {
                    return Err(("a specializable `default fn` override", Some(impl_method)));
                }
                impl_method
            }
            None => {
                // Non-overriding: the trait's default body is the target. With no
                // default body the impl can only inherit through specialization.
                if !tcx.defaultness(method_def_id).has_value() {
                    return Err((
                        "an impl that neither overrides the method nor inherits a default body",
                        Some(impl_def_id),
                    ));
                }
                method_def_id
            }
        };
        if !seen.insert(target) {
            continue;
        }
        if !target.is_local() {
            if let Some(decline) = foreign_rederivation::foreign_rederivation_decline(tcx, target) {
                return Err((decline.reason(), Some(target)));
            }
            foreign_total += 1;
            let in_crate = foreign_per_crate.entry(target.krate).or_default();
            *in_crate += 1;
            if *in_crate > per_crate_cap || foreign_total > total_cap {
                return Err((
                    "the impl set has more distinct foreign dispatch targets (in one crate, or in \
                     total) than the re-derivation cost bound can ever admit; declined from the \
                     impl set alone, before any verdict is forced",
                    Some(target),
                ));
            }
        }
        targets.push(target);
    }
    if !any_impl {
        // Vacuity must stay visible as the fatal row, never become a silent green.
        return Err(("the trait has no impl at all (vacuous)", None));
    }
    Ok(targets)
}

/// THE FOREIGN ARM of rungs 1 and 2: is every dispatch target of `method_def_id`,
/// over the complete impl set of the FOREIGN `trait_def_id`, panic-free — each
/// foreign one by a verdict re-derived in this compilation? See the module docs.
/// Every failure mode answers `false`, which keeps the call's fatal row.
pub(crate) fn foreign_impl_set_rederived_panic_free(
    tcx: TyCtxt<'_>,
    trait_def_id: DefId,
    method_def_id: DefId,
    shape: RelianceShape,
    rung: ClosureRung,
) -> bool {
    // Diagnostic-only trace (TRUST_FOREIGN_CLOSURE_PROBE=1): names the conjunct
    // that declined. Verdict-neutral — no branch depends on it.
    let probe = std::env::var_os("TRUST_FOREIGN_CLOSURE_PROBE").is_some();
    let decline = |why: &str, at: Option<DefId>| -> bool {
        if probe {
            let at =
                at.map(|def_id| format!(" at {}", probe_label(tcx, def_id))).unwrap_or_default();
            eprintln!(
                "TRUST_FOREIGN_CLOSURE_PROBE: method={} rung={rung:?} declined{at}: {why}",
                probe_label(tcx, method_def_id)
            );
        }
        false
    };
    let scanned_body = match shape_scanned_body(shape) {
        Ok(scanned_body) => scanned_body,
        Err(why) => return decline(why, None),
    };
    if let Some(why) = structural_decline(tcx, trait_def_id, method_def_id, rung) {
        return decline(why, None);
    }
    // Self-reliance: checked before the enumeration so a nested ask costs nothing.
    if FOREIGN_CLOSURE_IN_PROGRESS.with(|set| set.borrow().contains(&method_def_id)) {
        return decline(
            "self-reliance: this method's closure is being computed up this stack, and a \
             verdict memoized under that pending premise could be read later by a lane that \
             never re-checks it",
            None,
        );
    }
    // Cost step 1 (module docs, "Cost"): from the impl set alone.
    let targets = match dispatch_targets(tcx, trait_def_id, method_def_id) {
        Ok(targets) => targets,
        Err((why, at)) => return decline(why, at),
    };
    // The targets the SHARED BAR judges. Rung 1, a LOCAL override of the Φ
    // method: `discharge_trait_panic_free_contracts` holds it to Φ as a hard
    // error at the impl, in this very compilation — the premise the local-trait
    // rung already rests on — so it is never forced here. Checked by identity
    // (the override's inherited obligation IS this method), so a local target
    // that is anything else goes to the bar like every other target.
    let barred: Vec<DefId> = targets
        .iter()
        .copied()
        .filter(|&target| {
            !(target.is_local()
                && rung == ClosureRung::PanicFreeContract
                && trait_panic_free::inherited_panic_free_obligation(tcx, target)
                    == Some(method_def_id))
        })
        .collect();
    let decline_at_target = |target: DefId| -> bool {
        if probe {
            let instance =
                ty::Instance::new_raw(target, ty::GenericArgs::identity_for_item(tcx, target));
            let reason = dyn_dispatch_reliance::target_decline_reason(tcx, instance, scanned_body);
            eprintln!(
                "TRUST_FOREIGN_CLOSURE_PROBE: method={} rung={rung:?} declined at {}: {reason}",
                probe_label(tcx, method_def_id),
                probe_label(tcx, target)
            );
        }
        false
    };
    // Cost step 2: every NON-FORCING conjunct of the bar, for every target,
    // before any verdict is forced — a set that fails one of them costs nothing.
    for &target in &barred {
        if !dyn_dispatch_reliance::target_pre_conjuncts_hold_budget_free(tcx, target, scanned_body)
        {
            return decline_at_target(target);
        }
    }
    // Cost step 3: the whole set's budget, all or nothing, before any verdict is
    // forced. Held until this function returns; see
    // `foreign_rederivation::ForeignRederivationReservation`.
    let foreign: Vec<DefId> = barred.iter().copied().filter(|target| !target.is_local()).collect();
    let reservation = match foreign_rederivation::reserve_foreign_rederivations(tcx, &foreign) {
        Ok(reservation) => reservation,
        Err(budget) => {
            let why = format!(
                "{} foreign dispatch target(s) do not fit what remains of the re-derivation \
                 budget; declined before any verdict was forced, nothing charged ({})",
                foreign.len(),
                budget.reason()
            );
            return decline(why.as_str(), None);
        }
    };
    let Some(_guard) = ClosureGuard::enter(method_def_id) else {
        return decline("self-reliance (re-entered while enumerating)", None);
    };
    // The loop below FORCES verdicts, and a foreign target's first verdict is a
    // whole nested verification — whose bundle build clears and refills the
    // per-bundle `ADMITTED_DESTRUCTOR_ADTS` record while the ENCLOSING bundle
    // (the one this generic call sits in) has yet to read its own. See
    // [`AdmittedDestructorRecordPreserved`].
    let _destructor_record = AdmittedDestructorRecordPreserved::enter();
    // Forced in two passes: first every target whose re-derivation was already
    // paid for (local, or admitted/reserved before this closure), then the ones
    // this closure newly reserved — so a set that fails on an already-paid
    // verdict charges nothing new. The first failure stops the loop; the
    // reservation's drop releases every newly reserved body it never reached.
    let (paid, newly_reserved): (Vec<DefId>, Vec<DefId>) =
        barred.iter().copied().partition(|&target| !reservation.is_new(target));
    for target in paid.into_iter().chain(newly_reserved) {
        let instance =
            ty::Instance::new_raw(target, ty::GenericArgs::identity_for_item(tcx, target));
        if !dyn_dispatch_reliance::dyn_target_is_verified_panic_free(tcx, instance, scanned_body) {
            return decline_at_target(target);
        }
    }
    if probe {
        eprintln!(
            "TRUST_FOREIGN_CLOSURE_PROBE: method={} rung={rung:?} DISCHARGED over {} target(s) \
             ({} through the bar, {} foreign)",
            probe_label(tcx, method_def_id),
            targets.len(),
            barred.len(),
            foreign.len()
        );
    }
    true
}
