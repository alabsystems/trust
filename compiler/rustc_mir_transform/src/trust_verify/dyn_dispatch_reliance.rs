//! Trust rung 1, §(c) for `dyn` dispatch: when may a call through
//! `InstanceKind::Virtual` discharge its panic-freedom obligation?
//!
//! A virtual call names no body. Discharging it is sound only if EVERY impl the
//! receiver could hold has been proved panic-free, so the whole question is a
//! COMPLETENESS question and this module is two independent completeness
//! certificates. They discharge the same obligation by different arguments and
//! must be attacked separately; both fail closed.
//!
//! **C-UNIVERSAL** — the trait method carries `#[trust::panic_free]` (Φ), the
//! trait is LOCAL (so `trait_panic_free`'s per-impl discharge ran over the crate
//! that owns it, and no dependency could have supplied an impl — an impl must
//! name the trait), and the artifact is WHOLE-PROGRAM (so no crate compiled
//! later can add one). Quantifies over the IMPL SET. Identical to the certificate
//! the generic (`ImplSource::Param`) lane already uses, because a `dyn T` receiver
//! and a `T`-bounded type parameter range over exactly the same impls.
//!
//! **C-FLOW** — a `dyn T` value exists only because some `Unsize` coercion built
//! its vtable. If every coercion that can reach this call is inside the bundle,
//! the reachable `Self` types are a finite enumerated set and the obligation is a
//! decidable CASE SPLIT over them. Quantifies over the VALUE FLOW into one
//! receiver, not over the impl set, so it needs no seal and no whole-program bit
//! — which is what makes it usable from an rlib. Φ is FALSE for
//! `fmt::Write::write_str` (std's private `Adapter` impl forwards to an arbitrary
//! user `io::Write`), so declaring it would be a false promise of exactly the kind
//! `EXACT_TOTAL` membership is — C-UNIVERSAL can never serve that trait.
//!
//! MEASURED 2026-08-19, and this header used to say C-FLOW therefore serves it:
//! it no longer does, in the one shape anybody writes. `core::fmt::write` dispatches
//! each argument through a FUNCTION POINTER taking `&mut Formatter<'_>`, and
//! `Formatter` holds `buf: &'a mut dyn Write` in a FIELD such a callee could
//! overwrite — so `fmt::Write` is POISONED in every bundle containing a
//! `write!`/`format!`. That channel was invisible only because
//! `dyn_principals_in_ty` decomposed an ADT through its generic arguments alone,
//! which is the fail-open closed on that function. The shape stays verifiable
//! through the SIBLING `write_fmt` reduction;
//! `dyn_dispatch_reliance_cflow_concrete_sink.rs` records which lane carries it
//! and what going red there would mean.
//!
//! ## Why bundle-local coercion enumeration is complete
//!
//! Let `Bundle` be the functions lowered for root `f`, with every call from a
//! bundled body to a non-bundled one modeled fail-closed (`Assert(false)` +
//! havoc). Claim: on any CHC derivation that reaches a virtual site in `Bundle`
//! WITHOUT traversing a fail-closed edge, the receiver's vtable was built by a
//! coercion in `Bundle`.
//!
//! * A non-root bundled body is entered only through a modeled call edge, and
//!   those originate in `Bundle`. A real execution that enters it from an
//!   unbundled frame had to cross a fail-closed edge first, and `f` does not
//!   verify along that path anyway.
//! * A `dyn T` returned by an absent callee is `Undef`, and that path already
//!   carries the callee's `Assert(false)`.
//! * The remaining ways in are the ROOT's own parameters/return place and
//!   constants/statics of `dyn`-bearing type. Both POISON the trait here.
//!
//! So the enumeration is complete exactly when nothing poisons the trait, and
//! poisoning is what every unhandled shape does.
//!
//! ## The discharge channel is a STRING, and that string is MANY-TO-ONE
//!
//! Read this before touching the decision loop. Neither certificate above is
//! what the bridge consumes: it consumes `site.call_key`, the
//! `trust_mir_extract::func_operand_name` of the call, and drops an absent-callee
//! row when `dyn_contract_total_callees` contains that STRING. The string is not
//! an injective callee identity inside one crate — `direct_call_def_path`
//! disambiguates only duplicate CRATE names, and def paths omit `DefPathData`
//! disambiguators — so two block-scoped `trait Tick` in two blocks of one
//! function give two DIFFERENT vtables ONE key.
//!
//! MEASURED, and this is why the loop below groups: an earlier revision did
//! `out.insert(site.call_key.clone())` PER SITE, so a provable block's site
//! inserted a key that also named the next block's `panic!()` target — whose own
//! case split had already, correctly, DECLINED. Compiled and run, that program
//! was proved panic-free and then panicked. Two gates close it, and both are
//! properties of the KEY rather than of this certificate:
//!
//! * every site under a key must discharge, or the key is not inserted;
//! * [`CallKeyLedger`] refuses any key that ALSO names a bundled call this rule
//!   did not certify — including one the sibling `write_fmt` reduction owns.
//!
//! `tests/ui/trust/dyn_dispatch_reliance_key_alias_*.rs` pin all three shapes.
//!
//! ## Why a bundled-but-unproved target may NOT serve the case split
//!
//! Tempting and wrong: "the target body is in the bundle, so its obligations are
//! in the same conjunction." They are — but the target is reachable in the CHC
//! ONLY through the very virtual edge being discharged. Drop that edge and the
//! target's own obligations are never exercised: the discharge would prove
//! itself. Every case-split member therefore needs an INDEPENDENT verdict, which
//! is `trust_proof_results` on its own body — the same evidence rung 2 requires.
//!
//! ## Safety only
//!
//! Φ-reliance and C-FLOW discharge CALL obligations. A call instruction is not a
//! panic instruction, so the innermost frame of any panicking execution raised it
//! from its own body, which its own proof covered without appeal to either
//! certificate. That argument takes the innermost frame in one step and never
//! inducts on call depth, so forwarding impls (`impl<W: Write + ?Sized> Write for
//! &mut W`) are not circular — and it fails outright for termination, which is
//! why neither certificate may ever be extended to total correctness.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::{
    BasicBlockData, Body, CastKind, Operand, Place, RETURN_PLACE, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, Mutability, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::Spanned;
use rustc_span::def_id::DefId;

use super::static_str_write_fmt::StaticStrWriteFmtFacts;
use super::{
    DYN_SUMMARY_IN_PROGRESS, item_has_trust_attr, item_has_trust_skip_attr,
    optimized_mir_query_would_cycle, trait_panic_free,
};

thread_local! {
    /// Roots whose reliance decision is currently being computed.
    ///
    /// `dyn_target_is_verified_panic_free` FORCES a verdict for each case-split
    /// member, and that member's own verification can reach a `dyn` site whose
    /// case split names this root back. Left unguarded that is a
    /// `trust_proof_results` query cycle, which aborts compilation outright — a
    /// hard failure, not a conservative one. Re-entry therefore declines, which
    /// keeps the site's obligation. `def_id == root_def_id` alone does not cover
    /// it: the cycle can be indirect (A's target is B, B's target is A).
    static RELIANCE_IN_PROGRESS: std::cell::RefCell<FxHashSet<DefId>> =
        std::cell::RefCell::new(FxHashSet::default());
}

/// RAII ownership of one [`RELIANCE_IN_PROGRESS`] entry.
struct RelianceGuard(DefId);

impl RelianceGuard {
    fn enter(root_def_id: DefId) -> Option<Self> {
        RELIANCE_IN_PROGRESS
            .with(|set| set.borrow_mut().insert(root_def_id))
            .then_some(Self(root_def_id))
    }
}

impl Drop for RelianceGuard {
    fn drop(&mut self) {
        RELIANCE_IN_PROGRESS.with(|set| {
            set.borrow_mut().remove(&self.0);
        });
    }
}

/// Most distinct `Self` types one trait may accumulate before C-FLOW gives up.
/// A case split is only a proof if every branch is actually checked; past this
/// the analysis declines rather than spend the budget, which is the fail-closed
/// direction (the site keeps its obligation).
const MAX_ENUMERATED_SELF_TYPES: usize = 16;

/// Pointer layers peeled when matching an `Unsize` source against its target.
const MAX_POINTER_PEEL: usize = 4;

/// Type nodes [`dyn_principals_in_ty`] may visit before it reports the REST of
/// the type as unexamined (`opaque`), which refuses C-FLOW for the whole bundle.
///
/// Raised from 256 when that walk started descending into ADT FIELDS: a field
/// walk reaches a great deal more of a real type than its generic arguments do,
/// and exhausting this budget is not one site's decline but a bundle-wide
/// refusal. The visited set keeps the common cases far below it — what remains
/// is genuinely distinct types.
///
/// Not interchangeable with that visited set, which is why both exist. A
/// polymorphically recursive `struct P<T> { next: Box<P<(T, T)>> }` reaches
/// infinitely many DISTINCT types; no set of seen types bounds it, and only a
/// budget terminates the walk.
const MAX_CARRIER_WALK_FUEL: u32 = 4096;

/// One `InstanceKind::Virtual` call site, keyed by the EXACT identity the bridge
/// will see. Reconstructing it from a `DefId` is not good enough: extraction puts
/// instantiated generic arguments and duplicate-crate disambiguation in this
/// string, and a shorter spelling silently misses the bridge's call row.
struct VirtualCallSite<'tcx> {
    call_key: String,
    /// The TRAIT method (the vtable slot's declaration), not any impl.
    method_def_id: DefId,
    /// The virtual instance's arguments; `args[0]` is the erased `Self`.
    args: ty::GenericArgsRef<'tcx>,
}

/// Which lane — if either — CERTIFIED each bundled call that renders to one
/// `func_operand_name`.
///
/// GATE 0, shared by both rules in this bundle. The bridge discharges an
/// absent-callee row by testing `dyn_contract_total_callees.contains(callee)`
/// against `trust_mir_extract::func_operand_name` of the call, and that string
/// is MANY-TO-ONE inside a single crate: `direct_call_def_path` disambiguates
/// only duplicate CRATE names, and def paths omit `DefPathData` disambiguators,
/// so two block-scoped definitions of one function render one key (the finding
/// is written up on `direct_call_def_path` itself, and the exploit that forced
/// it is in `static_str_write_fmt`'s header).
///
/// Inserting a key therefore discharges EVERY bundled call that renders to it,
/// never the one site that happened to be examined. So a lane may insert a key
/// only when every call under it is a certified site OF THAT LANE — one lane's
/// evidence is not evidence for the other's, any more than one site's is for its
/// neighbour's.
#[derive(Default, Clone, Copy)]
struct CallKeyKinds {
    /// Some call under this key is an `InstanceKind::Virtual` site the `dyn`
    /// rule examines.
    dyn_site: bool,
    /// Some call under this key is a certified `write_fmt` reduction site.
    write_fmt_site: bool,
    /// Some call under this key was certified by NEITHER lane.
    uncertified: bool,
}

/// Every bundled call's callee key, classified by the lane that certified it.
///
/// Populated UNCONDITIONALLY from the one walk that sees every bundled body: no
/// attempt is made to predict which keys can alias. A pre-filter would be a
/// textual argument about `func_operand_name`'s output, which is exactly the
/// kind of reasoning this campaign keeps refuting, and it would go stale the
/// first time that renderer changes. The only cost of recording a key that could
/// never have collided is a discharge declined.
#[derive(Default)]
pub(super) struct CallKeyLedger {
    by_key: FxHashMap<String, CallKeyKinds>,
}

impl CallKeyLedger {
    fn record_dyn_site(&mut self, key: String) {
        self.by_key.entry(key).or_default().dyn_site = true;
    }

    fn record_write_fmt_site(&mut self, key: String) {
        self.by_key.entry(key).or_default().write_fmt_site = true;
    }

    fn record_uncertified(&mut self, key: String) {
        self.by_key.entry(key).or_default().uncertified = true;
    }

    /// May the `dyn` reliance rule discharge `key`?
    ///
    /// A key this walk never recorded answers NO: a site whose key is missing
    /// from the ledger is a call the classification did not reach, and an
    /// unclassified call is exactly the one that could collect a neighbour's
    /// proof.
    fn only_dyn_sites(&self, key: &str) -> bool {
        self.by_key
            .get(key)
            .is_some_and(|kinds| kinds.dyn_site && !kinds.write_fmt_site && !kinds.uncertified)
    }

    /// May the `write_fmt` reduction discharge `key`? Same rule, other lane.
    pub(super) fn only_write_fmt_sites(&self, key: &str) -> bool {
        self.by_key
            .get(key)
            .is_some_and(|kinds| kinds.write_fmt_site && !kinds.dyn_site && !kinds.uncertified)
    }
}

/// Everything the `dyn` reliance rule reads, gathered over ONE verification
/// bundle while its bodies are in hand.
#[derive(Default)]
pub(crate) struct DynDispatchBundleFacts<'tcx> {
    /// Region-erased principal trait ref (the FULL instantiation, `Self`
    /// erased) -> concrete `Self` types unsize-coerced to a trait object with
    /// exactly that instantiation (or to a subtrait object whose vtable embeds
    /// it) anywhere in the bundle. Keyed by `ExistentialTraitRef`, never bare
    /// `DefId`: a generic trait has ONE `DefId` but many vtable types, and a
    /// shared bucket handed a `dyn Fn(&CStr)` closure to a
    /// `<dyn FnMut(&OnceState)>::call_mut` site's case split, where it burned
    /// enumeration budget and its guaranteed-failing resolution vetoed the
    /// provable candidate's discharge through the first-failure short-circuit.
    coerced: FxHashMap<ty::ExistentialTraitRef<'tcx>, Vec<Ty<'tcx>>>,
    /// Traits for which a vtable of UNKNOWN origin can reach this bundle. A
    /// poisoned trait can never be served by C-FLOW. Deliberately `DefId`-coarse
    /// while `coerced` is instantiation-keyed: refusing EVERY instantiation of a
    /// trait somebody smuggled one vtable of is the fail-closed direction, and
    /// poison sources (root params, casts, constants) don't warrant precision.
    poisoned: FxHashSet<DefId>,
    /// A type this analysis could not decompose reached the bundle, so it cannot
    /// even NAME which traits to poison. C-FLOW declines for every trait.
    ///
    /// This is the fail-closed backstop for `dyn_principals_in_ty`'s catch-all: a
    /// type kind nobody enumerated (a projection that normalizes to a trait
    /// object, a type parameter in a polymorphic body, a variant a future rustc
    /// adds) must never silently read as "carries no vtable".
    opaque_carrier_seen: bool,
    virtual_sites: Vec<VirtualCallSite<'tcx>>,
    /// Bodies actually folded into this bundle. Membership is what decides
    /// whether a call's outputs were witnessed, so it is recorded rather than
    /// predicted from crate names and MIR availability.
    observed_bodies: FxHashSet<DefId>,
    /// `(callee, traits its outputs could carry)` for every call site. Resolved
    /// against `observed_bodies` at decision time, because a call is walked
    /// before the closure has finished deciding what it bundles.
    deferred_output_poisons: Vec<(DefId, DynCarriers)>,
    /// The `fmt::Write::write_fmt` reduction's own facts. A SEPARATE certificate
    /// with its own soundness argument (see that module), gathered here only
    /// because this walk is the one place every bundled body — including the
    /// B-lane's instantiated foreign ones — is in hand, and duplicating the walk
    /// would duplicate the seam where a missed body becomes a missed decline.
    static_str_write_fmt: StaticStrWriteFmtFacts<'tcx>,
    /// GATE 0 for BOTH lanes: what every bundled call renders to, and which lane
    /// certified it. See [`CallKeyLedger`].
    call_keys: CallKeyLedger,
}

impl<'tcx> DynDispatchBundleFacts<'tcx> {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Poison `trait_def_id` and every SUPERTRAIT of it: an unknown `dyn Sub`
    /// upcasts to an unknown `dyn Super`, so the unknown propagates upward.
    fn poison(&mut self, tcx: TyCtxt<'tcx>, trait_def_id: DefId) {
        for did in transitive_supertraits(tcx, trait_def_id) {
            self.poisoned.insert(did);
        }
    }

    /// Record `self_ty` as a possible dispatch target for the trait object
    /// `principal` describes and for every supertrait slot the same vtable
    /// serves — each keyed by its FULL instantiation. One vtable serves the
    /// principal and its supertraits AT THE PRINCIPAL'S OWN ARGUMENTS: the
    /// coercion to `dyn Sub<u8>` serves `<dyn Super<u8>>` slots and no other
    /// `Super` instantiation, so propagating by identity `DefId` was wrong in
    /// both directions (it fed sites of sibling instantiations, and it filed
    /// the supertrait entry under identity args instead of the coercion's).
    fn record(
        &mut self,
        tcx: TyCtxt<'tcx>,
        principal: ty::PolyExistentialTraitRef<'tcx>,
        self_ty: Ty<'tcx>,
    ) {
        for key in coercion_dyn_keys(tcx, principal, self_ty) {
            let entry = self.coerced.entry(key).or_default();
            if !entry.contains(&self_ty) {
                entry.push(self_ty);
            }
        }
    }

    /// Poison every trait object principal a value of `ty` could carry.
    fn poison_dyn_in_ty(&mut self, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, source: PoisonSource<'_>) {
        self.poison_carriers(tcx, &dyn_principals_in_ty(tcx, ty), source);
    }

    /// Apply a carrier set, naming WHERE it came from for the probe.
    ///
    /// `source` is probe-only and never influences a decision. It exists because
    /// the field walk made poison the ROUTINE decline reason where vacuity used
    /// to be: `site_discharges` can now say "trait `core::fmt::Write` poisoned"
    /// for a bundle in which nothing is obviously unknown, and the reader's next
    /// question — which entry point admitted the unknown vtable — had no answer
    /// anywhere in the output. This module already holds that a guard whose
    /// firing is indistinguishable from an ordinary decline cannot be watched
    /// (see `target_decline_reason`); the same standard applies to the poison
    /// that fires before any target is examined.
    fn poison_carriers(
        &mut self,
        tcx: TyCtxt<'tcx>,
        carriers: &DynCarriers,
        source: PoisonSource<'_>,
    ) {
        if !carriers.is_empty() && probe_enabled() {
            let named: Vec<String> = carriers
                .principals
                .iter()
                .map(|&did| with_no_trimmed_paths!(tcx.def_path_str(did)))
                .collect();
            eprintln!(
                "TRUST_DYN_RELIANCE_PROBE:   poison from {source}: {}{}",
                if named.is_empty() { "(none)".to_string() } else { named.join(", ") },
                if carriers.opaque { " [+ UNDECOMPOSABLE carrier]" } else { "" },
            );
        }
        if carriers.opaque {
            self.opaque_carrier_seen = true;
        }
        for &principal in &carriers.principals {
            self.poison(tcx, principal);
        }
    }

    /// Fold one bundled body into the facts.
    ///
    /// `is_root` marks the function whose verdict this bundle produces: only its
    /// signature is an uncontrolled entry point for a `dyn` value (every other
    /// bundled body is entered through a modeled call edge — see the module
    /// docs). `typing_env` must be the environment the body's own call sites
    /// resolve in: `post_analysis` for a body taken as-is, and
    /// `fully_monomorphized` for one the B-lane instantiated.
    pub(crate) fn observe_bundle_body(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        is_root: bool,
    ) {
        self.observed_bodies.insert(body.source.def_id());

        if is_root {
            // The root's parameters and return place carry `dyn` values chosen
            // by a caller this compilation cannot see. That is precisely the
            // `Display::fmt(&self, f: &mut Formatter)` shape: `f.buf` is a
            // `&mut dyn Write` supplied from outside, so `fmt::Write` is
            // poisoned here and the site stays fail-closed — the honest verdict,
            // since such a body really can panic through a panicking sink.
            for local in body.args_iter() {
                self.poison_dyn_in_ty(tcx, body.local_decls[local].ty, PoisonSource::RootParam);
            }
            self.poison_dyn_in_ty(tcx, body.local_decls[RETURN_PLACE].ty, PoisonSource::RootReturn);
        }

        for (block_id, block) in body.basic_blocks.iter_enumerated() {
            for stmt in &block.statements {
                let StatementKind::Assign(assign) = &stmt.kind else { continue };
                let (place, rvalue) = &**assign;
                match rvalue {
                    Rvalue::Cast(
                        CastKind::PointerCoercion(PointerCoercion::Unsize, _),
                        operand,
                        target_ty,
                    ) => {
                        let source_ty = operand.ty(&body.local_decls, tcx);
                        self.observe_unsize(tcx, source_ty, *target_ty);
                    }
                    // Any OTHER cast that lands on a `dyn`-bearing type may build a
                    // vtable this analysis did not witness (`transmute`, raw
                    // pointer reinterpretation). Refuse the trait outright; forged
                    // vtables belong to the unsafe lane, not to this rule. The one
                    // ENUMERATED exception is an element projection — see
                    // `is_array_element_projection`.
                    Rvalue::Cast(_, operand, target_ty) => {
                        let source_ty = operand.ty(&body.local_decls, tcx);
                        if !is_array_element_projection(source_ty, *target_ty) {
                            self.poison_dyn_in_ty(tcx, *target_ty, PoisonSource::CastTarget);
                        }
                    }
                    // A thread-local handle names storage no body in this bundle
                    // initialized, so a vtable reached through it has no witnessed
                    // origin.
                    Rvalue::ThreadLocalRef(_) => {
                        let place_ty = place.ty(&body.local_decls, tcx).ty;
                        self.poison_dyn_in_ty(tcx, place_ty, PoisonSource::ThreadLocal);
                    }
                    _ => {}
                }
            }

            // Constants — including the `&'static` handle by which a `static X:
            // &dyn T` is read — carry vtables minted outside any body. Their TYPE
            // is enough to refuse.
            let mut constant_carriers = DynCarriers::default();
            for_each_constant_ty(block, |ty| {
                constant_carriers.merge(dyn_principals_in_ty(tcx, ty))
            });
            self.poison_carriers(tcx, &constant_carriers, PoisonSource::Constant);

            // A `TailCall` has no destination place — it returns into the
            // caller's — so only its `&mut` arguments can hand a vtable back.
            //
            // EVERY call below is also classified into gate 0's ledger, on
            // whichever arm it leaves by. That is the point of the ledger: a call
            // this walk fails to classify is a call that could silently collect a
            // neighbour's proof through an aliased key.
            //
            // `is_plain_call` separates the two call terminators only because
            // `TerminatorKind::Call` is the exact set the `write_fmt` reduction
            // has always certified over; keeping it exact is what makes this
            // walk's CERTIFIED-site set byte-identical to the separate walk it
            // replaces. A `TailCall` is therefore uncertified — the fail-closed
            // answer, and the one this rule already gave it.
            let (func, args, destination, is_plain_call) = match &block.terminator().kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    (func, &**args, Some(destination), true)
                }
                TerminatorKind::TailCall { func, args, .. } => (func, &**args, None, false),
                _ => continue,
            };
            // What a call can hand BACK: its destination, and any `&mut`/`*mut`
            // argument whose pointee NESTS a trait object (an out-param the
            // callee could overwrite with a vtable of its own). Passing a
            // `dyn T` IN is harmless — that value's provenance is already
            // accounted for — and a `&mut dyn T` cannot be re-pointed, since an
            // unsized place is not assignable.
            let output_traits = self.call_output_traits(tcx, body, destination, args);
            let Some((callee_def_id, gen_args)) = func.const_fn_def() else {
                // An INDIRECT call (fn pointer / erased callable): no body to
                // witness, ever.
                self.call_keys.record_uncertified(trust_mir_extract::func_operand_name(tcx, func));
                self.poison_carriers(tcx, &output_traits, PoisonSource::IndirectCall);
                continue;
            };
            match ty::Instance::try_resolve(tcx, typing_env, callee_def_id, gen_args) {
                Ok(Some(instance)) => {
                    if let ty::InstanceKind::Virtual(method_def_id, _slot) = instance.def {
                        let call_key = trust_mir_extract::func_operand_name(tcx, func);
                        self.call_keys.record_dyn_site(call_key.clone());
                        self.virtual_sites.push(VirtualCallSite {
                            call_key,
                            method_def_id,
                            args: instance.args,
                        });
                    } else if is_plain_call
                        && self
                            .static_str_write_fmt
                            .observe_call(tcx, body, typing_env, block_id, func, args)
                    {
                        self.call_keys
                            .record_write_fmt_site(trust_mir_extract::func_operand_name(tcx, func));
                    } else {
                        self.call_keys
                            .record_uncertified(trust_mir_extract::func_operand_name(tcx, func));
                    }
                    // A callee whose body is NOT in this bundle may hand back a
                    // `dyn` value of its own making. Most such calls also carry an
                    // `Assert(false)` that fails the path closed on its own, but
                    // the discharge arms (ABI-total, the total-callee allowlists,
                    // the `?` desugar) do not — so refuse on the signature rather
                    // than reason about which arm claimed the call. DEFERRED:
                    // whether the body ends up bundled is not decided yet.
                    if !output_traits.is_empty() {
                        self.deferred_output_poisons.push((instance.def_id(), output_traits));
                    }
                }
                // Unresolved dispatch: the target is unknown, so its outputs are.
                _ => {
                    self.call_keys
                        .record_uncertified(trust_mir_extract::func_operand_name(tcx, func));
                    self.poison_carriers(tcx, &output_traits, PoisonSource::UnresolvedCall);
                }
            }
        }
    }

    /// The traits a call could hand BACK. Pure — poisoning is deferred until the
    /// bundle membership of the callee is known.
    fn call_output_traits(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        destination: Option<&Place<'tcx>>,
        args: &[Spanned<Operand<'tcx>>],
    ) -> DynCarriers {
        let mut out = DynCarriers::default();
        if let Some(destination) = destination {
            out.merge(dyn_principals_in_ty(tcx, destination.ty(&body.local_decls, tcx).ty));
        }
        for arg in args {
            let arg_ty = arg.node.ty(&body.local_decls, tcx);
            let pointee = match arg_ty.kind() {
                ty::Ref(_, inner, Mutability::Mut) => *inner,
                ty::RawPtr(inner, Mutability::Mut) => *inner,
                _ => continue,
            };
            // `&mut dyn T` itself cannot be re-pointed, so only a NESTED trait
            // object is an out-channel.
            if matches!(pointee.kind(), ty::Dynamic(..)) {
                continue;
            }
            out.merge(dyn_principals_in_ty(tcx, pointee));
        }
        out
    }

    /// Apply the deferred call-output poisons now that bundle membership is
    /// final: a callee whose body this bundle never walked could have produced a
    /// vtable nobody witnessed.
    fn settle_deferred_output_poisons(&mut self, tcx: TyCtxt<'tcx>) {
        let deferred = std::mem::take(&mut self.deferred_output_poisons);
        for (callee, principals) in deferred {
            if self.observed_bodies.contains(&callee) {
                continue;
            }
            // Naming the callee costs a `def_path_str` per deferred entry, so it
            // is built only when someone is reading. `with_no_trimmed_paths!`
            // is not optional here: bare `def_path_str` arms `trimmed_def_paths`
            // and ICEs when the compilation goes on to emit no diagnostic, which
            // is exactly the all-discharged run this instrument exists to watch.
            let name = if probe_enabled() {
                with_no_trimmed_paths!(tcx.def_path_str(callee))
            } else {
                String::new()
            };
            self.poison_carriers(tcx, &principals, PoisonSource::UnbundledCallee(&name));
        }
    }

    /// One `Unsize` coercion. Either it names a concrete source type — the whole
    /// point of the analysis — or it refuses the traits it produces.
    fn observe_unsize(&mut self, tcx: TyCtxt<'tcx>, source_ty: Ty<'tcx>, target_ty: Ty<'tcx>) {
        let carriers = dyn_principals_in_ty(tcx, target_ty);
        if carriers.opaque {
            // A coercion built SOMETHING this analysis cannot decompose. It may
            // be a vtable for a trait we cannot even name, so nothing may rely on
            // an enumeration in this bundle.
            if probe_enabled() {
                eprintln!(
                    "TRUST_DYN_RELIANCE_PROBE:   poison from an `Unsize` coercion whose TARGET \
                     is undecomposable: [UNDECOMPOSABLE carrier]"
                );
            }
            self.opaque_carrier_seen = true;
            return;
        }
        if carriers.principals.is_empty() {
            // `&[u8; N]` -> `&[u8]` and friends: no trait object anywhere in the
            // target, so nothing to say. The ELEMENT type can still carry one —
            // that is `UnsizeShape::Length` below, not this early return.
            return;
        }
        match classify_unsize(source_ty, target_ty) {
            // `[T; N]` -> `[T]`: this coercion turns pointer metadata into a
            // LENGTH and mints no vtable. Any `dyn` inside the element type was
            // built by its own `Unsize` earlier in this same body and is already
            // in the enumeration, so poisoning here would discard an answer that
            // succeeded.
            //
            // Not a corner case: this is `derive(Debug)` above five fields. rustc
            // switches from `debug_struct_field{1..5}_finish`, which passes each
            // `&dyn Debug` as its own argument, to
            // `debug_struct_fields_finish(.., values: &[&dyn Debug])`, which needs
            // `&[&dyn Debug; N]` -> `&[&dyn Debug]`. Reading that as a vtable
            // coercion refused a six-field struct while discharging a five-field
            // one — `dyn_dispatch_reliance_derive_debug_field_count.rs` pins it.
            UnsizeShape::Length => {}
            // A type parameter survives here when a POLYMORPHIC body is bundled
            // as-is. It names no impl, so it cannot serve a case split.
            //
            // Only the PEELED principal mints a vtable here. Any other `dyn`
            // nested elsewhere in the target was built by its own earlier
            // coercion (already recorded) or arrived by a route that poisoned
            // it — the same argument `UnsizeShape::Length` rests on.
            UnsizeShape::Vtable { source, principal } if !source.has_non_region_param() => {
                self.record(tcx, principal, source);
            }
            _ => self.poison_carriers(tcx, &carriers, PoisonSource::UnclassifiableUnsize),
        }
    }

    /// Decide every virtual site and write the discharged call identities into
    /// `out`. A site absent from `out` keeps the bridge's fail-closed
    /// absent-callee obligation, byte-for-byte as before this rule existed.
    pub(crate) fn resolve_reliance(
        &mut self,
        tcx: TyCtxt<'tcx>,
        root_def_id: DefId,
        out: &mut FxHashSet<String>,
    ) {
        self.settle_deferred_output_poisons(tcx);
        // A/B measurement switch, DEFAULT ON. Setting it restores the exact
        // pre-rule behavior: an empty set means every `dyn` call keeps its
        // fail-closed absent-callee obligation. There is no setting of this
        // variable that admits anything, downgrades a policy, or turns an
        // obligation into an assumption — the only direction available is LESS
        // proof. It exists so a before/after can be measured with ONE binary
        // instead of two builds, which is the difference between a reported
        // number and a claimed one.
        let dyn_rule_enabled = std::env::var_os("TRUST_NO_DYN_RELIANCE").is_none();
        let probe = std::env::var_os("TRUST_DYN_RELIANCE_PROBE").is_some();
        if (self.virtual_sites.is_empty() || !dyn_rule_enabled)
            && self.static_str_write_fmt.is_empty()
        {
            return;
        }
        // Re-entrant: some case-split member's verification reached back here.
        // Decline the whole decision rather than risk a query cycle. Held across
        // BOTH rules — the `write_fmt` reduction forces the same
        // `trust_proof_results` verdicts the case split does.
        let Some(_guard) = RelianceGuard::enter(root_def_id) else { return };
        if dyn_rule_enabled {
            // Group by the identity the discharge channel is keyed by — the SAME
            // grouping the `write_fmt` lane does, for the same reason. Inserting
            // `site.call_key` discharges every bundled call that renders to that
            // string, so the decision has to be all-or-nothing over the whole
            // group; a per-site insert let one block-scoped trait's provable site
            // discharge an identically-keyed panicking site in the next block.
            //
            // First-appearance order, not hash order, so the probe reads in
            // source order and two runs of one program print the same lines.
            let mut order: Vec<&str> = Vec::new();
            let mut by_callee: FxHashMap<&str, Vec<&VirtualCallSite<'tcx>>> = FxHashMap::default();
            for site in &self.virtual_sites {
                let key = site.call_key.as_str();
                let group = by_callee.entry(key).or_default();
                if group.is_empty() {
                    order.push(key);
                }
                group.push(site);
            }
            for call_key in order {
                let sites = &by_callee[call_key];
                let count = sites.len();
                // GATE 0. A key that also names a bundled call NO lane certified
                // — or one the OTHER lane certified — is refused outright: the
                // discharge cannot be aimed at a subset of the calls the string
                // covers.
                if !self.call_keys.only_dyn_sites(call_key) {
                    if probe {
                        eprintln!(
                            "TRUST_DYN_RELIANCE_PROBE: site={call_key} ({count} site(s)) \
                             => kept (callee key ALIASES a bundled call this rule did not certify)"
                        );
                    }
                    continue;
                }
                let mut all_discharged = true;
                for site in sites {
                    let discharged = self.site_discharges(tcx, site, root_def_id, probe);
                    if probe {
                        // `def_path_str` arms `trimmed_def_paths`, which ICEs if the
                        // compilation then emits NO diagnostic. A probe that discharges
                        // everything emits none — so the instrument crashed in exactly the
                        // success case it exists to observe.
                        //
                        // `({count} site(s))` is what makes an ALIAS visible: two
                        // distinct definitions sharing one key print one group of
                        // two, and that is the only place the collision surfaces.
                        with_no_trimmed_paths!(eprintln!(
                            "TRUST_DYN_RELIANCE_PROBE: site={} ({count} site(s)) method={} => {}",
                            site.call_key,
                            tcx.def_path_str(site.method_def_id),
                            if discharged { "DISCHARGED" } else { "kept" },
                        ));
                    }
                    // Every site is decided, not short-circuited: the probe has to
                    // be able to show WHICH member of an aliased group refused.
                    all_discharged &= discharged;
                }
                if all_discharged {
                    out.insert(call_key.to_string());
                } else if probe && count > 1 {
                    eprintln!(
                        "TRUST_DYN_RELIANCE_PROBE: site={call_key} ({count} site(s)) \
                         => kept (not every site under this callee key discharges)"
                    );
                }
            }
        }
        self.static_str_write_fmt.resolve_reliance(tcx, root_def_id, out, probe, &self.call_keys);
    }

    fn site_discharges(
        &self,
        tcx: TyCtxt<'tcx>,
        site: &VirtualCallSite<'tcx>,
        root_def_id: DefId,
        probe: bool,
    ) -> bool {
        let Some(trait_def_id) = tcx.trait_of_assoc(site.method_def_id) else { return false };

        // ---- C-UNIVERSAL -------------------------------------------------
        if dyn_call_relies_on_trait_panic_free_contract(tcx, site.method_def_id) {
            if probe {
                with_no_trimmed_paths!(eprintln!(
                    "TRUST_DYN_RELIANCE_PROBE:   C-UNIVERSAL trait={}",
                    tcx.def_path_str(trait_def_id)
                ));
            }
            return true;
        }

        // ---- C-FLOW ------------------------------------------------------
        if self.opaque_carrier_seen {
            if probe {
                eprintln!(
                    "TRUST_DYN_RELIANCE_PROBE:   C-FLOW declined: an undecomposable type reached \
                     this bundle, so no trait's vtable set can be bounded"
                );
            }
            return false;
        }
        if self.poisoned.contains(&trait_def_id) {
            if probe {
                with_no_trimmed_paths!(eprintln!(
                    "TRUST_DYN_RELIANCE_PROBE:   C-FLOW declined: trait {} poisoned",
                    tcx.def_path_str(trait_def_id)
                ));
            }
            return false;
        }
        let Some(self_tys) = self.coerced.get(&site_dyn_key(tcx, trait_def_id, site)) else {
            // No coercion, no poison: the site is unreachable in this bundle.
            // Vacuity must stay VISIBLE as the fatal row, never become a silent
            // green — the same rule rung 2 applies to an empty impl set.
            if probe {
                eprintln!("TRUST_DYN_RELIANCE_PROBE:   C-FLOW declined: no coercion (vacuous)");
            }
            return false;
        };
        if self_tys.is_empty() || self_tys.len() > MAX_ENUMERATED_SELF_TYPES {
            return false;
        }
        for &self_ty in self_tys {
            let Some(target) = resolve_virtual_target(tcx, site, self_ty) else {
                if probe {
                    // `Ty`'s Display goes through the same printer, so it arms the
                    // assertion too — not only `def_path_str`.
                    with_no_trimmed_paths!(eprintln!(
                        "TRUST_DYN_RELIANCE_PROBE:   C-FLOW declined: {self_ty} unresolved"
                    ));
                }
                return false;
            };
            if !dyn_target_is_verified_panic_free(tcx, target, root_def_id) {
                if probe {
                    // Name WHICH conjunct declined. They are different refusals
                    // with different repairs, and a falsification run has to be
                    // able to see which one fired — a guard whose firing is
                    // indistinguishable from an ordinary decline cannot be watched.
                    let reason = target_decline_reason(tcx, target, root_def_id);
                    with_no_trimmed_paths!(eprintln!(
                        "TRUST_DYN_RELIANCE_PROBE:   C-FLOW declined: target {} {reason}",
                        tcx.def_path_str(target.def_id())
                    ));
                }
                return false;
            }
        }
        if probe {
            eprintln!("TRUST_DYN_RELIANCE_PROBE:   C-FLOW admitted {} target(s)", self_tys.len());
        }
        true
    }
}

/// C-UNIVERSAL, stated for a `dyn` receiver.
///
/// DELEGATES to `trait_panic_free`'s certificate rather than restating it. The
/// certificate transfers verbatim because both call shapes quantify over the SAME
/// set: every `X: T` can be coerced to `dyn T`, and nothing else can — so "every
/// impl of `T::m` discharged Φ, and no impl can be added" is exactly as strong a
/// premise for an erased receiver as for a `T`-bounded type parameter.
///
/// Delegating is not tidiness. An earlier draft of this function re-derived what
/// looked like the same three conjuncts (Φ declared, local trait, whole-program)
/// and silently DROPPED the fourth: a specializing `default fn` in an impl means
/// the body that runs need not be the one the per-impl discharge checked. The
/// duplicate compiled, read plausibly, and would have credited a specialized
/// dispatch target nobody proved. One predicate, one place.
fn dyn_call_relies_on_trait_panic_free_contract(tcx: TyCtxt<'_>, method_def_id: DefId) -> bool {
    trait_panic_free::generic_call_relies_on_panic_free_contract(tcx, method_def_id)
}

/// Resolve the vtable slot for one enumerated `Self` type.
///
/// Returns `None` unless resolution names a CONCRETE body: a residual `Virtual`
/// (dyn-to-dyn), an `Ok(None)` left open by specialization, or any error is a
/// target this case split cannot check.
fn resolve_virtual_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    site: &VirtualCallSite<'tcx>,
    self_ty: Ty<'tcx>,
) -> Option<ty::Instance<'tcx>> {
    let mut args: Vec<ty::GenericArg<'tcx>> = site.args.iter().collect();
    // `args[0]` of a trait method is `Self` — here the erased `dyn T`.
    *args.first_mut()? = self_ty.into();
    let args = tcx.mk_args(&args);
    if args.has_non_region_param() {
        return None;
    }
    // A candidate coerced to a DIFFERENT instantiation of this generic trait
    // must not reach selection — see `self_ty_matches_site_instantiation`.
    if !self_ty_matches_site_instantiation(tcx, site, self_ty, args) {
        return None;
    }
    let instance = ty::Instance::try_resolve(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        site.method_def_id,
        args,
    )
    .ok()??;
    match instance.def {
        ty::InstanceKind::Item(_) => Some(instance),
        _ => None,
    }
}

/// May `self_ty` be handed to `Instance::try_resolve` for this site at all?
///
/// `coerced` is keyed by the full region-erased instantiation, so a candidate
/// from a DIFFERENT instantiation of a generic trait should never reach this
/// site at all. This guard stays anyway, as DEFENSE IN DEPTH: resolution
/// safety must not hinge on the keying, because the failure mode of a missed
/// mismatch is not a wrong verdict but an ICE — one trait, two vtable types
/// (`dyn FnMut(&CStr)` vs `dyn FnMut(&OnceState)`). Such a pair must not reach
/// selection: for the signature-keyed BUILT-IN impls (closures, fn items and
/// fn pointers against the `Fn`/`AsyncFn` families, coroutines against
/// `Coroutine`) selection commits to the candidate by KIND and only then
/// unifies the signature, so the mismatch surfaces as
/// `SelectionError::SignatureMismatch` — which `codegen_select_candidate`
/// treats as a compiler bug (ICE), not as `Unimplemented`. Every other shape
/// reports a mismatch as ordinary `Unimplemented` (a top-level impl that fails
/// to match) or as a nested fulfillment error (core's `&F`/`&mut F` forwarding
/// impls), both of which `try_resolve` already maps to a clean decline.
///
/// Returning `false` declines the candidate, which fails closed: the site
/// keeps its obligation.
fn self_ty_matches_site_instantiation<'tcx>(
    tcx: TyCtxt<'tcx>,
    site: &VirtualCallSite<'tcx>,
    self_ty: Ty<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
) -> bool {
    let Some(trait_def_id) = tcx.trait_of_assoc(site.method_def_id) else { return false };

    // The `Fn`/`AsyncFn` families carry the tupled inputs as the trait's one
    // non-`Self` parameter.
    let fn_family = tcx.fn_trait_kind_from_def_id(trait_def_id).is_some()
        || tcx.async_fn_trait_kind_from_def_id(trait_def_id).is_some();
    let demanded_inputs = if fn_family {
        match args.get(1).and_then(|arg| arg.as_type()) {
            Some(tuple) => Some(tuple),
            // A malformed site names no tuple to check against: refuse.
            None => return false,
        }
    } else {
        None
    };
    // The tupled inputs that `self_ty`'s built-in `Fn`-family impls are keyed
    // by, for the type kinds that have such impls.
    //
    // Late-bound regions are ERASED, not skipped: `skip_binder` left the sig's
    // `for<'a>` regions bound, and a bound region never equals the site's
    // erased one — which declined every candidate whose signature mentions a
    // reference, INCLUDING the matching one, and kept its site closed. The
    // structural mismatch this guard exists for (`(&CStr,)` vs `(&OnceState,)`)
    // survives erasure untouched.
    let offered_inputs = match self_ty.kind() {
        ty::Closure(_, closure_args) => Some(
            tcx.instantiate_bound_regions_with_erased(closure_args.as_closure().sig()).inputs()[0],
        ),
        ty::CoroutineClosure(_, cc_args) => Some(
            tcx.instantiate_bound_regions_with_erased(
                cc_args.as_coroutine_closure().coroutine_closure_sig(),
            )
            .tupled_inputs_ty,
        ),
        ty::FnDef(..) | ty::FnPtr(..) => Some(Ty::new_tup(
            tcx,
            tcx.instantiate_bound_regions_with_erased(self_ty.fn_sig(tcx)).inputs(),
        )),
        _ => None,
    };
    match (demanded_inputs, offered_inputs) {
        // Signature-keyed on both sides: the built-in impl exists exactly for
        // the matching tuple. Regions are erased on BOTH sides — vtable
        // identity never depends on them, and the site's tuple has already
        // been through instance resolution while the closure's has not.
        (Some(demanded), Some(offered)) => {
            tcx.erase_and_anonymize_regions(demanded) == tcx.erase_and_anonymize_regions(offered)
        }
        // A callable against a trait outside the `Fn` families resolves
        // through ordinary impls — except `dyn Coroutine<R>`, whose resume
        // type is a trait parameter and whose built-in candidate is committed
        // by kind too.
        (None, _) => {
            if tcx.lang_items().coroutine_trait() == Some(trait_def_id) {
                if let ty::Coroutine(_, c_args) = self_ty.kind() {
                    let demanded = match args.get(1).and_then(|arg| arg.as_type()) {
                        Some(resume) => resume,
                        None => return false,
                    };
                    return tcx.erase_and_anonymize_regions(demanded)
                        == tcx.erase_and_anonymize_regions(c_args.as_coroutine().resume_ty());
                }
            }
            true
        }
        // An `Fn`-family site with a non-callable candidate: selection has no
        // built-in candidate to commit to, so a mismatch is graceful.
        (Some(_), None) => true,
    }
}

/// Is this case-split member INDEPENDENTLY proved panic-free?
///
/// Independence is the requirement, not a nicety: a body reachable in the CHC
/// only through the edge we are discharging would prove itself (see the module
/// docs). An independent verdict exists only for a body this compilation
/// verified in its own right, which is why a std impl declines here and its site
/// stays fail-closed.
///
/// The evidence bar is `trait_panic_free::body_discharges_panic_freedom`, shared
/// verbatim with Φ's per-impl discharge rather than re-derived. Sharing it is
/// what keeps the two lanes from drifting, and it is what makes this check
/// stronger than a bare `trust_proof_results` summary read: an aggregate summary
/// is not guaranteed to surface an unproved absent-callee or drop-glue row, so a
/// body with an undischarged inner call could otherwise present as
/// "zero obligations" and be credited.
///
/// `pub(super)` so the `fmt::Write::write_fmt` reduction uses THIS bar rather
/// than a second copy of it; a hand-copied evidence ledger is exactly how a
/// soundness conjunct gets silently dropped.
pub(super) fn dyn_target_is_verified_panic_free<'tcx>(
    tcx: TyCtxt<'tcx>,
    target: ty::Instance<'tcx>,
    root_def_id: DefId,
) -> bool {
    let def_id = target.def_id();
    if def_id == root_def_id {
        return false;
    }
    // A `#[trust::skip]` body is UNVERIFIED by user decree and a
    // `#[trust::assume_total]` one is an axiom, not a proof. Either would make
    // the case split a laundering step for the very panic it hides.
    if item_has_trust_skip_attr(tcx, def_id) || item_has_trust_attr(tcx, def_id, "assume_total") {
        return false;
    }
    if !def_id.is_local() {
        return false;
    }
    // A verdict computed under an AUTHORED CLAUSE is conditional, and neither
    // lane that reads this bar can discharge the condition: a `dyn` site has an
    // erased receiver, and the `write_fmt` reduction's caller reaches the target
    // through core frames that are not in the bundle at all. So a conditional
    // verdict must never be read as panic-freedom.
    if body_carries_authored_clause(tcx, def_id) {
        return false;
    }
    // Forcing a verdict for a body whose MIR query would cycle, or whose
    // summaries are already being computed up the stack, aborts compilation or
    // reads half-built state. Both bail fail-closed.
    if optimized_mir_query_would_cycle(tcx, def_id) {
        return false;
    }
    if DYN_SUMMARY_IN_PROGRESS.with(|s| s.borrow().contains(&def_id)) {
        return false;
    }
    if RELIANCE_IN_PROGRESS.with(|set| set.borrow().contains(&def_id)) {
        return false;
    }
    // The shared bar's own last conjunct is the ASSUMPTION-ROOT gate: a body whose
    // verdict rests on a `#[trust::assume_total]`/`#[trust::skip]` callee anywhere
    // in its bundle is proved only CONDITIONALLY, and neither lane can discharge
    // the condition. It lives in the bar rather than here on purpose — the bar has
    // four consumers (Φ's per-impl discharge, this case split, the `write_fmt`
    // reduction, and the drop-glue premise), and a check written here would have
    // covered two of them.
    trait_panic_free::body_discharges_panic_freedom(tcx, def_id).is_ok()
}

/// WHY a target was refused, for the probe. Decision-free: it recomputes the
/// same conjuncts in the same order and never influences a verdict.
///
/// Both lanes render this, so a fired guard is distinguishable from an ordinary
/// decline in either one. That is not cosmetic: the `write_fmt` lane used to print
/// the fixed string "unproved" for every refusal, which made a new refusal
/// unwatchable there — and a guard whose firing cannot be observed cannot be
/// falsified. PROBE-ONLY: both call sites are behind their lane's `probe` flag,
/// because naming the conjunct costs a second full evaluation of the bar.
///
/// ONE REPORTED REASON CHANGED vs the string this lane printed before the
/// assumption-root gate, and it is deliberate: a NON-LOCAL target used to be
/// reported as "carries an authored contract clause", because
/// `body_carries_authored_clause` fails closed with `true` for any def it cannot
/// read. Both statements are true of such a target and the DECISION is identical
/// either way; the locality arm is tested first here so the reported reason names
/// the thing the reader can act on. Do not reorder to "restore" the old string —
/// the clause arm would then absorb every cross-crate decline again.
pub(super) fn target_decline_reason<'tcx>(
    tcx: TyCtxt<'tcx>,
    target: ty::Instance<'tcx>,
    root_def_id: DefId,
) -> String {
    let def_id = target.def_id();
    if def_id == root_def_id {
        return "is the bundle root itself (a self-discharge)".to_string();
    }
    if item_has_trust_skip_attr(tcx, def_id) {
        return "carries `#[trust::skip]` (unverified by user decree)".to_string();
    }
    if item_has_trust_attr(tcx, def_id, "assume_total") {
        return "carries `#[trust::assume_total]` (an axiom, not a proof)".to_string();
    }
    if !def_id.is_local() {
        return "is not local to this crate, so it has no independent verdict here".to_string();
    }
    if body_carries_authored_clause(tcx, def_id) {
        return "carries an authored contract clause (its verdict is conditional)".to_string();
    }
    if optimized_mir_query_would_cycle(tcx, def_id)
        || DYN_SUMMARY_IN_PROGRESS.with(|s| s.borrow().contains(&def_id))
        || RELIANCE_IN_PROGRESS.with(|set| set.borrow().contains(&def_id))
    {
        return "is already being computed up the stack (declined to avoid a query cycle)"
            .to_string();
    }
    match trait_panic_free::body_discharges_panic_freedom(tcx, def_id) {
        Ok(()) => "is verified (no decline)".to_string(),
        Err(reason) => reason,
    }
}

/// Does this body carry an AUTHORED SPEC CLAUSE — i.e. is its own verdict
/// conditional on a predicate somebody else has to establish?
///
/// This is a soundness conjunct of [`dyn_target_is_verified_panic_free`], not a
/// nicety. A precondition is CONJOINED INTO THE BODY'S OWN VCs
/// (`trust-mir-extract/src/lib.rs`: "contract preconditions become BODY
/// hypotheses (`conjoin_live_preconditions`)", and the reproduction of that in
/// `trust-ir-bridge/src/lower.rs::conjoin_live_preconditions_full`), while a
/// definition-site `#[requires]` row is filtered back out as bookkeeping
/// (`trust-mir-extract/src/verifier_api.rs::exact_definition_site_precondition_rows`).
/// So a body like
///
/// ```ignore (trust-contract-grammar-rustdoc-cannot-parse)
/// fn write_str(&mut self, s: &str) -> fmt::Result requires s.len() >= 4 {
///     self.n = self.n.wrapping_add(s.len() as u32 - 4);
///     Ok(())
/// }
/// ```
///
/// verifies panic-free — CONDITIONALLY — and `write!(w, "ab")` then panics in it.
/// Without this conjunct both lanes would read that conditional verdict as
/// panic-freedom and prove a program that panics.
///
/// Neither lane can discharge the condition. A `dyn` site's receiver is erased,
/// and the `write_fmt` reduction's argument reaches `write_str` through core
/// frames (`spec_write_fmt`, `fmt::write`) that are not in the bundle, so there
/// is no call site in the module where a precondition obligation could be minted.
///
/// TWO INDEPENDENT SURFACES mint a clause and a body needs only one of them:
///
/// 1. **First-class signature clauses** (`fn f(..) requires P`), read here
///    through `TrustContractBundle::def_may_have_contracts` — the HIR
///    `body.contract` pre-filter that the `trust_contracts` provider itself
///    returns `empty()` on (`trust_contract_query.rs`), so it is exactly the
///    query's own non-empty condition, and reading it does not FORCE the query.
///    Not forcing is deliberate: that provider EMITS contract-lowering errors,
///    and `liveness.rs::trust_contract_clauses_mention` documents why a consumer
///    reads the HIR inputs instead.
/// 2. **Attribute clauses**, which `trust-mir-extract` mints from ANY attribute
///    whose LAST path segment is a `contract_kind_from_name` name — the tool
///    prefix is not examined, so `#[requires(..)]`, `#[trust::requires(..)]` and
///    `#[contracts_requires(..)]` all produce a `Contract`. The two-name
///    `trust::`-only check at `trait_panic_free.rs:377-405` (Φ's refusal of
///    CONDITIONAL panic-freedom, the precedent for this decline) would miss every
///    one of those spellings AND miss surface 1 entirely, which is why this is a
///    fresh mirror of the producer rather than a call to it.
///
/// ANY clause declines, not only `requires`. This module grounds the semantics of
/// NO clause kind, and the house rule is that what cannot be grounded fails
/// closed; a `matches!(kind, Requires | Invariant | LoopInvariant)` list would
/// also silently readmit the next kind added to `TrustContractKind`. The cost of
/// the wider rule is measured and is zero: no fixture in `tests/ui/trust`
/// combines an authored clause with a `dyn`-reliance or Φ target.
fn body_carries_authored_clause(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    // Callers reach this only for a LOCAL def (`dyn_target_is_verified_panic_free`
    // returns false for a non-local one first). Fail closed rather than assume it
    // if that ever changes: a body whose clauses cannot be read is not a body
    // whose verdict is known to be unconditional.
    let Some(local_def_id) = def_id.as_local() else { return true };
    if rustc_middle::mir::trust_contract::TrustContractBundle::def_may_have_contracts(
        tcx,
        local_def_id,
    ) {
        return true;
    }
    // A local def's attributes are always queryable ([`super::attrs_queryable`]
    // returns true unconditionally for one), so no cross-crate guard is needed
    // here — the `as_local` above IS that guard.
    #[allow(deprecated)]
    let attrs = tcx.get_all_attrs(def_id);
    attrs.iter().any(|attr| {
        attr.path().last().is_some_and(|name| {
            matches!(
                name.as_str(),
                "requires"
                    | "contracts_requires"
                    | "trust_requires"
                    | "ensures"
                    | "contracts_ensures"
                    | "trust_ensures"
                    | "invariant"
                    | "trust_invariant"
                    | "decreases"
                    | "trust_decreases"
            )
        })
    })
}

/// `trait_def_id` plus every transitive supertrait of it.
///
/// Spelled out over `explicit_super_predicates_of` — the same walk
/// `dyn_trait_sealedness` uses — rather than pulled from `rustc_type_ir`, so this
/// module adds no dependency to `rustc_mir_transform`. Depth is bounded by a fuel
/// counter: a malformed cyclic supertrait graph must not spin here.
fn transitive_supertraits(tcx: TyCtxt<'_>, trait_def_id: DefId) -> Vec<DefId> {
    let mut out = vec![trait_def_id];
    let mut cursor = 0;
    let mut fuel = 64u32;
    while cursor < out.len() {
        let current = out[cursor];
        cursor += 1;
        if fuel == 0 {
            break;
        }
        fuel -= 1;
        for (predicate, _) in tcx
            .explicit_super_predicates_of(current)
            .iter_identity_copied()
            .map(ty::Unnormalized::skip_norm_wip)
        {
            if let ty::ClauseKind::Trait(trait_pred) = predicate.kind().skip_binder() {
                let super_def_id = trait_pred.trait_ref.def_id;
                if !out.contains(&super_def_id) {
                    out.push(super_def_id);
                }
            }
        }
    }
    out
}

/// The region-erased existential trait refs whose vtable slots ONE witnessed
/// coercion can serve: the coercion's principal plus every transitive
/// supertrait, each instantiated with the principal's OWN arguments via
/// `explicit_super_predicates_of` — never with identity args, which name the
/// trait's parameters instead of this vtable's instantiation.
///
/// `self_ty` stands in for `Self` when a supertrait bound mentions it
/// (`trait Sub: Super<Self>`). The resulting key names the concrete type, and a
/// site through `dyn Sub` demands `Super<dyn Sub>`, so the two can never meet —
/// fail-closed, and honestly so: such a vtable's `Super` slots really do serve
/// only `Super<Concrete>`, which `resolve_virtual_target` could not check
/// against an erased demand anyway.
///
/// Same fuel discipline as `transitive_supertraits`, and for the same reason —
/// with the extra twist that a malformed cyclic graph can GROW args on each
/// lap, so the fuel bound is what guarantees termination, not the dedup.
fn coercion_dyn_keys<'tcx>(
    tcx: TyCtxt<'tcx>,
    principal: ty::PolyExistentialTraitRef<'tcx>,
    self_ty: Ty<'tcx>,
) -> Vec<ty::ExistentialTraitRef<'tcx>> {
    let principal = tcx.instantiate_bound_regions_with_erased(principal);
    let mut refs = vec![principal.with_self_ty(tcx, self_ty)];
    let mut out = Vec::new();
    let mut cursor = 0;
    let mut fuel = 64u32;
    while cursor < refs.len() {
        let current = refs[cursor];
        cursor += 1;
        let key =
            tcx.erase_and_anonymize_regions(ty::ExistentialTraitRef::erase_self_ty(tcx, current));
        if !out.contains(&key) {
            out.push(key);
        }
        if fuel == 0 {
            break;
        }
        fuel -= 1;
        for (clause, _) in tcx
            .explicit_super_predicates_of(current.def_id)
            .iter_instantiated_copied(tcx, current.args)
            .map(ty::Unnormalized::skip_norm_wip)
        {
            let pred = clause.kind();
            let ty::ClauseKind::Trait(trait_pred) = pred.skip_binder() else { continue };
            let super_ref =
                tcx.instantiate_bound_regions_with_erased(pred.rebind(trait_pred.trait_ref));
            if !refs.contains(&super_ref) {
                refs.push(super_ref);
            }
        }
    }
    out
}

/// The region-erased existential trait ref one virtual site dispatches
/// through — the DEMANDED instantiation, rebuilt from the site's own args so a
/// `<dyn FnMut(&OnceState)>::call_mut` site can only ever read candidates
/// coerced to a `dyn FnMut(&OnceState)` vtable, never a sibling
/// instantiation's. `site.args` are the trait METHOD's args with `args[0]` the
/// erased `Self`, so truncating to the trait's generics and erasing `Self`
/// yields exactly the shape `coercion_dyn_keys` files under.
fn site_dyn_key<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_def_id: DefId,
    site: &VirtualCallSite<'tcx>,
) -> ty::ExistentialTraitRef<'tcx> {
    let trait_ref = ty::TraitRef::from_assoc(tcx, trait_def_id, site.args);
    tcx.erase_and_anonymize_regions(ty::ExistentialTraitRef::erase_self_ty(tcx, trait_ref))
}

/// What trait objects a VALUE of some type can carry.
///
/// `opaque` means the walk met a type it could not decompose, so `principals` is
/// NOT a complete answer and the caller must refuse every trait rather than trust
/// an empty list.
#[derive(Default)]
struct DynCarriers {
    principals: Vec<DefId>,
    opaque: bool,
}

impl DynCarriers {
    fn merge(&mut self, other: DynCarriers) {
        self.opaque |= other.opaque;
        for principal in other.principals {
            if !self.principals.contains(&principal) {
                self.principals.push(principal);
            }
        }
    }

    fn is_empty(&self) -> bool {
        self.principals.is_empty() && !self.opaque
    }
}

/// Is the reliance probe on?
///
/// Cached: the poison probe fires from inside per-call and per-block walks, and
/// an `env::var_os` on each of those is a syscall-shaped cost paid by every
/// compilation to answer a question whose answer cannot change during one.
fn probe_enabled() -> bool {
    static PROBE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *PROBE.get_or_init(|| std::env::var_os("TRUST_DYN_RELIANCE_PROBE").is_some())
}

/// WHICH entry point admitted a vtable of unknown origin.
///
/// PROBE-ONLY. No decision reads it, and it is constructed at every
/// `poison_carriers` call whether or not the probe is on — a `&'static str` and
/// a discriminant, so the cost of always building it is nil and there is no
/// second code path to keep in step with the first.
#[derive(Clone, Copy)]
enum PoisonSource<'a> {
    /// The bundle root's own parameter — the caller chose this vtable. The
    /// canonical instance is `Display::fmt`'s `f: &mut Formatter<'_>`.
    RootParam,
    /// The bundle root's return place.
    RootReturn,
    /// A cast that is not an `Unsize` and not an array-element projection.
    CastTarget,
    /// A thread-local handle: storage no bundled body initialized.
    ThreadLocal,
    /// A constant or static operand, whose vtable was minted outside any body.
    Constant,
    /// An indirect call (fn pointer / erased callable) — no body to witness.
    IndirectCall,
    /// A call whose target `Instance::try_resolve` could not name.
    UnresolvedCall,
    /// A resolved callee whose BODY this bundle never walked, reached through
    /// its destination place or an out-parameter.
    UnbundledCallee(&'a str),
    /// An `Unsize` coercion `classify_unsize` could not put in a shape —
    /// notably a `dyn`-to-`dyn` upcast, whose source is already erased.
    UnclassifiableUnsize,
}

impl std::fmt::Display for PoisonSource<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RootParam => f.write_str("a ROOT PARAMETER (the caller chose this vtable)"),
            Self::RootReturn => f.write_str("the ROOT RETURN PLACE"),
            Self::CastTarget => f.write_str("a non-`Unsize` CAST target"),
            Self::ThreadLocal => f.write_str("a THREAD-LOCAL handle"),
            Self::Constant => f.write_str("a CONSTANT/STATIC operand"),
            Self::IndirectCall => f.write_str("an INDIRECT call's outputs"),
            Self::UnresolvedCall => f.write_str("an UNRESOLVED call's outputs"),
            Self::UnbundledCallee(callee) => {
                write!(f, "the outputs of UNBUNDLED callee `{callee}`")
            }
            Self::UnclassifiableUnsize => f.write_str("an UNCLASSIFIABLE `Unsize` coercion"),
        }
    }
}

/// Every trait-object principal a VALUE of `ty` can carry.
///
/// Deliberately NOT `ty.walk()`. A callable's TYPE mentions its whole signature,
/// so `ty.walk()` on the `FnDef` constant of `<dyn Write>::write_str` reports
/// `dyn Write` — and poisoning on that refuses every trait at the very call site
/// the rule exists to discharge, which is exactly what the first build of this
/// module did. A `fn(&mut dyn T)` value carries no vtable: it only lets a caller
/// PASS one in, and anything a call HANDS BACK is caught on the destination place
/// instead (`call_output_traits`). So function signatures are skipped, while
/// closures and coroutines are descended into — a closure's captured upvars and a
/// coroutine's saved locals are real held values.
///
/// The match is EXHAUSTIVE in intent and its catch-all sets `opaque` rather than
/// returning "carries nothing". Skipping by default would be fail-OPEN: a
/// projection that normalizes to a trait object, a type parameter left in a
/// polymorphic body, or a type kind a future rustc adds would all read as "no
/// vtable here" and quietly widen the case split. Marking them opaque instead
/// makes C-FLOW decline for every trait in the bundle.
///
/// ## An ADT is decomposed through its FIELDS, not only its generic arguments
///
/// MEASURED LIVE FALSE PROVE, closed here 2026-08-19. This arm used to be
/// `ty::Adt(_, args) => for arg in args.types()`, so a `dyn` reachable through a
/// field whose type is written CONCRETELY — rather than through a type
/// parameter — was invisible to the whole analysis:
///
/// ```ignore (narrative-fragment-trait-Emit-and-Good-are-not-in-scope)
/// pub struct Bundle<'a> { pub sink: &'a mut dyn Emit }   // no type parameter
/// pub fn drive(b: &mut Bundle<'_>) -> u32 {
///     let mut g = Good;
///     let local: &mut dyn Emit = &mut g;
///     let a = local.emit(1);      // WITNESSED  -> coerced[dyn Emit] = {Good}
///     let c = b.sink.emit(2);     // the CALLER's vtable, never witnessed
///     a.wrapping_add(c)
/// }
/// ```
///
/// `Bundle<'a>`'s arguments are one LIFETIME, so this function reported no
/// principal, `observe_bundle_body`'s root-parameter poison never fired, and
/// C-FLOW discharged `Emit::emit` against the enumeration `{Good}` — which does
/// not contain the receiver the call actually dispatches on. Compiled as an rlib
/// on the DEFAULT lane the crate verified with exit 0; linked to a driver
/// supplying a panicking `Emit` it panicked at runtime. `core::fmt::Formatter`
/// (`buf: &'a mut dyn Write`) is the same shape, which is why
/// `dyn_dispatch_reliance_open_sink_stays_closed.rs` was declining by VACUITY
/// rather than by the poison its own header claimed.
///
/// The pure case failed closed BY ACCIDENT — with no coercion anywhere,
/// `coerced.get(trait)` is `None` and `site_discharges` declines on vacuity. The
/// unsound shape is MIXED: add one unrelated witnessed coercion for the same
/// trait and the set looks complete and non-empty, its members prove, and the
/// case split runs over an enumeration missing the caller's vtable.
///
/// That is precisely the shape `17b2aaf890` named and closed for UNHANDLED type
/// kinds. It did not close this one, because `ty::Adt` is a HANDLED arm: a
/// handled arm that returns nothing is indistinguishable from a type that really
/// carries nothing, and only the arms are auditable. Every path out of this walk
/// is now written against that distinction.
///
/// ## A callable's interior is FOUR questions, not one
///
/// SECOND FAIL-OPEN OF THE SAME FAMILY, closed here 2026-08-20 in the arm
/// immediately below the ADT one. `Closure`, `Coroutine`, `CoroutineClosure` and
/// `CoroutineWitness` shared a single arm that walked `args.types()` under one
/// stated premise — *"their held values — the captured upvars, and a coroutine's
/// live locals — ARE their generic arguments"*. That premise holds for two of the
/// four kinds and is FALSE for the other two:
///
/// | kind | parts | premise |
/// |---|---|---|
/// | `Closure` | `{parent_args, closure_kind_ty, closure_sig_as_fn_ptr_ty, tupled_upvars_ty}` | TRUE — upvars are an argument |
/// | `CoroutineClosure` | `+ signature_parts_ty, coroutine_captures_by_ref_ty` | TRUE — upvars are an argument |
/// | `Coroutine` | `{parent_args, kind_ty, resume_ty, yield_ty, return_ty, tupled_upvars_ty}` | **FALSE — no witness field** |
/// | `CoroutineWitness` | the coroutine's own generic arguments | **FALSE — those are not the held types** |
///
/// A coroutine's live locals stopped being generic arguments when the witness
/// field was removed from `CoroutineArgsParts`; they are now reachable only from
/// the MIR coroutine layout (`tcx.mir_coroutine_witnesses`). So a `&mut dyn Emit`
/// held across an `await` reported `principals: []` with `opaque: false` — the
/// literal reading "this value carries no vtable" — and `poison_carriers` then
/// poisoned nothing AND raised no `opaque_carrier_seen` flag, defeating the
/// root-param poison the module header's completeness argument rests on.
///
/// The four kinds now have four arms with four separate justifications.
///
/// ## SEVERITY OF THAT FAIL-OPEN: **LATENT**, not live — and the masks are NAMED
///
/// MEASURED 2026-08-20, stage1 `b38db06a6d`, and this paragraph is the whole
/// reason the arms above are worth reading. **This walk cannot reach a coroutine
/// today.** The split produces ZERO observable change: fixtures built against a
/// stage1 with and without it are byte-identical, so the coverage price of the
/// interior walk is measured at zero rather than merely hoped to be small.
///
/// That is NOT evidence the defect is imaginary — the premise really is false,
/// `CoroutineArgsParts` really has no witness field, and nothing under
/// `trust_verify/` called `mir_coroutine_witnesses` before this. It is evidence
/// that two UNRELATED refusals sit in front of it, each of which some future
/// slice will lift for its own reasons, neither of which will think about this
/// file:
///
/// * **MASK A — the native typed-TrustIr frontier refuses ACROSS-AWAIT SAVED
///   LOCALS outright.** Measured verbatim: *"unsupported operation: coroutine
///   frame field 2 is an across-await saved local (len 1); the single/multi-await
///   native frontier is not yet modeled"*, reported as `Trust full verification
///   failed ... native typed-TrustIr lowering did not complete`. An across-await
///   saved local **is** the coroutine interior this walk exists to read, so the
///   mask covers the fail-open's target exactly: every body whose interior could
///   carry an invisible `dyn` is already refused one layer earlier.
/// * **MASK B — a sync body whose SIGNATURE carries the coroutine never reaches
///   extraction.** A `fn drive() -> impl Future<..>` produced no verified body at
///   all; the only name in the report was `drive::{closure#0}`. Consistent with
///   the `clean-skip-unrevealed-opaque` decline. This closes the door
///   COMPLETELY, because a coroutine type is not nameable in surface Rust — the
///   return place is the only way one can appear in a sync signature, and
///   `observe_bundle_body`'s root-parameter door cannot be used at all.
///
/// The one door NOT measured is a CALL DESTINATION: a sync caller of an
/// `async fn` holds the coroutine in a local and `call_output_traits` walks that
/// type. It needs the callee to fall outside `observed_bodies` before
/// `deferred_output_poisons` fires, so it may be masked too — nobody has
/// checked. **Treat it as OPEN.** It is also the only door through which this
/// walk could be exercised today, so it is where to look first if you want to
/// falsify any of the above.
///
/// ### What fires when a mask lifts — a PAIR of fixtures, and they must stay a pair
///
/// `tests/ui/trust/dyn_dispatch_reliance_coroutine_interior_mask_tripwire.rs`
/// pins MASK A **by name** and turns RED the moment the across-await frontier is
/// modeled, and pins MASK B by the ABSENCE of any diagnostic on its sync root.
/// Its header carries the reproduction and the exact next step. Do NOT delete it
/// on the grounds that "the coroutine case is unreachable" — that unreachability
/// is the thing it measures, and it is the only mechanism that will tell anyone
/// this walk has just become load-bearing.
///
/// `tests/ui/trust/dyn_dispatch_reliance_poison_lane_liveness.rs` holds the
/// controls, and the split is FORCED rather than tidy. MEASURED: **a body whose
/// native lowering fails aborts the crate's verification before other bodies are
/// reached, so a fixture containing one cannot carry pins on any other body.**
/// MASK A's own evidence is such a body, so when the controls lived in the
/// tripwire the report named `drive::{closure#0}` and nothing else — the control
/// that must ERROR could not, and the control that must stay CLEAN was satisfied
/// by never running. An absence is only evidence if the thing that would fill it
/// still works, so mask B's pin depends on the liveness file staying green.
/// Merging the two files back together compiles, stays green, and silently
/// re-vacuums both controls.
///
/// Its honest residual, stated there too: if a mask lifts AND this walk has been
/// reverted, the tripwire stays green. No test can cover that, because a
/// differential needs a reachable door and there is none. That asymmetry is why
/// the fix ships despite being unobservable — defense in depth is the correct
/// disposition for a fail-open whose only protection is a refusal somewhere else.
///
/// ## Termination: a VISITED SET, with fuel still failing CLOSED
///
/// A field walk recurses through `struct List { next: Option<Box<List>> }`
/// forever, so the walk carries a visited set keyed by the FULL INTERNED TYPE.
/// A repeat is SKIPPED rather than reported opaque, and that is sound for a
/// reason the fail-open above did not have: the identical `Ty` is already being
/// walked into the SAME `out`, so every principal it carries is collected by
/// that walk. Keying on `AdtDef` instead would NOT be sound — `Wrapper<u8>`
/// would suppress `Wrapper<&dyn Emit>` — which is why the key is the type.
///
/// Reporting opaque on a revisit was considered and rejected: it would make
/// every recursive, indeed every merely REPEATED, type refuse C-FLOW for the
/// entire bundle. Fuel keeps the fail-closed role for the case a visited set
/// cannot bound at all (see [`MAX_CARRIER_WALK_FUEL`]) — unexamined is not
/// absent.
fn dyn_principals_in_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> DynCarriers {
    fn walk<'tcx>(
        tcx: TyCtxt<'tcx>,
        ty: Ty<'tcx>,
        fuel: &mut u32,
        visited: &mut FxHashSet<Ty<'tcx>>,
        out: &mut DynCarriers,
    ) {
        if *fuel == 0 {
            // Ran out of budget mid-type: the rest is unexamined, not absent.
            out.opaque = true;
            return;
        }
        *fuel -= 1;
        match ty.kind() {
            ty::Dynamic(data, ..) => match data.principal_def_id() {
                Some(principal) => {
                    if !out.principals.contains(&principal) {
                        out.principals.push(principal);
                    }
                }
                // An auto-trait-only object (`dyn Send`) has no principal and no
                // method slots, so there is nothing to dispatch — but naming it
                // is impossible, so refuse rather than ignore.
                None => out.opaque = true,
            },
            ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => walk(tcx, *inner, fuel, visited, out),
            ty::Slice(inner) | ty::Array(inner, _) | ty::Pat(inner, _) => {
                walk(tcx, *inner, fuel, visited, out)
            }
            ty::Tuple(elements) => {
                for element in elements.iter() {
                    walk(tcx, element, fuel, visited, out);
                }
            }
            // A HELD value of this type holds every one of its fields, at THIS
            // instantiation. `all_fields` iterates every variant, so an enum
            // payload and a union field are covered by the same walk as a struct
            // field — see
            // `dyn_dispatch_reliance_field_held_dyn_variant_carrier_stays_closed.rs`.
            //
            // The generic arguments are STILL walked. They are not redundant: a
            // `PhantomData<&mut dyn Emit>` carries its argument in no field at
            // all, and an argument that appears only in an uninhabited variant is
            // still nameable. Overlap is free — `DynCarriers::merge` and the
            // push below both dedup.
            ty::Adt(adt_def, args) => {
                if !visited.insert(ty) {
                    return;
                }
                for arg in args.types() {
                    walk(tcx, arg, fuel, visited, out);
                }
                for field in adt_def.all_fields() {
                    walk(tcx, instantiated_field_ty(tcx, field, args), fuel, visited, out);
                }
            }
            // Trust: NOT collapsed into the ADT arm — a callable has no
            // `all_fields` — and, since 2026-08-20, NOT collapsed with each
            // other either. See "A callable's interior is FOUR questions" in
            // the doc comment: the premise these four shared held for one and a
            // half of them.
            //
            // CLOSURE. The premise is TRUE. `ClosureArgsParts` is
            // `{parent_args, closure_kind_ty, closure_sig_as_fn_ptr_ty,
            // tupled_upvars_ty}`, and a closure value holds exactly its
            // captured upvars — which `tupled_upvars_ty` carries into the
            // `Tuple` arm. `closure_sig_as_fn_ptr_ty` is a signature and lands
            // in the `FnPtr` arm, which carries no vtable for the reason the
            // doc comment gives. Same decomposition upstream uses to decide
            // whether a closure is `Send`
            // (`rustc_next_trait_solver::solve::assembly::structural_traits`).
            //
            // The visited guard is the ADT arm's, for the ADT arm's reason: a
            // boxed recursive closure reaches itself.
            ty::Closure(_, args) => {
                if !visited.insert(ty) {
                    return;
                }
                for arg in args.types() {
                    walk(tcx, arg, fuel, visited, out);
                }
            }
            // Trust: CORO-CLOSURE. The premise is TRUE, but for a DIFFERENT
            // reason than the closure's, which is why it gets its own arm
            // rather than sharing one. `CoroutineClosureArgsParts` is
            // `{parent_args, closure_kind_ty, signature_parts_ty,
            // tupled_upvars_ty, coroutine_captures_by_ref_ty}` — the value an
            // async closure HOLDS is `tupled_upvars_ty` and nothing else; the
            // two `fn`-shaped parts are signatures. The coroutine it RETURNS is
            // a separate `ty::Coroutine` value that does not exist until the
            // closure is called, and the place it appears is a call
            // DESTINATION, which `call_output_traits` already walks — through
            // the arm below, which now reaches that coroutine's interior.
            // Upstream draws the same line: `structural_traits` answers
            // `[tupled_upvars_ty]` for this kind.
            ty::CoroutineClosure(_, args) => {
                if !visited.insert(ty) {
                    return;
                }
                for arg in args.types() {
                    walk(tcx, arg, fuel, visited, out);
                }
            }
            // Trust: COROUTINE. The premise is FALSE, and this was a fail-open —
            // a LATENT one. `CoroutineArgsParts` is `{parent_args, kind_ty,
            // resume_ty, yield_ty, return_ty, tupled_upvars_ty}` — there is NO
            // witness field. The upvars are covered by `tupled_upvars_ty` and
            // the signature by the resume/yield/return tys, but the locals a
            // coroutine holds ACROSS A SUSPEND POINT appear in NONE of them.
            // They live in the MIR coroutine layout and are reachable only
            // through the witness, so a `&mut dyn Emit` saved across an `await`
            // reported `principals: []`, `opaque: false` — "carries no vtable" —
            // and `poison_carriers` then poisoned nothing AND set no flag.
            //
            // Same defect as the ADT arm's, in the arm immediately below it: a
            // HANDLED arm that returns nothing is indistinguishable from a type
            // that really carries nothing.
            //
            // MEASURED UNREACHABLE 2026-08-20, and the ADT one was not — do not
            // read this arm as carrying the same urgency. Two masks stand in
            // front of it and the doc comment names both; this code has never
            // run on a real coroutine. It is here so that the day one of those
            // masks lifts, the answer is already correct instead of being
            // discovered by whoever lifted it.
            //
            // The witness is synthesized rather than looked up because
            // `ty::Coroutine` no longer carries one, and it is walked as a TYPE
            // rather than inlined so the `visited` set keys the recursion — a
            // coroutine that awaits a boxed future of itself reaches its own
            // witness, and the region erasure inside
            // `new_coroutine_witness_for_coroutine` is what makes that a repeat
            // rather than an infinite family. Exactly upstream's decomposition:
            // `[tupled_upvars_ty, coroutine_witness]`.
            ty::Coroutine(def_id, args) => {
                if !visited.insert(ty) {
                    return;
                }
                for arg in args.types() {
                    walk(tcx, arg, fuel, visited, out);
                }
                walk(
                    tcx,
                    Ty::new_coroutine_witness_for_coroutine(tcx, *def_id, *args),
                    fuel,
                    visited,
                    out,
                );
            }
            // Trust: WITNESS. The premise is FALSE, and this is where the
            // interior actually lives. `args` here are the typeck root's
            // generic arguments, not the held values; the held values are the
            // coroutine layout's saved locals, instantiated at `args`.
            //
            // `coroutine_interior_tys` fails CLOSED (`None`) for every reason it
            // can be unable to answer — not a coroutine def, no layout recorded
            // (an errored or metadata-less coroutine), or an argument list it
            // cannot safely instantiate against. That is the same disposition
            // the fuel exhaustion above takes, and for the same reason:
            // unexamined is not absent.
            ty::CoroutineWitness(def_id, args) => {
                if !visited.insert(ty) {
                    return;
                }
                for arg in args.types() {
                    walk(tcx, arg, fuel, visited, out);
                }
                match coroutine_interior_tys(tcx, *def_id, *args) {
                    Some(interior) => {
                        for interior_ty in interior {
                            walk(tcx, interior_ty, fuel, visited, out);
                        }
                    }
                    None => out.opaque = true,
                }
            }
            // Scalars and `!`: no interior at all.
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::Foreign(_) => {}
            // A signature, not a held vtable. See the doc comment.
            ty::FnDef(..) | ty::FnPtr(..) => {}
            // Everything else — projections, opaque types, params, inference and
            // error types, and any variant added after this was written — is
            // undecomposable HERE. Fail closed.
            _ => out.opaque = true,
        }
    }
    let mut out = DynCarriers::default();
    let mut fuel = MAX_CARRIER_WALK_FUEL;
    let mut visited = FxHashSet::default();
    walk(tcx, ty, &mut fuel, &mut visited, &mut out);
    out
}

/// One field's type, instantiated for the ADT it was reached through and
/// NORMALIZED where that is possible.
///
/// Normalization is a PRECISION measure, not a soundness one, and the direction
/// matters: an unresolved `Alias` falls into the walk's catch-all and reports
/// `opaque`, which refuses C-FLOW for the WHOLE bundle. Associated-type fields
/// are ordinary — `Peekable<I> { peeked: Option<Option<I::Item>> }` is in core —
/// so leaving them unresolved would trade the fail-open this walk just closed
/// for a broad capability loss that buys nothing.
///
/// The two guards are what keep the query honest, and each fails CLOSED:
///
/// * `fully_monomorphized` carries an EMPTY param env, so a type still
///   mentioning a parameter or an inference variable must not be handed to it.
///   Such a type is returned untouched, meets the catch-all, and refuses — the
///   same answer the walk already gives a bare `ty::Param`, which is correct: a
///   polymorphic body names no impl and can serve no case split.
/// * A normalization that FAILS likewise returns the alias untouched and is
///   refused there. `try_normalize_erasing_regions` is the fallible spelling for
///   exactly this reason; the infallible one would ICE on a type that does not
///   resolve, turning a conservative decline into a compiler crash.
fn instantiated_field_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    field: &ty::FieldDef,
    args: ty::GenericArgsRef<'tcx>,
) -> Ty<'tcx> {
    normalized_carrier_ty(tcx, field.ty(tcx, args))
}

// Trust: the guarded-normalization tail of [`instantiated_field_ty`], factored out
// unchanged so the coroutine-interior walk added in the same slice normalizes by
// the SAME discipline. Two carrier paths with two normalization policies would
// mean a `dyn` behind an associated type is seen through a struct field and not
// through a coroutine's saved local, for no reason a reader could reconstruct.
fn normalized_carrier_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    unnormalized: ty::Unnormalized<'tcx, Ty<'tcx>>,
) -> Ty<'tcx> {
    let raw = unnormalized.skip_normalization();
    if !raw.has_aliases() {
        return raw;
    }
    if raw.has_non_region_param() || raw.has_infer() || raw.has_escaping_bound_vars() {
        return raw;
    }
    tcx.try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), unnormalized)
        .unwrap_or(raw)
}

/// Trust: every type a COROUTINE holds that its generic arguments do not name —
/// the locals saved across its suspend points — at the instantiation `args`.
///
/// `None` means "could not be examined", and every caller must read that as
/// `opaque`, not as "holds nothing". That is the whole point of the arm this
/// serves: the fail-open it closes was a handled arm returning an empty answer.
///
/// ## Why `mir_coroutine_witnesses` and NOT `coroutine_hidden_types`
///
/// `coroutine_hidden_types` is the query upstream's trait solver uses for the
/// same structural question, and it is the obvious reach. It is the wrong one
/// HERE, on three counts, all of which point the same way:
///
/// * It FILTERS `ignore_for_traits`. That flag is set for a raw pointer created
///   from a non-thread-local `static` access and for a fake borrow — both
///   irrelevant to whether a coroutine is `Send`, and both able to carry a
///   vtable this analysis is asking about. A filtered saved local is a silent
///   hole of exactly the kind this slice exists to close.
/// * It cannot say "unavailable". A coroutine with no recorded layout — errored,
///   or foreign with no encoded MIR — yields an EMPTY type list, which reads as
///   "holds nothing". `mir_coroutine_witnesses` returns `Option`, so the two
///   answers stay distinguishable and the second one fails closed.
/// * It builds an `InferCtxt` and solves `WellFormed` obligations
///   (`compute_assumptions`). Running arbitrary trait selection from inside a
///   MIR pass widens the re-entrancy surface for no gain; the layout query
///   reaches strictly less.
///
/// ## Why calling this query from the `TrustVerify` pass cannot cycle
///
/// Established by reading, because an E0391 here is a fatal compiler bug and
/// strictly worse than the fail-open it repairs. `TrustVerify` is scheduled ONLY
/// at the end of `run_optimization_passes`, so the live query ancestors are
/// `optimized_mir(F)` and `mir_drops_elaborated_and_const_checked(F)`.
///
/// * FOREIGN `def_id`: `mir_coroutine_witnesses` is `separate_provide_extern`, so
///   the answer is a metadata table read (`rmeta::mod.rs`'s
///   `mir_coroutine_witnesses` table) and no local query runs at all. An absent
///   entry decodes as `None`, which this function forwards as a refusal.
/// * LOCAL `def_id`, already computed: a cache hit cannot cycle.
/// * LOCAL `def_id`, not yet computed: the provider borrows `tcx.mir_promoted(G).0`
///   and then depends on the ANALYSIS pipeline (`mir_built`, `mir_borrowck` of the
///   typeck root, `check_liveness`). Nothing in that closure calls `optimized_mir`,
///   and the only route back to `mir_drops_elaborated_and_const_checked(F)` is
///   `mir_for_ctfe(F)` — which `inner_optimized_mir` drives to completion with
///   `ensure_done` BEFORE the steal for the one `hir_body_const_context` that
///   reaches this pass (`ConstFn`; every other const context `panic!`s there
///   rather than running `optimized_mir`). A cached `mir_for_ctfe(F)` short-circuits
///   before it can re-enter the ancestor.
///
/// The neighbouring hazard is a STOLEN value, not a cycle, and it is closed by an
/// upstream pairing rather than by anything here: `mir_promoted(_).0` has exactly
/// ONE stealer (`mir_drops_elaborated_and_const_checked`, `rustc_mir_transform`'s
/// `lib.rs`), and it runs `ensure_done().mir_coroutine_witnesses(def)` for every
/// `is_coroutine` def IMMEDIATELY BEFORE stealing. So on any path where the steal
/// has happened this query is already cached, and on any path where it has not the
/// borrow succeeds. If that pairing is ever broken upstream, this is the caller
/// that notices — as a `Steal` panic, loudly, not as a wrong verdict.
fn coroutine_interior_tys<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: ty::GenericArgsRef<'tcx>,
) -> Option<Vec<Ty<'tcx>>> {
    // The witness arm's `def_id` is a coroutine by construction. Testing it
    // anyway keeps the query's precondition local to its call, so a future
    // caller that synthesizes a witness for something else refuses instead of
    // asking a MIR query about a def that has no MIR body.
    if !tcx.is_coroutine(def_id) {
        return None;
    }
    let layout = tcx.mir_coroutine_witnesses(def_id)?;
    // A coroutine's saved locals are written in terms of the TYPECK ROOT's
    // parameters — the synthetic closure parameters are carried in the args and
    // never named by a body type — so the witness args are exactly
    // `GenericArgs::for_item(tcx, typeck_root, ..)`, which is what
    // `Ty::new_coroutine_witness_for_coroutine` builds. Any other length means
    // an `EarlyBinder::instantiate` below could index past the end and ICE.
    // Refusing is the conservative answer and costs a bundle-wide decline; an
    // out-of-range index costs the build.
    if args.len() != tcx.generics_of(tcx.typeck_root_def_id(def_id)).count() {
        return None;
    }
    let mut interior = Vec::with_capacity(layout.field_tys.len());
    for saved in &layout.field_tys {
        // Deliberately NOT filtered on `saved.ignore_for_traits` — see above.
        let raw = saved.ty;
        // `EarlyBinder::instantiate` ASSERTS rather than returns when handed an
        // empty argument list for a value that still carries parameters. A
        // coroutine in a non-generic typeck root has none; if one appears
        // anyway, refuse rather than trip the assertion.
        if args.is_empty() && raw.has_param() {
            return None;
        }
        interior.push(normalized_carrier_ty(
            tcx,
            ty::EarlyBinder::bind(tcx, raw).instantiate(tcx, args),
        ));
    }
    Some(interior)
}

/// Is this cast a pointer to an ARRAY or SLICE re-typed as a pointer to its
/// ELEMENT — `*const [T; N] -> *const T`, `*const [T] -> *const T`, and the
/// `&`/`&mut` forms — with `T` IDENTICAL on both sides?
///
/// That operation re-points at the element position of a sequence whose elements
/// were each minted by a witnessed coercion and are already in the enumeration.
/// It is what slice iteration compiles to, and it creates no vtable.
///
/// DELIBERATELY A SHAPE, NOT A SET COMPARISON. The tempting generalization is
/// "poison only principals NEW in the target relative to the source", and it is
/// UNSOUND:
///
/// ```text
/// *const (&dyn Emit, usize)  ->  *const &dyn Emit
/// ```
///
/// Source principals `{Emit}`, target principals `{Emit}`, difference empty — so a
/// set rule skips the poison. But that cast can be aimed at the `usize` field and
/// reinterpret integer bytes as a fat pointer: a FORGED vtable, admitted precisely
/// because the principal happened to appear elsewhere in the source layout. A
/// tuple is not an array, so this arm never fires on it and the forging case stays
/// refused. `dyn_dispatch_reliance_cast_forged_vtable_stays_closed.rs` plants that
/// violation; if this predicate is ever "simplified" into a set difference, that
/// test is what fails.
///
/// Same discipline as `UnsizeShape::Length`: name the narrow shape that is
/// provably safe and refuse everything else.
fn is_array_element_projection<'tcx>(source_ty: Ty<'tcx>, target_ty: Ty<'tcx>) -> bool {
    fn pointee<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        match ty.kind() {
            ty::Ref(_, inner, _) => Some(*inner),
            ty::RawPtr(inner, _) => Some(*inner),
            _ => None,
        }
    }
    let (Some(source), Some(target)) = (pointee(source_ty), pointee(target_ty)) else {
        return false;
    };
    match source.kind() {
        ty::Array(element, _) | ty::Slice(element) => *element == target,
        _ => false,
    }
}

/// What an `Unsize` coercion actually BUILDS.
enum UnsizeShape<'tcx> {
    /// The target peels down to `dyn Trait`: a vtable is minted here, `source`
    /// is the concrete type it was minted for, and `principal` is the exact
    /// (still-bound) trait ref the target names — the identity `record` keys
    /// the candidate under.
    Vtable { source: Ty<'tcx>, principal: ty::PolyExistentialTraitRef<'tcx> },
    /// `[T; N]` -> `[T]` with `T` unchanged: pointer metadata becomes a length.
    /// No vtable is created, whatever `T` happens to contain.
    Length,
    /// Unclassifiable — notably a `dyn`-to-`dyn` upcast, whose source is already
    /// erased. Callers must fail closed.
    Unknown,
}

/// Peel matching layers off an `Unsize` source/target pair to decide which of the
/// three shapes it is; for a vtable coercion the source at that depth is the
/// concrete `Self`.
///
/// Handles `&`/`&mut`/`*const`/`*mut` and same-ADT wrappers (`Box`, `Rc`, `Arc`,
/// user smart pointers) by descending into the single differing type argument.
fn classify_unsize<'tcx>(source_ty: Ty<'tcx>, target_ty: Ty<'tcx>) -> UnsizeShape<'tcx> {
    let mut source = source_ty;
    let mut target = target_ty;
    for _ in 0..MAX_POINTER_PEEL {
        if let ty::Dynamic(data, ..) = target.kind() {
            return match (source.kind(), data.principal()) {
                (ty::Dynamic(..), _) => UnsizeShape::Unknown,
                // An auto-trait-only object (`dyn Send`) mints no dispatchable
                // slot and names no principal to key one by. Unreachable in
                // practice — `dyn_principals_in_ty` already refused the target
                // as opaque — but a missing principal must never read as one.
                (_, None) => UnsizeShape::Unknown,
                (_, Some(principal)) => UnsizeShape::Vtable { source, principal },
            };
        }
        // Array to slice. The EQUAL-ELEMENT-TYPE condition is what makes this arm
        // sound and MUST NOT be relaxed — it is the only thing forbidding a vtable
        // from being minted here. `&Foo` -> `&dyn Debug` where `Foo` nests a
        // `dyn Debug` never reaches this line: it peels to `ty::Dynamic` above and
        // takes the strict path.
        if let (ty::Array(source_element, _), ty::Slice(target_element)) =
            (source.kind(), target.kind())
        {
            return if source_element == target_element {
                UnsizeShape::Length
            } else {
                UnsizeShape::Unknown
            };
        }
        match (source.kind(), target.kind()) {
            (ty::Ref(_, s, _), ty::Ref(_, t, _)) | (ty::RawPtr(s, _), ty::RawPtr(t, _)) => {
                source = *s;
                target = *t;
            }
            (ty::Adt(s_def, s_args), ty::Adt(t_def, t_args)) if s_def == t_def => {
                // Descend into the one type argument that differs. Two differing
                // arguments would be ambiguous, so decline.
                let mut differing = s_args.types().zip(t_args.types()).filter(|(s, t)| s != t);
                let Some((s, t)) = differing.next() else { return UnsizeShape::Unknown };
                if differing.next().is_some() {
                    return UnsizeShape::Unknown;
                }
                source = s;
                target = t;
            }
            _ => return UnsizeShape::Unknown,
        }
    }
    UnsizeShape::Unknown
}

/// Visit the TYPE of every constant operand in `block`, including the ones in the
/// terminator. A `dyn`-bearing constant carries a vtable no body built.
fn for_each_constant_ty<'tcx>(block: &BasicBlockData<'tcx>, mut visit: impl FnMut(Ty<'tcx>)) {
    let mut on_operand = |operand: &Operand<'tcx>| {
        if let Operand::Constant(constant) = operand {
            visit(constant.ty());
        }
    };
    for stmt in &block.statements {
        let StatementKind::Assign(assign) = &stmt.kind else { continue };
        let (_, rvalue) = &**assign;
        match rvalue {
            Rvalue::Use(operand, _)
            | Rvalue::Repeat(operand, _)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::UnaryOp(_, operand) => on_operand(operand),
            Rvalue::BinaryOp(_, operands) => {
                on_operand(&operands.0);
                on_operand(&operands.1);
            }
            Rvalue::Aggregate(_, operands) => {
                for operand in operands.iter() {
                    on_operand(operand);
                }
            }
            _ => {}
        }
    }
    match &block.terminator().kind {
        TerminatorKind::Call { func, args, .. } | TerminatorKind::TailCall { func, args, .. } => {
            on_operand(func);
            for arg in args.iter() {
                on_operand(&arg.node);
            }
        }
        TerminatorKind::SwitchInt { discr, .. } | TerminatorKind::Assert { cond: discr, .. } => {
            on_operand(discr)
        }
        _ => {}
    }
}
