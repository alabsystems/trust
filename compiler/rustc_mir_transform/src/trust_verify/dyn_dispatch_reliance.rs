//! Trust rung 1, §(c) for `dyn` dispatch: when may a call through
//! `InstanceKind::Virtual` discharge its panic-freedom obligation?
//!
//! A virtual call names no body. Discharging it is sound only if EVERY impl the
//! receiver could hold has been proved panic-free, so the whole question is a
//! COMPLETENESS question and this module is three independent completeness
//! certificates. They discharge the same obligation by different arguments and
//! must be attacked separately; all three fail closed.
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
//! **C-SEALED** — the trait is SEALED (`dyn_trait_sealedness`) and every member
//! of its enumerated impl set is independently verified panic-free. Quantifies
//! over the IMPL SET like C-UNIVERSAL, but earns the closure from the SEAL
//! rather than from a declared Φ, so it needs no attribute on the trait. This is
//! `sealed_generic_dispatch_impls_all_panic_free` — lattice rung 2 — called at a
//! virtual site instead of a `ImplSource::Param` one, and it is *the same
//! predicate*, not a restatement: the C-UNIVERSAL note below already records why
//! delegating is mandatory here (a hand-rolled duplicate silently dropped the
//! specialization conjunct).
//!
//! The certificate transfers for exactly the reason C-UNIVERSAL's does, stated
//! in this header since 2026-08: "a `dyn T` receiver and a `T`-bounded type
//! parameter range over exactly the same impls". An `Unsize` coercion to `dyn T`
//! requires `S: T`, so the vtable slot for `T::m` is the impl method rung 2
//! enumerated, or the trait default body it also enumerates. Sealing bounds that
//! set; independent verdicts (`trust_proof_results` on each member's own body,
//! never a bundled-but-unproved target — see below) bound its contents.
//!
//! WHY IT IS NOT REDUNDANT WITH C-FLOW, which also enumerates. C-FLOW's
//! enumeration is over the coercions *inside one bundle*, so it is refused
//! outright by a `dyn`-bearing ROOT PARAMETER — which poisons the trait — and
//! `fn total(shapes: &[&dyn Shape])` is exactly that shape. C-SEALED does not
//! look at the bundle at all, so it serves the function that TAKES a trait
//! object, which is the shape ordinary Rust is written in. It was measured
//! 2026-09-19: `total` was the last refusing row of the realistic `p4` once its
//! callers verified, with the generic twin of the same program (`w4`) already
//! green through rung 2 — one lattice rung wired to one call shape and not the
//! other.
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

use rustc_ast::attr::AttributeExt;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Body, CastKind, Operand, Place, RETURN_PLACE, Rvalue,
    StatementKind, TerminatorKind,
};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, Mutability, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::Spanned;
use rustc_span::def_id::DefId;

use super::static_str_write_fmt::{
    StaticStrWriteFmtFacts, instance_is_core_default_write_fmt, resolve_write_str_for_args,
    virtual_write_fmt_site_is_from_str_backed,
};
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
    args: ty::GenericArgs<'tcx>,
    /// Trust (2026-09-21): this site is `fmt::Write::write_fmt` AND its
    /// `Arguments` operand is `from_str`-backed (the reduction's gate 3),
    /// decided where the call was observed. `false` for every other site. Read
    /// by C-FLOW per enumerated `Self`, where the resolved target is core's
    /// default body and the ordinary bar therefore declines on locality alone.
    write_fmt_from_str_backed: bool,
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
    /// The subset of [`Self::poisoned`] whose poison came from a source that
    /// could put a vtable of FORGED origin in this bundle, rather than one of
    /// merely UNKNOWN origin.
    ///
    /// The distinction exists for C-SEALED and nothing else. That certificate
    /// bounds the dispatch target by the trait's IMPL SET, so a `dyn T` built by
    /// a real `Unsize` coercion Trust did not witness — a root parameter, a
    /// callee's return place — is inside its premise even though C-FLOW's
    /// enumeration cannot see it. A vtable REINTERPRETED from arbitrary bits is
    /// not: it can name a function that is no impl of anything, and
    /// `dyn_dispatch_reliance_cast_forged_vtable_stays_closed.rs` is the rail
    /// that says so. `PoisonSource::vtable_origin_is_a_real_coercion` is the
    /// split, and it fails closed for every source that is not obviously one.
    forge_poisoned: FxHashSet<DefId>,
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
    /// Trust (D1 increment 2): the third element says the call was a VIRTUAL
    /// `<dyn fmt::Debug|Display>::fmt` site, so an unwalked callee is named
    /// [`PoisonSource::NestedFormatterOutput`] instead of `UnbundledCallee`.
    deferred_output_poisons: Vec<(DefId, DynCarriers, bool)>,
    /// The `fmt::Write::write_fmt` reduction's own facts. A SEPARATE certificate
    /// with its own soundness argument (see that module), gathered here only
    /// because this walk is the one place every bundled body — including the
    /// B-lane's instantiated foreign ones — is in hand, and duplicating the walk
    /// would duplicate the seam where a missed body becomes a missed decline.
    static_str_write_fmt: StaticStrWriteFmtFacts<'tcx>,
    /// GATE 0 for BOTH lanes: what every bundled call renders to, and which lane
    /// certified it. See [`CallKeyLedger`].
    call_keys: CallKeyLedger,
    /// Trust (D1 increment 1, writer-relative facts): the subset of
    /// [`Self::poisoned`] poisoned by ANY source other than the bundle root's own
    /// `&mut Formatter` parameter ([`PoisonSource::RootFormatterParam`]). Read
    /// ONLY by [`Self::writer_relative_facts`]; no C-FLOW, C-SEALED or
    /// C-UNIVERSAL decision reads it. `fmt::Write` in this set means some writer
    /// in the bundle may have come from somewhere other than the caller's
    /// `Formatter` — `self`, a constant, a cast, an unbundled callee — and the
    /// writer-relative premise ("the only writer is the one the sink supplied")
    /// cannot be stated.
    poisoned_beyond_formatter_param: FxHashSet<DefId>,
    /// Trust (D1 increment 1): some bundled call returns a value whose type
    /// mentions `core::fmt::Formatter` (`Formatter::new`, `with_options`, a user
    /// helper returning one). A `Formatter` minted inside the bundle names a
    /// writer the sink did not supply. Read only by
    /// [`Self::writer_relative_facts`].
    formatter_minted: bool,
    /// Trust (D1 increment 1, G-MEMBER): some body walked into this bundle —
    /// the ROOT included — carries a terminator that can raise a panic (or
    /// abort) without minting a row of its own: an `Assert`, a call with no
    /// return target (a diverging callee: `panic*`, `unwrap_failed`, `abort`), a
    /// `TailCall` (divergence not visible), inline asm, a `Drop`, or a coroutine
    /// terminator. A bundled member's `Assert` mints NO obligation (docs/TCB.md),
    /// and it folds into the whole-function panic-freedom aggregate under a
    /// representative that may be a writer edge — so the writer-relative class is
    /// refused outright for such a bundle. Read only by
    /// [`Self::writer_relative_facts`].
    panic_site_in_bundle: bool,
    /// Trust (D1 increment 2): the subset of [`Self::forge_poisoned`] whose
    /// forged-origin source was anything OTHER than
    /// [`PoisonSource::PadAdapterConstant`]. Read only by
    /// [`Self::writer_relative_facts`]; C-SEALED keeps reading `forge_poisoned`,
    /// which is filled exactly as before.
    forge_poisoned_beyond_pad_adapter: FxHashSet<DefId>,
    /// Trust (D1 increment 2): some walked body holds a CONSTANT whose type carries
    /// a trait object ONLY through core's private `fmt::builders::PadAdapter`
    /// ([`constant_ty_carries_dyn_only_through_pad_adapter`]) — the builders'
    /// `let mut slot = None;`. Poisoned as [`PoisonSource::PadAdapterConstant`].
    /// Recorded for the writer-relative facts' disclosure; the justification is
    /// the source audit in that predicate's docs.
    pad_adapter_constant_seen: bool,
    /// Trust (D1 increment 2): some virtual `<dyn fmt::Debug|Display>::fmt` site
    /// handed a `&mut Formatter` to a callee this bundle did not walk (poisoned as
    /// [`PoisonSource::NestedFormatterOutput`]). The writer-relative facts accept
    /// that only when EVERY nested-formatter site's enumerated targets were
    /// admitted ([`Self::decide_nested_formatters`]).
    nested_formatter_output_poisoned: bool,
    /// Trust (D1 increment 2, G-MEMBER): a walked body was a UB-CHECK member
    /// ([`body_is_ub_check_member`]) and its non-unwinding abort was NOT counted
    /// as an unrowed panic site. Read only by [`Self::writer_relative_facts`],
    /// which then also demands `!non_sysroot_unsafe_walked`.
    ub_check_member_walked: bool,
    /// Trust (P-UB, absent UB-check members, 2026-11-08): every DIRECT plain
    /// call, made from a walked body of an authentic foundational crate, whose
    /// callee is a UB-check `precondition_check`
    /// ([`def_is_ub_check_precondition_fn`]) — the callee and its rendered call
    /// key — and every call key rendered by ANY other call (another callee, a
    /// caller outside the sysroot, a tail call, an indirect call). At facts time
    /// the two name the absent UB-check fold sites P-UB excuses exactly as it
    /// excuses a walked UB-check member: a candidate whose body was never walked
    /// (so the bridge mints an absent-callee marker for it) and whose key no
    /// other call renders (so the marker cannot be another callee's). Read only
    /// by [`Self::writer_relative_facts`].
    ///
    /// Why it exists: the 1.101 derive finishers (upstream `ff7c30e864ac`, ported
    /// in `eaa3250ddc`) route every derive through `debug_struct_fields_finish`
    /// and the byte-level `split_str_by_space`, so the walked bundle now holds
    /// `<Split<'_, u8, _> as Iterator>::next` (and `slice_contains`), whose
    /// inlined `slice::Iter::new` calls `<*mut T>::add::precondition_check`. The
    /// bundler declines every `core::ptr::` body (the plumbing-family gate in
    /// `trust_verify.rs`), so that check is ABSENT, not walked, and its marker
    /// was refused by the writer-relative bar while the identical check, walked,
    /// is not counted (G-MEMBER) — measured on `fmt_writer_relative_derive.rs`
    /// `#nested_local` and five sink revisions (stage-1 `39d11b38d7`).
    ub_check_precondition_candidates: Vec<(DefId, String)>,
    ub_check_other_callee_keys: FxHashSet<String>,
    /// Trust (96a18b names-split finishers, G-MEMBER): a walked body was a
    /// NAMES-SPLIT member ([`names_split_member_kind`]) — authentic core's
    /// `debug_struct_field{1..5}_finish` derive helpers or the `str::split(' ')`
    /// machinery their concatenated-names argument pulls in — and its panic
    /// sites were NOT counted as unrowed. Those sites are the split's internal
    /// invariants (`Split::next().unwrap()`, the char searcher's length and
    /// encoding unwraps, an alignment `debug_assert!`), discharged only by the
    /// per-call evidence [`Self::observe_bundle_body`] records in
    /// [`Self::names_split_unproven`] (docs/TCB.md "Formatting premises",
    /// P-SPLIT). Read only by [`Self::writer_relative_facts`], which then also
    /// demands `!non_sysroot_unsafe_walked`, the same belt as P-UB.
    names_split_member_walked: bool,
    /// Trust (96a18b names-split finishers): some walked CALL into the
    /// names-split machinery failed its evidence check — a finisher `names`
    /// argument that is not a constant `&str` with at least the finisher's
    /// arity of `' '` separators, an `is_aligned_to` alignment that is not a
    /// constant power of two (or a literal `align_of`), or `encode_utf8_raw`
    /// called from a walked body outside the authentic sysroot. Voids the
    /// exemption above: [`Self::writer_relative_facts`] refuses while this is
    /// set (and a names-split member was walked).
    names_split_unproven: bool,
    /// The n-ary member has no independent entry premise. Each walked body
    /// needs an authenticated fixed-wrapper entry; any other incoming edge
    /// sets `names_split_unproven`, including a direct six-field derive.
    names_split_nary_walked: FxHashSet<DefId>,
    names_split_forwarded_nary: FxHashSet<DefId>,
    /// Trust (96a18b names-split finishers): every DIRECT callee (def + rendered
    /// call key) of a walked NAMES-SPLIT member body, and every call key some
    /// OTHER walked body calls. At facts time the two name the machinery's
    /// absent-callee fold sites: a candidate whose body was never walked (so
    /// the bridge mints an absent-callee marker for it inside the machinery)
    /// and that no non-machinery body calls by the same key (so the marker
    /// cannot be another member's). Read only by
    /// [`Self::writer_relative_facts`].
    names_split_candidates: Vec<(DefId, String)>,
    names_split_other_callee_keys: FxHashSet<String>,
    /// Trust (D1 increment 2): some walked body outside the authentic sysroot
    /// crates uses `unsafe` (its own source, or a non-sysroot body inlined into
    /// it — `function_uses_unsafe_outside_std`). The UB-check exemption above is
    /// void when this is set. This is a BELT, not the premise: it sees only
    /// walked bodies, and an invalid value built by `unsafe` OUTSIDE the bundle
    /// (in `main`, or in a verify-off dependency) can still reach a sysroot
    /// precondition through `&self`. That is excluded only because the root's own
    /// `unsafe` rows are Level 0 errors and a verify-off dependency call is
    /// fail-closed (docs/TCB.md "Formatting premises", P-UB; probes `fa26`/`fa27`).
    non_sysroot_unsafe_walked: bool,
    /// Trust (D1 increment 2): per bundled CALL KEY, whether every call rendering
    /// to it is core's `caller_location` intrinsic (a total read of the caller's
    /// `Location`; it cannot panic). Keyed by the same `func_operand_name` string
    /// the rows are matched by, ANDed per key exactly like gate 0's ledger, so a
    /// key that also names any other call answers `false`. Read only by
    /// [`Self::writer_relative_facts`].
    caller_location_only_keys: FxHashMap<String, bool>,
    /// Trust (D1 increment 2): the NESTED-FORMATTER decision
    /// ([`Self::decide_nested_formatters`]), computed in `resolve_reliance` under
    /// the reliance guard (so a case-split member's verdict is forced exactly as
    /// C-FLOW forces one). `None` = never computed, which the writer-relative
    /// facts read as a refusal whenever a nested-formatter site exists.
    nested_formatters: Option<NestedFormatterDecision>,
}

/// Trust (D1 increment 2): which `<dyn fmt::Debug|Display>::fmt` call keys of a
/// formatting-impl root's bundle are NESTED-FORMATTER edges the writer-relative
/// class may excuse, and the local impls they can reach. Discharges nothing: it
/// never enters `dyn_contract_total_callees`.
#[derive(Default)]
struct NestedFormatterDecision {
    /// Keys every site of which had its whole enumerated target set admitted.
    accepted_keys: FxHashSet<String>,
    /// Keys some site of which did not. Wins over `accepted_keys`.
    rejected_keys: FxHashSet<String>,
    /// The LOCAL formatting impls an admitted site can dispatch to, for error
    /// transparency at the sink (`fmt_error_transparency`). Deduplicated, in
    /// walk order (`DefId` is deliberately not `Ord`).
    local_targets: Vec<DefId>,
}

impl<'tcx> DynDispatchBundleFacts<'tcx> {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Poison `trait_def_id` and every SUPERTRAIT of it: an unknown `dyn Sub`
    /// upcasts to an unknown `dyn Super`, so the unknown propagates upward.
    fn poison(
        &mut self,
        tcx: TyCtxt<'tcx>,
        trait_def_id: DefId,
        forged: bool,
        beyond_formatter_param: bool,
        forged_beyond_pad_adapter: bool,
    ) {
        for did in transitive_supertraits(tcx, trait_def_id) {
            self.poisoned.insert(did);
            if forged {
                self.forge_poisoned.insert(did);
            }
            // Trust (D1 increment 1): see `poisoned_beyond_formatter_param`.
            if beyond_formatter_param {
                self.poisoned_beyond_formatter_param.insert(did);
            }
            // Trust (D1 increment 2): see `forge_poisoned_beyond_pad_adapter`.
            if forged_beyond_pad_adapter {
                self.forge_poisoned_beyond_pad_adapter.insert(did);
            }
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
    /// `source` was probe-only until C-SEALED arrived; it now ALSO decides
    /// [`Self::forge_poisoned`] (see that field), and only that. No C-FLOW
    /// decision reads it. It exists because
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
        let forged = !source.vtable_origin_is_a_real_coercion();
        // Trust (D1 increment 2): the two new sources poison EXACTLY as the ones
        // they refine (`Constant`, `UnbundledCallee`) for every certificate — the
        // same `poisoned`/`forge_poisoned` entries, the same `forged` answer — and
        // differ ONLY in what the writer-relative facts record: for
        // `core::fmt::Write` itself (and for nothing else) they are not a writer
        // "beyond the formatter parameter", because the writer-relative facts
        // justify each separately (`writer_relative_facts`).
        //
        // Trust (identity-anchor sweep, 2026-09-28): `core::fmt::Write` is the
        // diagnostic item AND authentic resident core
        // (`authentic_core_diagnostic_item`). For a whole-`core` substitute's
        // `FmtWrite` the refinement does not apply, so its sources poison as the
        // ones they refine — the refusal direction.
        let fmt_write = super::authentic_core_diagnostic_item(tcx, rustc_span::sym::FmtWrite);
        for &principal in &carriers.principals {
            match source {
                PoisonSource::PadAdapterConstant => self.pad_adapter_constant_seen = true,
                PoisonSource::NestedFormatterOutput(_) => {
                    self.nested_formatter_output_poisoned = true
                }
                _ => {}
            }
            let is_fmt_write = Some(principal) == fmt_write;
            let beyond_formatter_param = match source {
                PoisonSource::RootFormatterParam => false,
                PoisonSource::PadAdapterConstant | PoisonSource::NestedFormatterOutput(_) => {
                    !is_fmt_write
                }
                _ => true,
            };
            let forged_beyond_pad_adapter =
                forged && !(matches!(source, PoisonSource::PadAdapterConstant) && is_fmt_write);
            self.poison(tcx, principal, forged, beyond_formatter_param, forged_beyond_pad_adapter);
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
                let param_ty = body.local_decls[local].ty;
                // Trust (D1 increment 1): the root's `&mut Formatter` parameter is
                // told apart from every other root parameter. The poison itself is
                // IDENTICAL either way (C-FLOW still declines on it); only the
                // writer-relative facts read the distinction.
                let source = if ty_is_mut_ref_to_formatter(tcx, param_ty) {
                    PoisonSource::RootFormatterParam
                } else {
                    PoisonSource::RootParam
                };
                self.poison_dyn_in_ty(tcx, param_ty, source);
            }
            self.poison_dyn_in_ty(tcx, body.local_decls[RETURN_PLACE].ty, PoisonSource::RootReturn);
        }

        // Trust (D1 increment 1, G-MEMBER): every walked body, the root included.
        // See `panic_site_in_bundle`. Decides nothing but the writer-relative facts.
        // Trust (D1 increment 2): a UB-CHECK member (`body_is_ub_check_member`) is
        // not counted — its only panic is the non-unwinding abort of a VIOLATED
        // sysroot `unsafe` precondition — but taking that exemption is recorded,
        // and `writer_relative_facts` voids it when any non-sysroot walked body
        // uses `unsafe` (a belt only — see `non_sysroot_unsafe_walked` and P-UB:
        // an invalid value from `unsafe` OUTSIDE the bundle is excluded by other
        // rules, not by this one).
        let body_def_id = body.source.def_id();
        // Trust (96a18b names-split finishers): computed once per body; the
        // G-MEMBER exemption below and the per-call evidence/candidate
        // recording in the call loop both read it.
        let caller_names_split_kind = names_split_member_kind(tcx, body_def_id);
        let caller_is_names_split_member = caller_names_split_kind.is_some();
        if caller_names_split_kind == Some(NamesSplitMember::NaryFinisher) {
            self.names_split_nary_walked.insert(body_def_id);
        }
        // Trust (D1 increment 2, live): name every `Drop` G-MEMBER does NOT count
        // (`drop_runs_no_code`), so the relaxation is a measurement too.
        if probe_enabled() {
            for (block_id, block) in body.basic_blocks.iter_enumerated() {
                if let TerminatorKind::Drop { place, .. } = &block.terminator().kind {
                    let place_ty = place.ty(&body.local_decls, tcx).ty;
                    if drop_runs_no_code(tcx, place_ty, typing_env) {
                        with_no_trimmed_paths!(eprintln!(
                            "TRUST_DYN_RELIANCE_PROBE:   G-MEMBER: no-op drop (no drop glue) \
                             not counted in `{}` at {block_id:?}: `{place_ty}`",
                            tcx.def_path_str(body_def_id)
                        ));
                    }
                }
            }
        }
        if body_is_ub_check_member(tcx, body_def_id) {
            self.ub_check_member_walked = true;
        } else if caller_is_names_split_member {
            // Trust (96a18b names-split finishers, G-MEMBER): not counted, under
            // the per-call evidence recorded below (`names_split_unproven`) and
            // the P-UB belt. Named under the probe like every other G-MEMBER
            // decision, so the exemption is a measurement too.
            self.names_split_member_walked = true;
            if probe_enabled() {
                with_no_trimmed_paths!(eprintln!(
                    "TRUST_DYN_RELIANCE_PROBE:   G-MEMBER: names-split member \
                     not counted: `{}`",
                    tcx.def_path_str(body_def_id)
                ));
            }
        } else if let Some((block, kind)) = first_unrowed_panic_site(tcx, body, typing_env) {
            // Trust (D1 increment 2, live): NAME the body and terminator, so a
            // G-MEMBER refusal is a measurement rather than an inference.
            if probe_enabled() {
                with_no_trimmed_paths!(eprintln!(
                    "TRUST_DYN_RELIANCE_PROBE:   G-MEMBER: unrowed panic site in `{}` \
                     at {block:?}: {kind:?}",
                    tcx.def_path_str(body_def_id)
                ));
            }
            self.panic_site_in_bundle = true;
        }
        if !self.non_sysroot_unsafe_walked
            && !super::crate_is_authentic_foundational(tcx, body_def_id.krate)
        {
            use rustc_hir::def::DefKind;
            // The source question is asked only of bodies that HAVE source: a fn,
            // method or closure (`function_uses_unsafe_outside_std`, which is
            // conservative for a non-local one). A tuple-struct/variant constructor
            // is compiler-generated and has no HIR body to walk (asking would
            // ICE), and cannot contain `unsafe`. Anything else cannot be confirmed
            // safe here and counts as `unsafe` (fail-closed: it only voids the
            // UB-check exemption).
            let uses_unsafe = match tcx.def_kind(body_def_id) {
                DefKind::Fn | DefKind::AssocFn | DefKind::Closure => {
                    super::function_uses_unsafe_outside_std(tcx, body)
                }
                DefKind::Ctor(..) => false,
                _ => true,
            };
            if uses_unsafe {
                self.non_sysroot_unsafe_walked = true;
            }
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
                    // vtables belong to the unsafe lane, not to this rule. The
                    // enumerated origin-preserving exceptions are an element
                    // projection and exact carrier retags — see the predicates
                    // below. Neither discharges validity or erases prior poison.
                    Rvalue::Cast(kind, operand, target_ty) => {
                        let source_ty = operand.ty(&body.local_decls, tcx);
                        let preserves_carrier =
                            cast_preserves_dyn_carrier(tcx, *kind, source_ty, *target_ty);
                        if !is_array_element_projection(source_ty, *target_ty) && !preserves_carrier
                        {
                            if probe_enabled() {
                                with_no_trimmed_paths!(eprintln!(
                                    "TRUST_DYN_RELIANCE_PROBE:   cast {kind:?}: `{source_ty}` -> `{target_ty}`"
                                ));
                            }
                            self.poison_dyn_in_ty(tcx, *target_ty, PoisonSource::CastTarget);
                        } else if preserves_carrier && probe_enabled() {
                            with_no_trimmed_paths!(eprintln!(
                                "TRUST_DYN_RELIANCE_PROBE:   origin-preserving cast in `{}` at {block_id:?}: {kind:?} `{source_ty}` -> `{target_ty}`",
                                tcx.def_path_str(body.source.def_id()),
                            ));
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
            //
            // Trust (D1 increment 2): a constant whose type carries a trait object
            // ONLY through core's private `fmt::builders::PadAdapter` is poisoned
            // under its own source, which poisons identically for every
            // certificate (see `poison_carriers`). The probe names every
            // `dyn`-bearing constant's TYPE, so which constant a bundle holds is a
            // measurement rather than an inference (D1 memo: "confirm the
            // `Constant` poison before admitting it").
            let mut constant_carriers = DynCarriers::default();
            let mut pad_adapter_carriers = DynCarriers::default();
            for_each_constant(block, |constant| {
                let ty = constant.ty();
                let carriers = dyn_principals_in_ty(tcx, ty);
                if carriers.is_empty() {
                    return;
                }
                // A value of the authenticated, fieldless PhantomData lang
                // item contains no runtime pointer or vtable. This excludes
                // only an evaluated by-value ZeroSized constant as an origin;
                // the conservative type walk and all other sources stay intact.
                if constant_is_empty_phantom_data(tcx, constant) {
                    if probe_enabled() {
                        with_no_trimmed_paths!(eprintln!(
                            "TRUST_DYN_RELIANCE_PROBE:   exact PhantomData ZeroSized constant in `{}` at {block_id:?}: `{ty}` carries no runtime vtable",
                            tcx.def_path_str(body.source.def_id()),
                        ));
                    }
                    return;
                }
                // Trust (D1 increment 2, live): BOTH the type audit and the
                // value's own pointer-freedom (`constant_value_holds_no_pointer`).
                let pad_adapter_ty = constant_ty_carries_dyn_only_through_pad_adapter(tcx, ty);
                let pointer_free = constant_value_holds_no_pointer(tcx, constant);
                let only_pad_adapter = pad_adapter_ty && pointer_free;
                if probe_enabled() {
                    with_no_trimmed_paths!(eprintln!(
                        "TRUST_DYN_RELIANCE_PROBE:   dyn-bearing constant in `{}` at {block_id:?} of type `{ty}` \
                         (carries a trait object only through core's `PadAdapter`: \
                         {pad_adapter_ty}; value holds no pointer: {pointer_free})",
                        tcx.def_path_str(body.source.def_id()),
                    ));
                }
                if only_pad_adapter {
                    pad_adapter_carriers.merge(carriers);
                } else {
                    constant_carriers.merge(carriers);
                }
            });
            self.poison_carriers(tcx, &constant_carriers, PoisonSource::Constant);
            self.poison_carriers(tcx, &pad_adapter_carriers, PoisonSource::PadAdapterConstant);

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
            // Trust (D1 increment 2): the callee key, rendered ONCE per call and
            // used by every ledger below (it was rendered once per arm before;
            // same function, same operand, same string).
            let call_key = trust_mir_extract::func_operand_name_in_body(tcx, body, func);
            // Trust (D1 increment 2): the `caller_location` ledger — see
            // `caller_location_only_keys`. EVERY call is recorded, so a key that
            // also names any other callee answers `false`.
            let is_caller_location = func.const_fn_def().is_some_and(|(did, _)| {
                tcx.intrinsic(did).is_some_and(|i| i.name == rustc_span::sym::caller_location)
            });
            self.caller_location_only_keys
                .entry(call_key.clone())
                .and_modify(|all| *all &= is_caller_location)
                .or_insert(is_caller_location);
            // Trust (D1 increment 1): a call that hands back a `Formatter`-bearing
            // value mints a formatter this bundle did not receive from its caller.
            // Trust (D1 increment 2): except core's `PadAdapter::wrap` and the
            // private `Formatter::wrap_buf` it calls (`callee_wraps_formatter_in_
            // pad_adapter`): the formatter they return writes into a `PadAdapter`
            // over the writer of the formatter they were GIVEN (source-audited,
            // docs/TCB.md "Formatting premises" P2), so it names no writer the
            // sink did not supply.
            if let Some(destination) = destination
                && ty_mentions_formatter(tcx, destination.ty(&body.local_decls, tcx).ty)
                && !func
                    .const_fn_def()
                    .is_some_and(|(did, _)| callee_wraps_formatter_in_pad_adapter(tcx, did))
            {
                self.formatter_minted = true;
            }
            let Some((callee_def_id, gen_args)) = func.const_fn_def() else {
                // An INDIRECT call (fn pointer / erased callable): no body to
                // witness, ever.
                // Trust (P-UB, absent UB-check members): and never a UB-check
                // candidate, so its key disqualifies any candidate rendered alike.
                self.ub_check_other_callee_keys.insert(call_key.clone());
                self.call_keys.record_uncertified(call_key);
                self.poison_carriers(tcx, &output_traits, PoisonSource::IndirectCall);
                continue;
            };
            // Trust (P-UB, absent UB-check members, 2026-11-08): record this direct
            // call for the absent-UB-check fold-site judgment at facts time. A
            // candidate is a plain call from a walked AUTHENTIC-SYSROOT body to an
            // authenticated `precondition_check` (never the `panic_nounwind`
            // entries: an absent call to one of those IS the abort), with no generic
            // argument and no trait object in its arguments or its outputs, so not
            // walking its body hides no vtable from the poison analysis above. Any
            // other call rendering the same key disqualifies the key.
            let ub_check_candidate = is_plain_call
                && gen_args.is_empty()
                && output_traits.is_empty()
                && super::crate_is_authentic_foundational(tcx, body_def_id.krate)
                && def_is_ub_check_precondition_fn(tcx, callee_def_id)
                && args.iter().all(|arg| {
                    dyn_principals_in_ty(tcx, arg.node.ty(&body.local_decls, tcx)).is_empty()
                });
            if ub_check_candidate {
                self.ub_check_precondition_candidates.push((callee_def_id, call_key.clone()));
            } else {
                self.ub_check_other_callee_keys.insert(call_key.clone());
            }
            // Trust (96a18b names-split finishers): record this direct call
            // for the fold-site judgment at facts time — a machinery body's
            // absent callees are the markers P-SPLIT excuses; any other body's
            // call to the same rendered key disqualifies that key, so a marker
            // is never excused on a name another member could have minted.
            if caller_is_names_split_member {
                self.names_split_candidates.push((callee_def_id, call_key.clone()));
            } else {
                self.names_split_other_callee_keys.insert(call_key.clone());
            }
            // Trust (96a18b names-split finishers, G-MEMBER evidence): every
            // DIRECT walked call into the names-split machinery must discharge
            // the invariant its callee's uncounted panic site rests on, or the
            // exemption recorded in `names_split_member_walked` is void. An
            // indirect call into the machinery has no `const_fn_def` and never
            // reaches here: it also cannot be the edge that walked a machinery
            // BODY in (the bundle closure follows direct callees), and a
            // diverging indirect call is still counted at its own terminator.
            match names_split_member_kind(tcx, callee_def_id) {
                Some(NamesSplitMember::Finisher(arity)) => {
                    if !finisher_names_arg_well_formed(tcx, body, args, arity) {
                        self.names_split_unproven = true;
                        if probe_enabled() {
                            with_no_trimmed_paths!(eprintln!(
                                "TRUST_DYN_RELIANCE_PROBE:   G-MEMBER: names-split \
                                 evidence FAILED: finisher `{}` called from `{}` \
                                 without a constant names argument of arity {arity}",
                                tcx.def_path_str(callee_def_id),
                                tcx.def_path_str(body_def_id)
                            ));
                        }
                    }
                }
                Some(NamesSplitMember::NaryFinisher) => {
                    // Trust: inherit only the fixed wrapper's already-required
                    // names premise, with receiver and ordered fields from that
                    // same immutable parameter tuple. One unrelated incoming
                    // edge voids the entire exemption, even if another edge is
                    // a valid wrapper. The shape helper grants no authority.
                    let forwarded = is_plain_call
                        && match caller_names_split_kind {
                            Some(NamesSplitMember::Finisher(arity)) => {
                                trust_mir_extract::debug_fixed_finisher_forwards_inputs(
                                    tcx, body, block_id, arity,
                                )
                            }
                            _ => false,
                        };
                    if forwarded {
                        self.names_split_forwarded_nary.insert(callee_def_id);
                    } else {
                        self.names_split_unproven = true;
                        if probe_enabled() {
                            with_no_trimmed_paths!(eprintln!(
                                "TRUST_DYN_RELIANCE_PROBE:   G-MEMBER: names-split \
                                 evidence FAILED: n-ary finisher `{}` called from `{}` \
                                 without authenticated fixed-wrapper forwarding",
                                tcx.def_path_str(callee_def_id),
                                tcx.def_path_str(body_def_id)
                            ));
                        }
                    }
                }
                Some(NamesSplitMember::IsAlignedTo) => {
                    // Discharged by a constant power-of-two operand, or by
                    // the caller being a UB-check member itself: inside a
                    // sysroot `precondition_check`, `is_aligned_to` IS the
                    // alignment precondition test (fed the check's captured
                    // `align_of::<T>()`), so its abort is the very abort
                    // P-UB already excuses in that body.
                    if !body_is_ub_check_member(tcx, body_def_id)
                        && !args
                            .get(1)
                            .is_some_and(|arg| const_pow2_usize_operand(tcx, body, &arg.node))
                    {
                        self.names_split_unproven = true;
                        if probe_enabled() {
                            with_no_trimmed_paths!(eprintln!(
                                "TRUST_DYN_RELIANCE_PROBE:   G-MEMBER: names-split \
                                 evidence FAILED: `is_aligned_to` called from `{}` \
                                 without a constant power-of-two alignment",
                                tcx.def_path_str(body_def_id)
                            ));
                        }
                    }
                }
                Some(NamesSplitMember::EncodeUtf8Raw) => {
                    // Its buffer-length panic is caller-discharged only inside
                    // authentic core (every core caller passes a `char` code
                    // point and a buffer of at least `char::MAX_LEN_UTF8`).
                    if !super::crate_is_authentic_foundational(tcx, body_def_id.krate) {
                        self.names_split_unproven = true;
                        if probe_enabled() {
                            with_no_trimmed_paths!(eprintln!(
                                "TRUST_DYN_RELIANCE_PROBE:   G-MEMBER: names-split \
                                 evidence FAILED: `encode_utf8_raw` called from \
                                 non-sysroot body `{}`",
                                tcx.def_path_str(body_def_id)
                            ));
                        }
                    }
                }
                Some(NamesSplitMember::CharIntoSearcher | NamesSplitMember::PanicFmt) | None => {}
            }
            match ty::Instance::try_resolve(tcx, typing_env, callee_def_id, gen_args) {
                Ok(Some(instance)) => {
                    let is_virtual = matches!(instance.def, ty::InstanceKind::Virtual(..));
                    if let ty::InstanceKind::Virtual(method_def_id, _slot) = instance.def {
                        self.call_keys.record_dyn_site(call_key.clone());
                        // The site stays in THIS lane (gate 0's ledger says so
                        // above); the reduction is only asked its one operand
                        // question here, because this is the sole point the
                        // defining body is in hand.
                        let write_fmt_from_str_backed = virtual_write_fmt_site_is_from_str_backed(
                            tcx,
                            method_def_id,
                            body,
                            block_id,
                            args,
                        );
                        self.virtual_sites.push(VirtualCallSite {
                            call_key,
                            method_def_id,
                            args: instance.args,
                            write_fmt_from_str_backed,
                        });
                    } else if is_plain_call
                        && self
                            .static_str_write_fmt
                            .observe_call(tcx, body, typing_env, block_id, func, args)
                    {
                        self.call_keys.record_write_fmt_site(call_key);
                    } else {
                        self.call_keys.record_uncertified(call_key);
                    }
                    // A callee whose body is NOT in this bundle may hand back a
                    // `dyn` value of its own making. Most such calls also carry an
                    // `Assert(false)` that fails the path closed on its own, but
                    // the discharge arms (ABI-total, the total-callee allowlists,
                    // the `?` desugar) do not — so refuse on the signature rather
                    // than reason about which arm claimed the call. DEFERRED:
                    // whether the body ends up bundled is not decided yet.
                    // Trust (D1 increment 2): whether the call was a VIRTUAL
                    // nested-formatter site rides along, so the settle step can
                    // name that source (`PoisonSource::NestedFormatterOutput`).
                    if !output_traits.is_empty() {
                        self.deferred_output_poisons.push((
                            instance.def_id(),
                            output_traits,
                            is_virtual && nested_formatter_trait(tcx, instance.def_id()).is_some(),
                        ));
                    }
                }
                // Unresolved dispatch: the target is unknown, so its outputs are.
                _ => {
                    self.call_keys.record_uncertified(call_key);
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
        for (callee, principals, nested_formatter_site) in deferred {
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
            // Trust (D1 increment 2): identical poison; the source names the
            // nested-formatter case for the writer-relative facts alone.
            let source = if nested_formatter_site {
                PoisonSource::NestedFormatterOutput(&name)
            } else {
                PoisonSource::UnbundledCallee(&name)
            };
            self.poison_carriers(tcx, &principals, source);
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
            // one. `tests/ui/trust/dyn_dispatch_reliance_slice_of_dyn_not_a_vtable.rs`
            // pins it with a local trait: a derive pair cannot, since both arities
            // fail on unrelated rows with byte-identical stderr either way.
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
    /// Trust (2026-09-14): see `StaticStrWriteFmtFacts::deferrable_key_for_instance`.
    /// The bundle closure asks this before expanding a foreign instance; a
    /// `Some(key)` means "do not bundle this body yet — if `resolve_reliance`
    /// discharges `key`, the root's call is covered by the reduction and the body
    /// stays out; otherwise expand it after all".
    pub(crate) fn write_fmt_reduction_deferral_key(
        &self,
        tcx: TyCtxt<'tcx>,
        instance: &ty::Instance<'tcx>,
        root_def_id: DefId,
    ) -> Option<String> {
        if std::env::var_os("TRUST_NO_STATIC_STR_WRITE_FMT").is_some() {
            return None;
        }
        self.static_str_write_fmt.deferrable_key_for_instance(tcx, instance, root_def_id)
    }

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
            // Trust (D1 increment 2): the NESTED-FORMATTER decision of a
            // formatting-impl root, taken HERE — under the reliance guard, after
            // the case splits above — so a local target's verdict is forced
            // exactly as C-FLOW forces one (same in-progress and cycle bails).
            // It RECORDS; it discharges nothing (`out` is untouched), and its only
            // reader is `writer_relative_facts`.
            if super::fmt_writer_relative::formatting_impl_root(tcx, root_def_id) {
                let decision = self.decide_nested_formatters(tcx, root_def_id, probe);
                self.nested_formatters = Some(decision);
            }
        }
        self.static_str_write_fmt.resolve_reliance(tcx, root_def_id, out, probe, &self.call_keys);
    }

    /// Trust (D1 increment 2): for every VIRTUAL `<dyn fmt::Debug|Display>::fmt`
    /// site (a NESTED FORMATTER — `derive(Debug)`'s `field(&self.0)` reaches one
    /// inside core's builders), is its whole target set enumerable from this
    /// bundle's coercions, and is every target one whose panics are exactly its
    /// `Formatter`'s writer's? See [`nested_formatter_target_admitted`] for the
    /// three admitted target kinds.
    ///
    /// The enumeration is C-FLOW's, verbatim in its conjuncts: no undecomposable
    /// carrier, the trait not poisoned, a non-vacuous coerced set of at most
    /// [`MAX_ENUMERATED_SELF_TYPES`], each `Self` resolved by
    /// [`resolve_virtual_target`]. What differs is only the target bar: C-FLOW
    /// demands ABSOLUTE panic-freedom (and so declines core's `&T` forwarding
    /// impl on locality), this admits a writer-relative one. That is why an
    /// admitted key is recorded here and never written to `out`.
    fn decide_nested_formatters(
        &self,
        tcx: TyCtxt<'tcx>,
        root_def_id: DefId,
        probe: bool,
    ) -> NestedFormatterDecision {
        let mut decision = NestedFormatterDecision::default();
        for site in &self.virtual_sites {
            let Some(trait_def_id) = nested_formatter_trait(tcx, site.method_def_id) else {
                continue;
            };
            let admitted = self.nested_formatter_site_admitted(
                tcx,
                site,
                trait_def_id,
                root_def_id,
                &mut decision.local_targets,
            );
            if probe {
                eprintln!(
                    "TRUST_DYN_RELIANCE_PROBE: nested formatter site={} => {}",
                    site.call_key,
                    if admitted { "ADMITTED (writer-relative)" } else { "refused" },
                );
            }
            if admitted {
                decision.accepted_keys.insert(site.call_key.clone());
            } else {
                decision.rejected_keys.insert(site.call_key.clone());
            }
        }
        decision
    }

    /// Trust (D1 increment 2): one nested-formatter site. See
    /// [`Self::decide_nested_formatters`].
    fn nested_formatter_site_admitted(
        &self,
        tcx: TyCtxt<'tcx>,
        site: &VirtualCallSite<'tcx>,
        trait_def_id: DefId,
        root_def_id: DefId,
        local_targets: &mut Vec<DefId>,
    ) -> bool {
        if self.opaque_carrier_seen || self.poisoned.contains(&trait_def_id) {
            return false;
        }
        // No coercion: the site is unreachable in this bundle, or its receiver
        // came by a route that would have poisoned the trait. Vacuity stays the
        // fatal row, as it does for C-FLOW.
        let key = site_dyn_key(tcx, trait_def_id, site);
        let Some(self_tys) = self.coerced.get(&key) else {
            return false;
        };
        if self_tys.is_empty() || self_tys.len() > MAX_ENUMERATED_SELF_TYPES {
            return false;
        }
        // Trust: current core's n-ary formatter takes a reference to each
        // already-erased value. Its authenticated reference impl forwards back
        // into this exact target set. Close only that edge, while still requiring
        // a concrete base target and checking every other member normally.
        let mut concrete_target_seen = false;
        for &self_ty in self_tys {
            let Some(target) = resolve_virtual_target(tcx, site, self_ty) else {
                return false;
            };
            let same_set = nested_formatter_returns_to_same_set(tcx, key, self_ty, target);
            if probe_enabled() {
                with_no_trimmed_paths!(eprintln!(
                    "TRUST_DYN_RELIANCE_PROBE: nested formatter candidate `{self_ty}` target `{}` same-set forwarding={same_set}",
                    tcx.def_path_str(target.def_id()),
                ));
            }
            if same_set {
                // Unknown-origin poisons alone do not prove that a user-authored
                // unsafe body could not create a cyclic reference chain. This
                // credit is only for safe callers of core's forwarding impls.
                if self.non_sysroot_unsafe_walked {
                    return false;
                }
                continue;
            }
            concrete_target_seen = true;
            if !nested_formatter_target_admitted(
                tcx,
                trait_def_id,
                self_ty,
                target,
                root_def_id,
                0,
                local_targets,
            ) {
                return false;
            }
        }
        concrete_target_seen
    }

    /// Trust (D1 increment 1): the WRITER-EDGE call keys of this bundle, when —
    /// and only when — every `core::fmt::Write` value in it provably came from the
    /// root's own `&mut Formatter` parameter, and no body in it can panic without
    /// a row of its own. `None` otherwise (fail-closed).
    ///
    /// Trust (D1 increment 2, 2026-09-25): the returned
    /// [`WriterRelativeFacts`](super::fmt_writer_relative::WriterRelativeFacts)
    /// now also carries the admitted NESTED-FORMATTER keys, the
    /// `caller_location` keys, and the local formatting impls the nested sites
    /// can reach (for error transparency). See the increment-2 conjuncts below.
    ///
    /// A writer-edge key names `<dyn fmt::Write as fmt::Write>::{write_str,
    /// write_char}` virtual sites. Returning it DISCHARGES NOTHING: it is never
    /// written into `dyn_contract_total_callees`, and the shared evidence bar
    /// (`dyn_target_is_verified_panic_free`) never reads it. Its only reader is
    /// `fmt_writer_relative`, which uses it to publish a CONDITIONAL verdict
    /// ("panic-free relative to its Formatter's writer") whose rows stay
    /// `runtime-checked`.
    ///
    /// The conjuncts, each fail-closed:
    /// * the facts were gathered over a completed walk: no undecomposable carrier
    ///   (`opaque_carrier_seen`), so every poison source was named;
    /// * `fmt::Write` is poisoned by NO source but the root's `&mut Formatter`
    ///   parameter — not `self`, a constant, a cast, a thread-local, an indirect,
    ///   unresolved or unbundled call — and is not forge-poisoned; (increment 2:
    ///   the two exceptions are [`PoisonSource::PadAdapterConstant`], justified by
    ///   the source audit on `constant_ty_carries_dyn_only_through_pad_adapter`,
    ///   and [`PoisonSource::NestedFormatterOutput`], justified by requiring EVERY
    ///   nested-formatter site to be admitted, below;)
    /// * NO `Unsize` coercion anywhere in the bundle builds a `fmt::Write` vtable
    ///   (or a subtrait's, which `record` files under `fmt::Write` too) — so the
    ///   bundle cannot hand a writer of its own choosing to a writer edge;
    ///   (increment 2: except for core's private `PadAdapter`, which wraps the
    ///   writer of the formatter it was given — `ty_is_core_pad_adapter`;)
    /// * NO bundled call returns a `Formatter`-bearing value (`Formatter::new`,
    ///   `with_options`); (increment 2: except core's `PadAdapter::wrap` /
    ///   `Formatter::wrap_buf`, which return a formatter over a `PadAdapter` of
    ///   the given formatter's writer;)
    /// * G-MEMBER: no walked body — the root included — has a panic site that
    ///   mints no row of its own (`first_unrowed_panic_site`); (increment 2:
    ///   UB-check members are not counted, and when one was walked, NO walked body
    ///   outside the authentic sysroot may use `unsafe`;)
    /// * every site under a returned key is a virtual `write_str`/`write_char` of
    ///   the REAL `core::fmt::Write` (by `DefId`) on a `dyn fmt::Write` receiver,
    ///   and gate 0's ledger says the key names ONLY virtual sites — the key is
    ///   the string the rows are matched by, and it is many-to-one;
    /// * (increment 2) a nested-formatter key is returned only when the decision
    ///   was taken, EVERY nested-formatter site in the bundle was admitted (a
    ///   single refused one refuses the class), and gate 0 says the key names only
    ///   virtual sites, all nested-formatter ones;
    /// * (increment 2) a `caller_location` key is returned only when every
    ///   bundled call rendering to it is that intrinsic, and only beside at least
    ///   one writer-edge or nested-formatter key.
    // Trust (D1 increment 2): `pub(super)`, not `pub(crate)` — the facts type is
    // `pub(super)` in `fmt_writer_relative`, and the only caller is in
    // `trust_verify` (a wider method would be a `private_interfaces` warning).
    pub(super) fn writer_relative_facts(
        &self,
        tcx: TyCtxt<'tcx>,
    ) -> Option<super::fmt_writer_relative::WriterRelativeFacts> {
        // Trust (identity-anchor sweep, 2026-09-28): the REAL `fmt::Write` is the
        // diagnostic item AND authentic resident core; a whole-`core` substitute's
        // records no writer-relative facts at all.
        let fmt_write = super::authentic_core_diagnostic_item(tcx, rustc_span::sym::FmtWrite)?;
        // Trust (D1 increment 2): a coercion to `dyn fmt::Write` is admitted only
        // when EVERY `Self` coerced under a `fmt::Write` key is core's `PadAdapter`.
        // Order-insensitive: an existence test over the entries.
        #[allow(rustc::potential_query_instability)]
        let coerces_a_foreign_writer = self.coerced.iter().any(|(key, self_tys)| {
            key.def_id == fmt_write
                && !self_tys.iter().all(|&self_ty| ty_is_core_pad_adapter(tcx, self_ty))
        });
        // Trust (D1 increment 2): name every conjunct's state, so a refusal (or an
        // admission) of the class is a measurement rather than an inference.
        if probe_enabled() {
            eprintln!(
                "TRUST_DYN_RELIANCE_PROBE: writer-relative facts: opaque_carrier={} \
                 write_poisoned_beyond_formatter_param={} write_forge_poisoned={} \
                 formatter_minted={} unrowed_panic_site={} ub_check_member={} \
                 names_split_member={} names_split_unproven={} \
                 non_sysroot_unsafe={} foreign_writer_coercion={} pad_adapter_constant={} \
                 nested_formatter_output_poisoned={} nested_formatters_decided={}",
                self.opaque_carrier_seen,
                self.poisoned_beyond_formatter_param.contains(&fmt_write),
                self.forge_poisoned_beyond_pad_adapter.contains(&fmt_write),
                self.formatter_minted,
                self.panic_site_in_bundle,
                self.ub_check_member_walked,
                self.names_split_member_walked,
                self.names_split_unproven,
                self.non_sysroot_unsafe_walked,
                coerces_a_foreign_writer,
                self.pad_adapter_constant_seen,
                self.nested_formatter_output_poisoned,
                self.nested_formatters.is_some(),
            );
        }
        if self.opaque_carrier_seen
            || self.poisoned_beyond_formatter_param.contains(&fmt_write)
            || self.forge_poisoned_beyond_pad_adapter.contains(&fmt_write)
            || self.formatter_minted
            || self.panic_site_in_bundle
            || (self.ub_check_member_walked && self.non_sysroot_unsafe_walked)
            // Trust (96a18b names-split finishers): the exemption is void when
            // any walked call into the machinery failed its evidence check, and
            // carries the P-UB belt — a walked non-sysroot `unsafe` body could
            // have forged the `&str` the split searches (the premise proper is
            // docs/TCB.md P-SPLIT, resting on the same (1)/(2) as P-UB).
            || (self.names_split_member_walked
                && (self.names_split_unproven || self.non_sysroot_unsafe_walked))
            || !self.names_split_nary_walked.is_subset(&self.names_split_forwarded_nary)
            || coerces_a_foreign_writer
        {
            return None;
        }
        let method_named = |name: &str| {
            tcx.associated_items(fmt_write)
                .in_definition_order()
                .find(|item| item.opt_name().is_some_and(|item_name| item_name.as_str() == name))
                .map(|item| item.def_id)
        };
        let write_str = method_named("write_str")?;
        let write_char = method_named("write_char")?;
        let is_writer_edge = |site: &VirtualCallSite<'tcx>| {
            (site.method_def_id == write_str || site.method_def_id == write_char)
                && matches!(
                    site.args.first().and_then(|arg| arg.as_type()).map(|self_ty| *self_ty.kind()),
                    Some(ty::Dynamic(preds, ..))
                        if preds.principal_def_id() == Some(fmt_write)
                )
        };
        let mut keys: FxHashSet<String> = FxHashSet::default();
        for site in &self.virtual_sites {
            if is_writer_edge(site) {
                keys.insert(site.call_key.clone());
            }
        }
        #[allow(rustc::potential_query_instability)]
        keys.retain(|key| {
            self.call_keys.only_dyn_sites(key)
                && self
                    .virtual_sites
                    .iter()
                    .filter(|site| site.call_key == *key)
                    .all(|site| is_writer_edge(site))
        });
        // Trust (D1 increment 2): the NESTED-FORMATTER keys.
        let is_nested_site = |site: &VirtualCallSite<'tcx>| {
            nested_formatter_trait(tcx, site.method_def_id).is_some()
        };
        let has_nested_site = self.virtual_sites.iter().any(|site| is_nested_site(site));
        if self.nested_formatter_output_poisoned && !has_nested_site {
            // The source is only ever minted for a nested-formatter site; a
            // disagreement is a bug in this module, and it refuses.
            return None;
        }
        let mut nested_local_targets = Vec::new();
        if has_nested_site {
            let decision = self.nested_formatters.as_ref()?;
            if !decision.rejected_keys.is_empty() {
                return None;
            }
            #[allow(rustc::potential_query_instability)]
            for key in &decision.accepted_keys {
                let only_nested = self.call_keys.only_dyn_sites(key)
                    && self
                        .virtual_sites
                        .iter()
                        .filter(|site| site.call_key == *key)
                        .all(|site| is_nested_site(site));
                if !only_nested {
                    return None;
                }
                keys.insert(key.clone());
            }
            // Every nested site's key must be among the admitted ones.
            if !self
                .virtual_sites
                .iter()
                .filter(|site| is_nested_site(site))
                .all(|site| decision.accepted_keys.contains(&site.call_key))
            {
                return None;
            }
            nested_local_targets = decision.local_targets.clone();
        }
        // Trust (D1 increment 2): the `caller_location` keys — a total intrinsic
        // (it reads the caller's `Location` and cannot panic) that core's
        // `#[track_caller]` UB-check members call. Only beside real edges.
        if !keys.is_empty() {
            #[allow(rustc::potential_query_instability)]
            for (key, only_caller_location) in &self.caller_location_only_keys {
                if *only_caller_location {
                    keys.insert(key.clone());
                }
            }
        }
        // Trust (96a18b, P-SPLIT): the machinery's own absent-callee keys.
        // Reaching this return at all means the per-call evidence held
        // (`names_split_unproven` refused above), so these markers stand
        // discharged by the same evidence that excused the members' panic
        // sites in G-MEMBER.
        let names_split_callee_keys: FxHashSet<String> = self
            .names_split_candidates
            .iter()
            .filter(|(callee, key)| {
                !self.observed_bodies.contains(callee)
                    && !self.names_split_other_callee_keys.contains(key)
            })
            .map(|(_, key)| key.clone())
            .collect();
        // Trust (P-UB, absent UB-check members, 2026-11-08): the absent
        // `precondition_check` keys, under the P-UB belt (none while a walked
        // non-sysroot body uses `unsafe` — the condition that refuses the class
        // above when a UB-check member is WALKED). Recording none only leaves
        // their markers unexcused, which is the refusal direction.
        let ub_check_callee_keys = absent_ub_check_callee_keys(
            &self.ub_check_precondition_candidates,
            &self.observed_bodies,
            &self.ub_check_other_callee_keys,
            self.non_sysroot_unsafe_walked,
        );
        if probe_enabled() && !ub_check_callee_keys.is_empty() {
            #[allow(rustc::potential_query_instability)]
            let mut named: Vec<&str> = ub_check_callee_keys.iter().map(String::as_str).collect();
            named.sort_unstable();
            eprintln!(
                "TRUST_DYN_RELIANCE_PROBE:   P-UB: absent UB-check fold keys (not walked, \
                 called only from sysroot bodies): {named:?}"
            );
        }
        Some(super::fmt_writer_relative::WriterRelativeFacts {
            excusable_keys: keys,
            nested_local_targets,
            names_split_callee_keys,
            ub_check_callee_keys,
        })
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
        if self.cflow_discharges(tcx, site, trait_def_id, root_def_id, probe) {
            return true;
        }

        // ---- C-SEALED ----------------------------------------------------
        // Rung 2 at a virtual site. Reached only after C-FLOW declined, which is
        // the cheaper order in the common case AND the one that keeps every
        // C-FLOW probe line printing exactly as before; the two are independent,
        // so a C-FLOW decline is never evidence against this one. In particular a
        // POISONED trait (a `dyn`-bearing root parameter) is fatal to C-FLOW's
        // value-flow enumeration and irrelevant here, because this certificate
        // quantifies over the impl set instead.
        //
        // DELEGATED, for the reason `dyn_call_relies_on_trait_panic_free_contract`
        // records one screen below: an earlier draft of THAT function re-derived
        // what looked like the same conjuncts and dropped one. The same trap is
        // open here — sealedness, non-empty impl set, per-impl independent
        // verdict, `#[trust::skip]`, the assumption-root gate, the self-scan,
        // in-progress and MIR-cycle bails — so this calls the one predicate.
        //
        // `root_def_id` is passed as the scanned body: forcing
        // `trust_proof_results` on the root of the bundle whose reliance is being
        // decided is the query cycle the parameter exists to refuse.
        //
        // THE ONE PREMISE C-SEALED DOES NOT INHERIT FROM RUNG 2. A type parameter
        // is resolved by the compiler and cannot be forged; a vtable pointer can.
        // So the impl-set argument holds only while every `dyn T` in reach was
        // built by a real `Unsize` coercion — unwitnessed is fine, REINTERPRETED
        // is not. `forge_poisoned` carries exactly that split and
        // `opaque_carrier_seen` is its backstop (a type this walk could not
        // decompose may hide the very cast that would have raised it). Both are
        // refusals C-FLOW already makes; C-SEALED keeps the forging half and
        // drops the value-flow half, which is the whole difference between them.
        //
        // Trust (D4 increment B): the shape is `Virtual`, so rung 2's FOREIGN-trait
        // arm declines here — it serves generic call sites only, for the forging
        // reason above, which a foreign trait makes unanswerable from this bundle.
        if !self.opaque_carrier_seen
            && !self.forge_poisoned.contains(&trait_def_id)
            && super::sealed_generic_dispatch_impls_all_panic_free(
                tcx,
                root_def_id,
                trait_def_id,
                site.method_def_id,
                super::foreign_trait_closure::RelianceShape::Virtual,
            )
        {
            if probe {
                with_no_trimmed_paths!(eprintln!(
                    "TRUST_DYN_RELIANCE_PROBE:   C-SEALED trait={}",
                    tcx.def_path_str(trait_def_id)
                ));
            }
            return true;
        }
        false
    }

    /// C-FLOW for one virtual site: is the set of `Self` types that can reach it
    /// enumerable from this bundle's `Unsize` coercions, and is every one of them
    /// verified panic-free?
    ///
    /// Split out of `site_discharges` when C-SEALED was added, verbatim — every
    /// decline path and probe line is the one that was here before, so the two
    /// certificates compose by `||` rather than by one reaching into the other's
    /// bail conditions.
    fn cflow_discharges(
        &self,
        tcx: TyCtxt<'tcx>,
        site: &VirtualCallSite<'tcx>,
        trait_def_id: DefId,
        root_def_id: DefId,
        probe: bool,
    ) -> bool {
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
                // Trust (2026-09-21): the `write_fmt` reduction, per enumerated
                // `Self`. When this `Self` does NOT override `write_fmt`, the
                // target just resolved IS core's default body — a sysroot body,
                // which the bar above never re-derives (D4-A) — and that is the
                // exact body `static_str_write_fmt` certifies: on a `from_str`-
                // backed `Arguments` it performs ONE `<Self as Write>::write_str`
                // and returns its result. The obligation therefore transfers to
                // this `Self`'s own `write_str`, which the same bar then judges.
                //
                // MEASURED before this arm, one compilation, one type `Buf` that
                // inherits the default: the concrete `write!(b, "lit")` printed
                // `=> DISCHARGED (every site reduces to its own proved write_str)`
                // while `write!(w, "lit")` through `&mut dyn Write` — the SAME
                // monomorphic instance, `Item(core::fmt::Write::write_fmt)` at
                // `[Buf]` — printed `declined: target ... is not local to this
                // crate`. One body, credited through one entry and refused
                // through the other, on locality. The module header's C-SEALED
                // paragraph already states the vtable slot for a default method
                // is "the trait default body it also enumerates".
                //
                // EVERY gate of the reduction is re-run here, none bypassed:
                //   gate 1 — `instance_is_core_default_write_fmt(target)`, on the
                //            RESOLVED target of THIS `Self`, so an overriding impl
                //            (a foreign `fn write_fmt { panic!() }`) never rides;
                //   gate 3 — `write_fmt_from_str_backed`, decided at observation;
                //   gate 4 — this `Self`'s own `write_str`, resolved by the same
                //            resolver the concrete lane uses, through the same bar;
                //   gate 0 — untouched: the site is filed in THIS lane's ledger
                //            and the discharge rides `all_discharged` over every
                //            site under the key, so an aliased or unbacked
                //            neighbour still vetoes the whole group;
                //   gate 2 — is that same all-or-nothing, per site.
                // Failure direction is over-refusal today, and the arm only
                // admits: a `write_str` that panics, is `#[trust::skip]`ped,
                // foreign, cyclic, or unproved fails gate 4 exactly as before.
                if site.write_fmt_from_str_backed
                    && instance_is_core_default_write_fmt(tcx, &target)
                    && let Some(fmt_write) =
                        super::authentic_core_diagnostic_item(tcx, rustc_span::sym::FmtWrite)
                    && let Some(write_str) = resolve_write_str_for_args(tcx, fmt_write, target.args)
                    && dyn_target_is_verified_panic_free(tcx, write_str, root_def_id)
                {
                    if probe {
                        with_no_trimmed_paths!(eprintln!(
                            "TRUST_DYN_RELIANCE_PROBE:   C-FLOW admitted {self_ty} via the \
                             write_fmt reduction (reduces to its own proved {})",
                            tcx.def_path_str(write_str.def_id())
                        ));
                    }
                    continue;
                }
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
///
/// Trust (D4 increment B, 2026-09-25): the call shape is `Virtual`, which the
/// foreign-trait arm (`foreign_trait_closure`) never serves — a vtable can be
/// minted in dependency bodies no walk of this compilation sees — so a FOREIGN
/// trait still answers `false` here, exactly as before that increment.
fn dyn_call_relies_on_trait_panic_free_contract(tcx: TyCtxt<'_>, method_def_id: DefId) -> bool {
    trait_panic_free::generic_call_relies_on_panic_free_contract(
        tcx,
        method_def_id,
        super::foreign_trait_closure::RelianceShape::Virtual,
    )
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
    args: ty::GenericArgs<'tcx>,
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
    // Trust (D1 increment 1): the pre-conjuncts are factored out VERBATIM so the
    // writer-relative bar (`fmt_writer_relative`) asks exactly the same ones; the
    // only thing that differs between the two bars is which rows they excuse.
    if !target_admits_independent_verdict(tcx, def_id, root_def_id) {
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

/// The conjuncts of [`dyn_target_is_verified_panic_free`] that come BEFORE its
/// evidence bar: not a self-discharge, not `#[trust::skip]`/`assume_total`, local,
/// no authored clause, and no query cycle or in-progress computation up the
/// stack. Shared with the writer-relative bar (`fmt_writer_relative`) so the two
/// bars can never disagree about which bodies may be asked for a verdict at all.
pub(super) fn target_admits_independent_verdict(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    root_def_id: DefId,
) -> bool {
    target_pre_conjuncts_hold(tcx, def_id, root_def_id, true)
}

/// [`target_admits_independent_verdict`] with the re-derivation COST BOUND left
/// out and nothing charged: every other pre-conjunct, in the same order, from the
/// same function. For a caller that must force a whole SET of targets and checks
/// the budget for the set in aggregate BEFORE forcing any of them
/// (`foreign_trait_closure`, via `foreign_rederivation::
/// reserve_foreign_rederivations`); it still passes each target through
/// [`dyn_target_is_verified_panic_free`] afterwards, which re-checks everything
/// and takes the charge. Never credit: it can only decline earlier.
pub(super) fn target_pre_conjuncts_hold_budget_free(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    root_def_id: DefId,
) -> bool {
    target_pre_conjuncts_hold(tcx, def_id, root_def_id, false)
}

/// The one body of the two functions above. `charge_budget`: admit a foreign
/// body under the cost bound (charging it), or read only the budget-free
/// re-derivation conjuncts.
fn target_pre_conjuncts_hold(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    root_def_id: DefId,
    charge_budget: bool,
) -> bool {
    if def_id == root_def_id {
        return false;
    }
    // A `#[trust::skip]` body is UNVERIFIED by user decree and a
    // `#[trust::assume_total]` one is an axiom, not a proof. Either would make
    // the case split a laundering step for the very panic it hides.
    if item_has_trust_skip_attr(tcx, def_id) || item_has_trust_attr(tcx, def_id, "assume_total") {
        return false;
    }
    // Trust (D4-A, 2026-09-24): a foreign body is admitted to the bar ONLY when
    // this compilation can RE-DERIVE its verdict (declared by crate identity,
    // statically linked, non-sysroot, encoded MIR, no interposable symbol, no
    // user `unsafe` source, within the cost bound — which this call charges).
    // Admission is not credit: the bar below still has to pass on a verdict
    // computed HERE. No dependency verdict, bit, or policy is ever read.
    if !def_id.is_local() {
        let decline = if charge_budget {
            super::foreign_rederivation::admit_foreign_rederivation(tcx, def_id)
        } else {
            super::foreign_rederivation::foreign_rederivation_decline(tcx, def_id)
        };
        if decline.is_some() {
            return false;
        }
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
    true
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
    // Trust (D4-A, 2026-09-24): name the re-derivation conjunct that declined.
    // `peek`, not `admit`: this probe must not charge the cost bound.
    if !def_id.is_local()
        && let Some(decline) = super::foreign_rederivation::peek_foreign_rederivation(tcx, def_id)
    {
        return decline.reason().to_string();
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
// Trust (D1 increment 1): `pub(super)` so `fmt_writer_relative`'s root predicate
// refuses exactly the bodies this bar refuses.
pub(super) fn body_carries_authored_clause(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    match def_id.as_local() {
        Some(local_def_id) => {
            if rustc_middle::mir::trust_contract::TrustContractBundle::def_may_have_contracts(
                tcx,
                local_def_id,
            ) {
                return true;
            }
        }
        // Trust (D4-A, 2026-09-24): a foreign def reaches here only when it is
        // re-derivable (`dyn_target_is_verified_panic_free` admits it first).
        // Surface 1 has no HIR to read, so its own arm reads the rmeta
        // `trust_contracts` row — the same row the re-derivation conjoins as
        // hypotheses — and fails closed when attributes cannot be queried. Any
        // other foreign def, or an unreadable one, is clause-bearing: a body whose
        // clauses cannot be read is not one whose verdict is known unconditional.
        None => {
            if !super::foreign_rederivation::foreign_body_rederivable_here(tcx, def_id)
                || super::foreign_rederivation::foreign_signature_clause_or_unreadable(tcx, def_id)
            {
                return true;
            }
        }
    }
    // Attributes are queryable here: always for a local def, and for a foreign
    // one `foreign_signature_clause_or_unreadable` returned `true` above unless
    // [`super::attrs_queryable`] held.
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
            .explicit_super_clauses_of(current)
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
            .explicit_super_clauses_of(current.def_id)
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
    /// canonical instance is `Display::fmt`'s `f: &mut Formatter<'_>`, which is
    /// reported as [`Self::RootFormatterParam`] since D1 increment 1.
    RootParam,
    /// Trust (D1 increment 1): the bundle root's parameter of type exactly
    /// `&mut core::fmt::Formatter<'_>`. Poisons EXACTLY as [`Self::RootParam`]
    /// does, for every certificate; the writer-relative facts alone tell the two
    /// apart (`poisoned_beyond_formatter_param`).
    RootFormatterParam,
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
    /// Trust (D1 increment 2): a [`Self::Constant`] whose type carries a trait
    /// object ONLY through core's private `fmt::builders::PadAdapter`
    /// (`constant_ty_carries_dyn_only_through_pad_adapter`). Poisons exactly as
    /// `Constant` does for every certificate (same `forged` answer); only the
    /// writer-relative facts tell the two apart.
    PadAdapterConstant,
    /// Trust (D1 increment 2): an [`Self::UnbundledCallee`] that is a VIRTUAL
    /// `<dyn fmt::Debug|Display>::fmt` site — a nested formatter handed the
    /// `&mut Formatter`. Poisons exactly as `UnbundledCallee` does; only the
    /// writer-relative facts tell the two apart, and they accept it only when
    /// every such site's enumerated targets were admitted.
    NestedFormatterOutput(&'a str),
}

impl PoisonSource<'_> {
    /// Does this source mean the vtable was built by a REAL `Unsize` coercion
    /// this bundle merely did not witness — as opposed to arbitrary bits that
    /// could have been reinterpreted as one?
    ///
    /// Read by C-SEALED only. `true` keeps that certificate available (the impl
    /// set still bounds the target); `false` withdraws it. The match is
    /// exhaustive on purpose: a new `PoisonSource` must be classified here, and
    /// the answer for anything uncertain is `false`.
    ///
    /// `UnclassifiableUnsize` IS an `Unsize` and would qualify on its name — it
    /// is `false` anyway, because "a shape `classify_unsize` could not put in a
    /// shape" is a catch-all, and a catch-all is the one place a forging
    /// operation would arrive unlabelled.
    fn vtable_origin_is_a_real_coercion(&self) -> bool {
        match self {
            Self::RootParam
            | Self::RootFormatterParam
            | Self::RootReturn
            | Self::IndirectCall
            | Self::UnresolvedCall
            | Self::UnbundledCallee(_)
            | Self::NestedFormatterOutput(_) => true,
            Self::CastTarget
            | Self::ThreadLocal
            | Self::Constant
            | Self::PadAdapterConstant
            | Self::UnclassifiableUnsize => false,
        }
    }
}

impl std::fmt::Display for PoisonSource<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RootParam => f.write_str("a ROOT PARAMETER (the caller chose this vtable)"),
            Self::RootFormatterParam => {
                f.write_str("the ROOT's `&mut Formatter` PARAMETER (the caller chose this vtable)")
            }
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
            Self::PadAdapterConstant => f.write_str(
                "a CONSTANT operand carrying a trait object only through core's `PadAdapter`",
            ),
            Self::NestedFormatterOutput(callee) => {
                write!(f, "the `&mut Formatter` handed to NESTED FORMATTER `{callee}`")
            }
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
                    walk(tcx, instantiated_field_ty(tcx, field, *args), fuel, visited, out);
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
    args: ty::GenericArgs<'tcx>,
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
    args: ty::GenericArgs<'tcx>,
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

/// These casts preserve the same carrier bits; they do not mint a vtable or
/// discharge pointer validity. Earlier unknown-origin poisons remain in force.
/// In particular, a matching set of nested trait names is not sufficient.
fn cast_preserves_dyn_carrier<'tcx>(
    tcx: TyCtxt<'tcx>,
    kind: CastKind,
    source_ty: Ty<'tcx>,
    target_ty: Ty<'tcx>,
) -> bool {
    fn raw_pointee<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        match ty.kind() {
            ty::RawPtr(inner, _) => Some(*inner),
            _ => None,
        }
    }
    fn non_null_pointee<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        let ty::Adt(adt, args) = ty.kind() else { return None };
        if !tcx.is_lang_item(adt.did(), rustc_attr_ir::lang_items::LangItem::NonNull)
            || !super::crate_is_authentic_core(tcx, adt.did().krate)
            || !adt.repr().transparent()
        {
            return None;
        }
        let mut fields = adt.all_fields();
        let field = fields.next()?;
        if fields.next().is_some() {
            return None;
        }
        let field_ty = instantiated_field_ty(tcx, field, *args);
        // Current core represents NonNull's only field as a non-null pattern
        // over a raw pointer. Inspect at most that one compiler pattern layer.
        let field_ty = match field_ty.kind() {
            ty::Pat(inner, _) => *inner,
            _ => field_ty,
        };
        raw_pointee(field_ty)
    }
    let pair = match kind {
        CastKind::PtrToPtr => raw_pointee(source_ty).zip(raw_pointee(target_ty)),
        CastKind::Transmute => raw_pointee(source_ty)
            .zip(non_null_pointee(tcx, target_ty))
            .or_else(|| non_null_pointee(tcx, source_ty).zip(raw_pointee(target_ty))),
        _ => None,
    };
    pair.is_some_and(|(source, target)| {
        tcx.erase_and_anonymize_regions(source) == tcx.erase_and_anonymize_regions(target)
    })
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
fn for_each_constant<'tcx>(
    block: &BasicBlockData<'tcx>,
    mut visit: impl FnMut(&rustc_middle::mir::ConstOperand<'tcx>),
) {
    let mut on_operand = |operand: &Operand<'tcx>| {
        if let Operand::Constant(constant) = operand {
            visit(constant);
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

/// Trust (D1 increment 1): is `ty` exactly `&mut core::fmt::Formatter<'_>` — the
/// formatting root's writer-carrying parameter? Decided by the `Formatter`
/// diagnostic item, never by a rendered name.
///
/// Trust (identity-anchor sweep, 2026-09-28): AND owned by authentic resident
/// core (`crate_is_authentic_core`). Every reader treats `true` as a grant input
/// (the root's `RootFormatterParam` poison source, the class's signature
/// conjunct, error transparency's pinned writer parameter), so `false` for a
/// whole-`core` substitute's `Formatter` is the refusal direction.
/// `ty_mentions_formatter` below is deliberately NOT anchored: it DETECTS a
/// minted formatter (a poison), where the broader match is the safe one.
pub(super) fn ty_is_mut_ref_to_formatter<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let ty::Ref(_, inner, Mutability::Mut) = *ty.kind() else { return false };
    matches!(
        inner.kind(),
        ty::Adt(adt, _) if tcx.is_diagnostic_item(rustc_span::sym::Formatter, adt.did())
            && super::crate_is_authentic_core(tcx, adt.did().krate)
    )
}

/// Trust (D1 increment 1): does `ty` mention `core::fmt::Formatter` in its type
/// tree (through generic arguments; a `Formatter` value, a `&mut Formatter`, an
/// `Option<Formatter>`)? Used only to notice a bundled call that hands back a
/// formatter the root did not receive.
fn ty_mentions_formatter<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    ty.walk().filter_map(|arg| arg.as_type()).any(|t| {
        matches!(
            t.kind(),
            ty::Adt(adt, _) if tcx.is_diagnostic_item(rustc_span::sym::Formatter, adt.did())
        )
    })
}

/// Trust (D1 increment 2, live): does dropping a value of `place_ty` run NO code
/// at all — a fully concrete type (no parameter, no unnormalized alias) with no
/// drop glue? Read by G-MEMBER ([`first_unrowed_panic_site`]) only.
fn drop_runs_no_code<'tcx>(
    tcx: TyCtxt<'tcx>,
    place_ty: Ty<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
) -> bool {
    !place_ty.has_param() && !place_ty.has_aliases() && !place_ty.needs_drop(tcx, typing_env)
}

/// Trust (D1 increment 1, G-MEMBER): does this body carry a terminator that can
/// panic or abort WITHOUT the bridge minting a row that names it?
///
/// * `Assert` — a bundled member's `Assert` mints no obligation (docs/TCB.md "A
///   bundled member's `Assert` mints NO obligation"); `DebugMap::key_with`'s
///   `assert!` is the measured instance (F2: a `debug_map().key(..).key(..)`
///   impl exits 101 while the only rows charged are its `dyn` edges).
/// * a `Call` with NO return target — the callee diverges (`core::panicking::*`,
///   `unwrap_failed`, `abort`, `process::exit`). Decided by the MIR's own
///   `target: None`, so no list of panicking names can go stale.
/// * `TailCall` — its divergence is not visible here.
/// * `InlineAsm`, `Drop` (a destructor is user- or std-chosen code the bundle
///   believes), `Yield`, `CoroutineDrop`.
///
/// Applied to EVERY walked body, the root included. The root's own `Assert`s do
/// get rows of their own, but they also fold into the whole-function
/// panic-freedom aggregate, whose representative may be a writer edge; refusing
/// them here costs only a formatting impl with a PROVED assert, which is an
/// accepted over-refusal for this increment. `precondition_check` bodies'
/// `panic_nounwind` is NOT exempted HERE; since D1 increment 2 the caller skips a
/// whole UB-check member instead (`body_is_ub_check_member`), under its own
/// conjunct.
///
/// Trust (D1 increment 2, live — measured 2026-09-25): a `Drop` of a place whose
/// type, as walked, is fully concrete and has NO drop glue (`!needs_drop`) is
/// not counted: dropping it runs no code at all, so it cannot panic or abort.
/// The generic builder `DebugTuple::field_with::<F>` (and its closure) keep a
/// `drop(value_fmt)` on the `?` early-return path of their generic optimized MIR;
/// instantiated at `DebugTuple::field`'s closure (`|f| value.fmt(f)`, which
/// captures only a reference) it is exactly such a no-op. A place type that still
/// mentions a parameter, or that needs dropping, is counted as before.
fn first_unrowed_panic_site<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
) -> Option<(BasicBlock, &'a TerminatorKind<'tcx>)> {
    body.basic_blocks.iter_enumerated().find_map(|(block_id, block)| {
        let kind = &block.terminator().kind;
        let unrowed = match kind {
            TerminatorKind::Drop { place, .. } => {
                !drop_runs_no_code(tcx, place.ty(&body.local_decls, tcx).ty, typing_env)
            }
            TerminatorKind::Assert { .. }
            | TerminatorKind::TailCall { .. }
            | TerminatorKind::InlineAsm { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop => true,
            TerminatorKind::Call { target, .. } => target.is_none(),
            _ => false,
        };
        unrowed.then_some((block_id, kind))
    })
}

/// Trust (D1 increment 2): is `method_def_id` the `fmt` method of core's
/// `Debug` or `Display` trait (by diagnostic item)? Returns the trait. A
/// virtual call to it is a NESTED FORMATTER — `derive(Debug)` reaches one
/// through `DebugTuple::field`'s `|f| value.fmt(f)`.
fn nested_formatter_trait(tcx: TyCtxt<'_>, method_def_id: DefId) -> Option<DefId> {
    let trait_def_id = tcx.trait_of_assoc(method_def_id)?;
    let is_formatting_trait = tcx.is_diagnostic_item(rustc_span::sym::Debug, trait_def_id)
        || tcx.is_diagnostic_item(rustc_span::sym::Display, trait_def_id);
    (is_formatting_trait && tcx.opt_item_name(method_def_id) == Some(rustc_span::sym::fmt))
        .then_some(trait_def_id)
}

/// Trust (D1 increment 2): may a nested-formatter site dispatch to `target`
/// (the resolved `<self_ty as Trait>::fmt`) under the WRITER-RELATIVE claim —
/// does `target` panic only through its `Formatter`'s writer, and never re-point
/// the `Formatter` it was handed? Admitted, and nothing else:
///
/// 1. core's reference-forwarding impl (`impl<T: ?Sized + Debug> Debug for &T`
///    / `&mut T`, `core/src/fmt/mod.rs` `fmt_refs!`: `$tr::fmt(&**self, f)`) —
///    PEELED, and the pointee's own target judged by this same rule, at most
///    [`MAX_POINTER_PEEL`] layers. A pointee that is itself a trait object
///    resolves to a `Virtual` instance and is refused.
/// 2. a SYSROOT impl (`def_is_in_real_sysroot_crate`) at a `Self` that passes
///    `ty_is_foundational_display` — premise P1 of docs/TCB.md "Formatting
///    premises", pre-existing: it is what already tolerates `println!("{:?}",
///    5u32)`. A sysroot impl at any other type (`Vec<LocalT>`, `Box<dyn Debug>`)
///    is refused: it would dispatch onward into code this rule did not see.
/// 3. a LOCAL formatting-impl root (`formatting_impl_root`: non-generic,
///    unattributed, no authored clause) that passes the ABSOLUTE bar or the
///    WRITER-RELATIVE bar, AND whose own bundle recorded writer-relative facts —
///    which is what says it mints no `Formatter` and coerces no writer of its own
///    (so it cannot re-point the `Formatter` it was handed). Its `DefId` is
///    recorded for error transparency at the sink.
///
/// Everything else — a foreign non-sysroot impl, a generic local impl, a shim —
/// is refused. `root_def_id` threads through to the bars' self-discharge and
/// in-progress bails, exactly as C-FLOW passes it.
fn nested_formatter_target_admitted<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_def_id: DefId,
    self_ty: Ty<'tcx>,
    target: ty::Instance<'tcx>,
    root_def_id: DefId,
    peeled: usize,
    local_targets: &mut Vec<DefId>,
) -> bool {
    let ty::InstanceKind::Item(def_id) = target.def else {
        return false;
    };
    // (1) core's `&T` / `&mut T` forwarding impl: judge the pointee's target.
    if is_core_reference_forwarding_fmt_impl(tcx, def_id, trait_def_id) {
        if peeled >= MAX_POINTER_PEEL {
            return false;
        }
        let ty::Ref(_, pointee, _) = *self_ty.kind() else {
            return false;
        };
        let Some(pointee_target) = resolve_formatting_method(tcx, trait_def_id, pointee) else {
            return false;
        };
        return nested_formatter_target_admitted(
            tcx,
            trait_def_id,
            pointee,
            pointee_target,
            root_def_id,
            peeled + 1,
            local_targets,
        );
    }
    // (2) a sysroot impl at a foundational type (P1).
    if !def_id.is_local() {
        return trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def_id)
            && super::ty_is_foundational_display(tcx, self_ty);
    }
    // (3) a local formatting impl with a verdict of its own.
    if !super::fmt_writer_relative::formatting_impl_root(tcx, def_id) {
        return false;
    }
    let passes_a_bar = dyn_target_is_verified_panic_free(tcx, target, root_def_id)
        || super::fmt_writer_relative::fmt_impl_is_writer_relative_panic_free(
            tcx,
            target,
            root_def_id,
        );
    // Read AFTER the bars: they force the target's verdict, and the bundle that
    // verdict builds is what records the facts.
    if !passes_a_bar
        || super::fmt_writer_relative::recorded_writer_relative_facts(tcx.sess, def_id).is_none()
    {
        return false;
    }
    if !local_targets.contains(&def_id) {
        local_targets.push(def_id);
    }
    true
}

/// Trust (D1 increment 2): is `method` the `fmt` of core's REFERENCE-FORWARDING
/// impl of `trait_def_id` — `impl<T: ?Sized + Trait> Trait for &T` (or `&mut
/// T`), authenticated by crate (`crate_is_authentic_core`, never a name) and by
/// the impl's identity self type being a reference to a type PARAMETER?
fn is_core_reference_forwarding_fmt_impl(
    tcx: TyCtxt<'_>,
    method: DefId,
    trait_def_id: DefId,
) -> bool {
    if !super::crate_is_authentic_core(tcx, method.krate) {
        return false;
    }
    let Some(impl_did) = tcx.trait_impl_of_assoc(method) else {
        return false;
    };
    let trait_ref = tcx.impl_trait_ref(impl_did).instantiate_identity().skip_normalization();
    trait_ref.def_id == trait_def_id
        && matches!(
            trait_ref.self_ty().kind(),
            ty::Ref(_, pointee, _) if matches!(pointee.kind(), ty::Param(_))
        )
}

/// Trust: a bounded chain of authentic core reference formatters may lead back
/// to the same already-enumerated trait-object target set. This alone never
/// establishes a base target, and unknown inputs still poison the entire set.
fn nested_formatter_returns_to_same_set<'tcx>(
    tcx: TyCtxt<'tcx>,
    key: ty::ExistentialTraitRef<'tcx>,
    mut self_ty: Ty<'tcx>,
    mut target: ty::Instance<'tcx>,
) -> bool {
    for _ in 0..MAX_POINTER_PEEL {
        let ty::InstanceKind::Item(def_id) = target.def else { return false };
        if !is_core_reference_forwarding_fmt_impl(tcx, def_id, key.def_id) {
            return false;
        }
        let ty::Ref(_, pointee, _) = *self_ty.kind() else { return false };
        if let ty::Dynamic(data, ..) = pointee.kind() {
            return data.principal().is_some_and(|principal| {
                tcx.erase_and_anonymize_regions(principal.skip_binder()) == key
            });
        }
        self_ty = pointee;
        let Some(next) = resolve_formatting_method(tcx, key.def_id, self_ty) else {
            return false;
        };
        target = next;
    }
    false
}

/// Trust (2026-09-28): [`nested_formatter_target_admitted`] for a `dyn Debug` /
/// `dyn Display` value that `root_def_id`'s OWN body minted — an unsize coercion
/// of `&self_ty` — and handed to core's formatting machinery, asked for a body
/// whose verdict rests on a runtime-checked bundled std member
/// (`fmt_machinery_reach_without_verdict`; before 2026-09-29, on the
/// lowering-failure tolerance path, where the bundle was discarded). The same
/// three admitted target kinds and the same bars; the local targets the rule
/// visits are not recorded, because no writer-relative fact is being written
/// here — this can only withhold the disposition, never grant a row.
pub(super) fn minted_formatter_value_admitted<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_def_id: DefId,
    self_ty: Ty<'tcx>,
    root_def_id: DefId,
) -> bool {
    let Some(target) = resolve_formatting_method(tcx, trait_def_id, self_ty) else {
        return false;
    };
    nested_formatter_target_admitted(
        tcx,
        trait_def_id,
        self_ty,
        target,
        root_def_id,
        0,
        &mut Vec::new(),
    )
}

/// Trust (D1 increment 2): resolve `<self_ty as Trait>::fmt` for a formatting
/// trait, fully monomorphized. `None` unless it names a concrete body — the
/// same resolution the formatting sinks use (`fmt_trait_impl_sink_basis`).
fn resolve_formatting_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_def_id: DefId,
    self_ty: Ty<'tcx>,
) -> Option<ty::Instance<'tcx>> {
    let method = tcx
        .associated_items(trait_def_id)
        .in_definition_order()
        .find(|item| item.opt_name() == Some(rustc_span::sym::fmt))?
        .def_id;
    let args = tcx.mk_args(&[self_ty.into()]);
    if args.has_non_region_param() {
        return None;
    }
    let instance =
        ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), method, args)
            .ok()??;
    matches!(instance.def, ty::InstanceKind::Item(_)).then_some(instance)
}

/// Trust (D1 increment 2): is `ty` core's PRIVATE `fmt::builders::PadAdapter` —
/// the writer core's debug builders wrap around a `Formatter`'s own writer in
/// `{:#?}` mode? Authenticated by crate (`crate_is_authentic_core`); the item
/// name and module segments only disambiguate WITHIN authentic core, where no
/// user code can add an item (the `def_path_has_module_segment` argument).
fn ty_is_core_pad_adapter<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let ty::Adt(adt, _) = ty.kind() else {
        return false;
    };
    let did = adt.did();
    super::crate_is_authentic_core(tcx, did.krate)
        && tcx.opt_item_name(did).is_some_and(|name| name.as_str() == "PadAdapter")
        && super::def_path_has_module_segment(tcx, did, "fmt")
        && super::def_path_has_module_segment(tcx, did, "builders")
}

/// Trust (D1 increment 2): does a CONSTANT of type `ty` carry a trait object
/// ONLY through core's `PadAdapter`? Accepted shapes, after peeling at most
/// [`MAX_POINTER_PEEL`] references/raw pointers: `PadAdapter` itself, or
/// `Option<P>` (the `Option` by diagnostic item) where `P`, after peeling at most
/// [`MAX_POINTER_PEEL`] references/raw pointers, is `PadAdapter`. Every other type
/// answers `false` and keeps the ordinary `Constant` poison.
///
/// Trust (D1 increment 2, live — measured 2026-09-25 on stage-1 `94837a9e8`):
/// the constant a derived `Debug` bundle actually holds is
/// `Option<&mut PadAdapter<'_, '_>>`, NOT the `Option<PadAdapter>` the increment
/// predicted: `PadAdapter::wrap`'s optimized MIR inlines `Option::insert`, whose
/// `self.as_mut().unwrap_unchecked()` leaves a `const None::<&mut PadAdapter>` on
/// the `None` arm (`TRUST_DYN_RELIANCE_PROBE`: "dyn-bearing constant of type
/// `Option<&mut PadAdapter<'_, '_>>`"). `let mut slot = None;` is an AGGREGATE,
/// not a constant. The `Option<&P>`/`Option<&mut P>` shapes are therefore
/// admitted by the same audit.
///
/// WHY SUCH A CONSTANT HOLDS NO WRITER (source audit, `library/core/src/fmt/`):
/// `PadAdapter` is private to `core::fmt::builders`, so only core names it; core
/// constructs one at exactly ONE site, `PadAdapter::wrap` (`builders.rs:26`),
/// from the RUNTIME `&mut dyn Write` of the formatter it is given, in a non-`const`
/// fn — so no compile-time value can hold a `PadAdapter` or point at one. A
/// constant of this type is therefore a `None` — it names no vtable at all.
/// docs/TCB.md "Formatting premises" P2 carries the audit. The caller ALSO
/// demands the constant's evaluated value carry no pointer at all
/// ([`constant_value_holds_no_pointer`]), which excludes a vtable independently
/// of the audit.
fn constant_ty_carries_dyn_only_through_pad_adapter<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let peel = |mut ty: Ty<'tcx>| {
        for _ in 0..=MAX_POINTER_PEEL {
            match *ty.kind() {
                ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => ty = inner,
                _ => break,
            }
        }
        ty
    };
    let ty = peel(ty);
    if ty_is_core_pad_adapter(tcx, ty) {
        return true;
    }
    match ty.kind() {
        ty::Adt(adt, args) if tcx.is_diagnostic_item(rustc_span::sym::Option, adt.did()) => {
            args.types().next().is_some_and(|inner| ty_is_core_pad_adapter(tcx, peel(inner)))
        }
        _ => false,
    }
}

/// An exact evaluated PhantomData value has no runtime fields from which a
/// virtual receiver can originate. References, containing types, unevaluated
/// constants and user lookalikes retain the ordinary conservative poison.
fn constant_is_empty_phantom_data<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::ConstOperand<'tcx>,
) -> bool {
    use rustc_middle::mir::{Const, ConstValue};
    if !matches!(constant.const_, Const::Val(ConstValue::ZeroSized, _)) {
        return false;
    }
    let ty::Adt(adt, _) = constant.ty().kind() else { return false };
    tcx.lang_items().phantom_data() == Some(adt.did())
        && super::crate_is_authentic_core(tcx, adt.did().krate)
        && adt.all_fields().next().is_none()
}

/// Trust (D1 increment 2, live): does this constant's EVALUATED value carry no
/// pointer — so no vtable pointer — at all? `true` only for a value this can
/// read without evaluating anything: a zero-sized value, a scalar that is a plain
/// integer (e.g. the null niche of `None::<&mut T>`), or an interned allocation
/// with no provenance anywhere in it. An unevaluated or type-system constant, a
/// pointer scalar, a slice, or a non-memory allocation answers `false`
/// (fail-closed: the constant keeps its ordinary `Constant` poison).
fn constant_value_holds_no_pointer<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::ConstOperand<'tcx>,
) -> bool {
    use rustc_middle::mir::interpret::{GlobalAlloc, Scalar, alloc_range};
    use rustc_middle::mir::{Const, ConstValue};
    let Const::Val(value, _) = constant.const_ else {
        return false;
    };
    match value {
        ConstValue::ZeroSized => true,
        ConstValue::Scalar(Scalar::Int(_)) => true,
        ConstValue::Scalar(Scalar::Ptr(..)) | ConstValue::Slice { .. } => false,
        ConstValue::Indirect { alloc_id, .. } => match tcx.try_get_global_alloc(alloc_id) {
            Some(GlobalAlloc::Memory(alloc)) => {
                let alloc = alloc.inner();
                alloc
                    .provenance()
                    .range_empty(alloc_range(rustc_abi::Size::ZERO, alloc.size()), &tcx)
            }
            _ => false,
        },
    }
}

/// Trust (D1 increment 2): is `callee` core's `PadAdapter::wrap` or the private
/// `Formatter::wrap_buf` it calls — the only two functions in core that return a
/// NEW `Formatter`, whose writer is a `PadAdapter` over the writer of the
/// formatter they were given (`builders.rs:20-28`, `mod.rs` `wrap_buf`:
/// `Formatter { buf: wrap(self.buf), options: self.options }`; `wrap_buf` has
/// no other caller)? Authenticated by crate and inherent-impl self type.
fn callee_wraps_formatter_in_pad_adapter(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if !super::crate_is_authentic_core(tcx, callee.krate) {
        return false;
    }
    let Some(impl_did) = tcx.inherent_impl_of_assoc(callee) else {
        return false;
    };
    let Some(name) = tcx.opt_item_name(callee) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_did).instantiate_identity().skip_normalization();
    match name.as_str() {
        "wrap" => ty_is_core_pad_adapter(tcx, self_ty),
        "wrap_buf" => matches!(
            self_ty.kind(),
            ty::Adt(adt, _) if tcx.is_diagnostic_item(rustc_span::sym::Formatter, adt.did())
        ),
        _ => false,
    }
}

/// Trust (D1 increment 2, G-MEMBER): is `def_id` a UB-CHECK member — a body whose
/// only panic is the NON-UNWINDING abort raised when a sysroot `unsafe`
/// precondition is violated?
///
/// * the `precondition_check` fn that `assert_unsafe_precondition!`
///   (`library/core/src/ub_checks.rs`) nests inside a sysroot fn — authenticated
///   crate (`crate_is_authentic_foundational`), a `fn` named
///   `precondition_check` whose PARENT is a fn or method, returning `()`; its
///   body is `if !cond { panic_nounwind_fmt(..) }` and it is called only under
///   `ub_checks()`;
/// * the `panic_nounwind` lang item and core's `panicking::panic_nounwind_fmt`
///   (`-> !`), and any body NESTED inside either (the `const_eval_select!`
///   `runtime` fn). Their own diverging call is irrelevant: any OTHER caller of
///   them diverges at its own call terminator (`target: None`), which G-MEMBER
///   still counts in that caller.
///
/// THE PREMISE (docs/TCB.md "Formatting premises", P-UB): a sysroot `unsafe`
/// precondition is violated only by undefined behaviour, and the sysroot is
/// already trusted to be free of it when every caller is safe code — the vanilla
/// ledger has always classified `precondition_check` callees as vanilla. The
/// writer-relative facts VOID this exemption when any walked body outside the
/// authentic sysroot uses `unsafe` (`non_sysroot_unsafe_walked`). That void
/// condition is NOT sufficient on its own and is not what the premise rests on:
/// it sees only WALKED bodies, while an invalid value built by `unsafe` outside
/// the bundle — an invalid `&str` from `main`'s own `unsafe` (probe `fa26`) or
/// returned by a verify-off dependency (`fa27`, `c01`) — reaches `<str as
/// Debug>`'s UB check through `&self` (runtime truth: exit 134). The premise
/// holds ONLY because (1) the root's own `unsafe` rows are Level 0 errors and
/// (2) a call into a verify-off dependency is fail-closed; relaxing either one
/// must re-establish it first. The measured instance is `Option::insert`'s
/// `unwrap_unchecked` inside `PadAdapter::wrap`, unreachable because the line
/// before it stores `Some`.
fn body_is_ub_check_member(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    use rustc_hir::def::DefKind;
    if !super::crate_is_authentic_foundational(tcx, def_id.krate) {
        return false;
    }
    let is_panic_nounwind_entry = |did: DefId| {
        tcx.lang_items().get(rustc_attr_ir::lang_items::LangItem::PanicNounwind) == Some(did)
            || (super::crate_is_authentic_core(tcx, did.krate)
                && tcx.opt_item_name(did).is_some_and(|name| name.as_str() == "panic_nounwind_fmt")
                && super::def_path_has_module_segment(tcx, did, "panicking")
                && matches!(tcx.def_kind(did), DefKind::Fn)
                && tcx.fn_sig(did).instantiate_identity().skip_binder().output().is_never())
    };
    // The entry itself, or a body nested inside it (bounded parent walk).
    let mut cursor = Some(def_id);
    for _ in 0..4 {
        let Some(did) = cursor else { break };
        if is_panic_nounwind_entry(did) {
            return true;
        }
        cursor = tcx.opt_parent(did);
    }
    def_is_ub_check_precondition_fn(tcx, def_id)
}

/// Trust (P-UB, absent UB-check members, 2026-11-08): the `precondition_check`
/// arm of [`body_is_ub_check_member`] ALONE — an authentic-foundational `fn`
/// named `precondition_check` whose parent is a fn or method, returning `()`:
/// the check `assert_unsafe_precondition!` (`library/core/src/ub_checks.rs`)
/// nests inside a sysroot fn, whose body is `if !cond { panic_nounwind_fmt(..) }`.
///
/// Split out so an ABSENT callee can be judged by the same identity anchors as a
/// walked member (`DynDispatchBundleFacts::ub_check_precondition_candidates`).
/// The `panic_nounwind` entries are deliberately NOT here: a walked entry is not
/// counted only because each of its callers diverges at its own call terminator,
/// which G-MEMBER still counts, whereas an absent-callee row naming an entry IS
/// that abort, and nothing else would count it.
fn def_is_ub_check_precondition_fn(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    use rustc_hir::def::DefKind;
    super::crate_is_authentic_foundational(tcx, def_id.krate)
        && matches!(tcx.def_kind(def_id), DefKind::Fn)
        && tcx.opt_item_name(def_id).is_some_and(|name| name.as_str() == "precondition_check")
        && tcx
            .opt_parent(def_id)
            .is_some_and(|parent| matches!(tcx.def_kind(parent), DefKind::Fn | DefKind::AssocFn))
        && tcx.fn_sig(def_id).instantiate_identity().skip_binder().output().is_unit()
}

/// Trust (P-UB, absent UB-check members, 2026-11-08): the rendered keys whose
/// absent-callee markers P-UB excuses in the writer-relative bar — a candidate
/// (`DynDispatchBundleFacts::ub_check_precondition_candidates`) whose body was
/// never walked and whose key no other call rendered — or none at all while a
/// walked non-sysroot body uses `unsafe` (the P-UB belt). Generic over the callee
/// identity only so the selection rule is unit-tested without a `TyCtxt`.
fn absent_ub_check_callee_keys<Id: Eq + std::hash::Hash>(
    candidates: &[(Id, String)],
    observed_bodies: &FxHashSet<Id>,
    other_callee_keys: &FxHashSet<String>,
    non_sysroot_unsafe_walked: bool,
) -> FxHashSet<String> {
    if non_sysroot_unsafe_walked {
        return FxHashSet::default();
    }
    candidates
        .iter()
        .filter(|(callee, key)| {
            !observed_bodies.contains(callee) && !other_callee_keys.contains(key)
        })
        .map(|(_, key)| key.clone())
        .collect()
}

/// Trust (96a18b names-split finishers, G-MEMBER): which piece of authentic
/// core's derive-`Debug` names-split machinery a body or callee is.
///
/// Upstream `96a18bf5ffa2` rewrote the doc-hidden `fmt_helpers_for_derive`
/// struct finishers (`core/src/fmt/mod.rs`): instead of one `&str` per name,
/// `debug_struct_field{1..5}_finish` now takes ONE concatenated
/// `"TypeName field1 field2"` string and recovers the parts with
/// `names.split(' ')` + `next().unwrap()`. That put panic sites
/// (`unwrap_failed`, the char searcher's length/encoding unwraps, an
/// alignment `debug_assert!` in the byte-search fast path) into bodies the
/// writer-relative walk has always entered, where G-MEMBER counts them as
/// unrowed and the class is refused — the measured `enum_i01` /
/// `format_enum` regression (`tests/ui/trust/fmt_writer_relative_derive.rs`).
///
/// The exemption parallels P-UB ([`body_is_ub_check_member`]) and its premise
/// is docs/TCB.md "Formatting premises" P-SPLIT. Authentication is by
/// authentic foundational crate plus item identity (name, impl self type,
/// module segment, never-returning signature) — the same anchors the
/// UB-check classifier uses — and every walked DIRECT call into the
/// machinery must additionally discharge its invariant
/// ([`finisher_names_arg_well_formed`], [`const_pow2_usize_operand`], the
/// sysroot-caller rule for `encode_utf8_raw`), recorded in
/// `DynDispatchBundleFacts::names_split_unproven`.
///
/// * `Finisher(n)`: inherent `Formatter::debug_struct_field{1..5}_finish`.
///   Current core delegates to the n-ary helper. Every incoming fixed call
///   still needs immutable constant names with enough separators, or a
///   space-free name selecting the tuple branch.
/// * `NaryFinisher`: inherent `Formatter::debug_struct_fields_finish`, only
///   under an authenticated fixed-wrapper entry preserving its receiver,
///   names parameter and ordered fixed array of original value parameters.
///   Every incoming edge must qualify; a walked body without such an entry
///   also refuses. A direct n-ary derive remains outside this premise.
/// * `CharIntoSearcher`: `<char as Pattern>::into_searcher`. Its `.expect`
///   converts an encoded length (at most `char::MAX_LEN_UTF8`, by the `char`
///   type itself) to `u8` — unreachable for every well-typed input.
/// * `EncodeUtf8Raw`: core's `char_internals` `encode_utf8_raw`. Its only
///   panic is an undersized destination buffer; core callers pass a `char`
///   code point and at least four bytes (`char::encode_utf8`). The evidence
///   check refuses the exemption when a walked non-sysroot body calls it.
/// * `IsAlignedTo`: `*const T` / `*mut T` / `NonNull<T>` inherent
///   `is_aligned_to`, whose only panic is a non-power-of-two alignment;
///   reached here from the byte searcher's `debug_assert!`. The evidence
///   check demands a constant power-of-two alignment at every walked call.
/// * `PanicFmt`: the panic entry shims (`std::rt::panic_fmt`,
///   `core::panicking::panic_fmt`). Like the `panic_nounwind` entry in
///   [`body_is_ub_check_member`]: their own diverging call is irrelevant,
///   because any caller of them diverges at its own call terminator, which
///   G-MEMBER still counts in that caller.
///
/// No additional byte-split/map member is admitted by this migration. Its
/// current bundled bodies still need their own evidence; a matching source
/// name alone is never an exemption.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum NamesSplitMember {
    Finisher(usize),
    NaryFinisher,
    CharIntoSearcher,
    EncodeUtf8Raw,
    IsAlignedTo,
    PanicFmt,
}

fn names_split_member_kind(tcx: TyCtxt<'_>, def_id: DefId) -> Option<NamesSplitMember> {
    if !super::crate_is_authentic_foundational(tcx, def_id.krate) {
        return None;
    }
    if let Some(kind) = names_split_member_kind_direct(tcx, def_id) {
        return Some(kind);
    }
    // A body NESTED inside `encode_utf8_raw` or a panic entry (the
    // `const_eval_select!` `runtime`/`do_panic` shims) shares its kind — the
    // same bounded parent walk as the UB-check classifier. Restricted to
    // those two kinds: a closure nested in a finisher or a searcher must not
    // inherit an arity or an input-independent invariant it does not have.
    let mut cursor = tcx.opt_parent(def_id);
    for _ in 0..4 {
        let did = cursor?;
        if let Some(kind @ (NamesSplitMember::EncodeUtf8Raw | NamesSplitMember::PanicFmt)) =
            names_split_member_kind_direct(tcx, did)
        {
            return Some(kind);
        }
        cursor = tcx.opt_parent(did);
    }
    None
}

fn names_split_member_kind_direct(tcx: TyCtxt<'_>, def_id: DefId) -> Option<NamesSplitMember> {
    use rustc_hir::def::DefKind;
    let name = tcx.opt_item_name(def_id)?;
    let name = name.as_str();

    // Inherent-impl members, authenticated by the impl's self type (the same
    // anchor as `callee_is_debug_builder_helper` / `callee_wraps_formatter_in_
    // pad_adapter`): coherence forbids a user crate adding inherent methods
    // to a foreign `Formatter` or raw pointer type.
    if matches!(tcx.def_kind(def_id), DefKind::AssocFn)
        && let Some(impl_did) = tcx.inherent_impl_of_assoc(def_id)
    {
        let self_ty = tcx.type_of(impl_did).instantiate_identity().skip_normalization();
        match self_ty.kind() {
            ty::Adt(adt, _)
                if super::crate_is_authentic_core(tcx, def_id.krate)
                    && tcx.is_diagnostic_item(rustc_span::sym::Formatter, adt.did()) =>
            {
                let arity = match name {
                    "debug_struct_field1_finish" => 1,
                    "debug_struct_field2_finish" => 2,
                    "debug_struct_field3_finish" => 3,
                    "debug_struct_field4_finish" => 4,
                    "debug_struct_field5_finish" => 5,
                    "debug_struct_fields_finish" => return Some(NamesSplitMember::NaryFinisher),
                    _ => return None,
                };
                return Some(NamesSplitMember::Finisher(arity));
            }
            ty::RawPtr(..) if name == "is_aligned_to" => {
                return Some(NamesSplitMember::IsAlignedTo);
            }
            ty::Adt(adt, _)
                if name == "is_aligned_to"
                    && super::crate_is_authentic_core(tcx, def_id.krate)
                    && tcx.item_name(adt.did()).as_str() == "NonNull"
                    && super::def_path_has_module_segment(tcx, adt.did(), "ptr") =>
            {
                return Some(NamesSplitMember::IsAlignedTo);
            }
            _ => {}
        }
    }

    // `<char as core::str::pattern::Pattern>::into_searcher`.
    if name == "into_searcher"
        && matches!(tcx.def_kind(def_id), DefKind::AssocFn)
        && super::crate_is_authentic_core(tcx, def_id.krate)
        && let Some(impl_did) = tcx.trait_impl_of_assoc(def_id)
    {
        let trait_ref = tcx.impl_trait_ref(impl_did).instantiate_identity().skip_normalization();
        let self_ty = trait_ref.self_ty();
        let trait_did = trait_ref.def_id;
        if self_ty == tcx.types.char
            && tcx.opt_item_name(trait_did).is_some_and(|n| n.as_str() == "Pattern")
            && super::def_path_has_module_segment(tcx, trait_did, "pattern")
        {
            return Some(NamesSplitMember::CharIntoSearcher);
        }
        return None;
    }

    // `core::char::encode_utf8_raw`.
    if name == "encode_utf8_raw"
        && matches!(tcx.def_kind(def_id), DefKind::Fn)
        && super::crate_is_authentic_core(tcx, def_id.krate)
        && super::def_path_has_module_segment(tcx, def_id, "char")
    {
        return Some(NamesSplitMember::EncodeUtf8Raw);
    }

    // The panic entry shims: name + home module + never-returning, mirroring
    // the `panic_nounwind_fmt` arm of `body_is_ub_check_member`.
    if name == "panic_fmt"
        && matches!(tcx.def_kind(def_id), DefKind::Fn)
        && (super::def_path_has_module_segment(tcx, def_id, "rt")
            || super::def_path_has_module_segment(tcx, def_id, "panicking"))
        && tcx.fn_sig(def_id).instantiate_identity().skip_binder().output().is_never()
    {
        return Some(NamesSplitMember::PanicFmt);
    }

    None
}

/// Trust (DEBUG-PACKED-NAMES): reuse the extractor's whole-body constant
/// custody guard for the actual names operand. Current core takes a tuple
/// branch when it has no ASCII spaces; otherwise it needs one separator per
/// field. A last assignment in this block is insufficient: even safe `&mut`
/// aliasing can replace the names after that assignment.
fn finisher_names_arg_well_formed<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    arity: usize,
) -> bool {
    args.get(1).is_some_and(|arg| {
        trust_mir_extract::debug_finisher_names_have_fields(tcx, body, &arg.node, arity)
    })
}

/// P-SPLIT's alignment argument must be an immutable literal `usize` power
/// of two. Use the same body-wide custody as packed names: a safe mutable
/// alias or an unknown incoming parameter cannot borrow an earlier value.
fn const_pow2_usize_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg: &Operand<'tcx>,
) -> bool {
    use rustc_middle::mir::interpret::Scalar;
    use rustc_middle::mir::{Const, ConstValue};
    let Some(constant) = trust_mir_extract::immutable_operand_const(body, arg) else {
        return false;
    };
    if constant.ty() != tcx.types.usize {
        return false;
    }
    let Const::Val(ConstValue::Scalar(Scalar::Int(int)), _) = constant else { return false };
    int.to_uint(int.size()).is_power_of_two()
}

// Trust (P-UB, absent UB-check members, 2026-11-08): the selection rule of
// `absent_ub_check_callee_keys` is pinned in `dyn_dispatch_reliance/tests.rs`.
#[cfg(test)]
mod tests;
