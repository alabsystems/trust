//! Trust: the flip registry (P1 item 5) — plumbing the green verdict + `trust_ir::Module`
//! from the `mir_built` hook to the `optimized_mir` provider.
//!
//! The `build_mir_inner_impl` hook (rustc_mir_build) is the only seam where the THIR-side
//! lowering AND the derived-vs-built MIR differential verdict both exist. When the verdict is
//! `DerivedAgreed` — the shim-derived MIR was proven canonically identical to the freshly built
//! MIR — the hook calls [`record_green`], which snapshots the per-body `trust_ir::Module` here.
//! Later, `rustc_mir_transform::trust_ir_flip::try_flip` (called from `inner_optimized_mir`)
//! [`take`]s the Module, re-derives a `mir::Body` from it, and — after fail-closed gates — the
//! compiler consumes that derived MIR on the codegen path: the first real
//! "compiled from trust-ir" lane.
//!
//! Ordering is guaranteed by the query graph: `optimized_mir` → `mir_drops_elaborated…` →
//! `mir_promoted` → `mir_built` (the hook). If `mir_built` was loaded from an incremental cache
//! the hook never ran, the registry is empty, and every body takes the normal path — fail-closed.
//!
//! Thread-safe (`mir_built` runs in parallel) through Session-owned compiler state, like
//! [`crate::crate_module`]. Memory-bounded: only GREEN bodies are recorded (green ⇒ the
//! slice-1 scalar fragment ⇒ small Modules), and [`take`] removes the entry — `optimized_mir`
//! runs at most once per def per session.
//!
//! # Session gates ([`flip_session_enabled`], checked at RECORD time so the registry never
//! # accumulates when the flip cannot fire)
//!
//! * `-Z trust-ir-lower` — the flip is part of the trust-ir lane; the flag is the opt-in.
//! * `-Z trust-ir-flip=no` disables the lane entirely (byte-compare baseline
//!   for the equivalence probes). This is a tracked option because the lane
//!   directly selects codegen/CTFE MIR.
//! * first-class `invariant`/`decreases` clauses require the v35 semantic
//!   source-provenance carrier. The compiler query is regenerated at both
//!   record and consume time; compiler-source, semantic-body, and binding
//!   digests plus an independently reconstructed natural-header/canonical
//!   parameter map must all agree. Missing, stale, forged, or partial carriers
//!   fail closed. Contract-free bodies remain eligible only with no carrier.
//! * `-C debuginfo=0` only. Per-instruction spans and lexical scopes now ride
//!   TrustIr, and parameter names reconstruct exactly, but corpus comparison
//!   still finds line-row/column structural divergence and the producer does
//!   not name locals. Flipping under debuginfo would therefore silently degrade
//!   debug info. Assert panic-location spans are additionally stitched from the
//!   borrow-checked sibling by [`crate::flip`].
//! * no `-C instrument-coverage`: coverage mappings are span-derived; dummy spans would
//!   corrupt them.
//!
//! # Per-BODY marker gate (slice 3 — replaces the old `-O0`-only session gate)
//!
//! The shim emits storage markers for OPERAND TEMPS only (wave-MF, 2026-08-12). Everything
//! else is still unemitted, so under `-O` a flipped body could lack the LLVM lifetime hints
//! the built body carries. Instead of gating the whole session to `-O0`,
//! [`record_green`] takes the derived-MIR differential's EXACT marker-channel verdict
//! (`DerivedReport::markers_exact`) and records a body at `-O` only when the marker
//! sequences were proven line-identical. An unproven sequence is exempted only where its
//! markers cannot reach any codegen or interpreter, which [`marker_gate_allows_flip`] decides:
//! the session emits no `llvm.lifetime` intrinsics, `RemoveStorageMarkers` provably runs on
//! `optimized_mir` (its own `is_enabled`, `mir_opt_level > 0`, under the
//! `-Zmir-enable-passes` override), no `-Zmir-opt-bisect-limit` is set (it can skip that pass
//! on any body), and the body is not one the CTFE seam installs (`mir_for_ctfe`, which that
//! pass never touches and the const-eval interpreter runs WITH its markers: a const or static
//! initializer, or a `#[rustc_comptime]` fn). Everywhere else `markers_exact` is required.
//! The flip therefore flips what it can PROVE at each opt level, per body.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: Apache-2.0

use std::collections::{BTreeMap, HashMap};

use rustc_middle::ty::TyCtxt;
use rustc_session::config::DebugInfo;
use rustc_span::def_id::LocalDefId;
use trust_ir::{Inst, Module, ProofDigest, ValueId};

use crate::{CalleeRef, Lowered, ThinReborrow, ThinReborrowProvenance};

/// One green body as the flip consumes it: the per-body mini-module, the
/// callee-identity ledger `to_mir` spells calls from, and the lineage digest
/// ([`crate::lineage::body_lineage_digest`]) binding both — computed at RECORD
/// time over the intact hook-time `Lowered`, so the flip event and the
/// coverage row (`crate_module`) can state the same identity.
/// Fields are `pub(crate)`: outside this crate a `GreenBody` is opaque, so the only
/// way to obtain one is [`take`] — which can only return what [`green_body`] minted.
pub struct GreenBody {
    pub(crate) module: Module,
    pub(crate) callees: Vec<CalleeRef>,
    /// Trust (L1, artifact-lineage attestation): always present — [`green_body`] is
    /// the only constructor and it refuses a body whose digest cannot be computed
    /// (no green without a digest), so every flip event carries it. The value is
    /// additionally RE-DERIVED and checked at the flip
    /// ([`crate::flip::derive_flip_body`]), so even an in-crate value assembled by
    /// some future path with a digest that does not describe its own payload fails
    /// closed rather than publishing a false attestation.
    pub(crate) lineage: ProofDigest,
    /// Trust (enum-switch provenance): the hook-time [`Lowered::enum_fold_switch_blocks`], carried
    /// because THIR IS NOT AVAILABLE AT FLIP TIME (see [`crate::flip::derive_flip_body`]) and the
    /// set cannot be recovered from the module — that is the whole reason it exists.
    ///
    /// DELIBERATELY OUTSIDE the lineage digest. The digest names the (module, callee ledger) pair;
    /// this set rides in the SAME registry entry the digest names, and the flip consumes both from
    /// that one entry, so the two cannot desynchronize. Folding it into `body_lineage_digest`
    /// would move every existing digest — including the pinned crystal A1 value — for no
    /// soundness gain. An entry that somehow carried an EMPTY set would merely suppress the
    /// reshape and miss flips: fail-closed, never a wrong body.
    pub(crate) enum_fold_switch_blocks: std::collections::HashSet<trust_ir::BlockId>,
    /// Opaque compiler-owned evidence that every carried
    /// source-loop/TrustIR-header association matched the independently built
    /// MIR header at one unique canonical CFG role.  Its private seal binds
    /// the exact two role maps to `lineage`; it is Session-owned and never
    /// serialized into the self-sealed artifact.
    pub(crate) source_header_correspondence: crate::mir_differential::SourceHeaderCorrespondence,
}

/// Trust: the WITNESS that [`body_lane_gates_allow_flip`] was READ, as a refusal, for THE BODY
/// ABOUT TO BE RECORDED — half TYPE FACT, half consumption-site check; see (1) and (2) below.
///
/// "A gate nothing reads is not a gate" used to be enforced by a test that
/// `include_str!`ed this very file and counted occurrences of the aggregate's own
/// name (`test_the_lane_gate_aggregate_is_read_by_record_green`, deleted with the
/// first cut of this type). TWO DIFFERENT PROPERTIES live in that sentence, and
/// they are carried by two different mechanisms. Conflating them is what the first
/// cut of this docblock got wrong — it claimed both as a type fact when only one is
/// — so they are spelled apart:
///
/// 1. THAT THE GATE IS READ AT ALL — a TYPE FACT, checked by rustc. The fields are
///    private; there is no `Default`, no `Clone`, no `Copy`, no `From` and no
///    constructor anywhere but the `Some` arm of [`body_lane_gates_allow_flip`];
///    and [`green_body`] — the SINGLE place a [`GreenBody`] comes into existence —
///    takes one BY VALUE. So a `record_green` that does not read the aggregate
///    cannot name the argument `green_body` demands, and "evaluated without acting
///    on the result" is unspellable, because outside that `Some` arm there is no
///    value to act on.
///
/// 2. THAT IT WAS READ FOR *THIS* BODY — NOT a type fact, and no longer claimed as
///    one. rustc only proves that SOME `Lowered` cleared the gates. So the token
///    BORROWS the `(module, callee ledger)` the gates actually ran over, and
///    [`green_body`] REFUSES unless the pair it was handed is that same pair BY
///    ADDRESS ([`LaneGatesPassed::witnesses`]). A token minted over body A cannot
///    license recording body B: `green_body` returns `None`, nothing is registered,
///    and the body stays on built MIR. The BORROW is what makes an address check
///    sound here — a token cannot outlive the `Lowered` it read, so a later body
///    cannot be allocated at a dead one's address and inherit its verdict.
///
/// (2) was, in the first cut, prose with a LIVE COUNTEREXAMPLE in this very module:
/// the test helper minted one token from a fixed fixture and handed it to
/// `green_body` for unrelated modules. The helpers now mint per body, and
/// `test_a_lane_gate_token_cannot_license_a_different_body` pins the refusal with a
/// fixture whose every other ingredient is valid.
///
/// MEASURED 2026-09-21, by deleting `record_green`'s refusal and nothing else and
/// reading what the compiler said. The lane was
/// `RUSTC_BOOTSTRAP=1 CFG_RELEASE=1.99.0-dev CFG_RELEASE_NUM=1.99.0
/// CFG_RELEASE_CHANNEL=dev CFG_VERSION=1.99.0-dev
/// CFG_COMPILER_HOST_TRIPLE=aarch64-apple-darwin targo --unverified check
/// -p trust-thir-lower --tests` — Targo's NO-PROOF-CLAIM lane, so nothing here is
/// a verification result:
///
/// ```text
/// error[E0425]: cannot find value `lane_gates` in this scope
///    --> crates/trust-thir-lower/src/flip_registry.rs:863:9
///     |
/// 863 |         lane_gates,
///     |         ^^^^^^^^^^ not found in this scope
/// ```
///
/// Before this type the same deletion COMPILED and the suite stayed green — 262/262
/// when wave-TR measured it on the tree of that day. NO pre-change run was ever
/// completed on this tree, so no before/after count is claimed for the conversion
/// itself, and none could be equal: deleting the self-parsing test moved this
/// file's count of `#[test]` ATTRIBUTES 17 -> 16 (this mention is not one).
///
/// WHAT THIS STILL DOES NOT GIVE, stated so the next reader does not over-trust it.
///
/// * IN-MODULE FORGERY, unchanged. `LaneGatesPassed`, its fields and `witnesses` are
///   private to THIS MODULE, and `record_green` lives in this module, so
///   `let lane_gates = LaneGatesPassed { module: &lowered.module, callees: &lowered.callees };`
///   — the aggregate not called at all — compiles, and because it names the right
///   pair it satisfies (2) as well. MEASURED 2026-09-21, that exact line substituted
///   for the refusal in the lane above: rc=0, 0 errors, and not even a warning.
///   What the type kills is the ONE-LINE mistake this file has paid for twice:
///   dropping the refusal and leaving everything else alone. Closing forgery means
///   moving the mint out of reach — this type, `body_lane_gates_allow_flip` and
///   `witnesses` in a sibling submodule re-exported by name only, so `record_green`
///   cannot name the constructor at all. That move is not made here.
/// * READER COUNT. Nothing bounds how many callers read the aggregate, and after (2)
///   nothing needs to: a second reader can only mint a token bound to its own body.
///   The deleted self-parsing test asserted "exactly two occurrences" in this file;
///   that count was a PROXY for (2), and (2) is now checked directly.
/// * AN EMPTY CALLEE LEDGER ALIASES. Two distinct empty `Vec<CalleeRef>`s share one
///   dangling `as_ptr()`, so for a body with no callees the ledger half of
///   `witnesses` is vacuous and only the module address discriminates. Fail-closed
///   either way: the ledger half can never admit a pair the module half rejects.
#[must_use]
struct LaneGatesPassed<'a> {
    /// The module the aggregate READ — borrowed, so the token cannot outlive it.
    module: &'a Module,
    /// The callee ledger the aggregate READ. The `thin_reborrows` conjunct consults
    /// it, so it is half of what the verdict is ABOUT and half of what is bound.
    callees: &'a [CalleeRef],
}

impl LaneGatesPassed<'_> {
    /// Whether this token was minted over EXACTLY the pair now being recorded.
    ///
    /// ADDRESS identity, not value equality. The question is not "is there a module
    /// that looks like this one" but "is this the very object the gates were read
    /// over"; value equality would re-admit what this exists to refuse — a clone, or
    /// a second body that happens to lower identically.
    fn witnesses(&self, module: &Module, callees: &[CalleeRef]) -> bool {
        std::ptr::eq(self.module, module)
            && self.callees.as_ptr() == callees.as_ptr()
            && self.callees.len() == callees.len()
    }
}

/// Trust (L1): mint the registry entry for one green body — the SINGLE place a
/// [`GreenBody`] comes into existence, and therefore the single place the
/// "no digest, no green" rule can be enforced.
///
/// `None` when the lineage digest refuses (a mini-module that is not a
/// single-function per-body lowering). The caller ([`record_green`]) then
/// records NOTHING: the flip cannot fire for a body it would be unable to name
/// by digest, so the attestation chain has no hole at its first link.
///
/// Split out of `record_green` — which needs a `TyCtxt` and so cannot be unit
/// tested — precisely so this rule is a test obligation and not a comment.
///
/// `lane_gates` carries TWO checks, one made by rustc and one made below. Only
/// [`body_lane_gates_allow_flip`] can mint a [`LaneGatesPassed`], so demanding one
/// BY VALUE turns "every per-body placeholder/provenance lane gate was read, as a
/// refusal" into a precondition rustc checks at the call rather than a sentence in a
/// comment. WHICH body they were read for is not something a type can say, so it is
/// checked here: [`LaneGatesPassed::witnesses`] compares the `(module, callee
/// ledger)` the gates actually ran over — borrowed by the token — against the pair
/// this call was handed, by address, and a mismatch refuses the body. See
/// [`LaneGatesPassed`] for both halves and for what neither of them closes.
fn green_body(
    definition: crate::lineage::DefinitionIdentity,
    module: &Module,
    callees: &[CalleeRef],
    source_header_correspondence: crate::mir_differential::SourceHeaderCorrespondence,
    lane_gates: LaneGatesPassed<'_>,
) -> Option<GreenBody> {
    // Trust: the lane gates were read for THIS body, not merely for SOME body — the
    // half rustc cannot state, checked by address against what the aggregate actually
    // ran over. Fail-closed: a mismatch registers nothing and the body stays on built
    // MIR. See `LaneGatesPassed`.
    if !lane_gates.witnesses(module, callees) {
        return None;
    }
    let lineage = crate::lineage::body_lineage_digest(definition, module, callees).ok()?;
    if !source_header_correspondence.authenticates(lineage) {
        return None;
    }
    // The provenance set is filled by `record_green` (the only caller with a `Lowered`); the unit
    // tests below mint digest-only entries and never reach the reshape.
    Some(GreenBody {
        module: module.clone(),
        callees: callees.to_vec(),
        lineage,
        enum_fold_switch_blocks: std::collections::HashSet::new(),
        source_header_correspondence,
    })
}

/// Green bodies for one compiler Session. The crate-local `DefIndex` is safe as
/// the key only inside that Session; a process-global registry let a later
/// rustc_driver Session consume stale MIR from an earlier crate at the same
/// index. Session storage is also the synchronization boundary for parallel
/// `mir_built` queries.
#[derive(Default)]
struct SessionFlipRegistry {
    entries: HashMap<u32, GreenBody>,
    /// def_indexes that saw a SECOND `record_green` — the once-per-def
    /// invariant broke, so no lowering for that def may be trusted for the
    /// rest of the session (see `record_green`). `take` refuses them.
    poisoned: std::collections::HashSet<u32>,
}

impl SessionFlipRegistry {
    /// The TyCtxt-free registry write (see `record_green` for the poison
    /// rationale). Split out so the record→take round-trip — including the
    /// lineage digest riding the entry — is a unit-testable obligation.
    fn insert_green(&mut self, def_index: u32, entry: GreenBody) {
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

    /// The TyCtxt-free registry consume: poisoned defs NEVER yield a module.
    fn take_green(&mut self, def_index: u32) -> Option<GreenBody> {
        if self.poisoned.contains(&def_index) {
            return None;
        }
        self.entries.remove(&def_index)
    }
}

/// Trust: all session-level flip gates (see module docs). Cheap; called per green body.
/// NOTE: lifetime markers are deliberately NOT a session gate anymore — they are a per-BODY
/// gate in [`record_green`] (`markers_exact`), so `-O` sessions flip what they can prove.
///
/// # What `debuginfo == None` costs, measured
///
/// The shim reconstructs MIR from the Module alone. The Module now carries
/// instruction spans, lexical scopes, and parameter names, but measured corpus
/// parity still finds line-row/column divergence and the producer deliberately
/// omits local names. A flipped body could therefore publish incomplete or
/// different line tables and locals. That is not a correctness question — it
/// is a debugger-visible regression, so the session declines rather than emit
/// a body it cannot describe exactly.
///
/// The scope of that decision deserves to be stated where the condition is,
/// because it is larger than it reads. targo's `dev` profile resolves to
/// `TomlDebugInfo::Full` and it emits `-C debuginfo` only when the level is not
/// `None`, so `dev` compiles carry `-C debuginfo=2` and `release` compiles carry
/// no debuginfo flag at all. Re-measured 2026-07-25 on a five-body scalar probe:
/// **5 flips with no `-C debuginfo` flag and at `=0`, 0 at `=1` and `=2`**, and
/// 3 at `-C opt-level=3` where the per-body marker gate takes the rest.
/// "Compiled from trust-ir" therefore describes debuginfo-free builds — a
/// `--release`-shaped profile — and never the default verified `targo trust
/// build`. (Earlier probe, kept because it shows the producer moving and the
/// cliff not: 4 at `-C debuginfo=0`, 1 at `-O`.)
///
/// The gate is not a coverage lever. Relaxing it to raise the flip rate would
/// trade real evidence for a bigger number; the way to widen this is to close
/// the measured span-attribution/structure differences and carry authenticated
/// names for locals so a flipped body can reproduce what it replaced.
pub fn flip_session_enabled(tcx: TyCtxt<'_>) -> bool {
    session_gates_allow_flip(
        tcx.sess.trust_ir_lower_enabled(),
        tcx.sess.opts.unstable_opts.trust_ir_flip,
        tcx.sess.opts.debuginfo,
        tcx.sess.instrument_coverage(),
    )
}

/// The gate above with the `TyCtxt` lifted out, so the scope it claims is a
/// test obligation and not just a comment. Splitting it is the only way the
/// measured numbers can be defended against a one-character edit.
pub const fn session_gates_allow_flip(
    trust_ir_lower_enabled: bool,
    trust_ir_flip_flag: bool,
    debuginfo: DebugInfo,
    instrument_coverage: bool,
) -> bool {
    trust_ir_lower_enabled
        && trust_ir_flip_flag
        && debuginfo_level_allows_flip(debuginfo)
        && !instrument_coverage
}

/// Exactly one debuginfo level is reproducible by the shim: the one that asks
/// for nothing. Every other level names line tables or locals the derived body
/// has no way to carry, so admitting it would emit a body that silently
/// describes itself wrongly to a debugger.
const fn debuginfo_level_allows_flip(debuginfo: DebugInfo) -> bool {
    match debuginfo {
        DebugInfo::None => true,
        // Trust (C2, re-measured 2026-07-26): line tables are STILL not earned, but the
        // reason recorded here has changed, and the change is the useful part.
        //
        // The consumption defect this arm used to name IS FIXED and verified. The producer
        // now stamps the tail `Return` at `shrink_to_hi()` like `construct_fn` does, and
        // `span_from_source_span` resolves the end-of-line column exactly instead of either
        // fabricating it or (my next mistake) rejecting it. On both hand-written probes the
        // dwarfdump line tables are now byte-identical, flip on vs off.
        //
        // Two probes agreeing is not a gate. At corpus scale — 300 tests/ui files, 64 of
        // which flipped at least one body (106 bodies total) — 49 agree and 15 DISAGREE, in
        // two distinct classes:
        //
        //   * ROW COUNT differs (6 files; e.g. 2039 built vs 2035 derived rows in
        //     threads-sendsync/yield.rs, 690/684 in box/unit/basic-operations.rs). The
        //     derived body has a different number of statements, so it cannot have the same
        //     number of line rows. This is not a span bug at all: `DerivedAgreed` is
        //     equivalence UP TO the documented normalizations, and line-table identity is a
        //     STRUCTURAL demand that equivalence-up-to-normalization does not answer.
        //   * COLUMN differs at equal row count (9 files; e.g. traits/issue-18412.rs, where
        //     built attributes a row to the method name at col 35 and the derived body puts
        //     it at col 5, the `fn` keyword). Genuine per-node attribution divergence —
        //     built picks a different sub-expression span than the producer's innermost-expr
        //     rule does.
        //
        // So opening this arm needs one of: a normalization ledger that preserves statement
        // structure under debuginfo, or an attribution pass that matches built's choice
        // node by node. Neither is a span-reconstruction fix, which is why the previous
        // note pointed the next reader at the wrong thing.
        //
        // `Limited`/`Full` need everything above PLUS `var_debug_info` for locals. The
        // lexical scope tree they also want now EXISTS (C2-scopes: the Module carries it,
        // `build_source_scopes` rebuilds it, and it reproduces built's per-`let` chain), but
        // the shim mints debug info for PARAMS only — deliberately, since binding a name to
        // a guessed local is worse than silence — so a derived body at `Limited` would show
        // a debugger correctly-nested scopes containing no locals.
        DebugInfo::LineDirectivesOnly
        | DebugInfo::LineTablesOnly
        | DebugInfo::Limited
        | DebugInfo::Full => false,
    }
}

/// Trust (union lane): may a body that registered `union_lane` union PLACEHOLDER lanes flip?
///
/// Never. Extracted as a `TyCtxt`-free predicate so the refusal is pinned by a
/// unit test instead of living only inside a function no test can call.
fn union_lane_allows_flip(union_lane: bool) -> bool {
    !union_lane
}

/// Trust (enum param lane): may a body that registered ENUM PARAM PLACEHOLDER lanes flip?
///
/// Never. The lane spells `Ty::Unit` — zero bytes — for a variant field that holds a caller's
/// `T`, so codegen'ing a function that copies such an enum by value would silently drop the
/// payload; and `to_mir` has no arm that compares a trust-ir `EnumDef`'s field list against the
/// built type, exactly as it has none for `StructDef` (the defect `union_lane_allows_flip`
/// exists for).
///
/// STATED AS ITS OWN PREDICATE rather than left to the walls that also refuse the class today —
/// `to_mir`'s param and return gates both require `!built.has_non_region_param()`, which a
/// param-lane enum's rustc type fails BY CONSTRUCTION, so `record_green` is not even reached.
/// That is a real wall, but it is somebody else's ground truth about GENERICS, not a decision
/// about placeholder lanes: a future monomorphized instantiation reaching this seam must relax
/// THIS line deliberately. Extracted `TyCtxt`-free for the same reason
/// [`union_lane_allows_flip`] is: the refusal is then pinned by a unit test instead of living
/// only inside a function no test can call.
fn enum_param_lane_allows_flip(enum_param_lane: bool) -> bool {
    !enum_param_lane
}

/// Trust (fn-ptr adapter lane): may a body whose module carries a PRODUCER-SYNTHESIZED
/// closure→fn-pointer adapter flip?
///
/// Never. The adapter is a function with no rustc counterpart, so there is no built-MIR oracle
/// for it and no `Instance` it could be codegen'd as; and the crate assembler drops it outright.
///
/// STATED AS ITS OWN PREDICATE rather than left to the three absences that also refuse it today —
/// `body_lineage_digest` errs on a module with != 1 function (so `green_body` returns `None`),
/// `to_mir::const_of` has no `Constant::FnDef` arm (so the derived-MIR verdict is never
/// `DerivedAgreed` and this function is never even called), and `BodyKind::StaticInit` is outside
/// the body-kind allow-list. Each of those is a real wall; none of them is a decision about
/// synthetic functions, and two of them would evaporate the moment someone widened an unrelated
/// arm. Extracted `TyCtxt`-free for the same reason [`union_lane_allows_flip`] is: the refusal is
/// then pinned by a unit test instead of living only inside a function no test can call.
fn fnptr_adapter_allows_flip(fnptr_adapter: bool) -> bool {
    !fnptr_adapter
}

/// Trust (wave-TR provenance ledger): may a body that FORWARDED unledgered THIN SHARED REBORROWS
/// flip?
///
/// Only when EVERY forwarded row is one this gate can CERTIFY against the module it is about to
/// hand codegen. Today that is exactly one provenance class, [`ThinReborrowProvenance::CallResult`],
/// and the certificate is [`call_result_reborrow_is_confined`]. Every other class is refused, on
/// the same reasoning the pre-ledger cut refused all of them.
///
/// # What the refusal was, and why supplying a record is a CERTIFICATION rather than a relaxation
///
/// The pre-ledger predicate was literally `!thin_reborrow` over a bare `bool`, and its stated
/// reason was: the wave-TR arm returns a `&T` VALUE that is in no pointer ledger (`borrow_ptrs` /
/// `ref_param_ptrs` / `global_ptrs` / `interior_ptrs`), so "the producer holds no record it could
/// hand the flip about where the pointer came from". That is a refusal for ABSENCE OF EVIDENCE,
/// not for a known hazard — the arm emits ZERO instructions, mints no allocation and makes no
/// memory-model claim. The honest way past it is therefore to produce the missing evidence and
/// CHECK it, which is what `Lowered::thin_reborrows` and this function do. Nothing here weakens a
/// guard: the gate still refuses every row it cannot account for, and it now additionally refuses
/// rows whose class tag says `CallResult` while the module says otherwise.
///
/// # Why this lane is still stated as OUR decision
///
/// The wall that used to also refuse the dominant provenance HAS FALLEN. `to_mir` once put a
/// `&T`-returning callee outside its call fragment ("Call(callee return outside the fragment: …)")
/// because `ir_scalar_of_body` is `None` for a reference and the fallback arm demanded a `Copy`,
/// `!needs_drop` `ty::Adt(struct)`. T2d added a shared-reference disjunct (`to_mir.rs:4401`/`:4448`,
/// for the `<LevelArc as Deref>::deref(&payload) -> &Level` shape) and T2e added a
/// scalar-`BackendRepr` enum disjunct, both for unrelated reasons. A `&T`-returning callee is now
/// INSIDE the call fragment, so this lane is the only thing that was still refusing the class —
/// which is precisely why it had to be a decision and not an inherited accident. `TyCtxt`-free for
/// the same reason [`union_lane_allows_flip`] and [`fnptr_adapter_allows_flip`] are: the whole
/// decision is then executable by a unit test.
/// Trust (wave-MR): the `&mut` twin of [`thin_reborrows_allow_flip`], and DELIBERATELY STRICTER —
/// it refuses the whole class rather than re-using the shared side's confinement certificate.
///
/// `call_result_reborrow_is_confined` was written for a value that is only READ: it establishes
/// that a forwarded `&T` cannot outlive or alias its way past what the module shows. A `&mut`
/// forwarded out of a body is a value someone may WRITE THROUGH, and the argument for that is not
/// the same argument — confinement of a read does not bound the effects of a write. Reusing the
/// certificate here would be borrowing the *shape* of a proof whose content does not transfer.
///
/// So: refuse for absence of evidence, which is exactly the pre-certificate wave-TR posture and is
/// honest as stated. The ROWS are still recorded (`Lowered::mut_reborrows`) so a later wave can
/// certify the class against the module rather than re-derive it from scratch — the same reason
/// the shared side kept its rows before it had a certificate.
///
/// `TyCtxt`-free, so the decision is executable by a unit test.
fn mut_reborrows_allow_flip(mut_reborrows: &[ThinReborrow]) -> bool {
    mut_reborrows.is_empty()
}

fn thin_reborrows_allow_flip(
    module: &Module,
    callees: &[CalleeRef],
    thin_reborrows: &[ThinReborrow],
) -> bool {
    thin_reborrows.iter().all(|reborrow| match reborrow.provenance {
        // CERTIFIABLE — and only if the module bears the claim out. See the function.
        ThinReborrowProvenance::CallResult => {
            call_result_reborrow_is_confined(module, callees, reborrow.value)
        }
        // REFUSED, unchanged from the pre-ledger cut. A binding read, a projection read and the
        // catch-all all name values that no instruction in this body mints: the value is whatever
        // a binding was bound to (possibly in a predecessor block, possibly by a `match` arm,
        // possibly by the caller), or whatever a load found in memory this lowering does not
        // model. There is no defining instruction to hand the flip, so there is nothing for a
        // confinement check to check, and the honest posture is the original refusal.
        //
        // Spelled as three NAMED arms rather than a `_ =>` wildcard: a future provenance class
        // must be classified deliberately here, and a wildcard would silently admit it into
        // whatever bucket the compiler picked.
        ThinReborrowProvenance::Binding
        | ThinReborrowProvenance::Projection
        | ThinReborrowProvenance::Other => false,
    })
}

/// Trust (wave-TR provenance ledger): THE CONFINEMENT CHECK. Is `value` — a `&T` this body
/// forwarded with no ledger entry behind it, claimed by the producer to be a CALL RESULT — minted
/// by a direct call to a ledgered callee inside the very module the flip is about to derive MIR
/// from?
///
/// # The property this establishes
///
/// If this returns `true` then, in the single body function of this per-body module:
///
///   1. `value` is not a block parameter of any block, so it never arrives along a control-flow
///      edge and cannot mean different things in different predecessors;
///   2. EXACTLY ONE instruction node lists `value` in its results, and `value` is that node's ONLY
///      result, so the value has one unambiguous definition site and is not one lane of a
///      multi-result instruction;
///   3. that instruction is a DIRECT [`Inst::Call`] — not `CallIndirect`, not any other form; and
///   4. its `callee` `FuncId` matches EXACTLY ONE entry in this body's callee identity ledger
///      ([`crate::CalleeRef`]) — the same ledger `crate_module` uses to rewrite intra-crate callee
///      ids and the same ledger the lineage digest frames, read under that ledger's own ambiguity
///      rule. Production allocation gives each exact callee identity one dense body-local
///      `FuncId`; this check nevertheless requires exactly one row and rejects a malformed or
///      replayed ledger that places two identities behind one id, matching `to_mir` and
///      `crate_module::resolve_callee`.
///
/// # Why that property makes the flip safe FOR THIS CLASS
///
/// The lane's stated hazard is that codegen would receive a pointer this body cannot account for.
/// Under (1)–(4) it CAN, and the account travels with the artifact rather than beside it: the
/// DEFINING INSTRUCTION of the forwarded pointer is in THE MODULE BEING FLIPPED, so `to_mir`
/// materializes the value as the destination local of that same call. There is no free-floating
/// reference in the flipped body.
///
/// STATED PRECISELY, because this is the text a later wave will cite when it widens the class:
/// what the module contains is the instruction that OBTAINS the pointer, not the instruction that
/// MINTS it. For the headline shape `<LevelArc as Deref>::deref(&payload) -> &Level` the pointer
/// is created inside `deref`'s body, in another translation unit; a ledgered callee may equally
/// return a pointer into one of its arguments, into a `'static`, or into another frame. NONE of
/// (1)–(4) excludes those, and this check does not claim pointer provenance in the aliasing sense.
/// It establishes a STRUCTURAL fact — this body has one nameable definition site for the value,
/// and it is a call to a callee this body already declared — which is exactly what the lane was
/// refusing for the absence of. Three specific ways the old refusal could have been right are
/// closed by name:
///
///   * **A dangling or ambiguous value.** Zero definitions would mean the arm forwarded a
///     `ValueId` the module never defines; two would mean the module is not in SSA at that value.
///     Either is a malformed input to `to_mir`, and (1)+(2) refuse both instead of hoping the
///     derived body happens to be well formed.
///   * **An origin outside the flip's own admission.** (3)+(4) confine the definition to a direct
///     call to a callee this body ALREADY declared, so the pointer's producing instruction is
///     subject to exactly the admissions the call itself passed. An indirect call is refused
///     because there is no statically-known callee to name — the record would be a record of
///     nothing.
///   * **A representation change hiding in the reborrow.** Already excluded upstream, and stated
///     here so the argument is complete: `thin_shared_reborrow_shape_admits` established that
///     `&*r` and `r` have the same region-erased type and that both sides are `FatShape::Thin`, so
///     the forwarded value is bit-identical to the call's return value.
///
/// # What it does NOT establish
///
/// Nothing about whether the callee's own body is trustworthy, nothing about aliasing, and nothing
/// about the MIR→machine-code leg (that is the differential gate's business). It establishes that
/// the flip is not being asked to vouch for a pointer out of nowhere — which is the one thing the
/// lane was refusing for.
///
/// # Non-vacuity
///
/// This is a check, not a rename: it can and does FAIL on a row whose class tag says `CallResult`.
/// A call the producer lowered to something other than a direct `Inst::Call` (an intrinsic folded
/// to arithmetic, a call whose result got rebound through a block parameter, a future arm that
/// forwards one lane of a multi-result call) is refused HERE, by the module, with the tag saying
/// otherwise. `test_a_call_result_row_the_module_does_not_bear_out_is_refused` drives exactly that.
fn call_result_reborrow_is_confined(
    module: &Module,
    callees: &[CalleeRef],
    value: ValueId,
) -> bool {
    // Fail closed unless this is a per-body mini-module with exactly one function. Stated as this
    // function's OWN obligation rather than inherited from `green_body`'s lineage-digest rule: the
    // lane gates run BEFORE the digest is minted, and a value id is only meaningful inside one
    // function's SSA space, so scanning a multi-function module could match a different function's
    // value of the same number.
    let [body] = module.functions.as_slice() else {
        return false;
    };
    // (1) NOT A BLOCK PARAMETER. A block param arrives along an edge; its "definition" is every
    // predecessor's branch argument, which is not a site the flip can name.
    if body.blocks.iter().any(|block| block.params.iter().any(|(param, _)| *param == value)) {
        return false;
    }
    // (2) EXACTLY ONE defining node, and `value` is its ONLY result.
    let mut definitions = body
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .filter(|node| node.results.contains(&value));
    let Some(definition) = definitions.next() else {
        return false;
    };
    if definitions.next().is_some() {
        return false;
    }
    if definition.results.as_slice() != [value] {
        return false;
    }
    // (3) A DIRECT CALL — `CallIndirect` has no statically-known callee to record, and every other
    // instruction form means the producer's `CallResult` claim does not describe what it emitted.
    let Inst::Call { callee, .. } = &definition.inst else {
        return false;
    };
    // (4) TO A LEDGERED CALLEE THE LEDGER CAN NAME — EXACTLY ONE ENTRY, never merely "at least
    // one". Production `admit_callee_inner` interns full identity and allocates a fresh dense id
    // for every new row, so two rows here require a malformed/replayed public input. The consumer
    // still rejects that set rather than letting an existential mint a confinement certificate
    // whose callee cannot be named — "a record of nothing", the same reason `CallIndirect` is
    // refused above.
    //
    // This is the ambiguity rule of BOTH peer consumers of this ledger, stated the same way:
    // `to_mir`'s Call arm (`[c] => .., [] => unsup("Call(unledgered callee FuncId)"), _ =>
    // unsup("Call(ambiguous callee FuncId: non-singleton ledger)")`) and
    // `crate_module::resolve_callee`,
    // whose `_ =>` arm declares `!ambiguous_callee_N` rather than link a guessed body.
    //
    // NOT written as `.any()` plus a note that `to_mir` refuses the body first. That would be
    // relying on unreachability, which is the exact mistake this lane exists to avoid: the wall
    // this gate replaced ("Call(callee return outside the fragment)") was widened away by T2d/T2e
    // for unrelated reasons, and a future wave disambiguating a `FuncId` by `site_args` would
    // retire `to_mir`'s refusal the same way — silently taking this certificate live.
    matches!(callees.iter().filter(|entry| entry.func_id == *callee).count(), 1)
}

/// Trust: the conjunction of every per-body PLACEHOLDER/PROVENANCE LANE gate — the single thing
/// [`record_green`] calls, so that "is this lane wired into the flip decision?" is a question a
/// unit test can answer.
///
/// WHY THIS EXISTS AS A FUNCTION. Each lane predicate below is `TyCtxt`-free precisely so a test
/// can execute it, but the CALL SITE was not: `record_green` takes a `TyCtxt` and no unit test can
/// reach it, so with the four gates spelled as consecutive `if … { return; }` blocks, DELETING one
/// left the whole suite green (measured, wave-TR: 262/262 passed with the thin-reborrow gate
/// removed from the body). A gate nothing reads is not a gate. Routing them through one
/// `&Lowered`-taking conjunction moves the wiring into a pure function, where
/// `test_every_body_lane_gate_is_wired_into_the_flip_decision` pins each lane by fixture.
///
/// AND WHY IT RETURNS A TOKEN RATHER THAN A `bool`. The aggregation fixed the LANE half and
/// MOVED the CALL-SITE half: deleting `record_green`'s one-line refusal still left the suite
/// green, and the compensation was a test that read this file's own source text. The `Some`
/// arm's [`LaneGatesPassed`] retires that test. It is the only way to obtain the token
/// [`green_body`] takes by value, so a `record_green` that does not read this function as a
/// refusal does not COMPILE — and the token is minted BOUND to this `Lowered`'s own
/// `(module, callee ledger)`, so one read cannot license a different body either. The exact
/// error, and the residue neither half closes, are quoted on [`LaneGatesPassed`].
///
/// Order is irrelevant — every conjunct is a pure `!flag` on an independent field — so this is a
/// conjunction, not a sequence, and nothing here may acquire a side effect.
fn body_lane_gates_allow_flip(lowered: &Lowered) -> Option<LaneGatesPassed<'_>> {
    // Trust (union lane): a body whose module registered a UNION PLACEHOLDER LANE never flips.
    // The lane spells `Ty::Unit` for a struct field that holds real `union` bytes, and `to_mir`'s
    // param/return gates cannot catch it: both admit any concrete `ty::Adt(struct)` with
    // `!needs_drop` and never compare the trust-ir `StructDef`'s field list against the built
    // type. `<Sha256 as Clone>::clone` — which returns `Sha256` BY VALUE over exactly such a
    // struct — is `BodyKind::Fn`, i.e. admitted by the body-kind gate in `record_green`, and fully
    // concrete, i.e. past the layout pre-gate. Flipping it would emit a copy that silently drops
    // the union's contents. Load-bearing, not defensive, and keyed on the producer's ledger
    // (`Lowered::union_lane`), never on the `()` spelling.
    let every_lane_clear = !lowered.unsubstituted_opaque_return
        && union_lane_allows_flip(lowered.union_lane)
        // Trust (enum param lane): a body whose module registered an ENUM PARAM PLACEHOLDER LANE
        // never flips — see `enum_param_lane_allows_flip`. Load-bearing as a DECISION, not as a
        // consequence of `to_mir`'s generic-param gates happening to refuse the class today.
        && enum_param_lane_allows_flip(lowered.enum_param_lane)
        // Trust (fn-ptr adapter lane): a body whose module carries a producer-synthesized adapter
        // never flips — see `fnptr_adapter_allows_flip`. Load-bearing as a DECISION, not as a
        // consequence of the lineage digest's arity rule.
        && fnptr_adapter_allows_flip(lowered.fnptr_adapter)
        // Trust (wave-TR provenance ledger): a body that forwarded unledgered thin shared reborrows
        // flips only if EVERY forwarded row is certified against the module — see
        // `thin_reborrows_allow_flip`. Load-bearing as a DECISION: `to_mir`'s
        // call-return-fidelity gate used to refuse the dominant provenance for unrelated reasons
        // and T2d/T2e have since widened it away, so nothing but this lane refuses the class.
        //
        // This conjunct is the one that reads the MODULE as well as a flag, which is why the
        // aggregate takes `&Lowered` and not a tuple of bools: the certificate is about the
        // artifact, not about a summary of it.
        && thin_reborrows_allow_flip(&lowered.module, &lowered.callees, &lowered.thin_reborrows)
        // Trust (wave-MR): the `&mut` twin, refused as a whole class — see
        // `mut_reborrows_allow_flip` for why the shared side's confinement certificate does not
        // transfer to a value someone may write through.
        && mut_reborrows_allow_flip(&lowered.mut_reborrows);
    // The ONLY mint. The token cannot exist outside this arm, so a caller cannot hold
    // one without having asked — and cannot ask without acting on the answer. It is
    // minted BOUND to the very `(module, callee ledger)` the conjunction above just
    // read, which is what lets `green_body` refuse a token borrowed for another body;
    // `record_green` passes `&lowered.module` / `&lowered.callees` on, so the
    // production path binds by construction.
    every_lane_clear.then(|| LaneGatesPassed {
        module: &lowered.module,
        callees: &lowered.callees,
    })
}

/// Whether this definition's TrustIR module carries a complete source-loop and
/// exact-place map authenticated by a freshly regenerated compiler query, and
/// whether its bindings fit the verifier body's one global source-name space.
///
/// The v35 carrier authenticates `name -> hir_local_id -> loop-header parameter
/// index`.  Carrier validation alone deliberately does not authorize a
/// multi-loop HIR-id/BlockId association; `record_green` additionally requires
/// the differential's compiler-stamped, canonical-role correspondence verdict.
/// `to_mir` consumes the authenticated identity by reusing one MIR place per
/// HIR binding and emitting real
/// `var_debug_info` for the place. In particular, a
/// mutable parameter no longer leaves a separately named frozen entry copy —
/// the exact bug that once made `invariant n == 5` prove after `n -= 1`.
///
/// Authentication is still necessary but not sufficient. Two hygienically
/// distinct bindings with one displayed spelling cannot be represented by the
/// verifier's current global formula namespace, so that body remains refused.
/// The MIR shim repeats the same injectivity check and fails closed if any place
/// or type cannot be reconstructed exactly.
pub fn source_place_provenance_allows_flip(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    module: &Module,
) -> bool {
    match crate::source_provenance::validated_source_provenance(tcx, def, module) {
        // Fail closed on every missing, stale, forged or ambiguous carrier.
        Err(_) => false,
        // Contract-free: nothing to erase, and the carrier correctly claims no
        // authority. Unchanged by this gate.
        Ok(None) => true,
        // Contracted: bound roots are eligible only when their authenticated
        // names remain globally injective for the reconstructed verifier body.
        Ok(Some(provenance)) => loop_bindings_allow_flip(&provenance),
    }
}

/// Trust: global `(name, HIR id)` injectivity required by today's formula-name
/// interface. The carrier can represent repeated use of one binding across
/// sequential loops. Shadowed bindings with the same spelling and one binding
/// respelled across loops are not representable.
fn loop_bindings_allow_flip(provenance: &trust_ir::SourceProvenance) -> bool {
    let mut names = BTreeMap::<&str, u32>::new();
    let mut bindings = BTreeMap::<u32, &str>::new();
    provenance.loops.iter().flat_map(|source_loop| &source_loop.bindings).all(|binding| {
        names
            .insert(binding.name.as_str(), binding.hir_local_id)
            .is_none_or(|previous| previous == binding.hir_local_id)
            && bindings
                .insert(binding.hir_local_id, binding.name.as_str())
                .is_none_or(|previous| previous == binding.name)
    })
}

/// Trust (F4, 2026-09-29; reworked after the review): the per-body marker gate with the
/// `TyCtxt` lifted out. A body whose marker sequence was not proven exact may flip only when
/// its markers cannot reach ANY codegen or interpreter:
///   * this session emits no lifetime intrinsics;
///   * `RemoveStorageMarkers` deletes every marker from `optimized_mir` before anything reads
///     it — its own `is_enabled` (`mir_opt_level > 0 && !emit_lifetime_markers`) under
///     `pass_manager::should_run_pass`'s `-Zmir-enable-passes` override (last matching entry
///     wins; the pass `is_required`, so `#[optimize(none)]` never suppresses it) — and NO
///     `-Zmir-opt-bisect-limit` is set: the bisect counter is global across passes and bodies,
///     so whether it skips this pass on this body cannot be decided here, and the answer is
///     no exemption rather than a prediction;
///   * the body is not one the CTFE seam installs (`ctfe_body`: a const or static initializer,
///     or a `#[rustc_comptime]` fn — `try_flip_ctfe`'s own admission set): its flip installs
///     `mir_for_ctfe`, which `RemoveStorageMarkers` never touches, which is encoded for other
///     crates as-is, and which the const-eval interpreter runs WITH its markers — a use of a
///     storage-dead local is an interpreter error, i.e. a different const-eval result. No
///     exemption there.
/// The encoded cross-crate copy of a codegen-seam FN body IS its post-pass `optimized_mir`
/// (`rustc_metadata` records `tcx.optimized_mir(def_id)`), so a stripped body carries no marker
/// to another crate either.
pub const fn marker_gate_allows_flip(
    markers_exact: bool,
    emit_lifetime_markers: bool,
    mir_opt_level: usize,
    remove_storage_markers_override: Option<bool>,
    opt_bisect_limited: bool,
    ctfe_body: bool,
) -> bool {
    if markers_exact {
        return true;
    }
    if ctfe_body || opt_bisect_limited {
        return false;
    }
    let stripped = match remove_storage_markers_override {
        Some(on) => on,
        None => mir_opt_level > 0,
    };
    !emit_lifetime_markers && stripped
}

/// Trust: called from the `mir_built` hook for bodies whose derived-MIR differential verdict is
/// `DerivedAgreed` (the caller checks the verdict; `unsupported` is re-checked here defensively).
/// `markers_exact` is the differential's EXACT marker-channel verdict for THIS body; when the
/// session emits lifetime markers (`-O` / sanitizers) it is required (see module docs).
/// No-op unless every gate holds — the registry stays empty when the flip cannot fire.
pub fn record_green(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    lowered: &Lowered,
    markers_exact: bool,
    source_header_correspondence: Option<&crate::mir_differential::SourceHeaderCorrespondence>,
) {
    if !flip_session_enabled(tcx) {
        return;
    }
    if !source_place_provenance_allows_flip(tcx, def, &lowered.module) {
        return;
    }
    // Trust: unlike compiler/source/semantic/binding digests, a self-sealed
    // carrier cannot prove which of several natural headers belongs to one HIR
    // loop.  The opaque value can only be minted by `compare_derived` after
    // matching compiler-stamped built headers and translated TrustIR headers by
    // equal UNIQUE canonical roles.  Require it for every body (contract-free
    // comparisons get a bound empty-map witness) so no caller can substitute a
    // naked success bit or silently omit the identity channel.
    let Some(source_header_correspondence) = source_header_correspondence.copied() else {
        return;
    };
    // Trust: per-body marker gate (module docs). Fail-closed: an unproven marker sequence
    // must never reach codegen where markers are material.
    //
    // Trust (F4, 2026-09-29): "not material" used to be decided by `!emit_lifetime_markers()`
    // alone, i.e. by THIS session's codegen. At `-Zmir-opt-level=0`, or with
    // `-Zmir-enable-passes=-RemoveStorageMarkers`, the unproven markers survive into
    // `optimized_mir`, which is what metadata encodes for an `#[inline]`/generic body, and a
    // downstream `-O` crate codegens them with lifetime intrinsics. REFUSES MORE: the
    // exemption now also requires that `RemoveStorageMarkers` runs in this session.
    let remove_storage_markers_override = tcx
        .sess
        .opts
        .unstable_opts
        .mir_enable_passes
        .iter()
        .rev()
        .find(|(name, _)| name == "RemoveStorageMarkers")
        .map(|&(_, on)| on);
    if !marker_gate_allows_flip(
        markers_exact,
        tcx.sess.emit_lifetime_markers(),
        tcx.sess.mir_opt_level(),
        remove_storage_markers_override,
        tcx.sess.opts.unstable_opts.mir_opt_bisect_limit.is_some(),
        // Trust (F4, round 4): a body the CTFE seam installs. `try_flip_ctfe` admits exactly
        // `hir_body_const_context` = `Const { .. } | Static(_)`, and that includes a
        // `#[rustc_comptime]` fn, whose `BodyKind` is `Fn`: the kind alone undercounts.
        matches!(lowered.body_kind, crate::BodyKind::ConstInit)
            || matches!(
                tcx.hir_body_const_context(def),
                Some(rustc_hir::ConstContext::Const { .. } | rustc_hir::ConstContext::Static(_))
            ),
    ) {
        return;
    }
    // Defensive: a green verdict implies a clean lowering, but never trust the caller.
    if !lowered.unsupported.is_empty() {
        return;
    }
    // Trust: EVERY per-body PLACEHOLDER/PROVENANCE LANE refusal, in one call — see
    // [`body_lane_gates_allow_flip`] for each lane's own predicate and its own reason. Aggregated
    // rather than written as four consecutive `if … { return; }` blocks so that the WIRING itself
    // is testable: no unit test can reach this `TyCtxt`-taking function, so with the gates spelled
    // inline, dropping one from the list was a silent widening that every existing test still
    // passed (measured, wave-TR mutation C).
    //
    // THIS LINE IS NOT PINNED BY A TEST ANY MORE — it is enforced by rustc. `lane_gates` is the
    // only `LaneGatesPassed` this function can obtain, nothing else in the crate can mint one,
    // and `green_body` below takes one BY VALUE. Delete this `let … else` and the `green_body`
    // call FAILS TO COMPILE instead of recording a lane-carrying body; the exact error, and the
    // forgery the type does NOT close, are quoted on `LaneGatesPassed`. That is wave-TR mutation
    // C, one level up, closed rather than moved — and it retires
    // `test_the_lane_gate_aggregate_is_read_by_record_green`, which enforced the same property by
    // `include_str!`ing this file and counting occurrences of the aggregate's own name.
    // Two halves stay OUTSIDE what rustc can see, and each has its own pin:
    // `test_every_body_lane_gate_is_wired_into_the_flip_decision` owns WHICH lanes the
    // aggregate consults, and `test_a_lane_gate_token_cannot_license_a_different_body` owns
    // that a token read over one body cannot record another — enforced at run time, by
    // address, inside `green_body`.
    let Some(lane_gates) = body_lane_gates_allow_flip(lowered) else {
        return;
    };
    // Trust (CTFE flip lane): FN bodies flip on the CODEGEN seam (`optimized_mir` → `try_flip`);
    // const/associated-const INITIALIZER bodies (`BodyKind::ConstInit`) flip on the CTFE seam
    // (`inner_mir_for_ctfe` → `try_flip_ctfe`), where the const-eval interpreter consumes MIR
    // re-derived from the trust-ir Module. `BodyKind::Fn` covers const FNs too — they are gated OUT
    // on BOTH seams (`flip::derive_flip_body`'s ConstFn arm rejects on the codegen seam;
    // `try_flip_ctfe`'s `Const|Static` pre-gate returns before `take` on the ctfe seam) so a const
    // fn can never get a split ctfe-vs-runtime body. STATIC initializers (`BodyKind::StaticInit`,
    // linkage / interior-mutability nuances) stay on built MIR pending a later wave. Any other body
    // kind is refused outright. The `pending_consts` gate below is a further defense: a const
    // initializer carrying un-evaluated placeholder sentinels is still refused.
    if !matches!(lowered.body_kind, crate::BodyKind::Fn | crate::BodyKind::ConstInit) {
        return;
    }
    // Trust: a pending-const body carries un-evaluated placeholder sentinels (patched only by
    // the crate finalizer, and only in the DUMP copy) — its Module must never reach codegen.
    // The derived-MIR differential already returns `DerivedUnsupported` for such bodies (so
    // the caller never sees a green verdict), but never trust the caller.
    if !lowered.pending_consts.is_empty() {
        return;
    }
    // Trust (L1, artifact-lineage attestation): mint the entry — including its lineage
    // digest over the INTACT hook-time (module, callee ledger), the same object
    // `crate_module::record` digests for the artifact row, BEFORE it strips `functions[0]`
    // for assembly. Fail-closed: no digest, no green — a flip event must always be able to
    // name, by digest, exactly which body it selected, or the whole attestation chain has a
    // hole at its first link.
    let definition = crate::lineage::DefinitionIdentity::from_def_id(tcx, def.to_def_id());
    let Some(mut entry) = green_body(
        definition,
        &lowered.module,
        &lowered.callees,
        source_header_correspondence,
        lane_gates,
    ) else {
        return;
    };
    // Trust (enum-switch provenance): carry the hook-time set forward for the flip's re-derivation.
    entry.enum_fold_switch_blocks = lowered.enum_fold_switch_blocks.clone();
    let def_index = def.to_def_id().index.as_u32();
    tcx.sess.with_trust_compiler_state::<SessionFlipRegistry, _>(|reg| {
        // `mir_built` runs once per def, so a SECOND registration for the same
        // def_index is an invariant violation — and a dangerous one. The
        // registry key is the bare DefIndex (no GenericArgs), while `take` is
        // consumed by `optimized_mir`/`mir_for_ctfe`, which are keyed on
        // LocalDefId. A first-write-wins `or_insert_with` would therefore let
        // ONE body's Module be codegen'd for the definition even if a later
        // registration carried a DIFFERENT lowering (e.g. a per-instance lane
        // specialized to one instantiation) — a silent MISCOMPILE with no
        // diagnostic. POISON instead: drop the entry and mark the def_index
        // permanently ineligible so `take` returns None and the body falls
        // back to built MIR (fail-closed, never a wrong body).
        reg.insert_green(def_index, entry);
    });
}

/// Trust: consume the green [`GreenBody`] (module, callee ledger, lineage digest) for `def`,
/// if any. Removing the entry bounds memory and makes a second `take` (which cannot happen:
/// `optimized_mir` runs once per def per session) inert. A poisoned registry (panic while
/// locked) yields `None` — fail-closed to the normal path.
pub fn take(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<GreenBody> {
    let def_index = def.to_def_id().index.as_u32();
    tcx.sess.with_trust_compiler_state::<SessionFlipRegistry, _>(|reg| {
        // A poisoned def NEVER yields a module: the flip falls back to built
        // MIR rather than risk codegen'ing a body registered for different
        // args (see `record_green`).
        reg.take_green(def_index)
    })
}

#[cfg(test)]
mod tests {
    use rustc_session::config::DebugInfo;
    use rustc_span::def_id::{CrateNum, DefId, DefIndex};
    use trust_ir::{
        Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
    };

    use super::{
        CalleeRef, GreenBody, Lowered, SessionFlipRegistry, ThinReborrow, ThinReborrowProvenance,
        body_lane_gates_allow_flip, call_result_reborrow_is_confined, enum_param_lane_allows_flip,
        fnptr_adapter_allows_flip, green_body, loop_bindings_allow_flip, session_gates_allow_flip,
        thin_reborrows_allow_flip, union_lane_allows_flip,
    };

    fn probe_definition(index: u64) -> crate::lineage::DefinitionIdentity {
        crate::lineage::DefinitionIdentity::test_only(0xC0DE, index)
    }

    /// Trust (#soundness): authenticated bound roots may flip now that `to_mir`
    /// gives one HIR identity one real named place. The remaining representability
    /// wall is global injectivity: a shadowed spelling or a respelled HIR binding
    /// must not let the formula-name scan select either local by accident.
    #[test]
    fn loop_bindings_require_global_name_hir_injectivity() {
        use trust_ir::{SourceBindingProvenance, SourceLoopProvenance, SourcePlace};
        let digest = trust_ir::proof::ProofDigest::zero();
        let mk = |loops: Vec<Vec<SourceBindingProvenance>>| trust_ir::SourceProvenance {
            schema: 35,
            compiler_source_digest: digest.clone(),
            semantic_body_digest: digest.clone(),
            binding_digest: digest.clone(),
            loops: loops
                .into_iter()
                .enumerate()
                .map(|(index, bindings)| SourceLoopProvenance {
                    source_loop_id: index as u32,
                    hir_local_id: index as u32,
                    header: BlockId::new(index as u32 + 1),
                    bindings,
                })
                .collect(),
        };
        let binding = |name: &str, hir_local_id: u32| SourceBindingProvenance {
            name: name.to_string(),
            hir_local_id,
            place: SourcePlace::LoopParameter { index: 0 },
        };

        assert!(
            loop_bindings_allow_flip(&mk(vec![Vec::new()])),
            "a literal loop clause binds no source root and must stay flip-eligible"
        );
        assert!(
            loop_bindings_allow_flip(&mk(vec![vec![binding("n", 1)]])),
            "one authenticated bound source root is now exactly representable"
        );
        assert!(
            loop_bindings_allow_flip(&mk(vec![vec![binding("n", 1)], vec![binding("n", 1)]])),
            "the same HIR binding may be reused across sequential loop headers"
        );
        assert!(
            !loop_bindings_allow_flip(&mk(vec![vec![binding("n", 1)], vec![binding("n", 2)]])),
            "two shadowed HIR bindings with one spelling remain ambiguous"
        );
        assert!(
            !loop_bindings_allow_flip(&mk(vec![vec![binding("n", 1)], vec![binding("m", 1)]])),
            "one HIR binding may not acquire two formula spellings"
        );
    }
    use crate::lineage::body_lineage_digest;

    fn probe_module(fn_name: &str) -> Module {
        let mut module = Module::new("flip_registry_probe");
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(Function::new(FuncId::new(0), fn_name, ty, BlockId::new(0)))
            .expect("Module::try_add_function: test fixture");
        module
    }

    /// A real [`super::LaneGatesPassed`] FOR `lowered`, minted the only way anything
    /// can: by running the aggregate and taking its `Some`.
    ///
    /// Deliberately NOT a `#[cfg(test)]` constructor on the token. A test-only back
    /// door into the one type that carries "the gate is read" would be that
    /// invariant's own escape hatch, and it would be in scope for `record_green`
    /// in exactly the configuration the suite runs in.
    ///
    /// It takes the caller's `&Lowered` rather than fabricating one, because the token
    /// is BOUND to the body the gates were read over. The first cut of this helper took
    /// no argument and minted from a fixed fixture, which made it a live counterexample
    /// to the per-body claim on [`super::LaneGatesPassed`]: it handed out a witness for
    /// a body the caller never recorded.
    fn lane_gates_for(lowered: &Lowered) -> super::LaneGatesPassed<'_> {
        body_lane_gates_allow_flip(lowered)
            .expect("the all-clear lane fixture must pass every per-body lane gate")
    }

    /// The [`lane_probe_lowered`] posture, carrying THIS module — so a
    /// [`super::LaneGatesPassed`] minted from it is bound to the body the caller is
    /// about to record.
    ///
    /// `green_body` compares the token's borrowed `(module, callee ledger)` against its
    /// own arguments BY ADDRESS, so a caller must pass `&lowered.module` and
    /// `&lowered.callees` — never a separate copy of the same bytes.
    fn lane_probe_carrying(module: Module) -> Lowered {
        let mut lowered = lane_probe_lowered();
        lowered.module = module;
        lowered
    }

    fn green_body_for_test(
        definition: crate::lineage::DefinitionIdentity,
        module: &Module,
    ) -> Option<GreenBody> {
        let lowered = lane_probe_carrying(module.clone());
        let lineage = body_lineage_digest(definition, &lowered.module, &lowered.callees).ok()?;
        green_body(
            definition,
            &lowered.module,
            &lowered.callees,
            crate::mir_differential::SourceHeaderCorrespondence::test_only(lineage),
            lane_gates_for(&lowered),
        )
    }

    /// Built through the production constructor, never by hand — a test that
    /// assembled a `GreenBody` field-by-field could not witness the fail-closed rule.
    fn green_probe(fn_name: &str) -> GreenBody {
        green_body_for_test(probe_definition(3), &probe_module(fn_name))
            .expect("a single-function probe module must mint a green body")
    }

    /// Trust (L1) FAIL-CLOSED: no digest, no green. A mini-module that is not a
    /// single-function per-body lowering cannot be attested, so no registry entry
    /// exists for it and the body stays on built MIR.
    ///
    /// Trust (fn-ptr adapter lane): the MULTI-function half is now a shape the producer can
    /// actually emit (a body plus its synthesized closure→fn-pointer adapter), not a
    /// hypothetical — so it is asserted here alongside the body-less one.
    #[test]
    fn test_green_body_declines_when_lineage_cannot_be_digested() {
        assert!(
            green_body_for_test(probe_definition(3), &Module::new("no_bodies")).is_none(),
            "a body-less mini-module must not become a green entry: the flip event could \
             not name, by digest, which body it selected"
        );
        let mut two = probe_module("probe");
        let ty = two.functions[0].ty;
        two.try_add_function(Function::new(
            FuncId::new(crate::ADAPTER_FUNC_ID_BASE),
            "probe::{fnptr-adapter}",
            ty,
            BlockId::new(0),
        ))
        .expect("Module::try_add_function: test fixture");
        assert!(
            green_body_for_test(probe_definition(3), &two).is_none(),
            "a mini-module carrying a producer-synthesized adapter names two program objects; \
             it must not become a green entry"
        );
        assert!(
            green_body_for_test(probe_definition(3), &probe_module("probe")).is_some(),
            "the ordinary single-function case must still be admitted (the gate is not vacuous)"
        );
    }

    #[test]
    fn source_header_correspondence_witness_is_bound_to_exact_body_lineage() {
        let definition = probe_definition(3);
        // Each case owns the `Lowered` its token is minted over, so the only thing
        // varying between them is the witness/lineage pair this test is about. Minting
        // once and reusing the token would make the `is_none()` cases pass for the
        // WRONG reason — `LaneGatesPassed`'s own per-body refusal — and the test would
        // stop saying anything about the correspondence witness.
        let first = lane_probe_carrying(probe_module("first"));
        let lineage = body_lineage_digest(definition, &first.module, &first.callees)
            .expect("probe lineage");
        let witness = crate::mir_differential::SourceHeaderCorrespondence::test_only(lineage);

        // One `LaneGatesPassed` per call: the token is deliberately not `Clone`, so
        // each `green_body` here re-runs the aggregate for its own body.
        assert!(
            green_body(
                definition,
                &first.module,
                &first.callees,
                witness,
                lane_gates_for(&first)
            )
            .is_some(),
            "the witness must admit exactly the body lineage it seals"
        );
        let changed = lane_probe_carrying(probe_module("changed"));
        assert!(
            green_body(
                definition,
                &changed.module,
                &changed.callees,
                witness,
                lane_gates_for(&changed)
            )
            .is_none(),
            "a module mutation cannot reuse an earlier built/derived correspondence witness"
        );
        assert!(
            green_body(
                probe_definition(4),
                &first.module,
                &first.callees,
                witness,
                lane_gates_for(&first)
            )
            .is_none(),
            "a different stable definition identity cannot reuse the witness"
        );
    }

    /// **THE PER-BODY PIN.** A [`super::LaneGatesPassed`] read over one body must not
    /// license recording another.
    ///
    /// This is the half rustc cannot state — it only proves that SOME `Lowered` cleared
    /// the gates — and in the first cut of that type it was claimed in prose while this
    /// module's own test helper did exactly the thing the prose called impossible. The
    /// shapes that matter in production are a mint hoisted out of a loop, and a second
    /// `flip_registry` helper that mints once and records twice: both compile with 0
    /// errors, and both are refused here, fail-closed.
    ///
    /// EVERY OTHER INGREDIENT OF THE REFUSED CALL IS VALID — the witness authenticates
    /// the recorded body's own lineage, and the second assertion records that same body
    /// with its own token, so the refusal cannot be passing vacuously.
    #[test]
    fn test_a_lane_gate_token_cannot_license_a_different_body() {
        let definition = probe_definition(3);
        let read_over = lane_probe_carrying(probe_module("the_body_the_gates_read"));
        let recorded = lane_probe_carrying(probe_module("a_different_body"));
        let lineage = body_lineage_digest(definition, &recorded.module, &recorded.callees)
            .expect("probe lineage");
        let witness = crate::mir_differential::SourceHeaderCorrespondence::test_only(lineage);
        assert!(
            green_body(
                definition,
                &recorded.module,
                &recorded.callees,
                witness,
                lane_gates_for(&read_over)
            )
            .is_none(),
            "a lane-gate token read over one body must not record a different one"
        );
        assert!(
            green_body(
                definition,
                &recorded.module,
                &recorded.callees,
                witness,
                lane_gates_for(&recorded)
            )
            .is_some(),
            "the same call with the recorded body's OWN token must be admitted, or the \
             refusal above proves nothing"
        );
    }

    /// Trust (fn-ptr adapter lane) FLIP REFUSAL, PINNED AS A DECISION. A body whose module
    /// carries a producer-synthesized adapter never flips.
    ///
    /// The point of testing the PREDICATE rather than the pipeline: three unrelated walls also
    /// stop these bodies today — the lineage digest's `functions.len() != 1` rule above,
    /// `to_mir::const_of`'s missing `Constant::FnDef` arm (so the derived-MIR verdict is never
    /// `DerivedAgreed` and `record_green` is never called at all), and the `BodyKind` allow-list
    /// that excludes `StaticInit`. None of those is a decision about synthetic functions, and a
    /// future wave that widens any one of them must still meet this line.
    #[test]
    fn test_fnptr_adapter_body_never_flips() {
        assert!(
            fnptr_adapter_allows_flip(false),
            "an ordinary body must still flip — otherwise this gate proves nothing"
        );
        assert!(
            !fnptr_adapter_allows_flip(true),
            "a body carrying a function with no rustc counterpart has no built-MIR oracle for \
             that function and must never reach codegen"
        );
    }

    // -----------------------------------------------------------------------------------------
    // Trust (wave-TR provenance ledger): fixtures for the confinement check.
    // -----------------------------------------------------------------------------------------

    const PROBE_CALLEE: FuncId = FuncId::new(1);
    /// The forwarded `&T`: the result of the probe body's call.
    const FORWARDED: ValueId = ValueId::new(7);

    fn probe_callee_ref(func_id: FuncId) -> CalleeRef {
        let def_id = DefId {
            krate: CrateNum::from_u32(0),
            index: DefIndex::from_u32(11),
        };
        let definition = crate::lineage::DefinitionIdentity::test_only(0xC0DE, 11);
        CalleeRef {
            func_id,
            is_local: true,
            def_index: 11,
            def_id,
            definition,
            concrete_key: Some(crate::lineage::ConcreteCalleeKey::test_only(
                definition,
                crate::lineage::ConcreteInstanceKind::Item,
                Vec::new(),
            )),
            instance_args: Some(Vec::new()),
            def_path: "thin_reborrow_probe::callee".to_string(),
            force_havoc: false,
            site_def_id: def_id,
            site_args: Some(Vec::new()),
            ret_ty: None,
            ret_ty_conflict: false,
            abi: crate::calling_convention::FunctionAbi::C,
            // No contributing body withdrew this callee's signature, and none signed
            // it — the producer's own default at `admit_callee`'s push site.
            params: crate::ParamSignature::Unsigned,
        }
    }

    /// A per-body mini-module whose single function's entry block runs `body`, the caller's own
    /// instruction list. Every fixture below differs from the accept in exactly one way, so what
    /// the check is reacting to is never in doubt.
    fn reborrow_probe_module(body: Vec<InstrNode>) -> Module {
        let mut module = Module::new("thin_reborrow_probe");
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function =
            Function::new(FuncId::new(0), "thin_reborrow_probe_body", ty, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.body = body;
        function.blocks.push(entry);
        module.try_add_function(function).expect("Module::try_add_function: test fixture");
        module
    }

    /// `results: [FORWARDED]` on a direct `Call` to the ledgered callee — the ACCEPT shape, and
    /// exactly what `&*<LevelArc as Deref>::deref(..)` emits.
    fn call_defining_forwarded() -> InstrNode {
        let mut node = InstrNode::new(Inst::Call { callee: PROBE_CALLEE, args: Vec::new() });
        node.results = vec![FORWARDED];
        node
    }

    fn call_result_row() -> ThinReborrow {
        ThinReborrow { value: FORWARDED, provenance: ThinReborrowProvenance::CallResult }
    }

    /// Trust (wave-TR provenance ledger) **THE ACCEPT, STATED FIRST.** A gate that refuses
    /// everything proves nothing, so the live admission is asserted before any refusal below.
    ///
    /// This is `chain_callresult` / `Level::is_zero` in miniature: a `&T` forwarded with no ledger
    /// entry, whose defining instruction is a direct call to a callee this body declared.
    #[test]
    fn test_a_confined_call_result_reborrow_is_certified_and_flips() {
        let module = reborrow_probe_module(vec![call_defining_forwarded()]);
        let callees = [probe_callee_ref(PROBE_CALLEE)];
        assert!(
            call_result_reborrow_is_confined(&module, &callees, FORWARDED),
            "a value minted by a direct call to a LEDGERED callee, defined exactly once and never \
             a block parameter, is the one provenance this gate can account for — if this refuses, \
             the whole wave is vacuous"
        );
        assert!(
            thin_reborrows_allow_flip(&module, &callees, &[call_result_row()]),
            "and the lane predicate must carry that certificate through"
        );
    }

    /// Trust (wave-TR provenance ledger) **THE REFUSALS THE WAVE DOES NOT TOUCH — one fixture per
    /// class.** A check that admits everything is not a check.
    ///
    /// Each row below is otherwise IDENTICAL to the accept above — same module, same callee
    /// ledger, same `ValueId`, and a module that WOULD certify the value if it were claimed as a
    /// call result. Only the producer's provenance class differs, so the refusal can only be
    /// coming from the class.
    #[test]
    fn test_every_other_provenance_class_is_still_refused() {
        let module = reborrow_probe_module(vec![call_defining_forwarded()]);
        let callees = [probe_callee_ref(PROBE_CALLEE)];
        for provenance in [
            ThinReborrowProvenance::Binding,
            ThinReborrowProvenance::Projection,
            ThinReborrowProvenance::Other,
        ] {
            assert!(
                !thin_reborrows_allow_flip(
                    &module,
                    &callees,
                    &[ThinReborrow { value: FORWARDED, provenance }]
                ),
                "provenance class `{provenance:?}` names a value no instruction in this body \
                 mints, so there is nothing to certify and the original refusal must stand — even \
                 when the module would have borne out a `CallResult` claim for the same value"
            );
        }
    }

    /// Trust (wave-TR provenance ledger) **ONE UNCERTIFIABLE ROW POISONS THE BODY.** The gate is a
    /// universal over rows, not an existential: a body that forwards one certifiable call result
    /// and one binding read must not flip on the strength of the good row.
    #[test]
    fn test_a_single_uncertifiable_row_refuses_the_whole_body() {
        let module = reborrow_probe_module(vec![call_defining_forwarded()]);
        let callees = [probe_callee_ref(PROBE_CALLEE)];
        assert!(
            !thin_reborrows_allow_flip(
                &module,
                &callees,
                &[
                    call_result_row(),
                    ThinReborrow { value: FORWARDED, provenance: ThinReborrowProvenance::Binding },
                ]
            ),
            "every forwarded row must be certified; a body is only as accountable as its least \
             accountable reborrow"
        );
    }

    /// Trust (wave-TR provenance ledger) **THE NON-VACUITY PROOF: the check disagrees with the
    /// tag.** This is what separates a confinement check from a rename.
    ///
    /// Every case carries the class tag `CallResult` — the producer's claim — and every case is
    /// refused BY THE MODULE, because the module does not bear the claim out. If someone replaced
    /// [`call_result_reborrow_is_confined`] with `true`, every assertion here goes red.
    #[test]
    fn test_a_call_result_row_the_module_does_not_bear_out_is_refused() {
        let ledgered = [probe_callee_ref(PROBE_CALLEE)];

        // (a) NO DEFINITION. The arm forwarded a value the module never defines.
        assert!(
            !call_result_reborrow_is_confined(
                &reborrow_probe_module(Vec::new()),
                &ledgered,
                FORWARDED
            ),
            "a value with no defining instruction is a dangling id, not a call result"
        );

        // (b) TWO DEFINITIONS. Not SSA at this value; `to_mir` would have no single local.
        assert!(
            !call_result_reborrow_is_confined(
                &reborrow_probe_module(vec![call_defining_forwarded(), call_defining_forwarded()]),
                &ledgered,
                FORWARDED
            ),
            "two defining instructions mean the pointer's origin is ambiguous"
        );

        // (c) NOT A CALL. A `CallResult` claim over an instruction that is not a call.
        let mut not_a_call = InstrNode::new(Inst::Alloca { ty: Ty::I64, count: None, align: None });
        not_a_call.results = vec![FORWARDED];
        assert!(
            !call_result_reborrow_is_confined(
                &reborrow_probe_module(vec![not_a_call]),
                &ledgered,
                FORWARDED
            ),
            "the class tag is the producer's CLAIM; the instruction is the evidence, and here they \
             disagree"
        );

        // (d) AN INDIRECT CALL. No statically-known callee, so the record would name nothing.
        let mut indirect = InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(1),
            sig: trust_ir::FuncTyId::new(0),
            args: Vec::new(),
            calling_conv: trust_ir::CallingConv::C,
        });
        indirect.results = vec![FORWARDED];
        assert!(
            !call_result_reborrow_is_confined(
                &reborrow_probe_module(vec![indirect]),
                &ledgered,
                FORWARDED
            ),
            "an indirect call has no callee identity to hand the flip"
        );

        // (e) AN UNLEDGERED CALLEE. The call is direct, but this body never declared that callee,
        //     so `crate_module` cannot resolve or havoc it and the identity is unaccounted for.
        assert!(
            !call_result_reborrow_is_confined(
                &reborrow_probe_module(vec![call_defining_forwarded()]),
                &[probe_callee_ref(FuncId::new(2))],
                FORWARDED
            ),
            "a callee outside the identity ledger is exactly the case `crate_module` fails closed \
             on; the flip must not be more permissive than crate assembly"
        );

        // (i) AN AMBIGUOUS CALLEE: TWO LEDGER IDENTITIES BEHIND ONE `FuncId`. The call is direct
        //     and the `FuncId` IS in the ledger — but it names two different callees, so WHICH
        //     one minted the pointer is a guess. The dense producer allocator cannot create this
        //     set, but the consumer accepts public `CalleeRef` slices and therefore defends
        //     against a malformed/replayed ledger. Both peer consumers refuse the same set by
        //     name — `to_mir`'s Call arm ("Call(ambiguous callee FuncId: non-singleton ledger)") and
        //     `crate_module::resolve_callee`'s `_ =>` arm, which declares
        //     `!ambiguous_callee_N` rather than link. An existential over the ledger would answer
        //     "confined" here, which is strictly MORE PERMISSIVE than crate assembly.
        let mut second_identity = probe_callee_ref(PROBE_CALLEE);
        second_identity.def_id =
            DefId { krate: CrateNum::from_u32(1), index: DefIndex::from_u32(11) };
        second_identity.is_local = false;
        second_identity.def_path = "other_crate::callee".to_string();
        assert!(
            !call_result_reborrow_is_confined(
                &reborrow_probe_module(vec![call_defining_forwarded()]),
                &[probe_callee_ref(PROBE_CALLEE), second_identity],
                FORWARDED
            ),
            "two identities behind one FuncId means the callee cannot be NAMED; a confinement \
             certificate over a guessed callee is a record of nothing, and the flip must not be \
             more permissive than crate assembly"
        );

        // (f) A BLOCK PARAMETER. The value arrives along an edge, so its definition is every
        //     predecessor's branch argument — not a site the flip can name.
        let mut with_param = reborrow_probe_module(vec![call_defining_forwarded()]);
        with_param.functions[0].blocks[0].params.push((FORWARDED, Ty::Ptr));
        assert!(
            !call_result_reborrow_is_confined(&with_param, &ledgered, FORWARDED),
            "a block parameter has one id and many origins"
        );

        // (g) ONE LANE OF A MULTI-RESULT CALL. The forwarded pointer would be a projection of the
        //     call's result tuple, which is a different shape from "the call returned this".
        let mut multi = call_defining_forwarded();
        multi.results.push(ValueId::new(8));
        assert!(
            !call_result_reborrow_is_confined(
                &reborrow_probe_module(vec![multi]),
                &ledgered,
                FORWARDED
            ),
            "a multi-result call does not mint the forwarded pointer on its own"
        );

        // (h) NOT A PER-BODY MINI-MODULE. A value id only means something inside one function's
        //     SSA space; scanning several could match a different function's value of that number.
        let mut two_functions = reborrow_probe_module(vec![call_defining_forwarded()]);
        let ty = two_functions.functions[0].ty;
        two_functions
            .try_add_function(Function::new(FuncId::new(3), "second", ty, BlockId::new(0)))
            .expect("Module::try_add_function: test fixture");
        assert!(
            !call_result_reborrow_is_confined(&two_functions, &ledgered, FORWARDED),
            "the confinement check states the single-function obligation itself rather than \
             inheriting it from the lineage digest, which is minted LATER"
        );
    }

    /// Trust (wave-TR provenance ledger): a body that forwarded NOTHING is unaffected. The
    /// pre-ledger predicate was `!thin_reborrow`, so this is the case that must not have moved.
    #[test]
    fn test_a_body_that_forwarded_no_thin_reborrow_is_unchanged() {
        assert!(
            thin_reborrows_allow_flip(&probe_module("no_reborrows"), &[], &[]),
            "an ordinary body must still flip — the gate may only speak about rows that exist"
        );
    }

    /// Declared provenance independently refuses a stale green report without a fake call.
    #[test]
    fn an_unsubstituted_opaque_return_cannot_enter_the_flip_registry() {
        let mut lowered = lane_probe_lowered();
        assert!(body_lane_gates_allow_flip(&lowered).is_some());
        lowered.unsubstituted_opaque_return = true;
        assert!(!lowered.symbolic);
        assert!(!lowered.contains_call);
        assert!(body_lane_gates_allow_flip(&lowered).is_none());
    }

    /// A `Lowered` in the posture a body reaches `record_green` in: CLEAN, no pending consts, and
    /// every lane flag clear. The four lane flags are the ONLY thing the callers below vary.
    fn lane_probe_lowered() -> Lowered {
        Lowered {
            coroutine_frame_ptr: false,
            global_origins: Vec::new(),
            mut_reborrows: Vec::new(),
            module: probe_module("lane_gate_probe"),
            // Synthetic probe; see the note in `Lowered::enum_fold_switch_blocks`. Empty
            // keeps this helper at the CLEAN posture its doc comment promises.
            enum_fold_switch_blocks: std::collections::HashSet::new(),
            body_kind: crate::BodyKind::Fn,
            opaque_collapse: false,
            enum_declines: Vec::new(),
            union_lane: false,
            layout_withheld_structs: Vec::new(),
            enum_param_lane: false,
            symbolic: false,
            unsubstituted_opaque_return: false,
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

    /// **THE WIRING PIN.** Every per-body lane gate must actually be READ by the flip decision.
    ///
    /// This test exists because of a measured hole, not a hypothetical one. While the four gates
    /// were spelled as consecutive `if … { return; }` blocks inside `record_green` — a
    /// `TyCtxt`-taking function no unit test can call — DELETING one of them left the entire suite
    /// green (262/262, wave-TR mutation C). Each lane's own `*_allows_flip` test still passed,
    /// because those test the PREDICATE and the predicate was still correct; what had gone missing
    /// was the wire. `body_lane_gates_allow_flip` moves that wire into a pure function, and this
    /// test drives it with a real `Lowered`: set exactly one lane flag, and the flip must be
    /// refused. Drop any lane from the conjunction and the corresponding case goes red.
    ///
    /// ONE OF THREE HALVES — this one owns WHICH FIELDS. Whether `record_green` READS the
    /// aggregate at all stopped being a test's business: the function returns a
    /// [`super::LaneGatesPassed`] that only its own `Some` arm can mint and that `green_body`
    /// demands by value, so a `record_green` which skips it does not compile. Whether the read
    /// was for the body being recorded is `green_body`'s own address check, pinned by
    /// `test_a_lane_gate_token_cannot_license_a_different_body`. What neither rustc nor that
    /// check can see is which FIELDS of `Lowered` the conjunction consults — so that is pinned
    /// here, by fixture, one lane at a time.
    ///
    /// The all-clear case is asserted first: a gate list that refuses everything would satisfy the
    /// four refusals vacuously.
    #[test]
    fn test_every_body_lane_gate_is_wired_into_the_flip_decision() {
        assert!(
            body_lane_gates_allow_flip(&lane_probe_lowered()).is_some(),
            "a body with every lane flag clear must still be allowed to flip — otherwise the four \
             refusals below are vacuous"
        );
        let lanes: [(&str, fn(&mut Lowered)); 4] = [
            ("union_lane", |l| l.union_lane = true),
            ("enum_param_lane", |l| l.enum_param_lane = true),
            ("fnptr_adapter", |l| l.fnptr_adapter = true),
            // Trust (wave-TR provenance ledger): the lane's refusing posture, expressed as a row
            // the probe module cannot possibly certify (the probe body has no instructions at
            // all). This keeps the WIRING question — "does the aggregate read this lane?" —
            // separate from the CERTIFICATION question, which the fixtures above own.
            ("thin_reborrows", |l| {
                l.thin_reborrows.push(ThinReborrow {
                    value: ValueId::new(0),
                    provenance: ThinReborrowProvenance::CallResult,
                })
            }),
        ];
        for (name, set) in lanes {
            let mut probe = lane_probe_lowered();
            set(&mut probe);
            assert!(
                body_lane_gates_allow_flip(&probe).is_none(),
                "lane `{name}` is declared to refuse the flip but is NOT WIRED INTO the decision — \
                 its predicate being correct proves nothing if nothing calls it"
            );
        }
    }

    /// Trust (L1): the record→take round-trip carries the lineage digest — the flip
    /// consumes exactly the digest minted at record time, never a recomputation of a
    /// possibly-different object.
    #[test]
    fn test_flip_registry_round_trip_carries_lineage_digest() {
        let mut reg = SessionFlipRegistry::default();
        let entry = green_probe("probe");
        let minted = entry.lineage;
        reg.insert_green(7, entry);

        let taken = reg.take_green(7).expect("recorded green body must be takeable once");
        assert_eq!(taken.lineage, minted, "take must yield the digest minted at record time");
        assert_eq!(
            taken.lineage,
            body_lineage_digest(probe_definition(3), &taken.module, &taken.callees)
                .expect("taken module must still digest"),
            "the carried digest must still describe the carried (module, ledger)"
        );
        assert!(reg.take_green(7).is_none(), "a second take must be inert (memory bound)");
    }

    /// Trust (L1): the poison invariant survives the GreenBody refactor — a double
    /// record drops the entry, digest and all; nothing digest-bearing escapes.
    #[test]
    fn test_flip_registry_double_record_poisons_and_yields_nothing() {
        let mut reg = SessionFlipRegistry::default();
        reg.insert_green(7, green_probe("first"));
        reg.insert_green(7, green_probe("second"));
        assert!(
            reg.take_green(7).is_none(),
            "a def_index recorded twice is poisoned: no module (and no digest) may be trusted"
        );
    }

    /// The measured scope of "compiled from trust-ir", pinned so it cannot be
    /// widened by editing one comparison. Measured 2026-07-25 on a five-body
    /// scalar probe against stage2 `d8a9eb292`: 5 flips at `-C debuginfo=0` and
    /// with no `-C debuginfo` flag at all, 0 at `-C debuginfo=1` and `=2`. targo
    /// emits `-C debuginfo=2` for the `dev` profile and no flag at all for
    /// `release`, so this predicate is the whole reason the default verified
    /// build flips nothing.
    #[test]
    fn only_debuginfo_free_sessions_flip() {
        assert!(
            session_gates_allow_flip(true, true, DebugInfo::None, false),
            "a debuginfo-free, coverage-free session with both flags on must flip"
        );
        for level in [
            DebugInfo::LineDirectivesOnly,
            DebugInfo::LineTablesOnly,
            DebugInfo::Limited,
            DebugInfo::Full,
        ] {
            assert!(
                !session_gates_allow_flip(true, true, level, false),
                "{level:?} asks for line tables or locals the shim cannot reconstruct; \
                 admitting it would emit a body that describes itself wrongly"
            );
        }
    }

    #[test]
    fn every_other_session_gate_is_independently_sufficient_to_decline() {
        assert!(
            !session_gates_allow_flip(false, true, DebugInfo::None, false),
            "the flip is part of the trust-ir lane; without the lowering there is no Module"
        );
        assert!(
            !session_gates_allow_flip(true, false, DebugInfo::None, false),
            "-Ztrust-ir-flip=no is the byte-compare negative control and must disable the lane"
        );
        assert!(
            !session_gates_allow_flip(true, true, DebugInfo::None, true),
            "coverage mappings are span-derived; the shim's dummy spans would corrupt them"
        );
    }

    /// Trust (union lane) FLIP REFUSAL, PINNED. A body carrying a union PLACEHOLDER lane is
    /// permanently flip-ineligible. This is not defensive: the class contains `<Sha256 as
    /// Clone>::clone`, which is `BodyKind::Fn` (admitted by the body-kind gate), fully concrete
    /// (past the layout pre-gate), and returns the union-bearing struct BY VALUE. `to_mir`'s
    /// return gate accepts any concrete `ty::Adt(struct)` with `!needs_drop` and never compares
    /// the trust-ir `StructDef`'s field list against the built type, so it would wave through a
    /// copy that silently drops the union's contents.
    #[test]
    fn union_placeholder_lane_permanently_blocks_the_flip() {
        assert!(
            union_lane_allows_flip(false),
            "a body with no union lane must stay eligible — the gate is not vacuous"
        );
        assert!(
            !union_lane_allows_flip(true),
            "a union placeholder lane must block the flip: codegen would copy the struct by \
             value and drop the union's bytes"
        );
    }

    /// Trust (enum param lane) FLIP REFUSAL, PINNED, AND OWNED — not inherited.
    ///
    /// `to_mir`'s param and return gates both require `!built.has_non_region_param()`, which a
    /// param-lane enum's rustc type fails BY CONSTRUCTION, so no body in the class reaches
    /// `record_green` today. That is somebody else's ground truth about GENERICS, not a decision
    /// about placeholder lanes: it evaporates the moment a monomorphized instantiation carrying
    /// such a def reaches the seam. The refusal is stated here so that relaxation must be
    /// deliberate.
    ///
    /// The negative half keeps the gate non-vacuous.
    #[test]
    fn enum_param_placeholder_lane_permanently_blocks_the_flip() {
        assert!(
            enum_param_lane_allows_flip(false),
            "a body with no enum param lane must stay eligible — the gate is not vacuous"
        );
        assert!(
            !enum_param_lane_allows_flip(true),
            "an enum param placeholder lane must block the flip: codegen would copy the enum by \
             value with a lane sized at zero bytes and drop the caller's `T`"
        );
    }
}
