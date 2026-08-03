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
//! * no first-class `invariant`/`decreases` loop clauses. Their source names
//!   currently bind through MIR debug-place provenance, while the direct
//!   TrustIr module carries neither source-place identity nor `var_debug_info`.
//!   Flipping such a body would preserve execution but erase the verifier's
//!   only exact binder. The body stays on built MIR until that provenance rides
//!   TrustIr; ordinary contract-free bodies remain eligible.
//! * `-C debuginfo=0` only: the shim does not yet thread per-statement spans or
//!   `var_debug_info`, so flipping under debuginfo would silently degrade debug info.
//!   Fail-closed until spans ride trust-ir (P1.5). (Assert PANIC-LOCATION spans are already
//!   exact — [`crate::flip`] stitches them from the borrow-checked sibling.)
//! * no `-C instrument-coverage`: coverage mappings are span-derived; dummy spans would
//!   corrupt them.
//!
//! # Per-BODY marker gate (slice 3 — replaces the old `-O0`-only session gate)
//!
//! The shim emits no `StorageLive`/`StorageDead` (reconstruction from the Module alone is
//! provably impossible — `to_mir` module docs), so under `-O` a flipped body could lack the
//! LLVM lifetime hints the built body carries. Instead of gating the whole session to `-O0`,
//! [`record_green`] takes the derived-MIR differential's EXACT marker-channel verdict
//! (`DerivedReport::markers_exact`) and records a body at `-O` only when the marker
//! sequences were proven line-identical (today: the built body's reachable subgraph is
//! marker-free — unit fns, const-returning closures, param-identity bodies). When
//! `!sess.emit_lifetime_markers()` (`-O0`, no sanitizers) marker divergence is
//! codegen-immaterial — `RemoveStorageMarkers` (enabled exactly then, `mir_opt_level > 0`)
//! deletes markers+Nops from every body before codegen and codegen only emits
//! `llvm.lifetime` intrinsics under `emit_lifetime_markers()` — so `markers_exact` is not
//! required. The flip therefore flips what it can PROVE at each opt level, per body.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: Apache-2.0

use std::collections::HashMap;

use rustc_middle::ty::TyCtxt;
use rustc_session::config::DebugInfo;
use rustc_span::def_id::LocalDefId;
use trust_ir::{Module, ProofDigest};

use crate::{CalleeRef, Lowered};

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
fn green_body(module: &Module, callees: &[CalleeRef]) -> Option<GreenBody> {
    let lineage = crate::lineage::body_lineage_digest(module, callees).ok()?;
    Some(GreenBody { module: module.clone(), callees: callees.to_vec(), lineage })
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
/// The shim reconstructs MIR from the Module alone and the Module carries no
/// spans or `var_debug_info`, so a flipped body would silently lose the
/// line tables and local names the built body carries. That is not a
/// correctness question — it is a debugger-visible regression the flip has no
/// way to repair, so the session declines rather than emit a body it cannot
/// describe.
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
/// trade real evidence for a bigger number; the way to widen this is to thread
/// spans and `var_debug_info` through the Module so a flipped body can carry
/// what it replaced.
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

fn loop_contract_count_allows_flip(first_class_loop_contracts: usize) -> bool {
    first_class_loop_contracts == 0
}

/// Trust (union lane): may a body that registered `union_lane` union PLACEHOLDER lanes flip?
///
/// Never. Extracted as a `TyCtxt`-free predicate for the same reason
/// [`loop_contract_count_allows_flip`] is: the refusal is then pinned by a unit test instead of
/// living only inside a function no test can call.
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

/// Trust (wave-TR): may a body that FORWARDED an unledgered THIN SHARED REBORROW flip?
///
/// Never, for now. The wave-TR arm returns a `&T` VALUE that this lowering did not produce and
/// that is in no pointer ledger (`borrow_ptrs` / `ref_param_ptrs` / `global_ptrs` /
/// `interior_ptrs`) — a call result, a by-ref match binding, a ref-typed local. That posture is
/// right for the PRODUCER (the value already flowed unguarded before the reborrow existed; see
/// `Lowered::thin_reborrow`), but it means the producer holds no record it could hand the flip
/// about where the pointer came from. Codegen is the one seam where that matters, so it refuses.
///
/// STATED AS ITS OWN PREDICATE rather than left to the wall that also refuses the class today.
/// `to_mir` rejects the DOMINANT provenance — a `&T`-returning callee is outside its call fragment
/// ("Call(callee return outside the fragment: …)"), because `ir_scalar_of_body` is `None` for a
/// reference and the fallback arm demands a `Copy`, `!needs_drop` `ty::Adt(struct)`. That is a real
/// wall and it is NOT ABOUT THIS LANE: it is a call RETURN-FIDELITY rule, it would evaporate the
/// moment someone widened the return fragment for an unrelated reason, and it says nothing at all
/// about the other provenances (a by-ref match binding reaches its value through `ExtractField`,
/// under entirely separate gates). Relying on it would be relying on unreachability — the exact
/// mistake [`union_lane_allows_flip`] and [`fnptr_adapter_allows_flip`] exist to avoid. Extracted
/// `TyCtxt`-free for the same reason they are: the refusal is then pinned by a unit test instead of
/// living only inside a function no test can call.
fn thin_reborrow_allows_flip(thin_reborrow: bool) -> bool {
    !thin_reborrow
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
/// Order is irrelevant — every conjunct is a pure `!flag` on an independent field — so this is a
/// conjunction, not a sequence, and nothing here may acquire a side effect.
fn body_lane_gates_allow_flip(lowered: &Lowered) -> bool {
    // Trust (union lane): a body whose module registered a UNION PLACEHOLDER LANE never flips.
    // The lane spells `Ty::Unit` for a struct field that holds real `union` bytes, and `to_mir`'s
    // param/return gates cannot catch it: both admit any concrete `ty::Adt(struct)` with
    // `!needs_drop` and never compare the trust-ir `StructDef`'s field list against the built
    // type. `<Sha256 as Clone>::clone` — which returns `Sha256` BY VALUE over exactly such a
    // struct — is `BodyKind::Fn`, i.e. admitted by the body-kind gate in `record_green`, and fully
    // concrete, i.e. past the layout pre-gate. Flipping it would emit a copy that silently drops
    // the union's contents. Load-bearing, not defensive, and keyed on the producer's ledger
    // (`Lowered::union_lane`), never on the `()` spelling.
    union_lane_allows_flip(lowered.union_lane)
        // Trust (enum param lane): a body whose module registered an ENUM PARAM PLACEHOLDER LANE
        // never flips — see `enum_param_lane_allows_flip`. Load-bearing as a DECISION, not as a
        // consequence of `to_mir`'s generic-param gates happening to refuse the class today.
        && enum_param_lane_allows_flip(lowered.enum_param_lane)
        // Trust (fn-ptr adapter lane): a body whose module carries a producer-synthesized adapter
        // never flips — see `fnptr_adapter_allows_flip`. Load-bearing as a DECISION, not as a
        // consequence of the lineage digest's arity rule.
        && fnptr_adapter_allows_flip(lowered.fnptr_adapter)
        // Trust (wave-TR): a body that forwarded an unledgered thin shared reborrow never flips —
        // see `thin_reborrow_allows_flip`. Load-bearing as a DECISION, not as a consequence of
        // `to_mir`'s call-return-fidelity gate happening to refuse the dominant provenance today.
        && thin_reborrow_allows_flip(lowered.thin_reborrow)
}

/// Whether this definition has enough source-place provenance for the current
/// TrustIr -> MIR flip. Native loop clauses are parser-island expressions whose
/// identifiers are rebound to MIR places during E4/E5 reconstruction. The
/// direct module does not carry that binding yet, so only a definition with no
/// first-class loop clauses may enter the flip registry.
pub fn source_place_provenance_allows_flip(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    let first_class_loop_contracts = tcx
        .hir_maybe_body_owned_by(def)
        .and_then(|body| body.contract)
        .map_or(0, |contract| contract.loop_clauses.len());
    loop_contract_count_allows_flip(first_class_loop_contracts)
}

/// Trust: called from the `mir_built` hook for bodies whose derived-MIR differential verdict is
/// `DerivedAgreed` (the caller checks the verdict; `unsupported` is re-checked here defensively).
/// `markers_exact` is the differential's EXACT marker-channel verdict for THIS body; when the
/// session emits lifetime markers (`-O` / sanitizers) it is required (see module docs).
/// No-op unless every gate holds — the registry stays empty when the flip cannot fire.
pub fn record_green(tcx: TyCtxt<'_>, def: LocalDefId, lowered: &Lowered, markers_exact: bool) {
    if !flip_session_enabled(tcx) {
        return;
    }
    if !source_place_provenance_allows_flip(tcx, def) {
        return;
    }
    // Trust: per-body marker gate (module docs). Fail-closed: an unproven marker sequence
    // must never reach codegen where markers are material.
    if tcx.sess.emit_lifetime_markers() && !markers_exact {
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
    // TWO tests, and both are needed — the aggregation moves the hole, it does not close it.
    // `test_every_body_lane_gate_is_wired_into_the_flip_decision` executes the aggregate against a
    // real `Lowered` fixture and goes red if any lane leaves THE FUNCTION. It says nothing about
    // THIS LINE: delete the `if` below and that test stays green, which is mutation C one level up.
    // `test_the_lane_gate_aggregate_is_read_by_record_green` pins this call site by source text —
    // that the aggregate is read here, exactly once, as a REFUSAL (`if !… { return; }`).
    // Neither test may be dropped because the other exists.
    if !body_lane_gates_allow_flip(lowered) {
        return;
    }
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
    let Some(entry) = green_body(&lowered.module, &lowered.callees) else {
        return;
    };
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
    use trust_ir::{BlockId, FuncId, FuncTy, Function, Module};

    use super::{
        GreenBody, Lowered, SessionFlipRegistry, body_lane_gates_allow_flip,
        enum_param_lane_allows_flip, fnptr_adapter_allows_flip, green_body,
        loop_contract_count_allows_flip, session_gates_allow_flip, thin_reborrow_allows_flip,
        union_lane_allows_flip,
    };
    use crate::lineage::body_lineage_digest;

    fn probe_module(fn_name: &str) -> Module {
        let mut module = Module::new("flip_registry_probe");
        let ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(Function::new(FuncId::new(0), fn_name, ty, BlockId::new(0)));
        module
    }

    /// Built through the production constructor, never by hand — a test that
    /// assembled a `GreenBody` field-by-field could not witness the fail-closed rule.
    fn green_probe(fn_name: &str) -> GreenBody {
        green_body(&probe_module(fn_name), &[])
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
            green_body(&Module::new("no_bodies"), &[]).is_none(),
            "a body-less mini-module must not become a green entry: the flip event could \
             not name, by digest, which body it selected"
        );
        let mut two = probe_module("probe");
        let ty = two.functions[0].ty;
        two.add_function(Function::new(
            FuncId::new(crate::ADAPTER_FUNC_ID_BASE),
            "probe::{fnptr-adapter}",
            ty,
            BlockId::new(0),
        ));
        assert!(
            green_body(&two, &[]).is_none(),
            "a mini-module carrying a producer-synthesized adapter names two program objects; \
             it must not become a green entry"
        );
        assert!(
            green_body(&probe_module("probe"), &[]).is_some(),
            "the ordinary single-function case must still be admitted (the gate is not vacuous)"
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

    /// Trust (wave-TR) FLIP REFUSAL, PINNED AS A DECISION. A body that forwarded an unledgered
    /// thin shared reborrow (`&*r` where `r` is a call result / by-ref match binding / ref-typed
    /// local) never flips.
    ///
    /// The point of testing the PREDICATE rather than the pipeline: a wall also stops the dominant
    /// provenance today — `to_mir` puts a `&T`-returning callee outside its call fragment. That is
    /// a call RETURN-FIDELITY rule, not a decision about reborrow provenance, and it covers none of
    /// the other provenances. A future wave that widens the return fragment must still meet this
    /// line.
    #[test]
    fn test_thin_reborrow_body_never_flips() {
        assert!(
            thin_reborrow_allows_flip(false),
            "an ordinary body must still flip — otherwise this gate proves nothing"
        );
        assert!(
            !thin_reborrow_allows_flip(true),
            "a body forwarding a reference value the producer's ledgers do not record must never \
             reach codegen on that value"
        );
    }

    /// A `Lowered` in the posture a body reaches `record_green` in: CLEAN, no pending consts, and
    /// every lane flag clear. The four lane flags are the ONLY thing the callers below vary.
    fn lane_probe_lowered() -> Lowered {
        Lowered {
            module: probe_module("lane_gate_probe"),
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
            thin_reborrow: false,
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
    /// The all-clear case is asserted first: a gate list that refuses everything would satisfy the
    /// four refusals vacuously.
    #[test]
    fn test_every_body_lane_gate_is_wired_into_the_flip_decision() {
        assert!(
            body_lane_gates_allow_flip(&lane_probe_lowered()),
            "a body with every lane flag clear must still be allowed to flip — otherwise the four \
             refusals below are vacuous"
        );
        let lanes: [(&str, fn(&mut Lowered)); 4] = [
            ("union_lane", |l| l.union_lane = true),
            ("enum_param_lane", |l| l.enum_param_lane = true),
            ("fnptr_adapter", |l| l.fnptr_adapter = true),
            ("thin_reborrow", |l| l.thin_reborrow = true),
        ];
        for (name, set) in lanes {
            let mut probe = lane_probe_lowered();
            set(&mut probe);
            assert!(
                !body_lane_gates_allow_flip(&probe),
                "lane `{name}` is declared to refuse the flip but is NOT WIRED INTO the decision — \
                 its predicate being correct proves nothing if nothing calls it"
            );
        }
    }

    /// **THE WIRE ABOVE THE WIRE.** The test above proves each lane is read by
    /// `body_lane_gates_allow_flip`. It proves NOTHING about whether `record_green` reads that
    /// aggregate: `record_green` takes a `TyCtxt`, no unit test can call it, and deleting its
    /// one-line refusal gate leaves the whole suite green. That is wave-TR mutation C displaced
    /// one level up, and an adversarial review caught the refactor claiming to have fixed the hole
    /// when it had only moved it.
    ///
    /// So the call site is pinned by SOURCE TEXT, in the `lib.rs` wave-DP idiom (see
    /// `the_projected_pointee_lane_is_actually_wired`). Crude, and the honest tool for a property
    /// about the shape of a call inside a function no test can reach. This test goes RED if the
    /// gate is deleted, duplicated, evaluated without acting on the result, or turned into
    /// anything other than a refusal.
    #[test]
    fn test_the_lane_gate_aggregate_is_read_by_record_green() {
        // Needles are ASSEMBLED at run time: this test's own source is inside
        // `include_str!("flip_registry.rs")`, so a literal needle would match itself and the guard
        // would pass with the production call site deleted.
        let producer = include_str!("flip_registry.rs");

        // Read as a REFUSAL — `!aggregate(...)`. Exactly two occurrences in the file: this one's
        // `record_green` gate, and the fixture-driven wiring test above. A third means some other
        // caller now decides the same question; a first-and-only means the production gate is gone.
        let refusal = format!("!{}(", "body_lane_gates_allow_flip");
        assert_eq!(
            producer.matches(refusal.as_str()).count(),
            2,
            "the lane aggregate must be READ as a refusal in exactly two places — the \
             `record_green` gate and the wiring test — and this count is what makes deleting the \
             gate visible at all",
        );

        // …and one of those two must be INSIDE `record_green`.
        let fn_at = producer
            .find(&format!("pub fn {}(", "record_green"))
            .expect("`record_green` must exist");
        let fn_end = fn_at
            + producer[fn_at..]
                .find("\npub fn ")
                .expect("`record_green` must be followed by another item");
        let body = &producer[fn_at..fn_end];
        assert_eq!(
            body.matches(refusal.as_str()).count(),
            1,
            "`record_green` must read the lane aggregate — a gate nothing calls is not a gate, \
             and this is the exact hole (mutation C) this branch has now paid for twice",
        );

        // And it must REFUSE on it, not merely evaluate it: `if !… { return; }`.
        let at = body.find(refusal.as_str()).expect("the gate is inside `record_green`");
        assert!(
            body[..at].ends_with("if "),
            "the aggregate must be the CONDITION of an `if !…`, not a bound value some later line \
             may or may not consult",
        );
        let tail = &body[at..];
        let open = tail.find('{').expect("the gate must open a block");
        let close = tail.find('}').expect("the gate must close it");
        assert!(open < close, "the gate's block must be well-formed");
        assert!(
            tail[open..close].contains(&format!("{};", "return")),
            "the gate's block must RETURN — refusing the flip. Any other body (a log, a counter) \
             would let a lane-carrying body reach the registry",
        );
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
            body_lineage_digest(&taken.module, &taken.callees)
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

    #[test]
    fn first_class_loop_clauses_are_the_only_source_provenance_gate() {
        assert!(
            loop_contract_count_allows_flip(0),
            "an ordinary function must remain eligible at the source-provenance gate"
        );
        assert!(!loop_contract_count_allows_flip(1), "one native loop clause must block the flip");
        assert!(
            !loop_contract_count_allows_flip(2),
            "an invariant/decreases pair must block the flip as one provenance-sensitive lane"
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
