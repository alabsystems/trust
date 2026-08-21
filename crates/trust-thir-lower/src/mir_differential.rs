//! The derived-vs-built MIR differential (P1.2 slices 1+2): `derived-MIR ≡ built-MIR`.
//!
//! For a body the producer lowered cleanly, `crate::to_mir::lower_ir_to_mir` reconstructs a
//! `mir::Body` from the `trust_ir::Module`, and this module compares it against the THIR-built
//! MIR the `mir_built` query just produced. Log-only, fail-closed, no behavior change.
//!
//! WHY this gate exists: the interpreter differential (`crate::differential`) is blinded on
//! arithmetic/control-flow bodies by the MIR oracle's eagerly-trapping `Inst::Undef` seed
//! (`CheckedBinaryOp` tuples), which forces `NotRun`. This differential is *structural over
//! symbolic semantics* — it needs no interpretation, so it reaches a real verdict on exactly
//! those bodies, and is the future green gate for the per-function `trust-ir -> MIR -> LLVM`
//! fallback lane.
//!
//! HOW the comparison works (every normalization justified; see the NORMALIZATION LEDGER
//! below for the complete enumerated list + firing counters + retirement paths):
//!   1. Both bodies (freshly built + derived, both `MirPhase::Built`, same `DefId`) are run
//!      through `trust_mir_extract::extract_function` — the built snapshot is shared with the
//!      interpreter differential's identical oracle extraction, while the derived body is
//!      extracted here — yielding two `trust_types::VerifiableBody`s.
//!   2. Each is CANONICALIZED into a symbolic form (`canonicalize`):
//!      * Non-value statements are dropped: `StorageLive`/`StorageDead` (compared EXACTLY by
//!        the separate marker channel, `canon_markers` — LEDGER L2), `Nop` (extract maps
//!        `FakeRead`/`AscribeUserType` to `Nop`), `PlaceMention`. Justified:
//!        `trust_types::Statement::write_effect` classifies all of these `NoValueWrite` —
//!        they change no place value and carry no trap, so dropping them cannot hide a
//!        semantic difference. `Coverage` and `ConstEvalCounter` are FAIL-CLOSED (retired
//!        normalizations): `ConstEvalCounter` is only inserted by the post-built `ctfe_limit`
//!        pass so it can never appear here, and `Coverage` (mir_build's SpanMarker under
//!        `-Cinstrument-coverage`) is refused rather than dropped.
//!      * EVERY `Goto`-terminated block is jump-threaded onto its incoming edges (slice 2:
//!        this generalizes slice 1's statement-EMPTY threading to FORWARDING JOINS — blocks
//!        whose statements are all symbolically-absorbed pure assigns). Each edge through
//!        such a block applies the block's assigns to THAT edge's symbolic state, so the
//!        block's entire effect is captured, path-sensitively, in the phi merge at the join
//!        it forwards to. Justified: after the statement filter a threaded block contains
//!        only pure `Assign`s — and every one of them is STILL evaluated by `rvalue_expr`
//!        per edge, which rejects trapping ops (`Div`/`Rem`) and everything out-of-fragment
//!        REGARDLESS of liveness, so the dead-trapping-op rejection survives threading. A
//!        `Goto` terminator carries no payload, and no decision point is erased: every
//!        switch/assert/return block remains canonical and fully compared. This kills the
//!        producer's nested-if forwarding-join chains (derived `phi[3;phi[2;1]]` vs built
//!        flat `phi[3;2;1]`) and the DFS block-numbering shift they caused (the clamp false
//!        mismatch), symmetrically on both sides.
//!      * Blocks are renumbered by a deterministic DFS preorder from the (threaded) entry
//!        (successor order: switch cases in listed order, then otherwise; assert success
//!        edge), and unreachable blocks are ignored — identical rules on both sides.
//!      * RETURN-SPLIT (wave 3, LEDGER L14): every edge into a `Return`-terminated block is
//!        its own output node — one `return <expr>` observable per path, from that edge's
//!        symbolic state. This canonicalizes the short-circuit-let degenerate-switch family
//!        symmetrically: the builder threads BOTH arms of a `switch` into one shared return
//!        block (`[0->b1,else->b1]` + edge-phi) where the shim emits distinct per-arm
//!        return blocks (`[0->b1,else->b2]`). Justified: `Return` has no successors, so no
//!        decision point is erased; the block's kept statements are pure assigns evaluated
//!        per edge (trapping ops still rejected regardless of liveness); the per-edge
//!        rendering is strictly MORE precise than the phi it replaces — equality still
//!        requires pathwise-equal return values.
//!      * Locals are ELIMINATED entirely by forward symbolic evaluation: every statement in
//!        the fragment is a pure `Assign`, so each block's exit state maps locals to
//!        expressions over `Arg(i)` / constants / ops. Where predecessor edges disagree, a
//!        `phi[...]` expression (incoming exprs in canonical edge order) is formed — a phi's
//!        identity IS its incoming expressions, so no local-numbering alignment is needed.
//!        This also makes copy chains (`_5 = move (_3.0); _0 = copy _5` vs
//!        `_0 = copy (_3.0)`) and DEAD pure assigns vanish symmetrically. Justified: dropped
//!        assigns are pure and trap-free in this fragment (checked arithmetic traps only via its
//!        `Assert` TERMINATOR, which is always compared). Trust (wave-U): a `Div`/`Rem` is now
//!        rendered, but only ever with a LIVE result (the `to_mir` shim fails closed on a
//!        dead-result div/rem via `value_used_in`), so its value is always referenced by an
//!        emitted line and never dropped — the trap-free precondition is never leaned on for it;
//!        its trap is additionally pinned by the mandatory div-by-zero / overflow `Assert`s.
//!      * IN-FRAGMENT BORROWS (slice 2, the memory-promoted-slot class): a built-side
//!        `_r = &mut _x` (or `&_x`) of a BARE local becomes a pure alias binding `_r ↦ _x`;
//!        a deref read `(*_r)` reads `_x`'s current symbolic value, a deref store
//!        `(*_r) = v` writes it. Justified: within the fragment the alias resolves EVERY
//!        observation through `_r` to `_x`'s value at that program point — exactly the
//!        concrete semantics of a private reference — and the binding is UNCONDITIONALLY
//!        fail-closed the moment the reference VALUE itself could escape: any by-value read
//!        of an alias-bound local errors ("used by value"), a borrow of a projected place
//!        errors, nested derefs error, and a merge where the alias target differs (or the
//!        local is a value on one edge and a ref on another) drops the binding so later uses
//!        error. No aliasing effect can hide: the only mutation channel to `_x` besides
//!        direct assignment is a tracked deref-store, which updates `_x` in the same state.
//!        The producer's side of the same class (`Alloca` slots) is lowered by the shim to
//!        PLAIN locals, which this same evaluation absorbs.
//!      * `Copy`/`Move` operands both read the place's current symbolic value. Justified:
//!        for the scalar (`Copy`-type) fragment a `Move` is operationally a read; move-ness
//!        only matters to borrowck/analysis, which never sees the derived body.
//!      * `Rvalue::Cast` is an in-fragment pure assign, rendered exactly as
//!        `cast(<to_ty>,<operand>)` (wave 3: the checked-shift range check's IntToInt
//!        reinterpretation appears on BOTH sides — built by `as_rvalue.rs`, derived by
//!        `to_mir::shift_idiom`). Every cast kind the extraction admits into `Rvalue::Cast`
//!        is non-trapping (saturating float→int included), so L5 dropping a dead one is
//!        trap-safe; the erased cast KIND cannot alias two different casts because equality
//!        also requires the same target type and operand expression.
//!      * `const ()` (`ConstValue::Unit`) is an in-fragment constant (`c:unit`), so unit
//!        returns (`_0 = const (); return` — `Builder::push_assign_unit`) and the builder's
//!        dead unit temps compare symbolically like any other constant.
//!      * Spans and local debug names are never rendered. Justified: source locations and
//!        names carry no semantics.
//!   3. CYCLIC CFGs (slice 2, natural loops): a cyclic body is accepted iff every non-trivial
//!      SCC has a UNIQUE header (the one block with an in-edge from outside that SCC), removing
//!      every SCC-internal edge into its header leaves the whole graph acyclic, and multiple
//!      headers form one strict dominance chain. Thus disjoint SEQUENTIAL loops compose;
//!      nested/overlapping, branch-parallel or order-ambiguous, and irreducible loops fail closed.
//!      A later SCC may be branch-optional when all paths that enter it still pass the earlier
//!      header; its entered and bypass return paths remain separate observables. Each header's
//!      merged locals become symbolic loop variables: candidates (locals defined on every
//!      outside edge) are partitioned by
//!      congruence on `(seed expression, back-edge expression)` — the partition starts from
//!      equal seeds and is refined by re-evaluating the loop body with the current class
//!      names until it stabilizes (monotone refinement, bounded by the candidate count).
//!      Sequential headers are solved in dominance order: the already-solved header environment
//!      is used to evaluate the full prefix into the next header, so loop 1's post-state is the
//!      actual seed of loop 2 rather than an independent summary. Per-header class tokens are
//!      namespaced by canonical header role, and global liveness follows cross-loop references
//!      before pruning.
//!      SOUNDNESS (why this can never equate two loops with different bodies): two locals
//!      share a class only when they have identical seed phis AND identical back-edge
//!      expressions over the class representatives at a stable partition — an inductive
//!      bisimulation (equal at iteration 0; equality at iteration k forces equality at
//!      k+1), so a class denotes ONE well-defined value stream and the congruence never
//!      merges locals whose values could differ. The emitted observables fully pin the
//!      loop's semantics: per-class `loop@bH hN: seed=… back=…` (single loop) or
//!      `loop@bH lHhN: seed=… back=…` (sequential loops) definition lines carry the
//!      per-iteration transition (two loops differing only in an increment constant MISMATCH
//!      on the `back=` payload), and every terminator inside and after the loop — asserts
//!      included — is rendered over the class names. Classes never referenced (transitively)
//!      by any emitted line are pruned: dead, pure, trap-free value streams, the same
//!      justification as dead-assign elimination. Dropped candidates or alias assumptions
//!      only ever FAIL CLOSED (later reads error), never silently agree. Class NAMES are
//!      assigned AFTER pruning, from the surviving classes' content alone (name-erased
//!      signature-chain refinement over their (seed, back) definitions): the fixpoint's raw
//!      ids depend on the pre-pruning candidate set, so a side carrying extra pruned
//!      invariant candidates (the shim's materialized arg local, a const temp) would shift
//!      the surviving ids and falsely mismatch. Renaming is a per-side bijection applied to
//!      every observable; symmetric (automorphic) classes with no canonical order fail
//!      closed. See the L9 naming comments in `eval_loop` and `eval_sequential_loops` for the
//!      full soundness and ordered-composition arguments.
//!   4. What IS compared (the observables): arg count, arg/return types, the CFG skeleton,
//!      every terminator with its full symbolic payload — switch discriminant expression +
//!      case values + targets, assert condition expression + expected + message, DIRECT
//!      CALLS (wave 6: one `call(cs<site>,<callee>,foreign=..)[args..]->b<target>` line per
//!      call site, args rendered symbolically pre-binding; the result is the OPAQUE
//!      site-keyed symbol `cs<site>` — two calls to the same fn with the same args stay
//!      DISTINCT values, and reordered/renamed/arg-swapped call sites mismatch on their
//!      lines), the return value's expression PER INCOMING PATH (return-split) — with every
//!      op carrying its (width-normalized) result type, plus the loop-class definition
//!      lines above. Any construct outside the fragment on EITHER side is a fail-closed
//!      `DerivedUnsupported`, never a silent pass.
//!   4½. RAW CALL CHANNEL (wave 6, `raw_call_channel`): when any `Call` exists, a separate
//!      normalization-free rustc-side walk pins what the extraction ERASES — the interned
//!      `FnDef` callee identity (the def-path STRING channel can collide two DefIds), the
//!      built side's unwind shape (`Cleanup(lone-resume)` / `Continue` only; real cleanup
//!      work, `Terminate`, `Unreachable` fail closed — asserts checked identically). NOT
//!      `call_source` (wave-K): it is a rustc-doc "diagnostics-only" label (codegen-inert), so
//!      pinning it spuriously rejected every overloaded-operator call. Identity divergence is a
//!      `DerivedMismatch`; out-of-fragment shapes are `DerivedUnsupported`. `DerivedAgreed` is
//!      only reported when BOTH channels pass.
//!   5. THE EXACT MARKER CHANNEL (`canon_markers`, slice 3): `StorageLive`/`StorageDead` are
//!      additionally compared EXACTLY — full ordered sequence, positioned by (fine-walk block
//!      index, number of `Assign`s already seen in that block), locals alpha-renamed by first
//!      marker appearance and carrying their declared type. `DerivedReport::markers_exact` is
//!      true iff both sides' marker sequences are line-identical; blocks OUTSIDE the fine
//!      walk (cleanup/dead code) must be marker-free or the channel fails closed. The shim
//!      emits no markers (reconstruction from the Module alone is provably impossible — see
//!      `to_mir` module docs), so today `markers_exact` ⇔ the built body's reachable subgraph
//!      is marker-free; the flip requires `markers_exact` whenever
//!      `sess.emit_lifetime_markers()` (i.e. at `-O`), and at `-O0` marker divergence is
//!      codegen-immaterial: `RemoveStorageMarkers` (enabled iff `mir_opt_level > 0 &&
//!      !emit_lifetime_markers`) deletes markers+Nops from every body before codegen, and
//!      codegen only emits `llvm.lifetime` intrinsics under `emit_lifetime_markers()`.
//!
//! # NORMALIZATION LEDGER (the zero-normalizations ratchet)
//!
//! Every normalization this comparator performs, with soundness + the full-fidelity threading
//! that would retire it. Firing counters (`DerivedReport::norms`, cumulative per crate session over
//! BOTH sides of every comparison) are logged per body by the `mir_built` hook; the
//! normalization-counter probe measures which entries actually fire on a corpus.
//!
//! | # | name (counter) | what fires | why sound | retirement path |
//! |---|----------------|------------|-----------|-----------------|
//! | L1 | `nonvalue-stmt-drop` | a `Nop` (`FakeRead`/`AscribeUserType`) or `PlaceMention` dropped | `NoValueWrite`: no place value changes, no trap; `CleanupPostBorrowck` deletes them before runtime on both paths and codegen emits nothing for them | shim emits `FakeRead`-shaped Nops at the built positions (needs THIR `let`-structure the producer currently erases) |
//! | L2 | `storage-marker-drop` | a `StorageLive`/`StorageDead` dropped from the SEMANTIC channel | markers change no value and cannot trap; they are compared EXACTLY by the marker channel (step 5), whose verdict gates the `-O` flip; at `-O0` `RemoveStorageMarkers` deletes them from both paths pre-codegen | RETIRED for `-O` decisions (exact channel). Full retirement in the semantic channel = shim marker emission, PARTLY LANDED (wave-MF, 2026-08-12): operand temps are emitted, and the old "provably impossible from the Module alone" claim is retired — it predated the trust-ir lexical scope tree (v33 C2-scopes) and was measured false. What remains unemitted, each measured: aggregate construction, multi-block bodies, `Inst::Load`, right-nested trees, and any body carrying a source `let` (whose named binding locals and `FakeRead` the instruction stream cannot see — `func.scopes.is_some()` is the firewall, and it is a heuristic, NOT a proof: a destructuring param mints named binding locals with `scopes.is_none()`, and is refused by the ORACLE, not the firewall) |
//! | L3 | `goto-thread` | a `Goto` block inlined onto an incoming edge (per hop) | threaded blocks hold only pure assigns, still evaluated per edge (trapping ops still rejected regardless of liveness); no decision point is erased | shim emits the builder's exact trampoline/join block structure (requires modeling `mir_build` scope-exit block placement) |
//! | L4 | `block-renumber` | a reachable block whose canonical (DFS) id differs from its original id | ids carry no semantics; both sides renumbered by the identical deterministic DFS | shim allocates blocks in the builder's creation order so derived ids == built ids; then compare raw ids |
//! | L5 | `local-elim` | a pure `Assign` absorbed into symbolic state | assigns in the fragment are pure and trap-free (`Div`/`Rem` excluded); values are compared at every observable (terminator/return/loop line) | shim reproduces the builder's operand-temp discipline (`_t = copy _arg` chains) so statements match 1:1 under a local bijection |
//! | L6 | `phi-merge` | a `phi[...]` formed at a join (incl. loop back-edge merges) | a phi's identity is its incoming expressions in canonical edge order — no local alignment is assumed | with L5 retired, locals correspond 1:1 and per-local merge comparison becomes exact |
//! | L7 | `ref-alias` | an in-fragment borrow bound as a pure alias (`_r ↦ _x`) | every observation through `_r` resolves to `_x`'s value at that point; the binding fails closed the moment the ref VALUE could escape (by-value read, projected borrow, nested deref, divergent merge) | shim emits real `&`/`&mut` + deref statements mirroring built (needs borrow support in the flip fragment first) |
//! | L8 | `move-as-copy` | an `Operand::Move` read as the place's value | fragment types are all `Copy`; move-ness only matters to borrowck/analysis, which never see the derived body | shim emits `Move` exactly where the builder does (last-use discipline) and the comparator compares operand kinds |
//! | L9 | `loop-congruence` | one or more disjoint sequential single-header natural-loop fixpoint partitions (per body) | classes are inductive bisimulations over (seed, back-edge) signatures — never merges value streams that could differ; per-class `seed=`/`back=` lines pin every transition; sequential loop tokens are namespaced by canonical header role, so a later seed can depend on an earlier fixed point without aliasing its classes; class NAMES are post-pruning content-canonical (a bijective renaming of emitted classes — ids carry no semantics, definitions are compared in full; ambiguous automorphic namings fail closed). Nested, overlapping, irreducible, or branch-parallel loop SCCs remain fail-closed | with L5 retired, loop locals correspond 1:1 and each fixpoint degenerates to per-local equality |
//! | L10 | `unreachable-block-ignore` | a block unreachable in the non-unwind walk ignored (per block) | in-fragment cleanup blocks are a lone `resume` (assert unwind edges), and truly dead blocks are deleted by `SimplifyCfg` before codegen; the marker channel additionally REFUSES markers in such blocks | extraction threads unwind edges + `Resume` into `trust_types`, comparator compares the cleanup subgraph exactly |
//! | L14 | `return-split` | an incoming edge (beyond the first) of a shared `Return` block rendered as its own per-edge `return` observable | `Return` has no successors (no decision point erased); the block's statements are pure in-fragment assigns evaluated per edge with the same trapping-op rejection; strictly refines the observable — per-path return values replace the phi merge, and both sides split by the identical rule | shim reproduces the builder's shared-return-block join structure (scope-exit modeling), then returns compare 1:1 without duplication |
//! | L15 | `unit-return-collapse` | a unit-typed `_0` whose rendered return value is not literally `c:unit` (a built unit TAIL call `_0 = f()` vs the shim's unit convention `_0 = const ()`) | `()` is a singleton — the VALUE carries zero information; the producing call's EFFECT is separately pinned by its own `call(cs..)` site line, and `_0` initialization is still enforced (the read precedes the collapse). The tail-call/stmt-call built shapes are Module-indistinguishable (`{ f(); }` and `{ f() }` lower to byte-identical trust-ir — the marker-infeasibility precedent), so this is a comparator normalization, not a shim guess | shim threads built's call-destination choice (needs THIR tail-position info the producer currently erases) |
//! | L11 | (structural, no counter) `span/debug-name ignore` | spans and local debug names never rendered | no runtime semantics; panic-Location fidelity is separately enforced by the flip's assert-span stitching against the built sibling | producer threads spans through trust-ir (P1.5); comparator then compares spans exactly |
//! | L12 | **RETIRED (v25 B1)** `isize/usize width-collapse` | producer now emits first-class `Ty::Isize`/`Ty::Usize`/`Ty::Char`; BOTH extraction sides run the faithful lane (`extract_function_faithful`) and `canon_ty` renders distinct `isize`/`usize`/`char` tokens; the shim denotes them directly (the `to_mir::PtrSpell` respell subsystem is deleted) | — | done |
//! | L13 | (structural, no counter) `marker-local alpha-rename` | marker-channel locals named by first appearance | a bijective renaming of storage slots is observationally identical to LLVM (`lifetime` intrinsics have per-slot, not cross-slot, semantics); positions/types/event order still compared exactly | shim reuses built local numbering (blocked on L5's operand-temp discipline) |
//!
//! RETIRED (fail-closed now, were silent drops): `Coverage` statements (mir_build emits them
//! only under `-Cinstrument-coverage`; refusing them costs nothing on normal builds),
//! `ConstEvalCounter` (inserted only by the post-built `ctfe_limit` pass — cannot occur in
//! `mir_built` output; refusal is free and proves it).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: Apache-2.0

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use trust_ir::{ProofDigest, ProofDigestAlgorithm};
use trust_types::{
    AggregateKind, ConstValue, Operand, Place, Projection, Rvalue, Statement, Terminator, Ty,
    VerifiableBody,
};

use crate::{Lowered, to_mir};

/// Outcome of the derived-vs-built comparison for one body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DerivedVerdict {
    /// Both bodies canonicalized into identical symbolic forms: the shim reproduced the
    /// built MIR's semantics (up to the documented normalizations).
    DerivedAgreed,
    /// Both canonicalized, but the forms differ — a real structural/semantic divergence
    /// between the shim's reconstruction and the built MIR. `detail` has the first diff.
    DerivedMismatch,
    /// No verdict: the producer, the shim, or the comparator hit a construct outside the
    /// supported fragment (reason in `detail`). Never counted as agreement.
    DerivedUnsupported,
}

const SOURCE_HEADER_CORRESPONDENCE_DOMAIN: &str =
    "trust_thir_lower.source_header_correspondence_witness.v1";

/// Opaque flip capability minted only after the independently built and
/// translated MIR graphs agree on every source-loop header role.
///
/// The fields are deliberately private even though the type crosses the
/// `trust_thir_lower` crate boundary in [`DerivedReport`].  Consequently the
/// `mir_built` hook can only forward a witness produced by
/// [`compare_derived`]; it cannot replace the old authority bit with `true`.
/// `seal` binds the exact built+derived role-map digest to the stable
/// definition/module/callee lineage that was compared.
#[derive(Debug, Clone, Copy)]
pub struct SourceHeaderCorrespondence {
    lineage: ProofDigest,
    role_map: ProofDigest,
    seal: ProofDigest,
}

impl SourceHeaderCorrespondence {
    fn seal(lineage: ProofDigest, role_map: ProofDigest) -> Option<ProofDigest> {
        if lineage.algorithm != ProofDigestAlgorithm::Sha256
            || role_map.algorithm != ProofDigestAlgorithm::Sha256
        {
            return None;
        }
        let mut bytes = Vec::with_capacity(64);
        bytes.extend_from_slice(&lineage.bytes);
        bytes.extend_from_slice(&role_map.bytes);
        Some(ProofDigest::sha256_domain(SOURCE_HEADER_CORRESPONDENCE_DOMAIN, &bytes))
    }

    fn mint(
        tcx: TyCtxt<'_>,
        def: LocalDefId,
        lowered: &Lowered,
        roles: crate::source_provenance::AuthenticatedHeaderRoles,
    ) -> Result<Self, String> {
        let definition = crate::lineage::DefinitionIdentity::from_def_id(tcx, def.to_def_id());
        let lineage =
            crate::lineage::body_lineage_digest(definition, &lowered.module, &lowered.callees)?;
        let seal = Self::seal(lineage, roles.digest)
            .ok_or_else(|| "header correspondence uses a non-SHA256 digest".to_string())?;
        Ok(Self { lineage, role_map: roles.digest, seal })
    }

    pub(crate) fn authenticates(&self, lineage: ProofDigest) -> bool {
        self.lineage == lineage
            && Self::seal(self.lineage, self.role_map).is_some_and(|seal| seal == self.seal)
    }

    #[cfg(test)]
    pub(crate) fn test_only(lineage: ProofDigest) -> Self {
        let role_map = ProofDigest::sha256_domain("test.source_header_roles", b"exact");
        let seal = Self::seal(lineage, role_map).expect("test digests are SHA256");
        Self { lineage, role_map, seal }
    }
}

/// Per-body report plus the running tallies owned by this compiler Session.
#[derive(Debug)]
pub struct DerivedReport {
    pub verdict: DerivedVerdict,
    pub detail: String,
    /// EXACT storage-marker channel (module docs step 5; LEDGER L2). Only meaningful when
    /// `verdict == DerivedAgreed`: true iff derived and built marker sequences are
    /// line-identical. Gates the flip at `-O` (`flip_registry::record_green`).
    pub markers_exact: bool,
    /// Marker-channel diagnostic: identical-count on success, first diff / fail-closed
    /// reason otherwise.
    pub markers_detail: String,
    /// Opaque compiler-owned evidence that source HIR loop identities matched
    /// the carried TrustIR natural headers through equal, unique canonical CFG
    /// roles on the independently built and translated MIR graphs.  A
    /// valid/self-sealed carrier cannot construct this value.
    pub source_header_correspondence: Option<SourceHeaderCorrespondence>,
    /// Cumulative normalization-firing counters (LEDGER), snapshot after this body.
    pub norms: Vec<(&'static str, usize)>,
    /// Running (agreed, mismatch, unsupported) counts including this body.
    pub tally: (usize, usize, usize),
}

/// Invocation-owned aggregate for the derived-MIR ratchet. A rustc_driver
/// process may create multiple compiler Sessions, so this must never be a
/// process-global static. Normalization events are accumulated locally during
/// one comparison and merged here once, avoiding an atomic operation in every
/// symbolic-evaluation hot path.
#[derive(Default)]
struct DerivedSessionStats {
    tally: [usize; 3],
    norms: NormCounts,
}

impl DerivedSessionStats {
    fn record(
        &mut self,
        verdict: DerivedVerdict,
        norm_delta: NormCounts,
    ) -> (NormCounts, (usize, usize, usize)) {
        let verdict_index = match verdict {
            DerivedVerdict::DerivedAgreed => 0,
            DerivedVerdict::DerivedMismatch => 1,
            DerivedVerdict::DerivedUnsupported => 2,
        };
        self.tally[verdict_index] = self.tally[verdict_index].saturating_add(1);
        self.norms = add_norm_counts(self.norms, norm_delta);
        (self.norms, (self.tally[0], self.tally[1], self.tally[2]))
    }
}

fn report(
    tcx: TyCtxt<'_>,
    verdict: DerivedVerdict,
    detail: impl Into<String>,
    norm_delta: NormCounts,
) -> DerivedReport {
    let (norms, tally) = tcx.sess.with_trust_compiler_state::<DerivedSessionStats, _>(|stats| {
        stats.record(verdict, norm_delta)
    });
    DerivedReport {
        verdict,
        detail: detail.into(),
        markers_exact: false,
        markers_detail: String::new(),
        source_header_correspondence: None,
        norms: NORM_NAMES.iter().copied().zip(norms).collect(),
        tally,
    }
}

/// Compare the shim-derived MIR against the freshly THIR-built MIR for one body.
///
/// `built` is the in-scope `Body` the `mir_built` hook holds (never a query — cycle-safe,
/// exactly like `crate::differential::compare`).
pub fn compare_derived<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    lowered: &Lowered,
    built: &mir::Body<'tcx>,
    built_snapshot: Option<&trust_types::VerifiableFunction>,
) -> DerivedReport {
    // (0) Producer coverage gate: an unsupported THIR shape means the Module is partial.
    if !lowered.unsupported.is_empty() {
        return report(
            tcx,
            DerivedVerdict::DerivedUnsupported,
            format!("producer: {} unsupported THIR shape(s)", lowered.unsupported.len()),
            NO_NORMS,
        );
    }
    // (0.25) Pending-const guard: the module carries un-evaluated placeholder sentinels
    // (`Inst::Const { value: Constant::PhantomData }`, see `Lowered::pending_consts`) that the
    // crate finalizer patches later. The shim must never translate a sentinel into a derived
    // MIR constant, so the body is a precise fail-closed skip — never a verdict.
    if !lowered.pending_consts.is_empty() {
        return report(
            tcx,
            DerivedVerdict::DerivedUnsupported,
            format!(
                "pending local const ({} placeholder(s) awaiting finalizer eval)",
                lowered.pending_consts.len()
            ),
            NO_NORMS,
        );
    }
    // (0.5) `extract_function` REPLACES a derived-total (`#[derive]`) method's body with a
    // trivial `Return` on both sides — the comparison would be vacuously equal. Skip.
    if trust_mir_extract::is_derived_total_method(tcx, def.to_def_id()) {
        return report(
            tcx,
            DerivedVerdict::DerivedUnsupported,
            "derived-total method (extraction replaces the body; comparison would be vacuous)",
            NO_NORMS,
        );
    }

    // (1) The shim: trust-ir -> derived mir::Body. Fail-closed on anything out of fragment.
    // The built body's `_0` + arg-local types are threaded in for the opaque non-scalar
    // param classes (slice 3) and as the pointer-width respell's ABI anchors
    // (`to_mir::PtrSpell`; see the `to_mir` module docs for why neither threading can hide
    // a difference). Identical threading to the flip's call site (`flip::derive_flip_body`)
    // — the differential must compare EXACTLY the body the flip would consume.
    let built_arg_tys: Vec<rustc_middle::ty::Ty<'tcx>> =
        (1..=built.arg_count).map(|i| built.local_decls[mir::Local::from_usize(i)].ty).collect();
    let built_ret_ty = built.local_decls[mir::Local::from_usize(0)].ty;
    let derived = match to_mir::lower_ir_to_mir(
        tcx,
        def,
        &lowered.module,
        &lowered.callees,
        // Trust (C1/M1): the differential PROVIDES the types — it compares against built by
        // definition, and at this hook these are byte-identical to the THIR/typeck types the
        // builder consumed. Only the flip lane re-derives (`SigSource::Rederive`).
        to_mir::SigSource::Provided(built_arg_tys, built_ret_ty),
        // Trust (enum-switch provenance): the producer's own record of which enum switches folded
        // their LAST variant into `default`. Identical threading to the flip's call site — the
        // differential must compare EXACTLY the body the flip would consume.
        &lowered.enum_fold_switch_blocks,
    ) {
        Ok(lowering) => lowering,
        Err(e) => {
            return report(
                tcx,
                DerivedVerdict::DerivedUnsupported,
                format!("shim: {}", e.reason),
                NO_NORMS,
            );
        }
    };

    // (2) Reuse the built-side trusted extraction already produced by the
    // interpreter differential, then extract only the newly-derived body. The
    // former independent built extraction made this hook walk each clean built
    // MIR twice (three total extractions including the derived body).
    let Some(vf_built) = built_snapshot else {
        return report(
            tcx,
            DerivedVerdict::DerivedUnsupported,
            "missing shared built-MIR extraction snapshot (fail-closed)",
            NO_NORMS,
        );
    };
    // Trust (v25 B1): the built snapshot is the interpreter differential's
    // FAITHFUL extraction (isize/usize/char first-class) — extract the derived
    // body through the same lane so both sides render identical spellings.
    let vf_derived = trust_mir_extract::extract_function_faithful(tcx, &derived.body);

    // (2.5) SOURCE-LOOP HEADER IDENTITY CHANNEL.  A TrustIR carrier can seal a
    // swapped multi-loop mapping just as easily as the correct one, so neither
    // its digest nor `BlockId` order is authority.  The native builder has
    // independently stamped HIR loop ids on built-MIR natural-loop endpoints;
    // match those headers to translated TrustIR blocks only through equal,
    // unique canonical CFG roles.  Run this before semantic canonicalization:
    // the latter may separately refuse multiple SCCs, but it must never be the
    // accidental reason a forged provenance association stays out of green.
    let header_roles = match crate::source_provenance::authenticate_source_header_correspondence(
        tcx,
        def,
        &lowered.module,
        &derived.ir_block_map,
        built,
        &vf_derived.body,
        &vf_built.body,
    ) {
        Ok(evidence) => evidence,
        Err(reason) => {
            return report(
                tcx,
                DerivedVerdict::DerivedUnsupported,
                format!("source header correspondence: {reason}"),
                NO_NORMS,
            );
        }
    };

    // (2.75) A6 REFS-BOOTSTRAP GUARD. The derived side's shared-param exemption (step 3)
    // can fire only through `env.refs`, whose SOLE bootstrap is a projection-free
    // `Rvalue::Ref`. `to_mir` emits no such borrow today — every one of its `Rvalue::Ref`
    // sites borrows a PROJECTED place — but that invariant lives in an UNFROZEN file, so
    // the oracle refuses the shape itself instead of trusting another file to keep it
    // absent: fail-closed, and refuse-only by construction. See
    // `derived_bare_local_borrow` for the full argument.
    if let Some(found) = derived_bare_local_borrow(&vf_derived.body) {
        return report(
            tcx,
            DerivedVerdict::DerivedUnsupported,
            format!("derived-refs guard: {found}"),
            NO_NORMS,
        );
    }

    // (3) Canonicalize. A derived-side failure is a shim bug surfaced honestly; a built-side
    //     failure means the built MIR uses constructs outside the comparator fragment.
    // BOTH SIDES ARE ANNOTATED FROM THEIR OWN BODY. An earlier revision handed the derived
    // side an empty map on the belief that it had no rustc `mir::Body` to read callee
    // signatures from. It does: `lower_ir_to_mir` returns a `MirLowering` whose `.body` is
    // exactly that, and `vf_derived` is extracted from it at step (2) above.
    //
    // Reading each side from its OWN body is what makes the fact honest rather than
    // borrowed. Copying the built side's kinds across would assert that derived calls the
    // same callee with the same signature at the same block — which is a large part of what
    // this comparator EXISTS to check, so assuming it here would let a shim that called
    // something else inherit an exemption it never earned.
    //
    // Block keying is valid on this side for the same reason it is on the other: the
    // faithful extraction runs no block-rewriting pass, so `vf_derived.body`'s block ids are
    // `derived.body`'s block indices (see `CallArgKinds`).
    let (canon_derived, derived_norms) =
        canonicalize(&vf_derived.body, arg_borrow_kinds_by_block(tcx, &derived.body));
    let canon_derived = match canon_derived {
        Ok(c) => c,
        Err(e) => {
            return report(
                tcx,
                DerivedVerdict::DerivedUnsupported,
                format!("comparator(derived): {e}"),
                derived_norms,
            );
        }
    };
    // The BUILT side reads its own body likewise. Both sets are block-keyed and
    // `Freeze`-guarded at the mint, and the exemption they feed is live (see
    // `operand_expr_call_arg` and `EscapeNames`).
    let (canon_built, built_norms) =
        canonicalize(&vf_built.body, arg_borrow_kinds_by_block(tcx, built));
    let comparison_norms = add_norm_counts(derived_norms, built_norms);
    let canon_built = match canon_built {
        Ok(c) => c,
        Err(e) => {
            return report(
                tcx,
                DerivedVerdict::DerivedUnsupported,
                format!("comparator(built): {e}"),
                comparison_norms,
            );
        }
    };

    // (4) The verdict: line-for-line equality of the canonical forms.
    if canon_built == canon_derived {
        // (4.5) RAW CALL CHANNEL (wave 6): the extraction erases exactly the call payload
        // this pins — interned `FnDef` callee identity (the string channel can collide) and
        // the built side's unwind shape (dropped by `convert_terminator`); `call_source` is
        // deliberately NOT pinned (wave-K: diagnostics-only, codegen-inert).
        // Runs only when a Call terminator exists on either raw side; a divergence is a
        // real `DerivedMismatch`, an out-of-fragment shape a fail-closed unsupported.
        if let Err(e) = raw_call_channel(tcx, built, &derived.body) {
            return match e {
                CallChanErr::Diverge(d) => report(
                    tcx,
                    DerivedVerdict::DerivedMismatch,
                    format!("call channel: {d}"),
                    comparison_norms,
                ),
                CallChanErr::OutOfFragment(d) => report(
                    tcx,
                    DerivedVerdict::DerivedUnsupported,
                    format!("call channel: {d}"),
                    comparison_norms,
                ),
            };
        }
        let source_header_correspondence =
            match SourceHeaderCorrespondence::mint(tcx, def, lowered, header_roles) {
                Ok(witness) => witness,
                Err(reason) => {
                    return report(
                        tcx,
                        DerivedVerdict::DerivedUnsupported,
                        format!("source header correspondence lineage: {reason}"),
                        comparison_norms,
                    );
                }
            };
        let mut r = report(
            tcx,
            DerivedVerdict::DerivedAgreed,
            format!("{} canonical line(s) identical", canon_built.len()),
            comparison_norms,
        );
        r.source_header_correspondence = Some(source_header_correspondence);
        // (5) EXACT marker channel (module docs step 5): a separate, normalization-free
        // comparison of the StorageLive/StorageDead sequences. Its verdict gates the flip
        // at -O; failure here NEVER downgrades the semantic verdict (at -O0 the divergence
        // is codegen-immaterial — RemoveStorageMarkers, see LEDGER L2).
        match (canon_markers(&vf_built.body), canon_markers(&vf_derived.body)) {
            (Ok(mb), Ok(md)) => {
                if mb == md {
                    r.markers_exact = true;
                    r.markers_detail = format!("{} marker line(s) identical", mb.len());
                } else {
                    r.markers_detail = format!("markers differ: {}", first_diff(&mb, &md));
                }
            }
            (Err(e), _) => r.markers_detail = format!("marker channel(built): {e}"),
            (_, Err(e)) => r.markers_detail = format!("marker channel(derived): {e}"),
        }
        return r;
    }
    let detail = first_diff(&canon_built, &canon_derived);
    // Trust (mismatch diagnostics): `first_diff` reports the FIRST differing line, which is enough
    // to classify a local divergence (a reshaped switch, a materialized `Not`) but not a
    // whole-CFG-shape one — there the first difference is a canonical BLOCK NUMBER, and the cause
    // is however many blocks the two sides' DFS walks visited before it. Set
    // `TRUST_DIFF_CANON_DUMP` to a def-path substring (or `1` for every mismatch) to attach both
    // canonical forms in full. Diagnostic only: it widens the reported string, never the verdict.
    let detail = match std::env::var("TRUST_DIFF_CANON_DUMP") {
        Ok(want)
            if !want.is_empty()
                && (want == "1" || tcx.def_path_str(def.to_def_id()).contains(&want)) =>
        {
            format!(
                "{detail}\n--- built ({} lines) ---\n{}\n--- derived ({} lines) ---\n{}",
                canon_built.len(),
                canon_built.join("\n"),
                canon_derived.len(),
                canon_derived.join("\n"),
            )
        }
        _ => detail,
    };
    report(tcx, DerivedVerdict::DerivedMismatch, detail, comparison_norms)
}

/// Raw-call-channel failure split: `Diverge` = the two sides really disagree on a pinned
/// call payload (a `DerivedMismatch`); `OutOfFragment` = a single-side shape the channel
/// refuses to reason about (a fail-closed `DerivedUnsupported`).
enum CallChanErr {
    Diverge(String),
    OutOfFragment(String),
}

/// One raw call's pinned payload: the interned callee `FnDef` type (DefId + GenericArgs —
/// exact, unlike the extraction's def-path STRING), the arg count, and whether the source
/// was a plain call (`CallSource::Normal` — diagnostics-only per its rustc doc, compared
/// anyway; the shim only ever emits `Normal`).
type RawCall<'tcx> = (rustc_middle::ty::Ty<'tcx>, usize, bool);

/// Trust (wave-6): the RAW CALL CHANNEL — a normalization-free, rustc-side check over the
/// two `mir::Body`s, run by `compare_derived` only after the canonical forms compared equal
/// and only when a `Call` terminator exists on either side. It pins what the extraction
/// ERASES (so the semantic channel cannot see):
///   * CALLEE IDENTITY: `func_operand_name` renders a def-path string — sentinel rewrites
///     and path-disambiguator collapse can collide two DefIds. Here the interned `FnDef`
///     types are compared pairwise, in the SAME canonical DFS preorder the comparator's
///     walk uses (switch targets in listed order then otherwise; assert success edge; goto /
///     false-edge real target; call return target).
///   * UNWIND: `convert_terminator` DROPS the unwind successor of a direct call. Built MIR
///     at `Built` phase gives every call — and every assert in a diverge-carrying body —
///     `UnwindAction::Cleanup(bbN)` with `bbN` the drop tree's lone-`resume` cleanup block
///     (verified on real `-Zdump-mir=built`, probes/w6_shim_calls.rs); the shim emits the
///     post-`RemoveNoopLandingPads` normal form `Continue` (the assert arm's proven
///     convention). BOTH are accepted here, on asserts and calls alike; a cleanup block
///     carrying real work (drops), a `Terminate`, or an `Unreachable` unwind fails closed —
///     those never normalize to `Continue`, so the flipped body would diverge from built.
fn raw_call_channel<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    built: &mir::Body<'tcx>,
    derived: &mir::Body<'tcx>,
) -> Result<(), CallChanErr> {
    let has_call = |b: &mir::Body<'tcx>| {
        b.basic_blocks
            .iter()
            .any(|d| matches!(d.terminator().kind, mir::TerminatorKind::Call { .. }))
    };
    if !has_call(built) && !has_call(derived) {
        return Ok(());
    }
    let b_calls = raw_calls_in_dfs_order(tcx, built)?;
    let d_calls = raw_calls_in_dfs_order(tcx, derived)?;
    if b_calls.len() != d_calls.len() {
        return Err(CallChanErr::Diverge(format!(
            "call count built {} vs derived {}",
            b_calls.len(),
            d_calls.len()
        )));
    }
    for (i, (b, d)) in b_calls.iter().zip(d_calls.iter()).enumerate() {
        if b.0 != d.0 {
            return Err(CallChanErr::Diverge(format!(
                "call #{i} callee built {:?} vs derived {:?}",
                b.0, d.0
            )));
        }
        if b.1 != d.1 {
            return Err(CallChanErr::Diverge(format!(
                "call #{i} arg count built {} vs derived {}",
                b.1, d.1
            )));
        }
        // Trust (wave-K): `call_source` is INTENTIONALLY NOT compared. `mir::CallSource`
        // (rustc_middle/src/mir/syntax.rs, `#[doc = "Used only for diagnostics"]`) is a pure
        // label — every codegen/MIR-transform read destructures it as `call_source: _`, so it
        // never affects lowering, optimization, or emitted bytes. Built spells an overloaded
        // operator (`a + b` → `<T as Add>::add`, a `from_hir_call == false` desugar) with
        // `CallSource::OverloadedOperator`; the shim always emits `CallSource::Normal`. Pinning
        // this field rejected EVERY operator/comparison call as `DerivedMismatch` even though the
        // two bodies are byte-identical at the object level — a diagnostics-only field cannot
        // distinguish two codegen-divergent bodies, so dropping the pin admits no wrong flip
        // (the burn-in's byte-identical check is the independent backstop). `b.2`/`d.2` (the
        // `is_Normal` flag) stay in the tuple for the fragment scan but are no longer a gate.
        let _ = (b.2, d.2);
    }
    Ok(())
}

/// The `Cleanup(lone-resume)` / `Continue` benign-unwind check (see `raw_call_channel`).
fn benign_unwind<'tcx>(body: &mir::Body<'tcx>, ua: &mir::UnwindAction) -> Result<(), String> {
    match ua {
        mir::UnwindAction::Continue => Ok(()),
        mir::UnwindAction::Cleanup(bb) => {
            if bb.as_usize() >= body.basic_blocks.len() {
                return Err("unwind target out of range".to_string());
            }
            let data = &body.basic_blocks[*bb];
            let lone_resume = data.is_cleanup
                && data.statements.is_empty()
                && matches!(data.terminator().kind, mir::TerminatorKind::UnwindResume);
            if lone_resume {
                Ok(())
            } else {
                Err(format!("unwind cleanup block {bb:?} is not the lone-resume shape"))
            }
        }
        other => Err(format!("unwind action outside fragment: {other:?}")),
    }
}

/// Collect every `Call`'s pinned payload (`RawCall`) in the canonical DFS preorder, while
/// verifying per-terminator fragment shape: `Call` needs a `Some` return target, a benign
/// unwind, and a `Constant` func operand of interned `FnDef` type; `Assert` needs a benign
/// unwind; `FalseEdge`/`FalseUnwind` follow their REAL target — exactly the extraction's
/// convention (`convert_terminator`), so this walk visits the same blocks the semantic
/// channel reasons about. Any other terminator fails closed.
/// Trust (B4 de-risk pre-tranche, RFC TRUST_IR_V2 §B4): the borrow kind of ONE callee
/// parameter, read from the callee's instantiated signature.
///
/// `NotARef` is a POSITIVE claim ("this parameter is not a reference"), so it is only ever
/// minted where the signature was actually consulted. "We could not consult a signature" is
/// spelled by a `None` ENTRY in [`arg_borrow_kinds_in_dfs_order`], never by a vec of `NotARef`
/// — an absent record must deny the consumer a permission, not grant one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)] // Trust: INERT until the escape classifier consumes it (see below).
pub(crate) enum ArgBorrowKind {
    /// Not a reference (`i32`, `String`, a raw pointer, ...). A RAW POINTER is deliberately
    /// here and not in `Shared`: `*const T` carries no no-write guarantee (the callee may cast
    /// away constness), so it must never receive the shared-parameter exemption.
    NotARef,
    /// `&T` where `T: Freeze` — the callee provably cannot write through it. The `Freeze`
    /// requirement is load-bearing and is enforced at the mint site: a `&Cell<U>` is also
    /// `Ref(.., Not)` but IS writable through, so it is minted `Mut`, not `Shared`.
    Shared,
    /// `&mut T` — the callee may write through it.
    Mut,
}

/// Trust (B4 de-risk pre-tranche): per-ARG borrow kinds for every call, in the SAME canonical
/// DFS preorder [`raw_calls_in_dfs_order`] produces — index `i` here describes call `#i` there.
///
/// WHY THIS EXISTS. `mir_differential` has two walks over two types: the call channel walks a
/// rustc `mir::Body` WITH `tcx`, while `canonicalize` — which owns the escape classification
/// ("ref local _N used by value (escape) outside fragment") — walks a `VerifiableBody` with no
/// `tcx` and no rustc types. A signature fact the classifier needs must therefore be CARRIED.
/// The eventual use is B4's pre-tranche: a scalar slot whose address reaches a `&T` parameter
/// cannot be written through, so the conservative set can shrink per ARG instead of per CALL.
///
/// WHY IT DERIVES FROM `raw_calls_in_dfs_order` RATHER THAN RE-WALKING. Keying these facts to
/// the wrong argument would hand a no-write exemption to a parameter that IS written — the
/// manufactured-agreement failure mode, the one this comparator exists to prevent. Deriving
/// from the same list that pins callee identity makes the alignment hold BY CONSTRUCTION
/// rather than by a second traversal that has to be kept in sync: the caller collects `b_calls`
/// and `d_calls` in this same order and has already proven them equal callee-for-callee, so
/// ordinal `i` denotes the same callee on both sides.
///
/// A `None` entry means NOT RECORDED — a non-`FnDef` callee (fn pointer / indirect call), or a
/// signature whose inputs cannot be read. Consumers must treat `None` as
/// conservative-everything. Never returns a partial vec for a call.
///
/// Per-CALL argument borrow kinds keyed by ORIGINAL BLOCK ID — the form `canonicalize`
/// consumes (see [`Graph::arg_kinds`]).
///
/// WHY A SECOND KEYING EXISTS BESIDE [`arg_borrow_kinds_in_dfs_order`]. That one is keyed by
/// DFS ordinal and derives from `raw_calls_in_dfs_order`, which makes its alignment hold by
/// construction FOR THE CALL CHANNEL — the caller collects `b_calls`/`d_calls` in the same
/// order and proves them equal callee-for-callee, so ordinal `i` denotes the same callee on
/// both sides. That argument does NOT carry to the classifier, which walks a
/// `VerifiableBody`, a different IR: matching a DFS ordinal produced by walking
/// `mir::Body` against a position in a walk of `VerifiableBody` reintroduces exactly the
/// keeping-two-traversals-in-sync problem, and a mis-key here hands a no-write exemption to
/// a parameter that IS written — the manufactured-agreement failure this comparator exists
/// to prevent.
///
/// A block id is a TOTAL key instead, and it survives end to end: a MIR block has exactly
/// one terminator (hence at most one call), `convert.rs` stamps
/// `BasicBlock { id: BlockId(bb.as_usize()) }`, the faithful extraction runs no
/// block-rewriting pass, and `Graph::blocks` is 1:1 with `body.blocks` because it filters
/// STATEMENTS, not blocks. So the `b` the classifier holds IS the rustc block index and the
/// lookup is local, with no cross-IR correspondence to maintain.
///
/// AN ABSENT ENTRY MEANS NOT RECORDED and must DENY the exemption — never grant it. Same
/// discipline as the `None` entry in the DFS-ordered form.
pub(crate) type CallArgKinds = HashMap<usize, Vec<ArgBorrowKind>>;

/// [`CallArgKinds`] for `body`: for every block whose terminator is a `Call` with an interned
/// `FnDef` callee, the callee's per-parameter borrow kinds read from its instantiated
/// signature.
///
/// Blocks with a non-`FnDef` callee (fn pointer / indirect call) get NO entry, which the
/// consumer must read as conservative-everything. A call is never given a partial vec.
///
/// The classification is [`arg_borrow_kinds_in_dfs_order`]'s, extracted so both keyings mint
/// `Shared` under exactly one rule — including the `Freeze` requirement, whose absence would
/// hand the exemption to `&Cell<U>`.
///
/// INERT: nothing consumes the exemption yet. See [`operand_expr_call_arg`] for the one
/// question that must be answered before it can be enabled.
#[allow(dead_code)] // Trust: INERT — see above.
fn arg_borrow_kinds_by_block<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> CallArgKinds {
    let mut out = CallArgKinds::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let Some(term) = &data.terminator else { continue };
        let mir::TerminatorKind::Call { func, .. } = &term.kind else { continue };
        let Some(fn_ty) = func.constant().map(|c| c.const_.ty()) else { continue };
        let rustc_middle::ty::TyKind::FnDef(def_id, args) = fn_ty.kind() else { continue };
        let sig = tcx.fn_sig(*def_id).instantiate(tcx, args).skip_binder();
        out.insert(bb.as_usize(), sig.inputs().iter().map(|t| arg_borrow_kind_of(tcx, *t)).collect());
    }
    out
}

/// The ONE rule that mints an [`ArgBorrowKind`] from a parameter type.
///
/// Extracted so the DFS-ordered and block-keyed collectors cannot drift: a `Shared` minted
/// under a weaker rule in one of them would be a silent hole, and this classification is the
/// entire basis of the no-write exemption.
fn arg_borrow_kind_of<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    t: rustc_middle::ty::Ty<'tcx>,
) -> ArgBorrowKind {
    use rustc_middle::ty::TypeVisitableExt as _;
    match t.kind() {
        // `&T` grants the no-write exemption ONLY when `T: Freeze`. A `&Cell<U>` /
        // `&UnsafeCell<U>` is `Ref(.., Not)` too and the callee CAN write through it, so it is
        // minted `Mut` — which is exactly true of it. `NotARef` would be wrong: that variant is
        // a POSITIVE claim that the parameter is not a reference.
        rustc_middle::ty::TyKind::Ref(_, pointee, rustc_hir::Mutability::Not) => {
            // REENTRANCY/VALIDITY GUARD (ICE fix, 2026-08-20). Callers reach this through
            // `tcx.fn_sig(..).instantiate(..).skip_binder()`, and `skip_binder` LEAVES the
            // signature's late-bound regions in place as escaping `ReBound` vars. A parameter
            // whose POINTEE mentions one — canonically `&'a (dyn Trait + 'a)`, i.e. any
            // `&dyn Trait` argument — therefore arrives here carrying escaping bound vars.
            // `Ty::is_freeze` feeds the type to the `is_freeze_raw` query, which builds a
            // `Freeze<..>` `TraitRef` and wraps it in `ty::Binder::dummy`, and `dummy` asserts
            // `!has_escaping_bound_vars` (compiler/rustc_type_ir/src/binder.rs:86) — so the
            // query is not merely imprecise on this shape, it ABORTS THE COMPILER. Measured:
            // `tests/ui/trust/trust_ir_unsize_dyn_data_lane.rs` ICEd at
            // `rustc_middle/src/ty/predicate.rs:492` via `is_freeze_raw` on `dyn Speak`, from
            // `mir_built` for `call_through` (whose callee `through` takes `&dyn Speak`).
            //
            // This is the FOURTH instance of one family: a `tcx` query issued from inside
            // `mir_built` can close a fatal cycle or trip an invariant (previously RPIT, a
            // self-referential static, and TAIT normalization). The standing rule: a widening
            // change is also a reentrancy audit.
            //
            // FAIL CLOSED, never assume freeze-ness: an unqueryable pointee is minted `Mut`
            // ("the callee may write through it"), which DENIES the no-write exemption. That is
            // the refuses-more direction — it can cost a flip, never manufacture agreement.
            // Erasing the regions to recover precision would be a semantic change to the
            // comparator's admitted scope and is deliberately NOT done here.
            if pointee.has_escaping_bound_vars() {
                ArgBorrowKind::Mut
            } else if pointee.is_freeze(tcx, rustc_middle::ty::TypingEnv::fully_monomorphized()) {
                ArgBorrowKind::Shared
            } else {
                ArgBorrowKind::Mut
            }
        }
        rustc_middle::ty::TyKind::Ref(_, _, rustc_hir::Mutability::Mut) => ArgBorrowKind::Mut,
        _ => ArgBorrowKind::NotARef,
    }
}

/// INERT AS OF THIS COMMIT: nothing reads the result yet. It is landed and proved
/// behaviour-neutral first so the classifier change that consumes it is a small diff with a
/// clean before/after — the same two-step used for the topological intern (#174).
#[allow(dead_code)] // Trust: INERT — see above.
fn arg_borrow_kinds_in_dfs_order<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    calls: &[RawCall<'tcx>],
) -> Vec<Option<Vec<ArgBorrowKind>>> {
    calls
        .iter()
        .map(|(fn_ty, _arity, _normal)| {
            let rustc_middle::ty::TyKind::FnDef(def_id, args) = fn_ty.kind() else {
                return None;
            };
            let sig = tcx.fn_sig(*def_id).instantiate(tcx, args).skip_binder();
            Some(
                // Trust (2026-08-20): this used to inline a SECOND copy of the classification,
                // which is precisely the drift `arg_borrow_kind_of`'s doc comment says the
                // extraction exists to prevent — and the copy did not carry the escaping
                // bound-var guard, so a future consumer of this INERT keying would have
                // inherited the `&dyn Trait` ICE verbatim. Both keyings now mint through the
                // one rule; the A6 interior-mutability reasoning that stood here lives on that
                // function, next to the guard, rather than being duplicated and re-drifting.
                sig.inputs().iter().map(|t| arg_borrow_kind_of(tcx, *t)).collect(),
            )
        })
        .collect()
}

fn raw_calls_in_dfs_order<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> Result<Vec<RawCall<'tcx>>, CallChanErr> {
    let oof = |s: String| CallChanErr::OutOfFragment(s);
    let n = body.basic_blocks.len();
    let mut seen = vec![false; n];
    let mut out: Vec<RawCall<'tcx>> = Vec::new();
    let mut stack = vec![mir::START_BLOCK];
    while let Some(bb) = stack.pop() {
        if bb.as_usize() >= n {
            return Err(oof(format!("branch target {bb:?} out of range")));
        }
        if seen[bb.as_usize()] {
            continue;
        }
        seen[bb.as_usize()] = true;
        let term = body.basic_blocks[bb].terminator();
        let succs: Vec<mir::BasicBlock> = match &term.kind {
            mir::TerminatorKind::Goto { target } => vec![*target],
            mir::TerminatorKind::SwitchInt { targets, .. } => {
                let mut v: Vec<mir::BasicBlock> = targets.iter().map(|(_, t)| t).collect();
                v.push(targets.otherwise());
                v
            }
            mir::TerminatorKind::Assert { target, unwind, .. } => {
                benign_unwind(body, unwind).map_err(|e| oof(format!("assert {e}")))?;
                vec![*target]
            }
            mir::TerminatorKind::FalseEdge { real_target, .. } => vec![*real_target],
            mir::TerminatorKind::FalseUnwind { real_target, unwind } => {
                benign_unwind(body, unwind).map_err(|e| oof(format!("false-unwind {e}")))?;
                vec![*real_target]
            }
            mir::TerminatorKind::Return | mir::TerminatorKind::Unreachable => vec![],
            mir::TerminatorKind::Call {
                func,
                args,
                destination: _,
                target,
                unwind,
                call_source,
                fn_span: _,
            } => {
                let Some(target) = target else {
                    return Err(oof("diverging Call (no return target)".to_string()));
                };
                benign_unwind(body, unwind).map_err(|e| oof(format!("call {e}")))?;
                let fn_ty = match func {
                    mir::Operand::Constant(c) => c.const_.ty(),
                    other => {
                        return Err(oof(format!("non-constant call func operand: {other:?}")));
                    }
                };
                if !matches!(fn_ty.kind(), rustc_middle::ty::FnDef(..)) {
                    return Err(oof(format!("non-FnDef call func type: {fn_ty:?}")));
                }
                // Trust (wave-CR): ERASE REGIONS before pinning the callee `FnDef` identity. Built's
                // `mir_built` FnDef carries the callee's REAL regions (a named/inference region — e.g.
                // `for<Region('a)> fn(&'a i32){helper}`), while the shim reconstructs region-carrying
                // callees with `ReErased` (the producer's `encode_site_args` cannot losslessly carry a
                // real region, so it encodes a lifetime arg as `SiteArg::ErasedRegion`). Erasing regions
                // on BOTH sides makes the comparison REGION-BLIND while keeping the DefId + every TYPE
                // and CONST arg intact (`erase_regions` replaces only regions). SOUND: two `FnDef`s that
                // differ ONLY in regions codegen BYTE-IDENTICALLY — rustc erases all regions before
                // codegen — so admitting a region-only-different derived call cannot make a wrong flip;
                // a different DefId or type/const arg still differs after erasure and is rejected. The
                // region-free def-path STRING channel (`func_operand_name`) already agreed; this pins
                // the remaining did+type/const-arg identity region-insensitively.
                out.push((
                    tcx.erase_and_anonymize_regions(fn_ty),
                    args.len(),
                    matches!(call_source, mir::CallSource::Normal),
                ));
                vec![*target]
            }
            other => {
                return Err(oof(format!(
                    "terminator outside the call-channel fragment: {other:?}"
                )));
            }
        };
        // Reverse so the FIRST successor is visited first (preorder).
        for s in succs.into_iter().rev() {
            if s.as_usize() >= n {
                return Err(oof(format!("branch target {s:?} out of range")));
            }
            if !seen[s.as_usize()] {
                stack.push(s);
            }
        }
    }
    Ok(out)
}

fn first_diff(built: &[String], derived: &[String]) -> String {
    let n = built.len().max(derived.len());
    for i in 0..n {
        let b = built.get(i).map(String::as_str).unwrap_or("<end>");
        let d = derived.get(i).map(String::as_str).unwrap_or("<end>");
        if b != d {
            return format!("line {i}: built `{}` vs derived `{}`", clip(b), clip(d));
        }
    }
    "canonical forms differ (no line-level diff?)".to_string()
}

fn clip(s: &str) -> &str {
    // Keep log lines bounded. The canonical alphabet is ASCII (enforced by the format strings
    // in `canonicalize`), but guard the boundary anyway so a non-ASCII `Debug` payload from a
    // fragment-escaping value can never panic the differential.
    if s.len() <= 240 {
        return s;
    }
    let mut end = 240;
    while end > 0 && !s.is_char_boundary(end) {
        end -= 1;
    }
    &s[..end]
}

// ---------------------------------------------------------------------------
// Canonicalization: VerifiableBody -> Vec<String> (the symbolic canonical form)
// ---------------------------------------------------------------------------
//
// NOTE for the scratch harness: everything from `fn first_diff` above to EOF is pure
// trust-types logic (no rustc), extracted verbatim into the canon-test harness lib with
//   sed -n '/^fn first_diff/,$p' src/mir_differential.rs \
//     | sed -e 's/^fn /pub fn /' -e 's/^struct /pub struct /' -e 's/^const /pub const /'
// (see the harness lib.rs header for the full regeneration command).

type CanonResult<T> = Result<T, String>;

/// A block's canonical control-flow role is the deterministic successor-slot
/// path by which the goto-threaded DFS first discovers it.  Paths are unique
/// within one graph by construction and are independent of raw block numbers.
/// Two isomorphic sequential loops therefore still occupy distinct roles.
///
/// This intentionally shares the semantic canonicalizer's topology rules:
/// every `Goto` is threaded, switch cases precede `otherwise`, and calls have
/// their normal return target as their sole semantic successor.  The helper is
/// used only after both bodies passed the same extraction boundary; source
/// spans, producer `BlockId`s, function block-vector order, and provenance
/// digests never participate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CanonicalCfgRoles {
    by_block: HashMap<usize, Vec<u32>>,
    /// Every reachable raw block consulted while threading gotos, mapped to
    /// the semantic block that owns its canonical role.  Native MIR can stamp
    /// a natural-loop header on a forwarding block immediately before the
    /// branch block; looking up the raw id directly would then spuriously
    /// decline an otherwise identical loop.
    canonical_of: HashMap<usize, usize>,
}

impl CanonicalCfgRoles {
    pub(crate) fn role(&self, block: usize) -> Option<&[u32]> {
        let canonical = self.canonical_of.get(&block).copied().unwrap_or(block);
        self.by_block.get(&canonical).map(Vec::as_slice)
    }
}

pub(crate) fn canonical_cfg_roles(body: &VerifiableBody) -> CanonResult<CanonicalCfgRoles> {
    if body.blocks.is_empty() {
        return Err("empty body".to_string());
    }
    for (index, block) in body.blocks.iter().enumerate() {
        if block.id.0 != index {
            return Err("misindexed basic block".to_string());
        }
    }

    let canonical_of = std::cell::RefCell::new(HashMap::<usize, usize>::new());
    let thread = |start: usize| -> CanonResult<usize> {
        let mut block = start;
        let mut path = Vec::new();
        let mut hops = 0usize;
        loop {
            let data =
                body.blocks.get(block).ok_or_else(|| "goto target out of range".to_string())?;
            match data.terminator {
                Terminator::Goto(target) => {
                    path.push(block);
                    block = target.0;
                    hops += 1;
                    if hops > body.blocks.len() {
                        return Err("goto cycle (pure-forwarding loop) outside fragment".into());
                    }
                }
                _ => {
                    let mut aliases = canonical_of.borrow_mut();
                    aliases.insert(block, block);
                    for alias in path {
                        aliases.insert(alias, block);
                    }
                    return Ok(block);
                }
            }
        }
    };

    let successors = |block: usize| -> CanonResult<Vec<usize>> {
        let data =
            body.blocks.get(block).ok_or_else(|| "canonical block out of range".to_string())?;
        let raw = match &data.terminator {
            Terminator::SwitchInt { targets, otherwise, .. } => targets
                .iter()
                .map(|(_, target)| target.0)
                .chain(std::iter::once(otherwise.0))
                .collect::<Vec<_>>(),
            Terminator::Assert { target, .. } => vec![target.0],
            Terminator::Return | Terminator::Unreachable => Vec::new(),
            Terminator::Goto(_) => {
                return Err("goto block treated as canonical".to_string());
            }
            Terminator::Call { target: Some(target), .. } => vec![target.0],
            Terminator::Call { target: None, .. } => {
                return Err("diverging Call (no return target) outside fragment".to_string());
            }
            Terminator::Drop { .. } => return Err("Drop terminator".to_string()),
            Terminator::Opaque { kind, .. } => {
                return Err(format!("Opaque terminator {kind}"));
            }
            Terminator::Resume => return Err("Resume terminator".to_string()),
            _ => return Err("unknown terminator variant".to_string()),
        };
        raw.into_iter().map(&thread).collect()
    };

    let entry = thread(0)?;
    let mut by_block = HashMap::<usize, Vec<u32>>::new();
    let mut work = vec![(entry, Vec::<u32>::new())];
    while let Some((block, role)) = work.pop() {
        if by_block.contains_key(&block) {
            continue;
        }
        by_block.insert(block, role.clone());
        let next = successors(block)?;
        for (slot, target) in next.into_iter().enumerate().rev() {
            if by_block.contains_key(&target) {
                continue;
            }
            let mut target_role = role.clone();
            target_role.push(u32::try_from(slot).map_err(|_| "too many CFG successor slots")?);
            work.push((target, target_role));
        }
    }

    // This should follow from DFS-tree construction, but keep it executable:
    // the provenance gate relies on a role being a unique cross-graph key.
    let unique = by_block.values().cloned().collect::<HashSet<_>>();
    if unique.len() != by_block.len() {
        return Err("canonical CFG roles are not injective".to_string());
    }
    Ok(CanonicalCfgRoles { by_block, canonical_of: canonical_of.into_inner() })
}

/// Cap on a single symbolic expression's rendered length (defensive against pathological
/// expression blowup from phi-of-phi nesting; hit => fail-closed `Unsupported`).
const MAX_EXPR_LEN: usize = 1 << 16;

/// Bound on loop-fixpoint restarts (each restart strictly shrinks the candidate/alias
/// assumption sets, so this is defensive only).
const MAX_FIXPOINT_RESTARTS: usize = 256;

// ---------------------------------------------------------------------------
// NORMALIZATION LEDGER counters (module docs): one cell per counted ledger row.
// Each canonicalization owns a cheap local counter, including loop-fixpoint
// re-evaluations. Its delta is merged once into Session-owned cumulative state
// after BOTH sides of the comparison have run. This is a FIRING measure for the
// retirement ratchet, not a per-site count; it never influences a verdict.
// ---------------------------------------------------------------------------

const NORM_NAMES: [&'static str; 13] = [
    "nonvalue-stmt-drop",       // L1
    "storage-marker-drop",      // L2
    "goto-thread",              // L3
    "block-renumber",           // L4
    "local-elim",               // L5
    "phi-merge",                // L6
    "ref-alias",                // L7
    "move-as-copy",             // L8
    "loop-congruence",          // L9
    "unreachable-block-ignore", // L10
    "return-split",             // L14
    "unit-return-collapse",     // L15
    "interior-borrow",          // L16 (wave-29)
];
const NORM_COUNT: usize = NORM_NAMES.len();
type NormCounts = [usize; NORM_COUNT];
const NO_NORMS: NormCounts = [0; NORM_COUNT];

const NORM_NONVALUE_STMT_DROP: usize = 0;
const NORM_STORAGE_MARKER_DROP: usize = 1;
const NORM_GOTO_THREAD: usize = 2;
const NORM_BLOCK_RENUMBER: usize = 3;
const NORM_LOCAL_ELIM: usize = 4;
const NORM_PHI_MERGE: usize = 5;
const NORM_REF_ALIAS: usize = 6;
const NORM_MOVE_AS_COPY: usize = 7;
const NORM_LOOP_CONGRUENCE: usize = 8;
const NORM_UNREACHABLE_BLOCK_IGNORE: usize = 9;
const NORM_RET_SPLIT: usize = 10;
const NORM_UNIT_RET_COLLAPSE: usize = 11;
// Trust (wave-29): an interior shared borrow of a ref-param struct field, RETURNED
// (`_dst = &((*_p).K)`) rendered to the DISCRIMINATING symbolic value `iref(a{p},K)` — a
// wrong field index renders a different line, so this canonicalization never masks a difference.
const NORM_INTERIOR_BORROW: usize = 12;

fn add_norm_counts(mut left: NormCounts, right: NormCounts) -> NormCounts {
    for (dst, value) in left.iter_mut().zip(right) {
        *dst = dst.saturating_add(value);
    }
    left
}

/// Comparison-local normalization accounting. `Cell` keeps the counter
/// shareable across the canonicalizer's nested closures without threading a
/// mutable borrow through symbolic environments; the counter never escapes
/// the invoking thread.
struct NormCounter {
    counts: [Cell<usize>; NORM_COUNT],
}

impl Default for NormCounter {
    fn default() -> Self {
        Self { counts: std::array::from_fn(|_| Cell::new(0)) }
    }
}

impl NormCounter {
    fn fire(&self, idx: usize) {
        let count = &self.counts[idx];
        count.set(count.get().saturating_add(1));
    }

    fn snapshot(&self) -> NormCounts {
        std::array::from_fn(|idx| self.counts[idx].get())
    }
}

/// Trust (A6): side-stable names for body-locals whose ADDRESS escapes to a `&T` parameter.
///
/// THE PROBLEM THIS SOLVES. Admitting a `refs`-bound by-value read (see
/// [`operand_expr_call_arg`]) means rendering the address of a body-local, and a body-local
/// has no name in the value channel — `vals` names PARAMS `a{i}` and gives a body-local only
/// its symbolic VALUE. Rendering the address as a function of that value manufactures
/// agreement, because two distinct slots holding equal values render identically:
///
/// ```text
/// source     f(&a, &b)        distinct slots, EQUAL values
/// built      f(&_x, &_y)  ->  ref(v), ref(v)
/// derived    f(&_x, &_x)  ->  ref(v), ref(v)     <- shim wrongly aliased them, hidden
/// ```
///
/// THE FIX IS L13'S OWN ARGUMENT, APPLIED TO ADDRESSES. Number each escaping local by FIRST
/// APPEARANCE in the canonical walk. That is a BIJECTION slot <-> name, so it preserves
/// exactly the property a callee can observe about addresses — which pointers are EQUAL to
/// which — while discarding the absolute values, which no correct program can depend on
/// (they are not stable across runs in the first place). It is the same reasoning LEDGER L13
/// makes for storage-marker locals: "a bijective renaming of storage slots is observationally
/// identical".
///
/// Under it the collapse above no longer hides:
///
/// ```text
/// built      f(&_x, &_y)  ->  ref(e0), ref(e1)
/// derived    f(&_x, &_x)  ->  ref(e0), ref(e0)   <- DIFFERS -> mismatch -> no flip
/// ```
///
/// WHY IT IS SIDE-STABLE. First appearance is taken in the canonical block order the
/// comparator already imposes, so two bodies agree on the numbering exactly when they agree
/// on the structure the comparator is checking anyway. If their structures differ the
/// numbering differs too — which fails in the SAFE direction (a spurious mismatch, never a
/// spurious agreement).
///
/// WHY IT IS BODY-GLOBAL AND NOT PER-CALL. A callee may retain a pointer and compare it
/// against one received later. Numbering per call site would let two different slots take the
/// name `e0` at two sites, so a cross-call aliasing difference could render identically. One
/// counter for the whole body closes that.
///
/// WHY INTERIOR MUTABILITY. Numbering must NOT live in `Env`: `Env` is cloned per path and
/// merged at joins, so a per-path map would let two paths disagree on a name. This is one
/// counter for the whole canonicalization, advanced in the deterministic `g.topo` walk —
/// same shape as [`NormCounter`], and for the same reason.
#[derive(Default)]
struct EscapeNames {
    names: RefCell<HashMap<usize, usize>>,
}

impl EscapeNames {
    /// The stable name for `local`'s address: its existing number, or the next one.
    fn name_of(&self, local: usize) -> usize {
        let mut names = self.names.borrow_mut();
        let next = names.len();
        *names.entry(local).or_insert(next)
    }
}

/// Symbolic machine state at a program point: every VALUE-carrying local's symbolic
/// expression (`vals`), plus the reference-alias bindings created by in-fragment bare-local
/// borrows (`refs`: ref local -> target local). INVARIANT: a local is never in both maps —
/// a value write kills an alias binding and vice versa — and an alias target is always
/// read/written through `vals`, so aliasing is fully resolved at every use.
#[derive(Debug, Clone, Default, PartialEq)]
struct Env {
    vals: HashMap<usize, String>,
    refs: HashMap<usize, usize>,
    /// Trust (T2c, gate 3): PLACE aliases — `_r ↦ <place>` for a SHARED borrow of a projected
    /// place rooted at a shared-ref PARAM (`_r = &(((*_p) as V).k)`, the enum-payload binding
    /// rustc emits for `match self { E::A(x) => .. }`). `refs` cannot express this: it maps a
    /// local to a target LOCAL, and the target here is a projection path, not a local.
    ///
    /// WHY A PLACE AND NOT A RENDERED STRING. The whole point is that reading through `_r` must
    /// render IDENTICALLY to reading the borrowed place directly, because that is exactly what
    /// the derived side does — the shim binds the payload to `((*P) as V).k` and reads it with no
    /// borrow at all. So the binding is resolved LAZILY: `place_expr` re-renders the stored place
    /// AT THE READ, inheriting `place_expr`'s epoch stamping and all of its own fail-closed
    /// behaviour, instead of freezing a string at the borrow. Freezing would be the unsound
    /// variant: a read moved across a store would keep the borrow-time epoch and silently agree.
    ///
    /// The root is required to be a shared-ref param, so the referent is IMMUTABLE for the body's
    /// duration — there is no store channel that could invalidate the alias, which is the property
    /// that makes lazy re-rendering equivalent to a direct read. Every escape route the bare-local
    /// alias fails closed on is failed closed here identically: a by-value read of `_r` errors
    /// ("used by value"), a deref STORE through `_r` finds nothing in `refs` and errors, a
    /// reassignment of `_r` drops the binding, and `merge_envs` keeps it only when every incoming
    /// edge agrees on the same place.
    ref_places: HashMap<usize, Place>,
    // Trust (wave-24 → B10, ORDERED memory-effect observable): the caller-memory EFFECT log of
    // `(*_param).field = v` stores through `&mut Struct` PARAMs, IN PROGRAM ORDER along this
    // path. Each entry is one store: (param local, field index, stored expr). This is NOT folded
    // into `vals` (a store whose result is never read within the body would then render NOTHING
    // — the invisible-store trap — and a wrong shim collapse `(*_1).1=v` would canonicalize
    // identically to the correct `(*_1).0=v` = silent miscompile). It renders as an explicit,
    // DISCRIMINATING, ORDER-PRESERVING `mem[m0:..;m1:..]` suffix on the return observable.
    //
    // Trust (B10): the path's memory EPOCH is `memseq.len()`. Shared-ref-param deref READS and
    // CALL lines stamp the epoch at their own program point (`deref@m{n}` / `call@m{n}`, elided
    // at epoch 0), so a read/write/call reorder renders a DIFFERENT string — retiring the wave-S
    // order-ambiguity (read folded into the value channel + write in an order-blind sorted
    // suffix canonicalized reorder-blind; see [[canonical-form-is-order-blind-across-observable-
    // channels]]). The vec is NEVER sorted — order IS the observable. FIRST SLICE only:
    // straight-line, one store per param, single scalar field, plain `=` store; `merge_envs`
    // fails closed the moment a store would cross a control-flow join, and eval_loop fails
    // closed on a store before/inside a loop (B10 — those stores previously VANISHED from the
    // observable on both sides, a false-Agree channel). See
    // [[flip-needs-caller-memory-observable]].
    memseq: Vec<(usize, usize, String)>,
}

/// One incoming edge of a canonical block: the predecessor (`None` = the virtual entry edge
/// carrying the argument seed), the slot in the predecessor's canonical successor order, and
/// the threaded goto-block path whose pure assigns apply along the edge (in order).
#[derive(Debug, Clone)]
struct Edge {
    pred: Option<usize>,
    slot: usize,
    path: Vec<usize>,
}

/// The canonical CFG over NON-goto blocks (every `Goto` block is threaded onto edges).
struct Graph<'a> {
    /// Filtered blocks by ORIGINAL id: kept pure assigns + terminator (ALL original blocks).
    blocks: Vec<(Vec<&'a Statement>, &'a Terminator)>,
    /// Trust (A6): per-CALL argument borrow kinds, keyed by ORIGINAL BLOCK ID.
    ///
    /// WHY BLOCK ID AND NOT A DFS ORDINAL. A side vec keyed by DFS position would have to be
    /// matched against a traversal of a DIFFERENT IR (`raw_calls_in_dfs_order` walks the rustc
    /// `mir::Body`; this walks a `VerifiableBody`), and keeping two dissimilar traversals in sync
    /// is exactly the mis-keying that hands a no-write exemption to a parameter that IS written.
    /// A block id is a TOTAL key instead — a MIR block has exactly one terminator, hence at most
    /// one call — and it is preserved end-to-end: `convert.rs` stamps
    /// `BasicBlock { id: BlockId(bb.as_usize()) }`, the faithful extraction runs no
    /// block-rewriting pass, and `blocks` above is 1:1 with `body.blocks` (it filters
    /// STATEMENTS, not blocks). So `b` here IS the rustc block index, and the lookup is local.
    ///
    /// Each SIDE is annotated from its OWN body with its own `tcx` (built from the rustc body,
    /// derived from the shim's lowering), so nothing is ever matched ACROSS the two walks.
    /// An ABSENT entry means NOT RECORDED (non-`FnDef` callee) and denies the exemption.
    arg_kinds: CallArgKinds,
    /// Reachable canonical blocks in DFS preorder (canonical id -> original id). (The
    /// internal orig->preorder-id map is a LOCAL of `canonicalize` — output ids live in
    /// `final_of`/`ret_of`.)
    order: Vec<usize>,
    /// Canonical successors per canonical block, slot-ordered: (threaded target, path).
    succ_of: HashMap<usize, Vec<(usize, Vec<usize>)>>,
    /// Incoming edges per canonical block, canonically sorted (virtual entry edge first).
    edges_in: HashMap<usize, Vec<Edge>>,
    /// Deterministic topological order with back-edges removed (== full topo when acyclic).
    topo: Vec<usize>,
    /// Loop back-edges as (pred original id, slot). Empty when acyclic.
    back_edges: HashSet<(usize, usize)>,
    /// The single loop header (original id), retained for the established
    /// one-loop evaluator. `None` for acyclic and multi-loop graphs.
    header: Option<usize>,
    /// Natural-loop headers in backedge-free topological order. More than one
    /// is admitted only when they form one strict dominance chain (disjoint
    /// sequential loops); other multi-loop shapes fail closed at discovery.
    headers: Vec<usize>,
    /// OUTPUT node numbering (return-split, LEDGER L14): non-return reachable blocks by
    /// original id. `Return`-terminated blocks have NO block-level output id — every
    /// incoming edge gets its own node in `ret_of` instead.
    final_of: HashMap<usize, usize>,
    /// Per-edge output ids for edges INTO `Return` blocks, keyed by (pred original id —
    /// `None` for the virtual entry edge — , slot in the pred's canonical successor order).
    ret_of: HashMap<(Option<usize>, usize), usize>,
    /// Total output nodes (non-return blocks + per-edge return instances).
    nodes_total: usize,
}

impl<'a> Graph<'a> {
    /// Output label of `b`'s slot-`k` canonical successor: the per-edge return-instance id
    /// when the (threaded) target is a `Return` block, the block's output id otherwise.
    fn label(&self, b: usize, slot: usize) -> usize {
        let t = self.succ_of[&b][slot].0;
        if matches!(self.blocks[t].1, Terminator::Return) {
            self.ret_of[&(Some(b), slot)]
        } else {
            self.final_of[&t]
        }
    }
}

/// A6 FAIL-CLOSED GUARD (2026-08-20): the first projection-free `Rvalue::Ref`
/// (`_d = &_s` / `_d = &mut _s` — no projections on the BORROWED place) in a DERIVED body,
/// or `None`.
///
/// WHY THE ORACLE CHECKS THIS ITSELF. The shared-param exemption
/// ([`operand_expr_call_arg`]) can fire only through `env.refs`, and `env.refs` BOOTSTRAPS
/// at exactly one statement shape: `apply_stmt`'s bare-local-borrow arm. Every other write
/// to `refs` (the reborrow arm, the loop-header seeds) only PROPAGATES entries that already
/// exist. On the derived side that shape is absent today — every `Rvalue::Ref` emission
/// site in `to_mir::lower_ir_to_mir` borrows a PROJECTED place (`mk_place_field` /
/// `mk_place_deref`) — but that invariant lives in an UNFROZEN file, so inside the oracle
/// it was "empty by construction, provable only by reading another file".
/// `compare_derived` calls this at the derived-side canonicalize seam and REFUSES
/// (`DerivedUnsupported`) any derived body carrying the shape, which converts the
/// invariant into "empty by CHECK, enforced here".
///
/// Mutability is deliberately NOT consulted: `apply_stmt`'s borrow arm ignores it too, so
/// a bare-local `&mut` would seed `refs` exactly like a shared borrow — and the only thing
/// denying a `&mut` exemption after that is `arg_borrow_kind_of`'s `Freeze` check, again
/// outside this file. Refusing both mutabilities keeps the guard total over the bootstrap
/// shape. The destination's projections are likewise ignored (broader than the bootstrap,
/// which also requires a bare destination): refusing more is free, and it keeps the guard
/// a statement about the RVALUE alone.
///
/// This can only ever REFUSE more (cost a comparison, land `DerivedUnsupported`, ship
/// rustc's own built MIR), never widen what is accepted — the one direction the oracle
/// freeze permits.
fn derived_bare_local_borrow(body: &VerifiableBody) -> Option<String> {
    for block in &body.blocks {
        for s in &block.stmts {
            let Statement::Assign { place, rvalue: Rvalue::Ref { mutable, place: rp }, .. } = s
            else {
                continue;
            };
            if rp.projections.is_empty() {
                let amp = if *mutable { "&mut " } else { "&" };
                return Some(format!(
                    "bare-local borrow in derived body (bb{}: _{} = {amp}_{}) — the one \
                     env.refs bootstrap shape; to_mir emits only projected borrows, so this \
                     is refused before it can arm the shared-param exemption",
                    block.id.0, place.local, rp.local
                ));
            }
        }
    }
    None
}

fn canonicalize(body: &VerifiableBody, arg_kinds: CallArgKinds) -> (CanonResult<Vec<String>>, NormCounts) {
    let norms = NormCounter::default();
    // ONE counter for the whole body — see `EscapeNames` on why it is not per-call and not
    // in `Env`.
    let escapes = EscapeNames::default();
    let result = canonicalize_with_norms(body, arg_kinds, &norms, &escapes);
    (result, norms.snapshot())
}

fn canonicalize_with_norms(
    body: &VerifiableBody,
    arg_kinds: CallArgKinds,
    norms: &NormCounter,
    escapes: &EscapeNames,
) -> CanonResult<Vec<String>> {
    // --- signature lines ---
    let mut out: Vec<String> = Vec::new();
    out.push(format!("args:{}", body.arg_count));
    for i in 1..=body.arg_count {
        let decl = body
            .locals
            .get(i)
            .filter(|d| d.index == i)
            .ok_or_else(|| format!("missing/misindexed arg local {i}"))?;
        // `canon_param_ty`, not `canon_ty`: arg DECLARATIONS additionally admit the opaque
        // classes (refs/raw ptrs, zero-upvar closures) the slice-3 shim threads from the
        // built body. Rendered structurally + exactly; VALUE positions still use `canon_ty`.
        out.push(format!("arg{}:{}", i, canon_param_ty(&decl.ty)?));
    }
    // `canon_ret_ty`, not `canon_ty`: the RETURN declaration additionally admits the wave-15
    // opaque SHARED-reference class (`fn(..) -> &T { param }` identity forward), threaded
    // byte-for-byte from the built `_0` type — exactly the `canon_param_ty` argument for args.
    out.push(format!("ret:{}", canon_ret_ty(&body.return_ty)?));

    // --- filtered blocks: (stmts kept, terminator) indexed by original block id ---
    let mut blocks: Vec<(Vec<&Statement>, &Terminator)> = Vec::with_capacity(body.blocks.len());
    for (i, bb) in body.blocks.iter().enumerate() {
        if bb.id.0 != i {
            return Err("misindexed basic block".to_string());
        }
        let mut kept: Vec<&Statement> = Vec::new();
        for s in &bb.stmts {
            match s {
                Statement::Assign { .. } => kept.push(s),
                // Markers: dropped from the SEMANTIC channel (LEDGER L2) — the exact marker
                // channel (`canon_markers`) compares them separately, line-for-line.
                Statement::StorageLive(_) | Statement::StorageDead(_) => {
                    norms.fire(NORM_STORAGE_MARKER_DROP);
                }
                // NoValueWrite statements (LEDGER L1): no place value changes, no traps.
                Statement::Nop | Statement::PlaceMention(_) => {
                    norms.fire(NORM_NONVALUE_STMT_DROP);
                }
                // RETIRED normalizations (module docs): fail-closed, never dropped.
                Statement::Coverage => {
                    return Err(
                        "Coverage statement (instrument-coverage) outside fragment".to_string()
                    );
                }
                Statement::ConstEvalCounter => {
                    return Err("ConstEvalCounter statement (post-built ctfe_limit pass) \
                                cannot occur in mir_built output"
                        .to_string());
                }
                Statement::SetDiscriminant { .. } => return Err("SetDiscriminant".to_string()),
                Statement::Deinit { .. } => return Err("Deinit".to_string()),
                Statement::Retag { .. } => return Err("Retag".to_string()),
                Statement::Intrinsic { .. } => return Err("Intrinsic statement".to_string()),
                Statement::Unsupported { kind, .. } => {
                    return Err(format!("unsupported statement {kind}"));
                }
                _ => return Err("unknown statement variant".to_string()),
            }
        }
        blocks.push((kept, &bb.terminator));
    }
    if blocks.is_empty() {
        return Err("empty body".to_string());
    }

    // --- threading: EVERY goto block is inlined onto its incoming edges (module docs) ---
    let thread = |start: usize| -> CanonResult<(usize, Vec<usize>)> {
        let mut b = start;
        let mut path: Vec<usize> = Vec::new();
        loop {
            if b >= blocks.len() {
                return Err("goto target out of range".to_string());
            }
            match blocks[b].1 {
                Terminator::Goto(t) => {
                    norms.fire(NORM_GOTO_THREAD);
                    path.push(b);
                    if path.len() > blocks.len() {
                        return Err(
                            "goto cycle (pure-forwarding loop) outside fragment".to_string()
                        );
                    }
                    b = t.0;
                }
                _ => return Ok((b, path)),
            }
        }
    };

    // Canonical successors of a NON-goto block, in the FIXED order (threaded).
    let raw_succs = |b: usize| -> CanonResult<Vec<(usize, Vec<usize>)>> {
        Ok(match blocks[b].1 {
            Terminator::SwitchInt { targets, otherwise, .. } => {
                let mut v = Vec::with_capacity(targets.len() + 1);
                for (_, t) in targets {
                    v.push(thread(t.0)?);
                }
                v.push(thread(otherwise.0)?);
                v
            }
            Terminator::Assert { target, .. } => vec![thread(target.0)?],
            Terminator::Return | Terminator::Unreachable => vec![],
            Terminator::Goto(_) => return Err("goto block treated as canonical".to_string()),
            // Trust (wave-6): a direct call's single canonical successor is its return
            // target (the extraction already dropped the unwind edge and this comparator's
            // raw call channel separately verified the built unwind's benign shape).
            Terminator::Call { target: Some(t), .. } => vec![thread(t.0)?],
            Terminator::Call { target: None, .. } => {
                return Err("diverging Call (no return target) outside fragment".to_string());
            }
            Terminator::Drop { .. } => return Err("Drop terminator".to_string()),
            Terminator::Opaque { kind, .. } => return Err(format!("Opaque terminator {kind}")),
            Terminator::Resume => return Err("Resume terminator".to_string()),
            _ => return Err("unknown terminator variant".to_string()),
        })
    };

    // --- canonical numbering: iterative DFS preorder from the (threaded) entry, children
    //     pushed in REVERSE so the first successor is visited first ---
    let (entry, entry_path) = thread(0)?;
    let mut canon_of: HashMap<usize, usize> = HashMap::new();
    let mut order: Vec<usize> = Vec::new();
    let mut work = vec![entry];
    while let Some(b) = work.pop() {
        if canon_of.contains_key(&b) {
            continue;
        }
        canon_of.insert(b, order.len());
        order.push(b);
        let ss = raw_succs(b)?;
        for (s, _) in ss.into_iter().rev() {
            if !canon_of.contains_key(&s) {
                work.push(s);
            }
        }
    }

    // LEDGER L10 counter: ignored unreachable non-goto blocks (cleanup subgraphs like the
    // assert-unwind `resume`, and dead code — the marker channel refuses markers in these).
    // Reachable goto blocks are counted under L3; renumbering under L4 (output numbering).
    for (i, blk) in blocks.iter().enumerate() {
        if !canon_of.contains_key(&i) && !matches!(blk.1, Terminator::Goto(_)) {
            norms.fire(NORM_UNREACHABLE_BLOCK_IGNORE);
        }
    }

    let mut succ_of: HashMap<usize, Vec<(usize, Vec<usize>)>> = HashMap::new();
    for &b in &order {
        succ_of.insert(b, raw_succs(b)?);
    }

    // --- incoming edges per reachable block, in canonical order (virtual entry first) ---
    let mut edges_in: HashMap<usize, Vec<Edge>> = HashMap::new();
    edges_in.entry(entry).or_default().push(Edge { pred: None, slot: 0, path: entry_path });
    for &b in &order {
        for (slot, (t, path)) in succ_of[&b].iter().enumerate() {
            edges_in.entry(*t).or_default().push(Edge { pred: Some(b), slot, path: path.clone() });
        }
    }
    for es in edges_in.values_mut() {
        es.sort_by_key(|e| (e.pred.map(|p| canon_of[&p] + 1).unwrap_or(0), e.slot));
    }

    // --- OUTPUT node numbering (return-split; LEDGER L14) ---
    // Same deterministic DFS preorder as the canonical numbering above, EXCEPT every edge
    // into a `Return`-terminated block yields its OWN output node (a per-edge return
    // instance). A shared return join (the builder threads both arms of a short-circuit
    // switch into one return block) and split per-arm return blocks (the shim) thereby
    // canonicalize to the SAME output shape: one `return <expr>` observable per path,
    // rendered from that edge's symbolic state — strictly MORE precise than the phi merge
    // it replaces, and no decision point is erased (`Return` has no successors).
    let is_return = |b: usize| matches!(blocks[b].1, Terminator::Return);
    enum NodeItem {
        Block(usize),
        /// An edge into a `Return` block: (pred — `None` = virtual entry edge —, slot).
        RetEdge(Option<usize>, usize),
    }
    let mut final_of: HashMap<usize, usize> = HashMap::new();
    let mut ret_of: HashMap<(Option<usize>, usize), usize> = HashMap::new();
    let mut nodes_total = 0usize;
    let mut fwork: Vec<NodeItem> =
        vec![if is_return(entry) { NodeItem::RetEdge(None, 0) } else { NodeItem::Block(entry) }];
    while let Some(item) = fwork.pop() {
        match item {
            NodeItem::Block(b) => {
                if final_of.contains_key(&b) {
                    continue;
                }
                if b != nodes_total {
                    norms.fire(NORM_BLOCK_RENUMBER);
                }
                final_of.insert(b, nodes_total);
                nodes_total += 1;
                for (slot, (t, _)) in succ_of[&b].iter().enumerate().rev() {
                    if is_return(*t) {
                        fwork.push(NodeItem::RetEdge(Some(b), slot));
                    } else if !final_of.contains_key(t) {
                        fwork.push(NodeItem::Block(*t));
                    }
                }
            }
            NodeItem::RetEdge(pred, slot) => {
                ret_of.insert((pred, slot), nodes_total);
                nodes_total += 1;
            }
        }
    }
    // L4/L14 counters for the return instances: an instance whose id moved off the block's
    // original id is renumbering (L4); every edge BEYOND the first of a shared return block
    // is a split-off duplicate (L14).
    for &b in &order {
        if is_return(b) {
            for (k, e) in edges_in.get(&b).map(|v| v.as_slice()).unwrap_or(&[]).iter().enumerate() {
                if k > 0 {
                    norms.fire(NORM_RET_SPLIT);
                }
                if ret_of.get(&(e.pred, e.slot)) != Some(&b) {
                    norms.fire(NORM_BLOCK_RENUMBER);
                }
            }
        }
    }

    // Deterministic Kahn topological order over real edges, skipping `skip` (pred, slot).
    let topo_of = |skip: &HashSet<(usize, usize)>| -> Vec<usize> {
        let mut indeg: HashMap<usize, usize> = order.iter().map(|&b| (b, 0)).collect();
        for (t, es) in &edges_in {
            for e in es {
                if let Some(p) = e.pred {
                    if !skip.contains(&(p, e.slot)) {
                        *indeg.get_mut(t).expect("edge target is reachable") += 1;
                    }
                }
            }
        }
        let mut ready: Vec<usize> = order.iter().copied().filter(|b| indeg[b] == 0).collect();
        ready.sort_by_key(|b| canon_of[b]);
        let mut topo: Vec<usize> = Vec::with_capacity(order.len());
        while !ready.is_empty() {
            let b = ready.remove(0);
            topo.push(b);
            for (slot, (t, _)) in succ_of[&b].iter().enumerate() {
                if skip.contains(&(b, slot)) {
                    continue;
                }
                let d = indeg.get_mut(t).expect("succ target is reachable");
                *d -= 1;
                if *d == 0 {
                    ready.push(*t);
                    ready.sort_by_key(|x| canon_of[x]);
                }
            }
        }
        topo
    };

    // --- loop discovery: acyclic, or disjoint sequential single-header natural loops ---
    let mut back_edges: HashSet<(usize, usize)> = HashSet::new();
    let mut headers: Vec<usize> = Vec::new();
    if topo_of(&HashSet::new()).len() != order.len() {
        // Reachability sets (tiny graphs; set iteration order never observed).
        let reach = |from: usize| -> HashSet<usize> {
            let mut seen: HashSet<usize> = HashSet::new();
            let mut stack: Vec<usize> = succ_of[&from].iter().map(|(t, _)| *t).collect();
            while let Some(b) = stack.pop() {
                if seen.insert(b) {
                    stack.extend(succ_of[&b].iter().map(|(t, _)| *t));
                }
            }
            seen
        };
        let reach_of: HashMap<usize, HashSet<usize>> =
            order.iter().map(|&b| (b, reach(b))).collect();
        let in_cycle: Vec<usize> =
            order.iter().copied().filter(|b| reach_of[b].contains(b)).collect();
        // Partition in-cycle nodes into SCCs (mutual reachability).
        let mut sccs: Vec<Vec<usize>> = Vec::new();
        for &n in &in_cycle {
            match sccs
                .iter_mut()
                .find(|s| reach_of[&s[0]].contains(&n) && reach_of[&n].contains(&s[0]))
            {
                Some(s) => s.push(n),
                None => sccs.push(vec![n]),
            }
        }
        for scc_nodes in &sccs {
            let scc: HashSet<usize> = scc_nodes.iter().copied().collect();
            // Header: the unique SCC block with an in-edge from outside the SCC (or the entry).
            let mut scc_headers: Vec<usize> = scc_nodes
                .iter()
                .copied()
                .filter(|n| {
                    edges_in
                        .get(n)
                        .map(|es| es.iter().any(|e| e.pred.map_or(true, |p| !scc.contains(&p))))
                        .unwrap_or(false)
                })
                .collect();
            scc_headers.sort_by_key(|b| canon_of[b]);
            scc_headers.dedup();
            if scc_headers.len() != 1 {
                return Err("irreducible loop (no unique header) outside fragment".to_string());
            }
            let h = scc_headers[0];
            let mut found_backedge = false;
            for e in &edges_in[&h] {
                if let Some(p) = e.pred {
                    if scc.contains(&p) {
                        back_edges.insert((p, e.slot));
                        found_backedge = true;
                    }
                }
            }
            if !found_backedge {
                return Err("loop header without a back edge".to_string());
            }
            headers.push(h);
        }
        if topo_of(&back_edges).len() != order.len() {
            return Err("nested loop outside fragment".to_string());
        }

        let loop_free_topo = topo_of(&back_edges);
        let topo_pos: HashMap<usize, usize> =
            loop_free_topo.iter().enumerate().map(|(i, &b)| (b, i)).collect();
        headers.sort_by_key(|h| topo_pos[h]);

        // Multi-loop admission is intentionally narrower than "several SCCs":
        // every later header must be dominated by the preceding header in the
        // backedge-free graph. This proves one sequential composition order and
        // rejects parallel or order-ambiguous loops, while SCC separation plus
        // the global cycle-break check above keeps nested/overlapping loops out.
        // It does not claim that every later header post-dominates the earlier
        // one: a branch-optional later loop is admitted, and its bypass/entered
        // return paths are both retained by the symbolic evaluator.
        if headers.len() > 1 {
            let mut dominators: HashMap<usize, HashSet<usize>> = HashMap::new();
            for &b in &loop_free_topo {
                let preds: Vec<usize> = edges_in
                    .get(&b)
                    .map(|es| {
                        es.iter()
                            .filter_map(|e| {
                                let p = e.pred?;
                                (!back_edges.contains(&(p, e.slot))).then_some(p)
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                let mut dom = if preds.is_empty() {
                    HashSet::new()
                } else {
                    let mut intersection = dominators[&preds[0]].clone();
                    for p in &preds[1..] {
                        intersection.retain(|n| dominators[p].contains(n));
                    }
                    intersection
                };
                dom.insert(b);
                dominators.insert(b, dom);
            }
            for pair in headers.windows(2) {
                if !dominators[&pair[1]].contains(&pair[0]) {
                    return Err("non-sequential multiple loops outside fragment".to_string());
                }
            }
        }
    }
    let topo = topo_of(&back_edges);
    let header = (headers.len() == 1).then(|| headers[0]);

    let g = Graph {
        blocks,
        arg_kinds,
        order,
        succ_of,
        edges_in,
        topo,
        back_edges,
        header,
        headers,
        final_of,
        ret_of,
        nodes_total,
    };

    // --- symbolic evaluation ---
    let (term_lines, loop_lines) = match g.headers.as_slice() {
        [] => {
            let (lines, _) = eval_all(body, &g, None, None, norms, escapes)?;
            (lines, Vec::new())
        }
        [h] => eval_loop(body, &g, *h, norms, escapes)?,
        hs => eval_sequential_loops(body, &g, hs, norms, escapes)?,
    };

    for (i, line) in term_lines.into_iter().enumerate() {
        out.push(format!("b{i}: {line}"));
    }
    out.extend(loop_lines);
    Ok(out)
}

/// The symbolic state carried into a block along `edge`: the predecessor's exit state (or
/// the argument seed for the virtual entry edge), with each threaded goto block's pure
/// assigns applied in path order.
fn edge_env(
    body: &VerifiableBody,
    g: &Graph<'_>,
    edge: &Edge,
    exits: &HashMap<usize, Env>,
    norms: &NormCounter,
) -> CanonResult<Env> {
    let mut env = match edge.pred {
        Some(p) => exits
            .get(&p)
            .cloned()
            .ok_or_else(|| {
                format!("predecessor b{p} not evaluated (backedge-free topo order broken)")
            })?,
        None => Env {
            vals: (1..=body.arg_count).map(|i| (i, format!("a{i}"))).collect(),
            refs: HashMap::new(),
            // Trust (T2c): the entry env has no aliases of either kind — params are seeded as
            // values, and a PLACE alias can only come into existence from a borrow statement.
            ref_places: HashMap::new(),
            memseq: Vec::new(),
        },
    };
    for &tb in &edge.path {
        for s in &g.blocks[tb].0 {
            apply_stmt(body, s, &mut env, norms)?;
        }
    }
    Ok(env)
}

/// Merge predecessor-edge states: a local flows through only if EVERY edge defines it the
/// same WAY (value vs alias); differing value expressions form a `phi[...]` (edge order);
/// differing alias targets (or mixed kinds) drop the local so later uses fail closed.
fn merge_envs(envs: &[Env], norms: &NormCounter) -> CanonResult<Env> {
    if envs.len() == 1 {
        return Ok(envs[0].clone());
    }
    // Trust (wave-24): the ref-escape-write FIRST SLICE is straight-line only. A caller-memory
    // referent must NEVER cross a control-flow join — phi-merging a `(param,field,expr)` store
    // could mask a divergence (a wrong field on one edge). Fail closed the moment any incoming
    // edge carries a referent (the whole body then canonicalizes to DerivedUnsupported → no flip →
    // rustc's correct built MIR ships). See [[flip-needs-caller-memory-observable]].
    if envs.iter().any(|e| !e.memseq.is_empty()) {
        return Err("&mut referent store across a control-flow merge outside slice".to_string());
    }
    let mut merged = Env::default();
    'vals: for (local, first) in &envs[0].vals {
        let mut exprs: Vec<&String> = Vec::with_capacity(envs.len());
        exprs.push(first);
        for e in &envs[1..] {
            if e.refs.contains_key(local) {
                continue 'vals;
            }
            match e.vals.get(local) {
                Some(x) => exprs.push(x),
                None => continue 'vals,
            }
        }
        let expr = if exprs.iter().all(|e| *e == exprs[0]) {
            exprs[0].clone()
        } else {
            norms.fire(NORM_PHI_MERGE);
            let joined = exprs.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(";");
            format!("phi[{joined}]")
        };
        if expr.len() > MAX_EXPR_LEN {
            return Err("expression too large".to_string());
        }
        merged.vals.insert(*local, expr);
    }
    'refs: for (local, tgt) in &envs[0].refs {
        for e in &envs[1..] {
            if e.vals.contains_key(local) || e.refs.get(local) != Some(tgt) {
                continue 'refs;
            }
        }
        merged.refs.insert(*local, *tgt);
    }
    // Trust (T2c): a PLACE alias survives a join only when EVERY incoming edge binds the SAME
    // local to the SAME place. Any disagreement — a different place, a value on one edge, or the
    // local simply absent — DROPS the binding, so a later read of it errors rather than silently
    // resolving to one edge's target. Mirrors the `refs` rule above exactly.
    'refplaces: for (local, tgt) in &envs[0].ref_places {
        for e in &envs[1..] {
            if e.vals.contains_key(local)
                || e.refs.contains_key(local)
                || e.ref_places.get(local) != Some(tgt)
            {
                continue 'refplaces;
            }
        }
        merged.ref_places.insert(*local, tgt.clone());
    }
    Ok(merged)
}

/// Evaluate all canonical blocks in `g.topo` order (back-edges never feed a merge here; the
/// loop header, if any, takes `hdr_env` instead). `stop_before = Some(h)` withholds `h` and
/// every block whose complete incoming state depends on an unsolved header, while still
/// evaluating independent earlier-loop latches that an arbitrary Kahn order may place after
/// `h`. This computes loop seeds without mistaking topo tie-breaking for semantic sequencing.
/// Returns the terminator line per canonical id plus every evaluated block's exit state.
fn eval_all(
    body: &VerifiableBody,
    g: &Graph<'_>,
    hdr_env: Option<&Env>,
    stop_before: Option<usize>,
    norms: &NormCounter,
    escapes: &EscapeNames,
) -> CanonResult<(Vec<String>, HashMap<usize, Env>)> {
    let mut header_envs = HashMap::new();
    if let (Some(h), Some(env)) = (g.header, hdr_env) {
        header_envs.insert(h, env.clone());
    }
    eval_with_header_envs(body, g, &header_envs, stop_before, norms, escapes)
}

/// Generalized backedge-free walk used by the sequential-loop solver. Every
/// loop header reached before `stop_before` must have a separately solved
/// state in `header_envs`; there is no optimistic default for a missing loop.
fn eval_with_header_envs(
    body: &VerifiableBody,
    g: &Graph<'_>,
    header_envs: &HashMap<usize, Env>,
    stop_before: Option<usize>,
    norms: &NormCounter,
    escapes: &EscapeNames,
) -> CanonResult<(Vec<String>, HashMap<usize, Env>)> {
    let mut exits: HashMap<usize, Env> = HashMap::new();
    let mut lines: Vec<Option<String>> = vec![None; g.nodes_total];
    for &b in &g.topo {
        if stop_before == Some(b) {
            continue;
        }
        // Return blocks are rendered per incoming EDGE below (return-split, LEDGER L14) —
        // no merge, no block-level line, and no exit state (a Return has no successors).
        if matches!(g.blocks[b].1, Terminator::Return) {
            continue;
        }
        let mut env = if g.headers.contains(&b) {
            match header_envs.get(&b) {
                Some(env) => env.clone(),
                // In a partial seed/fixpoint walk, an unsolved later header is
                // a deliberate cut. Continue scanning: a latch belonging to
                // the loop currently being solved can be independent of this
                // cut even when Kahn's deterministic tie-break puts it later.
                None if stop_before.is_some() => continue,
                None => return Err("loop header reached without a fixpoint state".to_string()),
            }
        } else {
            let mut in_envs: Vec<Env> = Vec::new();
            let mut depends_on_unsolved_prefix = false;
            for e in g.edges_in.get(&b).map(|v| v.as_slice()).unwrap_or(&[]) {
                if let Some(p) = e.pred {
                    if g.back_edges.contains(&(p, e.slot)) {
                        continue;
                    }
                    if stop_before.is_some() && !exits.contains_key(&p) {
                        depends_on_unsolved_prefix = true;
                        break;
                    }
                }
                in_envs.push(
                    edge_env(body, g, e, &exits, norms)
                        .map_err(|reason| format!("block b{b} incoming edge: {reason}"))?,
                );
            }
            if depends_on_unsolved_prefix {
                continue;
            }
            if in_envs.is_empty() {
                return Err("non-entry reachable block without predecessors".to_string());
            }
            merge_envs(&in_envs, norms)?
        };

        for s in &g.blocks[b].0 {
            apply_stmt(body, s, &mut env, norms)?;
        }

        let line = match g.blocks[b].1 {
            Terminator::SwitchInt { discr, targets, .. } => {
                let d = operand_expr(discr, &env, norms)?;
                let mut cases = String::new();
                for (k, (v, _)) in targets.iter().enumerate() {
                    cases.push_str(&format!("{}->b{},", v, g.label(b, k)));
                }
                format!("switch({d})[{cases}else->b{}]", g.label(b, targets.len()))
            }
            Terminator::Assert { cond, expected, msg, .. } => {
                let c = operand_expr(cond, &env, norms)?;
                format!("assert({c},expected={expected},msg={msg:?})->b{}", g.label(b, 0))
            }
            // Trust (wave-6): a direct call — an OBSERVABLE line pinning the site, callee,
            // argument expressions (rendered BEFORE the destination binds, so `_2 = f(_2)`
            // reads the pre-call value), foreignness, and the return edge; the RESULT
            // becomes an OPAQUE site-keyed symbol `cs<site>`. Two calls to the same fn with
            // the same args are DIFFERENT values (side effects), so the key is the call
            // SITE — the block's canonical output id, which corresponds across the two
            // sides exactly when the structures do. The definition line at that site pins
            // the symbol's meaning (callee + args + position), so downstream uses compare
            // by site — the same definitional discipline the loop-class `h<N>` names use.
            // A call inside a loop stays sound under site keying: a "this-iteration" result
            // renders `cs<site>` (the binding is re-established by the call block every
            // trip) while a loop-CARRIED value renders its class name `h<k>` — the two
            // spellings cannot be confused, so iteration mixing cannot hide.
            Terminator::Call { func, args, dest, target: _, atomic, is_foreign, .. } => {
                if atomic.is_some() {
                    return Err("atomic-intrinsic Call outside fragment".to_string());
                }
                // Class-token hygiene: a callee path itself matching the `h<digits>` token
                // grammar (`fn h1()`, a `::h2::` segment) would collide with loop-class
                // renaming — fail closed on the (rare) name, never corrupt a rename.
                let mut probe: HashSet<usize> = HashSet::new();
                collect_class_refs(func, &mut probe);
                if !probe.is_empty() {
                    return Err(format!("callee name carries a class-shaped token: {func}"));
                }
                // Trust (A6): the callee's per-arg borrow kinds for THIS block's call. Absent =>
                // not recorded => no exemption for any argument (see `Graph::arg_kinds`).
                let kinds = g.arg_kinds.get(&b);
                let mut rendered: Vec<String> = Vec::with_capacity(args.len());
                for (i, a) in args.iter().enumerate() {
                    let shared_exempt =
                        kinds.and_then(|k| k.get(i)).copied() == Some(ArgBorrowKind::Shared);
                    rendered.push(operand_expr_call_arg(a, &env, norms, escapes, shared_exempt)?);
                }
                if !dest.projections.is_empty() {
                    return Err("projected call destination outside fragment".to_string());
                }
                let site = g.final_of[&b];
                env.refs.remove(&dest.local);
                // Trust (T2c): rebinding the local must also drop any PLACE alias, or a stale
                // alias would resolve a later read to a place this local no longer denotes.
                env.ref_places.remove(&dest.local);
                env.vals.insert(dest.local, format!("cs{site}"));
                // Trust (B10): stamp the call line with the path's memory EPOCH (elided at 0) —
                // a callee handed the &mut param can observe whether the store already happened,
                // so write-vs-call ORDER is semantically real and must render distinctly.
                // (Read-vs-call needs no pin: comparator-visible param-deref reads are shim-gated
                // to SHARED-ref scalar pointees, immutable for the borrow's duration.) Calls are
                // NOT pushed into memseq — that would trip the merge fail-close on every
                // call-before-join body (the println corpus); the stamp gives the same ordering
                // power with zero blast radius since store-bearing envs never cross merges.
                let stamp = if env.memseq.is_empty() {
                    String::new()
                } else {
                    format!("@m{}", env.memseq.len())
                };
                format!(
                    "call{stamp}(cs{site},{func},foreign={is_foreign})[{}]->b{}",
                    rendered.join(","),
                    g.label(b, 0)
                )
            }
            Terminator::Return => {
                return Err("return block reached the merge walk (return-split broken)".to_string());
            }
            // Trust (B10): render the memory suffix at the unreachable SINK too — closes the
            // store-then-unreachable invisibility (dead path, but symmetric and free).
            Terminator::Unreachable => format!("unreachable{}", render_memout(&env)),
            Terminator::Goto(_) => return Err("goto block treated as canonical".to_string()),
            _ => return Err("unknown terminator variant".to_string()),
        };
        lines[g.final_of[&b]] = Some(line);
        exits.insert(b, env);
    }
    // Per-edge RETURN observables (return-split, LEDGER L14): every incoming edge of a
    // reachable `Return` block is rendered as its own `return <expr>` line from THAT edge's
    // symbolic state — the block's kept statements are pure assigns, (re-)evaluated per
    // edge under the same fail-closed rules (trapping ops rejected regardless of liveness).
    if stop_before.is_none() {
        for &b in &g.order {
            if !matches!(g.blocks[b].1, Terminator::Return) {
                continue;
            }
            for e in g.edges_in.get(&b).map(|v| v.as_slice()).unwrap_or(&[]) {
                let mut env = edge_env(body, g, e, &exits, norms)
                    .map_err(|reason| format!("return b{b} incoming edge: {reason}"))?;
                for s in &g.blocks[b].0 {
                    apply_stmt(body, s, &mut env, norms)?;
                }
                let r =
                    env.vals.get(&0).ok_or_else(|| "return with uninitialized _0".to_string())?;
                // LEDGER L15 (unit-return collapse): `()` is a singleton — `_0`'s VALUE
                // carries zero information, and the effect of any call that produced it is
                // pinned by that call's own site line. Collapsing the rendered value makes
                // a built unit TAIL call (`_0 = f()`) and the shim's unit-return convention
                // (`_0 = const ()`) compare equal WITHOUT weakening initialization checking
                // (the `_0` read above still fails closed on an uninitialized return).
                let r = if matches!(body.return_ty, Ty::Unit) && r != "c:unit" {
                    norms.fire(NORM_UNIT_RET_COLLAPSE);
                    "c:unit"
                } else {
                    r.as_str()
                };
                let id = *g
                    .ret_of
                    .get(&(e.pred, e.slot))
                    .ok_or_else(|| "return edge without an output node".to_string())?;
                // Trust (wave-24): the caller-memory EFFECT observed at the function boundary — the
                // `&mut`-param field stores this edge performed, rendered as an explicit
                // DISCRIMINATING suffix (empty ⇒ no suffix ⇒ byte-identical to a pre-wave-24 return
                // line, so no existing body regresses). Emitted ALONGSIDE `_0` because the caller
                // observes the mutated referent exactly as it observes the return value.
                let mem = render_memout(&env);
                lines[id] = Some(format!("return {r}{mem}"));
            }
        }
    }
    let mut done: Vec<String> = Vec::new();
    if stop_before.is_none() {
        for (i, l) in lines.into_iter().enumerate() {
            done.push(l.ok_or_else(|| format!("missing canonical block b{i}"))?);
        }
    }
    Ok((done, exits))
}

/// The single-natural-loop fixpoint (module docs, step 3): partition the header's merged
/// locals into congruence classes by (seed, back-edge expression), refined to stability,
/// then emit the final terminator lines plus the per-class `loop@bH` definition lines.
fn eval_loop(
    body: &VerifiableBody,
    g: &Graph<'_>,
    h: usize,
    norms: &NormCounter,
    escapes: &EscapeNames,
) -> CanonResult<(Vec<String>, Vec<String>)> {
    // LEDGER L9: the loop-congruence machinery is engaged for this body.
    norms.fire(NORM_LOOP_CONGRUENCE);
    // Seed state: the merge of the header's OUTSIDE edges, evaluated on the loop-free prefix.
    let (_, prefix_exits) = eval_all(body, g, None, Some(h), norms, escapes)?;
    let outside: Vec<&Edge> = g.edges_in[&h]
        .iter()
        .filter(|e| e.pred.map_or(true, |p| !g.back_edges.contains(&(p, e.slot))))
        .collect();
    let mut seed_envs: Vec<Env> = Vec::new();
    for e in &outside {
        seed_envs.push(edge_env(body, g, e, &prefix_exits, norms)?);
    }
    if seed_envs.is_empty() {
        return Err("loop header without an entry edge".to_string());
    }
    let seed = merge_envs(&seed_envs, norms)?;
    // Trust (B10, loop-store hole 1): merge_envs' single-env early return skips the referent
    // gate, and hdr_env below resets memseq — so a `&mut`-param store BEFORE a single-entry loop
    // previously VANISHED from every post-loop return observable ON BOTH SIDES (a derived
    // wrong-field store would falsely Agree). Fail closed: a store preceding a loop is outside
    // the straight-line slice.
    if !seed.memseq.is_empty() {
        return Err("&mut-param store precedes a loop outside slice".to_string());
    }

    // Optimistic assumptions, shrunk (fail-closed) on evidence from back-edges.
    let mut cand: Vec<usize> = seed.vals.keys().copied().collect();
    cand.sort_unstable();
    let mut refs_assumed: Vec<(usize, usize)> = seed.refs.iter().map(|(l, t)| (*l, *t)).collect();
    refs_assumed.sort_unstable();

    let back: Vec<&Edge> = g.edges_in[&h]
        .iter()
        .filter(|e| e.pred.map_or(false, |p| g.back_edges.contains(&(p, e.slot))))
        .collect();
    if back.is_empty() {
        return Err("loop header without a back edge".to_string());
    }

    // Class ids from the \x1f-joined signature chains: distinct chains always differ at a
    // position inside their common length (every element is \x1f-terminated and chains have
    // equal element counts), so sig ORDER — and thus class naming — is stable under appends.
    let classes_of = |sig: &HashMap<usize, String>, cand: &[usize]| -> HashMap<usize, usize> {
        let mut sigs: Vec<String> = cand.iter().map(|l| sig[l].clone()).collect();
        sigs.sort_unstable();
        sigs.dedup();
        cand.iter().map(|l| (*l, sigs.binary_search(&sig[l]).expect("own sig present"))).collect()
    };

    let mut restarts = 0usize;
    'restart: loop {
        restarts += 1;
        if restarts > MAX_FIXPOINT_RESTARTS {
            return Err("loop fixpoint restart bound exceeded".to_string());
        }
        let mut sig: HashMap<usize, String> =
            cand.iter().map(|&l| (l, format!("{}\u{1f}", seed.vals[&l]))).collect();
        let mut cid_of = classes_of(&sig, &cand);
        for _round in 0..=cand.len() + 1 {
            let hdr_env = Env {
                vals: cand.iter().map(|&l| (l, format!("h{}", cid_of[&l]))).collect(),
                refs: refs_assumed.iter().copied().collect(),
                // Trust (T2c): DELIBERATELY EMPTY, and this is the fail-closed choice rather than
                // an omission. There is no `ref_places_assumed` counterpart to the `refs_assumed`
                // fixpoint, so a PLACE alias live at a loop header is simply DROPPED — any read
                // through it inside the loop then errors ("read of possibly-uninitialized local")
                // and the body falls out of the fragment. Carrying it optimistically instead would
                // require proving the alias survives every back edge, which is exactly the
                // shrink-on-evidence argument `refs_assumed` exists to make; until a payload
                // binding actually needs to cross a loop header, refusing is the honest answer.
                ref_places: HashMap::new(),
                // Trust (wave-24 → B10): a loop header is out of the straight-line
                // ref-escape-write slice. The empty memseq here is JUSTIFIED by the two B10
                // fail-closes: the seed gate above (no store enters the loop) and the back-edge
                // gate below (no store survives an iteration) — previously a store in either
                // position silently vanished.
                memseq: Vec::new(),
            };
            let (lines, exits) = eval_all(body, g, Some(&hdr_env), None, norms, escapes)?;
            let mut back_envs: Vec<Env> = Vec::new();
            for e in &back {
                back_envs.push(edge_env(body, g, e, &exits, norms)?);
            }
            // Trust (B10, loop-store hole 2): back-edge verification below checks vals/refs
            // ONLY — a `&mut`-param store INSIDE the loop previously died on the back edge and
            // was invisible in the suffix (false-Agree channel, same as the seed gate above).
            // Fail closed: a store inside a loop is outside the straight-line slice.
            if back_envs.iter().any(|be| !be.memseq.is_empty()) {
                return Err("&mut-param store inside a loop outside slice".to_string());
            }
            // Verify assumptions against every back edge; shrink + restart on failure.
            for &l in &cand {
                if back_envs.iter().any(|be| !be.vals.contains_key(&l)) {
                    cand.retain(|&x| x != l);
                    continue 'restart;
                }
            }
            for &(l, t) in &refs_assumed {
                if back_envs
                    .iter()
                    .any(|be| be.vals.contains_key(&l) || be.refs.get(&l) != Some(&t))
                {
                    refs_assumed.retain(|&(x, _)| x != l);
                    continue 'restart;
                }
            }
            // Back-edge expression per candidate (phi over back edges in canonical order).
            let mut backs: HashMap<usize, String> = HashMap::new();
            for &l in &cand {
                let exprs: Vec<&String> = back_envs.iter().map(|be| &be.vals[&l]).collect();
                let expr = if exprs.iter().all(|e| *e == exprs[0]) {
                    exprs[0].clone()
                } else {
                    norms.fire(NORM_PHI_MERGE);
                    let joined = exprs.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(";");
                    format!("phi[{joined}]")
                };
                if expr.len() > MAX_EXPR_LEN {
                    return Err("expression too large".to_string());
                }
                backs.insert(l, expr);
            }
            // Refine the partition by the back expressions.
            for &l in &cand {
                let chunk = format!("{}\u{1f}", backs[&l]);
                sig.get_mut(&l).expect("candidate sig").push_str(&chunk);
            }
            let new_cid_of = classes_of(&sig, &cand);
            if new_cid_of == cid_of {
                // Converged: `lines`/`backs` were computed WITH these very class names.
                // Emit the per-class definition lines, pruned to (transitively) used ones.
                let mut class_seed: HashMap<usize, &String> = HashMap::new();
                let mut class_back: HashMap<usize, &String> = HashMap::new();
                for &l in &cand {
                    class_seed.insert(cid_of[&l], &seed.vals[&l]);
                    class_back.insert(cid_of[&l], &backs[&l]);
                }
                let mut used: HashSet<usize> = HashSet::new();
                for line in &lines {
                    collect_class_refs(line, &mut used);
                }
                loop {
                    let mut grew = false;
                    for (cid, s) in class_seed.iter().chain(class_back.iter()) {
                        if used.contains(cid) {
                            let before = used.len();
                            collect_class_refs(s, &mut used);
                            grew |= used.len() != before;
                        }
                    }
                    if !grew {
                        break;
                    }
                }
                // POST-PRUNING CANONICAL NAMING (LEDGER L9 naming). The fixpoint's class
                // ids were assigned by sorted-signature order over the PRE-pruning
                // candidate set, so a side carrying extra (pruned) invariant candidates —
                // the shim's materialized arg local, a const temp — shifts the SURVIVING
                // ids (built `return h1` vs derived `return h2` for the SAME class: the
                // count_down false mismatch). Class names must therefore be derived from
                // the post-pruning classes alone: rename the USED classes by a
                // name-independent canonical order — signature-chain refinement over the
                // classes' (seed, back) content rendered under the CURRENT canonical
                // names, starting from the fully name-shared naming (content-only), the
                // exact discipline `classes_of` uses (appends preserve chain distinctness
                // and order). At the stable naming every used class must hold a UNIQUE
                // name — truly automorphic classes (identical content under a nontrivial
                // name bijection) FAIL CLOSED rather than pick an arbitrary order.
                //
                // WHY THIS CANNOT EQUATE DISTINCT LOOPS: the renaming is a per-side
                // BIJECTION on the emitted classes, applied uniformly to every observable
                // (terminator lines + per-class seed/back definition lines). Two sides
                // compare equal only if the canonical bijection matches seeds AND
                // per-iteration back-edge transitions AND every terminator observable —
                // which pins equal value streams by induction (equal at iteration 0,
                // equality at k forces k+1), the same bisimulation argument as the
                // congruence itself. Class ids, like block ids (L4) and local ids (L5),
                // carry no semantics; only their DEFINITIONS do, and those are compared
                // in full.
                let mut used_cids: Vec<usize> =
                    class_seed.keys().copied().filter(|c| used.contains(c)).collect();
                used_cids.sort_unstable();
                let mut nsig: HashMap<usize, String> =
                    used_cids.iter().map(|&c| (c, String::new())).collect();
                let mut name_of: HashMap<usize, usize> =
                    used_cids.iter().map(|&c| (c, 0)).collect();
                let mut stable = used_cids.is_empty();
                for _ in 0..=used_cids.len() + 1 {
                    for &c in &used_cids {
                        let chunk = format!(
                            "{}\u{1f}{}\u{1f}",
                            rename_class_refs(class_seed[&c], &name_of)?,
                            rename_class_refs(class_back[&c], &name_of)?
                        );
                        if nsig[&c].len() + chunk.len() > MAX_EXPR_LEN {
                            return Err("expression too large".to_string());
                        }
                        nsig.get_mut(&c).expect("used cid sig").push_str(&chunk);
                    }
                    let new_name_of = classes_of(&nsig, &used_cids);
                    if new_name_of == name_of {
                        stable = true;
                        break;
                    }
                    name_of = new_name_of;
                }
                if !stable {
                    // Chain refinement over <= |used| names cannot fail to stabilize;
                    // defensive.
                    return Err("loop-class canonical naming did not converge".to_string());
                }
                let mut names_seen: Vec<usize> = name_of.values().copied().collect();
                names_seen.sort_unstable();
                names_seen.dedup();
                if names_seen.len() != used_cids.len() {
                    return Err("ambiguous loop-class canonical naming (automorphic classes) \
                         outside fragment"
                        .to_string());
                }
                let mut emit_order: Vec<usize> = used_cids.clone();
                emit_order.sort_unstable_by_key(|c| name_of[c]);
                let mut loop_lines: Vec<String> = Vec::new();
                for &cid in &emit_order {
                    loop_lines.push(format!(
                        "loop@b{} h{}: seed={} back={}",
                        g.final_of[&h],
                        name_of[&cid],
                        rename_class_refs(class_seed[&cid], &name_of)?,
                        rename_class_refs(class_back[&cid], &name_of)?
                    ));
                }
                let mut out_lines: Vec<String> = Vec::with_capacity(lines.len());
                for l in &lines {
                    out_lines.push(rename_class_refs(l, &name_of)?);
                }
                return Ok((out_lines, loop_lines));
            }
            cid_of = new_cid_of;
        }
        // Monotone refinement over <= |cand| classes cannot fail to stabilize; defensive.
        return Err("loop fixpoint did not converge".to_string());
    }
}

/// One not-yet-canonically-named fixed point in a sequential multi-loop body.
/// `token_prefix` is unique within the body, so later-loop seeds may mention
/// earlier classes without either loop's post-pruning renamer capturing the
/// other's tokens.
struct SequentialLoopSolution {
    header: usize,
    token_prefix: String,
    class_seed: HashMap<usize, String>,
    class_back: HashMap<usize, String>,
}

fn class_ids_of(sig: &HashMap<usize, String>, cand: &[usize]) -> HashMap<usize, usize> {
    let mut sigs: Vec<String> = cand.iter().map(|l| sig[l].clone()).collect();
    sigs.sort_unstable();
    sigs.dedup();
    cand.iter().map(|l| (*l, sigs.binary_search(&sig[l]).expect("own sig present"))).collect()
}

/// Solve disjoint natural loops in their proved dominance order.  Earlier
/// header states are frozen while solving a later loop; therefore a later seed
/// may depend on an earlier loop class, but no circular cross-SCC assumption is
/// introduced.  Class pruning and naming are delayed until every loop is
/// solved, because a class that is dead at the first loop's exit block may be
/// live in a later loop's seed.
fn eval_sequential_loops(
    body: &VerifiableBody,
    g: &Graph<'_>,
    headers: &[usize],
    norms: &NormCounter,
    escapes: &EscapeNames,
) -> CanonResult<(Vec<String>, Vec<String>)> {
    norms.fire(NORM_LOOP_CONGRUENCE);
    let mut solved_headers = HashMap::<usize, Env>::new();
    let mut solutions = Vec::<SequentialLoopSolution>::with_capacity(headers.len());

    for (loop_index, &h) in headers.iter().enumerate() {
        let (_, prefix_exits) = eval_with_header_envs(body, g, &solved_headers, Some(h), norms, escapes)?;
        let outside: Vec<&Edge> = g.edges_in[&h]
            .iter()
            .filter(|e| e.pred.map_or(true, |p| !g.back_edges.contains(&(p, e.slot))))
            .collect();
        let mut seed_envs = Vec::<Env>::with_capacity(outside.len());
        for e in &outside {
            seed_envs.push(
                edge_env(body, g, e, &prefix_exits, norms)
                    .map_err(|reason| format!("header b{h} seed edge: {reason}"))?,
            );
        }
        if seed_envs.is_empty() {
            return Err("loop header without an entry edge".to_string());
        }
        let seed = merge_envs(&seed_envs, norms)?;
        if !seed.memseq.is_empty() {
            return Err("&mut-param store precedes a loop outside slice".to_string());
        }

        let mut cand: Vec<usize> = seed.vals.keys().copied().collect();
        cand.sort_unstable();
        let mut refs_assumed: Vec<(usize, usize)> =
            seed.refs.iter().map(|(l, t)| (*l, *t)).collect();
        refs_assumed.sort_unstable();
        let back: Vec<&Edge> = g.edges_in[&h]
            .iter()
            .filter(|e| e.pred.map_or(false, |p| g.back_edges.contains(&(p, e.slot))))
            .collect();
        if back.is_empty() {
            return Err("loop header without a back edge".to_string());
        }
        let token_prefix = format!("@L{loop_index}h");
        let stop_before = headers.get(loop_index + 1).copied();

        let mut restarts = 0usize;
        let (header_env, class_seed, class_back) = 'restart: loop {
            restarts += 1;
            if restarts > MAX_FIXPOINT_RESTARTS {
                return Err("loop fixpoint restart bound exceeded".to_string());
            }
            let mut sig: HashMap<usize, String> =
                cand.iter().map(|&l| (l, format!("{}\u{1f}", seed.vals[&l]))).collect();
            let mut cid_of = class_ids_of(&sig, &cand);
            for _round in 0..=cand.len() + 1 {
                let hdr_env = Env {
                    vals: cand
                        .iter()
                        .map(|&l| (l, format!("{token_prefix}{}", cid_of[&l])))
                        .collect(),
                    refs: refs_assumed.iter().copied().collect(),
                    ref_places: HashMap::new(),
                    memseq: Vec::new(),
                };
                let mut trial_headers = solved_headers.clone();
                trial_headers.insert(h, hdr_env.clone());
                let (_, exits) =
                    eval_with_header_envs(body, g, &trial_headers, stop_before, norms, escapes)?;
                let mut back_envs = Vec::<Env>::with_capacity(back.len());
                for e in &back {
                    back_envs.push(
                        edge_env(body, g, e, &exits, norms)
                            .map_err(|reason| format!("header b{h} back edge: {reason}"))?,
                    );
                }
                if back_envs.iter().any(|be| !be.memseq.is_empty()) {
                    return Err("&mut-param store inside a loop outside slice".to_string());
                }
                for &l in &cand {
                    if back_envs.iter().any(|be| !be.vals.contains_key(&l)) {
                        cand.retain(|&x| x != l);
                        continue 'restart;
                    }
                }
                for &(l, t) in &refs_assumed {
                    if back_envs
                        .iter()
                        .any(|be| be.vals.contains_key(&l) || be.refs.get(&l) != Some(&t))
                    {
                        refs_assumed.retain(|&(x, _)| x != l);
                        continue 'restart;
                    }
                }

                let mut backs = HashMap::<usize, String>::new();
                for &l in &cand {
                    let exprs: Vec<&String> = back_envs.iter().map(|be| &be.vals[&l]).collect();
                    let expr = if exprs.iter().all(|e| *e == exprs[0]) {
                        exprs[0].clone()
                    } else {
                        norms.fire(NORM_PHI_MERGE);
                        format!(
                            "phi[{}]",
                            exprs.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(";")
                        )
                    };
                    if expr.len() > MAX_EXPR_LEN {
                        return Err("expression too large".to_string());
                    }
                    backs.insert(l, expr);
                }
                for &l in &cand {
                    let chunk = format!("{}\u{1f}", backs[&l]);
                    sig.get_mut(&l).expect("candidate sig").push_str(&chunk);
                }
                let new_cid_of = class_ids_of(&sig, &cand);
                if new_cid_of == cid_of {
                    let mut class_seed = HashMap::<usize, String>::new();
                    let mut class_back = HashMap::<usize, String>::new();
                    for &l in &cand {
                        let cid = cid_of[&l];
                        let seed_value = seed.vals[&l].clone();
                        let back_value = backs[&l].clone();
                        if class_seed
                            .insert(cid, seed_value.clone())
                            .is_some_and(|previous| previous != seed_value)
                            || class_back
                                .insert(cid, back_value.clone())
                                .is_some_and(|previous| previous != back_value)
                        {
                            return Err("loop class members disagree after convergence".to_string());
                        }
                    }
                    break 'restart (hdr_env, class_seed, class_back);
                }
                cid_of = new_cid_of;
            }
            return Err("loop fixpoint did not converge".to_string());
        };

        solved_headers.insert(h, header_env);
        solutions.push(SequentialLoopSolution { header: h, token_prefix, class_seed, class_back });
    }

    let (mut term_lines, _) = eval_with_header_envs(body, g, &solved_headers, None, norms, escapes)?;

    // Global liveness closure over all fixed-point definitions. Starting from
    // terminator observables (including every loop condition), follow only
    // definitions of already-live classes. This prunes shim-only locals without
    // accidentally retaining a prior class merely because an unused later
    // class mentioned it.
    let mut used: Vec<HashSet<usize>> = vec![HashSet::new(); solutions.len()];
    for line in &term_lines {
        for (i, solution) in solutions.iter().enumerate() {
            collect_scoped_class_refs(line, &solution.token_prefix, &mut used[i])?;
        }
    }
    loop {
        let before: usize = used.iter().map(HashSet::len).sum();
        let snapshot = used.clone();
        for (i, cids) in snapshot.iter().enumerate() {
            for cid in cids {
                let seed = solutions[i]
                    .class_seed
                    .get(cid)
                    .ok_or_else(|| format!("live loop class {cid} has no seed definition"))?;
                let back = solutions[i]
                    .class_back
                    .get(cid)
                    .ok_or_else(|| format!("live loop class {cid} has no back definition"))?;
                for text in [seed, back] {
                    for (j, solution) in solutions.iter().enumerate() {
                        collect_scoped_class_refs(text, &solution.token_prefix, &mut used[j])?;
                    }
                }
            }
        }
        if used.iter().map(HashSet::len).sum::<usize>() == before {
            break;
        }
    }

    let mut final_names = Vec::<HashMap<usize, usize>>::with_capacity(solutions.len());
    for i in 0..solutions.len() {
        let current_prefix = solutions[i].token_prefix.clone();
        let mut used_cids: Vec<usize> = used[i].iter().copied().collect();
        used_cids.sort_unstable();
        let mut nsig: HashMap<usize, String> =
            used_cids.iter().map(|&c| (c, String::new())).collect();
        let mut name_of: HashMap<usize, usize> = used_cids.iter().map(|&c| (c, 0)).collect();
        let mut stable = used_cids.is_empty();
        for _ in 0..=used_cids.len() + 1 {
            let temporary_names: HashMap<usize, String> = name_of
                .iter()
                .map(|(&cid, &name)| (cid, format!("{current_prefix}{name}")))
                .collect();
            for &cid in &used_cids {
                let chunk = format!(
                    "{}\u{1f}{}\u{1f}",
                    rename_scoped_class_refs(
                        &solutions[i].class_seed[&cid],
                        &current_prefix,
                        &temporary_names,
                    )?,
                    rename_scoped_class_refs(
                        &solutions[i].class_back[&cid],
                        &current_prefix,
                        &temporary_names,
                    )?
                );
                if nsig[&cid].len() + chunk.len() > MAX_EXPR_LEN {
                    return Err("expression too large".to_string());
                }
                nsig.get_mut(&cid).expect("used cid sig").push_str(&chunk);
            }
            let new_name_of = class_ids_of(&nsig, &used_cids);
            if new_name_of == name_of {
                stable = true;
                break;
            }
            name_of = new_name_of;
        }
        if !stable {
            return Err("loop-class canonical naming did not converge".to_string());
        }
        let mut names_seen: Vec<usize> = name_of.values().copied().collect();
        names_seen.sort_unstable();
        names_seen.dedup();
        if names_seen.len() != used_cids.len() {
            return Err(
                "ambiguous loop-class canonical naming (automorphic classes) outside fragment"
                    .to_string(),
            );
        }

        let replacements: HashMap<usize, String> = name_of
            .iter()
            .map(|(&cid, &name)| (cid, format!("l{}h{name}", g.final_of[&solutions[i].header])))
            .collect();
        for line in &mut term_lines {
            *line = rename_scoped_class_refs(line, &current_prefix, &replacements)?;
        }
        for j in 0..solutions.len() {
            let live: Vec<usize> = used[j].iter().copied().collect();
            for cid in live {
                let seed = solutions[j]
                    .class_seed
                    .get_mut(&cid)
                    .ok_or_else(|| "live class lost its seed".to_string())?;
                *seed = rename_scoped_class_refs(seed, &current_prefix, &replacements)?;
                let back = solutions[j]
                    .class_back
                    .get_mut(&cid)
                    .ok_or_else(|| "live class lost its back transition".to_string())?;
                *back = rename_scoped_class_refs(back, &current_prefix, &replacements)?;
            }
        }
        final_names.push(name_of);
    }

    let mut loop_lines = Vec::<String>::new();
    for (i, solution) in solutions.iter().enumerate() {
        let mut emit_order: Vec<usize> = used[i].iter().copied().collect();
        emit_order.sort_unstable_by_key(|cid| final_names[i][cid]);
        for cid in emit_order {
            let token = format!("l{}h{}", g.final_of[&solution.header], final_names[i][&cid]);
            loop_lines.push(format!(
                "loop@b{} {token}: seed={} back={}",
                g.final_of[&solution.header], solution.class_seed[&cid], solution.class_back[&cid]
            ));
        }
    }
    Ok((term_lines, loop_lines))
}

/// Collect class ids bearing one exact sequential-loop namespace.
fn collect_scoped_class_refs(s: &str, prefix: &str, used: &mut HashSet<usize>) -> CanonResult<()> {
    let bytes = s.as_bytes();
    let prefix_bytes = prefix.as_bytes();
    let mut i = 0usize;
    while i + prefix_bytes.len() < bytes.len() {
        if bytes[i..].starts_with(prefix_bytes) {
            let start = i + prefix_bytes.len();
            let mut end = start;
            while end < bytes.len() && bytes[end].is_ascii_digit() {
                end += 1;
            }
            if end > start && (end == bytes.len() || !bytes[end].is_ascii_alphanumeric()) {
                let cid = s[start..end]
                    .parse::<usize>()
                    .map_err(|_| "scoped class-name token overflows usize".to_string())?;
                used.insert(cid);
                i = end;
                continue;
            }
        }
        i += 1;
    }
    Ok(())
}

/// Rewrite one exact sequential-loop token namespace. Every observed token
/// must be in `replacements`; global liveness closure guarantees this for
/// retained observables and definitions, so absence is a fail-closed internal
/// inconsistency rather than an invitation to leave a raw temporary token.
fn rename_scoped_class_refs(
    s: &str,
    prefix: &str,
    replacements: &HashMap<usize, String>,
) -> CanonResult<String> {
    let bytes = s.as_bytes();
    let prefix_bytes = prefix.as_bytes();
    let mut out = Vec::<u8>::with_capacity(bytes.len());
    let mut i = 0usize;
    while i < bytes.len() {
        if i + prefix_bytes.len() < bytes.len() && bytes[i..].starts_with(prefix_bytes) {
            let start = i + prefix_bytes.len();
            let mut end = start;
            while end < bytes.len() && bytes[end].is_ascii_digit() {
                end += 1;
            }
            if end > start && (end == bytes.len() || !bytes[end].is_ascii_alphanumeric()) {
                let cid = s[start..end]
                    .parse::<usize>()
                    .map_err(|_| "scoped class-name token overflows usize".to_string())?;
                let replacement = replacements.get(&cid).ok_or_else(|| {
                    format!("class {prefix}{cid} referenced but not canonically named")
                })?;
                out.extend_from_slice(replacement.as_bytes());
                i = end;
                continue;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8(out).map_err(|_| "non-UTF8 canonical line".to_string())
}

/// Collect every `h<digits>` class-name token in `s` (token boundaries: the `h` must not be
/// preceded by an alphanumeric, and the digits must not be followed by one — so `chk(`/
/// `phi[`/`switch(` never match and `h10` never counts as `h1`).
fn collect_class_refs(s: &str, used: &mut HashSet<usize>) {
    let b = s.as_bytes();
    let mut i = 0usize;
    while i < b.len() {
        if b[i] == b'h' && (i == 0 || !b[i - 1].is_ascii_alphanumeric()) {
            let mut j = i + 1;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 && (j == b.len() || !b[j].is_ascii_alphanumeric()) {
                if let Ok(cid) = s[i + 1..j].parse::<usize>() {
                    used.insert(cid);
                }
                i = j;
                continue;
            }
        }
        i += 1;
    }
}

/// Rewrite every `h<digits>` class-name token in `s` (identical token boundaries to
/// `collect_class_refs`) to `h<map[cid]>`. A referenced cid missing from `map` fails closed
/// (an emitted line may only reference canonically-named — used — classes; transitive
/// pruning closure guarantees this, the error is defensive). Non-token bytes are copied
/// verbatim (byte-level, so any non-ASCII `Debug` payload survives untouched — a token
/// match is pure ASCII, so UTF-8 well-formedness is preserved).
fn rename_class_refs(s: &str, map: &HashMap<usize, usize>) -> CanonResult<String> {
    let b = s.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(b.len());
    let mut i = 0usize;
    while i < b.len() {
        if b[i] == b'h' && (i == 0 || !b[i - 1].is_ascii_alphanumeric()) {
            let mut j = i + 1;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 && (j == b.len() || !b[j].is_ascii_alphanumeric()) {
                let cid: usize = s[i + 1..j]
                    .parse()
                    .map_err(|_| "class-name token overflows usize".to_string())?;
                let name = map
                    .get(&cid)
                    .ok_or_else(|| format!("class h{cid} referenced but not canonically named"))?;
                out.extend_from_slice(format!("h{name}").as_bytes());
                i = j;
                continue;
            }
        }
        out.push(b[i]);
        i += 1;
    }
    String::from_utf8(out).map_err(|_| "non-UTF8 canonical line".to_string())
}

/// Apply one kept (pure `Assign`) statement to the symbolic state. See the module docs for
/// the alias (borrow) rules; everything unexpected fails closed.
fn apply_stmt(
    body: &VerifiableBody,
    s: &Statement,
    env: &mut Env,
    norms: &NormCounter,
) -> CanonResult<()> {
    let Statement::Assign { place, rvalue, .. } = s else {
        unreachable!("filter kept only Assign");
    };
    match place.projections.as_slice() {
        [] => {
            // Trust (T2c): ONE authoritative point where a bare destination is rebound, so the
            // "a local is never in both alias maps" invariant that `place_expr`'s ref_places-first
            // lookup depends on is STRUCTURAL rather than the sum of per-rvalue removals. The
            // audit found three rvalue kinds (bare-local borrow, both reborrow branches) that
            // wrote `vals`/`refs` without dropping a stale place alias; siting the drop here
            // covers every present and future rvalue arm. The binding arm below re-inserts after
            // this, so a genuine payload borrow is unaffected.
            env.ref_places.remove(&place.local);
            if let Rvalue::Ref { place: rp, .. } = rvalue {
                match rp.projections.as_slice() {
                    // Borrow of a BARE local: a pure DEREF alias binding, observable only
                    // through Deref (any by-value use of the ref local fails closed). LEDGER L7.
                    [] => {
                        norms.fire(NORM_REF_ALIAS);
                        env.vals.remove(&place.local);
                        env.refs.insert(place.local, rp.local);
                        return Ok(());
                    }
                    // Trust (wave-8a): a REBORROW `_dst = &(*_src)` — `_dst` IS the same reference
                    // VALUE as `_src` (same address + provenance), so a by-value forward of `_dst`
                    // (`f(move _dst)`) renders identically to forwarding `_src`. This is what makes
                    // built's `_2 = &(*_1); f(move _2)` congruent with the shim's DIRECT forward
                    // `f(_1)`. Bind `_dst` to `_src`'s rendered VALUE (a param `a{i}` or a prior
                    // reborrow); a `_src` that is itself only a deref-alias reborrows to the SAME
                    // deref-alias. LEDGER L7 (reborrow sub-case).
                    [Projection::Deref] => {
                        norms.fire(NORM_REF_ALIAS);
                        if let Some(sym) = env.vals.get(&rp.local).cloned() {
                            env.refs.remove(&place.local);
                            // Trust (T2c): rebinding the local must also drop any PLACE alias, or a stale
                            // alias would resolve a later read to a place this local no longer denotes.
                            env.ref_places.remove(&place.local);
                            env.vals.insert(place.local, sym);
                            return Ok(());
                        }
                        if let Some(&tgt) = env.refs.get(&rp.local) {
                            env.vals.remove(&place.local);
                            env.refs.insert(place.local, tgt);
                            return Ok(());
                        }
                        // Trust (T2d): a reborrow of a PAYLOAD-ALIAS local — `_dst = &(*_src)`
                        // where `_src = &(((*_p) as V).k)`. rustc emits this between binding a
                        // by-ref match arm's payload and passing it on (`deref(&self.0)` inside
                        // `Level::is_zero`'s `Max` arm), and it is the third alias map's missing
                        // case: `_src` lives in `ref_places`, so neither lookup above found it.
                        //
                        // A SHARED reborrow denotes the SAME place as its source — `&(*_src)` is
                        // the address `_src` already holds — so `_dst` is bound to the SAME stored
                        // place, not to a copy of a rendered string. Lazy resolution is therefore
                        // preserved exactly: a later read through `_dst` re-renders the borrowed
                        // place at the read, identically to a read through `_src`, and inherits
                        // the root-stability the binding arm proved for it (shared-ref PARAM root,
                        // `local_ever_written` false). No new admission: this arm cannot introduce
                        // a place alias the `[Deref, Downcast, Field]` binding arm did not already
                        // gate, it only propagates one along a reborrow edge.
                        if let Some(target) = env.ref_places.get(&rp.local).cloned() {
                            env.vals.remove(&place.local);
                            env.refs.remove(&place.local);
                            env.ref_places.insert(place.local, target);
                            return Ok(());
                        }
                        return Err(format!(
                            "reborrow of untracked ref _{} outside fragment",
                            rp.local
                        ));
                    }
                    // Trust (wave-29, interior-borrow-return FLIP): an interior shared borrow of a
                    // ref-param struct FIELD — `_dst = &((*_p).K)` — the READ twin of wave-24's
                    // field store. The producer erased this to a bare-ptr `return pv` (wave-25,
                    // offset-0), so the shim reconstructs the real `[Deref, Field(K)]` borrow
                    // (`to_mir::reconstruct_interior_borrow`); BOTH sides then carry this exact MIR
                    // and render IDENTICALLY. Bound to the DISCRIMINATING symbolic value
                    // `iref(a{p},K)` — a wrong field index K renders a different line → mismatch →
                    // no flip (a wrong interior address is never accepted, per
                    // [[flip-needs-caller-memory-observable]]). The field TYPE / offset is not
                    // consulted here (the comparator is tcx-free); the shim (which has tcx) does the
                    // offset→field reconstruction and the flip gate re-certifies the [Deref,
                    // Field(scalar)] shape, so this arm only pins K equal on both sides.
                    [Projection::Deref, Projection::Field(k)] => {
                        let p = rp.local;
                        // The base must be a shared-ref PARAM (a genuine caller pointer — the
                        // producer's `ref_param_ptrs`). A `&mut`/raw-ptr base or an in-body ref
                        // (referent is a local snapshot) is out of slice → fail closed.
                        let is_shared_ref_param = p >= 1
                            && p <= body.arg_count
                            && body.locals.get(p).is_some_and(|d| {
                                d.index == p && matches!(d.ty, Ty::Ref { mutable: false, .. })
                            });
                        if !is_shared_ref_param {
                            return Err(
                                "interior borrow base is not a shared ref param outside fragment"
                                    .to_string(),
                            );
                        }
                        let base = env.vals.get(&p).cloned().ok_or_else(|| {
                            format!("interior borrow of untracked ref param _{p}")
                        })?;
                        norms.fire(NORM_INTERIOR_BORROW);
                        env.refs.remove(&place.local);
                        // Trust (T2c): rebinding the local must also drop any PLACE alias, or a stale
                        // alias would resolve a later read to a place this local no longer denotes.
                        env.ref_places.remove(&place.local);
                        env.vals.insert(place.local, format!("iref({base},{k})"));
                        return Ok(());
                    }
                    // Trust (T2c, gate 3): the ENUM-PAYLOAD binding `_dst = &(((*_p) as V).k)` —
                    // what rustc emits for `match self { E::A(x) => .. }` on a `&E`. This is the
                    // wave-29 interior borrow with a `Downcast` in the middle, and it is the last
                    // gate between a by-ref payload match and the flip.
                    //
                    // Bound as a PLACE alias, NOT as an opaque `iref(..)` value like wave-29's.
                    // That difference is forced by what the two sides emit: for the RETURN of an
                    // interior reference (wave-29) both sides carry the borrow, so an opaque
                    // discriminating symbol suffices; in T2c's READ case the derived side carries
                    // no borrow at all (the shim binds the payload directly to `((*P) as V).k`),
                    // so the built side's borrow-then-read has to render as the read it is.
                    // `place_expr` re-renders the stored place at the read, so the two sides
                    // produce the same string exactly when they name the same variant and field —
                    // a wrong `V` or `k` still renders differently and still mismatches.
                    //
                    // Trust (T2d): the ADDRESS-forwarding case joined this arm without changing
                    // it. There the shim DOES reconstruct the borrow on the derived side, so both
                    // sides bind here and both then use the local by value; `place_expr`'s bare
                    // by-value arm renders that use by re-rendering this same stored place. One
                    // binding, two read shapes — the local is still never in both alias maps, so
                    // `place_expr`'s ref_places-first lookup keeps its structural justification.
                    //
                    // Same base requirement as wave-29 and for the same reason: a shared-ref PARAM
                    // is a genuine caller pointer whose referent cannot be written during the body,
                    // so the alias cannot go stale. A `&mut` / raw-ptr / in-body-ref base is out.
                    [Projection::Deref, Projection::Downcast(_), Projection::Field(_)] => {
                        let p = rp.local;
                        let is_shared_ref_param = p >= 1
                            && p <= body.arg_count
                            && body.locals.get(p).is_some_and(|d| {
                                d.index == p && matches!(d.ty, Ty::Ref { mutable: false, .. })
                            });
                        if !is_shared_ref_param {
                            return Err(
                                "payload borrow base is not a shared ref param outside fragment"
                                    .to_string(),
                            );
                        }
                        // The base must already be a tracked ref-param value; without it
                        // `place_expr` could not render the alias at read time either.
                        if !env.vals.contains_key(&p) {
                            return Err(format!("payload borrow of untracked ref param _{p}"));
                        }
                        // The alias is resolved LAZILY, so the base must be STABLE: see
                        // `local_ever_written`. A rebindable base would let the read resolve
                        // against a different referent than the borrow took.
                        if local_ever_written(body, p) {
                            return Err(format!(
                                "payload borrow base _{p} is reassigned in this body"
                            ));
                        }
                        norms.fire(NORM_INTERIOR_BORROW);
                        env.vals.remove(&place.local);
                        env.refs.remove(&place.local);
                        // Trust (T2c): rebinding the local must also drop any PLACE alias, or a stale
                        // alias would resolve a later read to a place this local no longer denotes.
                        env.ref_places.remove(&place.local);
                        env.ref_places.insert(place.local, rp.clone());
                        return Ok(());
                    }
                    _ => {
                        return Err("borrow of a projected place outside fragment".to_string());
                    }
                }
            }
            // LEDGER L5: this pure assign is absorbed into symbolic state (never rendered
            // as a statement observable).
            norms.fire(NORM_LOCAL_ELIM);
            let expr = rvalue_expr(body, rvalue, place.local, env, norms)?;
            if expr.len() > MAX_EXPR_LEN {
                return Err("expression too large".to_string());
            }
            env.refs.remove(&place.local);
            // Trust (T2c): rebinding the local must also drop any PLACE alias, or a stale
            // alias would resolve a later read to a place this local no longer denotes.
            env.ref_places.remove(&place.local);
            env.vals.insert(place.local, expr);
        }
        [Projection::Deref] => {
            // LEDGER L5+L7: a deref-store absorbed through the alias binding.
            norms.fire(NORM_LOCAL_ELIM);
            let target = *env.refs.get(&place.local).ok_or_else(|| {
                format!("deref-store through untracked ref local _{}", place.local)
            })?;
            if matches!(rvalue, Rvalue::Ref { .. }) {
                return Err("borrow stored through a deref outside fragment".to_string());
            }
            let expr = rvalue_expr(body, rvalue, target, env, norms)?;
            if expr.len() > MAX_EXPR_LEN {
                return Err("expression too large".to_string());
            }
            env.refs.remove(&target);
            env.vals.insert(target, expr);
        }
        // Trust (wave-24 → B10, ref-escape FLIP-COHERENCE): a `(*_param).field = v` store through
        // a `&mut Struct` PARAM — the ref-escape write made flippable. Recorded as an explicit,
        // DISCRIMINATING, ORDERED caller-memory effect (`memseq`, program order), emitted on the
        // return observable — NOT folded into `vals` (see the `Env::memseq` doc: the
        // invisible-store miscompile trap). FIRST SLICE — every gate fails closed (the whole
        // body → DerivedUnsupported → no flip):
        [Projection::Deref, Projection::Field(fld)] => {
            let p = place.local;
            // (i) the base must be a `&mut`-typed ARG param. An in-body `&mut local` (referent is a
            //     local) or a shared `&T` is out of slice — a field store through those is not modeled.
            let is_mut_ref_param = p >= 1
                && p <= body.arg_count
                && body
                    .locals
                    .get(p)
                    .is_some_and(|d| d.index == p && matches!(d.ty, Ty::Ref { mutable: true, .. }));
            if !is_mut_ref_param {
                return Err("field store through a non-&mut-param place outside slice".to_string());
            }
            // (ii) never store a BORROW into the struct (a pointer aliasing caller/callee data).
            if matches!(rvalue, Rvalue::Ref { .. }) {
                return Err("borrow stored through a param field outside slice".to_string());
            }
            // (iii) single field write per param (single-field slice); a second store fails closed.
            if env.memseq.iter().any(|(pp, _, _)| *pp == p) {
                return Err("multiple stores through a &mut param outside slice".to_string());
            }
            // The stored value is rendered symbolically (a param `a{i}`, a binop of them, …). The
            // `dest_local=p` only feeds `dest_ty()` for cast/aggregate rvalues, which are outside the
            // scalar-store slice and fail closed there — a plain `Use`/`BinaryOp` never reads it.
            // Trust (B10): `rvalue_expr` runs BEFORE the push, so a param-deref read inside the
            // store's own rvalue correctly gets the PRE-store epoch.
            let expr = rvalue_expr(body, rvalue, p, env, norms)?;
            if expr.len() > MAX_EXPR_LEN {
                return Err("expression too large".to_string());
            }
            env.memseq.push((p, *fld, expr));
        }
        _ => return Err("projected assignment destination outside fragment".to_string()),
    }
    Ok(())
}

/// Trust (wave-24 → B10): render the caller-memory effect (`&mut`-param field stores) captured
/// in `env.memseq` as a canonical suffix on the return observable. EMPTY when no `&mut`-param
/// store occurred — so a body with no ref-escape write renders a byte-identical return line
/// (zero regression). Trust (B10): rendered IN PROGRAM ORDER with explicit sequence indices
/// (`|mem[m0:p2.0=..;m1:p3.2=..]`) — ORDER IS THE OBSERVABLE; do NOT re-sort this (a "stable
/// rendering" cleanup that sorts it silently reintroduces the wave-S reorder-blindness). The
/// index is redundant with position today but makes the reorder-SAT diff loud and future-proofs
/// the format for B4 joins. A wrong field/value/param/ORDER on the derived side renders a
/// DIFFERENT suffix → the exact-equality gate rejects it.
fn render_memout(env: &Env) -> String {
    if env.memseq.is_empty() {
        return String::new();
    }
    let body = env
        .memseq
        .iter()
        .enumerate()
        .map(|(i, (p, fld, expr))| format!("m{i}:p{p}.{fld}={expr}"))
        .collect::<Vec<_>>()
        .join(";");
    format!("|mem[{body}]")
}

/// Canonical rendering of a `trust_types::Ty` in the scalar(-tuple) fragment.
fn canon_ty(ty: &Ty) -> CanonResult<String> {
    match ty {
        Ty::Bool => Ok("bool".to_string()),
        Ty::Int { width, signed } => Ok(format!("{}{}", if *signed { "i" } else { "u" }, width)),
        // Trust (v25 B1): faithful scalar witnesses. DISTINCT tokens from the
        // width-collapsed carriers (isize != i64, char != u32) — both sides of
        // the comparison now extract through the FAITHFUL lane (the built side
        // via the interpreter differential's shared snapshot, the derived side
        // via `extract_function_faithful` in `compare_derived`), so the tokens
        // compare the same spelling of the same rustc type; a faithful-vs-
        // carrier mix is a real asymmetry and must MISMATCH, never alias.
        Ty::PtrSizedInt { signed } => Ok(if *signed { "isize" } else { "usize" }.to_string()),
        Ty::Char => Ok("char".to_string()),
        // Trust (wave-FL): float scalar witness. Distinct f32/f64 tokens (the width prevents any
        // cross-width confusion). The derived float local's type is threaded byte-for-byte from the
        // built local (the ABI gate re-pins them equal), so this is a witness of the IDENTICAL type
        // on both sides, never a discriminator — the VALUE is discriminated in `const_expr` (fbits).
        Ty::Float { width } => Ok(format!("f{width}")),
        Ty::Unit => Ok("()".to_string()),
        Ty::Tuple(elems) => {
            let mut parts: Vec<String> = Vec::with_capacity(elems.len());
            for e in elems {
                parts.push(canon_ty(e)?);
            }
            Ok(format!("({})", parts.join(",")))
        }
        // Trust (wave-D, Drop-free aggregate constructor-return FLIP): a STRUCT `_0` decl witness.
        // `variants.is_empty()` restricts to structs (an ENUM `Ty::Adt` — non-empty variants —
        // falls through to fail closed). Rendered by NAME only (`safe_def_path_str`, the fully
        // qualified def path — collision-free) with NO field recursion: this is a DECL line for
        // `_0`, whose derived type is threaded byte-for-byte from the built `_0` type (the ABI gate
        // re-pins them equal), so both sides render the IDENTICAL string of the IDENTICAL type — it
        // is a witness, never a discriminator. The field VALUES are discriminated where it matters,
        // in the `Rvalue::Aggregate` observable (`rvalue_expr`), not here.
        Ty::Adt { name, variants, .. } if variants.is_empty() => Ok(format!("adt:{name}")),
        // Trust (wave-V, fieldless-enum discriminant-read FLIP; enum arc slice 1, payload enums): an
        // enum decl WITNESS (`_1: E` on BOTH sides — the shim declares the derived enum param with the
        // built enum type, so this line is a witness of the IDENTICAL type, never a discriminator).
        // Rendered by NAME only (the fully qualified def path — collision-free) with NO field/variant
        // recursion. Wave-V restricted this to FIELDLESS enums; enum arc slice 1 admits a PAYLOAD enum
        // too (`enum E { A(i32), B(bool) }`), because the render is a witness of a type threaded
        // byte-for-byte from built to derived — the VALUES are discriminated where it matters: the
        // discriminant in the `Rvalue::Discriminant` observable + the reshaped `SwitchInt` tag set,
        // and (slice 2) a payload in the `Downcast`+`Field` place observable. A payload never flows
        // into a canonical value through this line — it only names the arg-decl type. `variants`
        // non-empty keeps STRUCTS on the `adt:{name}` arm above.
        Ty::Adt { name, variants, .. } if !variants.is_empty() => Ok(format!("enum:{name}")),
        other => Err(format!("type outside fragment: {other:?}")),
    }
}

/// Canonical rendering of an arg-local DECLARATION type: the value fragment (`canon_ty`)
/// plus the slice-3 OPAQUE param classes — references / raw pointers (closure envs `&{closure}`,
/// plain refs) and zero-upvar by-value closures (`FnOnce` env ZSTs). Opaque classes are
/// rendered via the full structural `Debug` form (deterministic, collision-free for these
/// shapes), prefixed `opaque:`. SOUNDNESS: this widening applies to arg-declaration LINES
/// only; every VALUE position still renders through `canon_ty`, so an opaque-typed value can
/// never flow into an op observable — and the derived side's decl is threaded byte-for-byte
/// from the built side's rustc type, so the two lines compare the SAME conversion of the SAME
/// type. Everything else stays fail-closed.
fn canon_param_ty(ty: &Ty) -> CanonResult<String> {
    if let Ok(s) = canon_ty(ty) {
        return Ok(s);
    }
    match ty {
        Ty::Ref { .. } | Ty::RawPtr { .. } => Ok(format!("opaque:{ty:?}")),
        Ty::Closure { upvars, .. } if upvars.is_empty() => Ok(format!("opaque:{ty:?}")),
        other => Err(format!("param type outside fragment: {other:?}")),
    }
}

/// Canonical rendering of the RETURN-local (`_0`) DECLARATION type: the value fragment
/// (`canon_ty`) plus the wave-15 opaque SHARED-reference return class — a `fn(..) -> &T { param }`
/// identity forward (`_0 = copy _p; return`). SOUNDNESS, identical to `canon_param_ty` for args:
/// the derived `_0` type is threaded byte-for-byte from the BUILT `_0` type (`compare_derived`
/// passes `built_ret_ty` into `to_mir`, which pins the derived return decl), so derived and built
/// render the SAME opaque string of the SAME rustc type — the DECL widening can never hide a
/// difference, and the return VALUE is still observed through `place_expr`/`env.vals` (a returned
/// ref that is NOT an identity-forwarded param routes `_0` into `env.refs` and fails closed at
/// "return with uninitialized _0"). Admits ONLY `&T` (shared): a `&mut T` / raw-ptr / fat-DST
/// return stays fail-closed, matching the flip's own `_0` gate (`flip.rs`, `m.is_not()`), so this
/// never manufactures a `DerivedAgreed` the flip would then reject as a loud fallback.
fn canon_ret_ty(ty: &Ty) -> CanonResult<String> {
    if let Ok(s) = canon_ty(ty) {
        return Ok(s);
    }
    match ty {
        Ty::Ref { mutable: false, .. } => Ok(format!("opaque:{ty:?}")),
        other => Err(format!("return type outside fragment: {other:?}")),
    }
}

/// Trust (T2c, HIGH fix): is `local` ever WRITTEN anywhere in the body?
///
/// This is the guard the place-alias needs and the one its first version was missing. The
/// justification for resolving a `ref_places` alias LAZILY is that the borrowed place renders the
/// same at the read as at the borrow. "The root is a shared-ref param, so the referent is
/// immutable" establishes that nobody writes THROUGH `_p` — it says nothing about `_p` ITSELF,
/// which in MIR is an ordinary mutable local. rustc accepts
///
///     pub enum E { A(u32), B }
///
///     pub fn f<'a>(mut p: &'a E, q: &'a E) -> u32 {
///         if let E::A(x) = p { p = q; return *x; }   // `_4 = &(((*_1) as A).0); _1 = copy _2;`
///         0
///     }
///
/// where the reborrow `_4` still denotes the ORIGINAL referent while `_1` has been rebound. A lazy
/// re-render would resolve `_1` at the read and canonicalize the built side to the WRONG referent.
/// Requiring the root to be write-free makes `env.vals[root]` constant along every path, so
/// read-time and borrow-time renderings coincide — which is exactly the property the lazy
/// resolution assumes. A body that does rebind the base fails closed instead.
fn local_ever_written(body: &VerifiableBody, local: usize) -> bool {
    body.blocks.iter().any(|bb| {
        bb.stmts.iter().any(|st| match st {
            Statement::Assign { place, .. } => place.local == local,
            Statement::SetDiscriminant { place, .. } => place.local == local,
            _ => false,
        }) || match &bb.terminator {
            Terminator::Call { dest, .. } => dest.local == local,
            _ => false,
        }
    })
}

/// Symbolic expression for reading `place` in `env`. A leading `Deref` resolves through the
/// alias map (fail-closed when untracked); any OTHER use of an alias-bound local errors — with
/// ONE exception, added by T2d: a BARE by-value use of a `ref_places`-bound local (a payload
/// interior borrow rooted at a never-reassigned shared-ref param) renders as `ref(<the borrowed
/// place>)`. A by-value use of a `refs`-bound local — the reference value genuinely escaping the
/// fragment — still errors.
fn place_expr(place: &Place, env: &Env) -> CanonResult<String> {
    let (base, projs): (usize, &[Projection]) = match place.projections.split_first() {
        // Trust (T2c, gate 3): a PLACE alias (`_r = &(((*_p) as V).k)`) resolves by re-rendering
        // the borrowed place HERE, at the read, then applying whatever projections the read adds
        // on top. Checked before `refs`/`vals` because the two maps are disjoint by construction
        // (the binding arm removes the local from both). Re-rendering rather than replaying a
        // frozen string is what makes this read identical to the derived side's direct read of the
        // same place, epoch stamping included.
        Some((Projection::Deref, rest)) if env.ref_places.contains_key(&place.local) => {
            let target = env.ref_places[&place.local].clone();
            let mut expr = place_expr(&target, env)?;
            for p in rest {
                match p {
                    Projection::Field(k) => expr = format!("fld({expr},{k})"),
                    Projection::Downcast(v) => expr = format!("downcast({expr},{v})"),
                    _ => {
                        return Err("projection after payload-alias outside fragment".to_string());
                    }
                }
            }
            return Ok(expr);
        }
        // Trust (T2d, gate 3): a BARE BY-VALUE use of a payload-alias local — `f(move _3)` where
        // `_3 = &(((*_p) as V).k)`. T2c left this failing closed as an "escape", which was right
        // when only the BUILT side carried the borrow: the derived side read the payload place
        // directly, so there was nothing for the escaped reference to agree WITH. The T2d shim
        // reconstructs the same borrow on the derived side (`to_mir` payload-ADDRESS arm) for a
        // payload whose address is forwarded to a call, so both sides now carry the identical
        // `Rvalue::Ref` and the identical by-value use, and the honest rendering of that use is
        // the address it denotes.
        //
        // Rendered by RE-RENDERING the borrowed place at the read, exactly as the Deref arm above
        // does, wrapped in `ref(..)` so an ADDRESS never collides with the VALUE at that address.
        // That composition is what makes it discriminating: `ref(fld(downcast(deref(a{p}),V),k))`
        // is injective in the base param, the variant AND the field, so a wrong `V` or `k` on
        // either side renders a different string → mismatch → no flip. This is the wave-29
        // `iref(a{p},k)` argument (which has admitted by-value escape of an interior borrow since
        // it landed) with the variant added, and it inherits T2c's two structural preconditions
        // unchanged, both enforced at the BINDING arm: the root is a SHARED-ref PARAM (a genuine
        // caller address, not a local snapshot whose address escaping would mean something else),
        // and `local_ever_written` proved that root is never reassigned, so the lazy re-render
        // cannot resolve against a different referent than the borrow took.
        //
        // BARE uses only (`projections` empty). A `refs`-bound local is deliberately NOT given
        // this treatment and still fails closed below: `refs` maps local -> LOCAL, so its referent
        // is a body-local snapshot rather than a caller pointer, and none of the above applies.
        None if env.ref_places.contains_key(&place.local) => {
            let target = env.ref_places[&place.local].clone();
            let inner = place_expr(&target, env)?;
            return Ok(format!("ref({inner})"));
        }
        Some((Projection::Deref, rest)) => {
            match env.refs.get(&place.local) {
                // An aliased ref (`_2 = &_1`) resolves through the alias map to its target place.
                Some(tgt) => (*tgt, rest),
                // Trust (wave-S): a SHARED-ref PARAM read (`*_p`) — the param is seeded in `env.vals`
                // (as `a{p}`), never in `env.refs`. Render `deref(a{p})` SYMMETRICALLY on both the
                // built and derived sides (the shim emits `copy (*_p)` for exactly this shape), so a
                // read of the SAME param agrees and a read of a DIFFERENT param (mis-route) renders a
                // different symbol → mismatch. Broader than shared-ref-params in isolation, but the
                // shim (which has `tcx`) gates the DERIVED side to shared-ref scalar only, and this
                // canon runs on the built side only after the shim SUCCEEDED, so it is only
                // consequential for admitted shapes. A trailing scalar field (`(*_p).k`) is pre-staged
                // for the deferred `self.0` getter; a nested deref / other projection fails closed.
                None => {
                    let val = env.vals.get(&place.local).ok_or_else(|| {
                        format!("deref-read through untracked ref local _{}", place.local)
                    })?;
                    // Trust (B10): stamp the read with the path's memory EPOCH (stores so far),
                    // elided at epoch 0 — so every store-free body renders byte-identically to
                    // before, while a read moved across a store renders a DIFFERENT token
                    // (retires the wave-S read/write reorder blindness). The epoch is baked into
                    // the string at READ time and travels through `vals`/phi/loop signatures
                    // like any sub-expression — the loaded value is the referent AT LOAD TIME.
                    let n = env.memseq.len();
                    let mut expr =
                        if n == 0 { format!("deref({val})") } else { format!("deref@m{n}({val})") };
                    for p in rest {
                        match p {
                            Projection::Field(k) => expr = format!("fld({expr},{k})"),
                            // Trust (T2b): a payload read through a SHARED-REF scrutinee —
                            // `((*_p) as V).k`. Rendered exactly as the aliased-ref branch below
                            // renders its `Downcast`, so the two spellings of the same read agree
                            // and a DIFFERENT variant renders a different symbol → mismatch. This
                            // arm is what the by-ref payload lane needs: without it the projection
                            // list `[Deref, Downcast, Field]` fell to the error below even though
                            // both `Deref` and the trailing `Field` were already understood.
                            Projection::Downcast(v) => expr = format!("downcast({expr},{v})"),
                            _ => {
                                return Err(
                                    "projection after param-deref outside fragment".to_string()
                                );
                            }
                        }
                    }
                    return Ok(expr);
                }
            }
        }
        _ => (place.local, place.projections.as_slice()),
    };
    let mut expr = env.vals.get(&base).cloned().ok_or_else(|| {
        // Trust (T2c/T2d): a `refs`-bound local read by value is a genuine escape (its referent is
        // a body-local snapshot) and still fails closed here. A `ref_places`-bound local reaches
        // this point ONLY through a PROJECTED use — a bare one was answered by the by-value arm
        // above — and a projection applied to a payload interior borrow is outside the fragment,
        // so the same message is still the right verdict for it.
        if env.refs.contains_key(&base) || env.ref_places.contains_key(&base) {
            format!("ref local _{base} used by value (escape) outside fragment")
        } else {
            format!("read of possibly-uninitialized local _{base}")
        }
    })?;
    for p in projs {
        match p {
            Projection::Field(k) => expr = format!("fld({expr},{k})"),
            // Trust (enum arc slice 2): a payload read `((_e as V).k)` — the `Downcast` selects
            // variant V. Rendered INJECTIVELY on the variant index (a wrong variant renders a
            // different symbol → canonical mismatch → no false flip); built and derived spell the
            // SAME source variant, so a correct shim `Downcast` agrees, and the trailing `Field(k)`
            // reads the payload scalar. Admits the payload-read place onto the value fragment; enum
            // construction / whole-value reads stay fail-closed elsewhere.
            Projection::Downcast(v) => expr = format!("downcast({expr},{v})"),
            Projection::Deref => {
                return Err("nested deref projection outside fragment".to_string());
            }
            other => return Err(format!("projection outside fragment: {other:?}")),
        }
    }
    Ok(expr)
}

/// Symbolic expression for an operand. `Copy` and `Move` both read the place's current value
/// (see module docs for why that is sound in this scalar fragment).
///
/// Trust (wave-GH2) L8 CAVEAT: the fold's original premise — "move-ness only matters to
/// borrowck/analysis, which never see the derived body" — is FALSE for one codegen-visible shape:
/// a MEMORY-ABI (indirectly passed) struct call ARG. codegen_ssa gives a memory-backed `Copy` arg
/// a defensive fresh-alloca+memcpy while `Move` passes the place's own address, so a Copy-vs-Move
/// skew there is correct-but-byte-DIVERGENT object code. The comparator deliberately KEEPS the
/// fold (canonical VALUE equality is the right semantics here); the parity is enforced where it
/// belongs: the shim re-spells one-shot struct call-result temps as `Move` (built's as_operand
/// discipline), and `flip.rs::gate_derived_body` fail-closes any residual memory-ABI whole-struct
/// `Copy` call arg. Immediate/Pair operands remain genuinely spelling-blind in codegen.
/// [`operand_expr`] for an operand in ARGUMENT position, told whether the callee's matching
/// parameter is `&T` with `T: Freeze` ([`ArgBorrowKind::Shared`]).
///
/// TODAY THIS IS EXACTLY `operand_expr`. `shared_exempt` is plumbed and honestly derived —
/// block-keyed ([`CallArgKinds`]), `Freeze`-guarded at the mint — but it grants NOTHING yet,
/// so this lane is behaviour-neutral by construction. That is deliberate, and it is the same
/// two-step [`arg_borrow_kinds_in_dfs_order`] used: land the fact, prove it changes nothing,
/// then change behaviour in a diff small enough to argue about.
///
/// WHAT THE EXEMPTION WOULD PERMIT. `place_expr` fails closed on a by-value read of a
/// `refs`-bound local — "ref local _N used by value (escape) outside fragment" — because the
/// referent is a body-local snapshot. `Shared` answers one objection to admitting it: the
/// callee provably cannot WRITE through the parameter, so the alias cannot be invalidated by
/// the call.
///
/// WHAT IT PERMITS, AND WHY THAT IS SOUND. `place_expr` fails closed on a by-value read of a
/// `refs`-bound local — "ref local _N used by value (escape) outside fragment" — because the
/// referent is a body-local snapshot and nothing invalidates `vals` if the callee writes
/// through the pointer. (The `Call` arm rebinds only `dest`; there is no havoc.) `Shared`
/// removes exactly that objection: `&T` with `T: Freeze` cannot be written through, so the
/// symbolic value of the referent survives the call unchanged.
///
/// The remaining objection is that "cannot write" is not "cannot observe" — a `&T` callee may
/// still `ptr::eq` the pointer. That is answered by HOW the address is rendered, not by
/// `Shared`: [`EscapeNames`] numbers each escaping local by first appearance, a BIJECTION that
/// preserves precisely which pointers are equal to which while discarding absolute addresses
/// no correct program can depend on. See its doc for the argument and for why the numbering is
/// body-global rather than per-call.
///
/// So the two halves are separate and both are needed: `Shared` licenses the VALUE surviving
/// the call, the bijection licenses the ADDRESS being rendered at all. Neither alone is enough,
/// which is why this stayed inert until the second one existed.
///
/// STILL FAILS CLOSED for everything else: a projected use of a `refs`-bound local, a
/// `ref_places` binding (those are answered earlier by `place_expr`'s own arms), a `Mut` or
/// `NotARef` parameter, and any call whose kinds were not recorded — an absent entry denies.
fn operand_expr_call_arg(
    op: &Operand,
    env: &Env,
    norms: &NormCounter,
    escapes: &EscapeNames,
    shared_exempt: bool,
) -> CanonResult<String> {
    if shared_exempt {
        // A BARE by-value read only. A projection on top of the reference is a different
        // idiom and keeps failing closed in `place_expr`, where it already does.
        if let Operand::Copy(p) | Operand::Move(p) = op {
            if p.projections.is_empty() {
                if let Some(&target) = env.refs.get(&p.local) {
                    // `ref(..)` so an ADDRESS can never collide with the VALUE at that
                    // address — the same wrapper the T2d arm uses for an interior borrow.
                    return Ok(format!("ref(e{})", escapes.name_of(target)));
                }
            }
        }
    }
    operand_expr(op, env, norms)
}

fn operand_expr(op: &Operand, env: &Env, norms: &NormCounter) -> CanonResult<String> {
    match op {
        Operand::Copy(p) => place_expr(p, env),
        Operand::Move(p) => {
            // LEDGER L8: a Move read as the place's current value (Copy semantics).
            norms.fire(NORM_MOVE_AS_COPY);
            place_expr(p, env)
        }
        Operand::Constant(cv) => const_expr(cv),
        Operand::Symbolic(_) => Err("symbolic operand".to_string()),
        Operand::Unsupported { kind, .. } => Err(format!("unsupported operand {kind}")),
        _ => Err("unknown operand variant".to_string()),
    }
}

fn const_expr(cv: &ConstValue) -> CanonResult<String> {
    match cv {
        ConstValue::Bool(b) => Ok(format!("c:bool:{b}")),
        ConstValue::Int(v) => Ok(format!("c:int:{v}")),
        ConstValue::Uint(v, w) => Ok(format!("c:uint:{v}:w{w}")),
        // Trust (wave-FL): float constants render by their EXACT IEEE bit pattern + width — an
        // INJECTIVE discriminator (distinct floats / NaN payloads / +0.0(0x0)≠-0.0(sign bit) all
        // differ; the `:w{width}` keeps an f32 low-bit pattern from colliding with an f64). BOTH
        // sides extract to `ConstValue::FloatBits` via trust-mir-extract, and built is ground truth,
        // so a wrong reconstructed float value renders a different token → DerivedMismatch → no flip
        // (AXIS-B closed). This is a discriminator, NOT a normalization.
        ConstValue::FloatBits { bits, width } => Ok(format!("c:fbits:{bits}:w{width}")),
        ConstValue::Unit => Ok("c:unit".to_string()),
        ConstValue::CallableItem { def_path, kind, def_path_hash } => Ok(format!(
            "c:callable:{}",
            ConstValue::callable_smt_var_name(def_path, *kind, *def_path_hash)
        )),
        // Trust (wave-str, `&str`-LITERAL-RETURN FLIP): a `&str` literal, rendered as INJECTIVE
        // lowercase-hex over its UTF-8 bytes — "Alpha" (416c706861) ≠ "Beta" (42657461) ≠ "" — so a
        // wrong reconstruction (different bytes/length) can never canonicalize to the built value
        // (AXIS B). Built `_0 = const "..."` and the shim's re-emitted `&str` const both extract to
        // `ConstValue::Str { bytes }` (trust-mir-extract convert.rs), so this arm renders both sides.
        ConstValue::Str { bytes } => {
            Ok(format!("c:str:{}", bytes.iter().map(|b| format!("{b:02x}")).collect::<String>()))
        }
        other => Err(format!("constant outside fragment: {other:?}")),
    }
}

/// The EXACT storage-marker channel (module docs step 5; LEDGER L2 retirement): render every
/// `StorageLive`/`StorageDead` of `body` as one line, in a deterministic fine-grained walk.
/// Compared line-for-line between derived and built by `compare_derived`; any inequality (or
/// fail-closed error) makes the body flip-ineligible at `-O` (`markers_exact = false`).
///
/// Exactness properties:
///   * The walk is a DFS preorder over the RAW CFG (no goto threading): successor order is
///     switch cases in listed order, then otherwise; assert success edge; goto target. Both
///     sides are walked by the identical rule, so fine block indices correspond iff the raw
///     block structures correspond.
///   * A marker line carries (fine block index, number of `Assign`s already seen in that
///     block, live/dead, alpha local name, declared local type). Relative order of adjacent
///     markers is preserved by line order; position relative to every value statement is
///     pinned by the assign count. `Nop`/`PlaceMention` do not advance the position — they
///     emit no code, so marker-vs-code order is unaffected (LEDGER L1 applies to them).
///   * Local names are alpha-renamed by first marker appearance (LEDGER L13): a bijective
///     renaming of storage slots is observationally identical for `llvm.lifetime` intrinsics
///     (per-slot semantics); event order, positions, and types are still exact.
///   * Blocks OUTSIDE the walk (assert-unwind cleanup subgraphs, dead code) must be
///     marker-free, else the channel fails closed — a marker can never hide there.
fn canon_markers(body: &VerifiableBody) -> CanonResult<Vec<String>> {
    if body.blocks.is_empty() {
        return Err("empty body".to_string());
    }
    for (i, bb) in body.blocks.iter().enumerate() {
        if bb.id.0 != i {
            return Err("misindexed basic block".to_string());
        }
    }
    let raw_succs = |i: usize| -> CanonResult<Vec<usize>> {
        Ok(match &body.blocks[i].terminator {
            Terminator::Goto(t) => vec![t.0],
            Terminator::SwitchInt { targets, otherwise, .. } => {
                let mut v: Vec<usize> = targets.iter().map(|(_, t)| t.0).collect();
                v.push(otherwise.0);
                v
            }
            Terminator::Assert { target, .. } => vec![target.0],
            Terminator::Return | Terminator::Unreachable => vec![],
            // Trust (wave-6): a direct call's fine-walk successor is its return target
            // (extraction already dropped the unwind edge; the raw call channel verified
            // the built unwind's benign lone-resume shape, which is marker-free — and the
            // unwalked-block sweep below refuses markers there regardless).
            Terminator::Call { target: Some(t), .. } => vec![t.0],
            Terminator::Call { target: None, .. } => {
                return Err("diverging Call (no return target) outside fragment".to_string());
            }
            Terminator::Drop { .. } => return Err("Drop terminator".to_string()),
            Terminator::Opaque { kind, .. } => return Err(format!("Opaque terminator {kind}")),
            Terminator::Resume => return Err("Resume terminator".to_string()),
            _ => return Err("unknown terminator variant".to_string()),
        })
    };
    // DFS preorder over raw successors; children pushed in reverse so the first successor
    // is visited first (the same discipline as the semantic channel's canonical numbering).
    let mut fine_of: HashMap<usize, usize> = HashMap::new();
    let mut fine_order: Vec<usize> = Vec::new();
    let mut work = vec![0usize];
    while let Some(b) = work.pop() {
        if fine_of.contains_key(&b) {
            continue;
        }
        if b >= body.blocks.len() {
            return Err("branch target out of range".to_string());
        }
        fine_of.insert(b, fine_order.len());
        fine_order.push(b);
        for s in raw_succs(b)?.into_iter().rev() {
            if s >= body.blocks.len() {
                return Err("branch target out of range".to_string());
            }
            if !fine_of.contains_key(&s) {
                work.push(s);
            }
        }
    }
    let mut out: Vec<String> = Vec::new();
    let mut names: HashMap<usize, usize> = HashMap::new();
    for (fine, &b) in fine_order.iter().enumerate() {
        let mut assigns_seen = 0usize;
        for s in &body.blocks[b].stmts {
            let (local, live) = match s {
                Statement::Assign { .. } => {
                    assigns_seen += 1;
                    continue;
                }
                Statement::StorageLive(l) => (*l, true),
                Statement::StorageDead(l) => (*l, false),
                // Position-neutral (no code emitted; LEDGER L1). Everything the semantic
                // channel refuses is refused here too — same fail-closed fragment.
                Statement::Nop | Statement::PlaceMention(_) => continue,
                Statement::Coverage => {
                    return Err(
                        "Coverage statement (instrument-coverage) outside fragment".to_string()
                    );
                }
                Statement::ConstEvalCounter => {
                    return Err("ConstEvalCounter statement (post-built ctfe_limit pass) \
                                cannot occur in mir_built output"
                        .to_string());
                }
                Statement::SetDiscriminant { .. } => return Err("SetDiscriminant".to_string()),
                Statement::Deinit { .. } => return Err("Deinit".to_string()),
                Statement::Retag { .. } => return Err("Retag".to_string()),
                Statement::Intrinsic { .. } => return Err("Intrinsic statement".to_string()),
                Statement::Unsupported { kind, .. } => {
                    return Err(format!("unsupported statement {kind}"));
                }
                _ => return Err("unknown statement variant".to_string()),
            };
            let next = names.len();
            let alpha = *names.entry(local).or_insert(next);
            let decl = body
                .locals
                .get(local)
                .filter(|d| d.index == local)
                .ok_or_else(|| format!("marker on missing local _{local}"))?;
            out.push(format!(
                "mk b{fine}.{assigns_seen}:{} s{alpha}:{}",
                if live { "live" } else { "dead" },
                canon_param_ty(&decl.ty)?
            ));
        }
    }
    // Fail-closed: no marker may hide in a block the walk never reaches (cleanup/dead code).
    //
    // Trust (2026-08-11): the same sweep now refuses a DROP TERMINATOR there, and that is a hole
    // being closed rather than a new rule. `Terminator::Drop` is refused on the walked path
    // (`raw_succs`, this file), but an unwalked CLEANUP block was reached by no channel at all:
    // `is_cleanup` is consulted exactly ONCE in this file (inside `benign_unwind`), which is
    // reachable only from `raw_calls_in_dfs_order`, and `raw_call_channel` short-circuits with
    // `if !has_call(built) && !has_call(derived) { return Ok(()) }` — so for a CALL-FREE body no
    // cleanup subgraph is ever visited. The canonicalizer additionally drops unwind successors by
    // design. This loop was the only remaining net over unwalked blocks and it inspected
    // STATEMENTS only, never terminators.
    //
    // Consequence before this change: a built sibling could carry a real drop tree in a cleanup
    // block and still reach `DerivedAgreed`. Today that population is empty only because the
    // aggregate-return gate keeps Drop-bearing types out of the fragment — i.e. the safety rested
    // on a gate whose stated rationale (pass-totality) is separately measurable as over-strict.
    // Anyone narrowing that gate needs this net to exist FIRST, which is why it lands on its own.
    //
    // Deliberately Drop-ONLY. `Resume` is the normal terminator of a legitimate cleanup block, so
    // refusing it here would reject every body with an unwind edge and withdraw flips that are
    // sound today. This is a tightening: it can turn an `agreed` into a refusal, never the reverse.
    for (i, bb) in body.blocks.iter().enumerate() {
        if fine_of.contains_key(&i) {
            continue;
        }
        if matches!(bb.terminator, Terminator::Drop { .. }) {
            return Err(format!("Drop terminator in unwalked block {i} (cleanup/dead code)"));
        }
        for s in &bb.stmts {
            if matches!(s, Statement::StorageLive(_) | Statement::StorageDead(_)) {
                return Err(format!("storage marker in unwalked block {i} (cleanup/dead code)"));
            }
        }
    }
    Ok(out)
}

/// Symbolic expression for an rvalue assigned to `dest_local`. Op nodes carry the DESTINATION
/// local's declared type so a width difference between the two bodies can never hide behind
/// width-less `Int` constants.
fn rvalue_expr(
    body: &VerifiableBody,
    rvalue: &Rvalue,
    dest_local: usize,
    env: &Env,
    norms: &NormCounter,
) -> CanonResult<String> {
    let dest_ty = || -> CanonResult<String> {
        let decl = body
            .locals
            .get(dest_local)
            .filter(|d| d.index == dest_local)
            .ok_or_else(|| format!("missing local decl _{dest_local}"))?;
        canon_ty(&decl.ty)
    };
    match rvalue {
        Rvalue::Use(op) => operand_expr(op, env, norms),
        Rvalue::BinaryOp(op, l, r) => {
            // Trust (wave-U, div/rem FLIP): `Div`/`Rem` STATEMENTS are now rendered. Their trap
            // conditions (UB on zero / `MIN ÷ -1`) are NOT trusted to the value expression — they
            // are pinned by the mandatory `Assert` TERMINATORS the shim emits alongside every
            // div/rem (`Eq(divisor, 0)` div-by-zero + `BitAnd(Eq(divisor, -1), Eq(dividend, MIN))`
            // overflow), which the canonical form ALWAYS renders (a terminator is never dropped by
            // the pure-assign elimination). The div-by-zero assert's `cond` pins the divisor and
            // its `msg` operand pins the dividend, so even a DEAD div (whose value expression the
            // elimination may drop) stays fully characterized by its guards — a guardless or
            // wrong-operand div cannot false-agree (built always carries the matching guards). The
            // shim (`to_mir` `div_idiom`) emits a `Div`/`Rem` ONLY in that guarded shape, and
            // DerivedAgreed ships the shim's faithful body.
            Ok(format!(
                "bin({op:?},{},{},{})",
                dest_ty()?,
                operand_expr(l, env, norms)?,
                operand_expr(r, env, norms)?
            ))
        }
        Rvalue::CheckedBinaryOp(op, l, r) => Ok(format!(
            "chk({op:?},{},{},{})",
            dest_ty()?,
            operand_expr(l, env, norms)?,
            operand_expr(r, env, norms)?
        )),
        Rvalue::UnaryOp(op, o) => {
            if matches!(op, trust_types::UnOp::PtrMetadata) {
                return Err("UnaryOp(PtrMetadata) outside fragment".to_string());
            }
            Ok(format!("un({op:?},{},{})", dest_ty()?, operand_expr(o, env, norms)?))
        }
        // A cast statement (the checked-shift range check's `amt as u_ty` IntToInt on BOTH the
        // built side and the shim's derived side; see `to_mir::shift_idiom`). PURE for L5: every
        // cast kind trust-mir-extract admits into `Rvalue::Cast` is non-trapping (IntToInt,
        // saturating FloatToInt, FloatToFloat, IntToFloat, PtrToPtr, and the address-preserving
        // transmute legs — convert.rs's `Rvalue::Cast` arms; every other kind extracts as
        // `Rvalue::Unsupported`, which the fall-through below fails closed). The extraction ERASES
        // the cast KIND, but two casts only render equal here with the SAME target type AND the
        // same operand expression — which pins the kind for the integer targets this fragment
        // reaches (a float/ptr-sourced operand renders differently or fails `operand_expr`).
        Rvalue::Cast(o, to_ty) => {
            Ok(format!("cast({},{})", canon_ty(to_ty)?, operand_expr(o, env, norms)?))
        }
        // Trust (wave-D, Drop-free aggregate constructor-return FLIP): a struct construction
        // `_0 = Adt { f0, f1, ... }`. THE discrimination anchor — the field operands are rendered
        // IN ORDER via `operand_expr`, so a wrong field ORDER (`{a,b}` vs `{b,a}`) or a wrong field
        // VALUE renders a different string → `compare_derived` mismatch → no flip. The Adt
        // NAME (`safe_def_path_str`, args-free) rides along, but the DefId/args are pinned by the
        // shim from `built_ret_ty` (attack A1) — a wrong-args reconstruction is impossible, so the
        // args-free name is sufficient. Only single-variant STRUCT Adts (variant 0, no union
        // `active_field`); Tuple/Array/Closure/etc. aggregates fail closed (out of slice).
        Rvalue::Aggregate(kind, ops) => {
            let tag = match kind {
                AggregateKind::Adt { name, variant, active_field, args } => {
                    if active_field.is_some() {
                        return Err("union aggregate outside fragment".to_string());
                    }
                    // Trust (C1): render the generic ARGS, not just the args-free path. This tag
                    // is the comparator's whole view of an Adt aggregate, and erasing the args
                    // is why `to_mir` must source struct identity from `built_ret_ty` — its own
                    // comment says a wrong-args reconstruction "cannot be seen" here (attack A1).
                    // Now it can. Both sides of the comparison run through the same converter, so
                    // this tightens the check symmetrically.
                    //
                    // `None` means the producing site did not KNOW the args (the const-destructure
                    // path), not that there were none — so it is rendered distinctly from a
                    // known-empty argument list rather than collapsing to the same tag.
                    match args {
                        Some(args) => format!("adt:{name}:{variant}:args={args}"),
                        None => format!("adt:{name}:{variant}:args=?"),
                    }
                }
                // Trust (wave-L, scalar-tuple constructor-return FLIP): a tuple aggregate
                // `_0 = (f0, f1, ...)`. Both built and derived extract to `AggregateKind::Tuple`
                // (trust-mir-extract/convert.rs), so both render `agg(tuple,[..])`; the ORDERED
                // operand list below is the discrimination anchor (a wrong field order/value renders
                // a different string → mismatch → no flip). A tuple carries no identity to pin
                // (nullary kind).
                AggregateKind::Tuple => "tuple".to_string(),
                other => return Err(format!("aggregate kind outside fragment: {other:?}")),
            };
            let mut parts: Vec<String> = Vec::with_capacity(ops.len());
            for op in ops {
                parts.push(operand_expr(op, env, norms)?);
            }
            Ok(format!("agg({tag},[{}])", parts.join(",")))
        }
        // Trust (wave-V, fieldless-enum discriminant-read FLIP): `_d = Discriminant(place)` — the
        // enum tag read BOTH the built body (`_d = discriminant(_1)`) and the shim's derived body
        // (re-emitted from the producer's `extractfield 0`) carry. Rendered as `disc(dest_ty,
        // place)`: `dest_ty` pins the discriminant integer width (`discriminant_ty` — e.g. `i64`
        // for a repr-less enum on a 64-bit target), and `place_expr` pins the SOURCE place (a wrong
        // source — reading a different enum — renders a different symbol → mismatch → no flip; the
        // historical enum-reshape perturbation burn-in proved the reconstruction load-bearing).
        // This value flows (via the L-ledger fold) into the reshaped `SwitchInt` discriminant, whose
        // exhaustive tag set + `Unreachable` otherwise are the discrimination anchor for the dispatch.
        Rvalue::Discriminant(place) => {
            Ok(format!("disc({},{})", dest_ty()?, place_expr(place, env)?))
        }
        other => Err(format!("rvalue outside fragment: {other:?}")),
    }
}

#[cfg(test)]
mod session_state_tests {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, SourceSpan, Statement,
        UnwindEdge,
    };

    use super::*;

    fn sequential_loop_body(first_step: u128) -> VerifiableBody {
        let uint = Ty::Int { width: 32, signed: false };
        let copy = |local| Operand::Copy(Place::local(local));
        let sub = |local, step| {
            Rvalue::BinaryOp(BinOp::Sub, copy(local), Operand::Constant(ConstValue::Uint(step, 32)))
        };
        let assign = |local, rvalue| Statement::Assign {
            place: Place::local(local),
            rvalue,
            span: SourceSpan::default(),
        };
        let switch = |local, zero, body| Terminator::SwitchInt {
            discr: copy(local),
            targets: vec![(0, BlockId(zero))],
            otherwise: BlockId(body),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: uint.clone(), name: None },
                LocalDecl { index: 1, ty: uint.clone(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: uint.clone(), name: Some("m".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: switch(1, 3, 2) },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(1, sub(1, first_step))],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // This edge is the composition seam: loop 1's post-state is
                // copied into loop 2's seed. No independent initial value for
                // `_2` exists.
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(2, Rvalue::Use(copy(1)))],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: switch(2, 6, 5) },
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![assign(2, sub(2, 1))],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock {
                    id: BlockId(6),
                    stmts: vec![assign(0, Rvalue::Use(copy(2)))],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: uint,
            datatype_defs: Default::default(),
        }
    }

    fn sequential_loop_body_with_canonical_latches() -> VerifiableBody {
        let mut body = sequential_loop_body(1);
        for (latch, header) in [(2, 1), (5, 4)] {
            body.blocks[latch].terminator = Terminator::Assert {
                cond: Operand::Constant(ConstValue::Bool(true)),
                expected: true,
                msg: AssertMessage::Custom("canonical-latch".into()),
                target: BlockId(header),
                span: SourceSpan::default(),
                unwind: UnwindEdge::Unreachable,
            };
        }
        body
    }

    #[test]
    fn derived_stats_are_isolated_and_accumulate_only_explicit_deltas() {
        let mut first_session = DerivedSessionStats::default();
        let second_session = DerivedSessionStats::default();

        let mut first_delta = NO_NORMS;
        first_delta[NORM_LOCAL_ELIM] = 2;
        first_delta[NORM_PHI_MERGE] = 1;
        let (first_norms, first_tally) =
            first_session.record(DerivedVerdict::DerivedAgreed, first_delta);

        assert_eq!(first_tally, (1, 0, 0));
        assert_eq!(first_norms[NORM_LOCAL_ELIM], 2);
        assert_eq!(first_norms[NORM_PHI_MERGE], 1);
        assert_eq!(second_session.tally, [0, 0, 0]);
        assert_eq!(second_session.norms, NO_NORMS);

        let mut second_delta = NO_NORMS;
        second_delta[NORM_LOCAL_ELIM] = 3;
        let (second_norms, second_tally) =
            first_session.record(DerivedVerdict::DerivedUnsupported, second_delta);

        assert_eq!(second_tally, (1, 0, 1));
        assert_eq!(second_norms[NORM_LOCAL_ELIM], 5);
        assert_eq!(second_norms[NORM_PHI_MERGE], 1);
    }

    #[test]
    fn comparison_local_counters_do_not_share_state() {
        let first = NormCounter::default();
        let second = NormCounter::default();

        first.fire(NORM_GOTO_THREAD);
        first.fire(NORM_GOTO_THREAD);
        second.fire(NORM_MOVE_AS_COPY);

        assert_eq!(first.snapshot()[NORM_GOTO_THREAD], 2);
        assert_eq!(first.snapshot()[NORM_MOVE_AS_COPY], 0);
        assert_eq!(second.snapshot()[NORM_GOTO_THREAD], 0);
        assert_eq!(second.snapshot()[NORM_MOVE_AS_COPY], 1);
    }

    #[test]
    fn correspondence_witness_seal_covers_the_exact_role_map_digest() {
        let lineage = ProofDigest::sha256_domain("test.lineage", b"body");
        let mut witness = SourceHeaderCorrespondence::test_only(lineage);
        assert!(witness.authenticates(lineage));

        witness.role_map = ProofDigest::sha256_domain("test.source_header_roles", b"swapped");
        assert!(
            !witness.authenticates(lineage),
            "changing the exact built/derived role-map digest must invalidate the private seal"
        );
    }

    #[test]
    fn sequential_loop_fixed_points_compose_into_later_seed_and_return() {
        let (canonical, _) = canonicalize(&sequential_loop_body(1), CallArgKinds::new());
        let canonical = canonical.expect("two dominance-ordered natural loops are supported");
        let rendered = canonical.join("\n");

        assert!(
            rendered.contains("loop@b0 l0h0: seed=a1 back=bin(Sub,u32,l0h0,c:uint:1:w32)"),
            "first transition is an explicit observable:\n{rendered}",
        );
        assert!(
            rendered.contains("loop@b1 l1h0: seed=l0h0 back=bin(Sub,u32,l1h0,c:uint:1:w32)"),
            "loop 1's post-state must feed loop 2's seed:\n{rendered}",
        );
        assert!(
            rendered.contains("return l1h0"),
            "the final return must observe the composed second transition:\n{rendered}",
        );
    }

    #[test]
    fn mutating_only_the_first_transition_changes_the_composed_canonical_body() {
        let (correct, _) = canonicalize(&sequential_loop_body(1), CallArgKinds::new());
        let (mutated, _) = canonicalize(&sequential_loop_body(2), CallArgKinds::new());
        let correct = correct.expect("reference two-loop body is supported");
        let mutated = mutated.expect("mutation stays in-fragment so it must be compared");

        assert_ne!(
            correct, mutated,
            "loop 1 is the sole source of loop 2's seed; changing its transition must mismatch",
        );
        assert!(
            first_diff(&correct, &mutated).contains("back=bin(Sub"),
            "the mismatch must expose the changed first-loop transition"
        );
    }

    #[test]
    fn later_header_does_not_truncate_an_earlier_canonical_latch() {
        let (canonical, _) = canonicalize(&sequential_loop_body_with_canonical_latches(), CallArgKinds::new());
        let canonical = canonical.expect(
            "topological tie-breaking may place loop 2 before loop 1's independent latch",
        );
        assert_eq!(
            canonical.iter().filter(|line| line.contains("loop@b")).count(),
            2,
            "both sequential fixed points must be solved: {canonical:#?}",
        );
    }

    #[test]
    fn a_branch_optional_later_loop_retains_bypass_and_entered_observables() {
        let mut body = sequential_loop_body(1);
        body.blocks[3].terminator = Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(1)),
            targets: vec![(0, BlockId(6))],
            otherwise: BlockId(4),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };

        let (canonical, _) = canonicalize(&body, CallArgKinds::new());
        let canonical = canonical.expect(
            "a later optional SCC is still dominance-ordered when every entered path follows loop 1",
        );
        assert_eq!(
            canonical.iter().filter(|line| line.contains("loop@b")).count(),
            2,
            "both fixed-point definitions remain explicit: {canonical:#?}",
        );
        assert!(
            canonical.iter().filter(|line| line.contains("return ")).count() >= 2,
            "both the bypass and entered return paths remain observable: {canonical:#?}",
        );
    }

    #[test]
    fn an_optional_earlier_loop_cannot_authorize_a_later_header() {
        let mut body = sequential_loop_body(1);
        body.blocks[0].terminator = Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(1)),
            targets: vec![(0, BlockId(3))],
            otherwise: BlockId(1),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };

        let (canonical, _) = canonicalize(&body, CallArgKinds::new());
        assert_eq!(
            canonical.unwrap_err(),
            "non-sequential multiple loops outside fragment",
            "the first header no longer dominates the second, so the multi-loop gate must close",
        );
    }

    /// A6: the exemption ADMITS the case it exists for, and only that case.
    ///
    /// Without `shared_exempt` a by-value read of a `refs`-bound local is an escape and
    /// fails closed — that is the behaviour every other call keeps. With it, the read
    /// renders as an address. Both directions are asserted here because a test that only
    /// checked the admit would pass just as well if the flag were ignored and the escape
    /// admitted unconditionally, which is the dangerous shape.
    #[test]
    fn the_shared_param_exemption_admits_only_when_the_kind_says_shared() {
        let mut env = Env::default();
        env.refs.insert(7, 3); // `_7 = &_3`
        env.vals.insert(3, "a1".to_string());
        let arg = Operand::Copy(Place::local(7));
        let norms = NormCounter::default();

        let denied = operand_expr_call_arg(&arg, &env, &norms, &EscapeNames::default(), false);
        assert_eq!(
            denied.unwrap_err(),
            "ref local _7 used by value (escape) outside fragment",
            "without a Shared kind the escape must still fail closed",
        );

        let admitted = operand_expr_call_arg(&arg, &env, &norms, &EscapeNames::default(), true);
        assert_eq!(
            admitted.unwrap(),
            "ref(e0)",
            "a Shared parameter admits the escape, rendered as an ADDRESS",
        );
    }

    /// A6: the exemption changes the ADDRESS case and nothing else.
    ///
    /// `*_r` where `_r |-> _x` is the ordinary ref-alias READ (LEDGER L7) and has always
    /// been admitted, rendering the referent's VALUE. The escape the exemption unlocks is
    /// the BARE use of `_r`, which denotes its ADDRESS. Those are different observables,
    /// and the exemption must not blur them.
    ///
    /// (This test first asserted the deref was REFUSED — mistaking "projection on a
    /// reference" for "escape". It is not one, and running the test is what said so.)
    #[test]
    fn the_exemption_leaves_ordinary_alias_reads_untouched() {
        let mut env = Env::default();
        env.refs.insert(7, 3); // `_7 = &_3`
        env.vals.insert(3, "a1".to_string());
        let deref = Operand::Copy(Place { local: 7, projections: vec![Projection::Deref] });
        let norms = NormCounter::default();

        let without =
            operand_expr_call_arg(&deref, &env, &norms, &EscapeNames::default(), false).unwrap();
        let with =
            operand_expr_call_arg(&deref, &env, &norms, &EscapeNames::default(), true).unwrap();
        assert_eq!(without, "a1", "a read THROUGH the alias renders the referent's value");
        assert_eq!(
            with, without,
            "the exemption must not alter an ordinary read — it exists only for the bare \
             ADDRESS case, and a value rendered as an address would be a different observable",
        );
    }

    /// A6, THE PROPERTY THE WHOLE RENDERING EXISTS FOR: an address escape cannot
    /// canonicalize two DISTINCT slots to the same string.
    ///
    /// This is the manufactured-agreement case. If the address were rendered from the
    /// slot's VALUE, then `f(&a, &b)` with `a` and `b` holding equal values would render
    /// identically to a shim that wrongly aliased them into `f(&a, &a)` — the comparator
    /// would agree, the flip would be admitted, and a callee doing `ptr::eq` would observe
    /// the difference at runtime. The first-appearance bijection is what closes it.
    #[test]
    fn distinct_slots_never_render_the_same_address_even_with_equal_values() {
        let mut env = Env::default();
        env.refs.insert(7, 3); // `_7 = &_3`
        env.refs.insert(8, 4); // `_8 = &_4`
        // EQUAL values in the two referents — the case a value-derived rendering collapses.
        env.vals.insert(3, "a1".to_string());
        env.vals.insert(4, "a1".to_string());
        let norms = NormCounter::default();
        let render = |a: usize, b: usize| {
            let escapes = EscapeNames::default();
            let one = operand_expr_call_arg(
                &Operand::Copy(Place::local(a)), &env, &norms, &escapes, true,
            )
            .unwrap();
            let two = operand_expr_call_arg(
                &Operand::Copy(Place::local(b)), &env, &norms, &escapes, true,
            )
            .unwrap();
            format!("{one},{two}")
        };

        let honest = render(7, 8); // f(&_3, &_4)
        let aliased = render(7, 7); // a shim that collapsed them: f(&_3, &_3)
        assert_eq!(honest, "ref(e0),ref(e1)", "distinct slots take distinct names");
        assert_eq!(aliased, "ref(e0),ref(e0)", "the same slot takes the same name twice");
        assert_ne!(
            honest, aliased,
            "a wrongly-aliased call MUST canonicalize differently, or the comparator \
             would admit a flip that changes what `ptr::eq` observes",
        );
    }

    /// A6: the escape numbering is a BIJECTION and is body-global.
    ///
    /// Same slot -> same name however often it appears (so genuine aliasing still reads as
    /// aliasing), distinct slots -> distinct names (so a collapse cannot hide), and the
    /// counter does not restart per call — a callee may retain a pointer and compare it
    /// against one received at a LATER call, which per-site numbering would let two
    /// different slots both answer to `e0`.
    #[test]
    fn escape_names_are_a_body_global_bijection() {
        let escapes = EscapeNames::default();
        assert_eq!(escapes.name_of(3), 0);
        assert_eq!(escapes.name_of(4), 1);
        assert_eq!(escapes.name_of(3), 0, "the same slot keeps its name");
        assert_eq!(escapes.name_of(9), 2, "a later first appearance continues the count");
        assert_eq!(escapes.name_of(4), 1, "and earlier names are stable");
    }

    /// A6 guard helper: a body whose bb0 carries `_2 = &proj(_1)` (or `&mut`) and returns a
    /// constant — the minimal carrier for one `Rvalue::Ref` statement shape.
    fn body_with_one_borrow(projections: Vec<Projection>, mutable: bool) -> VerifiableBody {
        let uint = Ty::Int { width: 32, signed: false };
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: uint.clone(), name: None },
                LocalDecl { index: 1, ty: uint.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: uint.clone(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable, place: Place { local: 1, projections } },
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: uint,
            datatype_defs: Default::default(),
        }
    }

    /// `_2 = &_1; observe(move _2) -> bb1; _0 = _3; return` — the exact derived-side shape
    /// that would arm the shared-param exemption if it ever reached `canonicalize`.
    fn bare_borrow_then_call_body() -> VerifiableBody {
        let uint = Ty::Int { width: 32, signed: false };
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: uint.clone(), name: None },
                LocalDecl { index: 1, ty: uint.clone(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(uint.clone()) },
                    name: None,
                },
                LocalDecl { index: 3, ty: uint.clone(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        func: "observe".into(),
                        args: vec![Operand::Move(Place::local(2))],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: uint,
            datatype_defs: Default::default(),
        }
    }

    /// A6 GUARD: the ONE `env.refs` bootstrap shape — a borrow of a bare local — is
    /// refused, in BOTH mutabilities. `apply_stmt`'s borrow arm ignores `mutable`, so a
    /// bare `&mut _1` would seed `refs` exactly like `&_1`; a guard that only caught the
    /// shared spelling would leave open exactly the `&mut` latency it exists to close.
    #[test]
    fn the_refs_bootstrap_shape_is_refused_in_both_mutabilities() {
        for mutable in [false, true] {
            let found = derived_bare_local_borrow(&body_with_one_borrow(vec![], mutable))
                .expect("a projection-free Rvalue::Ref must be refused");
            assert!(
                found.contains("bare-local borrow in derived body (bb0: _2 = &"),
                "the refusal names the site: {found}"
            );
        }
    }

    /// A6 GUARD: every `Rvalue::Ref` shape `to_mir::lower_ir_to_mir` actually emits
    /// PASSES. Measured at to_mir.rs blob cb034e4b (six sites, all projected): three via
    /// `mk_place_deref` (`&(*p)`), one via `mk_place_field` on a deref (`&((*p).k)`), and
    /// two via `mk_place_field` on a downcast of a deref (`&(((*p) as V).k)`). The guard
    /// must refuse NONE of them — it pins the absent shape, never narrows the present ones.
    #[test]
    fn every_projected_borrow_shape_to_mir_emits_passes_the_guard() {
        let shapes: [Vec<Projection>; 3] = [
            vec![Projection::Deref],
            vec![Projection::Deref, Projection::Field(0)],
            vec![Projection::Deref, Projection::Downcast(1), Projection::Field(0)],
        ];
        for projections in shapes {
            for mutable in [false, true] {
                assert!(
                    derived_bare_local_borrow(&body_with_one_borrow(projections.clone(), mutable))
                        .is_none(),
                    "a projected borrow {projections:?} must pass the guard"
                );
            }
        }
    }

    /// A6 GUARD, THE MUTATION PROOF: the refused shape is not hypothetical. Fed to
    /// `canonicalize` with a `Shared` kind, the SAME body renders the exemption's address
    /// token; with no recorded kinds it fails closed as an escape. So the guard sits in
    /// front of a genuinely armable path (it is not vacuous), and the kinds map is
    /// genuinely consulted (the M2 direction at unit scale). `compare_derived` refuses
    /// this body at the guard BEFORE canonicalize ever sees it.
    #[test]
    fn the_guarded_shape_genuinely_arms_the_exemption_when_it_reaches_canonicalize() {
        let body = bare_borrow_then_call_body();
        let refusal =
            derived_bare_local_borrow(&body).expect("the guard must catch the body this test arms");
        assert!(refusal.contains("bare-local borrow in derived body"));

        let mut shared = CallArgKinds::new();
        shared.insert(0, vec![ArgBorrowKind::Shared]);
        let (armed, _) = canonicalize(&body, shared);
        let armed = armed.expect("with a Shared kind the exemption admits the escape");
        assert!(
            armed.iter().any(|line| line.contains("ref(e0)")),
            "the exemption rendered the borrow as an address: {armed:?}"
        );

        let (denied, _) = canonicalize(&body, CallArgKinds::new());
        assert_eq!(
            denied.unwrap_err(),
            "ref local _2 used by value (escape) outside fragment",
            "with no recorded kinds the same body must fail closed",
        );
    }
}
