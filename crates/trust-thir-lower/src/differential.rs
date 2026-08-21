//! The differential-equivalence gate: `THIR-trust-ir` vs an independently-built `MIR-trust-ir`
//! oracle, checked by *interpretation* on sampled inputs.
//!
//! This is a sampled semantic-equivalence gate over returns/traps for effect-free bodies, not a
//! structural comparison. For one body we obtain two
//! `trust_ir::Module`s built by two independent front-ends:
//!   * THIR-side (NEW, primary): `crate::lower_module` → `Lowered.module`.
//!   * MIR-side (compatibility ORACLE): `trust_mir_extract::extract_function_faithful(tcx, &Body)`
//!     → `trust_ir_bridge::lower_mir_compat_to_trust_ir(&vf)` (the retained P9 path).
//!
//! We then interpret BOTH modules' entry function (`FuncId::new(0)`) on a fixed sample of inputs
//! including type boundaries (0, 1, -1, MIN, MAX) and a few mids, declaring them equal iff every
//! sample agrees on the return value, nothing was `unsupported`, and the direct-call-reachable
//! bodies contain no memory/provenance effect omitted from
//! [`InterpretOutcome`](trust_ir::interpret::InterpretOutcome).
//!
//! CYCLE SAFETY (critical): this runs INSIDE `build_mir_inner_impl`, the implementation of the
//! `mir_built` query. Calling `tcx.optimized_mir(def)` (or `tcx.mir_built(def)`) here would be a
//! query cycle. Instead the hook already holds the freshly-built `Body<'tcx>` and passes it in by
//! reference; `extract_function_faithful` takes a `&mir::Body` and
//! its call tree (`extract_body` + `convert::*`) issues NO `optimized_mir`/`mir_built` query — the
//! only `optimized_mir` call sites in that crate are in `after_analysis` driver callbacks, off this
//! path. The oracle therefore reflects *unoptimized, freshly-built* MIR — the most faithful
//! reference for THIR-equivalence (no optimization has yet had a chance to change behavior).
//!
//! Any disagreement, any `unsupported` THIR shape, or any interpreter divergence is REPORTED, never
//! silently accepted. Non-interpretable bodies (external call, non-scalar params, oversized arity,
//! oracle lowering failure) are SKIPPED as coverage-only (`mode = NotRun`): they neither prove nor
//! refute equivalence.
//!
//! OPAQUE PARAMS (slice 3 widening): a `Ty::Ptr` or `Ty::Unit` parameter passes the
//! interpretability gate when its entry-param `ValueId` is PROVEN never-read in BOTH modules
//! (probe over `trust_ir::mem2reg::rewrite_inst`, the authoritative match-on-every-variant
//! operand walker — covers call args, branch args, stores-as-value, everything). Such a param
//! is sampled as a single placeholder (`NullPtr` / `Unit`) that the interpreter type-checks
//! but — by the proof — never evaluates, so it cannot influence any sample. This is exactly
//! the closure-environment class (`&{closure}` env of a non-capturing closure body), which
//! previously forced thousands of `NotRun` skips. An ACTUALLY-read pointer (deref'd,
//! compared, escaped) fails the probe and keeps the precise coverage-only skip.
//!
//! POINTER-PARAM INPUT LANE (Q1): the converse of the opaque widening above. A `Ty::Ptr` param
//! that IS read has no sampleable value TODAY because `Ty::Ptr` is opaque — the signature does
//! not name the referent's type, so there is nothing to enumerate. The lane RECOVERS that type
//! from the body (`sole_pointee_load`: the param's `ValueId` is used only as the `ptr` operand
//! of plain `Load`s, all of one type) and then MATERIALIZES a referent, so the body becomes
//! sampleable through its pointer instead of around it.
//!
//! The referent is materialized by a SYNTHESIZED WRAPPER — `Alloca` the pointee, `Store` the
//! sampled value, `Call` the entry with the slot, return what the entry returned — because the
//! interpreter owns its `MemoryState` and exposes no seam to pre-seed an allocation.
//! `execute_callee` swaps only `state.values` and threads `state` through, so the wrapper's
//! `Alloca` is visible to the callee.
//!
//! WHY THE WRAPPER DOES NOT DIE AT `first_unmodeled_observation`. An `Alloca`+`Store` pair is
//! exactly what that walk refuses (it escapes `private_nonescaping_slots`, whose argument is
//! about slots INTERNAL to one function). It survives because THE WALK NEVER SEES IT: the walk
//! is rooted at `thir_entry`/`oracle_entry` and follows `Inst::Call` CALLEE-ward only, so a
//! wrapper that CALLS the entry is not reachable from it. The entry itself is walked exactly as
//! before, and a plain `Load` is not an observable effect
//! (`Inst::has_observable_effects` returns `*volatile`), so the newly-sampled read does not
//! degrade the walk either.
//!
//! THE DEBT THAT CREATES, AND HOW IT IS DISCHARGED. Skipping the wrapper in the walk means the
//! wrapper's own memory effects are never compared across sides. That is sound ONLY because the
//! two wrappers are built identically on both sides from the same abstract sample — so
//! `wrappers_agree` ASSERTS it structurally (instruction-for-instruction, modulo each side's own
//! entry `FuncId`) and fails CLOSED rather than leaving the argument in a comment. The
//! pass-through param types are held id-free by admission (`pointer_lane_param_ok`), which is
//! what makes that assertion a plain equality rather than a cross-module type comparison.

use std::collections::{BTreeSet, HashMap, HashSet};

use rustc_middle::mir;
use rustc_middle::ty::{TyCtxt, TypeVisitableExt};
use rustc_span::def_id::LocalDefId;
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::{
    Block, CastOp, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

use crate::Lowered;

/// Which oracle the differential actually ran against. Recorded so a green result is never confused
/// with an un-run (coverage-only) one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DiffMode {
    /// Nothing ran — `unsupported` THIR, a cross-module call, or a structural skip.
    #[default]
    NotRun,
    /// The two modules were sample-interpreted and DISAGREED (a real divergence verdict).
    MirOracle,
    /// The two modules were sample-interpreted and agreed on every input, with no reachable
    /// memory/provenance effect omitted from the interpreter outcome.
    Agreed,
}

/// Outcome of comparing the THIR-side `Module` against the MIR-side oracle `Module` for one body,
/// by sampled interpretation.
#[derive(Debug, Default)]
pub struct DiffReport {
    /// True iff both modules were interpretable, every sampled input produced an identical return
    /// value, nothing was `unsupported`, AND no reachable memory/provenance effect was omitted from
    /// the interpreter outcome. A coverage-only skip is `equal = false` but NOT a claim of
    /// inequivalence — read `mode`.
    pub equal: bool,
    /// THIR `ExprKind`s / `Ty`s the direct lowering could not handle yet.
    pub unsupported: Vec<(String, &'static str)>,
    /// Human-readable notes on divergence, skips, and what ran.
    pub notes: Vec<String>,
    /// Number of distinct input tuples interpreted on BOTH sides (0 if skipped).
    pub samples_checked: usize,
    /// What actually ran. `Agreed`/`MirOracle` ⇒ a real differential happened; `NotRun` ⇒
    /// coverage-only (do NOT read `equal` as a proof of inequivalence).
    pub mode: DiffMode,
}

/// Cap on integer/bool parameters we exhaustively cross-product. 4 params × (≤8 samples) stays well
/// under the interpreter's default fuel. OPAQUE params (proven never-read `Ptr`/`Unit`, one
/// placeholder each) do not enter the product and do not count against this cap.
const MAX_PARAMS: usize = 4;

/// How one parameter is sampled (see module docs, "OPAQUE PARAMS").
#[derive(Clone, Copy, PartialEq, Eq)]
enum ParamClass {
    /// Interpretable scalar: enters the boundary+mid cross-product.
    Scalar,
    /// Proven-never-read `Ptr`/`Unit`: one type-correct placeholder, never evaluated.
    Opaque,
    /// Trust (B3/E6): eligible first-class enum param — enters the cross-product via an
    /// index-encoded abstract-sample column; realized PER SIDE at the args site (an
    /// `InterpretValue`'s `Ty::Enum(id)` carries a MODULE-LOCAL id, so one shared value
    /// cannot type against both modules).
    Enum,
    /// Trust (aggregate param lane): eligible BY-VALUE STRUCT param — same index-encoded
    /// column shape as `Enum`, realized PER SIDE against that module's OWN `StructDef`
    /// (`Ty::Struct(id)` is module-local for the identical reason). Eligibility is
    /// deliberately narrower than `tys_agree`'s comparison: see `struct_param_admissible`.
    Struct,
    /// Trust (Q1, pointer-param INPUT lane): a READ `Ty::Ptr` param whose referent type was
    /// recovered from the body. It consumes ONE sample column exactly like `Scalar` — but the
    /// column is over the POINTEE type, and the sampled value is turned into a pointer by the
    /// synthesized wrapper (see the module docs), never by the args site. The pointee type is
    /// carried out-of-band in `ptr_pointees[i]`, the same parallel-vec idiom `enum_samples`
    /// and `struct_samples` use, so `ParamClass` stays `Copy`.
    PtrTo,
}

/// Cap on the nesting depth of an eligible by-value struct param. A struct whose fields are
/// themselves structs is marshalled recursively; anything deeper than this fails CLOSED
/// (coverage-only), never approximately.
const MAX_STRUCT_DEPTH: u32 = 4;

/// Cap on the number of SCALAR LEAVES an eligible by-value struct param may carry. Every leaf
/// is an independent sample column inside the aggregate, so this bounds both the marshalling
/// work and the width over which the leaf-rotation recipe below can keep leaves distinguishable.
const MAX_STRUCT_LEAVES: usize = 8;

/// Number of abstract samples minted for one by-value struct param.
const MAX_STRUCT_SAMPLES: usize = 8;

/// Trust (B9-A): is this body DEFERRED to the crate-finalize seam differential? The SINGLE
/// source of truth for both the hook's event suppression and `record()`'s deferred flag
/// (must-fix 5: if suppression and deferral diverged, the scorecard's first-event-wins would
/// drop seam verdicts).
///
/// A clean body is deferred when the hook could not reach a verdict for a reason the FINALIZER
/// dissolves. There are two such reasons, and they are independent:
///
///   * **call-bearing** (B9-A) — the per-body module carries its callees as bodyless
///     declarations, so interpretation must wait until crate assembly links them.
///   * **pending-const** (slice 20) — the body carries placeholder `Inst::Const` nodes for
///     local consts the hook could not evaluate without re-entering MIR building.
///     `resolve_pending_consts` patches in the real values before the seam runs, so by then
///     the body is ordinarily interpretable. A pending-const body may be call-FREE; the seam
///     handles that uniformly (its reachable-callee closure is just the entry).
///
/// Both are TIMING facts about the hook, never facts about the body — which is exactly why
/// re-asking at finalize is sound rather than a second bite at the same cherry.
pub fn deferred_to_seam(thir_side: &Lowered) -> bool {
    deferred_to_seam_parts(
        thir_side.unsupported.is_empty(),
        thir_side.pending_consts.is_empty(),
        thir_side.contains_call,
    )
}

/// The component-wise spelling of [`deferred_to_seam`], for the one caller that has already
/// destructured `Lowered` (`crate_module::record`).
///
/// This exists because the "SINGLE source of truth" the doc comment above claims was, until
/// slice 20, only a claim: `record` re-implemented the predicate by hand against its own
/// destructured fields, so the hook and the registry each carried a private copy of a
/// condition whose divergence silently drops seam verdicts. They now share this function.
pub fn deferred_to_seam_parts(
    unsupported_is_empty: bool,
    pending_consts_is_empty: bool,
    contains_call: bool,
) -> bool {
    unsupported_is_empty && (contains_call || !pending_consts_is_empty)
}

/// Trust: the DIRECT interpretation differential's STRUCTURAL SKIP — the one predicate on
/// `Lowered` that routes a body away from [`compare`]'s sampled interpretation.
///
/// [`compare`] evaluates this before it builds the MIR-side oracle and returns
/// `DiffMode::NotRun` when it holds (see the cross-module call guard, step 0.5). Nothing else in
/// `Lowered` does this: in particular `Lowered::symbolic` is NEVER READ by `compare` — its only
/// consumer outside the coverage census is `crate_module::record` → `BodyRecord::symbolic` →
/// `splice_ok`. Producer lanes whose value model is degraded therefore FORCE `contains_call`
/// (`LowerCx::register_union_lane`, `LowerCx::register_enum_param_lane`) rather than relying on
/// `symbolic`, which would leave the manufactured-agreement channel open.
///
/// Extracted as a named `TyCtxt`-free predicate so those lanes' confinement can be pinned by a
/// unit test end to end, instead of resting on a reading of `compare`'s control flow.
pub fn contains_call_forces_not_run(thir_side: &Lowered) -> bool {
    thir_side.contains_call
}

/// Compare the THIR-side `Lowered.module` against the MIR-via-bridge oracle by sampled
/// interpretation. `mir` is the FRESHLY-BUILT body the `mir_built` query is producing (passed in to
/// avoid a query cycle — see the module docs).
///
/// Trust (B9-A): returns the MIR-side `VerifiableFunction` snapshot alongside the report for
/// every body that reaches extraction — the crate-finalize seam differential needs it to build
/// the linked oracle BUNDLE for call-bearing bodies (and call-FREE clean bodies are the CALLEES
/// of those bundles, so their snapshots matter too). Extraction happens exactly once here.
pub fn compare<'tcx>(
    tcx: TyCtxt<'tcx>,
    _def: LocalDefId,
    thir_side: &Lowered,
    mir: &mir::Body<'tcx>,
) -> (DiffReport, Option<trust_types::VerifiableFunction>) {
    let mut report =
        DiffReport { unsupported: thir_side.unsupported.clone(), ..Default::default() };

    // (0) Any unsupported THIR shape forces a non-equal, coverage-only result.
    if !thir_side.unsupported.is_empty() {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.notes.push(format!(
            "{} unsupported THIR shape(s); differential not run (coverage gap)",
            thir_side.unsupported.len()
        ));
        return (report, None);
    }

    // (0.4) Unrevealed-opaque guard, on the ORACLE rather than on the producer.
    //
    //       The producer's own layout demands are already pre-gated
    //       (`crate::layout_query_is_reentrant_safe`), but the MIR-side oracle is
    //       `trust-mir-extract` — a crate written for the verification pipeline, which runs
    //       AFTER borrowck and therefore never had to defend against this. Calling it from
    //       inside `mir_built` puts its `layout_of` on a local decl in a position the crate
    //       does not expect: if the type still mentions an unrevealed opaque of this body,
    //       `layout_of` normalizes it, demands `type_of(opaque)`, which demands borrowck of the
    //       defining body, which demands the `mir_built` already in flight. That is a FATAL
    //       E0391 query cycle, not the recoverable `LayoutError` every caller here assumes —
    //       so it is not a coverage question, it is `pub fn f() -> Result<impl Iterator, E>`
    //       failing to compile at all under batteries-on verification.
    //
    //       Declining is exact rather than conservative: `has_opaque_types` is the flag walk
    //       over the whole body, and the differential is a sampled-equivalence oracle whose
    //       documented posture for anything it cannot adjudicate is a coverage-only skip. It
    //       costs the direct lane a verdict on RPIT-returning bodies and costs the program
    //       nothing. Widening it means giving the oracle a reveal-safe entry point, not moving
    //       this gate.
    //
    //       Known boundary, stated because the flag name reads wider than it is: this catches a
    //       type that MENTIONS an opaque, not a free alias (`type T = impl Sized;`) that EXPANDS
    //       to one — that carries `HAS_TY_FREE_ALIAS`, not `HAS_TY_OPAQUE`. The same gap exists
    //       one layer up in `crate::cycle_safe_normalize`, and there it is still live: a TAIT in
    //       a callee signature reaches `try_normalize_erasing_regions` through
    //       `sig_shapes_coherent` and cycles before the differential is ever reached. Widening
    //       either guard to `has_aliases` is not free — for `cycle_safe_normalize` it would stop
    //       resolving concrete projections, which is the exact asymmetry the wave-19
    //       DST-coherence gate reads to catch a thin-vs-fat flip — so that repair is a separate,
    //       evidence-bearing change, not a flag swap.
    //
    //       That live gap fails one upstream test — `tests/ui/type-alias-impl-trait/
    //       issue-65679-inst-opaque-ty-from-val-twice.rs`, a `//@ check-pass` vanilla rustc
    //       accepts — so it is ledgered as `test-exc.tait.65679-free-alias-mir-built-cycle`
    //       (tests/upstream-rust/test-exceptions.toml, expires 2026-09-25). Retire that row with
    //       the evidence, NOT by widening this guard. Anchor: opaque-reveal-cycle-gate.
    if mir.has_opaque_types() {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.notes.push(
            "body mentions an unrevealed opaque (RPIT/TAIT) type; the MIR-side oracle's \
             layout queries would cycle through this body's own borrowck (coverage-only)"
                .to_string(),
        );
        return (report, None);
    }

    // Trust (B9-A): extract the MIR-side snapshot BEFORE the call guard — deferred bodies (and
    // the call-free clean bodies that serve as their callees) hand it to the seam via record().
    // Trust (v25 B1): the FAITHFUL extraction lane — isize/usize/char keep
    // their identity (TrustTy::PtrSizedInt/Char -> trust-ir Isize/Usize/Char)
    // so the oracle signature matches the producer's first-class spellings by
    // leaf equality. The VERIFIER pipeline stays on the legacy
    // `extract_function` (width-collapsed) until its own migration wave.
    let vf = trust_mir_extract::extract_function_faithful(tcx, mir);

    // (0.45) Pending-const guard. A LOCAL const the hook could not safely evaluate (reentrancy)
    //        left a placeholder `Inst::Const { value: Constant::PhantomData }` in the module,
    //        to be patched by the crate finalizer (see `Lowered::pending_consts`). A placeholder
    //        is NEVER interpreted HERE — executing it would manufacture a false TypeError-vs-value
    //        divergence verdict against THIR.
    //
    //        WHY THIS SITS BELOW THE EXTRACTION AND NOT ABOVE IT (slice 20). The placeholder is
    //        a fact about the PRODUCER's timing, not about the body: by the time the crate
    //        finalizer has run `resolve_pending_consts`, the module carries the REAL value and
    //        the body is as interpretable as any other. What it needs to be re-adjudicated then
    //        is the MIR-side oracle snapshot — and that snapshot can ONLY be taken here, from
    //        the freshly-built `mir` this hook was handed. It cannot be re-derived at finalize:
    //        `mir_built(def)` is a `Steal` already stolen by `mir_promoted`, and
    //        `run_required_analyses` forces `mir_borrowck` for every body owner (nested ones
    //        included, via `borrowck_collect_region_constraints`) because
    //        `trust_defer_verification()` is hardcoded `false` — all of it strictly before
    //        `trust_ir_crate_finalize`. `mir_promoted(def).0` is stolen too on any codegen
    //        compile. So the choice is to take the snapshot HERE or to have no oracle at all.
    //
    //        The body therefore stays a precise coverage-only skip AT THE HOOK, and returns its
    //        snapshot so `crate_module::run_seam_differentials` can re-adjudicate it after the
    //        patch (`differential::deferred_to_seam` routes it there).
    //
    //        ORDERING, both halves load-bearing:
    //          * BELOW (0.4): the opaque guard must still run FIRST. It exists precisely because
    //            calling the oracle's `layout_of` on an unrevealed-opaque body closes a FATAL
    //            E0391 through this body's own borrowck. Moving THIS gate below the extraction
    //            without leaving THAT one above it would hand the oracle the exact body it
    //            documents itself as unable to be asked about.
    //          * ABOVE (0.5): the call guard returns `Some(vf)` as well, so the snapshot is
    //            reached either way — but the pending-const note must WIN over the direct-call
    //            note for a body that is both, because the finalizer's re-adjudication is what
    //            actually happens to it and the note is the scorecard's classifier key.
    if !thir_side.pending_consts.is_empty() {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.notes.push(format!(
            "pending local const: {} placeholder(s) awaiting finalizer eval; \
             never interpreted (coverage-only skip)",
            thir_side.pending_consts.len()
        ));
        return (report, Some(vf));
    }

    // (0.5) Cross-module call guard. A direct call lowers to `Inst::Call { callee }` whose callee
    //       FuncId lives in another (single-function) module, so the interpreter cannot resolve it.
    //       We cannot assert interpretation-equivalence for such bodies; skip as coverage-only and
    //       do not even build the oracle (both sides would merely error at the call — a vacuous
    //       "agreement" we refuse to report as a verdict).
    if contains_call_forces_not_run(thir_side) {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        // Trust (B9-A): this note is now the FAIL-SAFE only — the hook suppresses the event for
        // deferred bodies (which get a seam verdict instead); it fires iff suppression and
        // deferral ever diverge. The note string is the burn-down ratchet's classifier key —
        // keep it VERBATIM.
        report.notes.push(
            "function contains a direct call (cross-module callee); \
             interpretation-equivalence not asserted (coverage-only)"
                .to_string(),
        );
        return (report, Some(vf));
    }

    // (1) Build the MIR-side oracle module WITHOUT any query call (the snapshot was extracted
    //     above): bridge the VerifiableFunction to trust-ir.
    let oracle: Module = match trust_ir_bridge::lower_mir_compat_to_trust_ir(&vf) {
        Ok(m) => m,
        Err(e) => {
            report.equal = false;
            report.mode = DiffMode::NotRun;
            report.notes.push(format!("oracle lowering failed (coverage-only skip): {e:?}"));
            return (report, Some(vf));
        }
    };

    // (1.5) Oracle interpretability guard: a non-interpretable oracle is NOT a trap reference.
    //
    // The trusted MIR-side bridge builds a `CheckedBinaryOp` result tuple by seeding an
    // `Inst::Undef` aggregate and `InsertField`-ing both fields into it (trust-ir-bridge
    // lower.rs ~12455-12482, taken when the operands are non-symbolic — which function params
    // always are on the oracle side). The reference interpreter, however, executes `Inst::Undef`
    // EAGERLY as `UndefinedBehavior` (trust-ir interpret.rs ~502) before the InsertFields run,
    // so such an oracle traps on EVERY input — even non-overflowing ones. That trap is an
    // oracle-construction artifact, not a source-level trap rustc would produce; counting it as a
    // genuine trap (`is_trap`) would manufacture a false `MirOracle` "THIR returned X but the
    // oracle proved a trap" divergence. We therefore skip such bodies as coverage-only (`NotRun`):
    // we cannot use this oracle as a faithful trap reference, and we refuse to assert (in)equivalence
    // against it. This is the trusted-side asymmetry the module docs already establish for oracle
    // incapacities. Making the oracle interpretable (lazy `Undef`, or a non-`Undef` tuple seed) is
    // tracked separately and would upgrade these bodies from `NotRun` to a real verdict.
    // Trust (B9-B1): the producer never emits `Inst::Undef` (fail-closed by construction); the
    // dead-seed substitution below must NEVER run on the side under test. Tripwire, not assumed.
    if module_has_undef(&thir_side.module) {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.notes.push(
            "THIR side unexpectedly carries Inst::Undef (producer invariant violated); \
             coverage-only skip"
                .to_string(),
        );
        return (report, Some(vf));
    }
    // Trust (B9-B1, oracle dead-seed rewrite): the bridge seeds CheckedBinaryOp tuples and
    // aggregate constructions with `Inst::Undef` that is PROVEN fully overwritten before any
    // observation (`classify_undefs`: single-use chain of InsertFields covering every field).
    // Such a seed carries no semantics — substitute a typed ZERO constant in a CLONE of the
    // oracle and interpret that (the bridge, trust-mc, the pinned interpreter, and the flip gate
    // are all untouched; this differential is LOG-ONLY). A LIVE havoc (an Undef whose value can
    // be observed — e.g. a `&str` const the bridge cannot spell) keeps the coverage-only skip,
    // now precisely classed. Converts most of the former clean-skip-oracle-undef population to
    // real verdicts (wave-9 acceptance pattern: Agreed strictly up, ZERO new divergences).
    // Trust (B9-B1): the bridge models a DIVERGING PANIC CALL as an unconditional
    // `assert(const false)` + PanicFreedom obligation — correct for the VERIFIER (prove the
    // path infeasible) but not a faithful trap reference for the INTERPRETER: executing it
    // traps at the model, not at source semantics. Previously masked by the Undef skip firing
    // first. Fail-closed skip, precisely classed.
    if oracle_has_const_false_assert(&oracle) {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.notes.push(
            "oracle models a diverging panic call as an unconditional assert(false) \
             (oracle-panic-model, a verification model not a faithful trap reference); \
             coverage-only skip"
                .to_string(),
        );
        return (report, Some(vf));
    }
    // Trust (B9-B1b): the bridge lowers an `expected=false` assert condition as
    // `ICmp Eq(cond, const false)` over BOOL operands (trust-ir unary `not` is integer-bitwise),
    // but the pinned interpreter's ICmp is int-only (`expect_int_value`) — every checked-arith
    // body's trap-input sample then infra-errors instead of trap-agreeing. Rewrite the shape in
    // the oracle (this differential's local copy; bridge/trust-mc/production consumers untouched)
    // into the producer's own bool-not idiom `Select(cond ? false : true)` — semantically
    // identical, interpreter-native.
    let mut oracle = oracle;
    rewrite_bool_not_icmp(&mut oracle);
    // Trust (vtable slice 12): BEFORE classification — the Array dead-seed walk models the
    // InsertElement form only, and the pinned interpreter has no InsertField-over-Array
    // arm (see `rewrite_array_insert_fields`).
    rewrite_array_insert_fields(&mut oracle);
    let (undef_class, undef_trace) = classify_undefs_traced(&oracle);
    let oracle: Module = match undef_class {
        UndefClass::None => oracle,
        UndefClass::DeadSeeds => substitute_dead_seeds(oracle),
        UndefClass::Live => {
            // Trust (vtable slice 10): the const-param/assoc-const SAMPLE-COLUMN carve-out.
            // A SYMBOLIC body's oracle twin carries its parametric reads as live
            // integer-sorted `Inst::Undef`s (the bridge's `ConstParam`/`OpaqueScalar` arms)
            // while the THIR side spells the SAME reads as `GlobalAddr`+`Load` of ONE
            // value-less `__trust_constparam_*`/`__trust_symconst_*` carrier. When the
            // single-parameter pairing audit holds (see `const_param_column_plan`), the
            // parameter becomes an interpretation INPUT: both sides receive the same
            // sampled value per execution, in per-sample local CLONES only — the
            // producer's module, `Lowered::symbolic`, the splice, and the verifier lanes
            // are untouched. Refusal falls through to the existing Live-havoc skip,
            // note verbatim.
            if let Some(mut tail) = const_param_column_compare(&thir_side.module, &oracle) {
                tail.unsupported = report.unsupported;
                return (tail, Some(vf));
            }
            report.equal = false;
            report.mode = DiffMode::NotRun;
            report.notes.push(format!(
                "MIR oracle carries a LIVE havoc (`Inst::Undef` outside the proven-dead-seed \
                 shape; eagerly-trapping, non-interpretable as a trap reference{}); \
                 coverage-only skip — NOT a THIR divergence",
                undef_trace.map(|t| format!("; offender: {t}")).unwrap_or_default()
            ));
            return (report, Some(vf));
        }
    };
    // Trust (vtable slice 6): align the oracle's once-stored escaping-slot spelling of a
    // promoted borrow with the producer's initializer-bearing-global spelling, in this
    // differential's local copy only (bridge/verifier/flip untouched). AFTER the dead-seed
    // substitution — the aggregate fold reads the substituted `Const` seeds. Admits
    // nothing by itself (the `GlobalAddr` tail-gate arm is unconditional); it is the
    // spelling precondition for the chain-item-(1) value model.
    let mut oracle = oracle;
    respell_promoted_slots_as_globals(&mut oracle);

    // Trust (vtable slice 12): the THIR-SIDE twin respell — the producer's once-stored
    // escaping ARRAY slot (`lower_inline_array_to_slice`'s Alloca+Store+PtrFromParts)
    // respelled as its own wave-16 promoted-global spelling, on a CLONE only (the shipped
    // `Lowered` and every non-differential consumer read the original; `None` = no
    // candidate fired = zero cost). PER-BODY path only, deliberately — and still so after
    // slice 13 retired the call-free admission bound: extending this respell to the
    // assembled SEAM module is a separate evidence-bearing change (the assembled entry's
    // slots interleave with spliced sibling bodies), and its absence only HOLDS seam rows
    // (fail-closed), never mints one. See `respell_thir_array_slots_as_globals` for the
    // side-under-test admissibility argument (fold-of-actual-store + total audit +
    // bit-exact pairing = a defect can only HOLD, never agree).
    let thir_respelled = respell_thir_array_slots_as_globals(&thir_side.module);
    let thir_module: &Module = thir_respelled.as_ref().unwrap_or(&thir_side.module);

    // Trust (B9-A): the per-body path delegates to the entry-parameterized core below.
    let mut tail = compare_entries(thir_module, FuncId::new(0), &oracle, FuncId::new(0));
    tail.unsupported = report.unsupported;
    (tail, Some(vf))
}

/// Trust: return the first direct-call-reachable observation that the comparator cannot establish.
///
/// The interpreter creates a fresh private memory/global state for each execution and returns only
/// values plus a step count. Return values and traps therefore suffice for pure/control-flow bodies
/// without local identity, but cannot establish agreement for memory writes, volatile/atomic
/// accesses, allocation/global provenance, callable/frame identity, permission/ARC state, or opaque
/// calls. Direct calls are inspected recursively so a pure linked seam body stays comparable while
/// an effectful callee cannot hide behind an identical caller return. We intentionally inspect only
/// the entry's call closure: the assembled crate module may contain unrelated effectful functions
/// that the sampled entry can never invoke.
fn constant_materializes_uncomparable_identity(value: &Constant) -> bool {
    match value {
        // Function and symbol identities are module/linker-local. Equal numeric `FuncId`s (or
        // equal synthetic interpreter addresses) across independently-built modules do not prove
        // that the referenced definitions are the same program object.
        Constant::Closure { .. } | Constant::FnDef(_) | Constant::SymbolAddr { .. } => true,
        Constant::Aggregate(values)
        | Constant::Array(values)
        | Constant::Vector(values)
        | Constant::Sequence(values)
        | Constant::Set(values) => values.iter().any(constant_materializes_uncomparable_identity),
        Constant::Record(fields) => {
            fields.iter().any(|(_, value)| constant_materializes_uncomparable_identity(value))
        }
        Constant::Int(_)
        | Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::PhantomData => false,
    }
}

/// Trust: the set of `Alloca` result slots in `func` that never escape — i.e. every use of
/// the slot pointer is the `ptr` operand of a `Load`/`Store` (no compare, no deref-into-value,
/// no pass-by-address). Such a slot is a provably private stack cell with no observable address
/// identity and no observable final memory, so the faithful-MIR oracle's multi-block promotion
/// of a `mut` scalar-enum local through it agrees with the direct-THIR SSA form. Uses the same
/// sentinel-remap escape probe as `nodes_using`; fails closed (empty set) if no sentinel is free.
fn private_nonescaping_slots(func: &Function) -> HashSet<ValueId> {
    let mut candidates: HashSet<ValueId> = HashSet::new();
    for blk in &func.blocks {
        for node in &blk.body {
            if matches!(node.inst, Inst::Alloca { .. }) {
                candidates.extend(node.results.iter().copied());
            }
        }
    }
    if candidates.is_empty() {
        return candidates;
    }
    let max_id = func.max_value_id();
    if max_id == u32::MAX {
        candidates.clear(); // no sentinel available -> fail closed
        return candidates;
    }
    let sentinel = ValueId::new(max_id + 1);
    candidates.retain(|&cand| {
        let map: HashMap<ValueId, ValueId> = std::iter::once((cand, sentinel)).collect();
        for blk in &func.blocks {
            for node in &blk.body {
                let mut probe = node.inst.clone();
                trust_ir::mem2reg::rewrite_inst(&mut probe, &map);
                // A benign Load/Store `ptr` use of the slot is fine: restore it, then require
                // the probe to be otherwise unchanged. Any surviving diff means the slot
                // appears in a non-`ptr` position -> it escapes.
                match &mut probe {
                    Inst::Load { ptr, .. } | Inst::Store { ptr, .. } if *ptr == sentinel => {
                        *ptr = cand;
                    }
                    _ => {}
                }
                if probe != node.inst {
                    return false;
                }
            }
        }
        true
    });
    candidates
}

/// Trust (vtable slice 7): the PAIRED promoted-global admission set — the names a
/// `first_unmodeled_observation` walk may treat as modeled module state.
///
/// A name is admitted only when EVERY conjunct below holds; each is load-bearing:
///
/// * **`__trust_promoted_*` or `__trust_bytes_*` name grammar on BOTH sides.** Post-slice-6 both
///   spellings of a promoted SCALAR borrow use the promoted mint (producer wave-16; oracle
///   `respell_promoted_slots_as_globals`); post-slice-8 both spellings of a promoted
///   string/byte-string LITERAL use the bytes mint (producer wave-17 `emit_bytes_global`; oracle
///   `emit_str_const_bytes_global`, the bridge's slice-8 mirror). Slice 7's "name grammar covers
///   the producer's bytes globals" was read off the CRATE module, where `prepare_body_tables`
///   renames every spliced global `__trust_promoted_{n}` — the PER-BODY modules this function
///   compares carry `__trust_bytes_{idx}`, so the bytes grammar must be admitted explicitly.
///   The slice-4 warning stands: a shape test alone (immutable, even initializer-less) would also
///   admit symbolic-const carriers — scoping to the two mint families plus the initializer
///   requirement below keeps the admission on exactly the promoted-allocation provenance question.
/// * **Unique per module.** A duplicated name would make "the paired global" ambiguous.
/// * **Immutable + initializer-BEARING on both sides.** An initializer-less global is BSS
///   (zero-filled) — value agreement over zero-fill was slice 4's measured trap; refuse it.
/// * **Data-only, BIT-EXACT equal initializer content** (`Constant`'s hand-written float-bit-exact
///   `Eq`). Content equality is what makes the two globals THE SAME immutable object. Without it,
///   an ADDRESS-returning body (`const A: &i32 = &2` returns the pointer, never loads) would
///   raw-agree on `Ptr{0,0}` while the two cells hold different values — the slice-5 blindness
///   in reverse. Identity-bearing constants (`FnDef`/`SymbolAddr`/`Closure`) refuse via
///   `constant_materializes_uncomparable_identity`. Trust (vtable slice 12): equality is
///   `promoted_init_content_eq` — plain `Eq` plus the one deliberate cross-VARIANT arm
///   (producer `Aggregate` vs oracle `Array`, elementwise bit-exact) the array spelling
///   split forces.
/// * **Cross-module structural type agreement** — `promoted_pair_tys_agree`: `tys_agree`
///   (fail-closed on `Err`) plus the one deliberate cross-SPELLING arm (homogeneous
///   producer `Tuple` vs oracle `Array`, length + per-element agreement), scoped to this
///   pairing site; `tys_agree` itself quarantines the pair so it can never mint a verdict.
/// * **Address-free type.** A paired global whose type contains a pointer would let a
///   `Load`-through manufacture an address VALUE outside the audited closure
///   (`promoted_addr_closure`); every population type is scalar/aggregate-of-scalars.
fn paired_admitted_promoted_globals(am: &Module, bm: &Module) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for ga in &am.globals {
        if !(ga.name.starts_with("__trust_promoted_") || ga.name.starts_with("__trust_bytes_")) {
            continue;
        }
        if am.globals.iter().filter(|g| g.name == ga.name).count() != 1 {
            continue; // duplicated name on the A side -> ambiguous pairing, refuse
        }
        let mut bs = bm.globals.iter().filter(|g| g.name == ga.name);
        let (Some(gb), None) = (bs.next(), bs.next()) else {
            continue; // absent or duplicated on the B side -> unpaired/ambiguous, refuse
        };
        if ga.mutable || gb.mutable {
            continue;
        }
        let (Some(ia), Some(ib)) = (&ga.initializer, &gb.initializer) else { continue };
        if constant_materializes_uncomparable_identity(ia) || !promoted_init_content_eq(ia, ib) {
            continue;
        }
        if !ty_is_address_free(am, &ga.ty, TY_CMP_DEPTH)
            || !ty_is_address_free(bm, &gb.ty, TY_CMP_DEPTH)
        {
            continue;
        }
        if !promoted_pair_tys_agree(am, bm, &ga.ty, &gb.ty) {
            continue;
        }
        out.insert(ga.name.clone());
    }
    out
}

/// Trust (vtable slice 12): initializer content equality for the promoted-global pairing,
/// tolerant of exactly ONE deliberate variant split — the producer folds its Tuple-spelled
/// array slot to `Constant::Aggregate` while the oracle folds its Array-spelled twin to
/// `Constant::Array`. Elementwise, top-level only, each element compared by `Constant`'s
/// own bit-exact `Eq` (floats included) — the slice-7 "same immutable object" claim is
/// about the BYTES, and a homogeneous aggregate's bytes do not depend on which of the two
/// aggregate variants spells them. Everything else remains plain `Eq`.
fn promoted_init_content_eq(a: &Constant, b: &Constant) -> bool {
    if a == b {
        return true;
    }
    match (a, b) {
        (Constant::Aggregate(xs), Constant::Array(ys))
        | (Constant::Array(xs), Constant::Aggregate(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| x == y)
        }
        _ => false,
    }
}

/// Trust (vtable slice 12): type agreement for the promoted-global pairing, tolerant of
/// the SAME single split — producer `Ty::Tuple(vec![elem; n])` vs oracle `Ty::Array(tid,
/// n)` for the same source `[T; N]` (the documented `map_ty` spelling; `tys_agree` itself
/// QUARANTINES the pair as Err precisely so no *verdict* is minted over it). Scoped to the
/// pairing site on purpose: here both globals were minted by this file's own respells (or
/// the producer's wave-16 lane), the contents are already proven bit-exact equal, and the
/// claim being licensed is "same immutable object" — for which a homogeneous tuple of N
/// elems and an N-array of the same element type are the same object. Cross-spelling
/// requires length match plus per-element `tys_agree == Ok(true)` against the array's
/// resolved element; any resolution failure refuses (fail-closed).
fn promoted_pair_tys_agree(am: &Module, bm: &Module, a: &Ty, b: &Ty) -> bool {
    if matches!(tys_agree(am, bm, a, b, TY_CMP_DEPTH), Ok(true)) {
        return true;
    }
    let elementwise = |tuple_side: &Module,
                       elems: &[Ty],
                       array_side: &Module,
                       tid: trust_ir::TyId,
                       n: u64,
                       tuple_is_a: bool| {
        if elems.is_empty() || elems.len() != n as usize {
            return false;
        }
        let Some(elem) = array_side.ty(tid) else { return false };
        elems.iter().all(|x| {
            let r = if tuple_is_a {
                tys_agree(tuple_side, array_side, x, elem, TY_CMP_DEPTH)
            } else {
                tys_agree(array_side, tuple_side, elem, x, TY_CMP_DEPTH)
            };
            matches!(r, Ok(true))
        })
    };
    match (a, b) {
        (Ty::Tuple(xs), Ty::Array(tid, n)) => elementwise(am, xs, bm, *tid, *n, true),
        (Ty::Array(tid, n), Ty::Tuple(ys)) => elementwise(bm, ys, am, *tid, *n, false),
        _ => false,
    }
}

/// True iff `ty` provably contains no address anywhere (recursively, through this module's own
/// tables). Anything unresolvable, deeper than the cap, or not on the explicit allow-list fails
/// CLOSED (`false`) — including `Ptr`/`FatPtr`/`Ref`/`RefMut`/raw pointers, `Rc`, `Func`,
/// `Closure`, `Record`, `Refine`, and `Error`.
fn ty_is_address_free(module: &Module, ty: &Ty, depth: u32) -> bool {
    if depth == 0 {
        return false;
    }
    match ty {
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Unit
        | Ty::Never => true,
        Ty::Vector(elem, _) => ty_is_address_free(module, elem, depth - 1),
        Ty::Tuple(tys) => tys.iter().all(|t| ty_is_address_free(module, t, depth - 1)),
        Ty::Array(id, _) | Ty::Sequence(id) | Ty::Set(id, _) => {
            module.ty(*id).is_some_and(|t| ty_is_address_free(module, t, depth - 1))
        }
        Ty::Struct(sid) => module.struct_def(*sid).is_some_and(|d| {
            d.fields.iter().all(|f| ty_is_address_free(module, &f.ty, depth - 1))
        }),
        Ty::Enum(eid) => module.enum_def(*eid).is_some_and(|d| {
            d.variants
                .iter()
                .all(|v| v.fields.iter().all(|f| ty_is_address_free(module, f, depth - 1)))
        }),
        _ => false,
    }
}

/// Trust (vtable slice 7): the audited value closure of a function's ADMITTED promoted-global
/// addresses — `Some((tracked, name))` iff every use of every address derived from an admitted
/// `GlobalAddr` is one of the four modeled forms, `None` (admit NOTHING in this function,
/// fail-closed) otherwise.
///
/// * **Seeds:** single-result `Inst::GlobalAddr` of a paired-admitted global. MORE THAN ONE
///   DISTINCT admitted name refuses outright — the slice-4 ≤1-distinct-admitted-global bound.
///   With exactly one admitted object per side, "the returned non-null pointer" can only be that
///   object's address, which is what makes the raw `InterpretPointer` comparison meaningful
///   (see the admission argument at the walk's `GlobalAddr` arm).
/// * **Closure:** `Borrow` (single-result) and `Copy` (single-result) over a tracked value track
///   their results — the interpreter executes both as pure pointer pass-throughs, so every
///   tracked value IS the admitted global's address at offset 0. This is the slice-6 kept-Borrows
///   arm: the oracle's `&(*_1)` reborrow chain and the `&raw const` copy hop.
/// * **Closure, the slice-8 FAT-CARRIER arm (the fat-return comparison arm at step (7)):** a
///   single-result `PtrFromParts` whose `ptr_ty` is `FatPtr(Slice|Str)` and whose DATA operand
///   is tracked also tracks its result. Why the step-(7) raw comparison of such a returned
///   value is then meaningful — `value_agree` compares an `InterpretValueKind::FatPtr`
///   exactly, i.e. its data lane by raw `InterpretPointer { allocation, offset }` equality and
///   its metadata lane bit-exactly:
///     - the DATA lane is the tracked value verbatim (the interpreter's `PtrFromParts` copies
///       the data operand into the fat value unchanged), so under the ≤1-distinct-admitted
///       bound the thin-case argument at the walk's `GlobalAddr` arm applies to it unchanged:
///       a non-null data pointer inside a returned fat value on an admitted body can only BE
///       the single paired global's address at offset 0 — raw agreement is agreement about
///       the SAME named immutable object with bit-exact equal content;
///     - the METADATA lane of a `Slice`/`Str` fat kind is canonically `U64` — an integer
///       length, compared bit-exactly — never an address. `FatPtrKind::TraitObject` is
///       excluded by construction (its metadata IS a pointer, a second address lane this
///       model does not cover): a TraitObject `PtrFromParts` over a tracked data operand
///       refuses the whole function's admission through the audit below.
/// * **Audit (sentinel-remap probe, `private_nonescaping_slots`' fail-closed idiom):** every use
///   of a tracked value must be a non-volatile `Load` through it, a single-result `Borrow` of it,
///   a single-result `Copy` of it, the DATA operand of a single-result `Slice`/`Str`
///   `PtrFromParts`, a `Return` operand, or (since vtable slice 13) a DIRECT-call argument
///   whose linked callee passes the seeded-parameter audit (`seeded_param_uses_modeled` —
///   which itself refuses return positions, so the address cannot come back as an un-audited
///   call result; call results never join the tracked set). Everything else — `Store` (either
///   operand), a `CallIndirect` operand (no static target to audit),
///   `GEP`/`PtrToInt`/`ICmp` (derived addresses / address arithmetic — a derived offset or an
///   address-as-integer would put a value the model does not cover into the comparison), the
///   METADATA operand of any `PtrFromParts` (an address flowing into a length lane), and any
///   operand position this list never anticipated — refuses the WHOLE function's admission.
fn promoted_addr_closure(
    func: &Function,
    module: &Module,
    paired: &BTreeSet<String>,
    exclude: &HashSet<ValueId>,
) -> Option<AddrClosureAudit> {
    let mut tracked: HashSet<ValueId> = HashSet::new();
    let mut name: Option<String> = None;
    let mut address_returned = false;
    for blk in &func.blocks {
        for node in &blk.body {
            let Inst::GlobalAddr { global } = &node.inst else { continue };
            let def = module.globals.get(global.as_usize())?;
            if !paired.contains(&def.name) {
                continue; // unadmitted global: its GlobalAddr keeps the existing note
            }
            let &[r] = node.results.as_slice() else { return None };
            // Trust (vtable slice 13): a seed whose whole closure is already proven DEAD
            // (`dead_promoted_addr_values`) is handled by the walk's dead arm and does
            // not consume the ≤1-distinct-admitted budget here.
            if exclude.contains(&r) {
                continue;
            }
            match &name {
                None => name = Some(def.name.clone()),
                Some(n) if *n == def.name => {}
                Some(_) => return None, // second DISTINCT admitted global: over the <=1 bound
            }
            tracked.insert(r);
        }
    }
    if tracked.is_empty() {
        return Some(AddrClosureAudit::default());
    }
    // Fixpoint: Borrow/Copy pass-throughs join the tracked set; so does a Slice/Str
    // `PtrFromParts` over a tracked DATA operand (the slice-8 fat carrier — see the doc
    // comment's fat-carrier arm for why its raw step-(7) comparison is then meaningful).
    // A TraitObject fat kind never joins: if its data operand is tracked, the audit below
    // refuses the whole function (its metadata is a second address lane, out of model).
    loop {
        let mut grew = false;
        for blk in &func.blocks {
            for node in &blk.body {
                let joins = match &node.inst {
                    Inst::Borrow { ptr } => tracked.contains(ptr),
                    Inst::Copy { operand, .. } => tracked.contains(operand),
                    Inst::PtrFromParts { ptr_ty, data, .. } => {
                        matches!(
                            ptr_ty,
                            Ty::FatPtr(
                                trust_ir::FatPtrKind::Slice(_) | trust_ir::FatPtrKind::Str
                            )
                        ) && tracked.contains(data)
                    }
                    _ => false,
                };
                if joins {
                    let &[r] = node.results.as_slice() else { return None };
                    grew |= tracked.insert(r);
                }
            }
        }
        if !grew {
            break;
        }
    }
    // Audit every use of every tracked value; unanticipated positions fail closed.
    let max_id = func.max_value_id();
    if max_id == u32::MAX {
        return None; // no sentinel available -> fail closed
    }
    let sentinel = ValueId::new(max_id + 1);
    for &v in &tracked {
        let map: HashMap<ValueId, ValueId> = std::iter::once((v, sentinel)).collect();
        for blk in &func.blocks {
            for node in &blk.body {
                let mut probe = node.inst.clone();
                trust_ir::mem2reg::rewrite_inst(&mut probe, &map);
                if probe == node.inst {
                    continue; // does not use v
                }
                match &mut probe {
                    Inst::Load { ptr, volatile: false, .. } if *ptr == sentinel => {
                        *ptr = v;
                    }
                    Inst::Borrow { ptr }
                        if *ptr == sentinel && node.results.len() == 1 =>
                    {
                        *ptr = v;
                    }
                    Inst::Copy { operand, .. }
                        if *operand == sentinel && node.results.len() == 1 =>
                    {
                        *operand = v;
                    }
                    // Trust (vtable slice 8): the DATA operand of a Slice/Str fat
                    // assembly is a modeled pass-through (the fat-carrier arm). ONLY
                    // the data position is restored: a tracked value in the METADATA
                    // operand stays sentinel'd, so the probe differs and the whole
                    // function refuses — an address in a length lane is exactly the
                    // out-of-model flow this audit exists to catch. TraitObject fat
                    // kinds take no arm at all (their metadata is a pointer), so a
                    // tracked data operand there also refuses.
                    Inst::PtrFromParts { ptr_ty, data, .. }
                        if *data == sentinel
                            && node.results.len() == 1
                            && matches!(
                                ptr_ty,
                                Ty::FatPtr(
                                    trust_ir::FatPtrKind::Slice(_)
                                        | trust_ir::FatPtrKind::Str
                                )
                            ) =>
                    {
                        *data = v;
                    }
                    Inst::Return { values } => {
                        let mut restored = false;
                        for x in values.iter_mut() {
                            if *x == sentinel {
                                *x = v;
                                restored = true;
                            }
                        }
                        if restored {
                            address_returned = true;
                        }
                    }
                    // Trust (vtable slice 13): a tracked address as a DIRECT call argument
                    // to a LINKED (bodyful, in-module) callee is a modeled use IFF the
                    // callee's own uses of the seeded parameter(s) all pass the same
                    // modeled-form audit AND the seeded value never reaches the callee's
                    // return (`seeded_param_uses_modeled`, recursive, cycle-guarded).
                    // Call RESULTS deliberately never join the tracked set: with the
                    // seeded audit refusing address returns, no callee can hand the
                    // admitted address back as an un-audited ordinary call result — the
                    // `ptr_to_int(callee())` hole the retired call-free bound existed
                    // for. `CallIndirect` takes no arm (no static target to audit), so a
                    // tracked value there still refuses the whole function.
                    Inst::Call { callee, args } => {
                        let mut positions: Vec<usize> = Vec::new();
                        for (i, a) in args.iter_mut().enumerate() {
                            if *a == sentinel {
                                *a = v;
                                positions.push(i);
                            }
                        }
                        if !positions.is_empty() {
                            let mut visited: HashSet<u32> = HashSet::new();
                            if !seeded_param_uses_modeled(
                                module,
                                *callee,
                                &positions,
                                &mut visited,
                                CALL_AUDIT_DEPTH,
                            ) {
                                return None;
                            }
                        }
                    }
                    _ => {}
                }
                if probe != node.inst {
                    return None;
                }
            }
        }
    }
    Some(AddrClosureAudit { tracked, admitted: name, address_returned })
}

/// Trust (vtable slice 13): the audited result of one function's paired-global address
/// walk — the tracked value closure, the (≤1) admitted name, and whether any tracked
/// value reaches a `Return` position (licensed for a single-function walk by the slice-7
/// argument; refused across a linked call boundary by `first_unmodeled_observation`).
#[derive(Default)]
struct AddrClosureAudit {
    tracked: HashSet<ValueId>,
    admitted: Option<String>,
    address_returned: bool,
}

/// Recursion budget for the seeded-parameter audit. The population is depth 1 (an entry
/// passing one promoted address to one leaf callee); the budget exists so a pathological
/// call chain fails CLOSED instead of recursing unboundedly.
const CALL_AUDIT_DEPTH: u32 = 8;

/// Trust (vtable slice 13): does `callee` use its `seeded` entry parameters ONLY in
/// modeled forms? The seeded parameters stand for a paired-admitted promoted-global
/// address handed across a linked direct call. Allowed uses of a seeded-tracked value —
/// non-volatile `Load` through it (the pairing's bit-exact content equality is what makes
/// the loaded value modeled), single-result `Borrow`/`Copy` pass-throughs (which join the
/// tracked set), and a further DIRECT call argument (recursive, `visited`-guarded, depth-
/// bounded). A `Return` position REFUSES — a returned address would surface in the caller
/// as an ordinary call result outside every audit. Everything else (Store in either
/// operand, `GEP`/`PtrToInt`/`ICmp`, `PtrFromParts`, `CallIndirect`, any unanticipated
/// position) refuses. Declarations and absent bodies refuse (nothing to audit).
fn seeded_param_uses_modeled(
    module: &Module,
    callee: FuncId,
    seeded: &[usize],
    visited: &mut HashSet<u32>,
    depth: u32,
) -> bool {
    if depth == 0 || !visited.insert(callee.index()) {
        return false; // depth exhausted or a call cycle: fail closed
    }
    let Some(func) = module.function_by_id(callee) else { return false };
    let Some(entry_block) = func.blocks.first() else { return false };
    let mut tracked: HashSet<ValueId> = HashSet::new();
    for &i in seeded {
        let Some((param, _ty)) = entry_block.params.get(i) else { return false };
        tracked.insert(*param);
    }
    // Closure: single-result Borrow/Copy pass-throughs join, exactly as in
    // `promoted_addr_closure`.
    loop {
        let mut grew = false;
        for blk in &func.blocks {
            for node in &blk.body {
                let joins = match &node.inst {
                    Inst::Borrow { ptr } => tracked.contains(ptr),
                    Inst::Copy { operand, .. } => tracked.contains(operand),
                    _ => false,
                };
                if joins {
                    let &[r] = node.results.as_slice() else { return false };
                    grew |= tracked.insert(r);
                }
            }
        }
        if !grew {
            break;
        }
    }
    // Audit every use of every tracked value (sentinel-remap probe, fail-closed).
    let max_id = func.max_value_id();
    if max_id == u32::MAX {
        return false;
    }
    let sentinel = ValueId::new(max_id + 1);
    for &v in &tracked {
        let map: HashMap<ValueId, ValueId> = std::iter::once((v, sentinel)).collect();
        for blk in &func.blocks {
            for node in &blk.body {
                let mut probe = node.inst.clone();
                trust_ir::mem2reg::rewrite_inst(&mut probe, &map);
                if probe == node.inst {
                    continue;
                }
                match &mut probe {
                    Inst::Load { ptr, volatile: false, .. } if *ptr == sentinel => {
                        *ptr = v;
                    }
                    Inst::Borrow { ptr } if *ptr == sentinel && node.results.len() == 1 => {
                        *ptr = v;
                    }
                    Inst::Copy { operand, .. }
                        if *operand == sentinel && node.results.len() == 1 =>
                    {
                        *operand = v;
                    }
                    Inst::Call { callee: next, args } => {
                        let mut positions: Vec<usize> = Vec::new();
                        for (i, a) in args.iter_mut().enumerate() {
                            if *a == sentinel {
                                *a = v;
                                positions.push(i);
                            }
                        }
                        if !positions.is_empty()
                            && !seeded_param_uses_modeled(
                                module,
                                *next,
                                &positions,
                                visited,
                                depth - 1,
                            )
                        {
                            return false;
                        }
                    }
                    _ => {}
                }
                if probe != node.inst {
                    return false;
                }
            }
        }
    }
    true
}

/// Trust (vtable slice 13): the per-function DEAD promoted-address set — results of
/// single-result `GlobalAddr`s of a mint-grammar (`__trust_promoted_*` /
/// `__trust_bytes_*`), immutable, initializer-BEARING, data-only, address-free-typed
/// global, whose closure under single-result `Borrow`/`Copy` has NO use outside that
/// closure: no Load, no Return, no Store, no call operand, nothing. Such an address
/// provably materializes no observation — nothing ever reads through it, compares it, or
/// lets it escape — so the walk may pass it WITHOUT any cross-module pairing (measured
/// population: sugar-ambiguity's two dead promoted addresses beside one live paired one,
/// and the oracle-only respell extras whose borrows are dead). The grammar +
/// initializer-bearing scope keeps every value-less symbolic carrier
/// (`__trust_symconst_*`, `__trust_constparam_*`, `__trust_opaque_*`, the vtable
/// identity) out: those are initializer-LESS and a different grammar, and admitting one
/// on a dead-use argument is still declined here — the slice-4 warning stands.
fn dead_promoted_addr_values(func: &Function, module: &Module) -> HashSet<ValueId> {
    let mut dead: HashSet<ValueId> = HashSet::new();
    let max_id = func.max_value_id();
    if max_id == u32::MAX {
        return dead;
    }
    let sentinel = ValueId::new(max_id + 1);

    // Per-seed proof: `Some(chain)` iff the seed's whole pass-through closure is CLOSED
    // (every use of every chain value is one of the chain's own single-result Borrow/Copy
    // nodes; anything else — Load, Return, Store, call/GEP/PtrFromParts/..., multi-result
    // — means the address is observable and the seed is NOT dead).
    let closed_chain = |seed: ValueId| -> Option<HashSet<ValueId>> {
        let mut chain: HashSet<ValueId> = std::iter::once(seed).collect();
        loop {
            let mut grew = false;
            for cblk in &func.blocks {
                for cnode in &cblk.body {
                    let joins = match &cnode.inst {
                        Inst::Borrow { ptr } => chain.contains(ptr),
                        Inst::Copy { operand, .. } => chain.contains(operand),
                        _ => false,
                    };
                    if joins {
                        let &[r] = cnode.results.as_slice() else { return None };
                        grew |= chain.insert(r);
                    }
                }
            }
            if !grew {
                break;
            }
        }
        for &v in &chain {
            let map: HashMap<ValueId, ValueId> = std::iter::once((v, sentinel)).collect();
            for ublk in &func.blocks {
                for unode in &ublk.body {
                    let mut probe = unode.inst.clone();
                    trust_ir::mem2reg::rewrite_inst(&mut probe, &map);
                    if probe == unode.inst {
                        continue;
                    }
                    let stays_in_chain = match &unode.inst {
                        Inst::Borrow { ptr } => *ptr == v && unode.results.len() == 1,
                        Inst::Copy { operand, .. } => *operand == v && unode.results.len() == 1,
                        _ => false,
                    };
                    if !stays_in_chain {
                        return None;
                    }
                }
            }
        }
        Some(chain)
    };

    for blk in &func.blocks {
        for node in &blk.body {
            let Inst::GlobalAddr { global } = &node.inst else { continue };
            let Some(def) = module.globals.get(global.as_usize()) else { continue };
            if !(def.name.starts_with("__trust_promoted_")
                || def.name.starts_with("__trust_bytes_"))
            {
                continue;
            }
            if def.mutable {
                continue;
            }
            let Some(init) = &def.initializer else { continue };
            if constant_materializes_uncomparable_identity(init) {
                continue;
            }
            if !ty_is_address_free(module, &def.ty, TY_CMP_DEPTH) {
                continue;
            }
            let &[seed] = node.results.as_slice() else { continue };
            if dead.contains(&seed) {
                continue;
            }
            if let Some(chain) = closed_chain(seed) {
                dead.extend(chain);
            }
        }
    }
    dead
}

/// True iff the entry's reachable closure contains any direct or indirect call — or anything the
/// traversal cannot resolve (fail-closed `true`).
///
/// Trust (vtable slice 13): this is no longer the promoted-global admission bound — that lane now
/// audits tracked addresses ACROSS linked direct calls (`promoted_addr_closure`'s Call arm +
/// `seeded_param_uses_modeled`, with call results never tracked and multi-function walks refusing
/// address returns). The remaining owner is the const-param COLUMN lane
/// (`const_param_column_plan`), whose single-function audit scope is its own documented rule.
fn closure_contains_call(module: &Module, entry: FuncId) -> bool {
    let Some(func) = module.function_by_id(entry) else {
        return true;
    };
    for blk in &func.blocks {
        for node in &blk.body {
            if matches!(node.inst, Inst::Call { .. } | Inst::CallIndirect { .. }) {
                return true;
            }
        }
    }
    false
}

/// Trust (vtable slice 10): the two producer mint families whose value-less globals carry a
/// PARAMETRIC read — a const-generic param (`lower_const_param`, deduped per param DefId) or a
/// generic assoc const (`__trust_symconst_`, deduped per `(def_id, args)`). Deliberately NOT the
/// `__trust_opaque_*` family (vtable metadata / opaque coercion carriers — those stand for a
/// value with an ADDRESS identity, not a scalar instantiation input) and NOT the promoted/bytes
/// mints (initializer-BEARING, owned by the slice-6/7/8 pairing lane).
const CONST_COLUMN_MINTS: [&str; 2] = ["__trust_constparam_", "__trust_symconst_"];

/// Shape key for column binding: `Bool` keys as `(1, false)` (no trust-ir integer has width 1,
/// so the key cannot collide), integers key as `int_shape`. `None` — floats, `Char`, aggregates,
/// pointers — refuses the column. Shape equality (not spelling equality) is the binding
/// condition because the two sides deliberately spell pointer-width scalars differently: the
/// producer's carrier is the faithful `Ty::Usize`/`Ty::Isize` while the oracle's
/// `ConstValue::ConstParam`/`OpaqueScalar` constants are width-collapsed to `U64`/`I64` — the
/// SAME 64-bit value semantics under the interpreter's own `int_shape` masking.
fn column_shape(t: &Ty) -> Option<(u32, bool)> {
    if matches!(t, Ty::Bool) {
        return Some((1, false));
    }
    int_shape(t)
}

/// Trust (vtable slice 10): the audited substitution plan binding ONE parametric column to both
/// sides' occurrence sites. Node coordinates are `(block index, node index)` into the ENTRY
/// function, captured before any mutation and applied by positional rebuild.
struct ConstColumnPlan {
    /// The column's canonical type — the PRODUCER carrier's spelling. Drives `sample_values`.
    column_ty: Ty,
    /// THIR-side carrier `GlobalAddr` nodes (removed; their only users are the Loads below).
    thir_drop: Vec<(usize, usize)>,
    /// THIR-side carrier `Load` nodes → `Inst::Const { column_ty, sample }` (results kept).
    thir_subst: Vec<(usize, usize, Ty)>,
    /// Oracle-side live `Undef` nodes → `Inst::Const { demanded ty, sample }` (results kept).
    oracle_subst: Vec<(usize, usize, Ty)>,
}

/// Trust (vtable slice 10): audit both modules for the single-parameter column binding.
/// `None` = not admitted (the caller keeps the Live-havoc skip, note verbatim).
///
/// THE PAIRING ARGUMENT, stated once. The oracle side cannot NAME its parametric reads: by the
/// time they are `Inst::Undef`s the bridge has discarded `ConstValue::ConstParam`'s
/// `{index, name}` (deliberately — each occurrence an independent fresh symbol), and
/// `ConstValue::OpaqueScalar` (generic assoc consts) carries no identity AT ALL. So
/// per-occurrence name pairing is impossible without a trust-types format change. Instead the
/// binding is proven by UNIQUENESS — "which parameter does this Undef read" must have exactly
/// one possible answer:
///
/// * **Exactly ONE distinct const-family carrier on the THIR side.** The producer's
///   `symbolic_consts` ledger dedupes the global per parameter identity (per param `DefId`; per
///   `(def_id, args)` for assoc consts), so one distinct global IS one distinct parameter. A
///   second distinct carrier — a genuinely multi-parameter body — refuses outright.
/// * **Occurrence counts match: producer carrier `Load`s == oracle live `Undef`s.** Both sides
///   lower the same body, so a parametric read appears once per source occurrence on each side.
///   This is the misalignment tripwire: an oracle Undef of ANY OTHER origin (a second
///   parametric read the producer evaluated concretely, or an unrelated havoc) breaks the
///   count and refuses — without it, binding "all live Undefs" to the single column would
///   assert a wrong value model for the foreign read and could mint a manufactured verdict.
/// * **Shape equality per occurrence** (`column_shape`): the demanded oracle type and the
///   producer carrier type must agree on width+signedness (or both be `Bool`).
///
/// Under those three conjuncts every parametric read on both sides is a read of the SAME single
/// parameter, and realizing the same raw sample per side (each at its own spelling — the
/// enum/struct-column per-side-realization precedent) gives both executions the same
/// instantiation. Anything else about the audit fails CLOSED:
///
/// * Both entry closures must be call-free (single-function audit scope, the slice-7 rule).
/// * Every use of every carrier `GlobalAddr` result must be the `ptr` of a non-volatile
///   single-result `Load` at the carrier's type — the carrier's ADDRESS must never escape.
/// * NO other value-less global may be addressed in the entry at all (an `__trust_opaque_*`
///   vtable/coercion carrier alongside the column would leave an unmodeled havoc; refusing
///   keeps the body's existing class rather than churning it).
/// * Every live oracle Undef must be single-result, in the entry, with ONE consistent
///   consumer-demanded type (`demanded_column_ty`, fail-closed on any unanticipated consumer).
///
/// THE SLICE-4 TRAP DOES NOT APPLY: the value-less carrier is never admitted as module state
/// and never LOADED — both the `GlobalAddr` and the `Load` are removed from the interpreted
/// clones, so no zero-filled BSS read can ever be compared. The slice-7
/// `paired_admitted_promoted_globals` contract (initializer-BEARING, bit-exact) is untouched;
/// its mint-prefix scoping already excludes these carriers.
fn const_param_column_plan(thir_module: &Module, oracle: &Module) -> Option<ConstColumnPlan> {
    let entry = FuncId::new(0);
    if closure_contains_call(thir_module, entry) || closure_contains_call(oracle, entry) {
        return None;
    }
    let tf = thir_module.function_by_id(entry)?;
    let of = oracle.function_by_id(entry)?;

    // (1) THIR side: exactly one distinct const-family carrier; no other value-less global.
    let mut carrier: Option<(trust_ir::value::GlobalId, Ty)> = None;
    let mut thir_drop: Vec<(usize, usize)> = Vec::new();
    for (bi, blk) in tf.blocks.iter().enumerate() {
        for (ni, node) in blk.body.iter().enumerate() {
            let Inst::GlobalAddr { global } = &node.inst else { continue };
            let def = thir_module.globals.get(global.as_usize())?;
            if !CONST_COLUMN_MINTS.iter().any(|p| def.name.starts_with(p)) {
                if def.initializer.is_none() {
                    return None; // some OTHER value-less carrier: out of this lane's scope
                }
                continue; // initializer-bearing global: the slice-6/7/8 pairing lane owns it
            }
            if def.mutable || def.initializer.is_some() {
                return None; // not the wave-CP/symconst shape: refuse rather than guess
            }
            if !is_interpretable_scalar(&def.ty) || column_shape(&def.ty).is_none() {
                return None; // non-scalar carrier (Char included): not sampleable here
            }
            match &carrier {
                None => carrier = Some((*global, def.ty.clone())),
                Some((g, _)) if *g == *global => {}
                Some(_) => return None, // >=2 distinct parameters: pairing has no unique answer
            }
            thir_drop.push((bi, ni));
        }
    }
    let (_, column_ty) = carrier?;
    let carrier_shape = column_shape(&column_ty)?;

    // (2) THIR-side audit: every use of every carrier address is a conforming Load.
    for &(bi, ni) in &thir_drop {
        let node = &tf.blocks[bi].body[ni];
        let &[r] = node.results.as_slice() else { return None };
        for user in nodes_using(tf, r) {
            match &user.inst {
                Inst::Load { ty, ptr, volatile: false, .. }
                    if *ptr == r && *ty == column_ty && user.results.len() == 1 => {}
                _ => return None,
            }
        }
    }
    let carrier_addrs: HashSet<ValueId> = thir_drop
        .iter()
        .filter_map(|&(bi, ni)| tf.blocks[bi].body[ni].results.first().copied())
        .collect();
    let mut thir_subst: Vec<(usize, usize, Ty)> = Vec::new();
    for (bi, blk) in tf.blocks.iter().enumerate() {
        for (ni, node) in blk.body.iter().enumerate() {
            if let Inst::Load { ptr, .. } = &node.inst {
                if carrier_addrs.contains(ptr) {
                    thir_subst.push((bi, ni, column_ty.clone()));
                }
            }
        }
    }
    if thir_subst.is_empty() {
        return None; // an addressed-but-never-read carrier binds nothing
    }

    // (3) Oracle side: every non-dead-seed Undef anywhere in the module must be an entry-local,
    //     single-result, shape-compatible occurrence with one consistent demanded type.
    let osig = oracle.func_type(of.ty)?;
    let mut oracle_subst: Vec<(usize, usize, Ty)> = Vec::new();
    for func in &oracle.functions {
        for (bi, blk) in func.blocks.iter().enumerate() {
            for (ni, node) in blk.body.iter().enumerate() {
                let Inst::Undef { ty } = &node.inst else { continue };
                if undef_is_dead_seed(oracle, func, blk, node, ty) {
                    continue; // owned by the standard dead-seed substitution, per clone
                }
                if func.id != of.id {
                    return None; // a live havoc off the entry: out of scope
                }
                let &[r] = node.results.as_slice() else { return None };
                let subst_ty = demanded_column_ty(of, osig, r, ty)?;
                if column_shape(&subst_ty)? != carrier_shape {
                    return None;
                }
                oracle_subst.push((bi, ni, subst_ty));
            }
        }
    }
    // (4) The occurrence-count pairing tripwire (see the doc comment).
    if oracle_subst.len() != thir_subst.len() {
        return None;
    }
    Some(ConstColumnPlan { column_ty, thir_drop, thir_subst, oracle_subst })
}

/// Trust (vtable slice 10): the ONE type every consumer of a live oracle Undef demands — the
/// type the interpreter itself will enforce at each use site (`eval_binop`/`eval_icmp`/… check
/// operands against the INSTRUCTION's type, `Cast` against `src_ty`, `Return` against the
/// signature). The bridge's contextless `ConstParam`/`OpaqueScalar` emission width-collapses
/// pointer-sized scalars (`U64`) while faithful-dest consumers are stamped `Usize`, so the
/// declared Undef type and the consumer-demanded type can legitimately differ by spelling —
/// substituting at the DEMANDED type is what makes the rewritten module execute, and the
/// caller's shape conjunct pins that respell to the same width+signedness. Conflicting demands,
/// a demand in a pointer position, or ANY consumer variant outside this table fail closed.
/// Zero consumers (a dead parametric read — `let _ = T::CONST;`) keep the declared type.
fn demanded_column_ty(func: &Function, sig: &FuncTy, r: ValueId, declared: &Ty) -> Option<Ty> {
    let mut demand: Option<Ty> = None;
    fn merge(demand: &mut Option<Ty>, t: Ty) -> Option<()> {
        match demand {
            None => {
                *demand = Some(t);
                Some(())
            }
            Some(d) if *d == t => Some(()),
            Some(_) => None,
        }
    }
    for user in nodes_using(func, r) {
        match &user.inst {
            Inst::BinOp { ty, lhs, rhs, .. }
            | Inst::Overflow { ty, lhs, rhs, .. }
            | Inst::ICmp { ty, lhs, rhs, .. } => {
                if *lhs == r || *rhs == r {
                    merge(&mut demand, ty.clone())?;
                }
            }
            Inst::UnOp { ty, operand, .. } | Inst::Copy { ty, operand } => {
                if *operand == r {
                    merge(&mut demand, ty.clone())?;
                }
            }
            Inst::Cast { src_ty, operand, .. } => {
                if *operand == r {
                    merge(&mut demand, src_ty.clone())?;
                }
            }
            Inst::Select { ty, cond, then_val, else_val } => {
                if *cond == r {
                    merge(&mut demand, Ty::Bool)?;
                }
                if *then_val == r || *else_val == r {
                    merge(&mut demand, ty.clone())?;
                }
            }
            Inst::Store { ty, ptr, value, volatile: false, .. } => {
                if *ptr == r {
                    return None; // a parametric value used AS an address: out of model
                }
                if *value == r {
                    merge(&mut demand, ty.clone())?;
                }
            }
            Inst::Assert { cond } | Inst::Assume { cond } => {
                if *cond == r {
                    merge(&mut demand, Ty::Bool)?;
                }
            }
            Inst::CondBr { cond, then_args, else_args, .. } => {
                if then_args.contains(&r) || else_args.contains(&r) {
                    return None; // block-param flow: demanded type lives on the target block
                }
                if *cond == r {
                    merge(&mut demand, Ty::Bool)?;
                }
            }
            Inst::Return { values } => {
                for (i, v) in values.iter().enumerate() {
                    if *v == r {
                        merge(&mut demand, sig.returns.get(i)?.clone())?;
                    }
                }
            }
            _ => return None, // unanticipated consumer: fail closed
        }
    }
    Some(demand.unwrap_or_else(|| declared.clone()))
}

/// The typed sample constant for one column realization. Bool realizes as `Constant::Bool`
/// (never an integer carrier — the validator/interpreter reject non-{0,1} bools); integer
/// spellings realize as `Constant::Int` of the raw (every `sample_values` raw is in-range for
/// its width by construction, and `i128` carries `u64::MAX` exactly).
fn column_const(ty: &Ty, raw: i128) -> Constant {
    if matches!(ty, Ty::Bool) { Constant::Bool(raw != 0) } else { Constant::Int(raw) }
}

/// Rebuild `module`'s entry function with the plan applied at one sample value: `drops` removed
/// outright, `substs` replaced by `Inst::Const { ty, value }` IN PLACE — same node, same
/// results, so every downstream operand reference and the observation walk see a defined
/// constant where the parametric read was. Positional indices refer to the PRE-rebuild body,
/// which is why removal and replacement happen in a single pass.
fn apply_const_column(
    module: &Module,
    drops: &[(usize, usize)],
    substs: &[(usize, usize, Ty)],
    raw: i128,
) -> Option<Module> {
    let mut m = module.clone();
    let fidx = m.functions.iter().position(|f| f.id == FuncId::new(0))?;
    for (bi, blk) in m.functions[fidx].blocks.iter_mut().enumerate() {
        let old = std::mem::take(&mut blk.body);
        let mut new_body = Vec::with_capacity(old.len());
        for (ni, mut node) in old.into_iter().enumerate() {
            if drops.contains(&(bi, ni)) {
                continue;
            }
            if let Some((_, _, ty)) = substs.iter().find(|(b, n, _)| (*b, *n) == (bi, ni)) {
                node.inst = Inst::Const { ty: ty.clone(), value: column_const(ty, raw) };
            }
            new_body.push(node);
        }
        blk.body = new_body;
    }
    Some(m)
}

/// Trust (vtable slice 10): the sample-column comparator — `Some(report)` iff the plan admits
/// the pair, `None` keeps the caller's Live-havoc skip verbatim.
///
/// One outer iteration per column sample (the same `sample_values` boundary+mid machinery every
/// scalar parameter column uses; a const param IS semantically an extra parameter for sampling
/// purposes). Each iteration substitutes the sample into per-sample CLONES of both modules,
/// re-runs the standard oracle tail on the clone (dead-seed substitution, then the slice-6
/// promoted respell — same order as the main path), and delegates to `compare_entries`
/// unchanged: the inner run still enforces signature agreement, the sampling floor, the
/// observation tail gate, and every divergence channel. Aggregation:
///
/// * ANY inner divergence returns immediately as the body's verdict, the note suffixed with the
///   column value that produced it.
/// * ANY inner coverage-only skip other than the trap-only value floor returns that inner
///   report verbatim (fail-closed; the body re-classes to the inner skip's own bucket).
/// * A trap-only inner run (both sides reproduced the same trap at this column value — the
///   floor note) is a legitimate per-sample trap agreement: recorded, not fatal.
/// * Agreement requires at least one inner run with a REAL value sample, mirroring step (8);
///   all-trap columns report the floor note verbatim.
///
/// The claim mode is unchanged from every other sampled input: per-sample agreement
/// (`DiffMode::Agreed` means "on sampled inputs"), never a ∀-instantiation claim.
fn const_param_column_compare(thir_module: &Module, oracle: &Module) -> Option<DiffReport> {
    let plan = const_param_column_plan(thir_module, oracle)?;
    let samples = sample_values(&plan.column_ty);
    if samples.is_empty() {
        return None;
    }
    let mut total_checked = 0usize;
    let mut agreed_runs = 0usize;
    let mut floor_report: Option<DiffReport> = None;
    for &v in &samples {
        let thir_local = apply_const_column(thir_module, &plan.thir_drop, &plan.thir_subst, v)?;
        let oracle_local = apply_const_column(oracle, &[], &plan.oracle_subst, v)?;
        // Tripwire parity with the main path: the substituted THIR clone must stay Undef-free.
        if module_has_undef(&thir_local) {
            return None;
        }
        let oracle_local = match classify_undefs(&oracle_local) {
            UndefClass::None => oracle_local,
            UndefClass::DeadSeeds => substitute_dead_seeds(oracle_local),
            // The plan claims to have consumed every live havoc; a survivor means the plan
            // and the classifier disagree — fail closed to the standard skip.
            UndefClass::Live => return None,
        };
        let mut oracle_local = oracle_local;
        respell_promoted_slots_as_globals(&mut oracle_local);
        let rep = compare_entries(&thir_local, FuncId::new(0), &oracle_local, FuncId::new(0));
        match rep.mode {
            DiffMode::Agreed => {
                total_checked += rep.samples_checked;
                agreed_runs += 1;
            }
            DiffMode::MirOracle => {
                let mut rep = rep;
                if let Some(last) = rep.notes.last_mut() {
                    last.push_str(&format!(" [const-param column {} = {v}]", plan.column_ty));
                }
                return Some(rep);
            }
            DiffMode::NotRun => {
                let floor = rep
                    .notes
                    .last()
                    .is_some_and(|n| n.starts_with("no value samples interpretable"));
                if floor {
                    floor_report = Some(rep); // trap-only at this column value: keep sampling
                } else {
                    return Some(rep); // any other incapacity: fail closed, inner note verbatim
                }
            }
        }
    }
    if agreed_runs == 0 {
        return floor_report; // every column value trap-only: the floor note, verbatim
    }
    Some(DiffReport {
        equal: true,
        unsupported: Vec::new(),
        notes: vec![format!(
            "THIR-trust-ir == MIR-trust-ir on {total_checked} sampled input(s) (differential \
             interpretation; const-param/assoc-const column {} sampled at {agreed_runs} \
             value(s), {} occurrence(s) bound per side)",
            plan.column_ty,
            plan.thir_subst.len()
        )],
        samples_checked: total_checked,
        mode: DiffMode::Agreed,
    })
}

/// Result of one side's unmodeled-observation walk: the first gap (if any), and the single
/// admitted promoted-global name (if the walk admitted one — see the cross-side consistency
/// check at the tail gate).
struct ObservationWalk {
    gap: Option<String>,
    /// Trust (vtable slice 13): every DISTINCT paired-global name admitted anywhere in the
    /// reachable closure. The per-FUNCTION ≤1-distinct bound is unchanged
    /// (`promoted_addr_closure` still refuses a second distinct name inside one function);
    /// a multi-function walk additionally refuses >1 distinct name PER SIDE after the walk
    /// (two functions each admitting a different name would make the cross-side "same
    /// immutable object" argument connect two different objects).
    admitted: BTreeSet<String>,
}

fn first_unmodeled_observation(
    module: &Module,
    entry: FuncId,
    paired: &BTreeSet<String>,
) -> ObservationWalk {
    let mut pending = vec![entry];
    let mut seen = HashSet::new();
    let mut admitted: BTreeSet<String> = BTreeSet::new();
    let mut address_returned = false;
    let gap = 'walk: loop {
        let Some(func_id) = pending.pop() else { break None };
        if !seen.insert(func_id) {
            continue;
        }
        let Some(func) = module.function_by_id(func_id) else {
            break Some(format!("reachable function {func_id:?} is missing from the module"));
        };
        if func.blocks.is_empty() {
            break Some(format!("reachable function `{}` has no executable body", func.name));
        }

        // Trust: a `mut` scalar-enum local reassigned across >=2 blocks is promoted to a
        // PRIVATE non-escaping stack slot by the faithful-MIR oracle (Alloca+Store+Load),
        // while the direct-THIR producer keeps it in SSA. Such a slot has no observable
        // address identity and no observable final memory — the return/trap sample already
        // characterizes it fully — so it must NOT degrade the pair to coverage-only NotRun.
        let private_slots = private_nonescaping_slots(func);

        // Trust (vtable slice 13): the DEAD promoted-address set — a mint-grammar,
        // immutable, initializer-bearing, data-only, address-free-typed global whose
        // address closure (single-result Borrow/Copy) has NO other use at all. Such an
        // address is never loaded through, never returned, never stored, never escapes —
        // the "observation" it would materialize does not exist, so it needs no pairing
        // (this is `private_nonescaping_slots`' argument applied to a global's address).
        // Computed BEFORE the paired audit and excluded from its seeds, so one dead chain
        // cannot burn the per-function ≤1-distinct-admitted budget (sugar-ambiguity's
        // measured shape: two dead promoted addresses beside one live paired one).
        let dead_addr = dead_promoted_addr_values(func, module);

        // Trust (vtable slice 7): the admitted promoted-global address closure — empty
        // (nothing admitted, every arm below behaves exactly as before) unless the caller
        // passed a paired-name set AND this function's audit proves every use of every
        // derived address is a modeled pass-through/load/return — or, since vtable
        // slice 13, a linked-call argument whose callee-side uses pass the seeded audit.
        // Fail-closed both ways.
        let audit = match promoted_addr_closure(func, module, paired, &dead_addr) {
            Some(a) if !paired.is_empty() => a,
            _ => AddrClosureAudit::default(),
        };
        let tracked = audit.tracked;
        if let Some(n) = audit.admitted {
            admitted.insert(n);
        }
        address_returned |= audit.address_returned;

        for block in &func.blocks {
            for node in &block.body {
                match &node.inst {
                    // A bodyful direct call has no effect beyond its callee's semantics. Inspect
                    // that callee exactly once; recursive call graphs terminate through `seen`.
                    Inst::Call { callee, .. } => {
                        pending.push(*callee);
                        continue;
                    }

                    // These effects are exactly the observations `compare_entries` already
                    // compares: returned values, control-selected returns, and traps.
                    Inst::Br { .. }
                    | Inst::CondBr { .. }
                    | Inst::Switch { .. }
                    | Inst::Return { .. }
                    | Inst::Assert { .. }
                    | Inst::Unreachable => continue,

                    // Trust (vtable slice 7): the ADMITTED promoted-global address — the ONE
                    // module-global observation the comparison DOES now carry. Why this is
                    // sound, given that step (7) raw-compares `InterpretPointer
                    // { allocation, offset }` on returned pointers:
                    //   * The paired global is immutable, initializer-bearing, and BIT-EXACT
                    //     content-equal across the two modules (`paired_admitted_promoted_
                    //     globals`), so a LOAD through the address reads the same bytes on
                    //     both sides by construction.
                    //   * If the ADDRESS itself is returned, the audit
                    //     (`promoted_addr_closure`) has proven that on THIS side every value
                    //     derived from it is a pure pass-through at offset 0 and that no
                    //     other addressable object can reach the return: any other
                    //     `GlobalAddr` fails the arm below, any escaping `Alloca` fails its
                    //     own arm, a private slot's address by definition never leaves
                    //     Load/Store ptr position, and (since slice 13, replacing the
                    //     call-free bound) a call boundary cannot smuggle one in — call
                    //     results are never tracked, a tracked call ARGUMENT requires the
                    //     seeded callee audit which refuses return positions, and a
                    //     multi-function walk refuses any tracked address in a Return
                    //     position outright. Under the <=1-distinct-admitted bound,
                    //     a returned non-null pointer on an admitted body can only BE the
                    //     single paired global's address at offset 0 — so the raw `Ptr`
                    //     agreement step (7) already measured is agreement about the SAME
                    //     named immutable object, not a synthetic-handle coincidence. The
                    //     slice-6 respell placed the oracle's `GlobalAddr` at the old
                    //     `Alloca`'s execution position, which is what keeps first-touch
                    //     allocation order (and therefore the raw ids) aligned; if it ever
                    //     skewed, the result is a step-(7) mismatch (fail-closed toward
                    //     divergence review), never a false green.
                    Inst::GlobalAddr { .. }
                        if !node.results.is_empty()
                            && node.results.iter().all(|r| tracked.contains(r)) =>
                    {
                        continue;
                    }
                    // Trust (vtable slice 13): a DEAD promoted address (see
                    // `dead_promoted_addr_values`) — the address provably has no use
                    // outside its own pure Borrow/Copy closure, so no observation exists
                    // for the comparison to miss. Needs no pairing: nothing is claimed
                    // about the value, because nothing ever reads or exposes it.
                    Inst::GlobalAddr { .. }
                        if !node.results.is_empty()
                            && node.results.iter().all(|r| dead_addr.contains(r)) =>
                    {
                        continue;
                    }
                    // Address/allocation identity and final memory are absent even though these
                    // result-producing instructions are not all DCE-style observable effects.
                    Inst::GlobalAddr { .. } => {
                        break 'walk Some(format!(
                            "reachable function `{}` materializes module-global state/provenance",
                            func.name
                        ));
                    }
                    // Trust: a private, non-escaping stack slot carries no observable
                    // address/memory — the interpreter outcome already characterizes it.
                    Inst::Alloca { .. }
                        if node.results.iter().all(|r| private_slots.contains(r)) =>
                    {
                        continue;
                    }
                    Inst::Alloca { .. } | Inst::HeapAlloc { .. } => {
                        break 'walk Some(format!(
                            "reachable function `{}` materializes allocation/provenance state",
                            func.name
                        ));
                    }
                    Inst::Const { value, .. }
                        if constant_materializes_uncomparable_identity(value) =>
                    {
                        break 'walk Some(format!(
                            "reachable function `{}` materializes callable/symbol identity",
                            func.name
                        ));
                    }
                    Inst::Cast { op: CastOp::ReifyFnPointer, .. } => {
                        break 'walk Some(format!(
                            "reachable function `{}` reifies module-local callable identity",
                            func.name
                        ));
                    }

                    // Trust: a store INTO a private non-escaping slot writes memory no
                    // observer can read; every other store still fails closed below.
                    Inst::Store { ptr, .. } if private_slots.contains(ptr) => continue,

                    // Trust (vtable slice 7): a shared `Borrow` of an admitted address is a
                    // pure pointer pass-through (the interpreter returns the same
                    // `InterpretPointer`; the audit already proved the result's own uses are
                    // modeled) — the slice-6 kept-Borrows arm. Every OTHER borrow still
                    // fails closed through `has_observable_effects` below.
                    // Trust (vtable slice 13): a Borrow inside a DEAD address closure is the
                    // same pure pass-through, and its result is proven use-free.
                    Inst::Borrow { ptr } if tracked.contains(ptr) || dead_addr.contains(ptr) => {
                        continue;
                    }

                    // Central TrustIR predicate: stores, atomics, volatile loads, indirect/opaque
                    // calls, coroutine/EH effects, permission/ARC changes, and future effectful
                    // instructions all fail closed without duplicating an inevitably stale list.
                    inst if inst.has_observable_effects() => {
                        break 'walk Some(format!(
                            "reachable function `{}` contains observable state not carried by the interpreter outcome",
                            func.name
                        ));
                    }
                    _ => {}
                }
            }
        }
    };

    // Trust (vtable slice 13): the two multi-function constraints, applied only to an
    // otherwise-clean walk (an earlier gap keeps its more specific note verbatim).
    // * >1 DISTINCT admitted name per side: two functions each admitting a different
    //   paired global would let the cross-side name-equality check compare one object
    //   against another — refuse the whole walk instead.
    // * a tracked (paired-global-derived) address in a Return position anywhere in a
    //   LINKED (multi-function) walk: a callee's returned address becomes an ordinary
    //   call result in its caller, where the slice-7 raw-`InterpretPointer` alignment
    //   argument (single function, first-touch allocation order) has no evidence — the
    //   single-function address-return admission is deliberately NOT extended across a
    //   call boundary.
    let gap = gap.or_else(|| {
        if admitted.len() > 1 {
            Some(format!(
                "the reachable closure admits {} distinct paired module globals \
                 ({:?}); the single-object address argument does not cover them",
                admitted.len(),
                admitted
            ))
        } else if seen.len() > 1 && address_returned {
            Some(
                "a paired module-global address reaches a return position inside a \
                 linked multi-function closure; the raw address-agreement argument is \
                 single-function only"
                    .to_string(),
            )
        } else {
            None
        }
    });

    ObservationWalk { gap, admitted }
}

/// Trust (B9-A): the interpretation-differential CORE, parameterized over the entry function on
/// each side — verbatim the former body of `compare` steps (2)-(8) (entry lookup, signature
/// resolve + vararg/param-class gates, structural signature agreement with the dual-spelling
/// reclass, sampled interpretation, the value-sample floor, and the Agreed tail). The per-body
/// hook path calls it with `FuncId::new(0)` on both sides; the crate-finalize SEAM calls it with
/// the assembled crate module's spliced entry vs the linked oracle BUNDLE's positional entry —
/// converting call-bearing clean bodies (the former clean-skip-direct-call class) into real
/// verdicts. Every note string is byte-identical to the pre-B9-A wording (classifier-stable).
pub(crate) fn compare_entries(
    thir_module: &Module,
    thir_entry: FuncId,
    oracle: &Module,
    oracle_entry: FuncId,
) -> DiffReport {
    let mut report = DiffReport::default();
    // (2) Both lowerings place the body's function at FuncId::new(0).
    let thir_fn = match thir_module.function_by_id(thir_entry) {
        Some(f) => f,
        None => {
            report.equal = false;
            report.mode = DiffMode::NotRun;
            report.notes.push("THIR-side module has no FuncId(0) (coverage-only skip)".to_string());
            return report;
        }
    };
    let oracle_fn = match oracle.function_by_id(oracle_entry) {
        Some(f) => f,
        None => {
            report.equal = false;
            report.mode = DiffMode::NotRun;
            report.notes.push("oracle module has no FuncId(0) (coverage-only skip)".to_string());
            return report;
        }
    };

    // (3) Resolve both signatures.
    let thir_sig: &FuncTy = match thir_module.func_type(thir_fn.ty) {
        Some(s) => s,
        None => {
            report.mode = DiffMode::NotRun;
            report.notes.push("THIR-side func type missing (coverage-only skip)".to_string());
            return report;
        }
    };
    let oracle_sig: &FuncTy = match oracle.func_type(oracle_fn.ty) {
        Some(s) => s,
        None => {
            report.mode = DiffMode::NotRun;
            report.notes.push("oracle func type missing (coverage-only skip)".to_string());
            return report;
        }
    };

    // (4) Interpretability gate: non-vararg; scalar int/bool/float params sample normally; Ptr/Unit
    //     params are admitted OPAQUELY when proven never-read in BOTH modules (module docs);
    //     everything else is a precise coverage-only skip. Only scalars count against the cap.
    if thir_sig.is_vararg || oracle_sig.is_vararg {
        report.mode = DiffMode::NotRun;
        report.notes.push("vararg signature is non-interpretable (coverage-only skip)".to_string());
        return report;
    }
    // Trust (Q1): decide the pointer-param INPUT lane before classifying, because three of its
    // conditions are whole-signature (exactly one read pointer, every other param id-free, no
    // pointer return). `None` leaves every note below byte-identical to today.
    let pointer_lane =
        pointer_param_input_lane(thir_module, thir_fn, thir_sig, oracle, oracle_fn, oracle_sig);
    let mut classes: Vec<ParamClass> = Vec::with_capacity(thir_sig.params.len());
    for (i, t) in thir_sig.params.iter().enumerate() {
        if is_interpretable_scalar(t) {
            classes.push(ParamClass::Scalar);
            continue;
        }
        // Trust (Q1): the materialized-referent lane claims this param before the opacity
        // machinery sees it; the pointee it samples over is carried in `ptr_pointees` below.
        if matches!(&pointer_lane, Some(PointerLane::Scalar { index, .. }) if *index == i) {
            classes.push(ParamClass::PtrTo);
            continue;
        }
        // Trust (B3/E6): an eligible FIRST-CLASS enum param samples as EnumDef-valid
        // (variant, payload) values, realized per side at the args site. Eligibility
        // here is THIR-LOCAL only (resolvable def, canonical tag, all-scalar payload
        // fields); cross-side structural identity — variant count, field arity + tys,
        // EFFECTIVE discriminants, canonical tag repr — is proven by sig_tys_agree
        // below BEFORE any sample is built (the mid-B3 spelling-split bodies fail
        // closed there, never sampled). Ineligible enums fall through to the
        // byte-identical non-scalar refusal.
        if let Ty::Enum(eid) = t {
            let eligible = thir_module.enum_def(*eid).is_some_and(|d| {
                !d.variants.is_empty()
                    && d.variants.len() <= MAX_ENUM_SAMPLES
                    && d.canonical_tag_repr().is_some()
                    && d.effective_discriminants().is_some()
                    && d.variants.iter().all(|v| {
                        v.fields
                            .iter()
                            // Trust (B3-2c): a canonical Unit field (the ZST-family
                            // admission respell) samples value-lessly — its
                            // realization is InterpretValueKind::Unit, no raw needed.
                            .all(|f| is_interpretable_scalar(f) || matches!(f, Ty::Unit))
                    })
            });
            if eligible {
                classes.push(ParamClass::Enum);
                continue;
            }
        }
        // Trust (aggregate param lane): an eligible BY-VALUE STRUCT param samples as a
        // positional aggregate of its scalar leaves, realized per side at the args site.
        //
        // Unlike the `Enum` arm above, eligibility here is TWO-SIDED and is checked BEFORE
        // the body is admitted, not left to `sig_tys_agree` at step (5). That is deliberate:
        // today every struct param returns the byte-identical non-scalar refusal below and
        // therefore NEVER REACHES step (5), so admitting one on a THIR-local test alone would
        // newly expose it to the divergence-publication channel on a SPELLING split — exactly
        // the divergence-manufacturing hole the B3-3 tuple-vs-struct reclass and TEST_P1S3_Foo
        // both came from. Two-sided admission keeps an unmarshallable shape on its existing
        // `not-run`, and admits only shapes whose marshalling is identical on both sides.
        //
        // `struct_param_admissible` is also STRICTER than `tys_agree`'s struct arm, which
        // compares field COUNT and field TYPES only: it additionally requires the two
        // `StructDef`s to agree on field NAMES, pairwise and recursively. Both producers read
        // that name from the SAME rustc `FieldDef` in source-declaration index order
        // (`trust-thir-lower`'s `register_struct` over `non_enum_variant().fields`;
        // `trust-mir-extract`'s `convert_ty_inner` over `adt_def.all_fields()`), so equality
        // is provable and cheap — and it is what pins FIELD IDENTITY rather than merely field
        // shape. Without it, `MemoryRegion { AllocationId, usize, usize }` would compare equal
        // to itself with its two `usize` fields transposed, and a positional marshalling would
        // then feed the two sides semantically different inputs.
        if let (Ty::Struct(_), Some(ot @ Ty::Struct(_))) = (t, oracle_sig.params.get(i)) {
            if struct_param_admissible(thir_module, oracle, t, ot) {
                classes.push(ParamClass::Struct);
                continue;
            }
        }
        // Trust (B2-3): a trait-object fat param joins the opacity-provable set — like
        // `Ty::Ptr` it is admitted ONLY under the two-sided `param_never_read` proof
        // below, preserving the Opaque-sampleability the class had when `&dyn` was
        // spelled thin. Slice/Str fat params stay non-interpretable (their values are
        // READ by the slice lanes; sampling them needs the B4 memory model).
        if !matches!(t, Ty::Ptr | Ty::Unit | Ty::FatPtr(trust_ir::FatPtrKind::TraitObject { .. })) {
            report.mode = DiffMode::NotRun;
            report.notes.push(
                "non-scalar parameter type is non-interpretable (coverage-only skip)".to_string(),
            );
            return report;
        }
        // Fail-closed opacity proof, on BOTH sides.
        match (param_never_read(thir_fn, i), param_never_read(oracle_fn, i)) {
            (Ok(true), Ok(true)) => classes.push(ParamClass::Opaque),
            (Ok(false), _) | (_, Ok(false)) => {
                report.mode = DiffMode::NotRun;
                // Trust (Q1, Slice B ceiling probe): the referent is a whole AGGREGATE whose byte
                // layout was proven to agree across both sides, so this body is materializable —
                // it is just not sampled YET (the aggregate sampler is the follow-on lane). Given
                // its own class so the follow-on's yield is measured on the corpus instead of
                // estimated from the `#[derive(Clone)]`-on-`Copy` file survey.
                if matches!(
                    &pointer_lane,
                    Some(PointerLane::AggregateCeiling { index }) if *index == i
                ) {
                    report.notes.push(format!(
                        "param {i} ({t}) is READ through a layout-agreeing AGGREGATE referent — \
                         materializable, aggregate referent sampling not implemented \
                         (coverage-only skip)"
                    ));
                    return report;
                }
                report.notes.push(format!(
                    "param {i} ({t}) is READ (dereferenced/used) — opaque sampling refused \
                     (coverage-only skip)"
                ));
                return report;
            }
            (Err(e), _) | (_, Err(e)) => {
                report.mode = DiffMode::NotRun;
                report.notes.push(format!("opacity scan failed ({e}); coverage-only skip"));
                return report;
            }
        }
    }
    // Trust (B3/E6): enum columns enter the product, so they count against the cap
    // (the note string stays verbatim — it is a classifier key).
    // Trust (aggregate param lane): struct columns do too, for the same reason.
    // Trust (Q1): so does a materialized-referent column — it is a scalar column over the POINTEE.
    let scalar_params = classes
        .iter()
        .filter(|c| {
            matches!(
                c,
                ParamClass::Scalar | ParamClass::Enum | ParamClass::Struct | ParamClass::PtrTo
            )
        })
        .count();
    if scalar_params > MAX_PARAMS {
        report.mode = DiffMode::NotRun;
        report.notes.push(format!(
            "scalar param count {} exceeds differential cap {} (coverage-only skip)",
            scalar_params, MAX_PARAMS
        ));
        return report;
    }

    // (5) Interface divergence: the two front-ends must agree on the signature. Comparison is
    //     STRUCTURAL, not id-wise: each module numbers its own `StructId`/`TyId`/`FuncTyId`
    //     spaces (the producer's ids are first-seen positional; the oracle's are
    //     registration-order), so `Ty::Struct(0) == Ty::Struct(0)` raw-id equality would be
    //     both unsound (equal ids, different defs → false agreement) and incomplete (different
    //     ids, same def → false divergence). `tys_agree` resolves table-indexed types through
    //     their OWN module's tables and compares the resolved field-type shape, failing CLOSED
    //     (`Err` → coverage-only skip, never a silent verdict) on an unresolvable id, an
    //     unbounded nesting (recursive defs), or any table-indexed variant it does not model.
    match sig_tys_agree(&thir_module, &oracle, thir_sig, oracle_sig) {
        Ok(true) => {}
        Ok(false) => {
            // Trust (B3-3, RETIRED 2026-07-24): the legacy tuple-vs-struct
            // dual-spelling reclass lived here. B3-2c deleted the producer's
            // legacy `(I64-tag, payload)` enum model, so the split it papered
            // over cannot occur; a one-cycle LOUD tripwire then confirmed it
            // on the 9014-body burn-in (postbuild-b33-final: ZERO hits, and
            // the 7 tuple-vs-struct divergences of the waveYDCH baseline are
            // gone). Every signature mismatch is now published as a real
            // divergence — no enum-shaped exemption remains.
            report.equal = false;
            report.mode = DiffMode::MirOracle;
            report.notes.push(format!(
                "signature divergence: THIR {:?}->{:?} vs MIR {:?}->{:?}",
                thir_sig.params, thir_sig.returns, oracle_sig.params, oracle_sig.returns
            ));
            return report;
        }
        Err(why) => {
            report.equal = false;
            report.mode = DiffMode::NotRun;
            report.notes.push(format!(
                "signature comparability failure ({why}); coverage-only skip (fail-closed)"
            ));
            return report;
        }
    }

    // (5.5) Trust (wave-DA): THE ADT-INTERIOR BYTE-ARITHMETIC GATE. A body that walks an ADT
    //       interior by a literal rustc byte offset must not be interpreted, because the
    //       interpreter derives its own ADT image rather than reading that offset — see
    //       `first_adt_interior_byte_arithmetic` for the two consumer rules and why neither is a
    //       claim of rustc parity. Interpreting such a body compares two addresses that were
    //       derived by different rules and reports the result as a verdict.
    //
    //       This is where the invariant "no verdict in this programme has ever been minted from
    //       an executed ADT-interior byte offset" stops being a measurement and becomes a gate.
    //       Placed LAST among the pre-sampling guards on purpose: every body already skipped for
    //       an earlier reason keeps its existing note verbatim (the notes are the burn-down
    //       ratchet's classifier keys), so this fires only on a body that would OTHERWISE HAVE
    //       RUN. Measured at the time of landing: of the 1,270 clean-kernel bodies that emit this
    //       shape, ZERO reach this point at either opt level — every one is held by a gate that
    //       exists for some other reason (1,256 by the cross-module-call guard, 6 by the
    //       pointer-parameter gate, 8 by an oracle incapacity) — so it costs no verdict today and
    //       refuses the class the moment one of those reasons is relaxed.
    //
    //       SCOPED to the entry's REACHABLE CLOSURE, and that scoping is load-bearing rather than
    //       tidy: the whole-module spelling was measured withdrawing two real `seam: agreed`
    //       verdicts over a byte walk in `cache::TypeCheckCache::stats`, which neither entry can
    //       reach. See `first_adt_interior_byte_arithmetic`.
    //
    //       BOTH sides are checked. The oracle does not emit this shape today (the bridge's five
    //       `Inst::GEP` sites all carry a typed `pointee_ty`), so the second conjunct is free; it
    //       is present because the hazard is a property of the SHAPE, not of which front-end
    //       produced it.
    //
    //       FREEZE, as scoped: this edit makes the oracle ACCEPT STRICTLY LESS — it can only turn
    //       a would-be sample into `NotRun`, never a `NotRun` into an `Agreed`. That is the
    //       permitted direction.
    let adt_byte_walk = first_adt_interior_byte_arithmetic(thir_module, thir_entry)
        .map(|why| format!("THIR side: {why}"))
        .or_else(|| {
            first_adt_interior_byte_arithmetic(oracle, oracle_entry)
                .map(|why| format!("MIR oracle side: {why}"))
        });
    if let Some(why) = adt_byte_walk {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.notes.push(format!(
            "ADT-interior literal byte arithmetic ({why}); the interpreter derives its own ADT \
             layout and would execute an offset it did not derive; coverage-only skip"
        ));
        return report;
    }

    // (6) Sample space: cross-product of per-SCALAR-param boundary+mid values (one empty
    //     tuple when every param is opaque or there are none); opaque params contribute one
    //     placeholder each, outside the product.
    // Trust (B3/E6): enum params contribute an INDEX-ENCODED column (0..samples.len())
    // over a parallel abstract-samples table — the i128 product machinery stays
    // untouched; realization happens per side at the args site.
    let mut enum_samples: Vec<Option<Vec<(usize, Vec<i128>)>>> = vec![None; thir_sig.params.len()];
    // Trust (aggregate param lane): the struct twin of `enum_samples` — one abstract sample is
    // the FLAT depth-first list of scalar-leaf raws, side-portable because the two `StructDef`s
    // were proven to agree (shape AND field names) at the admission gate.
    let mut struct_samples: Vec<Option<Vec<Vec<i128>>>> = vec![None; thir_sig.params.len()];
    // Trust (Q1): the recovered referent type per param — the pointer twin of `enum_samples`.
    // `Some` exactly at the `ParamClass::PtrTo` index; the wrapper's signature and the args site
    // both read the sampled column at the POINTEE type, never at `Ty::Ptr`.
    let mut ptr_pointees: Vec<Option<Ty>> = vec![None; thir_sig.params.len()];
    if let Some(PointerLane::Scalar { index, pointee }) = &pointer_lane {
        ptr_pointees[*index] = Some(pointee.clone());
    }
    let mut per_param: Vec<Vec<i128>> = Vec::new();
    for (i, (t, c)) in thir_sig.params.iter().zip(classes.iter()).enumerate() {
        match c {
            ParamClass::Scalar => per_param.push(sample_values(t)),
            ParamClass::PtrTo => {
                let Some(pointee) = ptr_pointees[i].clone() else {
                    report.mode = DiffMode::NotRun;
                    report.notes.push(
                        "could not build sample argument (coverage-only skip): recovered \
                         referent type unavailable"
                            .to_string(),
                    );
                    return report;
                };
                per_param.push(sample_values(&pointee));
            }
            ParamClass::Struct => {
                let samples = (|| {
                    let Ty::Struct(sid) = t else { return None };
                    struct_abstract_samples(thir_module, *sid)
                })();
                let Some(samples) = samples else {
                    report.mode = DiffMode::NotRun;
                    report.notes.push(
                        "could not build sample argument (coverage-only skip): struct sample \
                         description unavailable"
                            .to_string(),
                    );
                    return report;
                };
                per_param.push((0..samples.len() as i128).collect());
                struct_samples[i] = Some(samples);
            }
            ParamClass::Enum => {
                let samples = (|| {
                    let Ty::Enum(eid) = t else { return None };
                    enum_abstract_samples(thir_module.enum_def(*eid)?)
                })();
                let Some(samples) = samples else {
                    report.mode = DiffMode::NotRun;
                    report.notes.push(
                        "could not build sample argument (coverage-only skip): enum sample \
                         description unavailable"
                            .to_string(),
                    );
                    return report;
                };
                per_param.push((0..samples.len() as i128).collect());
                enum_samples[i] = Some(samples);
            }
            ParamClass::Opaque => {}
        }
    }
    // (7) Differential interpretation: run both modules on every sample, compare return vectors.
    //
    // Asymmetry is deliberate. The MIR-side is the TRUSTED oracle; the THIR-side is UNDER TEST. So:
    //   * If only the ORACLE errors with an *incapacity* code (e.g. a SignatureMismatch from the
    //     MIR-bridge typing a constant at the wrong width — a known oracle limitation), that is NOT
    //     evidence the THIR lowering is wrong. We downgrade to coverage-only (`NotRun`), never a
    //     divergence verdict. The oracle erroring with a genuine *trap* (`Panic`/`UB`) while the
    //     THIR side produced a value IS a real divergence (the THIR failed to trap).
    //   * If only the THIR side errors, it is a verdict against THIR ONLY for THIR-internal defect
    //     codes (malformed IR, signature/type errors, traps); infra limits (fuel/unsupported) are
    //     coverage-only.
    //   * `Err`/`Err` is an agreement only when both reproduce the *same genuine trap*.
    // `Agreed` further requires at least one `(Ok, Ok)` value sample, so a value-returning function
    // can never pass vacuously on trap-only agreement.
    // Trust (Q1): materialize the referent. Both sides get an identically-shaped wrapper that
    // allocates the pointee, stores the sampled value, and calls the entry with the slot; the
    // sample column is over the POINTEE type, so `exec_sig` (not the entry signature) is what the
    // args site marshals against.
    //
    // `first_unmodeled_observation` below is deliberately NOT re-pointed at the wrapper — it stays
    // on `thir_entry`/`oracle_entry`. `wrappers_agree` is what pays for that: the wrapper's own
    // memory effects go uncompared, which is sound only because the two wrappers are the same
    // program, and that is ASSERTED here rather than argued.
    let mut wrapped: Option<(Module, FuncId, FuncTy, Module, FuncId, FuncTy)> = None;
    if let Some(PointerLane::Scalar { index, pointee }) = &pointer_lane {
        let built = build_pointee_wrapper(thir_module, thir_entry, thir_sig, *index, pointee)
            .zip(build_pointee_wrapper(oracle, oracle_entry, oracle_sig, *index, pointee));
        let Some(((tm, tf, ts), (om, of, os))) = built else {
            report.mode = DiffMode::NotRun;
            report.notes.push(
                "could not build sample argument (coverage-only skip): referent wrapper \
                 construction failed"
                    .to_string(),
            );
            return report;
        };
        // Scoped so the two wrapper borrows END before the modules move into `wrapped` below.
        let agreement = match (tm.function_by_id(tf), om.function_by_id(of)) {
            (Some(wa), Some(wb)) => wrappers_agree(wa, thir_entry, wb, oracle_entry),
            _ => Err("a wrapper is unresolvable after construction".to_string()),
        };
        if let Err(why) = agreement {
            report.mode = DiffMode::NotRun;
            report.notes.push(format!(
                "returns/traps not sampled: the two materialized-referent wrappers are not the \
                 same program ({why}); the uncompared-wrapper argument does not hold \
                 (coverage-only skip)"
            ));
            return report;
        }
        wrapped = Some((tm, tf, ts, om, of, os));
    }
    let (thir_exec_module, thir_exec_entry, thir_exec_sig) = match &wrapped {
        Some((m, f, s, ..)) => (m, *f, s),
        None => (thir_module, thir_entry, thir_sig),
    };
    let (oracle_exec_module, oracle_exec_entry, oracle_exec_sig) = match &wrapped {
        Some((.., m, f, s)) => (m, *f, s),
        None => (oracle, oracle_entry, oracle_sig),
    };

    let thir_interp = Interpreter::with_module(thir_exec_module);
    let oracle_interp = Interpreter::with_module(oracle_exec_module);
    let mut checked = 0usize;
    let mut value_samples = 0usize;
    // A comparison gap is coverage-only, but it must never hide a concrete mismatch in a later
    // return position or sampled execution. Retain the first diagnostic and continue searching;
    // only downgrade after the complete sample stream has produced no negative witness.
    let mut return_comparability_gap: Option<(Vec<i128>, String)> = None;

    // Stream the cartesian product. The previous eager helper retained up to
    // 4096 separately allocated tuples per body and repeatedly cloned every
    // prefix while constructing them; the interpreter consumes one tuple at a
    // time, so that memory and copying had no semantic purpose.
    for tuple in CartesianProduct::new(&per_param) {
        // Positional arg assembly: scalars consume the tuple left-to-right; opaque params
        // get their (never-evaluated, type-correct) placeholder.
        // Trust (B3/E6): args are constructed PER SIDE from that side's OWN module +
        // signature — a table-indexed param ty (`Ty::Enum(id)` today; FatPtr(Slice)
        // when its opacity lands) carries a module-LOCAL id, and the interpreter's
        // entry check is exact Ty equality. A one-sided construction failure must
        // never reach execute_func: a mistyped THIR-side sample would surface as a
        // THIR-defect error code and MINT A FALSE DIVERGENCE via the (Err, Ok) arm.
        // Trust (Q1): marshalled against the EXEC signature — for a materialized-referent body
        // that is the wrapper's, whose param `i` is the pointee type, so the `PtrTo` column
        // realizes as an ordinary scalar and the wrapper turns it into a pointer.
        let thir_args = build_side_args(
            thir_exec_module,
            thir_exec_sig,
            &classes,
            &enum_samples,
            &struct_samples,
            &tuple,
        );
        let oracle_args = build_side_args(
            oracle_exec_module,
            oracle_exec_sig,
            &classes,
            &enum_samples,
            &struct_samples,
            &tuple,
        );
        let (args_thir, args_oracle) = match (thir_args, oracle_args) {
            (Ok(a), Ok(b)) => (a, b),
            (Err(why), _) | (_, Err(why)) => {
                report.mode = DiffMode::NotRun;
                report
                    .notes
                    .push(format!("could not build sample argument (coverage-only skip): {why}"));
                return report;
            }
        };
        let decoded =
            decoded_enum_sample_suffix(&thir_module, thir_sig, &classes, &enum_samples, &tuple);

        let thir_out = thir_interp.execute_func(thir_exec_entry, args_thir);
        let oracle_out = oracle_interp.execute_func(oracle_exec_entry, args_oracle);

        match (thir_out, oracle_out) {
            (Ok(a), Ok(b)) => {
                checked += 1;
                value_samples += 1;
                // Trust: STRUCTURAL return comparison (same rationale as the step-(5)
                // signature comparison): a returned value's `ty` may be `Ty::Struct`/
                // `Ty::Array` under each module's own id numbering, so raw `InterpretValue`
                // equality would manufacture false verdicts either way. Kinds are compared
                // recursively (aggregates element-wise), types via `tys_agree`; an
                // unresolvable/unmodeled shape fails CLOSED as a coverage-only skip.
                match returns_agree(&thir_module, &oracle, &a.returns, &b.returns) {
                    Ok(true) => {}
                    Ok(false) => {
                        report.equal = false;
                        report.mode = DiffMode::MirOracle;
                        report.samples_checked = checked;
                        report.notes.push(format!(
                            "DIVERGENCE on input {:?}{decoded}: THIR returned {:?}, MIR oracle returned {:?}",
                            tuple, a.returns, b.returns
                        ));
                        return report;
                    }
                    Err(why) => {
                        if return_comparability_gap.is_none() {
                            return_comparability_gap = Some((tuple.clone(), why));
                        }
                    }
                }
            }
            // Both errored: a genuine agreement ONLY when both reproduce the same trap.
            (Err(ea), Err(eb)) => {
                if ea.code == eb.code && is_trap(ea.code) {
                    checked += 1;
                } else if errerr_thir_defect_divergence(ea.code, eb.code) {
                    // The THIR side errored with a genuine LOWERING DEFECT (malformed
                    // IR / type / signature error — see `is_thir_defect`) while the
                    // oracle's error is merely an infra limit (e.g. `OutOfFuel`,
                    // `Unsupported*`). Without this arm the differing codes fall through
                    // to the `NotRun` coverage-only skip below, HIDING a real THIR
                    // defect behind the oracle's incidental incapacity. Report it as a
                    // verdict against THIR, mirroring the `(Err, Ok)` MirOracle arm.
                    report.equal = false;
                    report.mode = DiffMode::MirOracle;
                    report.samples_checked = checked;
                    report.notes.push(format!(
                        "DIVERGENCE on input {:?}{decoded}: THIR errored with a lowering defect ({}) \
                         while the MIR oracle only hit an infra limit ({}) — a genuine THIR \
                         defect masked by the oracle's incapacity, NOT a trap agreement",
                        tuple, ea, eb
                    ));
                    return report;
                } else {
                    report.equal = false;
                    report.mode = DiffMode::NotRun;
                    report.notes.push(format!(
                        "both sides errored non-trappily on input {:?} (THIR {}, oracle {}); \
                         coverage-only skip",
                        tuple, ea, eb
                    ));
                    return report;
                }
            }
            // Only the ORACLE errored. Incapacity ⇒ coverage-only; a real trap ⇒ THIR failed to trap.
            (Ok(a), Err(eb)) => {
                if is_trap(eb.code) {
                    report.equal = false;
                    report.mode = DiffMode::MirOracle;
                    report.samples_checked = checked;
                    report.notes.push(format!(
                        "DIVERGENCE on input {:?}{decoded}: THIR returned {:?} but MIR oracle proved a trap ({})",
                        tuple, a.returns, eb
                    ));
                    return report;
                }
                report.equal = false;
                report.mode = DiffMode::NotRun;
                report.notes.push(format!(
                    "MIR oracle could not interpret (incapacity {}); coverage-only skip — \
                     NOT a THIR divergence",
                    eb
                ));
                return report;
            }
            // Only the THIR side errored. A verdict against THIR only for THIR-internal defects.
            (Err(ea), Ok(b)) => {
                if is_thir_defect(ea.code) {
                    report.equal = false;
                    report.mode = DiffMode::MirOracle;
                    report.samples_checked = checked;
                    report.notes.push(format!(
                        "DIVERGENCE on input {:?}{decoded}: THIR errored ({}) but MIR oracle returned {:?}",
                        tuple, ea, b.returns
                    ));
                    return report;
                }
                report.equal = false;
                report.mode = DiffMode::NotRun;
                report
                    .notes
                    .push(format!("THIR side hit an infra limit ({}); coverage-only skip", ea));
                return report;
            }
        }
    }

    // (8) Agreement requires at least one real value sample (never a vacuous trap-only pass).
    if value_samples == 0 {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.notes.push(format!(
            "no value samples interpretable ({} trap-agreement sample(s)); coverage-only skip",
            checked
        ));
        return report;
    }

    if let Some((tuple, why)) = return_comparability_gap {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.samples_checked = checked;
        report.notes.push(format!(
            "return comparability failure on input {:?} ({why}); coverage-only skip \
             (fail-closed after checking every sample for a concrete divergence)",
            tuple
        ));
        return report;
    }

    // Trust: a return/trap match proves agreement only for the part of execution represented by
    // `InterpretOutcome`. Preserve every hard `MirOracle` return above, but never mint the green
    // tail when either entry's direct-call closure can mutate or expose discarded state. This is
    // deliberately a TAIL gate: an effectful pair whose returned values differ still supplies a
    // genuine negative witness and remains `MirOracle`; only an otherwise-green claim degrades to
    // the coverage-only state.
    //
    // Trust (vtable slice 7): the walk takes the PAIRED promoted-global admission set —
    // pairing is by NAME over the `__trust_promoted_*`/`__trust_bytes_*` mints with
    // bit-exact initializer-content equality; see `paired_admitted_promoted_globals` for
    // why each conjunct is load-bearing.
    //
    // Trust (vtable slice 13): the call-free bound (`closure_contains_call`) is RETIRED.
    // It existed because a callee could return the admitted address as an un-audited
    // ordinary call result (`ptr_to_int(callee())` would then compare synthetic addresses
    // as a verdict). That hole is now closed INSIDE the audit instead of by disabling
    // admission wholesale: a tracked address may cross a direct call boundary only into a
    // linked bodyful callee whose seeded-parameter audit passes and REFUSES return
    // positions (`seeded_param_uses_modeled`); call results never join the tracked set;
    // and a multi-function walk refuses any tracked address in a Return position and any
    // second distinct admitted name per side (`first_unmodeled_observation`'s post-walk
    // constraints). Every single-function walk behaves byte-identically to slice 7.
    let paired: BTreeSet<String> = paired_admitted_promoted_globals(thir_module, oracle);
    let thir_walk = first_unmodeled_observation(thir_module, thir_entry, &paired);
    let mut oracle_admitted: BTreeSet<String> = BTreeSet::new();
    let mut observation_gap = thir_walk.gap.map(|why| format!("THIR side: {why}"));
    if observation_gap.is_none() {
        let oracle_walk = first_unmodeled_observation(oracle, oracle_entry, &paired);
        observation_gap = oracle_walk.gap.map(|why| format!("MIR oracle side: {why}"));
        oracle_admitted = oracle_walk.admitted;
    }
    // Trust (vtable slice 7): if the two sides each admitted a paired global but DIFFERENT
    // ones, the "same immutable object" argument above does not connect them — a returned
    // address on one side would be compared against a different object's address on the
    // other. Held fail-closed rather than assumed (set-shaped since slice 13; each side's
    // walk already refuses >1 distinct admitted name, so this compares two singletons).
    if observation_gap.is_none()
        && !thir_walk.admitted.is_empty()
        && !oracle_admitted.is_empty()
        && thir_walk.admitted != oracle_admitted
    {
        observation_gap = Some(format!(
            "the two sides admitted different paired module globals ({:?} vs {:?})",
            thir_walk.admitted, oracle_admitted
        ));
    }
    if let Some(why) = observation_gap {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.samples_checked = checked;
        report.notes.push(format!(
            "returns/traps matched on {checked} sampled execution(s), but {why}; \
             observable-effect comparison is not modeled (coverage-only skip)"
        ));
        return report;
    }

    report.equal = true;
    report.mode = DiffMode::Agreed;
    report.samples_checked = checked;
    let opaque_params = classes.iter().filter(|c| **c == ParamClass::Opaque).count();
    report.notes.push(if opaque_params > 0 {
        format!(
            "THIR-trust-ir == MIR-trust-ir on {} sampled input(s) (differential \
             interpretation; {} proven-never-read opaque param(s) as placeholders)",
            checked, opaque_params
        )
    } else {
        format!(
            "THIR-trust-ir == MIR-trust-ir on {} sampled input(s) (differential interpretation)",
            checked
        )
    });
    report
}

/// Comparison depth cap for `tys_agree`/`value_agree`. The producer refuses recursive Adts
/// (`adt_visit_stack`), so any chain deeper than this is either an oracle-side recursive def or
/// a pathological nest — both fail CLOSED (`Err` → coverage-only), never a verdict.
const TY_CMP_DEPTH: u32 = 32;

/// Trust: STRUCTURAL signature agreement across two independently-numbered modules (see the
/// step-(5) comment). `Ok(false)` is a genuine interface divergence; `Err` is a comparability
/// failure (unresolvable id / unmodeled table-indexed shape / depth) — always fail-closed.
fn sig_tys_agree(am: &Module, bm: &Module, a: &FuncTy, b: &FuncTy) -> Result<bool, String> {
    if a.is_vararg != b.is_vararg || a.params.len() != b.params.len() {
        return Ok(false);
    }
    // Trust (task #166): the DIVERGING-RETURN spelling split. A function that
    // never returns is spelled `-> [Never]` by the producer (it carries the
    // `!` type through) and `-> []` by the MIR oracle (a diverging body has no
    // return VALUES). Both are correct renderings of "does not return"; the
    // disagreement is a comparability limitation, not a semantic divergence,
    // so it must NOT be published on divergence-signature — the channel
    // reserved for real signature bugs (the TEST_P1S3_Foo lesson).
    //
    // NARROW by construction: exactly one side is `[Never]`, the other is
    // EMPTY, and the parameter lists still have to agree below. Every other
    // return-arity mismatch stays `Ok(false)` — a genuine divergence.
    let diverging_split = |x: &FuncTy, y: &FuncTy| {
        x.returns.len() == 1 && matches!(x.returns[0], Ty::Never) && y.returns.is_empty()
    };
    if diverging_split(a, b) || diverging_split(b, a) {
        for (x, y) in a.params.iter().zip(&b.params) {
            if !tys_agree(am, bm, x, y, TY_CMP_DEPTH)? {
                return Ok(false);
            }
        }
        return Err(
            "diverging-return spelling split (THIR `-> !` vs MIR no-return); coverage-only"
                .to_string(),
        );
    }
    if a.returns.len() != b.returns.len() {
        return Ok(false);
    }
    for (x, y) in a.params.iter().zip(&b.params).chain(a.returns.iter().zip(&b.returns)) {
        if !tys_agree(am, bm, x, y, TY_CMP_DEPTH)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Trust: do `a` (in module `am`) and `b` (in module `bm`) denote the same type SHAPE?
///
/// Table-indexed types are resolved through their OWN module's tables and compared by resolved
/// field-type shape — the only sound cross-module comparison (ids are module-local):
///   * `Struct`: same field count, fields pairwise agree (names/ids ignored — the oracle names
///     closure envs differently; the differential compares VALUES, which are positional).
///   * `Array`: same length, resolved element types agree.
///   * `Func`: same vararg-ness, resolved params/returns pairwise agree.
///   * `FatPtr(Slice)`: resolved element types agree.
/// Same-kind pairs of UNMODELED table-indexed variants (`Enum`/`Record`/`Closure`/`Sequence`/
/// `Set`) are `Err` — comparing their raw ids across modules would be a guess. Cross-kind pairs
/// and table-free leaves fall through to plain equality (`Ok(false)` for cross-kind — a real
/// divergence spelling, exactly the pre-struct behavior).
fn tys_agree(am: &Module, bm: &Module, a: &Ty, b: &Ty, depth: u32) -> Result<bool, String> {
    if depth == 0 {
        return Err("type nesting exceeds comparison depth (possible recursive def)".to_string());
    }
    match (a, b) {
        (Ty::Struct(x), Ty::Struct(y)) => {
            let dx = am
                .struct_def(*x)
                .ok_or_else(|| format!("THIR-side struct id {} unresolvable", x.index()))?;
            let dy = bm
                .struct_def(*y)
                .ok_or_else(|| format!("oracle-side struct id {} unresolvable", y.index()))?;
            if dx.fields.len() != dy.fields.len() {
                return Ok(false);
            }
            for (fx, fy) in dx.fields.iter().zip(&dy.fields) {
                if !tys_agree(am, bm, &fx.ty, &fy.ty, depth - 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Ty::Array(x, nx), Ty::Array(y, ny)) => {
            if nx != ny {
                return Ok(false);
            }
            let ex = am.ty(*x).ok_or_else(|| format!("THIR-side type id {x} unresolvable"))?;
            let ey = bm.ty(*y).ok_or_else(|| format!("oracle-side type id {y} unresolvable"))?;
            tys_agree(am, bm, ex, ey, depth - 1)
        }
        (Ty::Tuple(xs), Ty::Tuple(ys)) => {
            if xs.len() != ys.len() {
                return Ok(false);
            }
            for (x, y) in xs.iter().zip(ys) {
                if !tys_agree(am, bm, x, y, depth - 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Ty::Vector(x, nx), Ty::Vector(y, ny)) => {
            if nx != ny {
                return Ok(false);
            }
            tys_agree(am, bm, x, y, depth - 1)
        }
        (Ty::Ref(x), Ty::Ref(y))
        | (Ty::RefMut(x), Ty::RefMut(y))
        | (Ty::PtrConst(x), Ty::PtrConst(y))
        | (Ty::PtrMut(x), Ty::PtrMut(y))
        | (Ty::Rc(x), Ty::Rc(y)) => tys_agree(am, bm, x, y, depth - 1),
        (Ty::Func(x), Ty::Func(y)) => {
            let fx = am
                .func_type(*x)
                .ok_or_else(|| format!("THIR-side func-type id {} unresolvable", x.as_usize()))?;
            let fy = bm
                .func_type(*y)
                .ok_or_else(|| format!("oracle-side func-type id {} unresolvable", y.as_usize()))?;
            if fx.is_vararg != fy.is_vararg
                || fx.params.len() != fy.params.len()
                || fx.returns.len() != fy.returns.len()
            {
                return Ok(false);
            }
            for (x, y) in fx.params.iter().zip(&fy.params).chain(fx.returns.iter().zip(&fy.returns))
            {
                if !tys_agree(am, bm, x, y, depth - 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Ty::FatPtr(kx), Ty::FatPtr(ky)) => {
            use trust_ir::FatPtrKind;
            match (kx, ky) {
                (FatPtrKind::Slice(x), FatPtrKind::Slice(y)) => {
                    let ex =
                        am.ty(*x).ok_or_else(|| format!("THIR-side type id {x} unresolvable"))?;
                    let ey =
                        bm.ty(*y).ok_or_else(|| format!("oracle-side type id {y} unresolvable"))?;
                    tys_agree(am, bm, ex, ey, depth - 1)
                }
                (FatPtrKind::Str, FatPtrKind::Str) => Ok(true),
                // Trust (B2-3): trait-object ids are CONTENT hashes of the principal
                // trait's def path, minted by the ONE shared helper
                // (`trust_ir::stable_trait_object_id`) on both producers from the same
                // `def_path_str` string — value equality IS def-path equality. (A hash
                // collision across distinct paths is tripwired at the producer mint,
                // which fail-closes the body before any comparison happens.)
                (
                    FatPtrKind::TraitObject { trait_id: x },
                    FatPtrKind::TraitObject { trait_id: y },
                ) => Ok(x == y),
                // A WITHIN-FatPtr kind mismatch (Str vs TraitObject, Slice vs Str, …) is
                // a producer spelling split, not a semantic verdict — the raw `kx == ky`
                // leaf this replaces would have manufactured a DIVERGENCE the moment both
                // producers emit multiple fat kinds. Err keeps the body coverage-only
                // (`NotRun`), the cross-kind guard's precedent below.
                _ => Err("fat-pointer kind mismatch (producer spelling split; coverage-only)"
                    .to_string()),
            }
        }
        // Trust (B2, RFC TRUST_IR_V2): fat-pointer spellings are MID-MIGRATION — B2-1
        // flips shared `&[T]` to first-class `Ty::FatPtr(Slice)` on BOTH producers,
        // but `&str` keeps the producer's legacy `Tuple([Ptr, I64])` model until the
        // B2-2 recognizer rework, while the ORACLE bridge (which cannot distinguish
        // `&str` from `&[u8]` — ty_convert spells both `Ref{Slice{u8}}`) respells the
        // whole class. A cross-kind pair falling to the `_ => Ok(a == b)` leaf would
        // report those bodies as DIVERGENCES when the truth is the documented split —
        // Err keeps them coverage-only (`NotRun`), the enum/closure-split precedent.
        (Ty::FatPtr(_), _) | (_, Ty::FatPtr(_)) => {
            Err("fat-pointer comparison not modeled (cross-kind fat spelling; documented \
             B2 migration residue)"
                .to_string())
        }
        // Trust (wave-5): ANY position involving a first-class `Ty::Enum` is a comparability
        // failure, not a verdict — the DOCUMENTED model split. The producer's general enum
        // path spells enums as `Ty::Enum` over an `EnumDef` (trust-ir's canonical tagged
        // union, the pinned interpreter's native shape); the MIR-side oracle spells the SAME
        // source enum as a FLATTENED struct (`__tag` + `__v{i}_{f}` union fields —
        // `trust_mir_extract::lower_enum_adt` → the bridge's Adt→Struct arm). Structurally
        // reconciling the two spellings (tag↔`__tag`, per-variant payload↔union slots) is a
        // real comparator feature, not an equality check — until it exists, a cross-kind
        // `Ok(false)` here would report every general-enum signature as a DIVERGENCE verdict
        // when the truth is "the two sides model enums differently by design". `Err` keeps
        // these bodies coverage-only (`NotRun`) — general enums land on the non-differential
        // surfaces; Option/Result-shaped enums deliberately stay on the legacy tuple spelling
        // (see `map_ty`'s enum arm) so their pre-existing verdict rows are untouched.
        // Trust (B3-1, RFC TRUST_IR_V2): BOTH sides can now spell an ELIGIBLE enum as
        // the format's first-class `Ty::Enum` (the producer via register_enum, the
        // oracle via the faithful-lane respell), so the same-kind pair compares
        // STRUCTURALLY through each module's OWN enum table — NEVER by raw EnumId
        // (the producer keys defs by (DefId, GenericArgs); the oracle dedups
        // structurally; the id spaces differ by construction). Agreement means:
        // same variant count, per-variant same field arity with pairwise
        // recursively-agreeing field types, EQUAL effective discriminants (the
        // REAL values, never variant indexes — the index-vs-discriminant seam),
        // and an EQUAL canonical tag repr (a dropped `#[repr(iN)]` hint on one
        // side would silently change the tag width the interpreter sizes).
        (Ty::Enum(x), Ty::Enum(y)) => {
            let dx = am
                .enum_def(*x)
                .ok_or_else(|| format!("THIR-side enum id {} unresolvable", x.index()))?;
            let dy = bm
                .enum_def(*y)
                .ok_or_else(|| format!("oracle-side enum id {} unresolvable", y.index()))?;
            if dx.variants.len() != dy.variants.len() {
                return Ok(false);
            }
            for (vx, vy) in dx.variants.iter().zip(&dy.variants) {
                if vx.fields.len() != vy.fields.len() {
                    return Ok(false);
                }
                for (fx, fy) in vx.fields.iter().zip(&vy.fields) {
                    if !tys_agree(am, bm, fx, fy, depth - 1)? {
                        return Ok(false);
                    }
                }
            }
            match (dx.effective_discriminants(), dy.effective_discriminants()) {
                (Some(ex), Some(ey)) if ex == ey => {}
                (Some(_), Some(_)) => return Ok(false),
                // An ill-formed def on either side is a comparability failure,
                // never a verdict (the validator rejects these at module level;
                // defense in depth here).
                _ => return Err("enum def without resolvable discriminants".to_string()),
            }
            // Trust (B3-3): the v31 layout descriptor is IDENTITY-BEARING —
            // both sides fill it from the SAME rustc layout query under
            // lockstep decline rules, so inequality (content OR presence) is
            // toolchain fill-rule drift, never a THIR-vs-MIR semantic
            // divergence. Err keeps such bodies coverage-only (the loud drift
            // tripwire) instead of publishing a manufactured verdict.
            // `field_names` deliberately never enter this arm (fidelity-only;
            // the field loop above compares `fields` element-wise — do NOT
            // refactor it to whole-EnumVariant equality, which would pull
            // names in via derived PartialEq).
            match (&dx.layout, &dy.layout) {
                (None, None) => {}
                (Some(lx), Some(ly)) if lx == ly => {}
                (Some(_), Some(_)) => {
                    return Err(
                        "enum layout descriptors disagree (producer/oracle fill drift;                          coverage-only)"
                            .to_string(),
                    );
                }
                _ => {
                    return Err(
                        "enum layout descriptor present on one side only (fill-gate                          asymmetry; coverage-only)"
                            .to_string(),
                    );
                }
            }
            match (dx.canonical_tag_repr(), dy.canonical_tag_repr()) {
                (Some(rx), Some(ry)) if rx == ry => Ok(true),
                (Some(_), Some(_)) => Ok(false),
                _ => Err("enum def without a canonical tag repr".to_string()),
            }
        }
        // Trust (B3-1): the CROSS-KIND guard stays — an enum spelled first-class on
        // ONE side only (an ineligible/still-flat class, or mid-migration nesting
        // like a producer-Tuple vs oracle-Enum struct field) is a documented
        // spelling split, not a semantic verdict. Err keeps those positions
        // coverage-only instead of letting them fall to the raw-equality leaf —
        // the divergence-manufacturing hole TEST_P1S3_Foo sat in.
        (Ty::Enum(_), _) | (_, Ty::Enum(_)) => {
            Err("enum spelled first-class on one side only (mid-B3 spelling split; \
             coverage-only)"
                .to_string())
        }
        (Ty::Record(_), Ty::Record(_)) => Err("record-typed comparison not modeled".to_string()),
        // Trust (B6, RFC TRUST_IR_V2 — slice B): BOTH sides now spell a by-value FnOnce
        // capturing env as the format's first-class `Ty::Closure` (the producer via
        // map_ty's kind-split, the oracle via the bridge's `call`-driven respell), so
        // the pair compares STRUCTURALLY through both modules' closure/func tables:
        // the call signatures (params + returns, recursively) and the capture lists
        // (recursively, position-wise) must both agree — `ClosureTy` identity IS
        // (func, captures), the ty#4145 rule.
        (Ty::Closure(x), Ty::Closure(y)) => {
            let cx = am
                .closure_type(*x)
                .ok_or_else(|| format!("THIR-side closure ty id {} unresolvable", x.index()))?;
            let cy = bm
                .closure_type(*y)
                .ok_or_else(|| format!("oracle-side closure ty id {} unresolvable", y.index()))?;
            let fx = am
                .func_type(cx.func)
                .ok_or_else(|| "THIR-side closure func ty unresolvable".to_string())?;
            let fy = bm
                .func_type(cy.func)
                .ok_or_else(|| "oracle-side closure func ty unresolvable".to_string())?;
            if fx.is_vararg != fy.is_vararg
                || fx.params.len() != fy.params.len()
                || fx.returns.len() != fy.returns.len()
                || cx.captures.len() != cy.captures.len()
            {
                return Ok(false);
            }
            for (x, y) in fx
                .params
                .iter()
                .zip(&fy.params)
                .chain(fx.returns.iter().zip(&fy.returns))
                .chain(cx.captures.iter().zip(&cy.captures))
            {
                if !tys_agree(am, bm, x, y, depth - 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // A REMAINING cross-kind pair (one side `Ty::Closure`, the other the legacy
        // `closure_env::` struct or tuple spelling) is the documented mid-migration
        // residue — a bridge-side `call: None` refinement, or a Fn/FnMut env whose two
        // spellings deliberately differ until v26. Err keeps those coverage-only
        // (`NotRun`), exactly like the enum split above — never a manufactured
        // divergence verdict.
        (Ty::Closure(_), _) | (_, Ty::Closure(_)) => {
            Err("closure-typed comparison not modeled (cross-kind closure spelling; documented \
             B6 migration residue)"
                .to_string())
        }
        (Ty::Sequence(_), Ty::Sequence(_)) => {
            Err("sequence-typed comparison not modeled".to_string())
        }
        (Ty::Set(..), Ty::Set(..)) => Err("set-typed comparison not modeled".to_string()),
        // Trust (B3-2b G0): a NESTED cross-spelling enum pair — an opaque-lane enum
        // field (Ty::Bool/Ty::Unit under the OPTFLAG/wave-EL collapse, or the legacy
        // Ty::Tuple tag model) on one side vs the oracle's flattened Ty::Struct on the
        // other, appearing as a FIELD of a (Struct, Struct) pair. (The top-level
        // tuple-vs-struct reclass this arm once complemented was RETIRED in B3-3
        // on a zero-hit burn-in; this nested arm is NOT dead — the plan records 7
        // live hits — and absent it the pair would
        // fall to the raw-equality leaf below → Ok(false) → a MANUFACTURED
        // signature-divergence VERDICT (the exact 2a analog that minted 12
        // partial_cmp divergences before the top-level reclass was widened). A
        // documented model split, not a semantic divergence: Err → coverage-only
        // NotRun. QUARANTINE: this broad leaf-shape rule does not carry enum
        // provenance and can therefore mask a genuine nested mismatch. It is
        // coverage accounting only and MUST NOT be cited as parity evidence.
        // A future widening must bind both sides to the same enum definition
        // before producing an Agreed verdict. A genuine (Struct, Struct) nested
        // pair hits the arm above and never reaches here.
        (Ty::Bool | Ty::Unit | Ty::Tuple(_), Ty::Struct(_))
        | (Ty::Struct(_), Ty::Bool | Ty::Unit | Ty::Tuple(_)) => Err(
            "nested spelling-split G0 quarantine (no enum provenance); coverage-only NotRun, not parity evidence"
                .to_string(),
        ),
        // Trust (vtable slice 12): the ARRAY-SPELLING quarantine. Trust (vtable slice 15,
        // NARROWED SCOPE): the producer now spells SCALAR-element `[T; N>0]` first-class
        // `Ty::Array` (lib.rs `map_ty`), so those positions reach the REAL (Array, Array) arm
        // above — resolved element + length — and can compare. What still lands here is the
        // AGGREGATE-element remainder (`[(usize,usize); 7]`, `[[T; N]; M]`, `[E; 3]` — the
        // producer's legacy `Ty::Tuple` spelling vs the oracle's `Ty::Array`) plus any
        // genuinely-mismatched pair. It stays a spelling split, not a semantic verdict:
        // before this arm the pair fell to the raw-equality leaf below → `Ok(false)` → a
        // MANUFACTURED "signature divergence" the moment such a body cleared its upstream
        // hold — exactly the trap slice 11 pinned (deriving-from's fully-covered
        // `Array(U32, 4)` lane). Err → coverage-only NotRun, the enum-split / closure-split /
        // fat-kind-mismatch precedent.
        // QUARANTINE, exactly like G0 above: this rule carries no array provenance and is
        // coverage accounting only — a future Agreed over the remaining pairs must first
        // align the aggregate-element spelling too (the map_ty comment's second half), not
        // weaken this arm into an equivalence.
        (Ty::Tuple(_), Ty::Array(..)) | (Ty::Array(..), Ty::Tuple(_)) => Err(
            "array-vs-tuple spelling split (producer spells [T; N>0] as Tuple, oracle as \
             Array); coverage-only"
                .to_string(),
        ),
        // Table-free leaves (scalars/Ptr/Unit/Never/Bool/floats) compare directly; any
        // CROSS-KIND pair also lands here as a plain inequality (a real divergence).
        _ => Ok(a == b),
    }
}

/// Trust: STRUCTURAL return-vector agreement (see the step-(7) comment). Kinds compare
/// recursively (aggregate-shaped kinds element-wise, everything else exactly — bit-level for
/// ints/floats, the pre-existing semantics); types compare via `tys_agree`.
fn returns_agree(
    am: &Module,
    bm: &Module,
    a: &[InterpretValue],
    b: &[InterpretValue],
) -> Result<bool, String> {
    values_agree_list(am, bm, a, b, TY_CMP_DEPTH)
}

fn values_agree_list(
    am: &Module,
    bm: &Module,
    xs: &[InterpretValue],
    ys: &[InterpretValue],
    depth: u32,
) -> Result<bool, String> {
    if xs.len() != ys.len() {
        return Ok(false);
    }
    let mut first_gap = None;
    for (index, (x, y)) in xs.iter().zip(ys).enumerate() {
        match value_agree(am, bm, x, y, depth) {
            Ok(true) => {}
            Ok(false) => return Ok(false),
            Err(why) => {
                if first_gap.is_none() {
                    first_gap = Some(format!("return value {index}: {why}"));
                }
            }
        }
    }
    match first_gap {
        Some(why) => Err(why),
        None => Ok(true),
    }
}

fn value_agree(
    am: &Module,
    bm: &Module,
    x: &InterpretValue,
    y: &InterpretValue,
    depth: u32,
) -> Result<bool, String> {
    if depth == 0 {
        return Err("value nesting exceeds comparison depth".to_string());
    }
    if !tys_agree(am, bm, &x.ty, &y.ty, depth)? {
        return Ok(false);
    }
    match (&x.kind, &y.kind) {
        (InterpretValueKind::Aggregate(xs), InterpretValueKind::Aggregate(ys))
        | (InterpretValueKind::Array(xs), InterpretValueKind::Array(ys))
        | (InterpretValueKind::Vector(xs), InterpretValueKind::Vector(ys))
        | (InterpretValueKind::Sequence(xs), InterpretValueKind::Sequence(ys)) => {
            values_agree_list(am, bm, xs, ys, depth - 1)
        }
        // These payloads contain ids minted independently by each module/execution. Raw equality
        // can false-green when both counters happen to allocate the same number. Establishing
        // callable equivalence requires body/lineage comparison, and frame handles are never a
        // cross-execution value, so keep either shape coverage-only.
        (InterpretValueKind::Closure { .. }, _)
        | (_, InterpretValueKind::Closure { .. })
        | (InterpretValueKind::FnDef(_), _)
        | (_, InterpretValueKind::FnDef(_))
        | (InterpretValueKind::Frame(_), _)
        | (_, InterpretValueKind::Frame(_)) => {
            Err("callable/frame identity comparison is not modeled".to_string())
        }
        // Everything else — scalar kinds, pointers, and any CROSS-KIND pair (plain
        // inequality) — compares exactly, byte-for-byte the pre-struct behavior.
        _ => Ok(x.kind == y.kind),
    }
}

/// Trust (B9-B1): true iff any function contains an `Inst::Assert` whose condition is defined
/// by a `Const Bool(false)` node — the bridge's diverging-panic-call VERIFICATION model
/// (lower.rs `is_panic_call` arm), which the interpreter must not treat as a trap reference.
pub(crate) fn oracle_has_const_false_assert(module: &Module) -> bool {
    for func in &module.functions {
        let mut false_ids: std::collections::HashSet<ValueId> = std::collections::HashSet::new();
        for blk in &func.blocks {
            for node in &blk.body {
                match &node.inst {
                    Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) } => {
                        if let Some(&r) = node.results.first() {
                            false_ids.insert(r);
                        }
                    }
                    Inst::Assert { cond } if false_ids.contains(cond) => return true,
                    _ => {}
                }
            }
        }
    }
    false
}

/// Trust (wave-DA): the FIRST **ADT-interior literal byte arithmetic** in `module`, named, or
/// `None`.
///
/// # What this recognizes, and why exactly this shape
///
/// A flat-byte `GEP` whose displacement is a compile-time literal and which is `inbounds` is this
/// producer's one spelling for "the address of a field inside an ADT, at rustc's byte offset".
/// All three sites that emit it are ADT-interior — the `&self.field` shared interior return
/// (`lib.rs:8665`), the `Deref`-accessor `&mut` interior (`lib.rs:14940`), and the by-REF enum
/// payload binding (`lib.rs:23921`, single-level and nested) — and all three take their number
/// from a `layout_of` query on rustc's layout. The producer's other two `GEP` sites are element
/// arithmetic, not ADT-interior, and are excluded by construction: the slice index scales a typed
/// `pointee_ty` and the string-literal byte walk is `inbounds: false`. Both byte spellings
/// (`I8`/`U8`) are matched so a respelling cannot slip past.
///
/// # Why it must gate the interpreter
///
/// The reference interpreter does not read that offset from the instruction stream — it derives
/// its OWN image of the ADT. For an enum it uses the producer-supplied
/// `EnumLayoutDescriptor` when one is present and otherwise trust-ir's CANONICAL tagged-union
/// layout, whose doc says in terms that it is "not a claim of rustc layout parity"
/// (`interpret.rs:2607`). For a STRUCT it has no descriptor path at all:
/// `interpret::struct_layout` (`interpret.rs:2543`) ignores `FieldDef::offset` entirely and lays
/// fields out C-style in DECLARATION order. So a producer byte offset executed by the interpreter
/// is a number one side derived from rustc and the other side did not derive at all — and any
/// verdict minted from it is a verdict about two different addresses.
///
/// Today no such verdict exists, because every body in this shape happens to be skipped for an
/// unrelated reason (the enum ones by the oracle's own address-walk refusal,
/// `trust-ir-bridge/src/lower.rs:1861`; the struct ones by the pointer-parameter interpretability
/// gate at step (4), which is a COVERAGE gate, not a soundness one, and which a future lane could
/// lift for reasons that have nothing to do with layout). This makes that accident a GATE.
///
/// # Scoped to the REACHABLE CLOSURE, not the whole module — and why that is not a weakening
///
/// The walk is `first_unmodeled_observation`'s, deliberately: that function is this model's own
/// definition of "what an interpretation of `entry` can observe", and the set of bodies whose
/// instructions can EXECUTE is the same set. A whole-module scan is not more conservative in any
/// useful sense, it is merely wrong about scope — MEASURED on clean-kernel at -O3, it withdrew the
/// `seam: agreed` verdicts of `<expr::types::BinderData as Default>::default` (1 sample) and
/// `env::origin::OriginTrust::needs_recheck` (3 samples) because `cache::TypeCheckCache::stats`
/// emits `gep inbounds i8, +64` somewhere else in the crate; the reachable closures of those two
/// entries are 3 and 2 functions and contain no byte walk at all. Withdrawing a verdict a body
/// earned is a cost, and paying it for a body that cannot run is a cost for nothing.
///
/// It is nevertheless WIDER than that walk in one direction: a function whose address is taken
/// (`Const { value: Constant::FnDef(..) }`) is followed too, because such a callee can be entered
/// through `CallIndirect` without ever appearing as an `Inst::Call { callee }`. Fail-closed on a
/// missing function, exactly as `first_unmodeled_observation` is.
///
/// FAIL-CLOSED and strictly subtractive: it can only turn a body that would have been SAMPLED
/// into `NotRun`. It cannot mint an `Agreed`, and it cannot move a flip — `flip.rs` reads
/// `DerivedAgreed` from the structural MIR comparator, not from this channel.
/// # wave-DZ: the walk now carries the CALLER'S literals into the callee
///
/// wave-DA judged each reachable function against its OWN constants only, so a displacement
/// materialized in a caller and handed to a callee that GEPs by its own parameter walked past
/// the gate (demonstrated by a passing adversarial test at review time, and recorded in the
/// wave-DA merge message as an admitted shape). The walk therefore carries, per reachable
/// function, the SET OF ENTRY-BLOCK PARAMETER POSITIONS that some reachable call site is proven
/// to pass a committed displacement into; [`committed_displacements`] seeds those params into
/// the callee's table. The ENTRY starts with an EMPTY mask, which is what keeps a byte GEP
/// indexed by a *sampled* parameter green — nothing has committed to a rustc offset there, and
/// that discrimination control is `element_arithmetic_and_non_literal_displacements_stay_green`.
///
/// An ADDRESS-TAKEN function (`Const { value: Constant::FnDef(..) }`) is entered with the FULL
/// mask, not the empty one: it can be reached through `CallIndirect` with arguments this walk
/// cannot see, so every parameter is assumed to carry a committed displacement. That is the
/// fail-closed direction for the one edge the walk cannot follow.
///
/// Termination: masks only ever GROW (a function is re-processed exactly when its known mask
/// gains a bit), and a mask has at most 64 bits, so each function is processed at most 65 times.
pub(crate) fn first_adt_interior_byte_arithmetic(module: &Module, entry: FuncId) -> Option<String> {
    // (function, mask of entry-block param indices proven to receive a committed displacement).
    let mut pending: Vec<(FuncId, u64)> = vec![(entry, 0)];
    let mut seen: HashMap<FuncId, u64> = HashMap::new();
    while let Some((func_id, mask)) = pending.pop() {
        let known = match seen.get(&func_id) {
            // Already judged with at least this much literal knowledge — nothing to re-derive.
            Some(&prev) if (prev | mask) == prev => continue,
            Some(&prev) => prev | mask,
            None => mask,
        };
        seen.insert(func_id, known);
        let Some(func) = module.function_by_id(func_id) else {
            return Some(format!("reachable function {func_id:?} is missing from the module"));
        };
        let committed = committed_displacements(func, known);
        if let Some(why) = function_adt_interior_byte_walk(func, &committed) {
            return Some(why);
        }
        for node in func.blocks.iter().flat_map(|b| b.body.iter()) {
            match &node.inst {
                Inst::Call { callee, args } => {
                    let mut callee_mask = 0u64;
                    for (position, arg) in args.iter().enumerate() {
                        if position < 64 && committed.contains_key(arg) {
                            callee_mask |= 1u64 << position;
                        }
                    }
                    pending.push((*callee, callee_mask));
                }
                // Address-taken: reachable through `CallIndirect` with unseen arguments, so
                // every parameter is assumed committed (fail-closed).
                Inst::Const { value: Constant::FnDef(callee), .. } => {
                    pending.push((*callee, u64::MAX))
                }
                _ => {}
            }
        }
    }
    None
}

/// The displacement values in `func` that are COMMITTED compile-time byte offsets — the table
/// [`function_adt_interior_byte_walk`] judges every flat-byte `GEP` against. `Some(k)` is a
/// known constant (so the diagnostic can name it); `None` is "committed, value not visible
/// here" (a parameter fed by a caller's literal).
///
/// Built over the WHOLE function before any `GEP` is judged, so a displacement constant
/// materialized in an earlier block — or, after any future scheduling change, a later one —
/// still counts. Missing one would be the fail-OPEN direction.
///
/// # wave-DZ: every integer SPELLING, not four of them
///
/// wave-DA matched `Ty::I64 | Ty::U64 | Ty::Isize | Ty::Usize`. All three producer sites emit
/// `Ty::I64` today, so the narrower table cost nothing — but the gate's claim is about the
/// SHAPE, and a `Const { ty: U32 }` respelling of the same offset walked straight past it
/// (again, demonstrated by a passing adversarial test at review time). A byte displacement is
/// a byte displacement in every integer width, so every integer `Const` enters the table.
///
/// STILL NOT MODELLED, stated rather than implied: a displacement that is COMPUTED
/// (`add %k, 8`), copied through a `Cast`, or loaded from memory is not in this table. Those
/// are not shapes any producer site emits — all three materialize the offset as one `Const`
/// immediately before the `GEP` — and following them is a dataflow analysis, not a table.
fn committed_displacements(func: &Function, literal_params: u64) -> HashMap<ValueId, Option<i128>> {
    let mut committed: HashMap<ValueId, Option<i128>> = HashMap::new();
    if let Some(entry) = func.block(func.entry) {
        for (position, (vid, _)) in entry.params.iter().enumerate() {
            // A parameter beyond bit 63 cannot be tracked in the mask, so it is treated as
            // committed unconditionally — the fail-closed reading of "unknown".
            if position >= 64 || literal_params & (1u64 << position) != 0 {
                committed.insert(*vid, None);
            }
        }
    }
    for node in func.blocks.iter().flat_map(|b| b.body.iter()) {
        if let Inst::Const { ty, value: Constant::Int(k) } = &node.inst {
            if ty.is_integer() {
                if let Some(&r) = node.results.first() {
                    committed.insert(r, Some(*k));
                }
            }
        }
    }
    committed
}

/// [`first_adt_interior_byte_arithmetic`] for one function, against a prepared displacement
/// table.
///
/// # wave-DZ: EVERY index position, not just the first
///
/// wave-DA read `indices.first()`. A flat-byte `GEP` carrying its literal in index position 1
/// was therefore admitted (the third shape the review demonstrated). The producer emits exactly
/// one index at all three sites, so this costs nothing today; it removes a recognizer limit
/// that a future multi-index spelling would turn into a hole.
fn function_adt_interior_byte_walk(
    func: &Function,
    committed: &HashMap<ValueId, Option<i128>>,
) -> Option<String> {
    for node in func.blocks.iter().flat_map(|b| b.body.iter()) {
        if let Inst::GEP { pointee_ty: Ty::I8 | Ty::U8, indices, inbounds: true, .. } = &node.inst {
            for (position, index) in indices.iter().enumerate() {
                let Some(k) = committed.get(index) else { continue };
                return Some(match k {
                    Some(k) => format!(
                        "`{}` emits `gep inbounds i8, +{k}` (index {position}) — a literal rustc \
                         byte offset into an ADT interior",
                        func.name
                    ),
                    None => format!(
                        "`{}` emits `gep inbounds i8` whose index {position} arrives as a \
                         call-site literal — a rustc byte offset into an ADT interior",
                        func.name
                    ),
                });
            }
        }
    }
    None
}

/// [`function_adt_interior_byte_walk`] against `func`'s OWN constants only — the single-function
/// spelling the scope control uses to prove an orphan really does carry the shape.
fn function_adt_interior_byte_arithmetic(func: &Function) -> Option<String> {
    function_adt_interior_byte_walk(func, &committed_displacements(func, 0))
}

/// True iff `func` contains an `Inst::Undef` anywhere (Trust B9-A: the per-closure-scoped
/// THIR tripwire — the seam must not over-skip every deferred body because ONE unrelated
/// body violates the invariant).
pub(crate) fn function_has_undef(func: &Function) -> bool {
    func.blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .any(|node| matches!(node.inst, Inst::Undef { .. }))
}

/// True iff `module` contains an `Inst::Undef` anywhere (the B9-B1 THIR-side tripwire).
fn module_has_undef(module: &Module) -> bool {
    module.functions.iter().any(function_has_undef)
}

/// Trust (B9-B1): classification of a module's `Inst::Undef` occurrences. The reference
/// interpreter executes `Inst::Undef` EAGERLY as `UndefinedBehavior` (a sound over-approximation
/// of the poison-seed reading), so an oracle that REACHES one traps on every input. But the
/// bridge's dominant Undef use is a DEAD SEED: an aggregate immediately and fully overwritten by
/// an InsertField chain before any observation — semantically inert. `DeadSeeds` = every Undef
/// in the module is such a proven-dead seed (substitutable); `Live` = at least one Undef could
/// be observed (fail-closed skip); `None` = no Undef at all.
pub(crate) enum UndefClass {
    None,
    DeadSeeds,
    Live,
}

pub(crate) fn classify_undefs(module: &Module) -> UndefClass {
    classify_undefs_traced(module).0
}

/// Trust (B3-1b): the traced twin — carries WHICH Undef broke the dead-seed
/// proof (function + type) so the live-havoc coverage note names the offender
/// instead of forcing a rebuild-and-instrument loop on every new class.
pub(crate) fn classify_undefs_traced(module: &Module) -> (UndefClass, Option<String>) {
    let mut any = false;
    for func in &module.functions {
        for blk in &func.blocks {
            for node in &blk.body {
                if let Inst::Undef { ty } = &node.inst {
                    any = true;
                    if !undef_is_dead_seed(module, func, blk, node, ty) {
                        return (
                            UndefClass::Live,
                            Some(format!("fn {} undef ty {}", func.name, ty)),
                        );
                    }
                }
            }
        }
    }
    (if any { UndefClass::DeadSeeds } else { UndefClass::None }, None)
}

/// The dead-seed proof (ALL conditions, else the caller classes the module `Live`):
/// the seed type is a tuple/struct/array aggregate with a spellable zero (`zero_const`); the
/// Undef's result is used EXACTLY ONCE in the whole function; that use is the `aggregate`
/// operand of an `InsertField` (tuple/struct) or the `array` operand of an `InsertElement`
/// with a resolvable constant index (array — see the slice-12 arm) in the SAME block (never
/// the inserted `value`); and following the single-use chain linearly, the inserts cover ALL
/// fields — each intermediate chain value again used exactly once, each field covered once —
/// BEFORE the chain value has any other use. The fully-built final value may then be used
/// freely (it is a complete, defined value). A `[T; 0]` Undef is a dead seed outright (the
/// substituted `Constant::Array([])` is the type's sole inhabitant — substitution is exact).
/// Uses are enumerated via `trust_ir::mem2reg::rewrite_inst` — the authoritative
/// match-on-every-variant operand walker (the opaque-param proof's technique) — so
/// call/branch/return/store positions and any future `Inst` variant are covered automatically.
fn undef_is_dead_seed(
    module: &Module,
    func: &Function,
    blk: &Block,
    node: &InstrNode,
    ty: &Ty,
) -> bool {
    // A declaration-shaped `Undef -> Store(Alloca)` is NOT a dead seed: a Load
    // may observe that slot before any real Store. Proving otherwise requires a
    // control-flow dominance analysis over every Load, which this local use
    // check deliberately does not attempt. The bridge now emits an uninitialized
    // Alloca for promoted non-argument locals, so an invalid early Load remains
    // UB; legacy/orphan modules carrying the old shape classify Live here and
    // are never rewritten to a deterministic zero.
    // Trust (vtable slice 12): the ARRAY seed arms. The oracle bridge seeds an array
    // literal/repeat with `Undef { ty: Array(tid, n) }`; after the differential-local
    // InsertField→InsertElement respell (`rewrite_array_insert_fields` — the pinned
    // interpreter's `eval_insert_field` has no Array arm, measured), the overwrite chain
    // is a single-use `InsertElement` chain with CONSTANT indexes. Two arms:
    //   * n == 0: the seed is the type's SOLE inhabitant (`Constant::Array([])`) — an
    //     Undef of `[T; 0]` carries no information at all, so substitution is exact, not
    //     a zero "choice"; no chain is required and every use position is fine (the
    //     Unit/PhantomData argument). Requires only that the elem zero spells (resolvable
    //     elem — fail-closed otherwise).
    //   * n > 0: the same single-use chain discipline as the tuple/struct InsertField
    //     walk below, with the field key replaced by an index that must RESOLVE to a
    //     defining `Const Int` in this function (in-bounds, not yet covered). An
    //     unresolvable/runtime index, an InsertField over the Array seed (a shape the
    //     respell should have rewritten), or any other user refuses — Live, fail-closed.
    if let Ty::Array(_, n) = ty {
        if zero_const(module, ty).is_none() {
            return false;
        }
        let arity = *n as usize;
        if arity == 0 {
            return true;
        }
        let mut cur = match node.results.as_slice() {
            &[r] => r,
            _ => return false,
        };
        // Value -> defining inst, for constant-index resolution (single-definition SSA).
        let mut defs: HashMap<ValueId, &Inst> = HashMap::new();
        for b in &func.blocks {
            for nd in &b.body {
                for r in &nd.results {
                    defs.insert(*r, &nd.inst);
                }
            }
        }
        let mut covered: std::collections::HashSet<usize> = std::collections::HashSet::new();
        while covered.len() < arity {
            let users = nodes_using(func, cur);
            let [user] = users.as_slice() else { return false };
            if !blk.body.iter().any(|n| std::ptr::eq(n, *user)) {
                return false;
            }
            match &user.inst {
                Inst::InsertElement { array, index, value, .. }
                    if *array == cur && *value != cur && *index != cur =>
                {
                    let idx = match defs.get(index) {
                        Some(Inst::Const { value: Constant::Int(i), .. }) => *i,
                        _ => return false,
                    };
                    let Ok(idx) = usize::try_from(idx) else { return false };
                    if idx >= arity || !covered.insert(idx) {
                        return false;
                    }
                    cur = match user.results.as_slice() {
                        &[r] => r,
                        _ => return false,
                    };
                }
                _ => return false,
            }
        }
        return true;
    }
    let arity = match ty {
        Ty::Tuple(elems) => elems.len(),
        Ty::Struct(id) => match module.struct_def(*id) {
            Some(sd) => sd.fields.len(),
            None => return false,
        },
        _ => return false,
    };
    if arity == 0 || zero_const(module, ty).is_none() {
        return false;
    }
    let mut cur = match node.results.as_slice() {
        &[r] => r,
        _ => return false,
    };
    let mut covered: std::collections::HashSet<u32> = std::collections::HashSet::new();
    while covered.len() < arity {
        let users = nodes_using(func, cur);
        let [user] = users.as_slice() else { return false };
        // The single user must be an InsertField in the SAME block consuming `cur` as the
        // AGGREGATE (never the stored value), covering a fresh in-bounds field.
        if !blk.body.iter().any(|n| std::ptr::eq(n, *user)) {
            return false;
        }
        match &user.inst {
            Inst::InsertField { aggregate, field, value, .. }
                if *aggregate == cur
                    && *value != cur
                    && (*field as usize) < arity
                    && !covered.contains(field) =>
            {
                covered.insert(*field);
                cur = match user.results.as_slice() {
                    &[r] => r,
                    _ => return false,
                };
            }
            _ => return false,
        }
    }
    true
}

/// Every node in `func` that uses `vid` in ANY operand position (sentinel-remap probe over
/// `rewrite_inst`). Node-granular: a node using `vid` twice counts once — the dead-seed proof
/// separately pins WHICH operand position the single user consumes.
fn nodes_using<'f>(func: &'f Function, vid: ValueId) -> Vec<&'f InstrNode> {
    let max_id = func.max_value_id();
    if max_id == u32::MAX {
        return Vec::new(); // no sentinel available -> zero users -> proof fails closed
    }
    let sentinel = ValueId::new(max_id + 1);
    let map: HashMap<ValueId, ValueId> = std::iter::once((vid, sentinel)).collect();
    let mut out = Vec::new();
    for blk in &func.blocks {
        for node in &blk.body {
            let mut probe = node.inst.clone();
            trust_ir::mem2reg::rewrite_inst(&mut probe, &map);
            if probe != node.inst {
                out.push(node);
            }
        }
    }
    out
}

/// A typed ZERO constant for a dead seed's aggregate type — `None` where no zero spelling
/// exists, which fails the dead-seed proof closed. The interpreter materializes
/// `(Ty::Tuple/Struct, Constant::Aggregate)` seeds natively (the producer's own wave-D
/// constant-seed path).
///
/// Trust (vtable slice 11): `Ty::Ptr` and `Ty::Unit` lanes now spell — the producer's own
/// wave-PS OVERWRITTEN-lane convention (`seed_overwritten_ty`, lib.rs), carried here with the
/// dead-seed proof itself as the witness. The producer's recorded decision is explicit that a
/// pointer zero is legal ONLY where the lane is provably overwritten; in this file that proof
/// is global: every `zero_const` consumer runs under `UndefClass::DeadSeeds`
/// (`substitute_dead_seeds` at `compare`'s Live arm, the const-param-column lane, and the
/// seam-bundle lane in crate_module.rs — all three gated on `classify_undefs`), and
/// `undef_is_dead_seed` accepts ONLY a Tuple/Struct-typed seed whose every top-level field is
/// overwritten by a single-use InsertField chain before any other use. A `Ptr`/`Unit` at any
/// depth therefore sits under an overwritten lane and can never be read — the exact wave-PS
/// argument ("a `Ty::Ptr` buried in a nested `Ty::Struct` of an overwritten field is as
/// unobservable as one at the top"). Both spellings are interpreter-native in the PINNED
/// trust-ir: `(Ty::Ptr, Constant::Int(0)) -> NullPtr` (interpret.rs, the trust-ir e1027ee
/// null-pointer arm; `shape_matches_ty` has admitted the pairing since the initial commit) and
/// `(Ty::Unit, Constant::PhantomData) -> Unit`. A TOP-LEVEL bare `Ptr`/`Unit` `Inst::Undef`
/// still classifies Live (the proof's arity match admits Tuple/Struct only), so the
/// `()`-family callable-identity posture (slice 9) is untouched.
///
/// Trust (vtable slice 12): `Ty::Array` now spells — `Constant::Array` of recursive elem
/// zeros, the interpreter-native pairing (`constant_to_value`'s `(Ty::Array,
/// Constant::Array)` arm; the producer's own `[T; 0]`/`emit_bytes_global` spelling). The
/// divergence trap that kept this arm out through slice 11 — the producer spells `[T; N>0]`
/// as `Ty::Tuple` while the oracle spells `Ty::Array`, and the (Tuple, Array) pair fell to
/// `tys_agree`'s raw-equality leaf, so unlocking a fully-covered array-lane seed would have
/// published a MANUFACTURED "signature divergence" (deriving-from, measured) — is answered
/// by the arm the pin demanded: `tys_agree` now holds the (Tuple, Array) pair as an Err
/// QUARANTINE (coverage-only), so an unlocked by-value-array body fail-closes at the
/// signature instead of minting a verdict. Pinned by
/// `array_lane_seed_substitutes_but_sig_quarantine_holds` (the rewritten slice-11 pin).
fn zero_const(module: &Module, ty: &Ty) -> Option<Constant> {
    match ty {
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        // Trust (v25 B1): the faithful scalars zero like their carriers
        // (char zero is '\0', a valid Unicode scalar).
        | Ty::Isize
        | Ty::Usize
        | Ty::Char => Some(Constant::Int(0)),
        Ty::F32 | Ty::F64 => Some(Constant::Float(0.0)),
        Ty::Bool => Some(Constant::Bool(false)),
        // Trust (vtable slice 11): the two OVERWRITTEN-lane spellings — see the doc above for
        // the witness argument. `Int(0)` at `Ty::Ptr` IS the null pointer (both trust-ir
        // authorities accept the pairing); `PhantomData` at `Ty::Unit` is the sole inhabitant.
        Ty::Ptr => Some(Constant::Int(0)),
        Ty::Unit => Some(Constant::PhantomData),
        Ty::Tuple(elems) => elems
            .iter()
            .map(|t| zero_const(module, t))
            .collect::<Option<Vec<_>>>()
            .map(Constant::Aggregate),
        Ty::Struct(id) => module
            .struct_def(*id)?
            .fields
            .iter()
            .map(|f| zero_const(module, &f.ty))
            .collect::<Option<Vec<_>>>()
            .map(Constant::Aggregate),
        // Trust (vtable slice 12): the Array zero — elem resolved through this module's own
        // type table, `Constant::Array` variant (NOT `Aggregate`: the VARIANT is part of the
        // interpreter's `(Ty::Array, Constant::Array)` pairing and of the slice-7 pairing
        // contract's bit-exact initializer comparison). `[T; 0]` spells as the empty array —
        // the type's SOLE inhabitant, which is what makes the arity-0 dead-seed admission in
        // `undef_is_dead_seed` exact rather than a zero "choice".
        Ty::Array(id, n) => {
            let elem = module.ty(*id)?;
            let z = zero_const(module, elem)?;
            Some(Constant::Array(vec![z; *n as usize]))
        }
        // Trust (B3-1b E5): a first-class enum zero-seeds as VARIANT 0 at its
        // EFFECTIVE discriminant (never the index) with recursively zero-seeded
        // payload lanes — the shape must satisfy the interpreter's
        // variant_by_discriminant + arity decode or dead-seed substitution
        // trades a coverage skip for a mid-interpretation type error.
        Ty::Enum(id) => {
            let def = module.enum_def(*id)?;
            let discs = def.effective_discriminants()?;
            let (disc, variant) = (discs.first()?, def.variants.first()?);
            let mut elems = vec![Constant::Int(*disc)];
            for fty in &variant.fields {
                elems.push(zero_const(module, fty)?);
            }
            Some(Constant::Aggregate(elems))
        }
        _ => None,
    }
}

/// Trust (B9-B1b): rewrite `ICmp { op: Eq, lhs, rhs }` where one operand is defined by a
/// `Const Bool(false)` node — the bridge's `expected=false` assert-condition shape — into the
/// producer's bool-not idiom `Select { ty: Bool, cond: <other>, then_val: <false>, else_val:
/// <true> }` (a fresh `Const Bool(true)` node is inserted immediately before). Semantically
/// identical (`x == false` ≡ `!x` ≡ `x ? false : true`).
///
/// Trust (#60, 2026-08-19): the justification this doc used to give — "the pinned
/// interpreter evaluates Select natively where its ICmp arm is int-only" — is FALSE and has
/// been since the interpreter grew a scalar-Bool arm: `eval_bool_icmp`
/// (`trust-ir/src/interpret.rs`, reached from the `Inst::ICmp` eval path), resolved through
/// this crate's own path dependency. The REAL reason this pass exists is producer spelling
/// divergence: this crate's lowering still emits the `Select` idiom for bool-not while
/// trust-ir-bridge emits `ICmp Eq(x, false)` (its `emit_unop`, since bffcc45c5a), and the
/// differential needs ONE spelling to compare. If the producers ever converge on one idiom,
/// DELETE this pass in the same commit — a normalizer that outlives its divergence hides the
/// next one. Applied to the differential's local oracle copy only.
pub(crate) fn rewrite_bool_not_icmp(module: &mut Module) {
    for func in &mut module.functions {
        // Function-unique fresh ids for the inserted `Const Bool(true)` nodes.
        let mut next_id = match func.max_value_id() {
            u32::MAX => continue, // id space exhausted: leave untouched (fail-closed skip later)
            m => m + 1,
        };
        // Pass 1: collect the false-const result ids.
        let mut false_ids: std::collections::HashSet<ValueId> = std::collections::HashSet::new();
        for blk in &func.blocks {
            for node in &blk.body {
                if let Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) } = &node.inst {
                    if let Some(&r) = node.results.first() {
                        false_ids.insert(r);
                    }
                }
            }
        }
        // Trust (B3-1b): no early-continue on empty false_ids — the UnOp::Not
        // rewrite below fires independently of the ICmp-Eq-false shape.
        // Pass 2: rewrite matching ICmp nodes, inserting a true-const right before each.
        for blk in &mut func.blocks {
            let mut i = 0;
            while i < blk.body.len() {
                let rewrite = match &blk.body[i].inst {
                    Inst::ICmp { op: trust_ir::ICmpOp::Eq, lhs, rhs, .. } => {
                        if false_ids.contains(rhs) && !false_ids.contains(lhs) {
                            Some((*lhs, *rhs))
                        } else if false_ids.contains(lhs) && !false_ids.contains(rhs) {
                            Some((*rhs, *lhs))
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some((cond, false_id)) = rewrite {
                    let true_id = ValueId::new(next_id);
                    next_id += 1;
                    blk.body.insert(
                        i,
                        trust_ir::InstrNode::new(Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(true),
                        })
                        .with_result(true_id),
                    );
                    blk.body[i + 1].inst =
                        Inst::Select { ty: Ty::Bool, cond, then_val: false_id, else_val: true_id };
                    i += 2;
                } else if matches!(
                    &blk.body[i].inst,
                    Inst::BinOp {
                        op: trust_ir::BinOp::And | trust_ir::BinOp::Or,
                        ty: Ty::Bool,
                        ..
                    }
                ) {
                    // Trust (B3-1b): the class's THIRD spelling — the bridge's
                    // range-assume lane (`lo <= disc && disc <= hi`) combines bool
                    // ICmp results with the integer-bitwise And/Or; the pinned
                    // interpreter's BinOp is int-only. Rewrite to the short-circuit
                    // Select equivalent (`a && b` = Select(a, b, false);
                    // `a || b` = Select(a, true, b)) — differential-local, as above.
                    let Inst::BinOp { op, lhs, rhs, .. } = &blk.body[i].inst else {
                        unreachable!()
                    };
                    let (cond, r) = (*lhs, *rhs);
                    let is_and = matches!(op, trust_ir::BinOp::And);
                    let aux_id = ValueId::new(next_id);
                    next_id += 1;
                    blk.body.insert(
                        i,
                        trust_ir::InstrNode::new(Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(!is_and),
                        })
                        .with_result(aux_id),
                    );
                    blk.body[i + 1].inst = if is_and {
                        Inst::Select { ty: Ty::Bool, cond, then_val: r, else_val: aux_id }
                    } else {
                        Inst::Select { ty: Ty::Bool, cond, then_val: aux_id, else_val: r }
                    };
                    i += 2;
                } else if let Inst::UnOp { op: trust_ir::UnOp::Not, ty: Ty::Bool, operand } =
                    &blk.body[i].inst
                {
                    // Trust (B3-1b): the B9-B1b class's SECOND spelling — the bridge
                    // lowers a bool negation (`!overflow_flag` in the checked-arith
                    // assert lane) as `UnOp::Not`, which trust-ir defines as integer-
                    // bitwise; the pinned interpreter's UnOp path is int-only, so a
                    // bool operand infra-errors ("expected integer value, got bool")
                    // on every sampled input. Rewrite into the producer's own
                    // interpreter-native bool-not idiom `Select(cond ? false : true)`
                    // — semantically identical, differential-local (this LOG-ONLY
                    // lane's oracle copy; bridge/production consumers untouched).
                    let cond = *operand;
                    let false_id = ValueId::new(next_id);
                    let true_id = ValueId::new(next_id + 1);
                    next_id += 2;
                    blk.body.insert(
                        i,
                        trust_ir::InstrNode::new(Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(false),
                        })
                        .with_result(false_id),
                    );
                    blk.body.insert(
                        i + 1,
                        trust_ir::InstrNode::new(Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(true),
                        })
                        .with_result(true_id),
                    );
                    blk.body[i + 2].inst =
                        Inst::Select { ty: Ty::Bool, cond, then_val: false_id, else_val: true_id };
                    i += 3;
                } else {
                    i += 1;
                }
            }
        }
    }
}

/// Trust (vtable slice 12): rewrite `InsertField { ty: Ty::Array(..), aggregate, field,
/// value }` — the bridge's ARRAY-LITERAL aggregate spelling (`Rvalue::Aggregate(Array)`
/// emits an InsertField chain over the `Undef [T x N]` seed, measured on
/// const-vecs-and-slices::y) — into the interpreter-native positional-write idiom the
/// bridge's own REPEAT lane already uses: a fresh `Const I64 field` node + `InsertElement
/// { ty, array, index, value }`. Semantically identical (a positional write into lane
/// `field`); required because the PINNED interpreter's `eval_insert_field` has arms for
/// Aggregate/Record/Closure value kinds ONLY — an `InterpretValueKind::Array` aggregate
/// (what a substituted `(Ty::Array, Constant::Array)` seed materializes as) falls to its
/// type-error arm, so a dead-seed-substituted array-literal chain would infra-error on
/// every sample. `eval_insert_element` handles the Array kind natively. Applied to this
/// differential's LOCAL oracle copy only (the `rewrite_bool_not_icmp` precedent, including
/// the fresh-const insertion idiom), in BOTH comparison paths BEFORE `classify_undefs` —
/// the Array dead-seed walk then needs to model only the InsertElement form, and an
/// InsertField-over-Array that somehow survives classifies Live (fail-closed; and even if
/// substituted it interprets as a typed oracle incapacity, never a trap — `is_trap`
/// excludes `TypeError`).
pub(crate) fn rewrite_array_insert_fields(module: &mut Module) {
    for func in &mut module.functions {
        let mut next_id = match func.max_value_id() {
            u32::MAX => continue, // id space exhausted: leave untouched (fail-closed later)
            m => m + 1,
        };
        for blk in &mut func.blocks {
            let mut i = 0;
            while i < blk.body.len() {
                let rewrite = match &blk.body[i].inst {
                    Inst::InsertField { ty: ty @ Ty::Array(..), aggregate, field, value } => {
                        Some((ty.clone(), *aggregate, *field, *value))
                    }
                    _ => None,
                };
                if let Some((ty, array, field, value)) = rewrite {
                    let idx_id = ValueId::new(next_id);
                    next_id += 1;
                    blk.body.insert(
                        i,
                        trust_ir::InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(field as i128),
                        })
                        .with_result(idx_id),
                    );
                    blk.body[i + 1].inst =
                        Inst::InsertElement { ty, array, index: idx_id, value };
                    i += 2;
                } else {
                    i += 1;
                }
            }
        }
    }
}

/// Substitute every (proven-dead, see `classify_undefs`) `Inst::Undef { ty }` with
/// `Inst::Const { ty, zero }` in a clone-by-move of the oracle. Two-phase (collect then apply)
/// so `struct_def` lookups never alias the mutation. Only called on `UndefClass::DeadSeeds`
/// modules, where every zero is spellable by construction.
pub(crate) fn substitute_dead_seeds(mut module: Module) -> Module {
    let mut subs: Vec<(usize, usize, usize, Constant)> = Vec::new();
    for (fi, func) in module.functions.iter().enumerate() {
        for (bi, blk) in func.blocks.iter().enumerate() {
            for (ni, node) in blk.body.iter().enumerate() {
                if let Inst::Undef { ty } = &node.inst {
                    if let Some(z) = zero_const(&module, ty) {
                        subs.push((fi, bi, ni, z));
                    }
                }
            }
        }
    }
    for (fi, bi, ni, z) in subs {
        let node = &mut module.functions[fi].blocks[bi].body[ni];
        if let Inst::Undef { ty } = &node.inst {
            node.inst = Inst::Const { ty: ty.clone(), value: z };
        }
    }
    module
}

/// Trust (vtable slice 6 — campaign chain item (0), the two-sided spelling ALIGNMENT):
/// respell the oracle's ONCE-STORED ESCAPING stack slot as a named initializer-bearing
/// immutable global, in this differential's LOCAL oracle copy only.
///
/// # Why this exists (the one-sided-observation finding, vtable slice 5)
///
/// The THIR producer spells a promoted borrow (`fn f() -> &'static u8 { &0 }`, `&K`, `&S`)
/// as an initializer-bearing module global + `Inst::GlobalAddr` (the wave-16
/// `__trust_promoted_{idx}` mint, lib.rs). The oracle is bridged from `mir_built`, which
/// PREDATES `PromoteTemps`: the same borrow arrives as `_2 = const k; _1 = &_2`, and
/// `trust-ir-bridge`'s `ensure_local_storage` (lower.rs) lowers it as an ESCAPING stack
/// slot — `Alloca` + a single `Store(k)` + `Inst::Borrow` of the slot pointer. The two
/// spellings are observationally equivalent (an immutable cell holding `k` whose stable
/// address escapes), but no PAIRED-global value model can ever fire while only one side
/// has a global at all. This rewrite retires exactly that asymmetry.
///
/// # The pattern, EXACT (totality — a partial match leaves the candidate untouched)
///
/// The bridge HOISTS slot storage: the extracted stream declares the `Alloca` at the top
/// of the entry block (measured: `const-address-of::A` is `%0 = alloca i32; %1 = const
/// i32 2; %2 = copy i32 %1; store %2 -> %0; %3 = borrow %0; %4 = copy ptr %3; ret %4`),
/// so no adjacency between the triple's members may be assumed. The gates are:
///
/// * `Alloca { ty, count: None }` with a single result `p`;
/// * the slot's ONLY store, anywhere: non-volatile `Store { ty, ptr: p, value: v }`
///   with `ty` equal to the alloca's (a second store — borrow-use-issue-46875's
///   `_1 = const 7` AFTER `_2 = &_1`, where an initializer-`5` global would be a WRONG
///   final memory — refuses);
/// * every OTHER use of `p` is a single-result shared `Borrow { ptr: p }` (≥ 1),
///   located in the STORE'S OWN BLOCK at a LATER position — positional order within one
///   block is execution order, which is what proves no alias to the slot exists before
///   the store runs (an alias read of the pre-store UNINIT slot would trap where the
///   always-initialized global does not). A `Load` (`read_local` after storage exists),
///   a `BorrowMut`, a `Copy` of `p` (the `&raw const` lane), a GEP, a call/branch/
///   return operand, or a cross-block borrow all refuse. Use detection is the
///   sentinel-remap probe (`private_nonescaping_slots`), so an operand position this
///   list never anticipated fails CLOSED;
/// * `v` const-folds to a data-only constant: defined by `Inst::Const` (identity-bearing
///   constants — `FnDef`/`SymbolAddr`/`Closure` — refused via
///   `constant_materializes_uncomparable_identity`), through `Inst::Copy` hops (the
///   operand-materialization copy above), or by an `InsertField` chain over such (the
///   bridge's aggregate build after `substitute_dead_seeds` replaced its dead `Undef`
///   seed — `Foo(const 3)` folds to `Aggregate([Int 3])`; run this AFTER the dead-seed
///   substitution). The chain nodes stay in place afterwards (pure, allocation-free).
///
/// # The rewrite
///
/// Append `Global { name: "__trust_promoted_{n}", ty, mutable: false, initializer:
/// Some(folded k), linkage: Internal }` — the THIR mint's exact shape — then replace the
/// `Alloca` ITSELF with `Inst::GlobalAddr { global }` keeping the SAME result id `p`,
/// and DELETE the `Store`. The `Borrow`s stay: `Borrow` of `p` is a pure pointer
/// pass-through in the interpreter, and a shared borrow of a global's stable address is
/// exactly what the source program means.
///
/// REPLACING THE ALLOCA IN PLACE is the load-bearing move, not style:
/// `InterpretPointer` raw-compares `{ allocation, offset }`, and allocation ids are
/// assigned in bump order per side (`global_pointer` allocates a global lazily at FIRST
/// TOUCH). Substituting the `GlobalAddr` at the alloca's own position makes the global's
/// first touch mint its allocation at EXACTLY the execution point the `Alloca` used to —
/// every allocation id the execution ever produces, on every path, in every
/// multi-candidate or call-bearing seam body, is unchanged BY CONSTRUCTION, with no gap
/// or ordering analysis at all. (The first draft deleted the alloca and rewrote the
/// borrows instead; that requires proving no allocation event sits between the deleted
/// alloca and its first borrow, which the hoisted-prologue shape makes false in
/// general.) Deleting the `Store` is allocation-neutral, and its write is exactly the
/// initializer the global materializes at first touch (same
/// `constant_to_value`/`encode_value` pair) — before the store's old position, which no
/// alias can observe because every alias derives from a borrow the order gate proved
/// later-than-store.
///
/// # What this slice does NOT do (recorded so the next reader does not infer it)
///
/// It admits nothing BY ITSELF. (Historical note: at slice-6 landing,
/// `first_unmodeled_observation`'s `Inst::GlobalAddr` arm was unconditional, so every
/// fired body stayed `clean-skip-unmodeled-observation`. The VALUE MODEL that consumes
/// the aligned spelling — name pairing + admission + the audited pass-through closure —
/// is chain item (1), SHIPPED as vtable slice 7: see `paired_admitted_promoted_globals`
/// and the admitted `GlobalAddr`/`Borrow` arms in the walk.)
///
/// # The pairing key, stated honestly
///
/// `__trust_promoted_{n}` counts fires in MODULE SCAN ORDER (functions in index order,
/// blocks in order, positions ascending). The THIR side numbers per BODY in PRODUCER
/// TRAVERSAL order, and the crate assembler renames crate-unique at splice. The names
/// coincide on every single-promoted per-body module — 16 of the 17 measured population
/// bodies — but nothing DOWNSTREAM may rely on that luck, for two MEASURED reasons
/// (sugar-ambiguity's `main`): order is only coincidentally shared (MIR statement order
/// vs THIR traversal order), and the COUNTS need not agree — this rewrite also fires on
/// once-stored borrowed locals the producer never promotes (`let ref pin: i32 = 0;`
/// mints an oracle-only `__trust_promoted_2`; the seam bundle likewise respells linked
/// CALLEES' slots). Chain item (1) must pair by name over the ≤1-distinct-global bound,
/// or by (position, initializer content), and must tolerate oracle-side extras
/// fail-closed. Recorded in TRUST_IR_V2.md's slice-6 section.
///
/// Mint collision (a module already carrying a `__trust_promoted_*` name — no oracle
/// module today) refuses the candidate, fail-closed.
pub(crate) fn respell_promoted_slots_as_globals(module: &mut Module) -> usize {
    // Fail closed outright if ANY existing global already uses the mint prefix: the
    // numbering below could otherwise collide, and a bundle that somehow carries one is
    // not a shape this rewrite has evidence about.
    if module.globals.iter().any(|g| g.name.starts_with("__trust_promoted_")) {
        return 0;
    }

    // Collect-then-apply, per house style (`substitute_dead_seeds`): no aliasing of the
    // module during detection.
    struct Plan {
        func: usize,
        alloca: (usize, usize),
        store: (usize, usize),
        ty: Ty,
        init: Constant,
    }
    let mut plans: Vec<Plan> = Vec::new();

    for (fi, func) in module.functions.iter().enumerate() {
        let max_id = func.max_value_id();
        if max_id == u32::MAX {
            continue; // no sentinel available -> fail closed (as private_nonescaping_slots)
        }
        let sentinel = ValueId::new(max_id + 1);

        // Value -> defining inst, for the stored-constant fold. Single-definition (SSA)
        // is a module invariant; a duplicate definition refuses the fold via overwrite
        // order never being consulted (the fold only reads Const/InsertField shapes).
        let mut defs: HashMap<ValueId, &Inst> = HashMap::new();
        for blk in &func.blocks {
            for node in &blk.body {
                for r in &node.results {
                    defs.insert(*r, &node.inst);
                }
            }
        }

        for (bi, blk) in func.blocks.iter().enumerate() {
            for (ni, node) in blk.body.iter().enumerate() {
                let Inst::Alloca { ty: slot_ty, count: None, .. } = &node.inst else { continue };
                let &[p] = node.results.as_slice() else { continue };
                // Log the DECLINE only (the lib.rs callee-link precedent): a refused Alloca
                // candidate is the rare, diagnosable event; the fire has its own event below.
                macro_rules! decline {
                    ($stage:expr) => {{
                        tracing::debug!(
                            func = %func.name,
                            block = bi,
                            pos = ni,
                            stage = $stage,
                            "trust-ir-lower: promoted-slot respell candidate declined"
                        );
                        continue;
                    }};
                }

                // Whole-function use audit via the sentinel-remap probe: every node
                // either ignores `p`, is THE single store into it, or is a
                // single-result shared borrow of `p`. Anything else refuses.
                let map: HashMap<ValueId, ValueId> =
                    std::iter::once((p, sentinel)).collect();
                let mut store: Option<(usize, usize, ValueId)> = None;
                let mut borrows: Vec<(usize, usize)> = Vec::new();
                let mut ok = true;
                'audit: for (ubi, ublk) in func.blocks.iter().enumerate() {
                    for (uni, unode) in ublk.body.iter().enumerate() {
                        let mut probe = unode.inst.clone();
                        trust_ir::mem2reg::rewrite_inst(&mut probe, &map);
                        if probe == unode.inst {
                            continue; // does not use p
                        }
                        match &unode.inst {
                            Inst::Store { ty, ptr, value, volatile: false, .. }
                                if *ptr == p
                                    && *value != p
                                    && ty == slot_ty
                                    && store.is_none() =>
                            {
                                store = Some((ubi, uni, *value));
                            }
                            Inst::Borrow { ptr } if *ptr == p && unode.results.len() == 1 => {
                                borrows.push((ubi, uni));
                            }
                            _ => {
                                ok = false; // second store, mutable/raw escape, load, ...
                                break 'audit;
                            }
                        }
                    }
                }
                if !ok {
                    decline!("non-borrow-use");
                }
                let Some((sbi, sni, stored)) = store else { decline!("no-single-store") };
                if borrows.is_empty() {
                    decline!("no-borrow");
                }
                // Execution order: every borrow strictly after the store, in ITS block.
                if !borrows.iter().all(|&(bbi, bni)| bbi == sbi && bni > sni) {
                    decline!("borrow-not-after-store");
                }

                let Some(init) = fold_stored_constant(&defs, stored, 64) else {
                    decline!("stored-value-not-constant");
                };
                plans.push(Plan {
                    func: fi,
                    alloca: (bi, ni),
                    store: (sbi, sni),
                    ty: slot_ty.clone(),
                    init,
                });
            }
        }
    }

    // Apply: in-place Alloca -> GlobalAddr swaps first (position-stable), then the
    // Store deletions, descending so recorded positions stay valid.
    let fired = plans.len();
    for (n, plan) in plans.iter().enumerate() {
        let name = format!("__trust_promoted_{n}");
        let global = trust_ir::value::GlobalId::new(module.globals.len() as u32);
        module.globals.push(trust_ir::Global {
            name: name.clone(),
            ty: plan.ty.clone(),
            mutable: false,
            initializer: Some(plan.init.clone()),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
        });
        let func = &mut module.functions[plan.func];
        let (bi, ni) = plan.alloca;
        let node = &mut func.blocks[bi].body[ni];
        node.inst = Inst::GlobalAddr { global };
        // Annotations described the Alloca this node no longer is.
        node.proofs.clear();
        tracing::debug!(
            func = %func.name,
            global = %name,
            ty = ?plan.ty,
            "trust-ir-lower: oracle once-stored escaping slot respelled as \
             initializer-bearing global (promoted-borrow spelling alignment)"
        );
    }
    let mut removals: Vec<(usize, usize, usize)> =
        plans.iter().map(|p| (p.func, p.store.0, p.store.1)).collect();
    removals.sort_unstable_by(|a, b| b.cmp(a));
    for (fi, bi, ni) in removals {
        module.functions[fi].blocks[bi].body.remove(ni);
    }
    fired
}

/// Trust (vtable slice 12): the THIR-SIDE twin of `respell_promoted_slots_as_globals` —
/// the producer's once-stored escaping ARRAY slot respelled as its own wave-16
/// initializer-bearing `__trust_promoted_*` global, on a CLONE (`Some(respelled)` iff at
/// least one candidate fired; the shipped `Lowered` is NEVER touched — flip, splice, and
/// every verifier lane read the original).
///
/// # Why a rewrite of the SIDE UNDER TEST is admissible here (stated, not assumed)
///
/// The slice-6 oracle respell aligned the trusted side's spelling; rewriting the tested
/// side is more delicate, because a careless rewrite could HIDE a producer defect behind
/// a corrected shape. This one cannot, for three reasons:
/// * the initializer is the fold of the ACTUAL stored chain (`fold_stored_constant`) — a
///   wrong stored value becomes a wrong initializer, which the slice-7 pairing's
///   BIT-EXACT content conjunct then refuses against the oracle's independently-folded
///   twin (the mismatch HOLDS the body; it can never agree);
/// * the use audit is total (sentinel-remap; single Store, every other use a shared
///   `Borrow` or a Slice/Str `PtrFromParts` DATA operand, all in the store's block at
///   LATER positions) — a shape outside the measured `lower_inline_array_to_slice`
///   pattern leaves the module untouched;
/// * the swap is the slice-6 in-place id-preserving move (`Alloca` → `GlobalAddr` at the
///   same position, `Store` deleted), so allocation order — and therefore every raw
///   `InterpretPointer` the execution mints — is unchanged by construction.
/// The rewrite changes WHERE the bytes live (stack slot → named immutable global), which
/// is exactly the spelling difference between the producer's slice lane
/// (`lower_inline_array_to_slice`: Alloca + Store + `PtrFromParts`, measured on
/// const-vecs-and-slices::y) and its own wave-16 promoted lane (`&[1,2,3,4]` at thin
/// `&[isize; 4]` mints the global directly, measured on const-vecs-and-slices::z). It
/// asserts nothing about the VALUE — the pairing and the interpretation do.
///
/// # Scope (blast-radius control, deliberately narrower than the oracle twin)
///
/// Slot type must be `Ty::Array(..)` or a HOMOGENEOUS non-empty `Ty::Tuple` — the
/// producer's two array spellings. Scalar snapshot slots (the wave-CB `&K` lane, the
/// issue-67710/dest_prop escaping-alloca holds) and genuine mixed tuples are excluded:
/// their oracle twins have no pairable initializer-bearing global today, so firing there
/// could only churn note text. The PtrFromParts use-arm accepts the DATA position of a
/// `FatPtr(Slice|Str)` assembly only — the metadata position, `TraitObject` fat kinds,
/// `Copy`/`Load`/GEP/call/store positions, and anything unanticipated refuse the
/// candidate (fail-closed, `private_nonescaping_slots`' idiom).
pub(crate) fn respell_thir_array_slots_as_globals(module: &Module) -> Option<Module> {
    if module.globals.iter().any(|g| g.name.starts_with("__trust_promoted_")) {
        return None; // mint collision: numbering could clash — fail closed outright
    }
    let homogeneous_array_slot = |ty: &Ty| match ty {
        Ty::Array(..) => true,
        Ty::Tuple(elems) => !elems.is_empty() && elems.iter().all(|e| e == &elems[0]),
        _ => false,
    };

    struct Plan {
        func: usize,
        alloca: (usize, usize),
        store: (usize, usize),
        ty: Ty,
        init: Constant,
    }
    let mut plans: Vec<Plan> = Vec::new();

    for (fi, func) in module.functions.iter().enumerate() {
        let max_id = func.max_value_id();
        if max_id == u32::MAX {
            continue; // no sentinel available -> fail closed
        }
        let sentinel = ValueId::new(max_id + 1);
        let mut defs: HashMap<ValueId, &Inst> = HashMap::new();
        for blk in &func.blocks {
            for node in &blk.body {
                for r in &node.results {
                    defs.insert(*r, &node.inst);
                }
            }
        }
        for (bi, blk) in func.blocks.iter().enumerate() {
            for (ni, node) in blk.body.iter().enumerate() {
                let Inst::Alloca { ty: slot_ty, count: None, .. } = &node.inst else { continue };
                if !homogeneous_array_slot(slot_ty) {
                    continue;
                }
                let &[p] = node.results.as_slice() else { continue };
                macro_rules! decline {
                    ($stage:expr) => {{
                        tracing::debug!(
                            func = %func.name,
                            block = bi,
                            pos = ni,
                            stage = $stage,
                            "trust-ir-lower: THIR promoted-slot respell candidate declined"
                        );
                        continue;
                    }};
                }
                let map: HashMap<ValueId, ValueId> = std::iter::once((p, sentinel)).collect();
                let mut store: Option<(usize, usize, ValueId)> = None;
                let mut escapes: Vec<(usize, usize)> = Vec::new();
                let mut ok = true;
                'audit: for (ubi, ublk) in func.blocks.iter().enumerate() {
                    for (uni, unode) in ublk.body.iter().enumerate() {
                        let mut probe = unode.inst.clone();
                        trust_ir::mem2reg::rewrite_inst(&mut probe, &map);
                        if probe == unode.inst {
                            continue; // does not use p
                        }
                        match &unode.inst {
                            Inst::Store { ty, ptr, value, volatile: false, .. }
                                if *ptr == p
                                    && *value != p
                                    && ty == slot_ty
                                    && store.is_none() =>
                            {
                                store = Some((ubi, uni, *value));
                            }
                            Inst::Borrow { ptr } if *ptr == p && unode.results.len() == 1 => {
                                escapes.push((ubi, uni));
                            }
                            Inst::PtrFromParts { ptr_ty, data, metadata, .. }
                                if *data == p
                                    && *metadata != p
                                    && unode.results.len() == 1
                                    && matches!(
                                        ptr_ty,
                                        Ty::FatPtr(
                                            trust_ir::FatPtrKind::Slice(_)
                                                | trust_ir::FatPtrKind::Str
                                        )
                                    ) =>
                            {
                                escapes.push((ubi, uni));
                            }
                            _ => {
                                ok = false; // second store, metadata escape, load, copy, ...
                                break 'audit;
                            }
                        }
                    }
                }
                if !ok {
                    decline!("non-modeled-use");
                }
                let Some((sbi, sni, stored)) = store else { decline!("no-single-store") };
                if escapes.is_empty() {
                    decline!("no-escape-use");
                }
                // Execution order: every escape strictly after the store, in ITS block —
                // the slice-6 proof that no alias can read the pre-store uninit slot.
                if !escapes.iter().all(|&(ebi, eni)| ebi == sbi && eni > sni) {
                    decline!("use-not-after-store");
                }
                let Some(init) = fold_stored_constant(&defs, stored, 64) else {
                    decline!("stored-value-not-constant");
                };
                plans.push(Plan {
                    func: fi,
                    alloca: (bi, ni),
                    store: (sbi, sni),
                    ty: slot_ty.clone(),
                    init,
                });
            }
        }
    }
    if plans.is_empty() {
        return None;
    }

    let mut out = module.clone();
    for (n, plan) in plans.iter().enumerate() {
        let name = format!("__trust_promoted_{n}");
        let global = trust_ir::value::GlobalId::new(out.globals.len() as u32);
        out.globals.push(trust_ir::Global {
            name: name.clone(),
            ty: plan.ty.clone(),
            mutable: false,
            initializer: Some(plan.init.clone()),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
        });
        let func = &mut out.functions[plan.func];
        let (bi, ni) = plan.alloca;
        let node = &mut func.blocks[bi].body[ni];
        node.inst = Inst::GlobalAddr { global };
        node.proofs.clear();
        tracing::debug!(
            func = %func.name,
            global = %name,
            ty = ?plan.ty,
            "trust-ir-lower: THIR once-stored escaping array slot respelled as \
             initializer-bearing global (slice-lane spelling alignment)"
        );
    }
    let mut removals: Vec<(usize, usize, usize)> =
        plans.iter().map(|p| (p.func, p.store.0, p.store.1)).collect();
    removals.sort_unstable_by(|a, b| b.cmp(a));
    for (fi, bi, ni) in removals {
        out.functions[fi].blocks[bi].body.remove(ni);
    }
    Some(out)
}

/// Fold the stored value's defining chain to a data-only `Constant`, or refuse.
/// `Const` of a non-identity constant is a leaf; `Copy` is the bridge's
/// operand-materialization hop and folds through; `InsertField` over a foldable
/// aggregate with a foldable element folds structurally (the bridge's
/// post-`substitute_dead_seeds` aggregate build). Everything else — params, `BinOp`
/// results, loads, symbolic carriers — refuses, which keeps runtime-valued slots
/// (locals-in-const-fn's `bar(mut i)`) out by construction. A param has no defining
/// node at all, so it refuses through the `defs` lookup.
fn fold_stored_constant(
    defs: &HashMap<ValueId, &Inst>,
    v: ValueId,
    depth: u32,
) -> Option<Constant> {
    if depth == 0 {
        return None;
    }
    match defs.get(&v)? {
        Inst::Const { value, .. } if !constant_materializes_uncomparable_identity(value) => {
            Some(value.clone())
        }
        Inst::Copy { operand, .. } => fold_stored_constant(defs, *operand, depth - 1),
        Inst::InsertField { aggregate, field, value, .. } => {
            let mut agg = fold_stored_constant(defs, *aggregate, depth - 1)?;
            let elem = fold_stored_constant(defs, *value, depth - 1)?;
            let Constant::Aggregate(elems) = &mut agg else { return None };
            let slot = elems.get_mut(*field as usize)?;
            *slot = elem;
            Some(agg)
        }
        // Trust (vtable slice 12): the ARRAY positional write — the repeat lane's native
        // spelling and the `rewrite_array_insert_fields` output. The index must itself
        // resolve to a defining `Const Int` (the bridge/rewrite always emit one; a runtime
        // index refuses the fold), in-bounds of the folded `Constant::Array`. The variant
        // gate is exact: an InsertElement over anything but an Array constant refuses —
        // the seed's `zero_const` spelling IS `Constant::Array`, so a fold that arrives
        // here with another variant is not the proven shape.
        Inst::InsertElement { array, index, value, .. } => {
            let mut agg = fold_stored_constant(defs, *array, depth - 1)?;
            let elem = fold_stored_constant(defs, *value, depth - 1)?;
            let idx = match defs.get(index)? {
                Inst::Const { value: Constant::Int(i), .. } => usize::try_from(*i).ok()?,
                _ => return None,
            };
            let Constant::Array(elems) = &mut agg else { return None };
            let slot = elems.get_mut(idx)?;
            *slot = elem;
            Some(agg)
        }
        _ => None,
    }
}

/// A genuine runtime trap the THIR side is obligated to reproduce (defined misbehavior).
fn is_trap(c: InterpretErrorCode) -> bool {
    matches!(c, InterpretErrorCode::Panic | InterpretErrorCode::UndefinedBehavior)
}

/// `(Err, Err)` verdict: BOTH sides errored, but with *different* codes (the
/// same-trap agreement was already handled). This returns `true` exactly when the
/// THIR side's code is a genuine lowering defect while the oracle's code is NOT —
/// i.e. the oracle merely hit an infra limit (e.g. `OutOfFuel`, `Unsupported*`).
/// Such a pair is a real THIR defect masked by the oracle's incidental incapacity,
/// and must be reported rather than swept into the `NotRun` coverage-only skip.
fn errerr_thir_defect_divergence(thir: InterpretErrorCode, oracle: InterpretErrorCode) -> bool {
    is_thir_defect(thir) && !is_thir_defect(oracle)
}

/// THIR-side error codes that indicate a real lowering defect (vs an infra/limitation code such as
/// `OutOfFuel`, `Unsupported*`, `MissingFunction`, `InvalidFunctionPointer`).
fn is_thir_defect(c: InterpretErrorCode) -> bool {
    matches!(
        c,
        InterpretErrorCode::TypeError
            | InterpretErrorCode::SignatureMismatch
            | InterpretErrorCode::MalformedInstruction
            | InterpretErrorCode::MissingBlock
            | InterpretErrorCode::MissingValue
            | InterpretErrorCode::Panic
            | InterpretErrorCode::UndefinedBehavior
    )
}

/// Is `t` a scalar the interpreter can construct an argument for and execute over?
/// Floats are included (wave 3): an f32/f64 argument is a `FloatBits` value both sides
/// type-check and evaluate natively (`eval_float_binop`/`eval_fcmp` run in the operand width),
/// and the return comparison is BIT equality on the IEEE pattern — deterministic on both sides
/// because the same interpreter executes both modules (NaN payloads included). f16 stays out
/// (interpreter-refused: "requires an explicit half-precision codec").
fn is_interpretable_scalar(t: &Ty) -> bool {
    matches!(
        t,
        Ty::Bool
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::F32
            | Ty::F64
            // Trust (v25 B1): first-class pointer-width ints (64-bit at the pinned
            // target, via `int_shape`) and Char (32-bit unsigned carrier whose
            // constants are Int leaves; sampled validity-aware — see `sample_values`).
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
    )
}

/// Width (bits) + signedness for an integer `Ty`. `None` for non-integers.
fn int_shape(t: &Ty) -> Option<(u32, bool)> {
    Some(match t {
        Ty::I8 => (8, true),
        Ty::I16 => (16, true),
        Ty::I32 => (32, true),
        Ty::I64 => (64, true),
        Ty::I128 => (128, true),
        Ty::U8 => (8, false),
        Ty::U16 => (16, false),
        Ty::U32 => (32, false),
        Ty::U64 => (64, false),
        Ty::U128 => (128, false),
        // Trust (v25 B1): first-class pointer-width integers execute at 64 bits —
        // the pinned 64-bit target, the same convention as trust-ir interpret's
        // own `int_shape` (so `InterpretValue::int` masks samples identically).
        Ty::Isize => (64, true),
        Ty::Usize => (64, false),
        // Trust (v25 B1): Char is deliberately NOT here. It is a 32-bit unsigned
        // CARRIER, not an integer type (no arithmetic), and the raw u32 boundary
        // samples this table drives (`sample_values`: 0xFFFFFFFF, 0x7FFFFFFF) are
        // INVALID Unicode scalars the trust-ir validator/interpreter rejects.
        // `sample_values` gives Char its own validity-aware early arm instead.
        _ => return None,
    })
}

/// Boundary + mid sample set for one scalar parameter type, as raw `i128`s (masked to width by
/// `InterpretValue::int`). Bool is sampled as {0, 1}. Duplicates removed so tiny widths don't blow up.
///
/// FLOATS are sampled as their IEEE-754 BIT PATTERNS carried in the same `i128` lane (the
/// cartesian plumbing is bit-agnostic; `build_arg` reassembles a `FloatBits` value). The set
/// covers the semantic boundary classes: both zero signs (`0.0`/`-0.0` — equal under `FCmp`,
/// distinct bitwise through arithmetic), an exact small value and a negative fractional one,
/// the largest finite (overflows to infinity under `FAdd`), the smallest positive normal,
/// `+inf`, and a quiet `NaN` (the FCmp ordered/unordered split and NaN propagation).
/// Trust (B3/E6): abstract, side-portable enum samples — `(variant index, payload raws)`,
/// realized PER SIDE against that module's OWN EnumDef. Only EnumDef-VALID variant values
/// are ever described (the interpreter does NOT validate entry aggregates — pinned by the
/// trust-ir 0c probe — so validity is THIS function's obligation). Capped at
/// `MAX_ENUM_SAMPLES` with VARIANT-COVERAGE-FIRST ordering: one sample per variant (the
/// first boundary value per payload field) before any variant's payload product deepens,
/// so truncation never drops a variant. Enums with zero or more than `MAX_ENUM_SAMPLES`
/// variants fail closed instead of silently omitting a variant.
///
/// **THE CONSTANT DOES TWO JOBS, AND ONE INVARIANT TIES THEM.** It is the ADMISSION gate
/// (`variants.len() > MAX_ENUM_SAMPLES` fails closed, here and at the param-class gate) and
/// it is the SAMPLE BUDGET (pass 2 stops at it). Pass 1 spends one sample per variant, so
/// "truncation never drops a variant" is exactly `budget >= variant count` — which one
/// constant guarantees for free. Do not split it without carrying that inequality.
///
/// **8 -> 12, 2026-08-17, MEASURED rather than chosen.** The value was 8, matching the widest
/// scalar pool (`sample_values` yields at most 8 values, for the floats) so an enum column could
/// never widen the cartesian product beyond what a scalar column already could. Measured over the
/// producer's own `clean_kernel.trust-ir.txt` (8,723 bodies, 209 enum defs, 52 distinct enums in
/// by-value param position), that symmetry was costing exactly one body and buying nothing:
///
///   * ONE enum is refused by the variant-count gate ALONE — `mode::SourceSystem`, 12 payload-free
///     variants, whose only user is `mode::CleanMode::from_source_system`, an UNBACKED codegen
///     flip. Every other >8-variant param enum (`ExprKind` 25, `ProofCert` 25, `ProofCertWire` 25,
///     `EnvError` 24, `TypeError` 23, `InductiveError` 16) is ALSO refused for a payload reason —
///     struct/enum/fat-pointer payload fields — so no value of this constant reaches them.
///   * The "deepens every enum already backed" worry is 2 bodies. 18 of the 20 admitted enums
///     already exercise their COMPLETE described sample space at 8. The two that truncate are
///     `CofibAtom` (space 10; 8 -> 10, i.e. now EXHAUSTIVE) in `CofibAtom::{var,value}`, and
///     `DecompressError` (space 29; 8 -> 12) whose one user is `not-run` for an unrelated reason
///     (a direct call) and therefore costs zero samples.
///   * Worst case per body rises 8^4 -> 12^4 against `MAX_PARAMS`. Measured, the largest sample
///     count anywhere in clean-kernel is 125 and no body carries more than two admitted enum
///     columns, the widest of which is 8 — so the ceiling stays theoretical.
const MAX_ENUM_SAMPLES: usize = 12;
fn enum_abstract_samples(def: &trust_ir::EnumDef) -> Option<Vec<(usize, Vec<i128>)>> {
    if def.variants.is_empty() || def.variants.len() > MAX_ENUM_SAMPLES {
        return None;
    }
    def.canonical_tag_repr()?;
    def.effective_discriminants()?;
    let pools: Vec<Vec<Vec<i128>>> = def
        .variants
        .iter()
        .map(|v| {
            v.fields
                .iter()
                .map(|fty| {
                    if is_interpretable_scalar(fty) {
                        Some(sample_values(fty))
                    } else if matches!(fty, Ty::Unit) {
                        // Trust (B3-2c): one dummy raw keeps the column arithmetic
                        // exact; the realization ignores it (Unit is value-less).
                        Some(vec![0])
                    } else {
                        None
                    }
                })
                .collect::<Option<Vec<_>>>()
        })
        .collect::<Option<Vec<_>>>()?;
    let mut out: Vec<(usize, Vec<i128>)> = Vec::new();
    // Pass 1: variant coverage — first value of every payload pool.
    for (v, vp) in pools.iter().enumerate() {
        if out.len() >= MAX_ENUM_SAMPLES {
            break;
        }
        let payload: Option<Vec<i128>> = vp.iter().map(|pool| pool.first().copied()).collect();
        out.push((v, payload?));
    }
    // Pass 2: round-robin payload deepening (deterministic; last field fastest — the
    // CartesianProduct orientation), one extra sample per variant per round.
    let mut depth = 1usize;
    'grow: loop {
        let mut grew = false;
        for (v, vp) in pools.iter().enumerate() {
            if out.len() >= MAX_ENUM_SAMPLES {
                break 'grow;
            }
            if vp.is_empty() {
                continue;
            }
            // Enumerate the payload cross-product in order; take element `depth`.
            // Only `depth < MAX_ENUM_SAMPLES` is observable. Saturation therefore
            // preserves the bounded recipe exactly while avoiding a host `usize`
            // overflow for wide scalar-payload variants.
            let total = vp.iter().fold(1usize, |n, p| n.saturating_mul(p.len()));
            if depth >= total {
                continue;
            }
            let mut idx = depth;
            let mut payload = Vec::with_capacity(vp.len());
            for pool in vp.iter().rev() {
                payload.push(pool[idx % pool.len()]);
                idx /= pool.len();
            }
            payload.reverse();
            out.push((v, payload));
            grew = true;
        }
        if !grew {
            break;
        }
        depth += 1;
    }
    if out.is_empty() { None } else { Some(out) }
}

/// Trust (aggregate param lane): the depth-first list of SCALAR LEAF types of an eligible
/// by-value struct, or `None` if the struct is not eligible.
///
/// Eligible means, exactly (fail CLOSED on everything else — a shape this cannot marshal
/// EXACTLY must stay `not-run`, because a wrong marshalling is a wrong verdict):
///   * the `StructId` resolves in `module`'s own table;
///   * the struct has at least one field (a field-less struct carries no observable value, so
///     admitting it would buy a verdict over an empty input space);
///   * every field is either an `is_interpretable_scalar` leaf or another eligible struct,
///     recursively, within `MAX_STRUCT_DEPTH`;
///   * the total leaf count is at most `MAX_STRUCT_LEAVES`.
///
/// Deliberately NOT eligible, each because the exact value model is not this lane's to invent:
///   * `Ty::Unit` fields — a producer `Ty::Unit` at a struct-field position is ALSO how the
///     union lane spells a `union` member (`struct_field_tys`), and the oracle spells the same
///     member as its real field type. Those bodies are already `not-run` (the union lane forces
///     `contains_call`), so this arm never sees one — but the refusal is written down rather
///     than relied upon, because a genuine ZST field and a union placeholder are the same
///     `Ty::Unit` here and only one of them is value-less.
///   * `Ty::Enum` fields — the tag/payload encoding is the `Enum` arm's discipline and carries
///     its own discriminant and tag-repr obligations; nesting it inside the struct recipe would
///     duplicate them at a second site.
///   * arrays, tuples, pointers, fat pointers, closures, records — no exact positional
///     marshalling is established for them here.
fn struct_leaf_tys(module: &Module, sid: trust_ir::StructId, depth: u32) -> Option<Vec<Ty>> {
    if depth == 0 {
        return None;
    }
    let def = module.struct_def(sid)?;
    if def.fields.is_empty() {
        return None;
    }
    let mut leaves = Vec::new();
    for field in &def.fields {
        match &field.ty {
            t if is_interpretable_scalar(t) => leaves.push(t.clone()),
            Ty::Struct(inner) => leaves.extend(struct_leaf_tys(module, *inner, depth - 1)?),
            _ => return None,
        }
        if leaves.len() > MAX_STRUCT_LEAVES {
            return None;
        }
    }
    if leaves.is_empty() || leaves.len() > MAX_STRUCT_LEAVES { None } else { Some(leaves) }
}

/// Trust (aggregate param lane): do the two sides' `StructDef`s agree on FIELD NAMES, pairwise
/// and recursively? This is the identity pin `tys_agree`'s struct arm deliberately does not
/// carry (it ignores names so the oracle may name closure envs differently), and it is what
/// makes a POSITIONAL marshalling sound: two same-typed sibling fields cannot be transposed
/// between the producer and the oracle without this disagreeing.
///
/// Both sides read the name from the same rustc `FieldDef` in source-declaration index order,
/// so agreement is the expected case and disagreement is a real spelling split — which returns
/// `false` and leaves the body on its existing `not-run`, never on a manufactured verdict.
fn struct_field_names_agree(
    am: &Module,
    bm: &Module,
    a: trust_ir::StructId,
    b: trust_ir::StructId,
    depth: u32,
) -> bool {
    if depth == 0 {
        return false;
    }
    let (Some(da), Some(db)) = (am.struct_def(a), bm.struct_def(b)) else {
        return false;
    };
    if da.fields.len() != db.fields.len() {
        return false;
    }
    da.fields.iter().zip(&db.fields).all(|(fa, fb)| {
        fa.name == fb.name
            && match (&fa.ty, &fb.ty) {
                (Ty::Struct(x), Ty::Struct(y)) => {
                    struct_field_names_agree(am, bm, *x, *y, depth - 1)
                }
                (Ty::Struct(_), _) | (_, Ty::Struct(_)) => false,
                _ => true,
            }
    })
}

/// Trust (aggregate param lane): the TWO-SIDED admission gate for a by-value struct param.
///
/// Every conjunct is an ADMISSION condition, never a comparison: failing any one of them leaves
/// the parameter on the byte-identical non-scalar refusal it has today (a `not-run`), so this
/// predicate can only ever produce MORE sampled verdicts, never a laxer comparison.
fn struct_param_admissible(am: &Module, bm: &Module, a: &Ty, b: &Ty) -> bool {
    let (Ty::Struct(sa), Ty::Struct(sb)) = (a, b) else {
        return false;
    };
    // (i) both sides marshal EXACTLY, to the same leaf sequence.
    let (Some(la), Some(lb)) =
        (struct_leaf_tys(am, *sa, MAX_STRUCT_DEPTH), struct_leaf_tys(bm, *sb, MAX_STRUCT_DEPTH))
    else {
        return false;
    };
    if la != lb {
        return false;
    }
    // (ii) field identity, not merely field shape.
    if !struct_field_names_agree(am, bm, *sa, *sb, MAX_STRUCT_DEPTH) {
        return false;
    }
    // (iii) the standard structural agreement the rest of the differential runs on. Checked
    //       HERE rather than left to step (5) because a struct param that reaches step (5)
    //       for the first time would publish a spelling split as a DIVERGENCE.
    matches!(tys_agree(am, bm, a, b, TY_CMP_DEPTH), Ok(true))
}

/// Trust (aggregate param lane): abstract, side-portable samples for one by-value struct param —
/// each sample is the FLAT depth-first list of raws for the struct's scalar leaves, realized per
/// side at the args site against that module's own `StructDef`.
///
/// THE LEAF ROTATION, and why it is not a plain diagonal. Sample `k` gives leaf `i` the value
/// `pool_i[(k + i) % pool_i.len()]`. Rotating by the leaf INDEX is what keeps sibling leaves at
/// DIFFERENT pool positions, and `sample_values` is sorted and deduplicated, so same-typed
/// siblings therefore hold pairwise-DISTINCT values in every sample. A plain diagonal
/// (`pool_i[k]`) would hand `MemoryRegion { AllocationId(u64), usize, usize }` the same number in
/// all three leaves, and `offset()` versus `len()` — two functions that differ only in which
/// field they read — would agree VACUOUSLY. The rotation is what makes the sample able to fail.
///
/// Coverage: `k` runs over the widest leaf pool (capped at `MAX_STRUCT_SAMPLES`), so every leaf
/// sees the boundary values `sample_values` mints for its own type, modulo its pool length.
fn struct_abstract_samples(module: &Module, sid: trust_ir::StructId) -> Option<Vec<Vec<i128>>> {
    let leaves = struct_leaf_tys(module, sid, MAX_STRUCT_DEPTH)?;
    let pools: Vec<Vec<i128>> = leaves.iter().map(|t| sample_values(t)).collect();
    if pools.iter().any(Vec::is_empty) {
        return None;
    }
    let widest = pools.iter().map(Vec::len).max()?;
    let count = widest.min(MAX_STRUCT_SAMPLES);
    let mut out = Vec::with_capacity(count);
    for k in 0..count {
        out.push(
            pools
                .iter()
                .enumerate()
                .map(|(i, pool)| pool[(k + i) % pool.len()])
                .collect::<Vec<i128>>(),
        );
    }
    if out.is_empty() { None } else { Some(out) }
}

/// Trust (aggregate param lane): realize one abstract struct sample against THIS module's own
/// `StructDef`, consuming `leaves` depth-first through `cursor`.
///
/// The value is a POSITIONAL `InterpretValueKind::Aggregate` with exactly one element per
/// declared field, in declaration order — the shape `eval_extract_field` indexes (`values.get(field)`)
/// and `eval_insert_field` rebuilds. trust-ir's aggregate value model carries NO padding and no
/// offsets (`size`/`align`/`FieldDef::offset` are layout METADATA, never elements), so there is
/// no padding lane to fabricate; `repr` likewise changes bytes, not the field list, so a
/// `repr(C)`/`repr(transparent)`/`repr(packed)` struct marshals identically here.
fn realize_struct_arg(
    module: &Module,
    sid: trust_ir::StructId,
    leaves: &[i128],
    cursor: &mut usize,
    depth: u32,
) -> Result<InterpretValue, String> {
    if depth == 0 {
        return Err("struct nesting exceeds marshalling depth".to_string());
    }
    let def = module
        .struct_def(sid)
        .ok_or_else(|| format!("struct id {} unresolvable at args site", sid.index()))?;
    let mut elems = Vec::with_capacity(def.fields.len());
    for field in &def.fields {
        match &field.ty {
            Ty::Struct(inner) => {
                elems.push(realize_struct_arg(module, *inner, leaves, cursor, depth - 1)?);
            }
            t if is_interpretable_scalar(t) => {
                let raw = *leaves.get(*cursor).ok_or("struct sample leaf missing")?;
                *cursor += 1;
                elems.push(build_arg(t, raw)?);
            }
            other => return Err(format!("no struct marshalling for field type {other}")),
        }
    }
    Ok(InterpretValue { ty: Ty::Struct(sid), kind: InterpretValueKind::Aggregate(elems) })
}

/// Decode enum columns for diagnostics without making note rendering an
/// admission condition. Construction has already succeeded before this helper
/// runs; any unexpected recipe drift simply omits the suffix.
fn decoded_enum_sample_suffix(
    module: &Module,
    sig: &trust_ir::FuncTy,
    classes: &[ParamClass],
    enum_samples: &[Option<Vec<(usize, Vec<i128>)>>],
    tuple: &[i128],
) -> String {
    let decode = || -> Option<String> {
        let mut column = 0usize;
        let mut parts = Vec::new();
        for (param, class) in classes.iter().enumerate() {
            match class {
                ParamClass::Scalar => column += 1,
                ParamClass::Opaque => {}
                // Trust (aggregate param lane): a struct column consumes its slot like any
                // other. Its decoded rendering lives with the struct sample table, which this
                // enum-only helper does not carry; the raw column value still appears in the
                // `input {tuple:?}` prefix every note already prints.
                ParamClass::Struct => column += 1,
                // Trust (Q1): a materialized-referent column consumes its slot like any other;
                // its value is an ordinary scalar and already appears in the `input {tuple:?}`
                // prefix, so this enum-only helper has nothing to add for it.
                ParamClass::PtrTo => column += 1,
                ParamClass::Enum => {
                    let raw = *tuple.get(column)?;
                    column += 1;
                    let sample_index = usize::try_from(raw).ok()?;
                    let (variant, payload) =
                        enum_samples.get(param)?.as_ref()?.get(sample_index)?;
                    let Ty::Enum(enum_id) = sig.params.get(param)? else { return None };
                    let def = module.enum_def(*enum_id)?;
                    let discriminants = def.effective_discriminants()?;
                    let discriminant = discriminants.get(*variant)?;
                    parts.push(format!(
                        "param {param}=variant {variant} (disc {discriminant}), payload {payload:?}"
                    ));
                }
            }
        }
        if column != tuple.len() {
            return None;
        }
        Some(if parts.is_empty() { String::new() } else { format!(" [{}]", parts.join("; ")) })
    };
    decode().unwrap_or_default()
}

/// Trust (B3/E6): per-side argument assembly — each side's values are typed against that
/// side's OWN module-local signature types. Scalars/opaques are id-less (shared recipe);
/// enum columns realize their abstract `(variant, payload)` description against THIS
/// module's EnumDef: element 0 = the EFFECTIVE discriminant (never the variant index)
/// typed EXACTLY at `canonical_tag_repr().ty()`, payload = the active variant's fields
/// only, in order, arity-exact. Err is fail-closed (the caller skips coverage-only).
fn build_side_args(
    module: &Module,
    sig: &trust_ir::FuncTy,
    classes: &[ParamClass],
    enum_samples: &[Option<Vec<(usize, Vec<i128>)>>],
    struct_samples: &[Option<Vec<Vec<i128>>>],
    tuple: &[i128],
) -> Result<Vec<InterpretValue>, String> {
    if classes.len() != sig.params.len() {
        return Err("parameter class table length does not match signature".to_string());
    }
    if enum_samples.len() != sig.params.len() {
        return Err("enum sample table length does not match signature".to_string());
    }
    if struct_samples.len() != sig.params.len() {
        return Err("struct sample table length does not match signature".to_string());
    }
    for (class, slot) in classes.iter().zip(enum_samples) {
        match (class, slot) {
            (ParamClass::Enum, Some(_))
            | (
                ParamClass::Scalar | ParamClass::Opaque | ParamClass::Struct | ParamClass::PtrTo,
                None,
            ) => {}
            _ => return Err("enum sample table is not aligned with parameter classes".to_string()),
        }
    }
    for (class, slot) in classes.iter().zip(struct_samples) {
        match (class, slot) {
            (ParamClass::Struct, Some(_))
            | (
                ParamClass::Scalar | ParamClass::Opaque | ParamClass::Enum | ParamClass::PtrTo,
                None,
            ) => {}
            _ => {
                return Err("struct sample table is not aligned with parameter classes".to_string());
            }
        }
    }
    let expected_columns = classes
        .iter()
        .filter(|class| {
            matches!(
                class,
                ParamClass::Scalar | ParamClass::Enum | ParamClass::Struct | ParamClass::PtrTo
            )
        })
        .count();
    if tuple.len() != expected_columns {
        return Err(format!(
            "sample tuple has {} column(s), expected {expected_columns}",
            tuple.len()
        ));
    }

    let mut k = 0usize;
    let args = sig
        .params
        .iter()
        .zip(classes.iter())
        .enumerate()
        .map(|(i, (ty, class))| match class {
            ParamClass::Scalar => {
                let raw = tuple.get(k).copied().ok_or("sample tuple column missing")?;
                k += 1;
                build_arg(ty, raw)
            }
            // Trust (Q1): the referent VALUE. `sig` here is the WRAPPER's signature, so `ty` is
            // already the recovered pointee type — this is byte-for-byte the `Scalar` recipe, and
            // the pointer is minted by the wrapper's `Alloca`/`Store`, never here. Marshalling a
            // pointer at the args site is what the lane deliberately does NOT do: a synthetic
            // `InterpretPointer` would name an allocation that no `MemoryState` holds.
            ParamClass::PtrTo => {
                let raw = tuple.get(k).copied().ok_or("sample tuple column missing")?;
                k += 1;
                build_arg(ty, raw)
            }
            ParamClass::Opaque => opaque_arg(ty),
            ParamClass::Enum => {
                // MUST consume the tuple exactly like Scalar (column desync otherwise).
                let raw = tuple.get(k).copied().ok_or("sample tuple column missing")?;
                k += 1;
                let samples = enum_samples
                    .get(i)
                    .and_then(|s| s.as_ref())
                    .ok_or("enum sample table missing")?;
                let sample_index = usize::try_from(raw)
                    .map_err(|_| "enum sample index is negative or too large")?;
                let (vidx, payload) =
                    samples.get(sample_index).ok_or("enum sample index out of bounds")?;
                let Ty::Enum(eid) = ty else {
                    return Err("enum param class on a non-enum signature type".to_string());
                };
                let def = module.enum_def(*eid).ok_or("enum def unresolvable at args site")?;
                let disc = *def
                    .effective_discriminants()
                    .ok_or("enum discriminants unresolvable at args site")?
                    .get(*vidx)
                    .ok_or("variant index out of bounds")?;
                let tag_ty =
                    def.canonical_tag_repr().ok_or("enum tag repr unresolvable at args site")?.ty();
                let fields = &def.variants.get(*vidx).ok_or("variant index out of bounds")?.fields;
                if fields.len() != payload.len() {
                    return Err("enum sample payload arity mismatch".to_string());
                }
                let mut elems = vec![
                    InterpretValue::int(tag_ty, disc)
                        .map_err(|e| format!("enum tag value: {e}"))?,
                ];
                for (fty, raw) in fields.iter().zip(payload) {
                    if matches!(fty, Ty::Unit) {
                        elems.push(InterpretValue {
                            ty: Ty::Unit,
                            kind: InterpretValueKind::Unit,
                        });
                        continue;
                    }
                    elems.push(build_arg(fty, *raw)?);
                }
                Ok(InterpretValue {
                    ty: Ty::Enum(*eid),
                    kind: InterpretValueKind::Aggregate(elems),
                })
            }
            ParamClass::Struct => {
                // MUST consume the tuple exactly like Scalar (column desync otherwise).
                let raw = tuple.get(k).copied().ok_or("sample tuple column missing")?;
                k += 1;
                let samples = struct_samples
                    .get(i)
                    .and_then(|s| s.as_ref())
                    .ok_or("struct sample table missing")?;
                let sample_index = usize::try_from(raw)
                    .map_err(|_| "struct sample index is negative or too large")?;
                let leaves =
                    samples.get(sample_index).ok_or("struct sample index out of bounds")?;
                let Ty::Struct(sid) = ty else {
                    return Err("struct param class on a non-struct signature type".to_string());
                };
                let mut cursor = 0usize;
                let value = realize_struct_arg(module, *sid, leaves, &mut cursor, MAX_STRUCT_DEPTH)?;
                if cursor != leaves.len() {
                    return Err(
                        "struct sample leaves were not consumed exactly (side shape drift)"
                            .to_string(),
                    );
                }
                Ok(value)
            }
        })
        .collect::<Result<Vec<_>, String>>()?;
    if k != tuple.len() {
        return Err("sample tuple columns were not consumed exactly".to_string());
    }
    Ok(args)
}

fn sample_values(t: &Ty) -> Vec<i128> {
    if matches!(t, Ty::Bool) {
        return vec![0, 1];
    }
    if matches!(t, Ty::F32 | Ty::F64) {
        let f32s = [0.0f32, -0.0, 1.0, -1.5, f32::MAX, f32::MIN_POSITIVE, f32::INFINITY, f32::NAN];
        let f64s = [0.0f64, -0.0, 1.0, -1.5, f64::MAX, f64::MIN_POSITIVE, f64::INFINITY, f64::NAN];
        return match t {
            Ty::F32 => f32s.iter().map(|v| i128::from(v.to_bits())).collect(),
            _ => f64s.iter().map(|v| i128::from(v.to_bits())).collect(),
        };
    }
    // Trust (v25 B1): Char samples must be VALID Unicode scalar values only —
    // 0..=0x10FFFF excluding the 0xD800..=0xDFFF surrogate gap — because the
    // trust-ir validator/interpreter rejects out-of-range char constants, so the
    // raw u32 boundaries the integer path below would produce (0xFFFFFFFF,
    // 0x7FFFFFFF) are unusable. Sample the boundaries of BOTH valid subranges
    // (0/0xD7FF and 0xE000/0x10FFFF) plus 1 and 'a' (0x61). `build_arg` carries
    // these through `InterpretValue::int` (Char is a 32-bit unsigned carrier in
    // the interpreter's int_shape; its constants are Int leaves).
    if matches!(t, Ty::Char) {
        return vec![0, 1, 0x61, 0xD7FF, 0xE000, 0x10FFFF];
    }
    let Some((bits, signed)) = int_shape(t) else {
        return Vec::new();
    };
    let mut v: Vec<i128> = Vec::new();
    v.push(0);
    v.push(1);
    if signed {
        v.push(-1);
    }
    if signed {
        if bits >= 128 {
            v.push(i128::MIN);
            v.push(i128::MAX);
        } else {
            let max = (1i128 << (bits - 1)) - 1;
            let min = -(1i128 << (bits - 1));
            v.push(min);
            v.push(max);
            v.push(max / 2);
            v.push(min / 2);
        }
    } else if bits >= 128 {
        // u128::MAX does not fit in i128; -1 masks to all-ones for unsigned.
        v.push(-1);
    } else {
        let max = (1i128 << bits) - 1;
        v.push(max);
        v.push(max / 2);
        v.push(2);
    }
    v.sort_unstable();
    v.dedup();
    v
}

/// Build one interpreter argument from a scalar `Ty` and a raw `i128` (for floats, the raw
/// value is the IEEE bit pattern `sample_values` produced; `FloatBits` carries f32 patterns in
/// the low 32 bits — the same convention `float_bits_from_f64` establishes for constants).
fn build_arg(t: &Ty, raw: i128) -> Result<InterpretValue, String> {
    match t {
        Ty::Bool => Ok(InterpretValue::bool(raw != 0)),
        Ty::F32 | Ty::F64 => {
            Ok(InterpretValue { ty: t.clone(), kind: InterpretValueKind::FloatBits(raw as u64) })
        }
        _ => InterpretValue::int(t.clone(), raw).map_err(|e| e.to_string()),
    }
}

/// The type-correct placeholder for a proven-never-read opaque param (module docs). The
/// interpreter checks `value.ty == expected_ty` at entry (`check_signature_values`) and —
/// by the opacity proof — never evaluates the value afterwards.
fn opaque_arg(t: &Ty) -> Result<InterpretValue, String> {
    match t {
        Ty::Ptr => Ok(InterpretValue { ty: Ty::Ptr, kind: InterpretValueKind::NullPtr }),
        Ty::Unit => Ok(InterpretValue { ty: Ty::Unit, kind: InterpretValueKind::Unit }),
        // Trust (B2-3): a NEVER-READ trait-object fat param — a two-lane null fat value
        // (data + vtable both NullPtr; TraitObject's metadata_ty is `Ty::Ptr`). Only
        // minted under the two-sided `param_never_read` proof, so the value is inert by
        // construction — it exists to satisfy the interpreter's arity/type admission.
        Ty::FatPtr(trust_ir::FatPtrKind::TraitObject { .. }) => Ok(InterpretValue {
            ty: t.clone(),
            kind: InterpretValueKind::FatPtr {
                data: Box::new(InterpretValue { ty: Ty::Ptr, kind: InterpretValueKind::NullPtr }),
                metadata: Box::new(InterpretValue {
                    ty: Ty::Ptr,
                    kind: InterpretValueKind::NullPtr,
                }),
            },
        }),
        other => Err(format!("no opaque placeholder for param type {other}")),
    }
}

/// Fail-closed opacity proof: is entry param `index` of `func` NEVER used by any instruction?
///
/// Non-destructive probe over `trust_ir::mem2reg::rewrite_inst` — the authoritative
/// match-on-every-variant operand walker (the same technique `to_mir`'s Alloca escape probe
/// uses): remap the param's `ValueId` to a fresh sentinel and see whether ANY instruction
/// changes. Covers every operand position — call/branch args, store-as-value, returns, GEPs —
/// and any future `Inst` variant automatically. SSA ids are function-unique, so the param id
/// cannot be shadowed or rebound.
fn param_never_read(func: &Function, index: usize) -> Result<bool, String> {
    let entry = func.block(func.entry).ok_or_else(|| "missing entry block".to_string())?;
    let (vid, _) =
        entry.params.get(index).ok_or_else(|| format!("entry block has no param {index}"))?;
    let max_id = func.max_value_id();
    if max_id == u32::MAX {
        return Err("value id space exhausted (no probe sentinel)".to_string());
    }
    let sentinel = ValueId::new(max_id + 1);
    let map: HashMap<ValueId, ValueId> = std::iter::once((*vid, sentinel)).collect();
    for blk in &func.blocks {
        for node in &blk.body {
            let mut probe = node.inst.clone();
            trust_ir::mem2reg::rewrite_inst(&mut probe, &map);
            if probe != node.inst {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

/// Trust (Q1): recover the REFERENT TYPE of a pointer parameter from the body.
///
/// `Ty::Ptr` is opaque — a signature never names what it points at — so a read pointer param has
/// no enumerable value until the body itself says what is behind it. The rule is deliberately the
/// narrowest one that is sound:
///
///   the param's entry `ValueId` is used ONLY as the `ptr` operand of PLAIN (non-volatile)
///   `Inst::Load`s, and every such load names the SAME type.
///
/// `Ok(Some(ty))` is that type; `Ok(None)` means the param is never read (the caller keeps the
/// existing opaque lane) or is read in some other way (fail-closed). Every rejection is silent
/// and returns `None` — this predicate can only ever ADD sampled verdicts.
///
/// Why "only as a `Load` ptr" and not merely "at least one `Load`": any other use OBSERVES THE
/// POINTER ITSELF rather than its referent — a `PtrToInt`, a comparison, a `Store` of the pointer,
/// a call argument, a return. The materialized referent is a fresh allocation whose raw
/// `InterpretPointer { allocation, offset }` is an artifact of allocation ORDER, which the two
/// sides are not obliged to share (their entries may hold different numbers of private slots). So
/// the moment the pointer's identity is observable, the sample stops being side-portable and this
/// lane would be manufacturing a verdict about an address nobody wrote. Restricting to the
/// dereference makes the pointer a pure conduit and the LOADED VALUE the only thing sampled.
///
/// Non-`Load` uses are detected with the same `rewrite_inst` substitution probe `param_never_read`
/// uses — the authoritative match-on-every-variant operand walker — so a new `Inst` variant that
/// carries an operand cannot silently slip past this scan.
fn sole_pointee_load(func: &Function, index: usize) -> Result<Option<Ty>, String> {
    let entry = func.block(func.entry).ok_or_else(|| "missing entry block".to_string())?;
    let (vid, _) =
        entry.params.get(index).ok_or_else(|| format!("entry block has no param {index}"))?;
    let max_id = func.max_value_id();
    if max_id == u32::MAX {
        return Err("value id space exhausted (no probe sentinel)".to_string());
    }
    let sentinel = ValueId::new(max_id + 1);
    let map: HashMap<ValueId, ValueId> = std::iter::once((*vid, sentinel)).collect();

    let mut pointee: Option<Ty> = None;
    for blk in &func.blocks {
        for node in &blk.body {
            // A plain load THROUGH the param is the one admitted use. `Inst::Load` carries
            // exactly one `ValueId` (`ptr`), so matching it here accounts for the whole node.
            if let Inst::Load { ty, ptr, volatile: false, .. } = &node.inst {
                if *ptr == *vid {
                    match &pointee {
                        None => pointee = Some(ty.clone()),
                        // Two loads of DIFFERENT types through one pointer: a reinterpreting
                        // read. There is no single referent value to sample, so fail closed.
                        Some(seen) if seen != ty => return Ok(None),
                        Some(_) => {}
                    }
                    continue;
                }
            }
            let mut probe = node.inst.clone();
            trust_ir::mem2reg::rewrite_inst(&mut probe, &map);
            if probe != node.inst {
                return Ok(None);
            }
        }
    }
    Ok(pointee)
}

/// Trust (Q1): may this parameter type ride through the synthesized wrapper's signature verbatim?
///
/// Load-bearing for the wrapper-equality ASSERTION, not merely for taste. A wrapper param type is
/// copied out of that side's OWN entry signature, and a table-indexed type (`Ty::Struct(id)`,
/// `Ty::Enum(id)`, `Ty::FatPtr(TraitObject { trait_id })`, ...) carries a MODULE-LOCAL id, so two
/// structurally-identical wrappers would compare UNEQUAL on the raw ids alone. Restricting the
/// pass-through set to id-FREE types is what lets `wrappers_agree` be an exact structural equality
/// instead of a cross-module type comparison — a weaker check that would then need its own
/// correctness argument. The excluded shapes keep the refusal they have today.
fn pointer_lane_param_ok(t: &Ty) -> bool {
    is_interpretable_scalar(t) || matches!(t, Ty::Ptr | Ty::Unit)
}

/// Trust (Q1): what the pointer-param input lane decided about one body.
#[derive(Debug, Clone, PartialEq, Eq)]
enum PointerLane {
    /// Slice A — SHIPPED. A scalar referent: sampled through the synthesized wrapper.
    Scalar { index: usize, pointee: Ty },
    /// Slice B — CEILING PROBE, not yet sampled. An aggregate referent whose two-sided BYTE
    /// LAYOUT was proven to agree (`struct_layout_agrees`). Recorded as its own skip class so the
    /// follow-on lane's yield is a MEASUREMENT on the real corpus rather than an estimate; today
    /// it still returns `NotRun`.
    AggregateCeiling { index: usize },
}

/// Trust (Q1): decide the pointer-param input lane for a body, two-sidedly and fail-closed.
///
/// Whole-signature, not per-param, because three of the conditions are about the body as a whole:
/// exactly ONE read pointer param, every OTHER param id-free and pass-through-able, and NO pointer
/// in a return position. The last one matters because `returns_agree` compares a returned pointer
/// RAW (`InterpretPointer { allocation, offset }`); the wrapper shifts every allocation id by the
/// slot it mints, and the two sides' entries need not allocate in the same order, so a returned
/// pointer could differ for a reason that is not a semantic divergence. Refusing pointer returns
/// keeps that comparison out of reach entirely.
fn pointer_param_input_lane(
    thir_module: &Module,
    thir_fn: &Function,
    thir_sig: &FuncTy,
    oracle: &Module,
    oracle_fn: &Function,
    oracle_sig: &FuncTy,
) -> Option<PointerLane> {
    if thir_sig.params.len() != oracle_sig.params.len() {
        return None;
    }
    // No pointer may reach a return position on either side (see the doc comment).
    let returns_a_pointer = |sig: &FuncTy| {
        sig.returns.iter().any(|t| matches!(t, Ty::Ptr | Ty::FatPtr(_)))
    };
    if returns_a_pointer(thir_sig) || returns_a_pointer(oracle_sig) {
        return None;
    }

    let mut lane: Option<usize> = None;
    for (i, t) in thir_sig.params.iter().enumerate() {
        if oracle_sig.params.get(i) != Some(t) {
            return None;
        }
        if !matches!(t, Ty::Ptr) {
            // Every non-target param must be able to ride the wrapper verbatim.
            if !pointer_lane_param_ok(t) {
                return None;
            }
            continue;
        }
        // A `Ty::Ptr` that is provably never read stays on the existing OPAQUE lane, which is
        // cheaper and already works; only a READ pointer is this lane's business.
        let read = matches!(param_never_read(thir_fn, i), Ok(false))
            || matches!(param_never_read(oracle_fn, i), Ok(false));
        if !read {
            continue;
        }
        // Exactly one read pointer param. A second one is refused outright rather than
        // materialized alongside: two referents multiply the sample space and, more importantly,
        // give the wrapper two slots whose relative allocation order becomes part of the model.
        if lane.is_some() {
            return None;
        }
        lane = Some(i);
    }
    let index = lane?;

    // The referent type must be recoverable on BOTH sides, and they must AGREE. This is the
    // cross-side JOIN the lane rests on: the pointee is not in either signature, so nothing else
    // in the differential would ever check that the two sides think the referent is the same
    // thing.
    let (Ok(Some(a)), Ok(Some(b))) =
        (sole_pointee_load(thir_fn, index), sole_pointee_load(oracle_fn, index))
    else {
        return None;
    };

    if is_interpretable_scalar(&a) && a == b {
        return Some(PointerLane::Scalar { index, pointee: a });
    }
    // Slice B ceiling probe: a whole-aggregate referent (`#[derive(Clone)]` on a `Copy` type is
    // `*self`, a WHOLE load) whose byte layout provably agrees across the two sides.
    if struct_layout_agrees(thir_module, oracle, &a, &b, MAX_STRUCT_DEPTH) {
        return Some(PointerLane::AggregateCeiling { index });
    }
    None
}

/// Trust (Q1): TWO-SIDED BYTE-LAYOUT PARITY for an aggregate referent — the reusable primitive.
///
/// This is deliberately a STRICTLY STRONGER gate than `struct_param_admissible`, and the reason is
/// the whole point of the pointer lane. A BY-VALUE struct param never touches bytes: trust-ir's
/// aggregate value model is a positional element list with NO padding and no offsets (`size`,
/// `align` and `FieldDef::offset` are layout METADATA, never elements), so `repr` and field
/// placement cannot change what `realize_struct_arg` marshals — which is exactly why the by-value
/// gate can ignore layout. A POINTER referent is the opposite case: the value is `Store`d into an
/// allocation and `Load`ed back through the interpreter's BYTE funnel, so offsets, size and align
/// are live semantics. Two sides that agree on the field LIST but disagree on where those fields
/// sit would round-trip differently, and the differential would read the disagreement as a
/// divergence in the program.
///
/// Every conjunct is an ADMISSION condition. Anything unproven — a `None` size, a `None` align, a
/// single `None` field offset, a depth overrun — fails CLOSED, because an absent layout fact is
/// precisely the case where the two producers are free to have chosen differently.
///
/// DECLARATION ORDER IS NOT CONSULTED, and must not be: `repr(Rust)` lets rustc REORDER fields, so
/// the i-th declared field is not the i-th field in memory. Parity is decided on the (name, type,
/// offset) triple per field, which is invariant under that reordering — while still pinning field
/// IDENTITY by name, so a struct cannot compare equal to itself with two same-typed fields
/// transposed (the `MemoryRegion { AllocationId, usize, usize }` hazard `struct_param_admissible`
/// names).
///
/// Generalisation, for the memory lanes this campaign still owes: the shape here — resolve both
/// sides' defs, refuse on any absent fact, compare the fields as an identity-bearing set rather
/// than a positional list, recurse with a depth bound — is the two-sided layout proof a caller-
/// memory observable will need in order to compare final memory rather than skip it. The only
/// piece it does not yet carry is padding-byte provenance, which a memory COMPARISON needs and an
/// input MATERIALIZATION does not.
fn struct_layout_agrees(am: &Module, bm: &Module, a: &Ty, b: &Ty, depth: u32) -> bool {
    if depth == 0 {
        return false;
    }
    match (a, b) {
        (Ty::Struct(sa), Ty::Struct(sb)) => {
            let (Some(da), Some(db)) = (am.struct_def(*sa), bm.struct_def(*sb)) else {
                return false;
            };
            // Whole-object footprint must be proven and equal on both sides.
            let (Some(sza), Some(szb)) = (da.size, db.size) else {
                return false;
            };
            let (Some(aa), Some(ab)) = (da.align, db.align) else {
                return false;
            };
            if sza != szb || aa != ab || da.repr != db.repr {
                return false;
            }
            if da.fields.len() != db.fields.len() {
                return false;
            }
            da.fields.iter().zip(&db.fields).all(|(fa, fb)| {
                let (Some(oa), Some(ob)) = (fa.offset, fb.offset) else {
                    return false;
                };
                // ALWAYS recurse on the field type — never short-circuit on `fa.ty == fb.ty`.
                // `Ty::Struct(id)` is a MODULE-LOCAL index, so raw equality is the classic false
                // agreement this file's step-(5) comment names: two DIFFERENT defs that happen to
                // sit at the same id compare equal, and a depth-2 layout disagreement underneath
                // is then never looked at. The `nested_depth_2` unit test is that exact case, and
                // it failed against the short-circuiting form.
                oa == ob
                    && fa.name == fb.name
                    && struct_layout_agrees(am, bm, &fa.ty, &fb.ty, depth - 1)
            })
        }
        // A scalar leaf's layout is fixed by its type, so equality IS the whole condition — and
        // `is_interpretable_scalar` is what keeps this arm from accepting any other table-indexed
        // type (`Ty::Enum`, `Ty::Array`, ...) on raw equality for the same reason as above. Those
        // referents need their own layout proof and are refused until they have one.
        _ => a == b && is_interpretable_scalar(a),
    }
}

/// Trust (Q1): the SYNTHESIZED WRAPPER — `Alloca` the referent, `Store` the sampled value, `Call`
/// the entry with the slot, return whatever the entry returned.
///
/// Returns the mutated module (the wrapper appended), the wrapper's `FuncId`, and its signature.
/// The signature MUST be registered with `Module::add_func_type`: the interpreter resolves
/// `Function::ty` through the module's func-type table on every call and hard-errors
/// `signature_mismatch` on an unregistered id, so an unregistered wrapper would fail every body
/// rather than none.
///
/// The wrapper is built from the ENTRY SIGNATURE and the lane index alone — no module-local ids
/// enter it (`pointer_lane_param_ok` guarantees the pass-through types are id-free, and the
/// pointee is a scalar) — which is what makes the two sides' wrappers literally comparable.
fn build_pointee_wrapper(
    module: &Module,
    entry: FuncId,
    sig: &FuncTy,
    index: usize,
    pointee: &Ty,
) -> Option<(Module, FuncId, FuncTy)> {
    let mut wrapper_sig = sig.clone();
    *wrapper_sig.params.get_mut(index)? = pointee.clone();

    let mut out = module.clone();
    let ty_id = out.add_func_type(wrapper_sig.clone());
    // The wrapper's id must be PROVABLY ABSENT from this module, and `functions.len()` does not
    // establish that. A `FuncId` in this producer IS a rustc `DefIndex`
    // (`admit_callee_inner`'s `FuncId::new(def_id.index.as_u32())`), so the id space is SPARSE:
    // a module holding the body at 0 and one callee at DefIndex 2 has `len() == 2`, and a wrapper
    // minted at 2 would collide — `function_by_id(2)` resolves index-first and would hand the
    // callee's own `Inst::Call` to the WRAPPER instead, i.e. silent infinite recursion or a call
    // to the wrong program object. This is the same requirement the fn-ptr adapter band states
    // ("the id must be provably ABSENT from the callee ledger"); one past the maximum satisfies
    // it without reserving anything, and `checked_add` fails the lane CLOSED at the top of the
    // space rather than wrapping into the adapter band.
    let func_id = FuncId::new(match out.functions.iter().map(|f| f.id.index()).max() {
        Some(max) => max.checked_add(1)?,
        None => 0,
    });
    // Deterministic, module-independent value numbering: params 0..n, then the slot, then the
    // call results. Both sides run this identical arithmetic, so the ids match by construction.
    let param_ids: Vec<ValueId> =
        (0..wrapper_sig.params.len()).map(|i| ValueId::new(u32::try_from(i).unwrap())).collect();
    let slot = ValueId::new(u32::try_from(wrapper_sig.params.len()).ok()?);
    let results: Vec<ValueId> = (0..sig.returns.len())
        .map(|i| ValueId::new(u32::try_from(wrapper_sig.params.len() + 1 + i).unwrap()))
        .collect();

    let mut block = Block::new(trust_ir::BlockId::new(0));
    for (id, ty) in param_ids.iter().zip(&wrapper_sig.params) {
        block.params.push((*id, ty.clone()));
    }
    block.body.push(InstrNode::new(Inst::Alloca {
        ty: pointee.clone(),
        count: None,
        align: None,
    })
    .with_results(vec![slot]));
    block.body.push(InstrNode::new(Inst::Store {
        ty: pointee.clone(),
        ptr: slot,
        value: param_ids[index],
        volatile: false,
        align: None,
    }));
    let mut call_args = param_ids.clone();
    call_args[index] = slot;
    block.body.push(
        InstrNode::new(Inst::Call { callee: entry, args: call_args })
            .with_results(results.clone()),
    );
    block.body.push(InstrNode::new(Inst::Return { values: results }));

    let mut func =
        Function::new(func_id, "__trust_diff_pointee_wrapper", ty_id, trust_ir::BlockId::new(0));
    func.blocks = vec![block];
    out.add_function(func);
    Some((out, func_id, wrapper_sig))
}

/// Trust (Q1): DISCHARGE the wrapper-skipping debt.
///
/// `first_unmodeled_observation` never walks the wrapper (it is rooted at the entry and follows
/// calls callee-ward), so the wrapper's `Alloca`/`Store` are never compared across sides. That is
/// sound only if the two wrappers ARE the same program, and this asserts exactly that rather than
/// arguing it in prose: same block structure, same params, same instruction sequence, modulo the
/// one field that is legitimately per-side — the `Call`'s callee, which is that module's own entry.
///
/// An argued relaxation left in a comment is the defect class this campaign has spent the day
/// finding, so this returns a diagnostic and the caller fails CLOSED on it.
fn wrappers_agree(
    a: &Function,
    a_entry: FuncId,
    b: &Function,
    b_entry: FuncId,
) -> Result<(), String> {
    if a.blocks.len() != b.blocks.len() || a.entry != b.entry {
        return Err("wrapper block structure differs across sides".to_string());
    }
    for (ba, bb) in a.blocks.iter().zip(&b.blocks) {
        if ba.id != bb.id || ba.params != bb.params {
            return Err("wrapper block parameters differ across sides".to_string());
        }
        if ba.body.len() != bb.body.len() {
            return Err("wrapper instruction count differs across sides".to_string());
        }
        for (na, nb) in ba.body.iter().zip(&bb.body) {
            if na.results != nb.results {
                return Err("wrapper result numbering differs across sides".to_string());
            }
            let same = match (&na.inst, &nb.inst) {
                (
                    Inst::Call { callee: ca, args: aa },
                    Inst::Call { callee: cb, args: ab },
                ) => *ca == a_entry && *cb == b_entry && aa == ab,
                (x, y) => x == y,
            };
            if !same {
                return Err("wrapper instruction sequence differs across sides".to_string());
            }
        }
    }
    Ok(())
}

/// Streaming cartesian product of per-parameter sample lists. The last column
/// advances fastest, matching the former eager helper exactly. Zero parameters
/// yields one empty tuple; any empty parameter list yields no tuples.
struct CartesianProduct<'a> {
    columns: &'a [Vec<i128>],
    indices: Vec<usize>,
    finished: bool,
}

impl<'a> CartesianProduct<'a> {
    fn new(columns: &'a [Vec<i128>]) -> Self {
        Self {
            columns,
            indices: vec![0; columns.len()],
            finished: columns.iter().any(Vec::is_empty),
        }
    }
}

impl Iterator for CartesianProduct<'_> {
    type Item = Vec<i128>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        let row =
            self.columns.iter().zip(&self.indices).map(|(column, &index)| column[index]).collect();

        if self.columns.is_empty() {
            self.finished = true;
            return Some(row);
        }
        for column in (0..self.columns.len()).rev() {
            self.indices[column] += 1;
            if self.indices[column] < self.columns[column].len() {
                return Some(row);
            }
            self.indices[column] = 0;
        }
        self.finished = true;
        Some(row)
    }
}

#[cfg(test)]
mod tests {
    use trust_ir::interpret::InterpretErrorCode as C;
    use trust_ir::value::GlobalId;
    use trust_ir::{EnumDef, EnumId, EnumTagRepr, EnumVariant};

    use super::*;

    /// Trust (slice 20): the pending-const routing, pinned as a truth table.
    ///
    /// The two deferral reasons are INDEPENDENT — a body qualifies on either — and the one case
    /// that must stay out is the ordinary clean call-free body, which still earns its verdict at
    /// the hook. Before slice 20 the middle two rows were `false`: a pending-const body was
    /// routed to NEITHER differential, so it could never be adjudicated at all, which is the
    /// 111-body population this slice recovers.
    #[test]
    fn deferred_to_seam_covers_pending_const_bodies_independently_of_calls() {
        // (clean, pending-empty, call-bearing) -> deferred?
        let cases = [
            // Ordinary clean call-free body: NOT deferred — the hook adjudicates it directly.
            ((true, true, false), false),
            // B9-A: clean and call-bearing.
            ((true, true, true), true),
            // Slice 20: clean, pending-const, CALL-FREE. The seam's callee closure is just the
            // entry and the bundle is a single function.
            ((true, false, false), true),
            // Slice 20: both reasons at once.
            ((true, false, true), true),
            // An unsupported shape vetoes deferral outright, whatever else holds: there is
            // nothing for the finalizer to dissolve.
            ((false, true, true), false),
            ((false, false, false), false),
            ((false, false, true), false),
        ];
        for ((unsup_empty, pending_empty, call), want) in cases {
            assert_eq!(
                deferred_to_seam_parts(unsup_empty, pending_empty, call),
                want,
                "deferred_to_seam_parts(unsupported_empty={unsup_empty}, \
                 pending_empty={pending_empty}, contains_call={call})"
            );
        }
    }

    #[test]
    fn cartesian_product_streams_in_stable_order() {
        let columns = vec![vec![1, 2], vec![10, 20, 30]];
        assert_eq!(
            CartesianProduct::new(&columns).collect::<Vec<_>>(),
            vec![vec![1, 10], vec![1, 20], vec![1, 30], vec![2, 10], vec![2, 20], vec![2, 30],]
        );
        assert_eq!(CartesianProduct::new(&[]).collect::<Vec<_>>(), vec![Vec::<i128>::new()]);
        assert!(CartesianProduct::new(&[Vec::new()]).next().is_none());
    }

    fn tagged_enum_def(id: EnumId, variants: usize) -> EnumDef {
        EnumDef::new(
            id,
            "Tagged",
            (0..variants)
                .map(|index| EnumVariant {
                    name: format!("V{index}"),
                    fields: if index == 1 { vec![Ty::I32] } else { Vec::new() },
                    field_names: Vec::new(),
                })
                .collect(),
        )
        .with_discriminants(vec![Some(-5), Some(7)])
        .with_repr(EnumTagRepr::I16)
    }

    fn module_with_tagged_enum(
        name: &str,
        target_is_id_one: bool,
        variants: usize,
    ) -> (Module, EnumId) {
        let mut module = Module::new(name);
        if target_is_id_one {
            module.add_enum(EnumDef::new(
                EnumId::new(0),
                "Dummy",
                vec![EnumVariant {
                    name: "Only".into(),
                    fields: Vec::new(),
                    field_names: Vec::new(),
                }],
            ));
        }
        let target = EnumId::new(u32::from(target_is_id_one));
        module.add_enum(tagged_enum_def(target, variants));
        (module, target)
    }

    fn enum_detector_module(
        name: &str,
        target_is_id_one: bool,
        variants: usize,
        constant_false: bool,
    ) -> Module {
        let (mut module, target) = module_with_tagged_enum(name, target_is_id_one, variants);
        let enum_ty = Ty::Enum(target);
        let sig = module.add_func_type(FuncTy {
            params: vec![enum_ty.clone()],
            returns: vec![Ty::Bool],
            is_vararg: false,
        });
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0)).with_param(v(0), enum_ty);
        if constant_false {
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
                    .with_result(v(1)),
            );
            block.body.push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        } else {
            block.body.push(
                InstrNode::new(Inst::ExtractField { ty: Ty::I16, aggregate: v(0), field: 0 })
                    .with_result(v(1)),
            );
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::I16, value: Constant::Int(13) })
                    .with_result(v(2)),
            );
            block.body.push(
                InstrNode::new(Inst::ICmp {
                    op: trust_ir::ICmpOp::Eq,
                    ty: Ty::I16,
                    lhs: v(1),
                    rhs: v(2),
                })
                .with_result(v(3)),
            );
            block.body.push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        }
        let mut function =
            Function::new(FuncId::new(0), "detect_last", sig, trust_ir::BlockId::new(0));
        function.blocks.push(block);
        module.add_function(function);
        module
    }

    #[test]
    fn build_side_args_mixes_scalar_enum_opaque_columns_per_side() {
        let (mut thir, thir_enum) = module_with_tagged_enum("thir", false, 2);
        let (mut oracle, oracle_enum) = module_with_tagged_enum("oracle", true, 2);
        let params = |enum_id| vec![Ty::I32, Ty::Enum(enum_id), Ty::Unit, Ty::Bool];
        let thir_sig_id = thir.add_func_type(FuncTy {
            params: params(thir_enum),
            returns: Vec::new(),
            is_vararg: false,
        });
        let oracle_sig_id = oracle.add_func_type(FuncTy {
            params: params(oracle_enum),
            returns: Vec::new(),
            is_vararg: false,
        });
        let classes =
            vec![ParamClass::Scalar, ParamClass::Enum, ParamClass::Opaque, ParamClass::Scalar];
        let samples = vec![None, Some(vec![(0, Vec::new()), (1, vec![42])]), None, None];
        let no_structs: Vec<Option<Vec<Vec<i128>>>> = vec![None; 4];
        let tuple = [17, 1, 1];
        let thir_args = build_side_args(
            &thir,
            thir.func_type(thir_sig_id).expect("THIR signature"),
            &classes,
            &samples,
            &no_structs,
            &tuple,
        )
        .expect("THIR-side recipe");
        let oracle_args = build_side_args(
            &oracle,
            oracle.func_type(oracle_sig_id).expect("oracle signature"),
            &classes,
            &samples,
            &no_structs,
            &tuple,
        )
        .expect("oracle-side recipe");

        assert_eq!(thir_args[0], InterpretValue::int(Ty::I32, 17).expect("i32"));
        assert_eq!(thir_args[2].kind, InterpretValueKind::Unit);
        assert_eq!(thir_args[3], InterpretValue::bool(true));
        assert_eq!(thir_args[1].ty, Ty::Enum(thir_enum));
        assert_eq!(oracle_args[1].ty, Ty::Enum(oracle_enum));
        let expected_payload = InterpretValueKind::Aggregate(vec![
            InterpretValue::int(Ty::I16, 7).expect("effective discriminant"),
            InterpretValue::int(Ty::I32, 42).expect("payload"),
        ]);
        assert_eq!(thir_args[1].kind, expected_payload);
        assert_eq!(oracle_args[1].kind, thir_args[1].kind);

        let fieldless = build_side_args(
            &thir,
            thir.func_type(thir_sig_id).expect("THIR signature"),
            &classes,
            &samples,
            &no_structs,
            &[17, 0, 1],
        )
        .expect("fieldless recipe");
        assert_eq!(
            fieldless[1].kind,
            InterpretValueKind::Aggregate(vec![
                InterpretValue::int(Ty::I16, -5).expect("effective discriminant")
            ])
        );
        assert!(
            decoded_enum_sample_suffix(
                &thir,
                thir.func_type(thir_sig_id).expect("THIR signature"),
                &classes,
                &samples,
                &tuple,
            )
            .contains("variant 1 (disc 7), payload [42]")
        );
    }

    #[test]
    fn enum_samples_cover_the_cap_and_reject_one_more() {
        // Written against `MAX_ENUM_SAMPLES` rather than a literal: the property under test is
        // "pass 1 spends one sample per variant, so the cap IS the admissible variant count",
        // which must hold at whatever the constant is. A literal here silently became a
        // restatement of the constant the day the cap moved.
        let cap = MAX_ENUM_SAMPLES;
        let at_cap = enum_abstract_samples(&tagged_enum_def(EnumId::new(0), cap))
            .expect("cap-many variants fit the complete-coverage cap");
        assert_eq!(at_cap.len(), cap);
        assert_eq!(
            at_cap.iter().map(|(variant, _)| *variant).collect::<Vec<_>>(),
            (0..cap).collect::<Vec<_>>()
        );
        assert!(enum_abstract_samples(&tagged_enum_def(EnumId::new(0), cap + 1)).is_none());

        let thir = enum_detector_module("over_cap_thir", false, cap + 1, false);
        let oracle = enum_detector_module("over_cap_oracle", true, cap + 1, false);
        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::NotRun);
        assert_eq!(report.samples_checked, 0);
    }

    #[test]
    fn enum_samples_high_field_count_is_bounded_without_overflow() {
        let fields = usize::BITS as usize + 1;
        let def = EnumDef::new(
            EnumId::new(0),
            "Wide",
            vec![EnumVariant {
                name: "V".into(),
                fields: vec![Ty::Bool; fields],
                field_names: Vec::new(),
            }],
        );
        let samples = enum_abstract_samples(&def).expect("wide payload remains bounded");
        assert_eq!(samples.len(), MAX_ENUM_SAMPLES);
        assert!(samples.iter().all(|(variant, payload)| *variant == 0 && payload.len() == fields));
    }

    #[test]
    fn build_side_args_rejects_malformed_recipe_shapes() {
        let (mut module, enum_id) = module_with_tagged_enum("malformed", false, 2);
        let sig_id = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::Enum(enum_id), Ty::Unit, Ty::Bool],
            returns: Vec::new(),
            is_vararg: false,
        });
        let sig = module.func_type(sig_id).expect("signature");
        let classes =
            vec![ParamClass::Scalar, ParamClass::Enum, ParamClass::Opaque, ParamClass::Scalar];
        let tables = vec![None, Some(vec![(0, Vec::new()), (1, vec![42])]), None, None];
        let no_structs: Vec<Option<Vec<Vec<i128>>>> = vec![None; 4];
        let rejects =
            |classes: &[ParamClass], tables: &[Option<Vec<(usize, Vec<i128>)>>], tuple: &[i128]| {
                build_side_args(&module, sig, classes, tables, &no_structs[..classes.len()], tuple)
                    .is_err()
            };

        assert!(rejects(&classes, &tables, &[17, 1]));
        assert!(rejects(&classes, &tables, &[17, 1, 1, 99]));
        assert!(rejects(&classes[..3], &tables, &[17, 1, 1]));
        assert!(rejects(&classes, &tables[..3], &[17, 1, 1]));

        let mut stray = tables.clone();
        stray[0] = Some(vec![(0, Vec::new())]);
        assert!(rejects(&classes, &stray, &[17, 1, 1]));
        let mut missing = tables.clone();
        missing[1] = None;
        assert!(rejects(&classes, &missing, &[17, 1, 1]));
        assert!(rejects(&classes, &tables, &[17, 99, 1]));
        assert!(rejects(&classes, &tables, &[17, -1, 1]));

        let mut bad_variant = tables.clone();
        bad_variant[1] = Some(vec![(99, Vec::new())]);
        assert!(rejects(&classes, &bad_variant, &[17, 0, 1]));
        let mut bad_payload = tables;
        bad_payload[1] = Some(vec![(1, Vec::new())]);
        assert!(rejects(&classes, &bad_payload, &[17, 0, 1]));
    }

    #[test]
    fn compare_entries_covers_last_enum_variant_across_local_ids_and_detects_divergence() {
        let thir = enum_detector_module("enum_thir", false, 8, false);
        let same = enum_detector_module("enum_same", true, 8, false);
        let agreed = compare_entries(&thir, FuncId::new(0), &same, FuncId::new(0));
        assert_eq!(
            agreed.mode,
            DiffMode::Agreed,
            "different local ids must agree: {:?}",
            agreed.notes
        );
        // The count is a function of the cap, stated rather than pasted. Pass 1 spends one
        // sample per variant (8 here); pass 2 then deepens the ONLY payload-bearing variant
        // (`tagged_enum_def` gives variant 1 an `i32`, whose `sample_values` pool is 7 wide)
        // one sample per round, so the recipe tops out at 8 + (7 - 1) = 14 and the budget
        // decides below that. Variant coverage — the property under test — is pass 1's, and
        // is therefore complete at every cap >= 8.
        assert!(MAX_ENUM_SAMPLES >= 8, "the 8-variant detector must fit the cap");
        assert_eq!(agreed.samples_checked, MAX_ENUM_SAMPLES.min(8 + 6));

        let perturbed = enum_detector_module("enum_perturbed", true, 8, true);
        let mismatch = compare_entries(&thir, FuncId::new(0), &perturbed, FuncId::new(0));
        assert_eq!(mismatch.mode, DiffMode::MirOracle, "eighth variant must be observed");
        assert_eq!(mismatch.samples_checked, 8);
        assert!(
            mismatch.notes.iter().any(|note| note.contains("variant 7 (disc 13), payload []")),
            "decoded divergence must identify the covered variant: {:?}",
            mismatch.notes
        );
    }

    #[test]
    fn enum_columns_count_toward_sampled_parameter_cap() {
        let build = |name: &str, target_is_id_one: bool| {
            let (mut module, enum_id) = module_with_tagged_enum(name, target_is_id_one, 2);
            let enum_ty = Ty::Enum(enum_id);
            let sig = module.add_func_type(FuncTy {
                params: vec![enum_ty.clone(); MAX_PARAMS + 1],
                returns: vec![Ty::Bool],
                is_vararg: false,
            });
            let v = ValueId::new;
            let mut block = Block::new(trust_ir::BlockId::new(0));
            for index in 0..=MAX_PARAMS {
                block = block.with_param(v(index as u32), enum_ty.clone());
            }
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
                    .with_result(v((MAX_PARAMS + 1) as u32)),
            );
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![v((MAX_PARAMS + 1) as u32)] }));
            let mut function =
                Function::new(FuncId::new(0), "too_many", sig, trust_ir::BlockId::new(0));
            function.blocks.push(block);
            module.add_function(function);
            module
        };

        let report = compare_entries(
            &build("cap_thir", false),
            FuncId::new(0),
            &build("cap_oracle", true),
            FuncId::new(0),
        );
        assert_eq!(report.mode, DiffMode::NotRun);
        assert!(report.notes.iter().any(|note| note.contains("scalar param count 5 exceeds")));
    }

    fn single_block_module(name: &str, params: Vec<Ty>, returns: Vec<Ty>, block: Block) -> Module {
        let mut module = Module::new(name.to_string());
        let sig = module.add_func_type(FuncTy { params, returns, is_vararg: false });
        let mut function = Function::new(FuncId::new(0), name, sig, trust_ir::BlockId::new(0));
        function.blocks.push(block);
        module.add_function(function);
        module
    }

    #[test]
    fn declaration_seed_store_then_load_is_live_havoc() {
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Alloca { ty: Ty::I64, count: None, align: None })
                .with_result(v(0)),
        );
        block.body.push(InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(1)));
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block.body.push(
            InstrNode::new(Inst::Load { ty: Ty::I64, ptr: v(0), volatile: false, align: None })
                .with_result(v(2)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let module = single_block_module("declaration_seed_load", vec![], vec![Ty::I64], block);

        let (class, trace) = classify_undefs_traced(&module);
        assert!(matches!(class, UndefClass::Live));
        assert_eq!(trace.as_deref(), Some("fn declaration_seed_load undef ty i64"));
        let err = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), vec![])
            .expect_err("executing a declaration seed is UB, never a deterministic zero");
        assert_eq!(err.code, C::UndefinedBehavior);
    }

    fn tuple_seed_module(complete: bool) -> Module {
        let v = ValueId::new;
        let tuple_ty = Ty::Tuple(vec![Ty::I64, Ty::Bool]);
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Undef { ty: tuple_ty.clone() }).with_result(v(0)));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(7) }).with_result(v(1)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: tuple_ty.clone(),
                aggregate: v(0),
                field: 0,
                value: v(1),
            })
            .with_result(v(2)),
        );
        let result = if complete {
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                    .with_result(v(3)),
            );
            block.body.push(
                InstrNode::new(Inst::InsertField {
                    ty: tuple_ty.clone(),
                    aggregate: v(2),
                    field: 1,
                    value: v(3),
                })
                .with_result(v(4)),
            );
            v(4)
        } else {
            v(2)
        };
        block.body.push(InstrNode::new(Inst::Return { values: vec![result] }));
        single_block_module("tuple_seed", vec![], vec![tuple_ty], block)
    }

    #[test]
    fn only_a_fully_overwritten_aggregate_seed_is_dead() {
        let partial = tuple_seed_module(false);
        assert!(matches!(classify_undefs(&partial), UndefClass::Live));

        let complete = tuple_seed_module(true);
        assert!(matches!(classify_undefs(&complete), UndefClass::DeadSeeds));
        let normalized = substitute_dead_seeds(complete);
        assert!(matches!(classify_undefs(&normalized), UndefClass::None));
        let outcome = Interpreter::with_module(&normalized)
            .execute_func(FuncId::new(0), vec![])
            .expect("the completely overwritten tuple should interpret after substitution");
        assert_eq!(
            outcome.returns[0].kind,
            InterpretValueKind::Aggregate(vec![
                InterpretValue::int(Ty::I64, 7).unwrap(),
                InterpretValue::bool(true),
            ])
        );
    }

    /// Trust (vtable slice 11): the A-shape corpus twin (issue-37550's `|| t` env) — a
    /// closure-env `struct { Ptr }` seed whose single lane is a borrow of a real stack slot,
    /// fully InsertField-covered. Before the slice the Ptr lane had no zero spelling, so the
    /// body was held LIVE despite the coverage proof; now it substitutes to the wave-PS null
    /// pointer and interprets to completion.
    #[test]
    fn ptr_lane_env_seed_is_dead_and_interprets_after_substitution() {
        use trust_ir::{FieldDef, StructDef, StructId};
        let v = ValueId::new;
        let mut module = Module::new("ptr_env_seed");
        let sid = module.add_struct(StructDef {
            id: StructId::new(0),
            name: "closure_env".into(),
            fields: vec![FieldDef { name: "t".into(), ty: Ty::Ptr, offset: None }],
            size: None,
            align: None,
            repr: Default::default(),
        });
        let env_ty = Ty::Struct(sid);
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Alloca { ty: Ty::Bool, count: None, align: None })
                .with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(v(1)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::Bool,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(2)));
        block.body.push(InstrNode::new(Inst::Undef { ty: env_ty.clone() }).with_result(v(3)));
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: env_ty.clone(),
                aggregate: v(3),
                field: 0,
                value: v(2),
            })
            .with_result(v(4)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        let sig = module.add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false });
        let mut function =
            Function::new(FuncId::new(0), "ptr_env_seed", sig, trust_ir::BlockId::new(0));
        function.blocks.push(block);
        module.add_function(function);

        assert!(matches!(classify_undefs(&module), UndefClass::DeadSeeds));
        let normalized = substitute_dead_seeds(module);
        assert!(matches!(classify_undefs(&normalized), UndefClass::None));
        Interpreter::with_module(&normalized)
            .execute_func(FuncId::new(0), vec![])
            .expect("the fully-overwritten ptr-lane env seed interprets after substitution");
    }

    /// Trust (vtable slice 11): the B-shape corpus twin (issue-97007's `Walk { _p: () }`) — a
    /// `struct { Unit }` seed fully covered by a unit InsertField. Held only on the missing
    /// `Ty::Unit` zero spelling before the slice; PhantomData is the sole inhabitant.
    #[test]
    fn unit_lane_struct_seed_is_dead_and_interprets_after_substitution() {
        use trust_ir::{FieldDef, StructDef, StructId};
        let v = ValueId::new;
        let mut module = Module::new("unit_field_seed");
        let sid = module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Walk".into(),
            fields: vec![FieldDef { name: "_p".into(), ty: Ty::Unit, offset: None }],
            size: None,
            align: None,
            repr: Default::default(),
        });
        let walk_ty = Ty::Struct(sid);
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Unit, value: Constant::PhantomData })
                .with_result(v(0)),
        );
        block.body.push(InstrNode::new(Inst::Undef { ty: walk_ty.clone() }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: walk_ty.clone(),
                aggregate: v(1),
                field: 0,
                value: v(0),
            })
            .with_result(v(2)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let sig = module
            .add_func_type(FuncTy { params: vec![], returns: vec![walk_ty], is_vararg: false });
        let mut function =
            Function::new(FuncId::new(0), "unit_field_seed", sig, trust_ir::BlockId::new(0));
        function.blocks.push(block);
        module.add_function(function);

        assert!(matches!(classify_undefs(&module), UndefClass::DeadSeeds));
        let normalized = substitute_dead_seeds(module);
        assert!(matches!(classify_undefs(&normalized), UndefClass::None));
        let outcome = Interpreter::with_module(&normalized)
            .execute_func(FuncId::new(0), vec![])
            .expect("the fully-overwritten unit-lane seed interprets after substitution");
        let InterpretValueKind::Aggregate(lanes) = &outcome.returns[0].kind else {
            panic!("unit-field struct return must be an aggregate");
        };
        assert_eq!(lanes.len(), 1);
    }

    /// Trust (vtable slice 11): the postures the two new zero arms must NOT move. A top-level
    /// bare `Ptr`/`Unit` `Inst::Undef` (the `()` callable-identity family, the slice-1 vtable
    /// lane) never enters the dead-seed proof — the arity match admits Tuple/Struct only — so
    /// it stays Live even though `zero_const` can now spell both types.
    #[test]
    fn bare_ptr_and_unit_undefs_stay_live() {
        for ty in [Ty::Ptr, Ty::Unit] {
            let v = ValueId::new;
            let mut block = Block::new(trust_ir::BlockId::new(0));
            block.body.push(InstrNode::new(Inst::Undef { ty: ty.clone() }).with_result(v(0)));
            block.body.push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
            let module =
                single_block_module("bare_undef", vec![], vec![ty.clone()], block);
            assert!(
                matches!(classify_undefs(&module), UndefClass::Live),
                "a bare top-level {ty} Undef must stay Live"
            );
        }
    }

    /// Trust (vtable slice 11): the C-family pin — a flat enum-model construction covers the
    /// tag and the CURRENT variant's lanes only, so an other-variant `Ptr` lane is never
    /// InsertField'd and the seed stays Live on the COVERAGE conjunct, zero spelling or not.
    /// (This is what keeps `Option<String>::None` / `Ok(())`-style rows held: unlocking them
    /// would need a value for a lane the construction deliberately never wrote.)
    #[test]
    fn uncovered_ptr_lane_keeps_flat_enum_model_seed_live() {
        use trust_ir::{FieldDef, StructDef, StructId};
        let v = ValueId::new;
        let mut module = Module::new("flat_enum_seed");
        let sid = module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Option_String".into(),
            fields: vec![
                FieldDef { name: "__tag".into(), ty: Ty::I64, offset: None },
                FieldDef { name: "__v1_0".into(), ty: Ty::Ptr, offset: None },
            ],
            size: None,
            align: None,
            repr: Default::default(),
        });
        let flat_ty = Ty::Struct(sid);
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(0) }).with_result(v(0)),
        );
        block.body.push(InstrNode::new(Inst::Undef { ty: flat_ty.clone() }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: flat_ty.clone(),
                aggregate: v(1),
                field: 0,
                value: v(0),
            })
            .with_result(v(2)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let sig = module
            .add_func_type(FuncTy { params: vec![], returns: vec![flat_ty], is_vararg: false });
        let mut function =
            Function::new(FuncId::new(0), "flat_enum_seed", sig, trust_ir::BlockId::new(0));
        function.blocks.push(block);
        module.add_function(function);
        assert!(matches!(classify_undefs(&module), UndefClass::Live));
    }

    /// Trust (vtable slice 12, rewriting the slice-11 pin): the deriving-from shape — a
    /// fully-covered seed over a struct with an `Ty::Array` lane — now SUBSTITUTES (the
    /// Array zero exists), and the divergence trap the slice-11 pin guarded is answered
    /// one gate later: the signature's (Tuple, Array) split is a `tys_agree` QUARANTINE
    /// (Err → coverage-only NotRun), NEVER the raw-equality `Ok(false)` that would have
    /// published a manufactured "signature divergence". Both halves pinned here.
    #[test]
    fn array_lane_seed_substitutes_but_sig_quarantine_holds() {
        use trust_ir::{FieldDef, StructDef, StructId};
        let v = ValueId::new;
        // Oracle side: struct { [u32 x 4] } built from a covered Array-constant lane.
        let mut oracle = Module::new("array_lane_seed");
        let elem_tid = oracle.add_type(Ty::U32);
        let sid = oracle.add_struct(StructDef {
            id: StructId::new(0),
            name: "TupleNonPathType".into(),
            fields: vec![FieldDef {
                name: "0".into(),
                ty: Ty::Array(elem_tid, 4),
                offset: None,
            }],
            size: None,
            align: None,
            repr: Default::default(),
        });
        let struct_ty = Ty::Struct(sid);
        assert!(
            zero_const(&oracle, &struct_ty).is_some(),
            "slice 12: the Array lane zero now spells"
        );
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Array(elem_tid, 4),
                value: Constant::Array(vec![
                    Constant::Int(1),
                    Constant::Int(2),
                    Constant::Int(3),
                    Constant::Int(4),
                ]),
            })
            .with_result(v(0)),
        );
        block.body.push(InstrNode::new(Inst::Undef { ty: struct_ty.clone() }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: struct_ty.clone(),
                aggregate: v(1),
                field: 0,
                value: v(0),
            })
            .with_result(v(2)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let sig = oracle
            .add_func_type(FuncTy { params: vec![], returns: vec![struct_ty], is_vararg: false });
        let mut function =
            Function::new(FuncId::new(0), "array_lane_seed", sig, trust_ir::BlockId::new(0));
        function.blocks.push(block);
        oracle.add_function(function);
        assert!(
            matches!(classify_undefs(&oracle), UndefClass::DeadSeeds),
            "the covered struct seed over an Array lane is now substitutable"
        );
        let oracle = substitute_dead_seeds(oracle);

        // THIR side: the producer's spelling of the same body — struct { (u32,u32,u32,u32) }.
        let mut thir = Module::new("thir_twin");
        let tsid = thir.add_struct(StructDef {
            id: StructId::new(0),
            name: "TupleNonPathType".into(),
            fields: vec![FieldDef {
                name: "0".into(),
                ty: Ty::Tuple(vec![Ty::U32; 4]),
                offset: None,
            }],
            size: None,
            align: None,
            repr: Default::default(),
        });
        let t_ty = Ty::Struct(tsid);
        let mut tb = Block::new(trust_ir::BlockId::new(0));
        tb.body.push(
            InstrNode::new(Inst::Const {
                ty: t_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Aggregate(vec![
                    Constant::Int(1),
                    Constant::Int(2),
                    Constant::Int(3),
                    Constant::Int(4),
                ])]),
            })
            .with_result(v(0)),
        );
        tb.body.push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        let tsig =
            thir.add_func_type(FuncTy { params: vec![], returns: vec![t_ty], is_vararg: false });
        let mut tf = Function::new(FuncId::new(0), "array_lane_seed", tsig, trust_ir::BlockId::new(0));
        tf.blocks.push(tb);
        thir.add_function(tf);

        // The trap half: the unlocked pair must HOLD at the quarantine, never mint a verdict.
        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::NotRun, "notes: {:?}", report.notes);
        assert!(
            report.notes.iter().any(|n| n.contains("signature comparability failure")
                && n.contains("array-vs-tuple spelling split")),
            "notes: {:?}",
            report.notes
        );
    }

    // ---- vtable slice 12: the array family — quarantine, dead seeds, respells, pairing ----

    /// The quarantine arm itself: (Tuple, Array) in EITHER orientation is Err — a
    /// comparability failure — never the raw-equality `Ok(false)` divergence spelling.
    #[test]
    fn tuple_vs_array_pair_is_quarantined_not_a_verdict() {
        let mut am = Module::new("a");
        let mut bm = Module::new("b");
        let ta = am.add_type(Ty::I64);
        let tb = bm.add_type(Ty::I64);
        assert!(tys_agree(&am, &bm, &Ty::Tuple(vec![Ty::I64; 3]), &Ty::Array(tb, 3), 8).is_err());
        assert!(tys_agree(&am, &bm, &Ty::Array(ta, 3), &Ty::Tuple(vec![Ty::I64; 3]), 8).is_err());
    }

    /// Trust (vtable slice 15): the producer's FIRST-CLASS scalar-element array ctor shape
    /// (`Const { Ty::Array, Constant::Array zeros }` + `Const I64 i` + `InsertElement` per
    /// element, by-value array signature) vs the oracle bridge's measured shape (`Undef
    /// [T x N]` + `InsertField`-over-Array chain) reaches AGREED end-to-end: the
    /// (Array, Array) signature pair takes the REAL resolved-element+length arm (never the
    /// slice-12 quarantine), the oracle's seed rewrites+substitutes, and the returned Array
    /// values compare elementwise bit-exact. This is the repeat-expr-in-static::FOO /
    /// const-vecs-and-slices::x walk, pinned at machinery level.
    #[test]
    fn first_class_array_ctor_pair_reaches_agreed() {
        let v = ValueId::new;
        // Tested side: the slice-15 producer ctor.
        let mut thir = Module::new("thir_first_class_array");
        let t_tid = thir.add_type(Ty::I32);
        let t_arr = Ty::Array(t_tid, 3);
        let mut tb = Block::new(trust_ir::BlockId::new(0));
        tb.body.push(
            InstrNode::new(Inst::Const {
                ty: t_arr.clone(),
                value: Constant::Array(vec![Constant::Int(0); 3]),
            })
            .with_result(v(0)),
        );
        let mut agg = v(0);
        let mut next = 1u32;
        for (i, e) in [11i128, 22, 33].iter().enumerate() {
            let ev = v(next);
            tb.body.push(
                InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(*e) })
                    .with_result(ev),
            );
            let iv = v(next + 1);
            tb.body.push(
                InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(i as i128) })
                    .with_result(iv),
            );
            let nv = v(next + 2);
            tb.body.push(
                InstrNode::new(Inst::InsertElement {
                    ty: t_arr.clone(),
                    array: agg,
                    index: iv,
                    value: ev,
                })
                .with_result(nv),
            );
            agg = nv;
            next += 3;
        }
        tb.body.push(InstrNode::new(Inst::Return { values: vec![agg] }));
        let thir =
            single_block_module_with(thir, "thir_first_class_array", vec![], vec![t_arr], tb);

        // Oracle side: the bridge's Undef seed + InsertField-over-Array chain.
        let mut oracle = Module::new("oracle_first_class_array");
        let o_tid = oracle.add_type(Ty::I32);
        let o_arr = Ty::Array(o_tid, 3);
        let mut ob = Block::new(trust_ir::BlockId::new(0));
        ob.body.push(InstrNode::new(Inst::Undef { ty: o_arr.clone() }).with_result(v(0)));
        let mut agg = v(0);
        let mut next = 1u32;
        for (i, e) in [11i128, 22, 33].iter().enumerate() {
            let ev = v(next);
            ob.body.push(
                InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(*e) })
                    .with_result(ev),
            );
            let nv = v(next + 1);
            ob.body.push(
                InstrNode::new(Inst::InsertField {
                    ty: o_arr.clone(),
                    aggregate: agg,
                    field: i as u32,
                    value: ev,
                })
                .with_result(nv),
            );
            agg = nv;
            next += 2;
        }
        ob.body.push(InstrNode::new(Inst::Return { values: vec![agg] }));
        let oracle = single_block_module_with(
            oracle,
            "oracle_first_class_array",
            vec![],
            vec![o_arr],
            ob,
        );
        let oracle = oracle_pipeline(oracle);

        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
        assert!(report.equal);
    }

    /// Trust (vtable slice 15): with the (Array, Array) signature arm now LIVE for producer
    /// output, its `Ok(false)` rows are REAL divergence channel — pin the two structural
    /// mismatches (length, element) so a respell bug surfaces as the divergence it is, and
    /// so nobody "fixes" a red sweep by widening the arm.
    #[test]
    fn first_class_array_pair_mismatches_are_real_divergences() {
        let mut am = Module::new("a");
        let mut bm = Module::new("b");
        let ta = am.add_type(Ty::I32);
        let tb = bm.add_type(Ty::I32);
        let tb64 = bm.add_type(Ty::I64);
        // Same element, same length: agree.
        assert!(matches!(tys_agree(&am, &bm, &Ty::Array(ta, 4), &Ty::Array(tb, 4), 8), Ok(true)));
        // Length mismatch: a real Ok(false), not a quarantine.
        assert!(matches!(tys_agree(&am, &bm, &Ty::Array(ta, 4), &Ty::Array(tb, 5), 8), Ok(false)));
        // Element mismatch: same.
        assert!(matches!(
            tys_agree(&am, &bm, &Ty::Array(ta, 4), &Ty::Array(tb64, 4), 8),
            Ok(false)
        ));
    }

    /// Trust (vtable slice 15): the first-class twin of the inline-slice crown test — the
    /// producer's `&[1, 2, 3]` slot is now `Alloca(Ty::Array)` storing an element-op-built
    /// value, and the THIR slot respell folds THAT chain to a `Constant::Array` initializer;
    /// the pairing then compares (Array, Array) through `tys_agree`'s real arm on both type
    /// and content. End-to-end AGREED against the unchanged oracle shape.
    #[test]
    fn first_class_array_slot_respell_reaches_agreed() {
        let v = ValueId::new;
        let mut module = Module::new("thir_inline_slice_fc");
        let elem_tid = module.add_type(Ty::U8);
        let arr_ty = Ty::Array(elem_tid, 3);
        let fat_ty = Ty::FatPtr(trust_ir::FatPtrKind::Slice(elem_tid));
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: arr_ty.clone(),
                value: Constant::Array(vec![Constant::Int(0); 3]),
            })
            .with_result(v(0)),
        );
        let mut agg = v(0);
        let mut next = 1u32;
        for (i, e) in [1i128, 2, 3].iter().enumerate() {
            let ev = v(next);
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(*e) })
                    .with_result(ev),
            );
            let iv = v(next + 1);
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(i as i128) })
                    .with_result(iv),
            );
            let nv = v(next + 2);
            block.body.push(
                InstrNode::new(Inst::InsertElement {
                    ty: arr_ty.clone(),
                    array: agg,
                    index: iv,
                    value: ev,
                })
                .with_result(nv),
            );
            agg = nv;
            next += 3;
        }
        let slot = v(next);
        block.body.push(
            InstrNode::new(Inst::Alloca { ty: arr_ty.clone(), count: None, align: None })
                .with_result(slot),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: arr_ty,
            ptr: slot,
            value: agg,
            volatile: false,
            align: None,
        }));
        let len_val = v(next + 1);
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(3) })
                .with_result(len_val),
        );
        let fat = v(next + 2);
        block.body.push(
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: fat_ty.clone(),
                metadata_ty: Ty::U64,
                data: slot,
                metadata: len_val,
            })
            .with_result(fat),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![fat] }));
        let thir =
            single_block_module_with(module, "thir_inline_slice_fc", vec![], vec![fat_ty], block);

        let respelled =
            respell_thir_array_slots_as_globals(&thir).expect("first-class slot respell fires");
        assert_eq!(respelled.globals.len(), 1);
        assert_eq!(
            respelled.globals[0].initializer,
            Some(Constant::Array(vec![Constant::Int(1), Constant::Int(2), Constant::Int(3)])),
            "the element-op chain folds to the Array-variant initializer"
        );
        let oracle = oracle_pipeline(oracle_inline_array_slice_module([1, 2, 3]));
        let report = compare_entries(&respelled, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
        assert!(report.equal);
    }

    /// The repeat lane's measured shape (repeat-expr-in-static FOO): `Undef [T x N]` +
    /// single-use `InsertElement` chain with constant indexes. Dead seed; the substituted
    /// module interprets and returns the REAL elements, not the zeros.
    #[test]
    fn array_insert_element_chain_is_dead_seed_and_interprets() {
        let v = ValueId::new;
        let mut module = Module::new("repeat_chain");
        let tid = module.add_type(Ty::I32);
        let arr_ty = Ty::Array(tid, 2);
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(7) }).with_result(v(0)),
        );
        block.body.push(InstrNode::new(Inst::Undef { ty: arr_ty.clone() }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(0) }).with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertElement {
                ty: arr_ty.clone(),
                array: v(1),
                index: v(2),
                value: v(0),
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(1) }).with_result(v(4)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertElement {
                ty: arr_ty.clone(),
                array: v(3),
                index: v(4),
                value: v(0),
            })
            .with_result(v(5)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(5)] }));
        let module =
            single_block_module_with(module, "repeat_chain", vec![], vec![arr_ty.clone()], block);
        assert!(matches!(classify_undefs(&module), UndefClass::DeadSeeds));
        let module = substitute_dead_seeds(module);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("substituted repeat chain interprets");
        match &outcome.returns[0].kind {
            trust_ir::interpret::InterpretValueKind::Array(vals) => {
                assert_eq!(vals.len(), 2);
            }
            other => panic!("expected an Array return, got {other:?}"),
        }
    }

    /// A PARTIALLY-covered InsertElement chain (or a runtime index) must stay Live.
    #[test]
    fn uncovered_or_runtime_index_array_chain_stays_live() {
        let v = ValueId::new;
        // Partial coverage: [T x 2] with only lane 0 written, final value returned.
        let mut m1 = Module::new("partial");
        let tid = m1.add_type(Ty::I32);
        let arr_ty = Ty::Array(tid, 2);
        let mut b1 = Block::new(trust_ir::BlockId::new(0));
        b1.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(7) }).with_result(v(0)),
        );
        b1.body.push(InstrNode::new(Inst::Undef { ty: arr_ty.clone() }).with_result(v(1)));
        b1.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(0) }).with_result(v(2)),
        );
        b1.body.push(
            InstrNode::new(Inst::InsertElement {
                ty: arr_ty.clone(),
                array: v(1),
                index: v(2),
                value: v(0),
            })
            .with_result(v(3)),
        );
        b1.body.push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        let m1 = single_block_module_with(m1, "partial", vec![], vec![arr_ty.clone()], b1);
        assert!(matches!(classify_undefs(&m1), UndefClass::Live));

        // Runtime index: the index is a PARAM, not a const — unresolvable, Live.
        let mut m2 = Module::new("runtime_idx");
        let tid2 = m2.add_type(Ty::I32);
        let arr_ty2 = Ty::Array(tid2, 1);
        let mut b2 = Block::new(trust_ir::BlockId::new(0));
        b2.params.push((v(0), Ty::I64));
        b2.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(7) }).with_result(v(1)),
        );
        b2.body.push(InstrNode::new(Inst::Undef { ty: arr_ty2.clone() }).with_result(v(2)));
        b2.body.push(
            InstrNode::new(Inst::InsertElement {
                ty: arr_ty2.clone(),
                array: v(2),
                index: v(0),
                value: v(1),
            })
            .with_result(v(3)),
        );
        b2.body.push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        let m2 = single_block_module_with(m2, "runtime_idx", vec![Ty::I64], vec![arr_ty2], b2);
        assert!(matches!(classify_undefs(&m2), UndefClass::Live));
    }

    /// `[T; 0]`: the seed is the type's sole inhabitant — dead outright, any use position.
    #[test]
    fn zero_len_array_undef_is_sole_inhabitant_dead_seed() {
        let v = ValueId::new;
        let mut module = Module::new("zero_len");
        let tid = module.add_type(Ty::Bool);
        let arr_ty = Ty::Array(tid, 0);
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Undef { ty: arr_ty.clone() }).with_result(v(0)));
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        let module = single_block_module_with(module, "zero_len", vec![], vec![], block);
        assert!(matches!(classify_undefs(&module), UndefClass::DeadSeeds));
        let module = substitute_dead_seeds(module);
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("substituted zero-length seed interprets");
    }

    /// The literal lane's InsertField-over-Array chain rewrites to the interpreter-native
    /// InsertElement form (the pinned interpreter's `eval_insert_field` has no Array arm).
    #[test]
    fn array_insert_fields_rewrite_to_insert_elements_and_interpret() {
        let v = ValueId::new;
        let mut module = Module::new("literal_chain");
        let tid = module.add_type(Ty::U8);
        let arr_ty = Ty::Array(tid, 2);
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(5) }).with_result(v(0)),
        );
        block.body.push(InstrNode::new(Inst::Undef { ty: arr_ty.clone() }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: arr_ty.clone(),
                aggregate: v(1),
                field: 0,
                value: v(0),
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: arr_ty.clone(),
                aggregate: v(2),
                field: 1,
                value: v(0),
            })
            .with_result(v(3)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        let mut module =
            single_block_module_with(module, "literal_chain", vec![], vec![arr_ty.clone()], block);
        rewrite_array_insert_fields(&mut module);
        assert!(
            !module.functions[0].blocks[0]
                .body
                .iter()
                .any(|n| matches!(&n.inst, Inst::InsertField { ty: Ty::Array(..), .. })),
            "every Array InsertField must be rewritten"
        );
        assert!(matches!(classify_undefs(&module), UndefClass::DeadSeeds));
        let module = substitute_dead_seeds(module);
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("rewritten literal chain interprets");
    }

    /// Helper: finish a module whose types/structs were pre-registered.
    fn single_block_module_with(
        mut module: Module,
        name: &str,
        params: Vec<Ty>,
        returns: Vec<Ty>,
        block: Block,
    ) -> Module {
        let sig = module.add_func_type(FuncTy { params, returns, is_vararg: false });
        let mut function = Function::new(FuncId::new(0), name, sig, trust_ir::BlockId::new(0));
        function.blocks.push(block);
        module.add_function(function);
        module
    }

    /// The measured THIR shape of `const BAR: &[u8] = &[1, 2, 3]`
    /// (`lower_inline_array_to_slice`, dumped on const-vecs-and-slices::y /
    /// references::BAR): Tuple-typed once-stored escaping slot feeding PtrFromParts data.
    fn thir_inline_array_slice_module(elems: [i128; 3]) -> Module {
        let v = ValueId::new;
        let mut module = Module::new("thir_inline_slice");
        let elem_tid = module.add_type(Ty::U8);
        let tuple_ty = Ty::Tuple(vec![Ty::U8; 3]);
        let fat_ty = Ty::FatPtr(trust_ir::FatPtrKind::Slice(elem_tid));
        let mut block = Block::new(trust_ir::BlockId::new(0));
        for (i, e) in elems.iter().enumerate() {
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(*e) })
                    .with_result(v(i as u32)),
            );
        }
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: tuple_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(0); 3]),
            })
            .with_result(v(3)),
        );
        for i in 0..3u32 {
            block.body.push(
                InstrNode::new(Inst::InsertField {
                    ty: tuple_ty.clone(),
                    aggregate: v(3 + i),
                    field: i,
                    value: v(i),
                })
                .with_result(v(4 + i)),
            );
        }
        block.body.push(
            InstrNode::new(Inst::Alloca { ty: tuple_ty.clone(), count: None, align: None })
                .with_result(v(7)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: tuple_ty,
            ptr: v(7),
            value: v(6),
            volatile: false,
            align: None,
        }));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(3) })
                .with_result(v(8)),
        );
        block.body.push(
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: fat_ty.clone(),
                metadata_ty: Ty::U64,
                data: v(7),
                metadata: v(8),
            })
            .with_result(v(9)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(9)] }));
        single_block_module_with(module, "thir_inline_slice", vec![], vec![fat_ty], block)
    }

    /// The measured ORACLE shape of the same body (hoisted alloca, Undef Array seed,
    /// InsertField chain, store, reborrow chain, PtrFromParts).
    fn oracle_inline_array_slice_module(elems: [i128; 3]) -> Module {
        let v = ValueId::new;
        let mut module = Module::new("oracle_inline_slice");
        let fat_tid = module.add_type(Ty::U8);
        let arr_tid = module.add_type(Ty::U8);
        let arr_ty = Ty::Array(arr_tid, 3);
        let fat_ty = Ty::FatPtr(trust_ir::FatPtrKind::Slice(fat_tid));
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Alloca { ty: arr_ty.clone(), count: None, align: None })
                .with_result(v(0)),
        );
        for (i, e) in elems.iter().enumerate() {
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(*e) })
                    .with_result(v(1 + i as u32)),
            );
        }
        block.body.push(InstrNode::new(Inst::Undef { ty: arr_ty.clone() }).with_result(v(4)));
        for i in 0..3u32 {
            block.body.push(
                InstrNode::new(Inst::InsertField {
                    ty: arr_ty.clone(),
                    aggregate: v(4 + i),
                    field: i,
                    value: v(1 + i),
                })
                .with_result(v(5 + i)),
            );
        }
        block.body.push(InstrNode::new(Inst::Store {
            ty: arr_ty,
            ptr: v(0),
            value: v(7),
            volatile: false,
            align: None,
        }));
        block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(8)));
        block.body.push(InstrNode::new(Inst::Borrow { ptr: v(8) }).with_result(v(9)));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(3) })
                .with_result(v(10)),
        );
        block.body.push(
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: fat_ty.clone(),
                metadata_ty: Ty::U64,
                data: v(9),
                metadata: v(10),
            })
            .with_result(v(11)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(11)] }));
        single_block_module_with(module, "oracle_inline_slice", vec![], vec![fat_ty], block)
    }

    /// Run the oracle half of the pipeline exactly as `compare` does (rewrite →
    /// classify → substitute → slice-6 respell).
    fn oracle_pipeline(mut oracle: Module) -> Module {
        rewrite_array_insert_fields(&mut oracle);
        assert!(
            matches!(classify_undefs(&oracle), UndefClass::DeadSeeds),
            "oracle array seed must be substitutable"
        );
        let mut oracle = substitute_dead_seeds(oracle);
        respell_promoted_slots_as_globals(&mut oracle);
        oracle
    }

    /// The crown test: the measured `&[1,2,3]` fat-slice pair, both respells, end-to-end
    /// AGREED — data lane raw-Ptr agreement over the paired cross-spelled globals,
    /// metadata lane bit-exact.
    #[test]
    fn measured_inline_array_slice_pair_reaches_agreed() {
        let thir = thir_inline_array_slice_module([1, 2, 3]);
        let respelled =
            respell_thir_array_slots_as_globals(&thir).expect("THIR slot respell fires");
        assert_eq!(respelled.globals.len(), 1);
        assert_eq!(respelled.globals[0].name, "__trust_promoted_0");
        assert_eq!(
            respelled.globals[0].initializer,
            Some(Constant::Aggregate(vec![
                Constant::Int(1),
                Constant::Int(2),
                Constant::Int(3)
            ]))
        );
        let oracle = oracle_pipeline(oracle_inline_array_slice_module([1, 2, 3]));
        assert_eq!(oracle.globals.len(), 1, "slice-6 respell minted the oracle twin");
        assert_eq!(
            oracle.globals[0].initializer,
            Some(Constant::Array(vec![
                Constant::Int(1),
                Constant::Int(2),
                Constant::Int(3)
            ]))
        );

        let report = compare_entries(&respelled, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
        assert!(report.equal);
    }

    /// The pairing's content conjunct is what makes the raw-Ptr agreement mean "the same
    /// immutable object": a CONTENT-mismatched pair still raw-agrees on the returned fat
    /// pointer (both sides return their own global's address at offset 0), so admission
    /// must refuse and the body must HOLD at the tail gate — never Agreed.
    #[test]
    fn content_mismatched_array_pair_holds_at_the_tail_gate() {
        let thir = thir_inline_array_slice_module([1, 2, 3]);
        let respelled =
            respell_thir_array_slots_as_globals(&thir).expect("THIR slot respell fires");
        let oracle = oracle_pipeline(oracle_inline_array_slice_module([1, 2, 9]));

        let report = compare_entries(&respelled, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::NotRun, "notes: {:?}", report.notes);
        assert!(
            report.notes.iter().any(|n| n.contains("module-global state/provenance")),
            "the hold must come from the unadmitted-global tail gate: {:?}",
            report.notes
        );
    }

    /// The THIR respell's scope and refusals: scalar slots (the wave-CB/issue-67710
    /// lanes), mixed tuples, second stores, pre-store escapes, and metadata-position
    /// uses all leave the module untouched.
    #[test]
    fn thir_array_respell_scope_and_refusals() {
        // Scalar slot: excluded by the ty scope.
        let scalar = once_stored_escaping_slot_module();
        assert!(respell_thir_array_slots_as_globals(&scalar).is_none());

        // Mixed (non-homogeneous) tuple slot: excluded.
        let v = ValueId::new;
        let mixed_ty = Ty::Tuple(vec![Ty::U8, Ty::U64]);
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: mixed_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
            })
            .with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Alloca { ty: mixed_ty.clone(), count: None, align: None })
                .with_result(v(1)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: mixed_ty,
            ptr: v(1),
            value: v(0),
            volatile: false,
            align: None,
        }));
        block.body.push(InstrNode::new(Inst::Borrow { ptr: v(1) }).with_result(v(2)));
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let mixed = single_block_module("mixed", vec![], vec![Ty::Ptr], block);
        assert!(respell_thir_array_slots_as_globals(&mixed).is_none());

        // Second store into the slot: refused (wrong final memory hazard).
        let mut second = thir_inline_array_slice_module([1, 2, 3]);
        let extra_store = {
            let f = &second.functions[0].blocks[0];
            let Inst::Store { ty, ptr, value, .. } = &f.body[8].inst else {
                panic!("expected the store at position 8");
            };
            Inst::Store {
                ty: ty.clone(),
                ptr: *ptr,
                value: *value,
                volatile: false,
                align: None,
            }
        };
        let ret = second.functions[0].blocks[0].body.len() - 1;
        second.functions[0].blocks[0].body.insert(ret, InstrNode::new(extra_store));
        assert!(respell_thir_array_slots_as_globals(&second).is_none());

        // Escape BEFORE the store: refused (a pre-store alias could read uninit).
        let mut pre = thir_inline_array_slice_module([1, 2, 3]);
        let body = &mut pre.functions[0].blocks[0].body;
        // Move the PtrFromParts (position 10) to just after the alloca (position 8),
        // i.e. before the store.
        let node = body.remove(10);
        body.insert(8, node);
        assert!(respell_thir_array_slots_as_globals(&pre).is_none());

        // Slot pointer in the METADATA position: refused (address in a length lane).
        let mut meta = thir_inline_array_slice_module([1, 2, 3]);
        {
            let body = &mut meta.functions[0].blocks[0].body;
            let Inst::PtrFromParts { data, metadata, .. } = &mut body[10].inst else {
                panic!("expected ptr_from_parts at position 10");
            };
            std::mem::swap(data, metadata);
        }
        assert!(respell_thir_array_slots_as_globals(&meta).is_none());
    }

    /// The cross-spelling pairing arms, directly: content (Aggregate vs Array,
    /// elementwise bit-exact) and type (homogeneous Tuple vs Array, length + element).
    #[test]
    fn cross_spelling_pairing_arms() {
        let ints =
            |v: &[i128]| v.iter().map(|i| Constant::Int(*i)).collect::<Vec<_>>();
        assert!(promoted_init_content_eq(
            &Constant::Aggregate(ints(&[1, 2])),
            &Constant::Array(ints(&[1, 2]))
        ));
        assert!(!promoted_init_content_eq(
            &Constant::Aggregate(ints(&[1, 2])),
            &Constant::Array(ints(&[1, 3]))
        ));
        assert!(!promoted_init_content_eq(
            &Constant::Aggregate(ints(&[1])),
            &Constant::Array(ints(&[1, 1]))
        ));

        let mut am = Module::new("a");
        let mut bm = Module::new("b");
        let _ = am.add_type(Ty::U8);
        let tb = bm.add_type(Ty::U8);
        assert!(promoted_pair_tys_agree(&am, &bm, &Ty::Tuple(vec![Ty::U8; 2]), &Ty::Array(tb, 2)));
        // Length mismatch refuses.
        assert!(!promoted_pair_tys_agree(&am, &bm, &Ty::Tuple(vec![Ty::U8; 3]), &Ty::Array(tb, 2)));
        // Element mismatch refuses.
        assert!(!promoted_pair_tys_agree(
            &am,
            &bm,
            &Ty::Tuple(vec![Ty::U16; 2]),
            &Ty::Array(tb, 2)
        ));
        // Empty tuple refuses (no zero-elem cross pairing).
        assert!(!promoted_pair_tys_agree(&am, &bm, &Ty::Tuple(vec![]), &Ty::Array(tb, 0)));
    }

    /// The zero-length pair (issue-40231-2 TEXT_U16: `&[] as &[u16]`): both sides spell
    /// `Ty::Array(_, 0)` + `Constant::Array([])` — SAME spelling, plain pairing. This
    /// test decides the pre-registered N=0 uncertainty: if zero-length globals do not
    /// materialize in the pinned interpreter, this fails and the respells must exclude
    /// len 0.
    #[test]
    fn zero_len_array_slice_pair_reaches_agreed() {
        let v = ValueId::new;
        // THIR: const Array([]) + alloca + store + ptr_from_parts + ret (measured).
        let mut thir = Module::new("thir_zero");
        let t_tid = thir.add_type(Ty::U16);
        let t_arr = Ty::Array(t_tid, 0);
        let t_fat = Ty::FatPtr(trust_ir::FatPtrKind::Slice(t_tid));
        let mut tb = Block::new(trust_ir::BlockId::new(0));
        tb.body.push(
            InstrNode::new(Inst::Const { ty: t_arr.clone(), value: Constant::Array(vec![]) })
                .with_result(v(0)),
        );
        tb.body.push(
            InstrNode::new(Inst::Alloca { ty: t_arr.clone(), count: None, align: None })
                .with_result(v(1)),
        );
        tb.body.push(InstrNode::new(Inst::Store {
            ty: t_arr,
            ptr: v(1),
            value: v(0),
            volatile: false,
            align: None,
        }));
        tb.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(0) })
                .with_result(v(2)),
        );
        tb.body.push(
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: t_fat.clone(),
                metadata_ty: Ty::U64,
                data: v(1),
                metadata: v(2),
            })
            .with_result(v(3)),
        );
        tb.body.push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        let thir = single_block_module_with(thir, "thir_zero", vec![], vec![t_fat], tb);
        let thir =
            respell_thir_array_slots_as_globals(&thir).expect("N=0 THIR respell fires");

        // Oracle: alloca + Undef [u16 x 0] + store + borrow + borrow + ptr_from_parts.
        let mut oracle = Module::new("oracle_zero");
        let o_fat_tid = oracle.add_type(Ty::U16);
        let o_arr_tid = oracle.add_type(Ty::U16);
        let o_arr = Ty::Array(o_arr_tid, 0);
        let o_fat = Ty::FatPtr(trust_ir::FatPtrKind::Slice(o_fat_tid));
        let mut ob = Block::new(trust_ir::BlockId::new(0));
        ob.body.push(
            InstrNode::new(Inst::Alloca { ty: o_arr.clone(), count: None, align: None })
                .with_result(v(0)),
        );
        ob.body.push(InstrNode::new(Inst::Undef { ty: o_arr.clone() }).with_result(v(1)));
        ob.body.push(InstrNode::new(Inst::Store {
            ty: o_arr,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        ob.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(2)));
        ob.body.push(InstrNode::new(Inst::Borrow { ptr: v(2) }).with_result(v(3)));
        ob.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(0) })
                .with_result(v(4)),
        );
        ob.body.push(
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: o_fat.clone(),
                metadata_ty: Ty::U64,
                data: v(3),
                metadata: v(4),
            })
            .with_result(v(5)),
        );
        ob.body.push(InstrNode::new(Inst::Return { values: vec![v(5)] }));
        let oracle = single_block_module_with(oracle, "oracle_zero", vec![], vec![o_fat], ob);
        let oracle = oracle_pipeline(oracle);
        assert_eq!(oracle.globals.len(), 1, "N=0 oracle respell fires");

        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
    }

    /// Trust (vtable slice 10): the producer twin of a symbolic const-param body — ONE
    /// value-less `__trust_constparam_*` carrier, `GlobalAddr`+`Load` at the read, computation
    /// at the faithful `Usize` spelling.
    fn const_column_thir_module(compute_div: bool) -> Module {
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: trust_ir::value::GlobalId::new(0) })
                .with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Load { ty: Ty::Usize, ptr: v(0), volatile: false, align: None })
                .with_result(v(1)),
        );
        let ret = if compute_div {
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::Usize, value: Constant::Int(2) })
                    .with_result(v(2)),
            );
            block.body.push(
                InstrNode::new(Inst::BinOp {
                    op: trust_ir::BinOp::UDiv,
                    ty: Ty::Usize,
                    lhs: v(1),
                    rhs: v(2),
                })
                .with_result(v(3)),
            );
            v(3)
        } else {
            v(1)
        };
        block.body.push(InstrNode::new(Inst::Return { values: vec![ret] }));
        let mut m = single_block_module("const_column_thir", vec![], vec![Ty::Usize], block);
        m.globals.push(trust_ir::Global {
            name: "__trust_constparam_0__f::N".to_string(),
            ty: Ty::Usize,
            mutable: false,
            initializer: None,
            linkage: trust_ir::Linkage::External,
            tls: None,
            align: None,
        });
        m
    }

    /// The oracle twin: a width-collapsed `U64` live `Undef` at the read (the bridge's
    /// contextless `ConstParam` spelling), faithful-dest `Usize` consumers — the measured
    /// `N / 2` shape `BinOp { ty: Usize, lhs: Undef(U64), .. }` whose demanded-type respell
    /// this lane exists to execute.
    fn const_column_oracle_module(compute_div: bool) -> Module {
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Undef { ty: Ty::U64 }).with_result(v(0)));
        let ret = if compute_div {
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::Usize, value: Constant::Int(2) })
                    .with_result(v(1)),
            );
            block.body.push(
                InstrNode::new(Inst::BinOp {
                    op: trust_ir::BinOp::UDiv,
                    ty: Ty::Usize,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
            );
            v(2)
        } else {
            v(0)
        };
        block.body.push(InstrNode::new(Inst::Return { values: vec![ret] }));
        single_block_module("const_column_oracle", vec![], vec![Ty::Usize], block)
    }

    #[test]
    fn const_param_column_agrees_across_the_width_collapsed_spelling_split() {
        // `N / 2` end-to-end: producer Usize carrier vs oracle U64 Undef under Usize-stamped
        // consumers. Five u64 boundary+mid samples, one execution each, every one agreeing.
        let thir = const_column_thir_module(true);
        let oracle = const_column_oracle_module(true);
        let rep = const_param_column_compare(&thir, &oracle)
            .expect("single-carrier div body must admit the column");
        assert_eq!(rep.mode, DiffMode::Agreed);
        assert!(rep.equal);
        assert_eq!(rep.samples_checked, sample_values(&Ty::Usize).len());
        assert!(rep.notes.last().unwrap().contains("const-param/assoc-const column usize"));
    }

    #[test]
    fn const_param_column_return_demand_respells_the_declared_width() {
        // `{ N }` shape: the Undef's only consumer is Return, whose demanded type is the
        // faithful `Usize` signature slot — substituted there, never at the declared `U64`.
        let thir = const_column_thir_module(false);
        let oracle = const_column_oracle_module(false);
        let rep = const_param_column_compare(&thir, &oracle)
            .expect("single-carrier passthrough body must admit the column");
        assert_eq!(rep.mode, DiffMode::Agreed);
        assert_eq!(rep.samples_checked, sample_values(&Ty::Usize).len());
    }

    #[test]
    fn const_param_column_surfaces_a_real_divergence_with_the_column_value() {
        // Producer returns N; oracle computes N / 2 — a genuine semantic split the sampled
        // column must PUBLISH (first witness: N = 1), never absorb as a skip.
        let thir = const_column_thir_module(false);
        let oracle = const_column_oracle_module(true);
        let rep = const_param_column_compare(&thir, &oracle)
            .expect("shape-admissible pair must run, and must diverge");
        assert_eq!(rep.mode, DiffMode::MirOracle);
        assert!(!rep.equal);
        let note = rep.notes.last().unwrap();
        assert!(note.contains("DIVERGENCE"), "note: {note}");
        assert!(note.contains("[const-param column usize = 1]"), "note: {note}");
    }

    #[test]
    fn const_param_column_refuses_two_distinct_carriers() {
        // Two distinct parameters: the identity-free binding has no unique answer — refuse.
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: trust_ir::value::GlobalId::new(0) })
                .with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Load { ty: Ty::Usize, ptr: v(0), volatile: false, align: None })
                .with_result(v(1)),
        );
        block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: trust_ir::value::GlobalId::new(1) })
                .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::Load { ty: Ty::Usize, ptr: v(2), volatile: false, align: None })
                .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::Usize,
                lhs: v(1),
                rhs: v(3),
            })
            .with_result(v(4)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(4)] }));
        let mut thir = single_block_module("two_carriers", vec![], vec![Ty::Usize], block);
        for name in ["__trust_constparam_0__f::N", "__trust_constparam_1__f::M"] {
            thir.globals.push(trust_ir::Global {
                name: name.to_string(),
                ty: Ty::Usize,
                mutable: false,
                initializer: None,
                linkage: trust_ir::Linkage::External,
                tls: None,
                align: None,
            });
        }
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Undef { ty: Ty::U64 }).with_result(v(0)));
        block.body.push(InstrNode::new(Inst::Undef { ty: Ty::U64 }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::U64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let oracle = single_block_module("two_undefs", vec![], vec![Ty::U64], block);
        assert!(const_param_column_compare(&thir, &oracle).is_none());
    }

    #[test]
    fn const_param_column_refuses_an_occurrence_count_mismatch() {
        // One producer read vs two oracle live Undefs: the misalignment tripwire — a foreign
        // Undef bound to the column would assert a wrong value model, so the pair refuses.
        let thir = const_column_thir_module(false);
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Undef { ty: Ty::U64 }).with_result(v(0)));
        block.body.push(InstrNode::new(Inst::Undef { ty: Ty::U64 }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::U64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let oracle = single_block_module("two_undefs", vec![], vec![Ty::U64], block);
        assert!(const_param_column_compare(&thir, &oracle).is_none());
    }

    #[test]
    fn const_param_column_bool_realizes_bool_constants_both_sides() {
        // A bool const-generic (`bool_consumer<const B: bool>() -> bool { B }`): the column
        // realizes `Constant::Bool` — never an integer at Bool — and samples both truth values.
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: trust_ir::value::GlobalId::new(0) })
                .with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Load { ty: Ty::Bool, ptr: v(0), volatile: false, align: None })
                .with_result(v(1)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        let mut thir = single_block_module("bool_column_thir", vec![], vec![Ty::Bool], block);
        thir.globals.push(trust_ir::Global {
            name: "__trust_constparam_0__f::B".to_string(),
            ty: Ty::Bool,
            mutable: false,
            initializer: None,
            linkage: trust_ir::Linkage::External,
            tls: None,
            align: None,
        });
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Undef { ty: Ty::Bool }).with_result(v(0)));
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        let oracle = single_block_module("bool_column_oracle", vec![], vec![Ty::Bool], block);
        let rep = const_param_column_compare(&thir, &oracle)
            .expect("bool column must admit");
        assert_eq!(rep.mode, DiffMode::Agreed);
        assert_eq!(rep.samples_checked, 2);
    }

    #[test]
    fn const_param_column_dead_read_substitutes_at_the_declared_ty() {
        // `let _ = Self::HASH_LEN;` — the read is discarded (zero consumers). The oracle Undef
        // keeps its declared type; the pair agrees on the unit return for every sample.
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: trust_ir::value::GlobalId::new(0) })
                .with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Load { ty: Ty::Usize, ptr: v(0), volatile: false, align: None })
                .with_result(v(1)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        let mut thir = single_block_module("dead_read_thir", vec![], vec![], block);
        thir.globals.push(trust_ir::Global {
            name: "__trust_symconst_0__Foo::HASH_LEN".to_string(),
            ty: Ty::Usize,
            mutable: false,
            initializer: None,
            linkage: trust_ir::Linkage::External,
            tls: None,
            align: None,
        });
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Undef { ty: Ty::U64 }).with_result(v(0)));
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        let oracle = single_block_module("dead_read_oracle", vec![], vec![], block);
        let rep = const_param_column_compare(&thir, &oracle)
            .expect("dead parametric read must still sample (unit agreement per value)");
        assert_eq!(rep.mode, DiffMode::Agreed);
        assert_eq!(rep.samples_checked, sample_values(&Ty::Usize).len());
    }

    #[test]
    fn const_param_column_refuses_conflicting_consumer_demands() {
        // One Undef feeding two consumers stamped at DIFFERENT widths: no single substitution
        // type exists — fail closed (never a mistyped execution, never a manufactured verdict).
        let thir = const_column_thir_module(false);
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Undef { ty: Ty::U64 }).with_result(v(0)));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(1) })
                .with_result(v(1)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::U32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        let oracle = single_block_module("conflicting_demands", vec![], vec![Ty::Usize], block);
        assert!(const_param_column_compare(&thir, &oracle).is_none());
    }

    /// The MEASURED oracle spelling of `const A: *const i32 = &raw const *&2;`
    /// (const-address-of::A, dumped via the slice-6 probe): hoisted alloca, const, an
    /// operand-materialization copy, store, shared borrow, pointer copy, ret.
    fn once_stored_escaping_slot_module() -> Module {
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Alloca { ty: Ty::I32, count: None, align: None })
                .with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(2) })
                .with_result(v(1)),
        );
        block.body.push(
            InstrNode::new(Inst::Copy { ty: Ty::I32, operand: v(1) }).with_result(v(2)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(2),
            volatile: false,
            align: None,
        }));
        block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(3)));
        block.body.push(
            InstrNode::new(Inst::Copy { ty: Ty::Ptr, operand: v(3) }).with_result(v(4)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(4)] }));
        single_block_module("promoted_slot", vec![], vec![Ty::Ptr], block)
    }

    #[test]
    fn respell_rewrites_the_exact_once_stored_escaping_slot_and_preserves_interpretation() {
        let before = once_stored_escaping_slot_module();
        let mut after = before.clone();
        assert_eq!(respell_promoted_slots_as_globals(&mut after), 1);

        // The mint mirrors the THIR wave-16 shape: named, initializer-bearing, immutable.
        assert_eq!(after.globals.len(), 1);
        let g = &after.globals[0];
        assert_eq!(g.name, "__trust_promoted_0");
        assert_eq!(g.ty, Ty::I32);
        assert!(!g.mutable);
        assert_eq!(g.initializer, Some(Constant::Int(2)));
        assert!(matches!(g.linkage, trust_ir::Linkage::Internal));

        // The Alloca becomes the GlobalAddr IN PLACE under the SAME result id (the
        // allocation-order argument), the Store is deleted, the Borrow stays a Borrow,
        // and the (now dead, pure) Const/Copy chain is left alone.
        let body = &after.functions[0].blocks[0].body;
        assert_eq!(body.len(), 6);
        assert!(matches!(body[0].inst, Inst::GlobalAddr { .. }));
        assert_eq!(body[0].results, vec![ValueId::new(0)]);
        assert!(matches!(body[1].inst, Inst::Const { .. }));
        assert!(matches!(body[2].inst, Inst::Copy { .. }));
        assert!(matches!(body[3].inst, Inst::Borrow { .. }));
        assert!(matches!(body[4].inst, Inst::Copy { .. }));
        assert!(matches!(body[5].inst, Inst::Return { .. }));

        // Interpretation equivalence, INCLUDING the raw pointer identity the sampled
        // comparison raw-compares: the global's first-touch allocation mints exactly
        // the allocation id the replaced Alloca used to.
        let before_out = Interpreter::with_module(&before)
            .execute_func(FuncId::new(0), vec![])
            .expect("the slot spelling interprets");
        let after_out = Interpreter::with_module(&after)
            .execute_func(FuncId::new(0), vec![])
            .expect("the respelled global spelling interprets");
        assert_eq!(before_out.returns, after_out.returns);
    }

    #[test]
    fn respell_refuses_reassigned_raw_escaping_and_runtime_valued_slots() {
        // (a) A second Store after the escape — borrow-use-issue-46875's `let mut x = 5;
        // let y = &x; x = 7`: an initializer-5 global would be a WRONG final memory.
        let reassigned = {
            let v = ValueId::new;
            let mut block = Block::new(trust_ir::BlockId::new(0));
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(5) })
                    .with_result(v(1)),
            );
            block.body.push(
                InstrNode::new(Inst::Alloca { ty: Ty::I32, count: None, align: None })
                    .with_result(v(0)),
            );
            block.body.push(InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            }));
            block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(2)));
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(7) })
                    .with_result(v(3)),
            );
            block.body.push(InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(3),
                volatile: false,
                align: None,
            }));
            block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
            single_block_module("reassigned_slot", vec![], vec![Ty::Ptr], block)
        };
        // (b) The `&raw const` lane: the slot pointer escapes through `Inst::Copy`, a
        // non-Borrow use (const-address-of::D/E/F, const_ptr).
        let raw_escape = {
            let v = ValueId::new;
            let mut block = Block::new(trust_ir::BlockId::new(0));
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(2) })
                    .with_result(v(1)),
            );
            block.body.push(
                InstrNode::new(Inst::Alloca { ty: Ty::I32, count: None, align: None })
                    .with_result(v(0)),
            );
            block.body.push(InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            }));
            block.body.push(
                InstrNode::new(Inst::Copy { ty: Ty::Ptr, operand: v(0) }).with_result(v(2)),
            );
            block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
            single_block_module("raw_escape_slot", vec![], vec![Ty::Ptr], block)
        };
        // (c) A runtime-valued store — locals-in-const-fn's `bar(mut i)`: the stored
        // value is the PARAM, not a foldable constant.
        let runtime_valued = {
            let v = ValueId::new;
            let mut block = Block::new(trust_ir::BlockId::new(0));
            block = block.with_param(v(1), Ty::I32);
            block.body.push(
                InstrNode::new(Inst::Alloca { ty: Ty::I32, count: None, align: None })
                    .with_result(v(0)),
            );
            block.body.push(InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            }));
            block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(2)));
            block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
            single_block_module("runtime_valued_slot", vec![Ty::I32], vec![Ty::Ptr], block)
        };

        for module in [reassigned, raw_escape, runtime_valued] {
            let mut touched = module.clone();
            assert_eq!(respell_promoted_slots_as_globals(&mut touched), 0);
            assert_eq!(touched, module, "a refused candidate must leave the module untouched");
        }
    }

    #[test]
    fn respell_folds_the_substituted_aggregate_build_chain() {
        // regions-dependent-let-ref's `_3 = Foo(const 3); _2 = &_3` after
        // `substitute_dead_seeds`: zeroed Const seed + InsertField, stored then borrowed.
        let v = ValueId::new;
        let tuple_ty = Ty::Tuple(vec![Ty::I64]);
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: tuple_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(0)]),
            })
            .with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(3) })
                .with_result(v(1)),
        );
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: tuple_ty.clone(),
                aggregate: v(0),
                field: 0,
                value: v(1),
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::Alloca { ty: tuple_ty.clone(), count: None, align: None })
                .with_result(v(3)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: tuple_ty.clone(),
            ptr: v(3),
            value: v(2),
            volatile: false,
            align: None,
        }));
        block.body.push(InstrNode::new(Inst::Borrow { ptr: v(3) }).with_result(v(4)));
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(4)] }));
        let mut module =
            single_block_module("aggregate_promoted_slot", vec![], vec![Ty::Ptr], block);

        assert_eq!(respell_promoted_slots_as_globals(&mut module), 1);
        let g = &module.globals[0];
        assert_eq!(g.name, "__trust_promoted_0");
        assert_eq!(g.ty, tuple_ty);
        assert_eq!(g.initializer, Some(Constant::Aggregate(vec![Constant::Int(3)])));
        // The pure build chain stays; the Alloca became the GlobalAddr, the Store went.
        let body = &module.functions[0].blocks[0].body;
        assert_eq!(body.len(), 6);
        assert!(matches!(body[3].inst, Inst::GlobalAddr { .. }));
        assert!(matches!(body[4].inst, Inst::Borrow { .. }));
    }

    #[test]
    fn enum_zero_const_uses_effective_discriminant_and_variant_zero_payload_lanes() {
        let mut module = Module::new("enum_zero_const");
        let enum_id = module.add_enum_def(
            trust_ir::EnumDef::new(
                trust_ir::EnumId::new(0),
                "Sparse",
                vec![
                    trust_ir::EnumVariant {
                        name: "Payload".into(),
                        fields: vec![Ty::I32, Ty::Bool],
                        field_names: Vec::new(),
                    },
                    trust_ir::EnumVariant {
                        name: "Empty".into(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                ],
            )
            .with_discriminants(vec![Some(11), None])
            .with_repr(trust_ir::EnumTagRepr::U8),
        );
        assert_eq!(
            zero_const(&module, &Ty::Enum(enum_id)),
            Some(Constant::Aggregate(vec![
                Constant::Int(11),
                Constant::Int(0),
                Constant::Bool(false),
            ]))
        );

        let pointer_enum = module.add_enum_def(
            trust_ir::EnumDef::new(
                trust_ir::EnumId::new(1),
                "PointerPayload",
                vec![trust_ir::EnumVariant {
                    name: "Only".into(),
                    fields: vec![Ty::Ptr],
                    field_names: Vec::new(),
                }],
            )
            .with_discriminants(vec![Some(5)]),
        );
        // Trust (vtable slice 11): the Ptr variant lane now spells the wave-PS null pointer.
        // Sound in every reachable context: the enum arm of `zero_const` is reached only for an
        // enum RECURSIVELY inside a Tuple/Struct seed (a top-level `Ty::Enum` Undef never
        // passes `undef_is_dead_seed`'s arity match), and that whole lane is overwritten by an
        // InsertField before any use — the same witness as the top-level Ptr arm.
        assert_eq!(
            zero_const(&module, &Ty::Enum(pointer_enum)),
            Some(Constant::Aggregate(vec![Constant::Int(5), Constant::Int(0)]))
        );
    }

    #[test]
    fn bool_rewrites_are_select_equivalent_for_every_input() {
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0))
            .with_param(v(0), Ty::Bool)
            .with_param(v(1), Ty::Bool);
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
                .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::ICmp {
                op: trust_ir::ICmpOp::Eq,
                ty: Ty::Bool,
                lhs: v(0),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::UnOp { op: trust_ir::UnOp::Not, ty: Ty::Bool, operand: v(1) })
                .with_result(v(4)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::And,
                ty: Ty::Bool,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(5)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Or,
                ty: Ty::Bool,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(6)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(3), v(4), v(5), v(6)] }));
        let mut module = single_block_module(
            "bool_rewrites",
            vec![Ty::Bool, Ty::Bool],
            vec![Ty::Bool, Ty::Bool, Ty::Bool, Ty::Bool],
            block,
        );

        rewrite_bool_not_icmp(&mut module);
        let body = &module.functions[0].blocks[0].body;
        assert_eq!(body.iter().filter(|node| matches!(&node.inst, Inst::Select { .. })).count(), 4);
        assert!(!body.iter().any(|node| matches!(
            &node.inst,
            Inst::ICmp { ty: Ty::Bool, .. }
                | Inst::UnOp { ty: Ty::Bool, .. }
                | Inst::BinOp { ty: Ty::Bool, .. }
        )));

        for (lhs, rhs) in [(false, false), (false, true), (true, false), (true, true)] {
            let outcome = Interpreter::with_module(&module)
                .execute_func(
                    FuncId::new(0),
                    vec![InterpretValue::bool(lhs), InterpretValue::bool(rhs)],
                )
                .expect("rewritten boolean operations should interpret");
            let got = outcome
                .returns
                .iter()
                .map(|value| value.as_bool().expect("a bool result"))
                .collect::<Vec<_>>();
            assert_eq!(got, vec![!lhs, !rhs, lhs && rhs, lhs || rhs]);
        }
    }

    // Fix #3: when BOTH sides error with DIFFERENT codes, a THIR-side lowering
    // defect (e.g. `MissingBlock` from malformed IR) paired with a mere oracle
    // infra limit (e.g. `OutOfFuel`) is a GENUINE THIR defect — it must be
    // reported, not swept into the `NotRun` coverage-only skip.
    #[test]
    fn errerr_thir_defect_masked_by_oracle_limit_is_reported() {
        // THIR malformed-IR defect vs oracle out-of-fuel: divergence.
        assert!(
            errerr_thir_defect_divergence(C::MissingBlock, C::OutOfFuel),
            "THIR `MissingBlock` (lowering defect) + oracle `OutOfFuel` (infra limit) \
             must be reported as a THIR divergence, not hidden as a coverage-only skip"
        );
        // A type error masked by an oracle Unsupported* code is likewise a defect.
        assert!(errerr_thir_defect_divergence(C::TypeError, C::UnsupportedInstruction));
        assert!(errerr_thir_defect_divergence(C::SignatureMismatch, C::OutOfMemory));
    }

    #[test]
    fn errerr_no_false_divergence_when_thir_is_not_at_fault() {
        // Oracle defect + THIR infra limit: NOT a THIR divergence (the THIR side
        // did not produce malformed IR; it merely ran out of an infra budget).
        assert!(!errerr_thir_defect_divergence(C::OutOfFuel, C::MissingBlock));
        // Both infra limits: coverage-only, never a THIR verdict.
        assert!(!errerr_thir_defect_divergence(C::OutOfFuel, C::OutOfFuel));
        assert!(!errerr_thir_defect_divergence(C::OutOfMemory, C::UnsupportedCall));
        // Both genuine defects (same kind class): the equal-code/same-trap path or
        // a both-defect pair is not a one-sided THIR fault here. With the THIR a
        // defect AND the oracle ALSO a defect, the masking condition is false.
        assert!(!errerr_thir_defect_divergence(C::MissingBlock, C::TypeError));
    }

    #[test]
    fn is_thir_defect_classifies_resource_limits_as_non_defects() {
        // Resource/incapacity codes are NOT defects (coverage-only).
        assert!(!is_thir_defect(C::OutOfFuel));
        assert!(!is_thir_defect(C::OutOfMemory));
        assert!(!is_thir_defect(C::UnsupportedInstruction));
        assert!(!is_thir_defect(C::MissingFunction));
        assert!(!is_thir_defect(C::InvalidFunctionPointer));
        // Genuine malformedness / type errors ARE defects.
        assert!(is_thir_defect(C::MissingBlock));
        assert!(is_thir_defect(C::TypeError));
        assert!(is_thir_defect(C::SignatureMismatch));
        assert!(is_thir_defect(C::MalformedInstruction));
        assert!(is_thir_defect(C::MissingValue));
    }

    // Trust (wave-31, NESTED-place assign): the emission contract of the Assign arm's chained
    // lowering, executed on the PINNED trust-ir interpreter (the same one both differential
    // sides run on). The module below is INSTRUCTION-FOR-INSTRUCTION the sequence
    // `lower_expr(Assign)` emits for `(*p).inner.gen1 = 7` on
    //   struct Inner { flag: bool, gen1: u64, lazy: u64 }
    //   struct Outer { inner: Inner, other: u64 }
    // (chain = [(inner,0),(gen1,1)]; the `&mut` param ptr is replaced by a self-contained
    // `Alloca` slot so the body is interpretable without opaque-param machinery):
    //   Load(root) / ExtractField(inner) / InsertField(gen1, v) / InsertField(inner, ·) /
    //   Store(root').
    // Asserts the VALUE-LEVEL surgery semantics the wave relies on: the leaf lane changes,
    // and the SIBLINGS AT BOTH NESTING LEVELS (`inner.flag`, `inner.lazy`, `other`)
    // round-trip unchanged through the whole-struct RMW.
    #[test]
    fn nested_assign_chain_updates_leaf_and_preserves_siblings() {
        use trust_ir::{
            Block, BlockId, Constant, FieldDef, Function as IrFunction, InstrNode, Module,
            StructDef, StructId, Ty as IrTy,
        };

        let mut m = Module::new("wave31_nested_assign_shape");
        let inner_sid = m.add_struct(StructDef {
            id: StructId::new(0),
            name: "Inner".into(),
            fields: vec![
                FieldDef { name: "flag".into(), ty: IrTy::Bool, offset: None },
                FieldDef { name: "gen1".into(), ty: IrTy::U64, offset: None },
                FieldDef { name: "lazy".into(), ty: IrTy::U64, offset: None },
            ],
            size: None,
            align: None,
            repr: Default::default(),
        });
        let outer_sid = m.add_struct(StructDef {
            id: StructId::new(1),
            name: "Outer".into(),
            fields: vec![
                FieldDef { name: "inner".into(), ty: IrTy::Struct(inner_sid), offset: None },
                FieldDef { name: "other".into(), ty: IrTy::U64, offset: None },
            ],
            size: None,
            align: None,
            repr: Default::default(),
        });
        let inner_ty = IrTy::Struct(inner_sid);
        let outer_ty = IrTy::Struct(outer_sid);

        let fty = m.add_func_type(FuncTy {
            params: vec![],
            returns: vec![IrTy::Bool, IrTy::U64, IrTy::U64, IrTy::U64],
            is_vararg: false,
        });
        let v = ValueId::new;
        let mut blk = Block::new(BlockId::new(0));
        // Slot + initial value: Outer { inner: Inner { flag: true, gen1: 41, lazy: 5 }, other: 9 }.
        blk.body.push(
            InstrNode::new(Inst::Alloca { ty: outer_ty.clone(), count: None, align: None })
                .with_result(v(0)),
        );
        blk.body.push(
            InstrNode::new(Inst::Const {
                ty: outer_ty.clone(),
                value: Constant::Aggregate(vec![
                    Constant::Aggregate(vec![
                        Constant::Bool(true),
                        Constant::Int(41),
                        Constant::Int(5),
                    ]),
                    Constant::Int(9),
                ]),
            })
            .with_result(v(1)),
        );
        blk.body.push(InstrNode::new(Inst::Store {
            ty: outer_ty.clone(),
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        // rhs value, lowered before the RMW (the arm's operand order).
        blk.body.push(
            InstrNode::new(Inst::Const { ty: IrTy::U64, value: Constant::Int(7) })
                .with_result(v(2)),
        );
        // — the wave-31 chain, verbatim —
        blk.body.push(
            InstrNode::new(Inst::Load {
                ty: outer_ty.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
        blk.body.push(
            InstrNode::new(Inst::ExtractField { ty: inner_ty.clone(), aggregate: v(3), field: 0 })
                .with_result(v(4)),
        );
        blk.body.push(
            InstrNode::new(Inst::InsertField {
                ty: inner_ty.clone(),
                aggregate: v(4),
                field: 1,
                value: v(2),
            })
            .with_result(v(5)),
        );
        blk.body.push(
            InstrNode::new(Inst::InsertField {
                ty: outer_ty.clone(),
                aggregate: v(3),
                field: 0,
                value: v(5),
            })
            .with_result(v(6)),
        );
        blk.body.push(InstrNode::new(Inst::Store {
            ty: outer_ty.clone(),
            ptr: v(0),
            value: v(6),
            volatile: false,
            align: None,
        }));
        // Read back every leaf (both levels) and return them.
        blk.body.push(
            InstrNode::new(Inst::Load {
                ty: outer_ty.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(7)),
        );
        blk.body.push(
            InstrNode::new(Inst::ExtractField { ty: inner_ty, aggregate: v(7), field: 0 })
                .with_result(v(8)),
        );
        blk.body.push(
            InstrNode::new(Inst::ExtractField { ty: IrTy::Bool, aggregate: v(8), field: 0 })
                .with_result(v(9)),
        );
        blk.body.push(
            InstrNode::new(Inst::ExtractField { ty: IrTy::U64, aggregate: v(8), field: 1 })
                .with_result(v(10)),
        );
        blk.body.push(
            InstrNode::new(Inst::ExtractField { ty: IrTy::U64, aggregate: v(8), field: 2 })
                .with_result(v(11)),
        );
        blk.body.push(
            InstrNode::new(Inst::ExtractField { ty: IrTy::U64, aggregate: v(7), field: 1 })
                .with_result(v(12)),
        );
        blk.body.push(InstrNode::new(Inst::Return { values: vec![v(9), v(10), v(11), v(12)] }));
        let mut f = IrFunction::new(FuncId::new(0), "wave31_probe", fty, BlockId::new(0));
        f.blocks.push(blk);
        m.add_function(f);

        let outcome = Interpreter::with_module(&m)
            .execute_func(FuncId::new(0), vec![])
            .expect("wave-31 nested-assign chain must interpret cleanly");
        let expected = vec![
            InterpretValue::bool(true),               // inner.flag — inner sibling
            InterpretValue::int(Ty::U64, 7).unwrap(), // inner.gen1 — the assigned leaf
            InterpretValue::int(Ty::U64, 5).unwrap(), // inner.lazy — inner sibling
            InterpretValue::int(Ty::U64, 9).unwrap(), // other      — root sibling
        ];
        assert_eq!(outcome.returns.len(), expected.len(), "return arity");
        for (i, (got, want)) in outcome.returns.iter().zip(&expected).enumerate() {
            assert_eq!(
                got.kind, want.kind,
                "return {i}: nested RMW must update ONLY the assigned lane (got {:?})",
                outcome.returns
            );
        }
    }

    // Trust (B9-A): `compare_entries` is the linked-callee comparison the crate-seam differential
    // runs. Build a two-function module `entry(x:i64) -> i64 { callee(x) }` and drive
    // `compare_entries` against an oracle that is (a) IDENTICAL and (b) has a DIVERGENT callee. The
    // entry `FuncId` is passed explicitly (the seam interprets from a non-zero `entry_slot` on the
    // bundle side) — here FuncId(0) both sides for the simplest shape.
    fn two_fn_module(name: &str, callee_returns_arg: bool) -> Module {
        use trust_ir::{Block, BlockId, Constant, Function as IrFunction, InstrNode, Ty as IrTy};
        let v = ValueId::new;
        let mut m = Module::new(name.to_string());
        // Shared signature: (i64) -> i64.
        let sig = m.add_func_type(FuncTy {
            params: vec![IrTy::I64],
            returns: vec![IrTy::I64],
            is_vararg: false,
        });

        // entry (FuncId 0): entry block takes the i64 param, calls callee, returns the result.
        let mut eb = Block::new(BlockId::new(0)).with_param(v(0), IrTy::I64);
        eb.body.push(
            InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![v(0)] })
                .with_result(v(1)),
        );
        eb.body.push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        let mut entry = IrFunction::new(FuncId::new(0), "entry", sig, BlockId::new(0));
        entry.blocks.push(eb);
        m.add_function(entry);

        // callee (FuncId 1): identity (`return y`) or constant-0 (`return 0`), ignoring the arg.
        let mut cb = Block::new(BlockId::new(0)).with_param(v(0), IrTy::I64);
        let ret = if callee_returns_arg {
            v(0)
        } else {
            cb.body.push(
                InstrNode::new(Inst::Const { ty: IrTy::I64, value: Constant::Int(0) })
                    .with_result(v(1)),
            );
            v(1)
        };
        cb.body.push(InstrNode::new(Inst::Return { values: vec![ret] }));
        let mut callee = IrFunction::new(FuncId::new(1), "callee", sig, BlockId::new(0));
        callee.blocks.push(cb);
        m.add_function(callee);
        m
    }

    /// Canonical `()` call shape: both signatures and returns have zero values, and the call node
    /// likewise declares no SSA result. This is the shape emitted directly from THIR.
    fn unit_call_module(name: &str) -> Module {
        use trust_ir::{Block, BlockId, Function as IrFunction, InstrNode};

        let mut m = Module::new(name.to_string());
        let sig =
            m.add_func_type(FuncTy { params: Vec::new(), returns: Vec::new(), is_vararg: false });

        let mut entry_block = Block::new(BlockId::new(0));
        entry_block
            .body
            .push(InstrNode::new(Inst::Call { callee: FuncId::new(1), args: Vec::new() }));
        entry_block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
        let mut entry = IrFunction::new(FuncId::new(0), "entry", sig, BlockId::new(0));
        entry.blocks.push(entry_block);
        m.add_function(entry);

        let mut callee_block = Block::new(BlockId::new(0));
        callee_block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
        let mut callee = IrFunction::new(FuncId::new(1), "callee", sig, BlockId::new(0));
        callee.blocks.push(callee_block);
        m.add_function(callee);
        m
    }

    fn add_mutable_i64_global(module: &mut Module, symbol: &str, initializer: i128) {
        module.globals.push(trust_ir::Global {
            name: symbol.to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(initializer)),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
        });
    }

    fn append_global_store(block: &mut Block, stored: i128) {
        let v = ValueId::new;
        block
            .body
            .push(InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(stored) })
                .with_result(v(1)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
    }

    /// `fn entry() -> i64 { GLOBAL = stored; returned }`.
    fn global_store_module(name: &str, stored: i128, returned: i128) -> Module {
        let mut module = Module::new(name.to_string());
        add_mutable_i64_global(&mut module, "GLOBAL", 0);
        let sig = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut block = Block::new(trust_ir::BlockId::new(0));
        append_global_store(&mut block, stored);
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(returned) })
                .with_result(ValueId::new(2)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }));
        let mut entry = Function::new(FuncId::new(0), "entry", sig, trust_ir::BlockId::new(0));
        entry.blocks.push(block);
        module.add_function(entry);
        module
    }

    /// `entry() -> i64 { effect(); returned }`, where `effect` writes a module global.
    fn effectful_callee_module(name: &str, stored: i128, returned: i128) -> Module {
        let mut module = Module::new(name.to_string());
        add_mutable_i64_global(&mut module, "GLOBAL", 0);
        let entry_sig = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let unit_sig = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });

        let mut entry_block = Block::new(trust_ir::BlockId::new(0));
        entry_block
            .body
            .push(InstrNode::new(Inst::Call { callee: FuncId::new(1), args: Vec::new() }));
        entry_block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(returned) })
                .with_result(ValueId::new(0)),
        );
        entry_block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        let mut entry =
            Function::new(FuncId::new(0), "entry", entry_sig, trust_ir::BlockId::new(0));
        entry.blocks.push(entry_block);
        module.add_function(entry);

        let mut callee_block = Block::new(trust_ir::BlockId::new(0));
        append_global_store(&mut callee_block, stored);
        callee_block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
        let mut callee =
            Function::new(FuncId::new(1), "effect", unit_sig, trust_ir::BlockId::new(0));
        callee.blocks.push(callee_block);
        module.add_function(callee);
        module
    }

    fn returned_global_pointer_module(name: &str, symbol: &str, initializer: i128) -> Module {
        let mut module = Module::new(name.to_string());
        add_mutable_i64_global(&mut module, symbol, initializer);
        let sig = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::Ptr],
            is_vararg: false,
        });
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) })
                .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        let mut entry = Function::new(FuncId::new(0), "entry", sig, trust_ir::BlockId::new(0));
        entry.blocks.push(block);
        module.add_function(entry);
        module
    }

    fn returned_fndef_module(name: &str, target_return: i128) -> Module {
        let mut module = Module::new(name.to_string());
        let target_sig = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry_sig = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::Func(target_sig)],
            is_vararg: false,
        });

        let mut entry_block = Block::new(trust_ir::BlockId::new(0));
        entry_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Func(target_sig),
                value: Constant::FnDef(FuncId::new(1)),
            })
            .with_result(ValueId::new(0)),
        );
        entry_block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        let mut entry =
            Function::new(FuncId::new(0), "entry", entry_sig, trust_ir::BlockId::new(0));
        entry.blocks.push(entry_block);
        module.add_function(entry);

        let mut target_block = Block::new(trust_ir::BlockId::new(0));
        target_block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(target_return) })
                .with_result(ValueId::new(0)),
        );
        target_block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        let mut target =
            Function::new(FuncId::new(1), "target", target_sig, trust_ir::BlockId::new(0));
        target.blocks.push(target_block);
        module.add_function(target);
        module
    }

    /// The first bool sample returns an equal scalar after an uncomparable callable; the second
    /// returns a side-specific scalar. This pins mismatch precedence both across return positions
    /// and across sampled executions.
    fn sampled_callable_and_scalar_module(name: &str, true_scalar: i128) -> Module {
        let mut module = Module::new(name.to_string());
        let target_sig = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry_sig = module.add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![Ty::Func(target_sig), Ty::I64],
            is_vararg: false,
        });
        let v = ValueId::new;
        let mut entry_block = Block::new(trust_ir::BlockId::new(0)).with_param(v(0), Ty::Bool);
        entry_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Func(target_sig),
                value: Constant::FnDef(FuncId::new(1)),
            })
            .with_result(v(1)),
        );
        entry_block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(0) }).with_result(v(2)),
        );
        entry_block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(true_scalar) })
                .with_result(v(3)),
        );
        entry_block.body.push(
            InstrNode::new(Inst::Select {
                ty: Ty::I64,
                cond: v(0),
                then_val: v(3),
                else_val: v(2),
            })
            .with_result(v(4)),
        );
        entry_block.body.push(InstrNode::new(Inst::Return { values: vec![v(1), v(4)] }));
        let mut entry =
            Function::new(FuncId::new(0), "entry", entry_sig, trust_ir::BlockId::new(0));
        entry.blocks.push(entry_block);
        module.add_function(entry);

        let mut target_block = Block::new(trust_ir::BlockId::new(0));
        target_block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(0) }).with_result(v(0)),
        );
        target_block.body.push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        let mut target =
            Function::new(FuncId::new(1), "target", target_sig, trust_ir::BlockId::new(0));
        target.blocks.push(target_block);
        module.add_function(target);
        module
    }

    /// The entry is pure; a second, uncalled function writes a global.
    fn pure_entry_with_unrelated_effect(name: &str, stored: i128) -> Module {
        let mut module = Module::new(name.to_string());
        add_mutable_i64_global(&mut module, "UNRELATED", 0);
        let entry_sig = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let unit_sig = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });

        let mut entry_block = Block::new(trust_ir::BlockId::new(0));
        entry_block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(7) })
                .with_result(ValueId::new(0)),
        );
        entry_block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        let mut entry =
            Function::new(FuncId::new(0), "entry", entry_sig, trust_ir::BlockId::new(0));
        entry.blocks.push(entry_block);
        module.add_function(entry);

        let mut unrelated_block = Block::new(trust_ir::BlockId::new(0));
        append_global_store(&mut unrelated_block, stored);
        unrelated_block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
        let mut unrelated =
            Function::new(FuncId::new(1), "unrelated_effect", unit_sig, trust_ir::BlockId::new(0));
        unrelated.blocks.push(unrelated_block);
        module.add_function(unrelated);
        module
    }

    #[test]
    fn compare_entries_different_global_stores_same_return_fail_closed() {
        let thir = global_store_module("effect_thir", 11, 7);
        let oracle = global_store_module("effect_oracle", 29, 7);

        // Pin the hole: TrustIR executes both writes but discards final global memory, so its
        // public outcomes are indistinguishable even though the observable post-states differ.
        let thir_out = Interpreter::with_module(&thir)
            .execute_func(FuncId::new(0), vec![])
            .expect("THIR effect witness interprets");
        let oracle_out = Interpreter::with_module(&oracle)
            .execute_func(FuncId::new(0), vec![])
            .expect("oracle effect witness interprets");
        assert_eq!(thir_out.returns, oracle_out.returns);

        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(rep.mode, DiffMode::NotRun, "uncompared global writes: {:?}", rep.notes);
        assert!(!rep.equal);
        assert_eq!(rep.samples_checked, 1, "the tail gate runs after the sampled comparison");
        assert!(
            rep.notes
                .iter()
                .any(|note| note.contains("observable-effect comparison is not modeled")),
            "the skip must name the missing observation: {:?}",
            rep.notes
        );
    }

    #[test]
    fn compare_entries_effectful_linked_callee_same_return_fail_closed() {
        let thir = effectful_callee_module("callee_effect_thir", 11, 7);
        let oracle = effectful_callee_module("callee_effect_oracle", 29, 7);
        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));

        assert_eq!(
            rep.mode,
            DiffMode::NotRun,
            "an effectful direct callee must be scanned recursively: {:?}",
            rep.notes
        );
        assert!(!rep.equal);
        assert!(
            rep.notes.iter().any(|note| note.contains("`effect`")),
            "the reachable callee should be identified: {:?}",
            rep.notes
        );
    }

    #[test]
    fn compare_entries_returned_global_pointer_identity_is_not_compared() {
        let thir = returned_global_pointer_module("pointer_thir", "THIR_GLOBAL", 1);
        let oracle = returned_global_pointer_module("pointer_oracle", "ORACLE_GLOBAL", 2);

        // Per-execution allocation ids both start at the same synthetic value, so raw pointer
        // equality cannot establish cross-module symbol/provenance identity.
        let thir_out = Interpreter::with_module(&thir)
            .execute_func(FuncId::new(0), vec![])
            .expect("THIR pointer witness interprets");
        let oracle_out = Interpreter::with_module(&oracle)
            .execute_func(FuncId::new(0), vec![])
            .expect("oracle pointer witness interprets");
        assert_eq!(thir_out.returns, oracle_out.returns, "synthetic ids expose the old blind spot");

        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(rep.mode, DiffMode::NotRun, "global provenance is unmodeled: {:?}", rep.notes);
        assert!(!rep.equal);
    }

    #[test]
    fn compare_entries_returned_callable_identity_is_not_raw_compared() {
        let thir = returned_fndef_module("callable_thir", 11);
        let oracle = returned_fndef_module("callable_oracle", 29);

        // Both interpreters allocate the target at FuncId(1), but those equal counters say
        // nothing about the independently-built target bodies (which deliberately differ here).
        let thir_out = Interpreter::with_module(&thir)
            .execute_func(FuncId::new(0), vec![])
            .expect("THIR callable witness interprets");
        let oracle_out = Interpreter::with_module(&oracle)
            .execute_func(FuncId::new(0), vec![])
            .expect("oracle callable witness interprets");
        assert_eq!(thir_out.returns, oracle_out.returns, "raw FuncIds expose the old blind spot");

        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(rep.mode, DiffMode::NotRun, "callable identity is unmodeled: {:?}", rep.notes);
        assert!(!rep.equal);
        assert!(
            rep.notes.iter().any(|note| note.contains("callable/frame identity")),
            "the comparability failure should identify the unsupported identity: {:?}",
            rep.notes
        );
    }

    #[test]
    fn callable_gap_does_not_mask_later_return_or_sample_divergence() {
        let thir = sampled_callable_and_scalar_module("callable_sample_thir", 11);
        let oracle = sampled_callable_and_scalar_module("callable_sample_oracle", 29);
        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));

        assert_eq!(
            rep.mode,
            DiffMode::MirOracle,
            "the concrete scalar mismatch must outrank the earlier callable gap: {:?}",
            rep.notes
        );
        assert!(!rep.equal);
        assert_eq!(rep.samples_checked, 2, "bool=false gap must not stop bool=true sampling");
        assert!(
            rep.notes.iter().any(|note| note.contains("DIVERGENCE on input [1]")),
            "the second-sample scalar mismatch should be reported: {:?}",
            rep.notes
        );
    }

    #[test]
    fn nested_callable_constants_and_frame_values_fail_closed() {
        let callable = Constant::Aggregate(vec![Constant::Array(vec![Constant::Closure {
            func: FuncId::new(0),
            captures: Vec::new(),
        }])]);
        assert!(constant_materializes_uncomparable_identity(&callable));

        let module = Module::new("frame_identity");
        let frame = InterpretValue { ty: Ty::Ptr, kind: InterpretValueKind::Frame(0) };
        assert!(
            value_agree(&module, &module, &frame, &frame, TY_CMP_DEPTH).is_err(),
            "equal synthetic frame counters must never establish cross-execution identity"
        );
    }

    #[test]
    fn compare_entries_unrelated_effectful_function_does_not_poison_pure_entry() {
        let thir = pure_entry_with_unrelated_effect("unrelated_thir", 11);
        let oracle = pure_entry_with_unrelated_effect("unrelated_oracle", 29);
        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));

        assert_eq!(
            rep.mode,
            DiffMode::Agreed,
            "only the entry's direct-call closure is relevant: {:?}",
            rep.notes
        );
        assert!(rep.equal);
    }

    #[test]
    fn compare_entries_effectful_return_divergence_remains_mir_oracle() {
        let thir = global_store_module("effect_divergence_thir", 11, 7);
        let oracle = global_store_module("effect_divergence_oracle", 29, 8);
        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));

        assert_eq!(
            rep.mode,
            DiffMode::MirOracle,
            "the observable-effect check is a green-tail gate, never a mismatch downgrade: {:?}",
            rep.notes
        );
        assert!(!rep.equal);
    }

    #[test]
    fn compare_entries_two_fn_identity_agrees() {
        let thir = two_fn_module("seam_thir", true);
        let oracle = two_fn_module("seam_oracle", true);
        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(
            rep.mode,
            DiffMode::Agreed,
            "identical linked callees must AGREE on every sampled input (note: {:?})",
            rep.notes
        );
        assert!(rep.samples_checked > 0, "at least one i64 sample must be interpreted");
    }

    /// Splice a DEAD ADT-interior byte walk (`%c = const i64 <off>; %p = gep inbounds i8, %base,
    /// %c`) into `func`'s entry block, immediately before its terminator. Dead on purpose: the
    /// result is never used, so nothing about the module's VALUES changes and the only thing the
    /// gate can be reacting to is the SHAPE.
    /// Append an UNREACHABLE block carrying one byte walk (`%c = const i64 <off>;
    /// %p = gep [inbounds] <pointee>, %base, %c`) to `func`.
    ///
    /// Unreachable on purpose, and it is the point of the construction: the recognizer is
    /// SYNTACTIC, so the gate must fire on an offset that is merely COMMITTED TO, and the
    /// discrimination controls below must stay green without the interpreter ever executing the
    /// spliced instruction (a `GEP` off an `i64` block param would trap, and a trap would make
    /// every control pass for the wrong reason).
    fn splice_byte_walk(m: &mut Module, func: usize, off: Option<i128>, pointee: Ty, inbounds: bool) {
        let f = &mut m.functions[func];
        let next = 900 + func as u32 * 10;
        let (kc, kp) = (ValueId::new(next), ValueId::new(next + 1));
        let mut blk = Block::new(trust_ir::BlockId::new(90 + func as u32));
        let idx = match off {
            Some(k) => {
                blk.body.push(
                    InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(k) })
                        .with_result(kc),
                );
                kc
            }
            // No literal: index the walk by the entry block's own param instead.
            None => ValueId::new(0),
        };
        blk.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: pointee,
                base: ValueId::new(0),
                indices: vec![idx],
                inbounds,
            })
            .with_result(kp),
        );
        blk.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        f.blocks.push(blk);
    }

    /// **THE RED PROOF OF THE ADT-INTERIOR BYTE-ARITHMETIC GATE (wave-DA).**
    ///
    /// The control is `compare_entries_two_fn_identity_agrees`: an identical pair that AGREES on
    /// every sampled input. Splice one dead `gep inbounds i8, +4` into the THIR side and the
    /// verdict must become `NotRun` — because the interpreter would be laying that ADT out by its
    /// own rule and executing an offset it did not derive. Without the gate this pair still
    /// reports `Agreed`, which is the wrong verdict the gate exists to refuse.
    #[test]
    fn adt_interior_byte_walk_turns_an_otherwise_green_pair_into_not_run() {
        // ACCEPT CONTROL first — the pair must be green BEFORE the perturbation, or the refusal
        // below proves nothing.
        let clean_thir = two_fn_module("da_ctrl_thir", true);
        let clean_oracle = two_fn_module("da_ctrl_oracle", true);
        let green = compare_entries(&clean_thir, FuncId::new(0), &clean_oracle, FuncId::new(0));
        assert_eq!(green.mode, DiffMode::Agreed, "control must be green: {:?}", green.notes);
        assert!(green.samples_checked > 0);

        let mut thir = two_fn_module("da_thir", true);
        splice_byte_walk(&mut thir, 0, Some(4), Ty::I8, true);
        let oracle = two_fn_module("da_oracle", true);
        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(
            rep.mode,
            DiffMode::NotRun,
            "an ADT-interior literal byte walk must refuse the interpreter channel: {:?}",
            rep.notes
        );
        assert!(!rep.equal, "a coverage-only skip is never `equal`");
        assert_eq!(rep.samples_checked, 0, "the gate must refuse BEFORE any sample is run");
        assert!(
            rep.notes.iter().any(|n| n.contains("ADT-interior literal byte arithmetic")
                && n.contains("THIR side")
                && n.contains("+4")),
            "the note must name the side and the offset: {:?}",
            rep.notes
        );
    }

    /// The gate is SIDE-SYMMETRIC. The oracle does not emit this shape today, but the hazard is a
    /// property of the shape, not of which front-end produced it — so an oracle carrying it is
    /// refused with the oracle named.
    #[test]
    fn adt_interior_byte_walk_is_refused_on_the_oracle_side_too() {
        let thir = two_fn_module("da_o_thir", true);
        let mut oracle = two_fn_module("da_o_oracle", true);
        splice_byte_walk(&mut oracle, 0, Some(16), Ty::U8, true);
        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(rep.mode, DiffMode::NotRun, "{:?}", rep.notes);
        assert!(
            rep.notes.iter().any(|n| n.contains("MIR oracle side") && n.contains("+16")),
            "the oracle side must be named: {:?}",
            rep.notes
        );
    }

    /// It catches the walk in a NON-ENTRY function that the entry CAN REACH — the seam links
    /// callees, and a reachable callee that walks an ADT interior is executed by the same
    /// interpreter. `two_fn_module`'s entry calls `callee`, so the walk spliced into `callee` is
    /// inside the closure.
    #[test]
    fn adt_interior_byte_walk_is_caught_in_a_linked_callee() {
        let mut thir = two_fn_module("da_callee_thir", true);
        splice_byte_walk(&mut thir, 1, Some(8), Ty::I8, true);
        let oracle = two_fn_module("da_callee_oracle", true);
        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(rep.mode, DiffMode::NotRun, "{:?}", rep.notes);
        assert!(rep.notes.iter().any(|n| n.contains("callee")), "{:?}", rep.notes);
    }

    /// **The discrimination controls.** A gate that refused every `GEP` would pass the RED proof
    /// above and cost the programme every element-arithmetic body for nothing. These are the three
    /// shapes the producer emits that are NOT ADT-interior byte arithmetic, and each must stay
    /// green: the slice index (typed `pointee_ty`), the string-literal byte walk
    /// (`inbounds: false`), and any byte GEP whose displacement is not a literal.
    #[test]
    fn element_arithmetic_and_non_literal_displacements_stay_green() {
        // (a) typed pointee — the slice-index shape.
        let mut typed = two_fn_module("da_typed_thir", true);
        splice_byte_walk(&mut typed, 0, Some(4), Ty::I64, true);
        let rep = compare_entries(
            &typed,
            FuncId::new(0),
            &two_fn_module("da_typed_oracle", true),
            FuncId::new(0),
        );
        assert_eq!(rep.mode, DiffMode::Agreed, "a TYPED pointee is element arithmetic: {:?}", rep.notes);

        // (b) `inbounds: false` — the string-literal byte walk.
        let mut oob = two_fn_module("da_oob_thir", true);
        splice_byte_walk(&mut oob, 0, Some(4), Ty::U8, false);
        let rep = compare_entries(
            &oob,
            FuncId::new(0),
            &two_fn_module("da_oob_oracle", true),
            FuncId::new(0),
        );
        assert_eq!(
            rep.mode,
            DiffMode::Agreed,
            "a non-`inbounds` byte walk is the literal-bytes shape, not an ADT interior: {:?}",
            rep.notes
        );

        // (c) a byte GEP whose index is a block PARAM, not a literal — no rustc offset is being
        //     committed to, so there is nothing for the two sides to disagree about.
        let mut dyn_idx = two_fn_module("da_dyn_thir", true);
        splice_byte_walk(&mut dyn_idx, 0, None, Ty::I8, true);
        let rep = compare_entries(
            &dyn_idx,
            FuncId::new(0),
            &two_fn_module("da_dyn_oracle", true),
            FuncId::new(0),
        );
        assert_eq!(
            rep.mode,
            DiffMode::Agreed,
            "a non-literal displacement is not a committed rustc offset: {:?}",
            rep.notes
        );
    }

    /// Splice `%k = const{ty} off ; %p = gep{pointee,inbounds} base=%0 indices ; ret %0` into
    /// `func`, where `indices` is built from `positions` — `None` = the entry block's own param,
    /// `Some(())` = the spliced constant. Lets each wave-DZ recognizer limit be perturbed one at
    /// a time (the spelling, the index position) off ONE shared shape.
    fn splice_byte_walk_at(
        m: &mut Module,
        func: usize,
        const_ty: Ty,
        off: i128,
        positions: &[Option<()>],
    ) {
        let f = &mut m.functions[func];
        let next = 940 + func as u32 * 10;
        let (kc, kp) = (ValueId::new(next), ValueId::new(next + 1));
        let mut blk = Block::new(trust_ir::BlockId::new(94 + func as u32));
        blk.body.push(
            InstrNode::new(Inst::Const { ty: const_ty, value: Constant::Int(off) }).with_result(kc),
        );
        let indices =
            positions.iter().map(|p| if p.is_some() { kc } else { ValueId::new(0) }).collect();
        blk.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base: ValueId::new(0),
                indices,
                inbounds: true,
            })
            .with_result(kp),
        );
        blk.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        f.blocks.push(blk);
    }

    /// **wave-DZ RED PROOF — a `Const { U32 }` respelling of the same byte offset.**
    ///
    /// wave-DA's table matched `I64 | U64 | Isize | Usize` only, so this exact module was
    /// ADMITTED at that HEAD (demonstrated by a passing adversarial test during the wave-DA
    /// review, and recorded in its merge message). A byte displacement is a byte displacement in
    /// every integer width.
    #[test]
    fn a_u32_spelled_displacement_is_refused() {
        let mut m = two_fn_module("dz_u32", true);
        splice_byte_walk_at(&mut m, 0, Ty::U32, 12, &[Some(())]);
        assert!(
            first_adt_interior_byte_arithmetic(&m, FuncId::new(0))
                .is_some_and(|why| why.contains("+12")),
            "a U32-spelled rustc byte offset is still a committed rustc byte offset",
        );
        // Every other integer spelling too — the point is the CLASS, not four more names.
        for ty in [Ty::I8, Ty::U8, Ty::I16, Ty::U16, Ty::I32, Ty::I128, Ty::U128] {
            let mut m = two_fn_module("dz_widths", true);
            splice_byte_walk_at(&mut m, 0, ty.clone(), 12, &[Some(())]);
            assert!(
                first_adt_interior_byte_arithmetic(&m, FuncId::new(0)).is_some(),
                "a {ty}-spelled displacement must be refused",
            );
        }
        // ACCEPT CONTROL: a NON-integer const in index position commits to no byte offset.
        let mut boolish = two_fn_module("dz_bool", true);
        splice_byte_walk_at(&mut boolish, 0, Ty::Bool, 1, &[Some(())]);
        assert_eq!(first_adt_interior_byte_arithmetic(&boolish, FuncId::new(0)), None);
    }

    /// **wave-DZ RED PROOF — the literal in index position 1.** wave-DA read `indices.first()`,
    /// so a flat-byte GEP carrying its displacement anywhere else walked past. The producer emits
    /// one index at all three sites, so this costs nothing today and removes the limit.
    #[test]
    fn a_literal_in_a_later_index_position_is_refused() {
        let mut m = two_fn_module("dz_pos1", true);
        // index 0 = the entry block's own (uncommitted) param; index 1 = the literal.
        splice_byte_walk_at(&mut m, 0, Ty::I64, 12, &[None, Some(())]);
        assert!(
            first_adt_interior_byte_arithmetic(&m, FuncId::new(0))
                .is_some_and(|why| why.contains("+12") && why.contains("index 1")),
            "a committed displacement is committed wherever it sits in the index list",
        );
    }

    /// A caller that materializes the displacement and hands it to a callee which GEPs by its
    /// OWN parameter — `func 0: %k = const 24 ; call callee(%0, %k)`, `callee: gep i8 %0[%1]`.
    fn call_boundary_module(name: &str, pass_literal: bool) -> Module {
        use trust_ir::{BlockId, Function as IrFunction};
        let v = ValueId::new;
        let mut m = Module::new(name.to_string());
        let sig = m.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });

        let mut eb = Block::new(BlockId::new(0)).with_param(v(0), Ty::I64).with_param(v(1), Ty::I64);
        eb.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(24) }).with_result(v(2)),
        );
        // The second argument is the caller's LITERAL, or (the control) its own opaque param.
        let passed = if pass_literal { v(2) } else { v(1) };
        eb.body.push(
            InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![v(0), passed] })
                .with_result(v(3)),
        );
        eb.body.push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        let mut entry = IrFunction::new(FuncId::new(0), "entry", sig, BlockId::new(0));
        entry.blocks.push(eb);
        m.add_function(entry);

        let mut cb = Block::new(BlockId::new(0)).with_param(v(0), Ty::I64).with_param(v(1), Ty::I64);
        cb.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(0),
                indices: vec![v(1)],
                inbounds: true,
            })
            .with_result(v(2)),
        );
        cb.body.push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        let mut callee = IrFunction::new(FuncId::new(1), "callee", sig, BlockId::new(0));
        callee.blocks.push(cb);
        m.add_function(callee);
        m
    }

    /// **wave-DZ RED PROOF — the displacement that crosses a call boundary.** wave-DA judged each
    /// reachable function against its OWN constants, so a literal materialized in the caller and
    /// GEP'd by the callee's parameter was admitted. The walk now carries the caller's committed
    /// values into the callee's parameter positions.
    ///
    /// The CONTROL is the same module with the caller passing its own opaque parameter instead:
    /// nothing has committed to a rustc offset, so the callee's GEP stays green. That control is
    /// what keeps this from being "refuse every byte GEP", which would have cost the programme
    /// every element-arithmetic body — the discrimination
    /// `element_arithmetic_and_non_literal_displacements_stay_green` also holds.
    #[test]
    fn a_displacement_that_crosses_a_call_boundary_is_refused() {
        let m = call_boundary_module("dz_callarg", true);
        assert!(
            first_adt_interior_byte_arithmetic(&m, FuncId::new(0))
                .is_some_and(|why| why.contains("callee") && why.contains("call-site literal")),
            "a literal that reaches the GEP through a parameter is still a committed offset",
        );
        // CONTROL: the identical shape with an opaque argument commits to nothing.
        let control = call_boundary_module("dz_callarg_ctrl", false);
        assert_eq!(
            first_adt_interior_byte_arithmetic(&control, FuncId::new(0)),
            None,
            "a byte GEP indexed by a value nobody committed a rustc offset to stays green",
        );
        // And entering AT the callee — where no call site is visible — is likewise green, so the
        // refusal above really is the propagation and not a recognizer that refuses every param.
        assert_eq!(first_adt_interior_byte_arithmetic(&m, FuncId::new(1)), None);
    }

    /// **THE ZERO DISPLACEMENT, which is the whole point of wave-DZ.** The recognizer always
    /// refused a literal `+0`; nothing ever EMITTED one, because both struct-interior producer
    /// sites short-circuited `off == 0` to a bare `return pv`. `zero_displacement_agrees` now
    /// makes the producer spell the contested case out, and this is the receiving end.
    #[test]
    fn a_zero_displacement_byte_walk_is_refused_exactly_like_a_nonzero_one() {
        let mut m = two_fn_module("dz_zero", true);
        splice_byte_walk(&mut m, 0, Some(0), Ty::I8, true);
        assert!(
            first_adt_interior_byte_arithmetic(&m, FuncId::new(0))
                .is_some_and(|why| why.contains("+0")),
            "a zero displacement is a committed rustc offset like any other — `Mixed.b` is at \
             rustc byte 0 and at trust-ir byte 8",
        );
        let rep = compare_entries(
            &m,
            FuncId::new(0),
            &two_fn_module("dz_zero_oracle", true),
            FuncId::new(0),
        );
        assert_eq!(rep.mode, DiffMode::NotRun, "{:?}", rep.notes);
        assert_eq!(rep.samples_checked, 0, "the gate must refuse BEFORE any sample is run");
    }

    /// The literal table is built over the WHOLE function before any `GEP` is judged, so a
    /// displacement materialized in an EARLIER block still counts. A one-pass recognizer that
    /// scanned instructions in order would already catch this; one that reset per block would not,
    /// and that is the fail-OPEN direction.
    #[test]
    fn adt_interior_byte_walk_is_caught_across_blocks() {
        // The GEP goes in one appended block and its displacement constant in ANOTHER, so a
        // recognizer that reset its literal table per block would miss it. That is the fail-OPEN
        // direction, which is why the table is built over the whole function first.
        let mut m = two_fn_module("da_xblock", true);
        let k = ValueId::new(970);
        let f = &mut m.functions[0];
        let mut gep_blk = Block::new(trust_ir::BlockId::new(80));
        gep_blk.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base: ValueId::new(0),
                indices: vec![k],
                inbounds: true,
            })
            .with_result(ValueId::new(971)),
        );
        gep_blk.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        f.blocks.push(gep_blk);
        let mut const_blk = Block::new(trust_ir::BlockId::new(81));
        const_blk.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(24) }).with_result(k),
        );
        const_blk.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        f.blocks.push(const_blk);

        assert!(
            first_adt_interior_byte_arithmetic(&m, FuncId::new(0))
                .is_some_and(|why| why.contains("+24") && why.contains("entry")),
            "a displacement defined in a LATER block must still be recognized",
        );
        // ACCEPT CONTROL: drop the constant and the same GEP commits to nothing.
        let mut clean = m.clone();
        clean.functions[0].blocks.pop();
        assert_eq!(
            first_adt_interior_byte_arithmetic(&clean, FuncId::new(0)),
            None,
            "without a literal displacement there is nothing committed to",
        );
    }

    /// **THE SCOPE CONTROL, and it is not hypothetical.** A byte walk in a function the entry
    /// CANNOT REACH must not refuse anything. Written after the whole-module version of this gate
    /// was MEASURED withdrawing two real `seam: agreed` verdicts
    /// (`<expr::types::BinderData as Default>::default`, 1 sample, and
    /// `env::origin::OriginTrust::needs_recheck`, 3 samples) because
    /// `cache::TypeCheckCache::stats` emits `gep inbounds i8, +64` elsewhere in clean-kernel —
    /// while those entries' reachable closures are 3 and 2 functions and contain no byte walk.
    /// Withdrawing a verdict a body earned is a cost; paying it for a body that cannot run buys
    /// nothing.
    #[test]
    fn a_byte_walk_outside_the_reachable_closure_refuses_nothing() {
        let mut thir = two_fn_module("da_unreach_thir", true);
        // A third function nobody calls, carrying the exact shape the RED proof uses.
        let sig = thir.functions[0].ty;
        let mut orphan = trust_ir::Function::new(FuncId::new(7), "orphan", sig, trust_ir::BlockId::new(0));
        orphan.blocks.push(Block::new(trust_ir::BlockId::new(0)).with_param(ValueId::new(0), Ty::I64));
        thir.functions.push(orphan);
        splice_byte_walk(&mut thir, 2, Some(4), Ty::I8, true);

        assert!(
            function_adt_interior_byte_arithmetic(&thir.functions[2]).is_some(),
            "the orphan really does carry the shape — without this the test is vacuous",
        );
        assert_eq!(
            first_adt_interior_byte_arithmetic(&thir, FuncId::new(0)),
            None,
            "a walk outside the entry's reachable closure must not be reported",
        );
        let rep = compare_entries(
            &thir,
            FuncId::new(0),
            &two_fn_module("da_unreach_oracle", true),
            FuncId::new(0),
        );
        assert_eq!(
            rep.mode,
            DiffMode::Agreed,
            "an unreachable byte walk must not withdraw a verdict the body earned: {:?}",
            rep.notes
        );
        // ACCEPT CONTROL: entering AT the orphan does report it, so the scoping is real and not
        // a recognizer that simply stopped working.
        assert!(first_adt_interior_byte_arithmetic(&thir, FuncId::new(7)).is_some());
    }

    /// The recognizer must be silent on a module that carries no byte walk at all — otherwise
    /// every refusal above is vacuous and the whole interpreter channel is dead.
    #[test]
    fn the_byte_walk_recognizer_is_silent_on_a_clean_module() {
        assert_eq!(first_adt_interior_byte_arithmetic(&two_fn_module("da_clean", true), FuncId::new(0)), None);
        assert_eq!(first_adt_interior_byte_arithmetic(&unit_call_module("da_clean_unit"), FuncId::new(0)), None);
    }

    #[test]
    fn compare_entries_divergent_callee_is_mir_oracle() {
        // The perturbation control the plan requires: only the ORACLE-side callee body differs
        // (identity vs constant-0) — the seam's linking must SURFACE that as a divergence, never
        // silently agree.
        let thir = two_fn_module("seam_thir", true);
        let oracle = two_fn_module("seam_oracle", false);
        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(
            rep.mode,
            DiffMode::MirOracle,
            "a divergent linked callee must be caught (note: {:?})",
            rep.notes
        );
        assert!(!rep.equal, "a divergence is never `equal`");
    }

    #[test]
    fn compare_entries_unit_call_uses_zero_result_convention() {
        let thir = unit_call_module("seam_unit_thir");
        let oracle = unit_call_module("seam_unit_oracle");
        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(
            rep.mode,
            DiffMode::Agreed,
            "canonical zero-result unit calls must interpret and agree (note: {:?})",
            rep.notes
        );
        assert!(rep.equal);
        assert!(rep.samples_checked > 0);
    }

    #[test]
    fn compare_entries_non_unit_call_missing_result_is_hard_divergence() {
        let mut thir = two_fn_module("seam_corrupt_thir", true);
        let oracle = two_fn_module("seam_corrupt_oracle", true);
        let call = thir.functions[0].blocks[0]
            .body
            .iter_mut()
            .find(|node| matches!(node.inst, Inst::Call { .. }))
            .expect("entry has a call");
        call.results.clear();

        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(
            rep.mode,
            DiffMode::MirOracle,
            "a non-unit callee returning into a resultless call is malformed THIR IR and must \
             remain a hard divergence (note: {:?})",
            rep.notes
        );
        assert!(!rep.equal);
        assert!(
            rep.notes.iter().any(|note| note.contains("result arity mismatch")),
            "control must exercise the former blanket string-downgrade class: {:?}",
            rep.notes
        );
    }

    #[test]
    fn compare_entries_real_signature_difference_is_hard_divergence() {
        let thir = two_fn_module("seam_signature_thir", true);
        let mut oracle = two_fn_module("seam_signature_oracle", true);
        oracle.func_types[0].returns[0] = Ty::U64;

        let rep = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(
            rep.mode,
            DiffMode::MirOracle,
            "a structurally different non-unit signature must never become coverage-only \
             (note: {:?})",
            rep.notes
        );
        assert!(!rep.equal);
        assert!(
            rep.notes.iter().any(|note| note.starts_with("signature divergence")),
            "control must exercise the former blanket signature downgrade: {:?}",
            rep.notes
        );
    }

    // ------------------------------------------------------------------
    // Trust (plan 2026-07-29 T1): the RECURSIVE POINTER-PAYLOAD enum shape
    // class — clean-kernel's `Level` (first-party/clean
    // crates/clean-kernel/src/level/mod.rs).
    //
    // `Level`'s recursive edges ride a newtype struct (`LevelArc`) wrapping
    // `Option<Arc<Level>>`; its `Param` variant carries `Name`, a struct
    // holding the nested recursive enum `NameInner` (`Arc<Name>` / `Arc<str>`
    // payloads). `map_ty`'s registration walk spells that DAG with NO cycle:
    // every recursive edge bottoms out at `NonNull`'s raw pointer, and the
    // RawPtr arm does not recurse into pointees, so `Arc<Level>` registers as
    // a struct whose deep field is `Ty::Ptr` and `Level` itself never
    // re-enters the walk (the `adt_visit_stack` guard can only fire on
    // by-value ADT cycles, which Rust's sized-ness rules already forbid).
    //
    // These tests pin the trust-ir-level machinery over the EXACT def DAG that
    // `register_enum` + `register_struct` commit for `Level` at HEAD (post
    // #174 struct-payload admission + wave-EP thin-pointer payloads): the
    // canonical tag resolves, the binary codec round-trips the defs
    // byte-stably, and the differential comparator accepts the shape
    // structurally across independently-numbered modules while still
    // detecting deep-leaf and discriminant divergences. The registration
    // WALK itself needs a TyCtxt and is exercised by the ui fixture
    // `tests/ui/trust/trust_ir_lower_recursive_pointer_payload_enum.rs`
    // (compile-terminates today; measured end-to-end after the next trustc
    // stage rebuild).
    // ------------------------------------------------------------------

    /// The `Level` def DAG, with every table id shifted by `offset` dummy
    /// defs so cross-module comparisons prove STRUCTURAL agreement (raw id
    /// equality would be a lie: the producer and oracle number their tables
    /// independently).
    fn level_shape_module(name: &str, offset: u32) -> (Module, EnumId) {
        use trust_ir::{
            EnumLayoutDescriptor, EnumTagEncoding, FieldDef, StructDef, StructId, StructRepr,
        };

        let mut module = Module::new(name);
        for i in 0..offset {
            module.add_struct(StructDef {
                id: StructId::new(i),
                name: format!("DummyS{i}"),
                fields: Vec::new(),
                size: Some(0),
                align: Some(1),
                repr: StructRepr::Rust,
            });
            module.add_enum(EnumDef::new(
                EnumId::new(i),
                format!("DummyE{i}"),
                vec![EnumVariant {
                    name: "Only".into(),
                    fields: Vec::new(),
                    field_names: Vec::new(),
                }],
            ));
        }
        let sid = |i: u32| StructId::new(offset + i);
        let eid = |i: u32| EnumId::new(offset + i);
        let field = |name: &str, ty: Ty, off: u64| FieldDef {
            name: name.to_string(),
            ty,
            offset: Some(off),
        };
        let ptr_struct = |id: StructId, name: &str, size: u64| StructDef {
            id,
            name: name.to_string(),
            fields: vec![field("pointer", Ty::Ptr, 0)],
            size: Some(size),
            align: Some(8),
            repr: StructRepr::Transparent,
        };
        let zst = |id: StructId, name: &str| StructDef {
            id,
            name: name.to_string(),
            fields: Vec::new(),
            size: Some(0),
            align: Some(1),
            repr: StructRepr::Rust,
        };

        // Struct table, nested-first (the producer's registration order):
        // s0 NonNull<ArcInner<Level>>, s1 PhantomData<ArcInner<Level>>,
        // s2 Global, s3 Arc<Level>, s4 LevelArc, s5 NonNull<ArcInner<Name>>,
        // s6 PhantomData<ArcInner<Name>>, s7 Arc<Name>,
        // s8 NonNull<ArcInner<str>>, s9 PhantomData<ArcInner<str>>,
        // s10 Arc<str>, s11 Name.
        module.add_struct(ptr_struct(sid(0), "NonNull<ArcInner<Level>>", 8));
        module.add_struct(zst(sid(1), "PhantomData<ArcInner<Level>>"));
        module.add_struct(zst(sid(2), "Global"));
        module.add_struct(StructDef {
            id: sid(3),
            name: "Arc<Level>".into(),
            fields: vec![
                field("ptr", Ty::Struct(sid(0)), 0),
                field("phantom", Ty::Struct(sid(1)), 8),
                field("alloc", Ty::Struct(sid(2)), 8),
            ],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        // e0 Option<Arc<Level>> — niche-encoded over the non-null pointer.
        module.add_enum(
            EnumDef::new(
                eid(0),
                "Option<Arc<Level>>",
                vec![
                    EnumVariant {
                        name: "None".into(),
                        fields: Vec::new(),
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "Some".into(),
                        fields: vec![Ty::Struct(sid(3))],
                        field_names: Vec::new(),
                    },
                ],
            )
            .with_discriminants(vec![Some(0), Some(1)]),
        );
        let option_def = module.enums.last_mut().expect("Option def just added");
        option_def.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Niche {
                untagged_variant: 1,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: 0,
                niche_offset: 0,
                niche_ty: EnumTagRepr::U64,
            },
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![], vec![0]],
        });
        module.add_struct(StructDef {
            id: sid(4),
            name: "LevelArc".into(),
            fields: vec![field("0", Ty::Enum(eid(0)), 0)],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        module.add_struct(ptr_struct(sid(5), "NonNull<ArcInner<Name>>", 8));
        module.add_struct(zst(sid(6), "PhantomData<ArcInner<Name>>"));
        module.add_struct(StructDef {
            id: sid(7),
            name: "Arc<Name>".into(),
            fields: vec![
                field("ptr", Ty::Struct(sid(5)), 0),
                field("phantom", Ty::Struct(sid(6)), 8),
                field("alloc", Ty::Struct(sid(2)), 8),
            ],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        // `Arc<str>`: the recorded rustc size is 16 (a FAT pointer) while the
        // producer's current spelling of the deep `*const ArcInner<str>` lane
        // is the thin `Ty::Ptr` (map_ty's RawPtr catch-all does not model
        // unsized-tail ADT pointees). Recorded here exactly as registered —
        // the spelling caveat is called out in `register_enum`'s doc and is a
        // named follow-up, not asserted away.
        module.add_struct(ptr_struct(sid(8), "NonNull<ArcInner<str>>", 16));
        module.add_struct(zst(sid(9), "PhantomData<ArcInner<str>>"));
        module.add_struct(StructDef {
            id: sid(10),
            name: "Arc<str>".into(),
            fields: vec![
                field("ptr", Ty::Struct(sid(8)), 0),
                field("phantom", Ty::Struct(sid(9)), 16),
                field("alloc", Ty::Struct(sid(2)), 16),
            ],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        // e1 NameInner { Anon, Str(Arc<Name>, Arc<str>), Num(Arc<Name>, u64) }.
        module.add_enum(
            EnumDef::new(
                eid(1),
                "NameInner",
                vec![
                    EnumVariant {
                        name: "Anon".into(),
                        fields: Vec::new(),
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "Str".into(),
                        fields: vec![Ty::Struct(sid(7)), Ty::Struct(sid(10))],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "Num".into(),
                        fields: vec![Ty::Struct(sid(7)), Ty::U64],
                        field_names: Vec::new(),
                    },
                ],
            )
            .with_discriminants(vec![Some(0), Some(1), Some(2)]),
        );
        module.add_struct(StructDef {
            id: sid(11),
            name: "Name".into(),
            fields: vec![field("inner", Ty::Enum(eid(1)), 0), field("cached_hash", Ty::U64, 24)],
            size: Some(32),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        // e2 Level { Zero, Succ(LevelArc), Max(LevelArc, LevelArc),
        //            IMax(LevelArc, LevelArc), Param(Name) }.
        let level = module.add_enum(
            EnumDef::new(
                eid(2),
                "Level",
                vec![
                    EnumVariant {
                        name: "Zero".into(),
                        fields: Vec::new(),
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "Succ".into(),
                        fields: vec![Ty::Struct(sid(4))],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "Max".into(),
                        fields: vec![Ty::Struct(sid(4)), Ty::Struct(sid(4))],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "IMax".into(),
                        fields: vec![Ty::Struct(sid(4)), Ty::Struct(sid(4))],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "Param".into(),
                        fields: vec![Ty::Struct(sid(11))],
                        field_names: Vec::new(),
                    },
                ],
            )
            .with_discriminants(vec![Some(0), Some(1), Some(2), Some(3), Some(4)]),
        );
        (module, level)
    }

    #[test]
    fn level_shape_canonical_tag_and_discriminants_resolve() {
        let (module, level) = level_shape_module("level_tag", 0);
        let def = module.enum_def(level).expect("Level def registered");
        assert_eq!(
            def.effective_discriminants().expect("Level discriminants resolve"),
            vec![0, 1, 2, 3, 4]
        );
        assert_eq!(
            def.canonical_tag_repr().expect("Level canonical tag resolves"),
            EnumTagRepr::U8,
            "5 non-negative discriminants, no repr hint -> smallest unsigned width"
        );
    }

    #[test]
    fn level_shape_binary_codec_round_trips_byte_stably() {
        let (module, level) = level_shape_module("level_codec", 0);
        let bytes = trust_ir::binary::serialize_module(&module);
        let decoded =
            trust_ir::binary::deserialize_module(&bytes).expect("Level module deserializes");
        assert_eq!(decoded.enums, module.enums, "enum defs (incl. niche descriptor) round-trip");
        assert_eq!(decoded.structs, module.structs, "struct defs round-trip");
        assert_eq!(
            trust_ir::binary::serialize_module(&decoded),
            bytes,
            "re-serialization is byte-stable"
        );
        assert!(decoded.enum_def(level).is_some());
    }

    #[test]
    fn level_shape_signatures_agree_structurally_across_id_spaces() {
        let (thir, thir_level) = level_shape_module("level_thir", 0);
        let (oracle, oracle_level) = level_shape_module("level_oracle", 2);
        assert_ne!(thir_level, oracle_level, "the two modules number their tables differently");
        assert_eq!(
            tys_agree(&thir, &oracle, &Ty::Enum(thir_level), &Ty::Enum(oracle_level), TY_CMP_DEPTH),
            Ok(true),
            "the Level DAG must compare structurally, never by raw id"
        );
        // A trivial body's signature over the shape: `fn(&Level) -> bool`
        // (the borrow is the producer's thin `Ty::Ptr`) and the by-value
        // `fn(Level) -> bool`.
        let by_ref = FuncTy { params: vec![Ty::Ptr], returns: vec![Ty::Bool], is_vararg: false };
        assert_eq!(sig_tys_agree(&thir, &oracle, &by_ref, &by_ref), Ok(true));
        let by_value_thir = FuncTy {
            params: vec![Ty::Enum(thir_level)],
            returns: vec![Ty::Bool],
            is_vararg: false,
        };
        let by_value_oracle = FuncTy {
            params: vec![Ty::Enum(oracle_level)],
            returns: vec![Ty::Bool],
            is_vararg: false,
        };
        assert_eq!(sig_tys_agree(&thir, &oracle, &by_value_thir, &by_value_oracle), Ok(true));
    }

    #[test]
    fn level_shape_deep_leaf_divergence_is_detected() {
        let (thir, thir_level) = level_shape_module("level_deep_thir", 0);
        let (mut oracle, oracle_level) = level_shape_module("level_deep_oracle", 1);
        // Corrupt the DEEPEST leaf on the oracle side: NonNull<ArcInner<Level>>
        // .pointer flips Ptr -> I64. Reaching it requires the comparator to
        // descend Enum(Level) -> Struct(LevelArc) -> Enum(Option) ->
        // Struct(Arc) -> Struct(NonNull) -> leaf.
        oracle.structs[1].fields[0].ty = Ty::I64;
        assert_eq!(
            tys_agree(&thir, &oracle, &Ty::Enum(thir_level), &Ty::Enum(oracle_level), TY_CMP_DEPTH),
            Ok(false),
            "a deep pointer-leaf disagreement must be a detected divergence, not a pass"
        );
    }

    #[test]
    fn level_shape_discriminant_divergence_is_detected() {
        let (thir, thir_level) = level_shape_module("level_disc_thir", 0);
        let (mut oracle, oracle_level) = level_shape_module("level_disc_oracle", 0);
        let od = oracle_level.as_usize();
        oracle.enums[od].discriminants[4] = Some(9);
        assert_eq!(
            tys_agree(&thir, &oracle, &Ty::Enum(thir_level), &Ty::Enum(oracle_level), TY_CMP_DEPTH),
            Ok(false),
            "effective-discriminant disagreement must be a detected divergence"
        );
    }

    // ----------------------------------------------------------------------------------------
    // Trust (aggregate param lane): the `ParamClass::Struct` arm.
    // ----------------------------------------------------------------------------------------

    fn sfield(name: &str, ty: Ty) -> trust_ir::FieldDef {
        trust_ir::FieldDef { name: name.to_string(), ty, offset: None }
    }

    fn sdef_named(id: u32, name: &str, fields: Vec<trust_ir::FieldDef>) -> trust_ir::StructDef {
        trust_ir::StructDef {
            id: trust_ir::StructId::new(id),
            name: name.to_string(),
            fields,
            size: None,
            align: None,
            repr: trust_ir::StructRepr::Rust,
        }
    }

    /// `AllocationId(u64)` at id 0, `MemoryRegion { alloc: AllocationId, offset: usize,
    /// len: usize }` at id 1 — the real three-field / nested shape from the census (§2a).
    /// `swap_names` transposes the two same-typed `usize` field NAMES, which is exactly the
    /// transposition `tys_agree` alone cannot see.
    fn memory_region_module(name: &str, swap_names: bool) -> Module {
        let mut module = Module::new(name);
        module.add_struct(sdef_named(0, "AllocationId", vec![sfield("0", Ty::U64)]));
        let (a, b) = if swap_names { ("len", "offset") } else { ("offset", "len") };
        module.add_struct(sdef_named(
            1,
            "MemoryRegion",
            vec![
                sfield("alloc", Ty::Struct(trust_ir::StructId::new(0))),
                sfield(a, Ty::Usize),
                sfield(b, Ty::Usize),
            ],
        ));
        module
    }

    /// A body over `MemoryRegion` that returns field `read_field` of the top-level struct
    /// (1 = `offset`, 2 = `len`) — the shape of `MemoryRegion::offset` / `::len`.
    fn memory_region_reader(name: &str, swap_names: bool, read_field: u32) -> Module {
        let mut module = memory_region_module(name, swap_names);
        let region = Ty::Struct(trust_ir::StructId::new(1));
        let sig = module.add_func_type(FuncTy {
            params: vec![region.clone()],
            returns: vec![Ty::Usize],
            is_vararg: false,
        });
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.params.push((v(0), region));
        block.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Usize,
                aggregate: v(0),
                field: read_field,
            })
            .with_result(v(1)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        let mut function = Function::new(FuncId::new(0), "region_read", sig, block.id);
        function.blocks.push(block);
        module.add_function(function);
        module
    }

    #[test]
    fn struct_leaf_tys_admits_nested_scalars_and_refuses_everything_else() {
        let module = memory_region_module("leaves", false);
        assert_eq!(
            struct_leaf_tys(&module, trust_ir::StructId::new(1), MAX_STRUCT_DEPTH),
            Some(vec![Ty::U64, Ty::Usize, Ty::Usize]),
            "a nested scalar wrapper flattens depth-first, in declaration order"
        );

        // Refusals, each a shape whose exact value model this lane does not establish.
        for bad in [Ty::Unit, Ty::Ptr, Ty::Enum(EnumId::new(0)), Ty::Tuple(vec![Ty::U8])] {
            let mut m = Module::new("bad");
            m.add_struct(sdef_named(0, "S", vec![sfield("x", Ty::U8), sfield("y", bad.clone())]));
            assert_eq!(
                struct_leaf_tys(&m, trust_ir::StructId::new(0), MAX_STRUCT_DEPTH),
                None,
                "field type {bad} must be refused, not approximated"
            );
        }

        // A field-less struct carries no observable value.
        let mut empty = Module::new("empty");
        empty.add_struct(sdef_named(0, "Zst", Vec::new()));
        assert_eq!(struct_leaf_tys(&empty, trust_ir::StructId::new(0), MAX_STRUCT_DEPTH), None);

        // Unresolvable id fails closed.
        assert_eq!(struct_leaf_tys(&empty, trust_ir::StructId::new(7), MAX_STRUCT_DEPTH), None);

        // The leaf cap bites before the marshalling does.
        let mut wide = Module::new("wide");
        wide.add_struct(sdef_named(
            0,
            "Wide",
            (0..=MAX_STRUCT_LEAVES).map(|i| sfield(&format!("f{i}"), Ty::U8)).collect(),
        ));
        assert_eq!(struct_leaf_tys(&wide, trust_ir::StructId::new(0), MAX_STRUCT_DEPTH), None);

        // The depth cap bites too: a self-referential def cannot spin.
        let mut deep = Module::new("deep");
        deep.add_struct(sdef_named(0, "Rec", vec![sfield("me", Ty::Struct(trust_ir::StructId::new(0)))]));
        assert_eq!(struct_leaf_tys(&deep, trust_ir::StructId::new(0), MAX_STRUCT_DEPTH), None);
    }

    #[test]
    fn struct_samples_keep_same_typed_siblings_distinguishable() {
        let module = memory_region_module("rotation", false);
        let samples = struct_abstract_samples(&module, trust_ir::StructId::new(1))
            .expect("a three-leaf scalar struct samples");
        assert!(!samples.is_empty());
        assert!(samples.len() <= MAX_STRUCT_SAMPLES);
        assert!(samples.iter().all(|s| s.len() == 3), "one raw per scalar leaf");

        // THE property the leaf rotation exists for: `offset` and `len` are BOTH `usize`, so a
        // plain diagonal would give them equal values in every sample and `MemoryRegion::offset`
        // would agree with `MemoryRegion::len` vacuously. Every sample must separate them.
        assert!(
            samples.iter().all(|s| s[1] != s[2]),
            "same-typed sibling leaves must differ in every sample: {samples:?}"
        );
    }

    #[test]
    fn realize_struct_arg_builds_the_positional_nested_aggregate() {
        let module = memory_region_module("realize", false);
        let mut cursor = 0usize;
        let value = realize_struct_arg(
            &module,
            trust_ir::StructId::new(1),
            &[11, 22, 33],
            &mut cursor,
            MAX_STRUCT_DEPTH,
        )
        .expect("nested realization");
        assert_eq!(cursor, 3, "every leaf raw is consumed exactly once");
        assert_eq!(value.ty, Ty::Struct(trust_ir::StructId::new(1)));
        assert_eq!(
            value.kind,
            InterpretValueKind::Aggregate(vec![
                InterpretValue {
                    ty: Ty::Struct(trust_ir::StructId::new(0)),
                    kind: InterpretValueKind::Aggregate(vec![
                        InterpretValue::int(Ty::U64, 11).expect("u64")
                    ]),
                },
                InterpretValue::int(Ty::Usize, 22).expect("usize"),
                InterpretValue::int(Ty::Usize, 33).expect("usize"),
            ]),
            "one element per DECLARED field, in declaration order, no padding lane"
        );
    }

    #[test]
    fn struct_param_admission_requires_field_names_not_merely_field_shape() {
        let thir = memory_region_module("names_thir", false);
        let straight = memory_region_module("names_oracle", false);
        let swapped = memory_region_module("names_swapped", true);
        let region = Ty::Struct(trust_ir::StructId::new(1));

        // `tys_agree` cannot see the transposition — the field TYPES are identical.
        assert_eq!(tys_agree(&thir, &swapped, &region, &region, TY_CMP_DEPTH), Ok(true));

        assert!(struct_param_admissible(&thir, &straight, &region, &region));
        assert!(
            !struct_param_admissible(&thir, &swapped, &region, &region),
            "a transposed field NAME must leave the body on its existing not-run"
        );
    }

    #[test]
    fn struct_param_body_is_sampled_and_agrees() {
        let thir = memory_region_reader("agree_thir", false, 1);
        let oracle = memory_region_reader("agree_oracle", false, 1);
        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "{:?}", report.notes);
        assert!(
            report.samples_checked > 0,
            "a newly-backed body must report a REAL sample count, never a verdict without one"
        );
    }

    #[test]
    fn struct_param_field_index_divergence_is_caught() {
        // The oracle reads `len` where the producer reads `offset`. Both sides pass
        // `sig_tys_agree` (same signature) — only the SAMPLE can tell them apart, and it can
        // only do so because the leaf rotation gave the two `usize` fields distinct values.
        let thir = memory_region_reader("swap_thir", false, 1);
        let oracle = memory_region_reader("swap_oracle", false, 2);
        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(
            report.mode,
            DiffMode::MirOracle,
            "a field-index divergence must be a DIVERGENCE: {:?}",
            report.notes
        );
    }

    #[test]
    fn struct_param_unadmissible_shape_keeps_the_verbatim_non_scalar_refusal() {
        // A `Ty::Unit` field is refused, and the body must land back on the byte-identical
        // reason string the census classifies by — not on a new one.
        let mk = |name: &str| {
            let mut module = Module::new(name);
            module.add_struct(sdef_named(
                0,
                "HasUnit",
                vec![sfield("a", Ty::U8), sfield("pad", Ty::Unit)],
            ));
            let sty = Ty::Struct(trust_ir::StructId::new(0));
            let sig = module.add_func_type(FuncTy {
                params: vec![sty.clone()],
                returns: vec![Ty::U8],
                is_vararg: false,
            });
            let v = ValueId::new;
            let mut block = Block::new(trust_ir::BlockId::new(0));
            block.params.push((v(0), sty));
            block.body.push(
                InstrNode::new(Inst::ExtractField { ty: Ty::U8, aggregate: v(0), field: 0 })
                    .with_result(v(1)),
            );
            block.body.push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
            let mut function = Function::new(FuncId::new(0), "read", sig, block.id);
            function.blocks.push(block);
            module.add_function(function);
            module
        };
        let report = compare_entries(&mk("unit_thir"), FuncId::new(0), &mk("unit_oracle"), FuncId::new(0));
        assert_eq!(report.mode, DiffMode::NotRun);
        assert_eq!(report.samples_checked, 0);
        assert!(
            report
                .notes
                .iter()
                .any(|n| n == "non-scalar parameter type is non-interpretable (coverage-only skip)"),
            "the refusal reason string is a census classifier key: {:?}",
            report.notes
        );
    }

    // ---- vtable slice 7: paired promoted-global admission at the tail gate ----

    fn promoted_global(init: Option<Constant>, mutable: bool) -> trust_ir::Global {
        trust_ir::Global {
            name: "__trust_promoted_0".to_string(),
            ty: Ty::I32,
            mutable,
            initializer: init,
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
        }
    }

    /// The THIR producer's wave-16 spelling of `const A: &i32 = &2;`: an
    /// initializer-bearing named global + `global_addr` + `ret`.
    fn thir_promoted_module(init: Constant) -> Module {
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        let mut module = single_block_module("thir_promoted", vec![], vec![Ty::Ptr], block);
        module.globals.push(promoted_global(Some(init), false));
        module
    }

    #[test]
    fn paired_promoted_global_address_return_reaches_agreed() {
        // The realistic pair: the producer spelling vs the slice-6 RESPELLED oracle (the
        // measured const-address-of::A shape run through the actual rewrite).
        let thir = thir_promoted_module(Constant::Int(2));
        let mut oracle = once_stored_escaping_slot_module();
        assert_eq!(respell_promoted_slots_as_globals(&mut oracle), 1);

        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
        assert!(report.equal);
        assert_eq!(report.samples_checked, 1);
    }

    #[test]
    fn reborrow_chain_over_admitted_address_reaches_agreed() {
        // The kept-Borrows arm: `&(*_1)` arrives as Borrow(Borrow(global_addr)); every hop
        // is a pure pointer pass-through the audit tracks transitively.
        let v = ValueId::new;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        block.body.push(InstrNode::new(Inst::Borrow { ptr: v(1) }).with_result(v(2)));
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let mut oracle = single_block_module("oracle_reborrow", vec![], vec![Ty::Ptr], block);
        oracle.globals.push(promoted_global(Some(Constant::Int(2)), false));

        let thir = thir_promoted_module(Constant::Int(2));
        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
    }

    #[test]
    fn oracle_extra_global_dead_address_admits_observed_address_still_holds() {
        // Trust (vtable slice 13): the oracle respells once-stored borrowed locals the
        // producer never promotes (sugar-ambiguity's `ref pin`), leaving an oracle-only
        // `__trust_promoted_1`. When that extra's address closure is provably DEAD (no
        // Load, no Return, no escape — nothing ever observes it), no observation exists
        // for the comparison to miss, and the dead-address arm passes it WITHOUT pairing
        // — the paired `__trust_promoted_0` then carries the verdict exactly as in the
        // extra-free shape. (Through slice 12 this held fail-closed as "unpaired extra";
        // the hold was the old model's posture, not a soundness requirement.)
        let thir = thir_promoted_module(Constant::Int(2));
        let mut oracle = once_stored_escaping_slot_module();
        assert_eq!(respell_promoted_slots_as_globals(&mut oracle), 1);
        oracle.globals.push(trust_ir::Global {
            name: "__trust_promoted_1".to_string(),
            ty: Ty::I32,
            mutable: false,
            initializer: Some(Constant::Int(7)),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
        });
        // Insert the extra touch AFTER the paired chain (before the Return) so the
        // allocation order of the RETURNED pointer is unchanged and step (7) agrees —
        // any verdict movement comes from the tail gate alone.
        let extra = ValueId::new(9);
        let ret_pos = oracle.functions[0].blocks[0].body.len() - 1;
        oracle.functions[0].blocks[0].body.insert(
            ret_pos,
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(1) }).with_result(extra),
        );

        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);

        // The OBSERVED twin: loading through the unpaired extra makes its chain live —
        // not dead, not paired — and the body must hold on the verbatim module-global
        // note. The dead-address arm is a use-freeness proof, never a value claim.
        let mut observed = once_stored_escaping_slot_module();
        assert_eq!(respell_promoted_slots_as_globals(&mut observed), 1);
        observed.globals.push(trust_ir::Global {
            name: "__trust_promoted_1".to_string(),
            ty: Ty::I32,
            mutable: false,
            initializer: Some(Constant::Int(7)),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
        });
        let addr = ValueId::new(9);
        let loaded = ValueId::new(10);
        let ret_pos = observed.functions[0].blocks[0].body.len() - 1;
        observed.functions[0].blocks[0].body.insert(
            ret_pos,
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(1) }).with_result(addr),
        );
        observed.functions[0].blocks[0].body.insert(
            ret_pos + 1,
            InstrNode::new(Inst::Load { ty: Ty::I32, ptr: addr, volatile: false, align: None })
                .with_result(loaded),
        );
        let report = compare_entries(&thir, FuncId::new(0), &observed, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::NotRun, "notes: {:?}", report.notes);
        assert!(
            report.notes.iter().any(|n| n.contains("MIR oracle side")
                && n.contains("materializes module-global state/provenance")),
            "notes: {:?}",
            report.notes
        );
    }

    #[test]
    fn admission_refuses_store_call_gep_and_int_cast_uses() {
        // `promoted_addr_closure` is the audit: any use of a derived address outside
        // Load/Borrow/Copy/Return refuses the whole function's admission.
        let paired: BTreeSet<String> =
            std::iter::once("__trust_promoted_0".to_string()).collect();
        let v = ValueId::new;
        let build = |extra: Inst, extra_results: Vec<ValueId>| {
            let mut block = Block::new(trust_ir::BlockId::new(0));
            block.body.push(
                InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) })
                    .with_result(v(0)),
            );
            block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
            let mut node = InstrNode::new(extra);
            for r in extra_results {
                node = node.with_result(r);
            }
            block.body.push(node);
            block.body.push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
            let mut module = single_block_module("audit", vec![], vec![Ty::Ptr], block);
            module.globals.push(promoted_global(Some(Constant::Int(2)), false));
            module
        };

        let no_exclude: HashSet<ValueId> = HashSet::new();

        // Store THROUGH the admitted address: refused.
        let store = build(
            Inst::Store { ty: Ty::Ptr, ptr: v(1), value: v(0), volatile: false, align: None },
            vec![],
        );
        assert!(promoted_addr_closure(&store.functions[0], &store, &paired, &no_exclude)
            .is_none());

        // Escape into a call whose callee cannot be audited (absent body here — FuncId(1)
        // does not exist): refused. Trust (vtable slice 13): the blanket call-operand
        // refusal became the seeded-callee audit; an unresolvable/declaration callee is
        // its fail-closed floor.
        let call = build(Inst::Call { callee: FuncId::new(1), args: vec![v(1)] }, vec![v(2)]);
        assert!(
            promoted_addr_closure(&call.functions[0], &call, &paired, &no_exclude).is_none()
        );
        assert!(closure_contains_call(&call, FuncId::new(0)));

        // A derived interior address (GEP over the tracked base): refused.
        let gep = build(
            Inst::GEP { pointee_ty: Ty::I32, base: v(1), indices: vec![], inbounds: false },
            vec![v(2)],
        );
        assert!(promoted_addr_closure(&gep.functions[0], &gep, &paired, &no_exclude).is_none());

        // The good shape (Borrow + Return only) admits, for contrast.
        let mut ok_block = Block::new(trust_ir::BlockId::new(0));
        ok_block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        ok_block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        ok_block.body.push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        let mut ok = single_block_module("audit_ok", vec![], vec![Ty::Ptr], ok_block);
        ok.globals.push(promoted_global(Some(Constant::Int(2)), false));
        let audit =
            promoted_addr_closure(&ok.functions[0], &ok, &paired, &no_exclude).expect("admits");
        assert_eq!(audit.admitted.as_deref(), Some("__trust_promoted_0"));
        assert!(audit.tracked.contains(&v(0)) && audit.tracked.contains(&v(1)));
        assert!(audit.address_returned, "the Return of a tracked value must be reported");
    }

    #[test]
    fn pairing_refuses_content_mismatch_and_shape_violations() {
        // Content inequality is what closes the slice-5 blindness in reverse: both sides
        // would raw-agree on Ptr{0,0} while the two cells hold DIFFERENT values. The
        // pairing must refuse, keeping the body on its existing coverage-only note.
        let thir = thir_promoted_module(Constant::Int(2));

        let mismatch = thir_promoted_module(Constant::Int(3));
        assert!(paired_admitted_promoted_globals(&thir, &mismatch).is_empty());
        let report = compare_entries(&thir, FuncId::new(0), &mismatch, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::NotRun, "notes: {:?}", report.notes);
        assert!(
            report
                .notes
                .iter()
                .any(|n| n.contains("materializes module-global state/provenance")),
            "notes: {:?}",
            report.notes
        );

        // Initializer-LESS twin (the slice-4 symbolic-const carrier warning: shape-only
        // admission would zero-fill-agree) and a mutable twin: both refuse pairing.
        let mut bss = thir_promoted_module(Constant::Int(2));
        bss.globals[0].initializer = None;
        assert!(paired_admitted_promoted_globals(&thir, &bss).is_empty());
        let mut mutable = thir_promoted_module(Constant::Int(2));
        mutable.globals[0].mutable = true;
        assert!(paired_admitted_promoted_globals(&thir, &mutable).is_empty());

        // An address-bearing global type refuses (a Load-through would manufacture an
        // un-audited address value).
        let mut ptr_ty = thir_promoted_module(Constant::Int(2));
        ptr_ty.globals[0].ty = Ty::Ptr;
        let mut ptr_ty_b = thir_promoted_module(Constant::Int(2));
        ptr_ty_b.globals[0].ty = Ty::Ptr;
        assert!(paired_admitted_promoted_globals(&ptr_ty, &ptr_ty_b).is_empty());

        // The happy pairing, for contrast.
        let good = paired_admitted_promoted_globals(&thir, &thir_promoted_module(Constant::Int(2)));
        assert_eq!(good.len(), 1);
        assert!(good.contains("__trust_promoted_0"));
    }

    #[test]
    fn callee_returned_admitted_address_holds_in_a_linked_closure() {
        // Identical two-function modules on both sides: entry calls a callee that returns
        // the promoted global's address. Step (7) agrees (same shape both sides), but a
        // callee-returned address circulates as an un-audited call result — the exact
        // `ptr_to_int(callee())` hole the retired call-free bound existed for. Trust
        // (vtable slice 13): the hold now comes from the multi-function walk's
        // address-return refusal (call results are never tracked; the callee's own walk
        // admits its GlobalAddr and reports the Return, which a >1-function closure
        // refuses outright).
        let v = ValueId::new;
        let build = |name: &str| {
            let mut module = Module::new(name);
            let entry_sig = module.add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Ptr],
                is_vararg: false,
            });
            let mut entry_block = Block::new(trust_ir::BlockId::new(0));
            entry_block.body.push(
                InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![] })
                    .with_result(v(0)),
            );
            entry_block.body.push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
            let mut entry = Function::new(FuncId::new(0), "entry", entry_sig, entry_block.id);
            entry.blocks.push(entry_block);
            module.add_function(entry);

            let callee_sig = module.add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Ptr],
                is_vararg: false,
            });
            let mut callee_block = Block::new(trust_ir::BlockId::new(0));
            callee_block.body.push(
                InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) })
                    .with_result(v(0)),
            );
            callee_block.body.push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
            let mut callee = Function::new(FuncId::new(1), "callee", callee_sig, callee_block.id);
            callee.blocks.push(callee_block);
            module.add_function(callee);
            module.globals.push(promoted_global(Some(Constant::Int(2)), false));
            module
        };
        let report = compare_entries(
            &build("call_thir"),
            FuncId::new(0),
            &build("call_oracle"),
            FuncId::new(0),
        );
        assert_eq!(report.mode, DiffMode::NotRun, "notes: {:?}", report.notes);
        assert!(
            report
                .notes
                .iter()
                .any(|n| n.contains("reaches a return position inside a linked")),
            "notes: {:?}",
            report.notes
        );
    }

    // ---- vtable slice 13: linked-call admission + dead promoted addresses ----

    /// The measured macro-named-default shape, built identically on both sides: a
    /// paired promoted global whose address is handed to a linked callee that never
    /// uses its parameter (`fn foo(&self) {}`), entry returning unit.
    fn linked_arg_module(name: &str, callee_uses: CalleeUse) -> Module {
        let v = ValueId::new;
        let mut module = Module::new(name);
        let entry_sig =
            module.add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false });
        let callee_sig = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: match callee_uses {
                CalleeUse::ReturnsIt => vec![Ty::Ptr],
                _ => vec![],
            },
            is_vararg: false,
        });

        let mut entry_block = Block::new(trust_ir::BlockId::new(0));
        entry_block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        entry_block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        let call = InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![v(1)] });
        // A value-returning callee needs a declared call result (unused) so the
        // interpreter's result-arity check is not what holds the pair.
        let call = match callee_uses {
            CalleeUse::ReturnsIt => call.with_result(v(2)),
            _ => call,
        };
        entry_block.body.push(call);
        entry_block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        let mut entry = Function::new(FuncId::new(0), "entry", entry_sig, entry_block.id);
        entry.blocks.push(entry_block);
        module.add_function(entry);

        let mut callee_block = Block::new(trust_ir::BlockId::new(0));
        callee_block.params.push((v(0), Ty::Ptr));
        match callee_uses {
            CalleeUse::Ignored => {
                callee_block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
            }
            CalleeUse::LoadsIt => {
                callee_block.body.push(
                    InstrNode::new(Inst::Load {
                        ty: Ty::I32,
                        ptr: v(0),
                        volatile: false,
                        align: None,
                    })
                    .with_result(v(1)),
                );
                callee_block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
            }
            CalleeUse::ReturnsIt => {
                callee_block.body.push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
            }
            CalleeUse::StoresIt => {
                callee_block.body.push(
                    InstrNode::new(Inst::Alloca { ty: Ty::Ptr, count: None, align: None })
                        .with_result(v(1)),
                );
                callee_block.body.push(InstrNode::new(Inst::Store {
                    ty: Ty::Ptr,
                    ptr: v(1),
                    value: v(0),
                    volatile: false,
                    align: None,
                }));
                callee_block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
            }
        }
        let mut callee = Function::new(FuncId::new(1), "leaf", callee_sig, callee_block.id);
        callee.blocks.push(callee_block);
        module.add_function(callee);
        module.globals.push(promoted_global(Some(Constant::Int(2)), false));
        module
    }

    #[derive(Clone, Copy)]
    enum CalleeUse {
        Ignored,
        LoadsIt,
        ReturnsIt,
        StoresIt,
    }

    #[test]
    fn linked_call_argument_to_an_ignoring_callee_reaches_agreed() {
        // The macro-named-default::main mechanism (measured by module dump before this
        // was built): the entry's paired-global address crosses ONE direct call into a
        // callee that never touches it. The seeded audit proves the callee use-free and
        // the pair mints the verdict the call-free bound used to withhold.
        let report = compare_entries(
            &linked_arg_module("thir_linked", CalleeUse::Ignored),
            FuncId::new(0),
            &linked_arg_module("oracle_linked", CalleeUse::Ignored),
            FuncId::new(0),
        );
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
        assert!(report.equal);
    }

    #[test]
    fn linked_call_argument_loaded_by_the_callee_reaches_agreed() {
        // A callee LOAD through the seeded address is modeled: the pairing's bit-exact
        // content equality is exactly what makes the loaded value the same on both sides.
        let report = compare_entries(
            &linked_arg_module("thir_load_arg", CalleeUse::LoadsIt),
            FuncId::new(0),
            &linked_arg_module("oracle_load_arg", CalleeUse::LoadsIt),
            FuncId::new(0),
        );
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
    }

    #[test]
    fn seeded_callee_returning_or_storing_the_address_refuses_admission() {
        // The callee RETURNING the seeded address would hand it back as an un-audited
        // ordinary call result; STORING it escapes the audit's value model. Both refuse
        // the seeded audit, the entry's GlobalAddr stays unadmitted, and the body holds
        // on the verbatim module-global note.
        for shape in [CalleeUse::ReturnsIt, CalleeUse::StoresIt] {
            let report = compare_entries(
                &linked_arg_module("thir_refuse", shape),
                FuncId::new(0),
                &linked_arg_module("oracle_refuse", shape),
                FuncId::new(0),
            );
            assert_eq!(report.mode, DiffMode::NotRun, "notes: {:?}", report.notes);
            assert!(
                report
                    .notes
                    .iter()
                    .any(|n| n.contains("materializes module-global state/provenance")),
                "notes: {:?}",
                report.notes
            );
        }
    }

    #[test]
    fn two_distinct_admitted_names_across_linked_functions_hold() {
        // Entry admits `__trust_promoted_0`, its callee admits `__trust_promoted_1`
        // (both paired, both content-equal across sides). The per-function ≤1 bound
        // passes each function, so the WALK-level per-side bound must refuse: two
        // admitted objects make the cross-side single-object argument ambiguous.
        let v = ValueId::new;
        let build = |name: &str| {
            let mut module = linked_arg_module(name, CalleeUse::Ignored);
            module.globals.push(trust_ir::Global {
                name: "__trust_promoted_1".to_string(),
                ty: Ty::I32,
                mutable: false,
                initializer: Some(Constant::Int(7)),
                linkage: trust_ir::Linkage::Internal,
                tls: None,
                align: None,
            });
            // The callee gains its own admitted-global observation: address + LOAD (a
            // live use, so the dead-address arm cannot absorb it).
            let callee = &mut module.functions[1];
            let ret = callee.blocks[0].body.pop().expect("return");
            callee.blocks[0].body.push(
                InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(1) })
                    .with_result(v(7)),
            );
            callee.blocks[0].body.push(
                InstrNode::new(Inst::Load { ty: Ty::I32, ptr: v(7), volatile: false, align: None })
                    .with_result(v(8)),
            );
            callee.blocks[0].body.push(ret);
            module
        };
        let report = compare_entries(
            &build("thir_two_names"),
            FuncId::new(0),
            &build("oracle_two_names"),
            FuncId::new(0),
        );
        assert_eq!(report.mode, DiffMode::NotRun, "notes: {:?}", report.notes);
        assert!(
            report.notes.iter().any(|n| n.contains("distinct paired module globals")),
            "notes: {:?}",
            report.notes
        );
    }

    #[test]
    fn dead_promoted_addresses_beside_one_live_paired_global_reach_agreed() {
        // The measured sugar-ambiguity::main shape: two DEAD promoted addresses (one of
        // them an oracle-only extra) beside ONE live, loaded, paired global. The dead
        // chains are absorbed by the use-freeness proof without consuming the
        // ≤1-distinct-admitted budget; the live global carries the verdict.
        let v = ValueId::new;
        let build = |name: &str, with_extra: bool| {
            let mut block = Block::new(trust_ir::BlockId::new(0));
            // Dead address of global 0 (borrow chain, never observed).
            block.body.push(
                InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
            );
            block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
            // Live, loaded address of global 1.
            block.body.push(
                InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(1) }).with_result(v(2)),
            );
            block.body.push(
                InstrNode::new(Inst::Load { ty: Ty::I32, ptr: v(2), volatile: false, align: None })
                    .with_result(v(3)),
            );
            if with_extra {
                // Oracle-only extra: dead outright.
                block.body.push(
                    InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(2) })
                        .with_result(v(4)),
                );
            }
            block.body.push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
            let mut module = single_block_module(name, vec![], vec![Ty::I32], block);
            module.globals.push(promoted_global(Some(Constant::Int(2)), false));
            module.globals.push(trust_ir::Global {
                name: "__trust_promoted_1".to_string(),
                ty: Ty::I32,
                mutable: false,
                initializer: Some(Constant::Int(5)),
                linkage: trust_ir::Linkage::Internal,
                tls: None,
                align: None,
            });
            if with_extra {
                module.globals.push(trust_ir::Global {
                    name: "__trust_promoted_2".to_string(),
                    ty: Ty::I32,
                    mutable: false,
                    initializer: Some(Constant::Int(9)),
                    linkage: trust_ir::Linkage::Internal,
                    tls: None,
                    align: None,
                });
            }
            module
        };
        let report = compare_entries(
            &build("thir_dead_beside_live", false),
            FuncId::new(0),
            &build("oracle_dead_beside_live", true),
            FuncId::new(0),
        );
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
        assert_eq!(report.samples_checked, 1);
    }

    #[test]
    fn load_through_admitted_address_reaches_agreed_on_value_return() {
        // The load-through form: agreement means "same initializer bytes", true by the
        // pairing's bit-exact content equality.
        let v = ValueId::new;
        let mut thir_block = Block::new(trust_ir::BlockId::new(0));
        thir_block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        thir_block.body.push(
            InstrNode::new(Inst::Load { ty: Ty::I32, ptr: v(0), volatile: false, align: None })
                .with_result(v(1)),
        );
        thir_block.body.push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        let mut thir = single_block_module("thir_load", vec![], vec![Ty::I32], thir_block);
        thir.globals.push(promoted_global(Some(Constant::Int(2)), false));

        let mut oracle_block = Block::new(trust_ir::BlockId::new(0));
        oracle_block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        oracle_block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        oracle_block.body.push(
            InstrNode::new(Inst::Load { ty: Ty::I32, ptr: v(1), volatile: false, align: None })
                .with_result(v(2)),
        );
        oracle_block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let mut oracle = single_block_module("oracle_load", vec![], vec![Ty::I32], oracle_block);
        oracle.globals.push(promoted_global(Some(Constant::Int(2)), false));

        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
        assert_eq!(report.samples_checked, 1);
    }

    // ---- vtable slice 8: bytes-global pairing + the fat-carrier audit arm ----

    fn bytes_global(name: &str, bytes: &[u8]) -> trust_ir::Global {
        trust_ir::Global {
            name: name.to_string(),
            ty: Ty::Array(trust_ir::value::TyId::new(0), bytes.len() as u64),
            mutable: false,
            initializer: Some(Constant::Array(
                bytes.iter().map(|b| Constant::Int(*b as i128)).collect(),
            )),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
        }
    }

    /// The producer's wave-17 spelling of `const FOO: &[u8] = b"foo";`: bytes global +
    /// `global_addr` + `const u64 len` + `ptr_from_parts fatptr<slice u8>` + `ret`
    /// (measured: references.rs FOO, byte-literals.rs BAR/BAZ).
    fn thir_bytes_fat_slice_module(bytes: &[u8]) -> Module {
        let v = ValueId::new;
        let fat = Ty::FatPtr(trust_ir::FatPtrKind::Slice(trust_ir::value::TyId::new(0)));
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(bytes.len() as i128),
            })
            .with_result(v(1)),
        );
        block.body.push(
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: fat.clone(),
                metadata_ty: Ty::U64,
                data: v(0),
                metadata: v(1),
            })
            .with_result(v(2)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let mut module = single_block_module("thir_bytes_fat", vec![], vec![fat], block);
        module.add_type(Ty::U8);
        module.globals.push(bytes_global("__trust_bytes_0", bytes));
        module
    }

    /// The slice-8 marshalled ORACLE spelling of the same body: the bridge's
    /// `emit_str_const_bytes_global` + the reborrow (`&(*_2)`) Borrow hop the
    /// mir_built stream carries.
    fn oracle_bytes_fat_slice_module(bytes: &[u8]) -> Module {
        let v = ValueId::new;
        let fat = Ty::FatPtr(trust_ir::FatPtrKind::Slice(trust_ir::value::TyId::new(0)));
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(bytes.len() as i128),
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: fat.clone(),
                metadata_ty: Ty::U64,
                data: v(1),
                metadata: v(2),
            })
            .with_result(v(3)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        let mut module = single_block_module("oracle_bytes_fat", vec![], vec![fat], block);
        module.add_type(Ty::U8);
        module.globals.push(bytes_global("__trust_bytes_0", bytes));
        module
    }

    #[test]
    fn bytes_global_fat_slice_return_reaches_agreed() {
        // The `const FOO: &[u8] = b"foo"` replica: a returned fat pointer whose data
        // lane is the single paired bytes global's address and whose metadata lane is
        // the exact length. The fat-carrier audit arm is what admits it at the tail
        // gate; step (7) compares the FatPtr kind raw (data Pointer + metadata Int).
        let thir = thir_bytes_fat_slice_module(b"foo");
        let oracle = oracle_bytes_fat_slice_module(b"foo");
        let paired = paired_admitted_promoted_globals(&thir, &oracle);
        assert!(paired.contains("__trust_bytes_0"), "bytes grammar must pair: {paired:?}");
        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
        assert!(report.equal);
        assert_eq!(report.samples_checked, 1);
    }

    #[test]
    fn bytes_global_str_fat_return_reaches_agreed() {
        // The `fn name() -> &'static str { "hi" }` replica at the id-less Str fat kind.
        let build = |name: &str, with_borrow: bool| {
            let v = ValueId::new;
            let fat = Ty::FatPtr(trust_ir::FatPtrKind::Str);
            let mut block = Block::new(trust_ir::BlockId::new(0));
            block.body.push(
                InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) })
                    .with_result(v(0)),
            );
            let mut data = v(0);
            let mut next = 1;
            if with_borrow {
                block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
                data = v(1);
                next = 2;
            }
            block.body.push(
                InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(2) })
                    .with_result(v(next)),
            );
            block.body.push(
                InstrNode::new(Inst::PtrFromParts {
                    ptr_ty: fat.clone(),
                    metadata_ty: Ty::U64,
                    data,
                    metadata: v(next),
                })
                .with_result(v(next + 1)),
            );
            block.body.push(InstrNode::new(Inst::Return { values: vec![v(next + 1)] }));
            let mut module = single_block_module(name, vec![], vec![fat], block);
            module.add_type(Ty::U8);
            module.globals.push(bytes_global("__trust_bytes_0", b"hi"));
            module
        };
        let report = compare_entries(
            &build("thir_str", false),
            FuncId::new(0),
            &build("oracle_str", true),
            FuncId::new(0),
        );
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
        assert_eq!(report.samples_checked, 1);
    }

    #[test]
    fn bytes_global_thin_array_ref_return_reaches_agreed() {
        // The `static BAR_FIXED: &[u8; 3] = b"..."` replica: THIN return of the bytes
        // global's address — the pre-existing thin machinery over the NEW bytes grammar.
        let v = ValueId::new;
        let mut thir_block = Block::new(trust_ir::BlockId::new(0));
        thir_block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        thir_block.body.push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        let mut thir = single_block_module("thir_thin_bytes", vec![], vec![Ty::Ptr], thir_block);
        thir.add_type(Ty::U8);
        thir.globals.push(bytes_global("__trust_bytes_0", b"jjj"));

        let mut oracle_block = Block::new(trust_ir::BlockId::new(0));
        oracle_block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        oracle_block.body.push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        oracle_block.body.push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        let mut oracle =
            single_block_module("oracle_thin_bytes", vec![], vec![Ty::Ptr], oracle_block);
        oracle.add_type(Ty::U8);
        oracle.globals.push(bytes_global("__trust_bytes_0", b"jjj"));

        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
        assert_eq!(report.samples_checked, 1);
    }

    #[test]
    fn bytes_global_content_mismatch_holds_fail_closed() {
        // Same shape, different bytes: step (7) would raw-agree on Ptr{0,0}+len — the
        // hold MUST come from the pairing's bit-exact content equality at the tail gate
        // (the slice-5 blindness in reverse, the slice-7 rule applied to bytes).
        let thir = thir_bytes_fat_slice_module(b"foo");
        let oracle = oracle_bytes_fat_slice_module(b"fop");
        assert!(paired_admitted_promoted_globals(&thir, &oracle).is_empty());
        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::NotRun, "notes: {:?}", report.notes);
        assert!(
            report
                .notes
                .iter()
                .any(|n| n.contains("materializes module-global state/provenance")),
            "notes: {:?}",
            report.notes
        );
    }

    #[test]
    fn fat_carrier_audit_scope_is_slice_str_data_lane_only() {
        // The audit's fat-carrier arm admits EXACTLY the Slice/Str data-lane position.
        let paired: BTreeSet<String> = std::iter::once("__trust_bytes_0".to_string()).collect();
        let v = ValueId::new;
        let fat_slice = Ty::FatPtr(trust_ir::FatPtrKind::Slice(trust_ir::value::TyId::new(0)));

        // (a) tracked address in the METADATA lane: refused (an address in a length
        //     lane is out of model even though the instruction kind is admitted).
        let mut meta_block = Block::new(trust_ir::BlockId::new(0));
        meta_block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        meta_block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(0) })
                .with_result(v(1)),
        );
        meta_block.body.push(
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: fat_slice.clone(),
                metadata_ty: Ty::U64,
                data: v(1),
                metadata: v(0),
            })
            .with_result(v(2)),
        );
        meta_block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let mut meta =
            single_block_module("audit_meta", vec![], vec![fat_slice.clone()], meta_block);
        meta.add_type(Ty::U8);
        meta.globals.push(bytes_global("__trust_bytes_0", b"foo"));
        assert!(promoted_addr_closure(&meta.functions[0], &meta, &paired, &HashSet::new()).is_none());

        // (b) a TraitObject fat assembly over the tracked address: refused — its
        //     metadata is a POINTER (a second address lane the model does not cover).
        let mut dyn_block = Block::new(trust_ir::BlockId::new(0));
        dyn_block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(v(0)),
        );
        dyn_block.body.push(
            InstrNode::new(Inst::Undef { ty: Ty::Ptr }).with_result(v(1)),
        );
        dyn_block.body.push(
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: Ty::FatPtr(trust_ir::FatPtrKind::TraitObject { trait_id: 7 }),
                metadata_ty: Ty::Ptr,
                data: v(0),
                metadata: v(1),
            })
            .with_result(v(2)),
        );
        dyn_block.body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let mut dyn_m = single_block_module(
            "audit_dyn",
            vec![],
            vec![Ty::FatPtr(trust_ir::FatPtrKind::TraitObject { trait_id: 7 })],
            dyn_block,
        );
        dyn_m.add_type(Ty::U8);
        dyn_m.globals.push(bytes_global("__trust_bytes_0", b"foo"));
        assert!(promoted_addr_closure(&dyn_m.functions[0], &dyn_m, &paired, &HashSet::new()).is_none());

        // (c) the good Slice shape admits, and the fat carrier joins the tracked set.
        let good = thir_bytes_fat_slice_module(b"foo");
        let audit = promoted_addr_closure(&good.functions[0], &good, &paired, &HashSet::new())
            .expect("admits");
        assert_eq!(audit.admitted.as_deref(), Some("__trust_bytes_0"));
        assert!(audit.tracked.contains(&v(0)), "the seed address is tracked");
        assert!(audit.tracked.contains(&v(2)), "the assembled fat carrier is tracked");
    }

    /// Trust (vtable slice 16): the flat-enum-model alignment, end-to-end — the measured
    /// `get`-shaped pair (`fn get() -> Result<Payload, ()>` returning `Ok(Payload{5,7})`;
    /// probe dumps in the slice record). THIR side: the producer's dump-verbatim spelling
    /// (`const struct {0,0}` seed + InsertFields, `const enum {0,{0,0}}` seed + payload
    /// InsertField). Oracle side: the post-widening bridge spelling — the struct
    /// construction still Undef-DEAD-SEEDED (substituted by the pipeline), the ENUM
    /// construction Const-seeded with the recursive struct zero, NO enum-typed Undef.
    /// Reaching Agreed pins all four stages at once: no LIVE havoc, (Enum,Enum) sig
    /// agreement through the struct-payload defs, both interpreters, value comparison.
    #[test]
    fn first_class_struct_payload_enum_ctor_pair_reaches_agreed() {
        let v = ValueId::new;
        let payload_fields =
            |m: &mut Module| -> trust_ir::value::StructId {
                m.add_struct(trust_ir::StructDef {
                    id: trust_ir::value::StructId::new(0),
                    name: "Payload".into(),
                    fields: vec![
                        trust_ir::ty::FieldDef { name: "a".into(), ty: Ty::U32, offset: Some(0) },
                        trust_ir::ty::FieldDef { name: "b".into(), ty: Ty::U64, offset: Some(8) },
                    ],
                    size: Some(16),
                    align: Some(8),
                    repr: trust_ir::ty::StructRepr::Rust,
                });
                trust_ir::value::StructId::new(0)
            };
        let enum_def = |sid: trust_ir::value::StructId| {
            trust_ir::EnumDef::new(
                trust_ir::value::EnumId::new(0),
                "Result",
                vec![
                    trust_ir::EnumVariant {
                        name: "Ok".into(),
                        fields: vec![Ty::Struct(sid)],
                        field_names: vec![],
                    },
                    trust_ir::EnumVariant {
                        name: "Err".into(),
                        fields: vec![Ty::Unit],
                        field_names: vec![],
                    },
                ],
            )
            .with_discriminants(vec![Some(0), Some(1)])
        };

        // THIR side — the producer's dump-verbatim construction.
        let mut thir = Module::new("thir_struct_payload_enum");
        let t_sid = payload_fields(&mut thir);
        thir.add_enum(enum_def(t_sid));
        let e_ty = Ty::Enum(trust_ir::value::EnumId::new(0));
        let s_ty = Ty::Struct(t_sid);
        let mut tb = Block::new(trust_ir::BlockId::new(0));
        tb.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(5) }).with_result(v(0)),
        );
        tb.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(7) }).with_result(v(1)),
        );
        tb.body.push(
            InstrNode::new(Inst::Const {
                ty: s_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
            })
            .with_result(v(2)),
        );
        tb.body.push(
            InstrNode::new(Inst::InsertField { ty: s_ty.clone(), aggregate: v(2), field: 0, value: v(0) })
                .with_result(v(3)),
        );
        tb.body.push(
            InstrNode::new(Inst::InsertField { ty: s_ty.clone(), aggregate: v(3), field: 1, value: v(1) })
                .with_result(v(4)),
        );
        tb.body.push(
            InstrNode::new(Inst::Const {
                ty: e_ty.clone(),
                value: Constant::Aggregate(vec![
                    Constant::Int(0),
                    Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
                ]),
            })
            .with_result(v(5)),
        );
        tb.body.push(
            InstrNode::new(Inst::InsertField { ty: e_ty.clone(), aggregate: v(5), field: 1, value: v(4) })
                .with_result(v(6)),
        );
        tb.body.push(InstrNode::new(Inst::Return { values: vec![v(6)] }));
        let thir =
            single_block_module_with(thir, "thir_struct_payload_enum", vec![], vec![e_ty.clone()], tb);

        // Oracle side — the post-widening bridge shape (struct ctor dead-seeded, enum
        // ctor Const-seeded; ids in a DIFFERENT order to keep the comparison honest).
        let mut oracle = Module::new("oracle_struct_payload_enum");
        let o_sid = payload_fields(&mut oracle);
        oracle.add_enum(enum_def(o_sid));
        let oe_ty = Ty::Enum(trust_ir::value::EnumId::new(0));
        let os_ty = Ty::Struct(o_sid);
        let mut ob = Block::new(trust_ir::BlockId::new(0));
        ob.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(5) }).with_result(v(0)),
        );
        ob.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(7) }).with_result(v(1)),
        );
        ob.body.push(InstrNode::new(Inst::Undef { ty: os_ty.clone() }).with_result(v(2)));
        ob.body.push(
            InstrNode::new(Inst::InsertField { ty: os_ty.clone(), aggregate: v(2), field: 0, value: v(0) })
                .with_result(v(3)),
        );
        ob.body.push(
            InstrNode::new(Inst::InsertField { ty: os_ty.clone(), aggregate: v(3), field: 1, value: v(1) })
                .with_result(v(4)),
        );
        ob.body.push(
            InstrNode::new(Inst::Const {
                ty: oe_ty.clone(),
                value: Constant::Aggregate(vec![
                    Constant::Int(0),
                    Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
                ]),
            })
            .with_result(v(5)),
        );
        ob.body.push(
            InstrNode::new(Inst::InsertField { ty: oe_ty.clone(), aggregate: v(5), field: 1, value: v(4) })
                .with_result(v(6)),
        );
        ob.body.push(InstrNode::new(Inst::Return { values: vec![v(6)] }));
        let oracle = single_block_module_with(
            oracle,
            "oracle_struct_payload_enum",
            vec![],
            vec![oe_ty],
            ob,
        );
        let oracle = oracle_pipeline(oracle);

        let report = compare_entries(&thir, FuncId::new(0), &oracle, FuncId::new(0));
        assert_eq!(report.mode, DiffMode::Agreed, "notes: {:?}", report.notes);
        assert!(report.equal);
    }

    /// Trust (vtable slice 16): the widening makes the NICHE descriptor identity LIVE for
    /// the first time (eligibility was Direct-only before) — pin all three outcomes of the
    /// B3-3 identity arm on a niche pair: equal descriptors agree; PRESENCE asymmetry is a
    /// coverage Err (the fill-drift tripwire), never Ok(false); CONTENT drift likewise.
    #[test]
    fn niche_descriptor_identity_agrees_and_drift_is_coverage_err() {
        let def = |layout: Option<trust_ir::EnumLayoutDescriptor>| {
            let mut d = trust_ir::EnumDef::new(
                trust_ir::value::EnumId::new(0),
                "Opt",
                vec![
                    trust_ir::EnumVariant { name: "None".into(), fields: vec![], field_names: vec![] },
                    trust_ir::EnumVariant {
                        name: "Some".into(),
                        fields: vec![Ty::Ptr],
                        field_names: vec![],
                    },
                ],
            )
            .with_discriminants(vec![Some(0), Some(1)]);
            d.layout = layout;
            d
        };
        let niche = |start: u128| trust_ir::EnumLayoutDescriptor {
            encoding: trust_ir::EnumTagEncoding::Niche {
                untagged_variant: 1,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: start,
                niche_offset: 0,
                niche_ty: trust_ir::EnumTagRepr::U64,
            },
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![], vec![0]],
        };
        let module_with = |layout: Option<trust_ir::EnumLayoutDescriptor>| {
            let mut m = Module::new("m");
            m.add_enum(def(layout));
            m
        };
        let a = module_with(Some(niche(0)));
        let b = module_with(Some(niche(0)));
        let e = Ty::Enum(trust_ir::value::EnumId::new(0));
        assert!(matches!(tys_agree(&a, &b, &e, &e, TY_CMP_DEPTH), Ok(true)));
        // Presence asymmetry: coverage Err, never a verdict.
        let c = module_with(None);
        assert!(tys_agree(&a, &c, &e, &e, TY_CMP_DEPTH).is_err());
        assert!(tys_agree(&c, &a, &e, &e, TY_CMP_DEPTH).is_err());
        // Content drift: coverage Err, never a verdict.
        let d2 = module_with(Some(niche(1)));
        assert!(tys_agree(&a, &d2, &e, &e, TY_CMP_DEPTH).is_err());
    }

    // ---- Trust (Q1): the pointer-param INPUT lane -----------------------------------
    //
    // Pure unit tests: no module build, no interpreter module fixture beyond what each test
    // constructs. `struct_layout_agrees` is the reusable two-sided layout-parity primitive; the
    // nested-depth-2 case below is the one that caught the raw-`Ty::Struct(id)` short-circuit.

    use trust_ir::interpret::InterpretValue as Q1Value;
    use trust_ir::{FieldDef, StructDef, StructId, StructRepr};

    fn q1_field(name: &str, ty: Ty, offset: Option<u64>) -> FieldDef {
        FieldDef { name: name.to_string(), ty, offset }
    }

    fn q1_sdef(
        id: u32,
        name: &str,
        fields: Vec<FieldDef>,
        size: Option<u64>,
        align: Option<u64>,
        repr: StructRepr,
    ) -> StructDef {
        StructDef { id: StructId::new(id), name: name.to_string(), fields, size, align, repr }
    }

    /// One module holding one struct def at id 0.
    fn q1_m(name: &str, def: StructDef) -> Module {
        let mut module = Module::new(name);
        module.add_struct(def);
        module
    }

    /// `{ a: u8, b: u64 }` as rustc REORDERS it under repr(Rust): `b` at 0, `a` at 8.
    fn q1_reordered(id: u32) -> StructDef {
        q1_sdef(
            id,
            "S",
            vec![q1_field("a", Ty::U8, Some(8)), q1_field("b", Ty::U64, Some(0))],
            Some(16),
            Some(8),
            StructRepr::Rust,
        )
    }

    /// The same field LIST in plain declaration order: `a` at 0, `b` at 8.
    fn q1_declaration_order(id: u32) -> StructDef {
        q1_sdef(
            id,
            "S",
            vec![q1_field("a", Ty::U8, Some(0)), q1_field("b", Ty::U64, Some(8))],
            Some(16),
            Some(8),
            StructRepr::Rust,
        )
    }

    /// POSITIVE: both sides carry the SAME rustc-reordered layout, whose offsets do not follow
    /// declaration index. Parity must be decided on offsets, so this agrees.
    #[test]
    fn layout_agrees_on_matching_reordered_layout() {
        let (am, bm) = (q1_m("a", q1_reordered(0)), q1_m("b", q1_reordered(0)));
        assert!(struct_layout_agrees(
            &am,
            &bm,
            &Ty::Struct(StructId::new(0)),
            &Ty::Struct(StructId::new(0)),
            MAX_STRUCT_DEPTH
        ));
    }

    /// DECLARATION-ORDER CONTROL for the test above: an ordinary, non-reordered layout also
    /// agrees. Without this control the positive could be passing for the wrong reason (e.g. a
    /// predicate that only ever looks at declaration index would also accept the reordered pair).
    #[test]
    fn layout_agrees_on_matching_declaration_order_layout() {
        let (am, bm) = (q1_m("a", q1_declaration_order(0)), q1_m("b", q1_declaration_order(0)));
        assert!(struct_layout_agrees(
            &am,
            &bm,
            &Ty::Struct(StructId::new(0)),
            &Ty::Struct(StructId::new(0)),
            MAX_STRUCT_DEPTH
        ));
    }

    /// And the two are NOT interchangeable: a reordered layout against a declaration-order one is
    /// the real cross-producer hazard, and it must be refused.
    #[test]
    fn layout_refuses_reordered_against_declaration_order() {
        let (am, bm) = (q1_m("a", q1_reordered(0)), q1_m("b", q1_declaration_order(0)));
        assert!(!struct_layout_agrees(
            &am,
            &bm,
            &Ty::Struct(StructId::new(0)),
            &Ty::Struct(StructId::new(0)),
            MAX_STRUCT_DEPTH
        ));
    }

    /// `None` OFFSET NEGATIVE: an absent layout fact is exactly the case where the two producers
    /// were free to choose differently, so it must fail CLOSED rather than be treated as "same".
    #[test]
    fn layout_refuses_missing_field_offset() {
        let mut without = q1_reordered(0);
        without.fields[0].offset = None;
        let (am, bm) = (q1_m("a", q1_reordered(0)), q1_m("b", without));
        assert!(!struct_layout_agrees(
            &am,
            &bm,
            &Ty::Struct(StructId::new(0)),
            &Ty::Struct(StructId::new(0)),
            MAX_STRUCT_DEPTH
        ));
        // ... and symmetrically when BOTH sides are missing it: equal-but-unproven is still
        // unproven. This is the case a naive `a.offset == b.offset` would wrongly accept.
        let (mut la, mut lb) = (q1_reordered(0), q1_reordered(0));
        la.fields[0].offset = None;
        lb.fields[0].offset = None;
        assert!(!struct_layout_agrees(
            &q1_m("a", la),
            &q1_m("b", lb),
            &Ty::Struct(StructId::new(0)),
            &Ty::Struct(StructId::new(0)),
            MAX_STRUCT_DEPTH
        ));
    }

    /// OFF-BY-ONE-BYTE NEGATIVE: a single byte of disagreement changes what a store/load
    /// round-trip reads back, so it is a refusal, not a rounding difference.
    #[test]
    fn layout_refuses_off_by_one_byte_offset() {
        let mut shifted = q1_reordered(0);
        shifted.fields[0].offset = Some(9);
        let (am, bm) = (q1_m("a", q1_reordered(0)), q1_m("b", shifted));
        assert!(!struct_layout_agrees(
            &am,
            &bm,
            &Ty::Struct(StructId::new(0)),
            &Ty::Struct(StructId::new(0)),
            MAX_STRUCT_DEPTH
        ));
    }

    /// NESTED DEPTH-2 NEGATIVE: the disagreement is one level down, invisible to any check that
    /// compares only the outer def's own size/align/offsets (both outers are identical here).
    #[test]
    fn layout_refuses_nested_depth_2_mismatch() {
        let inner_a = q1_sdef(
            1,
            "Inner",
            vec![q1_field("x", Ty::U32, Some(0)), q1_field("y", Ty::U32, Some(4))],
            Some(8),
            Some(4),
            StructRepr::Rust,
        );
        let mut inner_b = inner_a.clone();
        inner_b.fields[1].offset = Some(5); // one byte down, two levels deep
        let outer = |_id: u32| {
            q1_sdef(
                0,
                "Outer",
                vec![q1_field("i", Ty::Struct(StructId::new(1)), Some(0))],
                Some(8),
                Some(4),
                StructRepr::Rust,
            )
        };
        let mut am = Module::new("a");
        am.add_struct(outer(0));
        am.add_struct(inner_a);
        let mut bm = Module::new("b");
        bm.add_struct(outer(0));
        bm.add_struct(inner_b);
        assert!(!struct_layout_agrees(
            &am,
            &bm,
            &Ty::Struct(StructId::new(0)),
            &Ty::Struct(StructId::new(0)),
            MAX_STRUCT_DEPTH
        ));
    }

    /// `repr(packed)` NEGATIVE: same field list and same names, different representation — which
    /// is precisely a different byte layout. `repr` is part of the ABI contract, not a hint.
    #[test]
    fn layout_refuses_repr_packed_against_rust() {
        let packed = q1_sdef(
            0,
            "S",
            vec![q1_field("a", Ty::U8, Some(0)), q1_field("b", Ty::U64, Some(1))],
            Some(9),
            Some(1),
            StructRepr::Packed(1),
        );
        let (am, bm) = (q1_m("a", q1_declaration_order(0)), q1_m("b", packed));
        assert!(!struct_layout_agrees(
            &am,
            &bm,
            &Ty::Struct(StructId::new(0)),
            &Ty::Struct(StructId::new(0)),
            MAX_STRUCT_DEPTH
        ));
    }

    /// Field IDENTITY, not merely field shape: two same-typed fields transposed by NAME keep every
    /// offset, size and align equal. This is the `MemoryRegion { AllocationId, usize, usize }`
    /// hazard the by-value gate names, at the layout level.
    #[test]
    fn layout_refuses_transposed_same_typed_field_names() {
        let a = q1_sdef(
            0,
            "R",
            vec![q1_field("offset", Ty::U64, Some(0)), q1_field("len", Ty::U64, Some(8))],
            Some(16),
            Some(8),
            StructRepr::Rust,
        );
        let b = q1_sdef(
            0,
            "R",
            vec![q1_field("len", Ty::U64, Some(0)), q1_field("offset", Ty::U64, Some(8))],
            Some(16),
            Some(8),
            StructRepr::Rust,
        );
        assert!(!struct_layout_agrees(
            &q1_m("a", a),
            &q1_m("b", b),
            &Ty::Struct(StructId::new(0)),
            &Ty::Struct(StructId::new(0)),
            MAX_STRUCT_DEPTH
        ));
    }

    // ---- the lane mechanism itself -------------------------------------------------

    /// `fn(ptr) -> i32 { *ptr }` — the Slice-A shape: the param is used ONLY as a plain load ptr.
    fn q1_deref_entry(module: &mut Module) -> FuncId {
        let sig = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::Ptr));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_results(vec![ValueId::new(1)]),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
        let id = FuncId::new(u32::try_from(module.functions.len()).unwrap());
        let mut f = Function::new(id, "deref", sig, trust_ir::BlockId::new(0));
        f.blocks = vec![block];
        module.add_function(f);
        id
    }

    #[test]
    fn pointee_type_is_recovered_from_a_sole_plain_load() {
        let mut module = Module::new("m");
        let entry = q1_deref_entry(&mut module);
        let f = module.function_by_id(entry).unwrap();
        assert_eq!(sole_pointee_load(f, 0).unwrap(), Some(Ty::I32));
    }

    /// The pointer must be a pure conduit: any use that observes the POINTER itself refuses.
    #[test]
    fn pointee_recovery_refuses_a_pointer_that_escapes() {
        let mut module = Module::new("m");
        let sig = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::Ptr));
        // A PtrToInt observes the address, whose value is an allocation-order artifact.
        block.body.push(
            InstrNode::new(Inst::Cast {
                op: trust_ir::CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::I64,
                operand: ValueId::new(0),
            })
            .with_results(vec![ValueId::new(1)]),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
        let id = FuncId::new(0);
        let mut f = Function::new(id, "escapes", sig, trust_ir::BlockId::new(0));
        f.blocks = vec![block];
        module.add_function(f);
        let f = module.function_by_id(id).unwrap();
        assert_eq!(sole_pointee_load(f, 0).unwrap(), None);
    }

    /// END-TO-END: the wrapper actually materializes the referent and the entry reads it back.
    /// This is the whole lane in one assertion — if `execute_callee` did not share `state.memory`,
    /// or the wrapper's signature were unregistered, this is where it would fail.
    #[test]
    fn wrapper_materializes_a_referent_the_entry_can_load() {
        let mut module = Module::new("m");
        let entry = q1_deref_entry(&mut module);
        let sig = module.func_type(module.function_by_id(entry).unwrap().ty).unwrap().clone();
        let (wrapped, wrapper, wsig) =
            build_pointee_wrapper(&module, entry, &sig, 0, &Ty::I32).unwrap();
        assert_eq!(wsig.params, vec![Ty::I32]);

        for probe in [0i128, 1, -1, i32::MAX as i128] {
            let out = Interpreter::with_module(&wrapped)
                .execute_func(wrapper, vec![Q1Value::int(Ty::I32, probe).unwrap()])
                .expect("wrapper executes");
            assert_eq!(out.returns, vec![Q1Value::int(Ty::I32, probe).unwrap()]);
        }
    }

    /// The wrapper must be registered in the func-type table, or the interpreter hard-errors
    /// `signature_mismatch` on EVERY body. Pinned as a behaviour, not a comment.
    #[test]
    fn wrapper_signature_is_registered() {
        let mut module = Module::new("m");
        let entry = q1_deref_entry(&mut module);
        let sig = module.func_type(module.function_by_id(entry).unwrap().ty).unwrap().clone();
        let (wrapped, wrapper, _) =
            build_pointee_wrapper(&module, entry, &sig, 0, &Ty::I32).unwrap();
        let f = wrapped.function_by_id(wrapper).unwrap();
        assert!(wrapped.func_type(f.ty).is_some(), "wrapper signature must be registered");
    }

    /// The wrapper's id must be PROVABLY ABSENT, and `functions.len()` does not establish that.
    /// A `FuncId` in this producer is a rustc `DefIndex`, so the id space is SPARSE: this is the
    /// exact collision shape — body at 0, one callee at 2, `len() == 2`. A wrapper minted at
    /// `len()` would take the callee's id, and `function_by_id` resolves index-first, so the
    /// callee's own call would dispatch to the wrapper.
    #[test]
    fn wrapper_id_does_not_collide_in_a_sparse_id_space() {
        let mut module = Module::new("m");
        let entry = q1_deref_entry(&mut module);
        let csig =
            module.add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false });
        let sparse = FuncId::new(2);
        let mut callee = Function::new(sparse, "callee", csig, trust_ir::BlockId::new(0));
        let mut cb = Block::new(trust_ir::BlockId::new(0));
        cb.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        callee.blocks = vec![cb];
        module.add_function(callee);
        assert_eq!(module.functions.len(), 2, "len() == 2 while the max id is 2: the trap");

        let esig = module.func_type(module.function_by_id(entry).unwrap().ty).unwrap().clone();
        let (wrapped, wid, _) =
            build_pointee_wrapper(&module, entry, &esig, 0, &Ty::I32).unwrap();
        assert_ne!(wid, sparse, "wrapper took an id that is already in use");
        assert_eq!(
            wrapped.function_by_id(sparse).unwrap().name,
            "callee",
            "the pre-existing callee must still resolve to itself"
        );
    }

    /// The debt-discharging assertion: two wrappers built from the same shape agree, and one
    /// built from a different pointee does not.
    #[test]
    fn wrappers_agree_across_identically_shaped_sides() {
        let mut am = Module::new("a");
        let ae = q1_deref_entry(&mut am);
        let asig = am.func_type(am.function_by_id(ae).unwrap().ty).unwrap().clone();
        let mut bm = Module::new("b");
        let be = q1_deref_entry(&mut bm);
        let bsig = bm.func_type(bm.function_by_id(be).unwrap().ty).unwrap().clone();

        let (aw, af, _) = build_pointee_wrapper(&am, ae, &asig, 0, &Ty::I32).unwrap();
        let (bw, bf, _) = build_pointee_wrapper(&bm, be, &bsig, 0, &Ty::I32).unwrap();
        assert!(
            wrappers_agree(
                aw.function_by_id(af).unwrap(),
                ae,
                bw.function_by_id(bf).unwrap(),
                be
            )
            .is_ok()
        );

        // A different referent type is a different program, and must be caught.
        let (cw, cf, _) = build_pointee_wrapper(&bm, be, &bsig, 0, &Ty::I64).unwrap();
        assert!(
            wrappers_agree(
                aw.function_by_id(af).unwrap(),
                ae,
                cw.function_by_id(cf).unwrap(),
                be
            )
            .is_err()
        );
    }
}
