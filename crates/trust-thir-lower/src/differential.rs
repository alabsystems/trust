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

use std::collections::{HashMap, HashSet};

use rustc_middle::mir;
use rustc_middle::ty::{TyCtxt, TypeVisitableExt};
use rustc_span::def_id::LocalDefId;
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::value::GlobalId;
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
}

/// Trust (B9-A): is this body DEFERRED to the crate-finalize seam differential? Clean (no
/// unsupported shapes, no pending consts) but call-bearing — the per-body module carries its
/// callees as bodyless declarations, so interpretation must wait until the crate module links
/// them. The SINGLE source of truth for both the hook's event suppression and record()'s
/// deferred flag (must-fix 5: if suppression and deferral diverged, the scorecard's
/// first-event-wins would drop seam verdicts).
pub fn deferred_to_seam(thir_side: &Lowered) -> bool {
    thir_side.unsupported.is_empty()
        && thir_side.pending_consts.is_empty()
        && thir_side.contains_call
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

    // (0.25) Pending-const guard. A LOCAL const the hook could not safely evaluate (reentrancy)
    //        left a placeholder `Inst::Const { value: Constant::PhantomData }` in the module,
    //        to be patched by the crate finalizer (see `Lowered::pending_consts`). A placeholder
    //        is NEVER interpreted — executing it would manufacture a false TypeError-vs-value
    //        divergence verdict against THIR — so the body is a precise coverage-only skip.
    if !thir_side.pending_consts.is_empty() {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.notes.push(format!(
            "pending local const: {} placeholder(s) awaiting finalizer eval; \
             never interpreted (coverage-only skip)",
            thir_side.pending_consts.len()
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

    // (0.5) Cross-module call guard. A direct call lowers to `Inst::Call { callee }` whose callee
    //       FuncId lives in another (single-function) module, so the interpreter cannot resolve it.
    //       We cannot assert interpretation-equivalence for such bodies; skip as coverage-only and
    //       do not even build the oracle (both sides would merely error at the call — a vacuous
    //       "agreement" we refuse to report as a verdict).
    if thir_side.contains_call {
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
    let (undef_class, undef_trace) = classify_undefs_traced(&oracle);
    let oracle: Module = match undef_class {
        UndefClass::None => oracle,
        UndefClass::DeadSeeds => substitute_dead_seeds(oracle),
        UndefClass::Live => {
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

    // Trust (B9-A): the per-body path delegates to the entry-parameterized core below.
    let mut tail = compare_entries(&thir_side.module, FuncId::new(0), &oracle, FuncId::new(0));
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

fn first_unmodeled_observation(module: &Module, entry: FuncId) -> Option<String> {
    let mut pending = vec![entry];
    let mut seen = HashSet::new();

    while let Some(func_id) = pending.pop() {
        if !seen.insert(func_id) {
            continue;
        }
        let Some(func) = module.function_by_id(func_id) else {
            return Some(format!("reachable function {func_id:?} is missing from the module"));
        };
        if func.blocks.is_empty() {
            return Some(format!("reachable function `{}` has no executable body", func.name));
        }

        // Trust: a `mut` scalar-enum local reassigned across >=2 blocks is promoted to a
        // PRIVATE non-escaping stack slot by the faithful-MIR oracle (Alloca+Store+Load),
        // while the direct-THIR producer keeps it in SSA. Such a slot has no observable
        // address identity and no observable final memory — the return/trap sample already
        // characterizes it fully — so it must NOT degrade the pair to coverage-only NotRun.
        let private_slots = private_nonescaping_slots(func);

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

                    // Address/allocation identity and final memory are absent even though these
                    // result-producing instructions are not all DCE-style observable effects.
                    Inst::GlobalAddr { .. } => {
                        return Some(format!(
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
                        return Some(format!(
                            "reachable function `{}` materializes allocation/provenance state",
                            func.name
                        ));
                    }
                    Inst::Const { value, .. }
                        if constant_materializes_uncomparable_identity(value) =>
                    {
                        return Some(format!(
                            "reachable function `{}` materializes callable/symbol identity",
                            func.name
                        ));
                    }
                    Inst::Cast { op: CastOp::ReifyFnPointer, .. } => {
                        return Some(format!(
                            "reachable function `{}` reifies module-local callable identity",
                            func.name
                        ));
                    }

                    // Trust: a store INTO a private non-escaping slot writes memory no
                    // observer can read; every other store still fails closed below.
                    Inst::Store { ptr, .. } if private_slots.contains(ptr) => continue,

                    // Central TrustIR predicate: stores, atomics, volatile loads, indirect/opaque
                    // calls, coroutine/EH effects, permission/ARC changes, and future effectful
                    // instructions all fail closed without duplicating an inevitably stale list.
                    inst if inst.has_observable_effects() => {
                        return Some(format!(
                            "reachable function `{}` contains observable state not carried by the interpreter outcome",
                            func.name
                        ));
                    }
                    _ => {}
                }
            }
        }
    }

    None
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
    let mut classes: Vec<ParamClass> = Vec::with_capacity(thir_sig.params.len());
    for (i, t) in thir_sig.params.iter().enumerate() {
        if is_interpretable_scalar(t) {
            classes.push(ParamClass::Scalar);
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
    let scalar_params =
        classes.iter().filter(|c| matches!(c, ParamClass::Scalar | ParamClass::Enum)).count();
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

    // (6) Sample space: cross-product of per-SCALAR-param boundary+mid values (one empty
    //     tuple when every param is opaque or there are none); opaque params contribute one
    //     placeholder each, outside the product.
    // Trust (B3/E6): enum params contribute an INDEX-ENCODED column (0..samples.len())
    // over a parallel abstract-samples table — the i128 product machinery stays
    // untouched; realization happens per side at the args site.
    let mut enum_samples: Vec<Option<Vec<(usize, Vec<i128>)>>> = vec![None; thir_sig.params.len()];
    let mut per_param: Vec<Vec<i128>> = Vec::new();
    for (i, (t, c)) in thir_sig.params.iter().zip(classes.iter()).enumerate() {
        match c {
            ParamClass::Scalar => per_param.push(sample_values(t)),
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
    let thir_interp = Interpreter::with_module(&thir_module);
    let oracle_interp = Interpreter::with_module(&oracle);
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
        let thir_args = build_side_args(&thir_module, thir_sig, &classes, &enum_samples, &tuple);
        let oracle_args = build_side_args(&oracle, oracle_sig, &classes, &enum_samples, &tuple);
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

        let thir_out = thir_interp.execute_func(thir_entry, args_thir);
        let oracle_out = oracle_interp.execute_func(oracle_entry, args_oracle);

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
    let observation_gap = first_unmodeled_observation(thir_module, thir_entry)
        .map(|why| format!("THIR side: {why}"))
        .or_else(|| {
            first_unmodeled_observation(oracle, oracle_entry)
                .map(|why| format!("MIR oracle side: {why}"))
        });
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
/// the seed type is a tuple/struct aggregate with a spellable zero (`zero_const`); the Undef's
/// result is used EXACTLY ONCE in the whole function; that use is the `aggregate` operand of an
/// `InsertField` in the SAME block (never its `value`); and following the single-use chain
/// linearly, the inserts cover ALL fields — each intermediate chain value again used exactly
/// once, each field covered once — BEFORE the chain value has any other use. The fully-built
/// final value may then be used freely (it is a complete, defined value). Uses are enumerated
/// via `trust_ir::mem2reg::rewrite_inst` — the authoritative match-on-every-variant operand
/// walker (the opaque-param proof's technique) — so call/branch/return/store positions and any
/// future `Inst` variant are covered automatically.
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
/// exists (pointers, enums, everything outside the tuple/struct-of-scalars slice), which fails
/// the dead-seed proof closed. The interpreter materializes `(Ty::Tuple/Struct,
/// Constant::Aggregate)` seeds natively (the producer's own wave-D constant-seed path).
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
/// identical (`x == false` ≡ `!x` ≡ `x ? false : true`); the pinned interpreter evaluates
/// Select natively where its ICmp arm is int-only. Applied to the differential's local oracle
/// copy only.
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
/// so truncation never drops a variant. Enums with zero or more than eight
/// variants fail closed instead of silently omitting a variant.
const MAX_ENUM_SAMPLES: usize = 8;
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
    tuple: &[i128],
) -> Result<Vec<InterpretValue>, String> {
    if classes.len() != sig.params.len() {
        return Err("parameter class table length does not match signature".to_string());
    }
    if enum_samples.len() != sig.params.len() {
        return Err("enum sample table length does not match signature".to_string());
    }
    for (class, slot) in classes.iter().zip(enum_samples) {
        match (class, slot) {
            (ParamClass::Enum, Some(_)) | (ParamClass::Scalar | ParamClass::Opaque, None) => {}
            _ => return Err("enum sample table is not aligned with parameter classes".to_string()),
        }
    }
    let expected_columns = classes
        .iter()
        .filter(|class| matches!(class, ParamClass::Scalar | ParamClass::Enum))
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
    use trust_ir::{EnumDef, EnumId, EnumTagRepr, EnumVariant};

    use super::*;

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
        let tuple = [17, 1, 1];
        let thir_args = build_side_args(
            &thir,
            thir.func_type(thir_sig_id).expect("THIR signature"),
            &classes,
            &samples,
            &tuple,
        )
        .expect("THIR-side recipe");
        let oracle_args = build_side_args(
            &oracle,
            oracle.func_type(oracle_sig_id).expect("oracle signature"),
            &classes,
            &samples,
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
    fn enum_samples_cover_eight_and_reject_nine() {
        let eight = enum_abstract_samples(&tagged_enum_def(EnumId::new(0), 8))
            .expect("eight variants fit the complete-coverage cap");
        assert_eq!(eight.len(), 8);
        assert_eq!(
            eight.iter().map(|(variant, _)| *variant).collect::<Vec<_>>(),
            (0..8).collect::<Vec<_>>()
        );
        assert!(enum_abstract_samples(&tagged_enum_def(EnumId::new(0), 9)).is_none());

        let thir = enum_detector_module("nine_thir", false, 9, false);
        let oracle = enum_detector_module("nine_oracle", true, 9, false);
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
        let rejects =
            |classes: &[ParamClass], tables: &[Option<Vec<(usize, Vec<i128>)>>], tuple: &[i128]| {
                build_side_args(&module, sig, classes, tables, tuple).is_err()
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
        assert_eq!(agreed.samples_checked, 8);

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
        assert_eq!(zero_const(&module, &Ty::Enum(pointer_enum)), None);
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
}
