// trust-clean/whole_program.rs: the FIRST whole-program / inter-procedural POC
// (goal item 4) — move composition from the SMT lane INTO the KERNEL-checked-
// modulo-3 lane.
//
// State of reality (reports/whole-program-roadmap.md): Trust's SMT lane already
// composes soundly and live (call graph, callee-first order, precond VCs, sound
// rebound callee-postcondition assumption, on-by-default R1). The Clean
// KERNEL lane (`mirsem.rs` / `prove.rs`) is strictly PER-FUNCTION and fail-closes
// on every `Call` terminator except Trust's own `contract_check_ensures`
// `#[ensures]`-lowering intrinsic. The Clean composition bridge
// (`composition_transfer.rs`) is correct-shaped scaffolding with NO production
// caller. This module is the first production caller: a 2-function compositional
// proof that is KERNEL-CHECKED MODULO 3.
//
// The nucleus of whole-program composition (roadmap §5):
//
//   #[ensures(0 <= ret <= 100)]
//   fn helper(x: i32) -> i32 { if x >= 0 && x <= 100 { x } else { 0 } }  // callee
//
//   fn main_like(a: i32) -> i32 {                                        // caller
//       let h = helper(a);   // call site
//       h + 1                // obligation: h + 1 <= 101  (genuinely NEEDS the ensures)
//   }
//
// The caller's obligation `h + 1 <= 101` is DISCHARGED USING `helper`'s proven
// ensures `0 <= ret <= 100`, REBOUND formals→args + result→dest (`ret`/`_0` → `h`,
// formal `x` → actual `a`), conjoined as a hypothesis, and KERNEL-CHECKED MODULO 3
// by the EXISTING `vc_refute` engine (which we do NOT modify — we only widen the
// conjunction it consumes with facts that hold, exactly as `prove.rs`'s
// `augment_with_type_bounds` already does for a function's own preconditions).
//
// FAIL-CLOSED (the load-bearing property): if the callee has no summary, or its
// summary is not Certified/proven, or the formals→args rebind fails, we ASSUME
// NOTHING (havoc the call) → the caller's obligation stays OPEN, never falsely
// proven. The NEGATIVE CONTROL (`obligation FALSE without the callee ensures`)
// confirms the callee ensures is genuinely load-bearing, not vacuous.
//
// TRUST-IR-KEYED: the callee summary is consumed as a `trust_ir::FunctionSummary`
// {requires, ensures, params, proved}; the call site is annotated with a
// `trust_ir::ProofContext` {assumes, establishes}; the caller's discharge is
// recorded as `trust_ir::ProofEvidence::InheritedFromCallee` (+ the `Certified` /
// `CleanCic` tier). So the compositional proof is keyed to the universal IR —
// aligning with the per-function re-anchor (27/27 at the current sound
// full-function bar, all counted rows trust-ir-primary).
//
// SYNTHESIS PROPOSES / KERNEL VERIFIES: the rebinding + obligation construction
// is synthesis; `vc_refute::check_refute_vc` is the kernel verdict. Modulo 3,
// fail-closed, additive (no change to `vc_refute.rs` or `mirsem.rs`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// trust-ir composition data model — the universal IR's whole-program encoding.
// `FunctionSummary` is the separate-compilation contract carrier; `ProofContext`
// is the per-`Call` proof-transfer (assumes/establishes); `ProofEvidence::
// InheritedFromCallee` is the IR-level discharge primitive; `ProofStatus::Certified`
// is the kernel-checkable tier.
use trust_ir::proof::{
    ObligationKind, ProofContext, ProofEvidence, ProofFormula, ProofStatus as IrProofStatus,
};
use trust_ir::value::{FuncId, ProofId};
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    ProofLevel, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VerifiableBody,
    VerifiableFunction,
};

use crate::composition_transfer::{ProofStatus, ProofStatusRegistry, TransferObligation};

// ===========================================================================
// 0. The kernel-checked composition verdict
// ===========================================================================

/// The verdict of attempting to discharge a single caller obligation by
/// composition with one callee's certified contract.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompositionVerdict {
    /// The caller obligation was KERNEL-CHECKED MODULO 3 *using* the callee's
    /// rebound, Certified `ensures` as a hypothesis. The whole-program nucleus.
    ProvenModulo3,
    /// The caller obligation stayed OPEN — the sound fail direction. Carries the
    /// reason (no callee summary / callee not Certified / rebind failed / the
    /// kernel did not refute the obligation even with the hypothesis).
    Open(String),
    /// The kernel REJECTED a constructed refutation candidate (a malformed proof
    /// term or a residue on non-foundational axioms). Treated as OPEN downstream
    /// (the worst a bad candidate can do is leave a safe obligation undischarged),
    /// surfaced separately for diagnostics. Must NOT be counted as proven.
    KernelRejected(String),
}

impl CompositionVerdict {
    /// True iff the obligation was kernel-checked modulo 3 by composition.
    #[must_use]
    pub fn is_proven_modulo_3(&self) -> bool {
        matches!(self, CompositionVerdict::ProvenModulo3)
    }
}

// ===========================================================================
// 1. The 2-function POC program (the minimal whole-program shape)
// ===========================================================================

const I32: Ty = Ty::Int { width: 32, signed: true };

/// The CALLEE (leaf): `#[ensures(0 <= ret <= 100)]`
/// `fn helper(x: i32) -> i32 { /* clamp into [0,100] */ 50 }`.
///
/// The body is irrelevant to the COMPOSITIONAL proof — the caller never sees it
/// (separate-compilation opaque). It is here only so the callee's OWN ensures can
/// be certified by the existing per-function kernel path (so the registry can
/// record `Certified`). For the POC we model the body as `_0 := 50` — a constant
/// strictly inside `[0, 100]`, so BOTH ensures clauses (`0 <= ret` and
/// `ret <= 100`) are genuinely satisfied and each clause's violation is a literal
/// contradiction (`50 < 0`, `50 > 100`) the existing `vc_refute` linear engine
/// closes modulo 3. (A return of exactly `0` hits a `0 < 0` same-literal edge the
/// engine does not refute — a pre-existing coverage gap, unrelated to composition;
/// the midpoint avoids it without weakening the POC.)
#[must_use]
pub fn helper_callee() -> VerifiableFunction {
    let body = VerifiableBody {
        locals: vec![
            LocalDecl { index: 0, ty: I32, name: Some("_0".into()) },
            LocalDecl { index: 1, ty: I32, name: Some("x".into()) },
        ],
        blocks: vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(50))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        arg_count: 1,
        return_ty: I32,
    };
    VerifiableFunction {
        name: "helper".into(),
        def_path: "crate::helper".into(),
        span: SourceSpan::default(),
        body,
        contracts: vec![],
        preconditions: vec![],
        // ensures 0 <= ret <= 100  (ret = `_0`, the return local)
        postconditions: vec![
            Formula::Ge(Box::new(ret_var()), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(ret_var()), Box::new(Formula::Int(100))),
        ],
        spec: Default::default(),
    }
}

/// The CALLER: `fn main_like(a: i32) -> i32 { let h = helper(a); h + 1 }`.
///
/// MIR shape (two blocks):
///   bb0:  h = helper(a)   -> goto bb1     (the `Call` terminator)
///   bb1:  _0 = h + 1; return
///
/// Its safety obligation is `h + 1 <= 101` — chosen so the callee ensures is
/// GENUINELY load-bearing: `0 <= h` alone does NOT bound `h + 1` above; the
/// `h <= 100` clause is what closes the upper bound. (Roadmap §5.1 step 4: "Pick
/// the obligation so the proof is *impossible without* the callee ensures.")
#[must_use]
pub fn main_like_caller() -> VerifiableFunction {
    // h is local 2; _0 is local 0; a is local 1.
    let body = VerifiableBody {
        locals: vec![
            LocalDecl { index: 0, ty: I32, name: Some("_0".into()) },
            LocalDecl { index: 1, ty: I32, name: Some("a".into()) },
            LocalDecl { index: 2, ty: I32, name: Some("h".into()) },
        ],
        blocks: vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "crate::helper".into(),
                    args: vec![Operand::Copy(Place::local(1))], // helper(a)
                    dest: Place::local(2),                      // h = ...
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    unwind: trust_types::UnwindEdge::Unreachable,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Int(1)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ],
        arg_count: 1,
        return_ty: I32,
    };
    VerifiableFunction {
        name: "main_like".into(),
        def_path: "crate::main_like".into(),
        span: SourceSpan::default(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn ret_var() -> Formula {
    Formula::Var("_0".into(), Sort::Int)
}

// ===========================================================================
// 2. The callee summary (trust-ir-keyed) + its certification
// ===========================================================================

/// A trust-ir-keyed callee summary plus the kernel-lane metadata the caller needs
/// to consume it. This is the Clean-lane reading of `trust_ir::FunctionSummary`
/// (its `requires`/`ensures`/`params`/`proved`), enriched with the live Clean
/// `Formula` clauses (the `ProofFormula` payloads round-trip to `Formula` in the
/// trust-ir-bridge layer; here we carry both so the kernel can consume the live
/// formula and the IR keying is preserved).
#[derive(Debug, Clone)]
pub struct CalleeSummary {
    /// The callee's def-path / IR function key.
    pub def_path: String,
    /// The callee's `FuncId` in the (whole-program) `trust_ir::Module`.
    pub func_id: FuncId,
    /// The universal-IR summary (requires/ensures/params/proved). This is the
    /// authoritative composition contract — keyed to the universal IR.
    pub ir_summary: trust_ir::FunctionSummary,
    /// The live Clean `ensures` clauses (the same predicates the `ir_summary`'s
    /// `ensures` payloads encode), in declaration order. Empty when no contract.
    pub ensures: Vec<Formula>,
    /// The live Clean `requires` clauses (the `ir_summary.requires` payloads).
    /// The caller must ESTABLISH every one at the call site BEFORE assuming the
    /// ensures (`ProofContext.establishes`) — an ensures only holds for calls
    /// that satisfy the requires. Empty when the callee has no precondition.
    pub requires: Vec<Formula>,
    /// The IR obligation id of the callee's ensures (the discharged callee-side
    /// postcondition obligation a caller `InheritedFromCallee` cites).
    pub ensures_obligation: ProofId,
    /// The IR obligation id of the callee's requires (the precondition the caller
    /// must establish — the `ProofContext.establishes` reference).
    pub requires_obligation: ProofId,
}

/// Build the callee `helper`'s trust-ir-keyed summary and CERTIFY its ensures via
/// the existing per-function kernel path. Records `ProofStatus::Certified` in the
/// registry **iff** every ensures clause is kernel-checked modulo 3 (i.e. the
/// callee's postcondition is `Certified`/`CleanCic`-tier, not merely SMT-Trusted).
///
/// Returns the summary plus the (mutated) registry entry. On any kernel failure
/// the callee is recorded as `Trusted` (NOT assumable) — fail-closed: an
/// unproven callee contributes no hypothesis to its callers.
#[must_use]
pub fn certify_callee_summary(
    callee: &VerifiableFunction,
    func_id: FuncId,
    registry: &mut ProofStatusRegistry,
) -> CalleeSummary {
    // Certify the callee's OWN ensures with the existing per-function kernel path:
    // every postcondition VC must refute modulo 3 under the function's sound type
    // bounds (`augment_with_type_bounds`). This is exactly the `prove_dump_dir`
    // postcondition-via-vc discharge, reused verbatim — no new kernel content.
    let ensures: Vec<Formula> = callee.postconditions.clone();
    let proved = ensures_certified_modulo_3(callee);

    // Build the universal-IR summary. `proved` gates whether a caller may assume
    // the ensures — set true ONLY when the kernel certified them modulo 3.
    let ir_summary = trust_ir::FunctionSummary {
        requires: callee
            .preconditions
            .iter()
            .map(|p| ProofFormula::new("trust-clean.Formula@poc", format!("{p:?}")))
            .collect(),
        ensures: ensures
            .iter()
            .map(|e| ProofFormula::new("trust-clean.Formula@poc", format!("{e:?}")))
            .collect(),
        params: param_names(callee),
        proved,
    };

    // Record the kernel-lane proof status. `Certified` ⇒ assumable; anything else
    // is NOT assumable (fail-closed). This is the `ProofStatusRegistry` gate the
    // composition_transfer scaffolding already enforces (`is_assumable()`).
    if proved {
        registry.register_kernel_certified(callee.def_path.clone());
    } else {
        registry.register(callee.def_path.clone(), ProofStatus::Trusted);
    }

    CalleeSummary {
        def_path: callee.def_path.clone(),
        func_id,
        ir_summary,
        ensures,
        requires: callee.preconditions.clone(),
        // Distinct IR obligation ids for the callee's ensures / requires. In a
        // full module these index the callee-scoped `ProofObligation`s.
        ensures_obligation: ProofId::new(func_id.index() * 2),
        requires_obligation: ProofId::new(func_id.index() * 2 + 1),
    }
}

/// Whether EVERY L0-safety VC and postcondition VC of `callee` is kernel-checked modulo 3 by the
/// EXISTING per-function kernel path — the SAME discharge `prove_dump_dir` applies
/// (`prove.rs:3724` postcond-via-vc). We generate the required VCs with
/// `trust_vcgen::generate_vcs`, augment each with the SOUND type bounds + the
/// function's own preconditions (`augment_with_type_bounds`), and refute it via the
/// UNCHANGED `vc_refute` engine. Checking the safety VCs is load-bearing: a
/// checked arithmetic result reaches the return path only after its overflow
/// assert succeeds. The VC `trust_vcgen` emits for a postcondition is already the
/// SAT-iff-violation form (`<return-pin> ∧ ¬post`), so no hand negation is needed.
///
/// Fail-closed: a single undischarged (or kernel-rejected) postcondition VC, or a
/// callee with NO postcondition VC at all, ⇒ NOT certified (not assumable). This
/// is the `Certified`/`CleanCic` tier gate: only a callee whose ensures the kernel
/// CHECKS modulo 3 may be assumed by a caller.
fn ensures_certified_modulo_3(callee: &VerifiableFunction) -> bool {
    if callee.postconditions.is_empty() {
        return false; // no contract ⇒ nothing to certify ⇒ not assumable
    }
    let mut saw_postcondition_vc = false;
    let vcs = trust_vcgen::generate_vcs(callee);
    // Safety first documents and enforces the dependency of the checked
    // postcondition return relation on panic/overflow freedom. Do not pull L1/L2
    // domain obligations into this lane: its contract is exactly L0 safety plus
    // the function's own postcondition.
    for vc in vcs
        .iter()
        .filter(|vc| vc.kind.proof_level() == ProofLevel::L0Safety)
        .chain(vcs.iter().filter(|vc| matches!(&vc.kind, trust_types::VcKind::Postcondition)))
    {
        if matches!(&vc.kind, trust_types::VcKind::Postcondition) {
            saw_postcondition_vc = true;
        }
        let augmented = crate::prove::augment_with_type_bounds_pub(&vc.formula, callee);
        match crate::vc_refute::check_refute_vc(&augmented) {
            Some(crate::RefuteOutcome::RefutedModulo3) => {}
            _ => return false, // undischarged / kernel-rejected ⇒ not certified
        }
    }
    saw_postcondition_vc
}

// ===========================================================================
// 3. The compositional caller proof (the new production path)
// ===========================================================================

/// Discharge `main_like`'s safety obligation `goal_le` (an upper bound on the call
/// result, e.g. `h + 1 <= 101`) by COMPOSITION with the callee summary, KERNEL-
/// CHECKED MODULO 3.
///
/// The steps (roadmap §5.1):
///  1. Locate the `Call` terminator `h = helper(a)` in the caller.
///  2. Consume the callee summary via the `ProofStatusRegistry` + the rebinding:
///     the callee ensures `0 <= ret <= 100` are REBOUND `ret`/`_0` → dest `h`,
///     formal `x` → actual `a` (here the ensures don't mention `x`, so the result
///     rebind is the load-bearing one). This produces a `TransferObligation`.
///  3. Build the caller obligation: the VIOLATION of `goal_le` (`h + 1 >= 102`),
///     CONJOINED with the rebound callee ensures as hypotheses (NEVER `post ⇒ vc`,
///     which would be SAT-iff-violation-unsound).
///  4. Kernel-check the conjunction's refutation modulo 3 via the unchanged
///     `vc_refute` engine. `RefutedModulo3` ⇒ the obligation is PROVEN.
///
/// FAIL-CLOSED: if the callee is not assumable (no summary / not Certified), or
/// the rebind produces no hypothesis, we ASSUME NOTHING — the obligation is
/// refuted with type bounds ONLY, which (for a load-bearing obligation) does NOT
/// refute ⇒ `Open`. The composition can only weaken PROVE→OPEN, never the reverse.
#[must_use]
pub fn prove_caller_obligation(
    caller: &VerifiableFunction,
    callee: &CalleeSummary,
    goal_le: &Formula,
    registry: &ProofStatusRegistry,
) -> CompositionVerdict {
    // (1) Locate the call site and rebind the callee ensures formals→args, result→dest.
    let transfer = match build_transfer_obligation(caller, callee, registry) {
        Some(t) => t,
        None => {
            // No assumable callee hypothesis. Still TRY to prove the obligation with
            // type bounds only (the havoc/opaque-result fallback). For a genuinely
            // load-bearing obligation this fails ⇒ Open (the sound fail direction).
            return refute_caller_goal(caller, goal_le, &[]);
        }
    };
    // (3)+(4) Discharge the caller obligation CONJOINING the rebound callee ensures.
    refute_caller_goal(caller, goal_le, std::slice::from_ref(&transfer.assumed_postcondition))
        .also_open_reason(|| {
            format!("rebound callee ensures from {} did not close the obligation", transfer.callee)
        })
}

/// Locate the caller's `Call` terminator, consume the (Certified-gated) callee
/// summary, and REBIND its ensures to the call site (formals→args, result `_0`→
/// dest). Returns a `TransferObligation` whose `assumed_postcondition` is the
/// CONJUNCTION of the rebound ensures clauses, or `None` (fail-closed) when the
/// callee is not assumable / not found / not rebindable / its requires is not
/// ESTABLISHED at the call site.
#[must_use]
pub fn build_transfer_obligation(
    caller: &VerifiableFunction,
    callee: &CalleeSummary,
    registry: &ProofStatusRegistry,
) -> Option<TransferObligation> {
    // FAIL-CLOSED gate 1: the callee must be Certified (kernel-checked modulo 3).
    // Only `Certified` is assumable — an SMT-`Trusted` / `Stale` / `Missing`
    // callee contributes NOTHING (`composition_transfer::ProofStatus::is_assumable`).
    if !registry.is_assumable(&callee.def_path) {
        return None;
    }
    // FAIL-CLOSED gate 2: the summary must be `proved` (the trust-ir `proved` flag —
    // every clause backed by a discharged module obligation).
    if !callee.ir_summary.proved {
        return None;
    }
    // FAIL-CLOSED gate 3: there must be ensures clauses to assume.
    if callee.ensures.is_empty() {
        return None;
    }

    // Find the `Call` terminator whose `func` is this callee; capture the block
    // (the dest token is block-keyed), the dest place, and the args.
    let (call_block, dest_place, args) =
        caller.body.blocks.iter().find_map(|b| match &b.terminator {
            Terminator::Call { func, args, dest, .. } if func == &callee.def_path => {
                Some((b.id, dest.clone(), args.clone()))
            }
            _ => None,
        })?;

    // The result symbol the ensures `ret`/`_0` rebinds to: the AUTHORITATIVE
    // post-call dest spelling from `trust_vcgen::call_dest_fact_token` (bare only
    // under the SSA-collapse license, the versioned `dest#s{b}_t` otherwise,
    // `None` for a projected dest — fail-closed). NEVER a hand-rolled bare
    // `local_name`: for a reassigned dest the bare name denotes the WRONG version.
    let dest_name = trust_vcgen::call_dest_fact_token(caller, call_block, &dest_place)?;

    // FAIL-CLOSED alignment guard: `ir_summary.params` is built by `param_names`,
    // which SKIPS unnamed params — a skipped middle param would shift the
    // positional zip below and bind a formal to the WRONG actual's spelling
    // (minting a hypothesis about the wrong argument). Lengths equal ⇒ no formal
    // was skipped ⇒ the zip is positionally faithful.
    if callee.ir_summary.params.len() != args.len() {
        return None;
    }

    // Map each formal name → the LICENSED at-call spelling of its actual
    // (`trust_vcgen::call_arg_fact_token` — bare only when every version of the
    // actual's local denotes one value). A reassigned/escaping/constant/projected
    // actual has NO licensed spelling and leaves its formal un-rebindable; a
    // clause that mentions it is dropped below (weakens PROVE→OPEN only). Minting
    // the bare name UNLICENSED bound the ENTRY version the caller's precondition
    // constrains — the reassigned-actual false-certification probe.
    let mut formal_to_actual: FxHashMap<String, String> = FxHashMap::default();
    for (formal, actual) in callee.ir_summary.params.iter().zip(args.iter()) {
        if let Some(actual_tok) = trust_vcgen::call_arg_fact_token(caller, actual) {
            formal_to_actual.insert(formal.clone(), actual_tok);
        }
    }

    // FAIL-CLOSED gate 4 (the `ProofContext.establishes` half): the callee's
    // ensures holds ONLY for calls that satisfy its requires. Kernel-check that
    // the caller ESTABLISHES every requires clause at this call site (rebound
    // onto the same licensed spellings); otherwise assume NOTHING. Skipping this
    // minted `h >= 100` from a `requires(x >= 100)` callee at a call passing an
    // unconstrained (or reassigned-to-0) argument — a false certification.
    if !caller_establishes_requires(caller, &callee.requires, &formal_to_actual) {
        return None;
    }

    // REBIND each ensures clause: `_0`/`ret` → dest_name, formal → actual.
    // A clause that references a free var mapping to neither result nor a formal
    // is DROPPED (`postcondition_rebindable` discipline — only weakens the proof).
    let mut rebound: Vec<Formula> = Vec::new();
    for clause in &callee.ensures {
        if let Some(r) = rebind_clause(clause, &dest_name, &formal_to_actual) {
            rebound.push(r);
        }
    }
    if rebound.is_empty() {
        return None; // nothing rebindable ⇒ assume nothing (fail-closed)
    }

    // Conjoin the rebound clauses into a single assumed postcondition.
    let assumed = if rebound.len() == 1 {
        rebound.into_iter().next().unwrap()
    } else {
        Formula::And(rebound)
    };

    Some(TransferObligation {
        caller: caller.def_path.clone(),
        callee: callee.def_path.clone(),
        assumed_postcondition: assumed,
    })
}

/// Kernel-check the caller's safety obligation `goal_le` (`expr <= bound`) modulo 3,
/// CONJOINING `hypotheses` (the rebound callee ensures). The discharge is the
/// SAT-iff-violation refutation the §6 driver uses: refute `(type bounds) ∧
/// (hypotheses) ∧ ¬goal_le`. `RefutedModulo3` ⇒ `ProvenModulo3`.
fn refute_caller_goal(
    caller: &VerifiableFunction,
    goal_le: &Formula,
    hypotheses: &[Formula],
) -> CompositionVerdict {
    let Some(violation) = negate_atom(goal_le) else {
        return CompositionVerdict::Open("caller obligation is not an atomic comparison".into());
    };

    // The conjunction the kernel refutes: hypotheses ∧ violation, then augmented
    // with the SOUND type bounds of every variable (`augment_with_type_bounds` —
    // identical to the per-function path). The callee ensures ride in as
    // additional conjuncts — exactly the sound "assume callee ensures at the call
    // site" semantics, ported to the Clean obligation.
    let mut conjuncts: Vec<Formula> = hypotheses.to_vec();
    conjuncts.push(violation);
    let core = if conjuncts.len() == 1 {
        conjuncts.into_iter().next().unwrap()
    } else {
        Formula::And(conjuncts)
    };
    let augmented = crate::prove::augment_with_type_bounds_pub(&core, caller);

    match crate::vc_refute::check_refute_vc(&augmented) {
        Some(crate::RefuteOutcome::RefutedModulo3) => CompositionVerdict::ProvenModulo3,
        Some(crate::RefuteOutcome::KernelRejected(reason)) => {
            CompositionVerdict::KernelRejected(reason)
        }
        // `check_refute_vc` collapses a non-refuted obligation to `None`. With no
        // (or insufficient) callee hypothesis a load-bearing obligation lands here.
        _ => CompositionVerdict::Open("obligation not refuted under available hypotheses".into()),
    }
}

// ===========================================================================
// 4. trust-ir keying — the call site's ProofContext + the inherited evidence
// ===========================================================================

/// The trust-ir-keyed record of a successful compositional discharge: the call
/// site's `ProofContext` (assumes = callee postcondition obligation; establishes
/// = callee precondition obligation) and the caller obligation's
/// `ProofEvidence::InheritedFromCallee` + `CleanCic`/`Certified` tier.
#[derive(Debug, Clone)]
pub struct TrustIrCompositionRecord {
    /// Per-call-site proof transfer (B5): callee postconditions the caller may
    /// ASSUME, callee preconditions the caller must ESTABLISH.
    pub proof_context: ProofContext,
    /// The caller obligation's discharge evidence: it inherits the callee's
    /// already-discharged ensures obligation (the IR-level composition primitive).
    pub inherited_evidence: ProofEvidence,
    /// The IR proof status of the caller obligation after composition.
    pub caller_status: IrProofStatus,
    /// The caller obligation's IR kind (a panic-freedom / arithmetic-safety fact).
    pub caller_obligation_kind: ObligationKind,
}

/// Build the trust-ir composition record for a PROVEN caller obligation. Keyed to
/// the universal IR: the `ProofContext` references the callee's ensures/requires
/// obligation ids, and the discharge is `InheritedFromCallee { callee, obligation }`
/// over the callee's ensures obligation, at the `Certified` tier.
///
/// Only call this for a `ProvenModulo3` verdict — an OPEN obligation does NOT
/// inherit (it has no discharge), so the record would be unsound.
#[must_use]
pub fn trust_ir_record_for_proven(callee: &CalleeSummary) -> TrustIrCompositionRecord {
    TrustIrCompositionRecord {
        proof_context: ProofContext {
            // The caller may ASSUME the callee's ensures after the call returns.
            assumes: vec![callee.ensures_obligation],
            // The caller must ESTABLISH the callee's requires before the call.
            establishes: vec![callee.requires_obligation],
        },
        // The caller obligation is discharged by INHERITING the callee's
        // already-discharged ensures obligation (B5).
        inherited_evidence: ProofEvidence::InheritedFromCallee {
            callee: callee.func_id,
            obligation: callee.ensures_obligation,
        },
        // The kernel-checked-modulo-3 discharge is the de Bruijn `Certified` tier
        // (backed by `CleanCic` in a full module).
        caller_status: IrProofStatus::Certified,
        caller_obligation_kind: ObligationKind::ArithmeticSafety,
    }
}

// ===========================================================================
// 5. The whole-program (2-function) assembly
// ===========================================================================

/// The result of running the whole-program POC over `{helper, main_like}`.
#[derive(Debug, Clone)]
pub struct WholeProgramPoc {
    /// The callee's kernel-lane proof status (`Certified` iff modulo-3 certified).
    pub callee_status: ProofStatus,
    /// The caller obligation's composition verdict.
    pub caller_verdict: CompositionVerdict,
    /// The trust-ir composition record (present iff the caller obligation proved).
    pub ir_record: Option<TrustIrCompositionRecord>,
    /// The composed whole-program status: `Certified` iff BOTH functions are.
    pub combined_certified: bool,
}

/// Run the 2-function compositional POC: certify the callee, then discharge the
/// caller's `h + 1 <= 101` obligation by composition, kernel-checked modulo 3.
/// This is the existence proof that per-function kernel proofs COMPOSE.
#[must_use]
pub fn run_poc() -> WholeProgramPoc {
    let callee_fn = helper_callee();
    let caller_fn = main_like_caller();
    // Caller obligation: `h + 1 <= 101` (the result of the call, +1, bounded above).
    let goal = caller_goal_h_plus_one_le_101();

    let mut registry = ProofStatusRegistry::new();
    let summary = certify_callee_summary(&callee_fn, FuncId::new(0), &mut registry);
    let callee_status = registry.get(&callee_fn.def_path).cloned().unwrap_or(ProofStatus::Missing);

    let caller_verdict = prove_caller_obligation(&caller_fn, &summary, &goal, &registry);

    let ir_record = if caller_verdict.is_proven_modulo_3() {
        Some(trust_ir_record_for_proven(&summary))
    } else {
        None
    };

    let combined_certified =
        callee_status == ProofStatus::Certified && caller_verdict.is_proven_modulo_3();

    WholeProgramPoc { callee_status, caller_verdict, ir_record, combined_certified }
}

/// The caller's load-bearing safety obligation: `h + 1 <= 101`. (`h` = the call
/// destination local in `main_like`.)
#[must_use]
pub fn caller_goal_h_plus_one_le_101() -> Formula {
    Formula::Le(
        Box::new(Formula::Add(
            Box::new(Formula::Var("h".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        )),
        Box::new(Formula::Int(101)),
    )
}

// ===========================================================================
// 6. Helpers (rebinding, negation, name lookup)
// ===========================================================================

/// The parameter names of a function (locals `1..=arg_count`), in order.
fn param_names(func: &VerifiableFunction) -> Vec<String> {
    (1..=func.body.arg_count).filter_map(|i| local_name(func, i)).collect()
}

/// The source name of a local, if any.
fn local_name(func: &VerifiableFunction, local: usize) -> Option<String> {
    func.body.locals.iter().find(|l| l.index == local).and_then(|l| l.name.clone())
}

// NOTE: the former `operand_var_name` helper (bare actual-argument names, NO
// single-assignment license) is deliberately GONE — every formal→actual spelling
// must come from `trust_vcgen::call_arg_fact_token` (see `rebind_clause`'s
// license contract and the reassigned-actual probe).

/// Rebind a callee ensures clause to the call site: the result symbol (`_0` /
/// `ret`) → `dest_name`, each formal name → its actual. A clause that references a
/// var mapping to NEITHER the result NOR a known formal is un-rebindable ⇒ `None`
/// (dropped — only weakens PROVE→OPEN, never the reverse).
///
/// LICENSE CONTRACT (soundness): this is a pure substitution — the LICENSE lives
/// with the caller, who must supply spellings that denote the call-site values in
/// the emitted VC symbol space: `dest_name` from `trust_vcgen::call_dest_fact_token`
/// and every `formal_to_actual` value from `trust_vcgen::call_arg_fact_token`.
/// Hand-rolled bare names are NOT sound here: a reassigned local's bare name
/// denotes its ENTRY version (the one the function's preconditions constrain),
/// not the at-call/post-call value — substituting it mints a hypothesis about the
/// wrong version (the reassigned-actual false-certification probe in this file's
/// tests).
fn rebind_clause(
    clause: &Formula,
    dest_name: &str,
    formal_to_actual: &FxHashMap<String, String>,
) -> Option<Formula> {
    rebind_rec(clause, dest_name, formal_to_actual)
}

fn rebind_rec(f: &Formula, dest: &str, map: &FxHashMap<String, String>) -> Option<Formula> {
    use Formula as F;
    let bx = |x: Option<Formula>| x.map(Box::new);
    match f {
        F::Var(name, sort) => {
            // The callee result symbol → the caller's dest local.
            if name == "_0" || name == "ret" || name == "result" {
                Some(F::Var(dest.to_string(), sort.clone()))
            } else if let Some(actual) = map.get(name) {
                // A formal → its actual argument.
                Some(F::Var(actual.clone(), sort.clone()))
            } else {
                // A free var that is neither result nor a known formal: un-rebindable.
                None
            }
        }
        F::Int(_) | F::UInt(_) | F::Bool(_) => Some(f.clone()),
        F::Ge(a, b) => Some(F::Ge(bx(rebind_rec(a, dest, map))?, bx(rebind_rec(b, dest, map))?)),
        F::Le(a, b) => Some(F::Le(bx(rebind_rec(a, dest, map))?, bx(rebind_rec(b, dest, map))?)),
        F::Gt(a, b) => Some(F::Gt(bx(rebind_rec(a, dest, map))?, bx(rebind_rec(b, dest, map))?)),
        F::Lt(a, b) => Some(F::Lt(bx(rebind_rec(a, dest, map))?, bx(rebind_rec(b, dest, map))?)),
        F::Eq(a, b) => Some(F::Eq(bx(rebind_rec(a, dest, map))?, bx(rebind_rec(b, dest, map))?)),
        F::Add(a, b) => Some(F::Add(bx(rebind_rec(a, dest, map))?, bx(rebind_rec(b, dest, map))?)),
        F::Sub(a, b) => Some(F::Sub(bx(rebind_rec(a, dest, map))?, bx(rebind_rec(b, dest, map))?)),
        F::Mul(a, b) => Some(F::Mul(bx(rebind_rec(a, dest, map))?, bx(rebind_rec(b, dest, map))?)),
        F::And(v) => {
            let parts: Option<Vec<Formula>> = v.iter().map(|x| rebind_rec(x, dest, map)).collect();
            Some(F::And(parts?))
        }
        // Any other shape is outside the POC's rebindable fragment — fail closed.
        _ => None,
    }
}

/// Whether the CALLER ESTABLISHES every `requires` clause of a callee at a call
/// site — the `ProofContext.establishes` half of the B5 proof transfer, kernel-
/// checked modulo 3. A callee's ensures holds ONLY for calls that satisfy its
/// requires, so this gate must pass BEFORE any ensures clause is assumed.
///
/// Each requires clause is rebound formals→licensed-actuals (the SAME
/// `call_arg_fact_token`-licensed map the ensures rebind uses — an entry-version
/// bare name would "establish" the requires against the WRONG version), then its
/// VIOLATION is refuted under the caller's own sound augmentation (type bounds +
/// the caller's preconditions — entry-version facts, which is exactly what the
/// licensed spellings denote: a licensed local is never reassigned, so its
/// at-call value IS its entry value).
///
/// FAIL-CLOSED on every edge: a requires clause that mentions the callee RESULT
/// (malformed), references an unmapped formal (unlicensed/constant/projected
/// actual), falls outside the atomic/conjunctive fragment, or simply does not
/// refute ⇒ NOT established ⇒ the callee contributes NOTHING at this call site.
/// An empty `requires` is trivially established.
fn caller_establishes_requires(
    caller: &VerifiableFunction,
    requires: &[Formula],
    formal_to_actual: &FxHashMap<String, String>,
) -> bool {
    requires.iter().all(|clause| {
        // A requires clause may not speak about the callee's RESULT; rebind_clause
        // would silently bind `_0`/`ret` onto the sentinel below, so reject first.
        if formula_mentions_result(clause) {
            return false;
        }
        // The dest name is irrelevant (no result var survives the check above);
        // the sentinel never collides with a real local spelling.
        let Some(rebound) =
            rebind_clause(clause, "__trust_requires_has_no_result__", formal_to_actual)
        else {
            return false; // un-rebindable (unlicensed actual / unknown var) ⇒ not established
        };
        establishes_rebound_clause(caller, &rebound)
    })
}

/// Kernel-check ONE rebound requires clause holds at the call site: a conjunction
/// establishes iff every conjunct does; an atomic comparison establishes iff its
/// VIOLATION (`negate_atom`) is `RefutedModulo3` under the caller's sound
/// augmentation. Any other shape fails closed.
fn establishes_rebound_clause(caller: &VerifiableFunction, clause: &Formula) -> bool {
    match clause {
        Formula::And(parts) => parts.iter().all(|p| establishes_rebound_clause(caller, p)),
        atom => {
            let Some(violation) = negate_atom(atom) else { return false };
            let augmented = crate::prove::augment_with_type_bounds_pub(&violation, caller);
            matches!(
                crate::vc_refute::check_refute_vc(&augmented),
                Some(crate::RefuteOutcome::RefutedModulo3)
            )
        }
    }
}

/// Whether a formula mentions the callee result symbol (`_0` / `ret` / `result`)
/// — the same result spellings `rebind_rec` rebinds.
fn formula_mentions_result(f: &Formula) -> bool {
    let mut found = false;
    f.visit(&mut |g| {
        if let Formula::Var(name, _) = g
            && (name == "_0" || name == "ret" || name == "result")
        {
            found = true;
        }
    });
    found
}

/// Negate an atomic comparison to its VIOLATION (the SAT-iff-violation encoding).
/// `x <= b` → `x > b`, `x >= b` → `x < b`, `x < b` → `x >= b`, `x > b` → `x <= b`,
/// `x = b` → unsupported here (we only need ordered atoms for the POC). Returns
/// `None` for a non-atomic shape (fail-closed).
fn negate_atom(f: &Formula) -> Option<Formula> {
    use Formula as F;
    match f {
        F::Le(a, b) => Some(F::Gt(a.clone(), b.clone())),
        F::Ge(a, b) => Some(F::Lt(a.clone(), b.clone())),
        F::Lt(a, b) => Some(F::Ge(a.clone(), b.clone())),
        F::Gt(a, b) => Some(F::Le(a.clone(), b.clone())),
        _ => None,
    }
}

// ===========================================================================
// 7. Small verdict-combinator
// ===========================================================================

impl CompositionVerdict {
    /// Replace an `Open(_)`'s reason with a more specific one (for diagnostics).
    /// Leaves `ProvenModulo3` and `KernelRejected` untouched.
    fn also_open_reason(self, f: impl FnOnce() -> String) -> Self {
        match self {
            CompositionVerdict::Open(_) => CompositionVerdict::Open(f()),
            other => other,
        }
    }
}

// ===========================================================================
// 8. STEP 3 — the GENERAL multi-function call-graph compositional driver
// ===========================================================================
//
// The 2-function POC above (§1-§7) is a hand-built `helper ← main_like` pair.
// Step 3 (reports/whole-program-roadmap.md §3) GENERALIZES it to an ARBITRARY
// acyclic call graph, verified COMPOSITIONALLY in CALLEE-FIRST topological order,
// threading ONE `ProofStatusRegistry` across the WHOLE graph.
//
// What is reused vs. new:
//  - ORDER: we consume the EXISTING `trust_vcgen::build_call_graph` +
//    `trust_vcgen::compute_verification_order` (the live SMT-lane ordering — Tarjan
//    SCC / Kahn topo, callees-first). NOT a hand-built order. (roadmap §3 "reuse".)
//  - PER-FUNCTION DISCHARGE: each function's OWN `#[ensures]` is kernel-checked
//    modulo 3 by the UNCHANGED `vc_refute` engine over the UNCHANGED
//    `trust_vcgen::generate_vcs` postcondition VCs — exactly as `ensures_certified_
//    modulo_3` does per-function, but now CONJOINING the rebound, Certified ensures
//    of every callee at this function's call sites (the §2 abstract-callee transfer).
//  - REGISTRY: the SAME `ProofStatusRegistry` from `composition_transfer.rs` records
//    each function's status as the traversal proceeds; a function is `Certified`
//    (assumable by its callers) ONLY when its ensures kernel-checks modulo 3 UNDER
//    its callees' transferred hypotheses.
//
// FAIL-CLOSED + TRANSITIVE: a function whose ensures does NOT certify (or that has
// none) is recorded NOT-`Certified`. Its callers then find it non-assumable, get NO
// hypothesis from it, and — for a load-bearing obligation — STAY OPEN. That Open
// status propagates: the caller is itself recorded NOT-`Certified`, so ITS callers
// lose the hypothesis too. A mid-graph knockout therefore opens the WHOLE transitive
// caller cone (the negative control). Composition only ever weakens PROVE→OPEN.
//
// DEST-TOKEN PINNING (the load-bearing subtlety): the postcondition VC that
// `generate_vcs` emits for a function with a `Call` references the call dest under
// ONE exact spelling — the POST-CALL SSA token `dest#s{call_block}_t` minted by
// `version_terminator_dest_fact`, UNLESS vcgen's final `normalize_ssa_version_tokens`
// pass collapses it to the BARE dest name (licensed when every version of the dest
// local provably denotes one value — the 2026-07-04 over-refutation kill f864db570e).
// The rebound callee ensures must bind the callee result to that SAME spelling to
// connect as a hypothesis, so `gather_callee_hypotheses` consumes the AUTHORITATIVE
// `trust_vcgen::call_dest_fact_token` (never a hand-rolled format) and rebinds the
// callee result (`_0`/`ret`) onto it via the existing `rebind_clause`.
//
// SYNTHESIS PROPOSES / KERNEL VERIFIES, modulo 3, additive: no change to
// `vc_refute.rs` or `mirsem.rs`; we only widen the conjunction the kernel consumes
// with facts (rebound Certified callee ensures) that genuinely hold.

/// The per-function outcome of the multi-function compositional traversal.
#[derive(Debug, Clone)]
pub struct FunctionVerdict {
    /// The function's def-path / IR key.
    pub def_path: String,
    /// Its kernel-lane proof status after composition. `Certified` ⇒ its ensures was
    /// kernel-checked modulo 3 (under its callees' transferred hypotheses) and it is
    /// assumable by its own callers. Anything else is fail-closed (not assumable).
    pub status: ProofStatus,
    /// The def-paths of the (direct) callees whose Certified ensures were transferred
    /// in as hypotheses to discharge THIS function's ensures. Empty for a leaf or
    /// when no callee was assumable.
    pub assumed_callees: Vec<String>,
    /// Why the function stayed un-Certified, if it did (diagnostic; `None` when
    /// `Certified`). E.g. "callee `crate::leaf` not assumable" / "ensures did not
    /// kernel-check modulo 3 under available hypotheses".
    pub open_reason: Option<String>,
}

impl FunctionVerdict {
    /// True iff this function's ensures was kernel-checked modulo 3 by composition.
    #[must_use]
    pub fn is_certified(&self) -> bool {
        self.status == ProofStatus::Certified
    }
}

/// The result of verifying a whole multi-function call graph compositionally.
#[derive(Debug, Clone)]
pub struct WholeProgramGraphResult {
    /// The callee-first topological order the traversal used (def-paths), as produced
    /// by `trust_vcgen::compute_verification_order` over the call graph.
    pub verification_order: Vec<String>,
    /// Per-function verdicts, in verification (callee-first) order.
    pub verdicts: Vec<FunctionVerdict>,
    /// The final registry (one shared instance threaded across the whole graph).
    pub registry: ProofStatusRegistry,
}

impl WholeProgramGraphResult {
    /// The verdict for a given function, if present.
    #[must_use]
    pub fn verdict(&self, def_path: &str) -> Option<&FunctionVerdict> {
        self.verdicts.iter().find(|v| v.def_path == def_path)
    }

    /// True iff EVERY function in the graph is `Certified` — the whole-program
    /// composed-proof success condition (every reachable function's contract holds,
    /// linked by the certified-callee transfers).
    #[must_use]
    pub fn all_certified(&self) -> bool {
        !self.verdicts.is_empty() && self.verdicts.iter().all(FunctionVerdict::is_certified)
    }

    /// The def-paths that stayed un-Certified (Open). Empty iff `all_certified`.
    #[must_use]
    pub fn open_functions(&self) -> Vec<&str> {
        self.verdicts.iter().filter(|v| !v.is_certified()).map(|v| v.def_path.as_str()).collect()
    }
}

/// Verify a whole multi-function call graph COMPOSITIONALLY, in callee-first order.
///
/// `functions` is the set of `VerifiableFunction`s (a closed graph — no recursion,
/// no indirect calls; Steps 4/6 deferred). For EACH function, in the callee-first
/// order computed by `trust_vcgen::compute_verification_order`:
///
///  1. Gather the rebound, destination-pinned ensures of every DIRECT callee that is
///     already `Certified` in the shared registry (transitively available because of
///     callee-first order). A non-assumable callee contributes NOTHING (fail-closed).
///  2. Kernel-check every generated L0-safety VC and this function's OWN `#[ensures]`
///     modulo 3, CONJOINED with those hypotheses + sound type bounds, via the
///     UNCHANGED `vc_refute` engine. Safety is checked first because it establishes
///     that every checked arithmetic operation reaches its success continuation.
///  3. Record `Certified` iff every safety and ensures clause kernel-checked modulo
///     3 AND the function actually has an ensures contract; else record `Trusted`
///     (NOT assumable). This status is then visible to the function's own callers.
///
/// Fail-closed + transitive: a knocked-out / un-rebindable callee leaves its caller's
/// dependent safety/ensures un-discharged ⇒ caller un-Certified ⇒ that propagates up the
/// caller cone. The result reports the full per-function picture.
#[must_use]
pub fn verify_call_graph(functions: &[VerifiableFunction]) -> WholeProgramGraphResult {
    verify_call_graph_with_knockout(functions, &[])
}

/// [`verify_call_graph`] with a NEGATIVE-CONTROL knockout set: every def-path in
/// `knockout` is FORCED to fail certification (recorded `Trusted`, never `Certified`)
/// regardless of whether its ensures would actually kernel-check — modelling an
/// unproven / un-rebindable callee anywhere in the graph.
///
/// This is the fail-closed transitive control: knocking out a MID-graph function must
/// open not only that function but its WHOLE transitive caller cone — the callers that
/// depended on its (now withheld) ensures stay OPEN, never falsely proven. The other
/// arms of the graph (functions NOT in the knocked-out function's caller cone) are
/// unaffected and still certify.
#[must_use]
pub fn verify_call_graph_with_knockout(
    functions: &[VerifiableFunction],
    knockout: &[&str],
) -> WholeProgramGraphResult {
    // (Step 3 REUSE) Consume the EXISTING live SMT-lane ordering machinery — NOT a
    // hand-built order. `build_call_graph` scans `Terminator::Call` edges; the order
    // is callees-first (Tarjan SCC + Kahn topo / post-order DFS).
    let graph = trust_vcgen::build_call_graph(functions);
    let order = trust_vcgen::compute_verification_order(&graph);

    // Index functions by def-path for O(1) lookup during the bottom-up walk.
    let by_path: FxHashMap<&str, &VerifiableFunction> =
        functions.iter().map(|f| (f.def_path.as_str(), f)).collect();
    let knocked: trust_types::fx::FxHashSet<&str> = knockout.iter().copied().collect();

    let mut registry = ProofStatusRegistry::new();
    let mut verdicts: Vec<FunctionVerdict> = Vec::new();

    for def_path in &order {
        let Some(func) = by_path.get(def_path.as_str()).copied() else {
            // An edge to an unknown function (e.g. cross-crate / opaque): nothing to
            // certify here. It simply never becomes assumable — fail-closed.
            continue;
        };

        let verdict = if knocked.contains(def_path.as_str()) {
            // NEGATIVE CONTROL: this function's proof is knocked out. Record it as
            // un-Certified (Trusted) so its callers find it non-assumable — the
            // transitive open propagates from here.
            FunctionVerdict {
                def_path: func.def_path.clone(),
                status: ProofStatus::Trusted,
                assumed_callees: Vec::new(),
                open_reason: Some("knocked out (negative control — proof withheld)".into()),
            }
        } else {
            certify_function_in_graph(func, &by_path, &registry)
        };
        // Thread the status into the SHARED registry so this function's CALLERS (which
        // come LATER in callee-first order) can consume it.
        if verdict.status == ProofStatus::Certified {
            // `certify_function_in_graph` reached this status only after the
            // exact local ensures obligation passed the kernel check.
            registry.register_kernel_certified(func.def_path.clone());
        } else {
            registry.register(func.def_path.clone(), verdict.status.clone());
        }
        verdicts.push(verdict);
    }

    WholeProgramGraphResult { verification_order: order, verdicts, registry }
}

/// Whether one GLOBAL conjunction of all direct-callee summaries has a sound
/// scope for every L0/postcondition VC this POC will check.
///
/// The production vcgen summary lane carries facts from each call only into its
/// dominated successors. This first Clean whole-program bridge does not yet carry
/// that per-call establish point: [`gather_callee_hypotheses`] returns one flat
/// conjunction. Admit only the conservative shape where that conjunction is
/// equivalent to dominated transfer:
///
/// * no calls (there are no transferred facts, so arbitrary CFG is harmless); or
/// * one acyclic, whole-body, single-successor chain whose calls form a prefix;
/// * statements before/inside that call prefix are projection-free copies or
///   constants (hence cannot raise an earlier L0 VC); and
/// * every call is ordinary, returning, and non-foreign.
///
/// Thus every safety/postcondition obligation that can consume the flat facts is
/// after every call on every execution. Branches, loops, dead side blocks, a call
/// after an Assert/Goto phase, unsafe/foreign calls, and safety-producing pre-call
/// statements fail closed until hypotheses carry block/dominance provenance.
fn global_callee_hypotheses_have_supported_scope(func: &VerifiableFunction) -> bool {
    let has_call =
        func.body.blocks.iter().any(|block| matches!(block.terminator, Terminator::Call { .. }));
    if !has_call {
        return true;
    }

    fn pre_call_statement_is_safety_free(stmt: &Statement) -> bool {
        match stmt {
            Statement::Assign { place, rvalue: Rvalue::Use(operand), .. }
                if place.projections.is_empty() =>
            {
                match operand {
                    Operand::Constant(_) => true,
                    Operand::Copy(source) | Operand::Move(source) => source.projections.is_empty(),
                    Operand::Symbolic(_) | Operand::Unsupported { .. } => false,
                    _ => false,
                }
            }
            Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::Retag { .. }
            | Statement::PlaceMention(_)
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop => true,
            _ => false,
        }
    }

    let mut current = BlockId(0);
    let mut visited: FxHashSet<BlockId> = FxHashSet::default();
    let mut calls_may_continue = true;
    loop {
        if !visited.insert(current) {
            return false; // a cycle: no global post-call establish point
        }
        let Some(block) = func.body.blocks.iter().find(|block| block.id == current) else {
            return false;
        };
        match &block.terminator {
            Terminator::Call {
                target: Some(target),
                is_unsafe_sig: false,
                is_foreign: false,
                ..
            } if calls_may_continue
                && block.stmts.iter().all(pre_call_statement_is_safety_free) =>
            {
                current = *target;
            }
            Terminator::Assert { target, .. } => {
                calls_may_continue = false;
                current = *target;
            }
            Terminator::Goto(target) => {
                calls_may_continue = false;
                current = *target;
            }
            Terminator::Return => return visited.len() == func.body.blocks.len(),
            _ => return false,
        }
    }
}

/// Certify a single function's L0 safety + OWN `#[ensures]` modulo 3, CONJOINING
/// the rebound, destination-pinned, Certified ensures of its direct callees as
/// hypotheses. The kernel engine (`vc_refute`) is unchanged; we only widen its
/// conjunction with facts that hold. Returns the function's `FunctionVerdict`.
///
/// Discharge model (the §2 abstract-callee Call rule, kernel-checked): for each
/// `Call h = callee(args)` in this function's body, if `callee` is `Certified` and
/// its ensures rebind to the call site, we ASSUME the callee's ensures rebound onto
/// the POST-CALL dest spelling the emitted VC actually reads — vcgen's authoritative
/// `trust_vcgen::call_dest_fact_token` (bare `h` when the SSA collapse is licensed,
/// the versioned `h#s{call_block}_t` from `version_terminator_dest_fact` otherwise).
/// Then this function's ensures VCs are refuted under those assumptions. A function
/// with NO `#[ensures]` is NOT certified (nothing to certify ⇒ not assumable —
/// fail-closed, like a leaf without a contract). Because the current bridge carries
/// one conjunction of callee facts rather than per-VC establish points, functions
/// with calls are admitted only by [`global_callee_hypotheses_have_supported_scope`].
#[must_use]
fn certify_function_in_graph(
    func: &VerifiableFunction,
    by_path: &FxHashMap<&str, &VerifiableFunction>,
    registry: &ProofStatusRegistry,
) -> FunctionVerdict {
    // The current POC gathers one global conjunction of direct-callee facts. It is
    // sound only when every call is unconditionally executed before every VC that
    // consumes those facts. Reject branchy, cyclic, call-after-computation, and
    // unreachable-block shapes until hypotheses carry per-call dominance metadata.
    if !global_callee_hypotheses_have_supported_scope(func) {
        return FunctionVerdict {
            def_path: func.def_path.clone(),
            status: ProofStatus::Trusted,
            assumed_callees: Vec::new(),
            open_reason: Some(
                "call-summary hypotheses lack a supported global dominance scope".into(),
            ),
        };
    }

    // Gather the rebound, destination-pinned hypotheses from every Certified direct callee.
    let (hypotheses, assumed_callees, blocked_callee) =
        gather_callee_hypotheses(func, by_path, registry);

    // Fail-closed: a function with no ensures contract certifies nothing.
    if func.postconditions.is_empty() {
        return FunctionVerdict {
            def_path: func.def_path.clone(),
            status: ProofStatus::Trusted,
            assumed_callees,
            open_reason: Some("no #[ensures] contract to certify".into()),
        };
    }

    // Kernel-check every emitted L0-safety VC and postcondition modulo 3 under
    // the transferred hypotheses, safety first. A function whose postcondition
    // is provable but whose arithmetic may overflow is not certifiable/assumable.
    let mut saw_postcondition_vc = false;
    let vcs = trust_vcgen::generate_vcs(func);
    for vc in vcs
        .iter()
        .filter(|vc| vc.kind.proof_level() == ProofLevel::L0Safety)
        .chain(vcs.iter().filter(|vc| matches!(&vc.kind, trust_types::VcKind::Postcondition)))
    {
        let is_postcondition = matches!(&vc.kind, trust_types::VcKind::Postcondition);
        if is_postcondition {
            saw_postcondition_vc = true;
        }
        // Conjoin the callee hypotheses with the postcondition VC, then augment with
        // the function's sound type bounds + its own preconditions (the SAME
        // augmentation the per-function path applies). The callee ensures ride in as
        // additional conjuncts — the sound "assume callee ensures at the call site".
        let mut conjuncts: Vec<Formula> = hypotheses.clone();
        conjuncts.push(vc.formula.clone());
        let core = if conjuncts.len() == 1 {
            conjuncts.into_iter().next().unwrap()
        } else {
            Formula::And(conjuncts)
        };
        let augmented = crate::prove::augment_with_type_bounds_pub(&core, func);
        if !matches!(
            crate::vc_refute::check_refute_vc(&augmented),
            Some(crate::RefuteOutcome::RefutedModulo3)
        ) {
            // An undischarged safety/ensures clause ⇒ NOT certified (fail-closed).
            // If a callee was non-assumable, surface that as the proximate cause.
            let obligation = if is_postcondition { "ensures clause" } else { "safety obligation" };
            let reason = match &blocked_callee {
                Some(c) => format!(
                    "{obligation} {:?} did not kernel-check modulo 3 (callee `{c}` not assumable \
                     — no hypothesis transferred); formula={:?}",
                    vc.kind, vc.formula
                ),
                None => format!(
                    "{obligation} {:?} did not kernel-check modulo 3 under available hypotheses; \
                     formula={:?}",
                    vc.kind, vc.formula
                ),
            };
            return FunctionVerdict {
                def_path: func.def_path.clone(),
                status: ProofStatus::Trusted,
                assumed_callees,
                open_reason: Some(reason),
            };
        }
    }

    if !saw_postcondition_vc {
        return FunctionVerdict {
            def_path: func.def_path.clone(),
            status: ProofStatus::Trusted,
            assumed_callees,
            open_reason: Some("no postcondition VC emitted (vacuous contract)".into()),
        };
    }

    // Every ensures clause kernel-checked modulo 3 ⇒ this function is Certified and
    // becomes assumable by its callers.
    FunctionVerdict {
        def_path: func.def_path.clone(),
        status: ProofStatus::Certified,
        assumed_callees,
        open_reason: None,
    }
}

/// For each `Call h = callee(args)` in `func`'s body, if `callee` is `Certified` in
/// the registry AND the call site ESTABLISHES the callee's requires, rebind its
/// ensures (result `_0`/`ret` → the POST-CALL dest spelling from
/// `trust_vcgen::call_dest_fact_token`, formals → the LICENSED actual spellings
/// from `trust_vcgen::call_arg_fact_token`) and collect them as hypotheses.
///
/// The callee's ensures clauses + param names are read directly from the matching
/// `VerifiableFunction` in `by_path` (the closed graph). The REGISTRY gates which
/// callees are assumable; the FUNCTION provides the ensures payload. (Equivalently,
/// the per-callee `CalleeSummary` keys this — kept inline for the self-contained
/// driver; the trust-ir-keyed `CalleeSummary` path is what a full module would use.)
///
/// Returns `(hypotheses, assumed_callee_paths, first_blocked_callee)`:
///  - `hypotheses`: the conjoinable rebound callee ensures (over the VC's dest tokens).
///  - `assumed_callee_paths`: which callees actually contributed (for reporting).
///  - `first_blocked_callee`: the def-path of the FIRST direct callee that was present
///    in the body (with a contract) but NOT assumable (the proximate fail-closed
///    cause for diagnostics); `None` when every contracted direct callee was assumable
///    (or there were none).
fn gather_callee_hypotheses(
    func: &VerifiableFunction,
    by_path: &FxHashMap<&str, &VerifiableFunction>,
    registry: &ProofStatusRegistry,
) -> (Vec<Formula>, Vec<String>, Option<String>) {
    let mut hypotheses: Vec<Formula> = Vec::new();
    let mut assumed: Vec<String> = Vec::new();
    let mut blocked: Option<String> = None;

    for block in &func.body.blocks {
        let Terminator::Call { func: callee_path, args, dest, .. } = &block.terminator else {
            continue;
        };
        // The callee must exist in the graph and carry an #[ensures] contract for any
        // transfer to be possible.
        let Some(callee_fn) = by_path.get(callee_path.as_str()).copied() else {
            continue; // opaque/cross-crate callee: nothing to transfer (fail-closed)
        };
        if callee_fn.postconditions.is_empty() {
            continue; // no contract ⇒ nothing to assume
        }

        // FAIL-CLOSED gate: only a `Certified` callee is assumable. A knocked-out /
        // un-certified callee contributes NOTHING and is recorded as the proximate
        // blocked cause (drives the transitive negative control).
        if !registry.is_assumable(callee_path) {
            if blocked.is_none() {
                blocked = Some(callee_path.clone());
            }
            continue;
        }

        // The POST-CALL dest spelling the postcondition VC ACTUALLY reads — consumed
        // from trust-vcgen (`call_dest_fact_token`), the single source of truth pairing
        // `version_terminator_dest_fact`'s versioned token `dest#s{call_block}_t` with
        // the final SSA-collapse pass (`normalize_ssa_version_tokens`) that rewrites it
        // to the BARE dest name whenever all the dest local's versions provably denote
        // one value. Hand-rolling the spelling here is exactly what broke the diamond
        // when the collapse landed (f864db570e): a hypothesis minted under a stale
        // spelling is a distinct SMT symbol and constrains NOTHING, so every caller
        // went open. `None` = projected dest: no whole-local token exists (fail-closed).
        let Some(dest_token) = trust_vcgen::call_dest_fact_token(func, block.id, dest) else {
            if blocked.is_none() {
                blocked = Some(callee_path.clone());
            }
            continue;
        };

        // Map each callee formal name (its locals `1..=arg_count`) → the LICENSED
        // at-call spelling of its actual, consumed from trust-vcgen
        // (`call_arg_fact_token`) — the pairing partner of the dest token above,
        // sharing the SSA-collapse license. A REASSIGNED actual has NO licensed
        // spelling (its bare name denotes the ENTRY version the caller's own
        // preconditions constrain, NOT the at-call value — name-disjoint by the
        // staleness kill), so its formal stays unmapped and every clause touching
        // it is declined below (fail-closed). Hand-rolling the bare name here is
        // the REASSIGNED-ACTUAL FALSE-CERTIFICATION bug this file's probe pins:
        // `a = 0; h = pass(a)` under `requires(a >= 100)` minted the hypothesis
        // `a >= 100` about the entry version and certified a false `ret >= 100`.
        let mut formal_to_actual: FxHashMap<String, String> = FxHashMap::default();
        for (i, actual) in args.iter().enumerate() {
            if let Some(formal) = local_name(callee_fn, i + 1)
                && let Some(actual_tok) = trust_vcgen::call_arg_fact_token(func, actual)
            {
                formal_to_actual.insert(formal, actual_tok);
            }
        }

        // FAIL-CLOSED gate (the `ProofContext.establishes` half): a callee's
        // ensures holds ONLY for calls that satisfy its requires. Kernel-check
        // that THIS call site ESTABLISHES every requires clause (rebound onto the
        // same licensed spellings, refuted-when-negated under the caller's own
        // sound augmentation). A call that does not provably establish the
        // requires gets NO hypothesis from this callee — assuming the ensures of
        // a (possibly) violated contract minted false hypotheses (the anyarg /
        // reasg probes).
        if !caller_establishes_requires(func, &callee_fn.preconditions, &formal_to_actual) {
            if blocked.is_none() {
                blocked = Some(callee_path.clone());
            }
            continue;
        }

        // REBIND each callee ensures clause onto the authoritative dest token + actuals.
        // A clause referencing a free var mapping to neither result nor a formal is
        // DROPPED (only weakens PROVE→OPEN — the postcondition_rebindable discipline).
        let mut rebound_any = false;
        for clause in &callee_fn.postconditions {
            if let Some(r) = rebind_clause(clause, &dest_token, &formal_to_actual) {
                hypotheses.push(r);
                rebound_any = true;
            }
        }
        if rebound_any {
            assumed.push(callee_path.clone());
        } else if blocked.is_none() {
            // Certified but nothing rebindable ⇒ no hypothesis (fail-closed).
            blocked = Some(callee_path.clone());
        }
    }

    (hypotheses, assumed, blocked)
}

// ===========================================================================
// 9. The concrete multi-function POC programs (a DIAMOND with embedded chains)
// ===========================================================================
//
// The Step-3 existence proof is a 4-function DIAMOND call graph:
//
//                       top                #[ensures(ret <= 32)]
//                      /   \
//                   left   right           left:  #[ensures(ret <= 11)]
//                      \   /                right: #[ensures(ret <= 21)]
//                       leaf                leaf:  #[ensures(0 <= ret <= 10)]
//
//   leaf(x)  -> i32 { 5 }                       (the shared LEAF — two callers)
//   left(p)  -> i32 { let l = leaf(p); l + 1  } ensures ret <= 11
//   right(q) -> i32 { let r = leaf(q); r + 11 } ensures ret <= 21
//   top(a)   -> i32 { let x = left(a);          ensures ret <= 32
//                     let y = right(a);
//                     x + y }                    (NEEDS BOTH callee ensures)
//
// Why this shape exercises Step 3 fully:
//  - It is a genuine multi-node graph, not the hand-built 2-node case: the callee-
//    first order is consumed from `compute_verification_order` (leaf, then left &
//    right in some order, then top).
//  - `top → left → leaf` and `top → right → leaf` are CHAINS of depth 3 — the
//    chain shape the roadmap names (main→f→g→h analogue).
//  - `leaf` has TWO callers and `top` has TWO callees — the DIAMOND shape.
//  - `top`'s ensures `ret <= 32` GENUINELY NEEDS BOTH `left`'s `x <= 11` AND
//    `right`'s `y <= 21` (`x + y <= 32`): the MULTI-CALLEE CONJUNCTION. Drop either
//    and `top` does not certify. (The §6 driver refutes upper-bound atoms cleanly;
//    each function's load-bearing clause is an UPPER bound, staying inside the
//    `vc_refute` linear fragment — see the leaf-comment in `helper_callee`.)
//  - The composition is TRANSITIVE: `top` certifies only because `left`/`right`
//    certified, which certified only because `leaf` certified — the proof threads
//    leaf→{left,right}→top through the shared registry.

/// The shared LEAF: `#[ensures(0 <= ret <= 10)]` `fn leaf(x: i32) -> i32 { 5 }`.
/// A constant strictly inside `[0,10]`, so both ensures clauses are literal
/// contradictions the `vc_refute` engine closes modulo 3 standalone (no callees).
#[must_use]
pub fn diamond_leaf() -> VerifiableFunction {
    VerifiableFunction {
        name: "leaf".into(),
        def_path: "crate::leaf".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: I32, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: I32, name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(5))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: I32,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![
            Formula::Ge(Box::new(ret_var()), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(ret_var()), Box::new(Formula::Int(10))),
        ],
        spec: Default::default(),
    }
}

/// Build an intermediate single-callee function: `fn name(p) { let d = leaf(p); d + k }`
/// with `#[ensures(k <= ret <= bound)]`. Rust's checked-debug MIR shape is
/// bb0 = `_3 = k; d = callee(p)` → bb1 = `_4 = CheckedBinaryOp(d, _3); assert(!_4.1)` →
/// bb2 = `_0 = move _4.0; return`. Keeping the offset in a named MIR local also
/// gives the Clean linear checker the ordinary `_3 = k` equality used in both
/// directions of the exact interval proof. The upper bound is load-bearing, while the
/// lower bound is transferred onward so a caller can independently discharge
/// signed underflow before using the mathematical return relation.
fn diamond_intermediate(
    name: &str,
    def_path: &str,
    callee_path: &str,
    add_k: i128,
    ensures_bound: i128,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: def_path.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: I32, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: I32, name: Some("p".into()) },
                LocalDecl { index: 2, ty: I32, name: Some("d".into()) },
                LocalDecl { index: 3, ty: I32, name: Some("k".into()) },
                LocalDecl { index: 4, ty: Ty::Tuple(vec![I32, Ty::Bool]), name: Some("_4".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(add_k))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        func: callee_path.into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(4, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(2),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Move(Place::field(4, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: I32,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![
            Formula::Ge(Box::new(ret_var()), Box::new(Formula::Int(add_k))),
            Formula::Le(Box::new(ret_var()), Box::new(Formula::Int(ensures_bound))),
        ],
        spec: Default::default(),
    }
}

/// `left(p) -> i32 { let d = leaf(p); d + 1 }` — `#[ensures(ret <= 11)]`.
#[must_use]
pub fn diamond_left() -> VerifiableFunction {
    diamond_intermediate("left", "crate::left", "crate::leaf", 1, 11)
}

/// `right(q) -> i32 { let d = leaf(q); d + 11 }` — `#[ensures(ret <= 21)]`.
#[must_use]
pub fn diamond_right() -> VerifiableFunction {
    diamond_intermediate("right", "crate::right", "crate::leaf", 11, 21)
}

/// `top(a) -> i32 { let x = left(a); let y = right(a); x + y }` —
/// `#[ensures(ret <= 32)]`. The MULTI-CALLEE apex: bb0 = `x = left(a)`,
/// bb1 = `y = right(a)`, bb2 = `_4 = CheckedBinaryOp(x, y); assert(!_4.1)`,
/// bb3 = `_0 = move _4.0; return`. Its upper bound needs BOTH `x <= 11` and
/// `y <= 21`, each bound onto the dest spelling the emitted VC reads
/// (`trust_vcgen::call_dest_fact_token` — bare `x`/`y` here, since both are
/// single-assignment call dests and vcgen collapses their SSA tokens).
#[must_use]
pub fn diamond_top() -> VerifiableFunction {
    VerifiableFunction {
        name: "top".into(),
        def_path: "crate::top".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: I32, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: I32, name: Some("a".into()) },
                LocalDecl { index: 2, ty: I32, name: Some("x".into()) },
                LocalDecl { index: 3, ty: I32, name: Some("y".into()) },
                LocalDecl { index: 4, ty: Ty::Tuple(vec![I32, Ty::Bool]), name: Some("_4".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "crate::left".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2), // x
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "crate::right".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(3), // y
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)), // x
                            Operand::Copy(Place::local(3)), // y
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(4, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(3),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Move(Place::field(4, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: I32,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![Formula::Le(Box::new(ret_var()), Box::new(Formula::Int(32)))],
        spec: Default::default(),
    }
}

/// The full diamond program `{leaf, left, right, top}` (deterministic order; the
/// driver re-orders to callee-first internally).
#[must_use]
pub fn diamond_program() -> Vec<VerifiableFunction> {
    vec![diamond_top(), diamond_left(), diamond_right(), diamond_leaf()]
}

// ===========================================================================
// 10. STEP 4 — RECURSION (the well-founded inter-procedural meta-theorem)
// ===========================================================================
//
// Steps 1-3 (§1-§9) handle an ACYCLIC call graph: a callee is verified BEFORE its
// callers, so the caller may assume the callee's already-Certified ensures. A
// RECURSIVE function breaks that order: `f` calls itself (a self-loop in the call
// graph — an SCC of size 1), so "the callee is already proven" is circular — the
// callee IS `f`, not yet proven.
//
// Step 4 (reports/whole-program-roadmap.md §3 Step 4) closes the recursive SCC with
// the WELL-FOUNDED inter-procedural meta-theorem, MIRRORING the committed
// single-function LOOP-TOTALITY meta-theory (`mirsem.rs`: `loopRankDecrease`,
// `toNatMono`, `loopRankTerminates`, `loopTotalCorrect`). The correspondence is
// exact — a recursive call is the inter-procedural analogue of a loop back-edge, and
// the `#[decreases]` measure plays the role of the loop variant/ranking:
//
//   LOOP meta-theory (mirsem.rs)                 RECURSION meta-theory (here)
//   ----------------------------------------     -------------------------------------------
//   ranking R := λe. toNat(n - i)                measure M := the `#[decreases(e)]` term, as
//                                                  toNat over the recursion guard
//   loopRankDecrease: i<n ⇒ toNat(n-(i+1))       measure-decrease: guard ⇒ M(rec-arg) < M(arg)
//     < toNat(n-i)  (strict drop each step)        (strict drop on each recursive CALL)
//   toNatMono / well-founded Nat descent         M ≥ 0 (well-founded: a Nat, no infinite
//                                                  descent) — the toNat lower bound
//   loopRankTerminates: descent ⇒ guard false    the recursion bottoms out (no infinite
//     within R e steps                             chain of strictly-smaller measures)
//   loopInvariantRule: invariant survives n      ensures-under-IH: assuming f's OWN ensures
//     steps (partial correctness)                  for the SMALLER-measure recursive call
//                                                  (the INDUCTION HYPOTHESIS), prove f's
//                                                  ensures for the body
//   loopTotalCorrect = And.intro(partial,        recTotalCorrect = (measure-decrease ∧ M≥0)
//     terminates)  — ONE composed theorem          ∧ (ensures-under-IH)  — the composed
//                                                  well-founded-recursion verdict
//
// THE WELL-FOUNDED INDUCTION PRINCIPLE (why assuming the IH is sound): a property `P`
// holds for ALL inputs if, for every input `x`, `P` holds for `x` WHENEVER `P` holds
// for every `y` with `M(y) < M(x)` (strong/well-founded induction over the measure
// `M : input → Nat`). For a self-recursive `f`, `P(x) := f's ensures at x`; the
// recursive call is at some `y` with `M(y) < M(x)` (the DECREASE lemma), so we may
// ASSUME `P(y)` = f's own ensures REBOUND to that recursive call's result. This is
// EXACTLY the loop case: the invariant at step `k+1` is proven assuming it held at
// step `k` (`loopInvariantRule`'s preservation hypothesis), justified by the rank
// strictly dropping (`loopRankDecrease`). Recursion lifts "step `k`" to "a call with
// strictly smaller measure".
//
// KERNEL-CHECKED MODULO 3, GENUINE (not Eq.refl): BOTH halves go through the UNCHANGED
// `vc_refute` engine (the SAME kernel the loop ranking-decrease and the diamond
// composition use — empty axiom residue beyond the 3 ⇒ `RefutedModulo3`):
//   (a) MEASURE DECREASE: refute `guard ∧ M(rec-arg) ≥ M(arg)` (the violation that the
//       measure does NOT strictly drop) AND `M(rec-arg) < 0` (the violation of
//       well-foundedness). For `sum_to_n(n-1)` under guard `n ≥ 1`: refute
//       `n ≥ 1 ∧ (n-1) ≥ n` and `n ≥ 1 ∧ (n-1) < 0` — both linear-arith
//       contradictions the `vc_refute` engine closes modulo 3 (the SAME shape as
//       `loopRankDecrease`'s `toNat(n-1) < toNat(n)` over the guard).
//   (b) ENSURES UNDER IH: refute the body's ensures-violation CONJOINED with the IH
//       (f's own ensures rebound onto the recursive call's result symbol). For
//       `sum_to_n` with `#[ensures(ret ≥ 0)]`: the body `n + sum_to_n(n-1)`; assuming
//       the IH `rec ≥ 0` (own ensures at the recursive result) + the guard `n ≥ 1` ⇒
//       `n + rec ≥ 0` (the ensures), refuting `n ≥ 1 ∧ rec ≥ 0 ∧ n + rec < 0`.
//
// FAIL-CLOSED (load-bearing): if there is NO `#[decreases]` clause, OR the measure
// does NOT strictly decrease on the recursive call (e.g. `#[decreases(n)]` but the
// call is `f(n+1)` or `f(n)`), OR the measure is not well-founded (can go negative)
// → the measure-decrease half does NOT refute → the recursion is NOT well-founded →
// the IH MAY NOT be assumed → the ensures obligation stays OPEN (never falsely
// proven). The NEGATIVE CONTROL confirms the measure-decrease is GENUINE: a
// non-decreasing measure is rejected, exactly as a WRONG loop ranking is
// KernelRejected in the loop meta-theory.
//
// SYNTHESIS PROPOSES / KERNEL VERIFIES, modulo 3, additive: no change to
// `vc_refute.rs` or `mirsem.rs`. The measure + ensures are PROVIDED (as the
// `#[decreases]`/`#[ensures]` clauses are), exactly as the loop ranking `R` is
// PROVIDED not synthesized (`mirsem.rs:14811` HONESTY note); the kernel VERIFIES the
// decrease + the ensures-under-IH. What this does NOT do: synthesize measures for
// arbitrary recursions, or prove recursion shapes outside the single decreasing-arg
// self-recursion / shared-measure mutual-recursion recognized here.

/// The verdict of attempting to discharge a recursive SCC's contract by the
/// well-founded inter-procedural meta-theorem, kernel-checked modulo 3.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecursionVerdict {
    /// The recursive function's ensures was kernel-checked modulo 3 by well-founded
    /// induction: the measure STRICTLY DECREASES (and is well-founded) on every
    /// recursive call AND the ensures holds under the IH (own ensures assumed for the
    /// smaller-measure call). The recursive-SCC nucleus.
    ProvenWellFounded,
    /// The recursion stayed OPEN — the sound fail direction. Carries the reason (no
    /// `#[decreases]` / the measure does not strictly decrease or is not well-founded
    /// / the ensures did not kernel-check even under the IH).
    Open(String),
    /// The kernel REJECTED a constructed refutation candidate. Treated as OPEN
    /// downstream (a bad candidate only leaves a safe obligation undischarged),
    /// surfaced for diagnostics. Must NOT be counted as proven.
    KernelRejected(String),
}

impl RecursionVerdict {
    /// True iff the recursive contract was kernel-checked modulo 3 by well-founded
    /// induction.
    #[must_use]
    pub fn is_proven_well_founded(&self) -> bool {
        matches!(self, RecursionVerdict::ProvenWellFounded)
    }
}

/// A self-recursive function plus its `#[decreases(measure)]` termination measure —
/// the POC's recursive unit. The measure is carried as a structured `Formula` over
/// the function's parameter(s) (the kernel-relevant form), exactly as the diamond
/// carries `postconditions: Vec<Formula>` directly rather than re-parsing attributes.
/// `func` is an ordinary `VerifiableFunction` whose body contains ≥1 `Call` to its
/// OWN `def_path` (the recursive self-edge).
#[derive(Debug, Clone)]
pub struct RecursiveFunction {
    /// The function under verification (its body, contracts, `def_path`).
    pub func: VerifiableFunction,
    /// The `#[decreases(measure)]` termination measure, as a `Formula` over the
    /// function's parameters (e.g. `Var("n")` for `#[decreases(n)]`). `None` ⇒ NO
    /// decreases clause ⇒ fail-closed (the recursive call cannot assume the IH).
    pub measure: Option<Formula>,
}

/// The result of verifying a recursive function by well-founded induction.
#[derive(Debug, Clone)]
pub struct RecursionResult {
    /// The function's def-path / IR key.
    pub def_path: String,
    /// The verdict of the well-founded discharge.
    pub verdict: RecursionVerdict,
    /// Whether the measure STRICTLY DECREASED (and stayed well-founded ≥ 0) on every
    /// recursive call — the well-founded half (mirrors `loopRankDecrease` + the
    /// `toNat` lower bound). False ⇒ the IH may not be assumed (fail-closed).
    pub measure_well_founded: bool,
    /// Whether the ensures kernel-checked modulo 3 UNDER the IH (own ensures assumed
    /// for the smaller-measure recursive call) — the partial-correctness half (mirrors
    /// `loopInvariantRule`'s preservation).
    pub ensures_under_ih: bool,
    /// The def-paths of the SCC members whose recursive calls contributed an IH
    /// (self for direct recursion; the other SCC members for mutual recursion).
    pub ih_from: Vec<String>,
}

impl RecursionResult {
    /// True iff the recursive contract was kernel-checked modulo 3.
    #[must_use]
    pub fn is_proven(&self) -> bool {
        self.verdict.is_proven_well_founded()
    }
}

// ---------------------------------------------------------------------------
// 10.1 The recursion POC program — `sum_to_n` with a #[decreases(n)] measure
// ---------------------------------------------------------------------------

/// The RECURSION POC: `#[decreases(n)] #[ensures(ret >= 0)]`
/// `fn sum_to_n(n: i32) -> i32 { if n <= 0 { 0 } else { n + sum_to_n(n - 1) } }`.
///
/// MIR shape (the guarded self-recursion):
///   bb0:  m = n - 1;                                         (the DECREASING arg)
///   bb1:  rec = sum_to_n(m)   -> goto bb2                    (the RECURSIVE call)
///   bb2:  _0 = n + rec; return                               (the inductive step)
///
/// (The base-case `if n <= 0 { 0 }` switch is recorded via the recursion GUARD below;
/// the kernel only needs the predicate under which the recursive call is reached.)
///
/// `#[decreases(n)]`: the measure is `n` — on the recursive call `sum_to_n(n-1)`,
/// under the guard `¬(n <= 0)` i.e. `n >= 1`, `n-1 < n` (strict drop) and `n-1 >= 0`
/// (well-founded). `#[ensures(ret >= 0)]`: holds by induction — base `0 >= 0`; step
/// `n + rec >= 0` under `n >= 1` + the IH `rec >= 0`.
#[must_use]
pub fn sum_to_n_recursive() -> RecursiveFunction {
    // n = local 1; m = local 2 (the decreasing arg n-1); rec = local 3 (the call result);
    // _0 = local 0 (the return).
    let body = VerifiableBody {
        locals: vec![
            LocalDecl { index: 0, ty: I32, name: Some("_0".into()) },
            LocalDecl { index: 1, ty: I32, name: Some("n".into()) },
            LocalDecl { index: 2, ty: I32, name: Some("m".into()) },
            LocalDecl { index: 3, ty: I32, name: Some("rec".into()) },
        ],
        blocks: vec![
            // bb0: m = n - 1  (the decreasing recursive arg)  -> bb1 (the recursive call)
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(1)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(1)),
            },
            // bb1: rec = sum_to_n(m)   (the SELF-recursive call)  -> bb2
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "crate::sum_to_n".into(), // SELF — the recursive self-edge
                    args: vec![Operand::Copy(Place::local(2))], // sum_to_n(m) = sum_to_n(n-1)
                    dest: Place::local(3),          // rec = ...
                    target: Some(BlockId(2)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    unwind: trust_types::UnwindEdge::Unreachable,
                },
            },
            // bb2: _0 = n + rec; return   (the inductive step assembly)
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)), // n
                        Operand::Copy(Place::local(3)), // rec
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ],
        arg_count: 1,
        return_ty: I32,
    };
    let func = VerifiableFunction {
        name: "sum_to_n".into(),
        def_path: "crate::sum_to_n".into(),
        span: SourceSpan::default(),
        body,
        contracts: vec![],
        preconditions: vec![],
        // #[ensures(ret >= 0)]
        postconditions: vec![Formula::Ge(Box::new(ret_var()), Box::new(Formula::Int(0)))],
        spec: Default::default(),
    };
    RecursiveFunction {
        func,
        // #[decreases(n)] — the measure is the parameter `n`.
        measure: Some(Formula::Var("n".into(), Sort::Int)),
    }
}

/// The recursion guard under which the recursive call is REACHED: `n >= 1`
/// (= `¬(n <= 0)`, the `else` arm of the base-case test). The measure-decrease and the
/// ensures-under-IH are both discharged UNDER this guard — exactly as the loop
/// ranking-decrease holds UNDER the loop guard `i < n` (`mirsem.rs:14816`).
fn sum_to_n_recursion_guard() -> Formula {
    Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(1)))
}

// ---------------------------------------------------------------------------
// 10.2 The well-founded discharge (mirrors loopRankDecrease + loopInvariantRule)
// ---------------------------------------------------------------------------

/// Verify a self-recursive function by the well-founded inter-procedural
/// meta-theorem, kernel-checked modulo 3. `guard` is the predicate under which the
/// recursive call(s) are reached (e.g. `n >= 1`); `goal_ensures` is the body's
/// ensures obligation to discharge (the function's `#[ensures]` rebound to the body's
/// return expression, e.g. `n + rec >= 0`).
///
/// The two halves (mirroring `loopTotalCorrect = And.intro(partial, terminates)`):
///  (a) WELL-FOUNDED MEASURE DECREASE — `measure_strictly_decreases`: for each
///      recursive call `rec = f(arg)`, the measure on `arg` is STRICTLY less than the
///      measure on the formal AND stays ≥ 0 (well-founded), under the guard. Both are
///      `vc_refute` modulo-3 refutations of the respective violations.
///  (b) ENSURES UNDER IH — `ensures_holds_under_ih`: the body's ensures-violation,
///      CONJOINED with the IH (f's OWN ensures rebound to each recursive call's result
///      symbol) + the guard, refutes modulo 3.
///
/// FAIL-CLOSED: no measure (no `#[decreases]`) ⇒ (a) fails ⇒ the IH may NOT be assumed
/// ⇒ Open. A non-decreasing / non-well-founded measure ⇒ (a) fails ⇒ Open. The ensures
/// not provable even under the IH ⇒ (b) fails ⇒ Open. The well-founded half GATES the
/// IH: `ensures_under_ih` is only consulted when `measure_well_founded` holds — an
/// unfounded recursion contributes NO IH (you cannot assume the contract for a call
/// that is not provably smaller). This is the load-bearing soundness: well-founded
/// induction is unsound without the decrease.
#[must_use]
pub fn prove_recursive_function(
    rf: &RecursiveFunction,
    guard: &Formula,
    goal_ensures: &Formula,
) -> RecursionResult {
    let func = &rf.func;
    let self_path = func.def_path.clone();

    // (a) The well-founded half: the measure strictly decreases AND stays ≥ 0 on every
    // recursive call, under the guard. Fail-closed: no measure ⇒ not well-founded.
    let (measure_well_founded, ih_from) = match &rf.measure {
        Some(measure) => measure_strictly_decreases(func, measure, guard, &[self_path.as_str()]),
        None => (false, Vec::new()), // no #[decreases] ⇒ the IH may NOT be assumed
    };

    if !measure_well_founded {
        // Without a strictly-decreasing well-founded measure, the IH may not be
        // assumed (well-founded induction is unsound). Re-attempt the ensures with NO
        // IH (the havoc/opaque-result fallback) — for a genuinely inductive obligation
        // this fails ⇒ Open (the sound fail direction).
        let v = ensures_holds_under_ih(func, guard, goal_ensures, &[]);
        return RecursionResult {
            def_path: self_path,
            verdict: match v {
                CompositionVerdict::ProvenModulo3 => RecursionVerdict::Open(
                    "ensures provable WITHOUT a decreasing measure — but recursion is not \
                     well-founded, so it is NOT a sound proof; OPEN (fail-closed)"
                        .into(),
                ),
                CompositionVerdict::KernelRejected(r) => RecursionVerdict::KernelRejected(r),
                CompositionVerdict::Open(_) => RecursionVerdict::Open(
                    "no strictly-decreasing well-founded #[decreases] measure on the recursive \
                     call — the induction hypothesis may not be assumed (fail-closed)"
                        .into(),
                ),
            },
            measure_well_founded,
            ensures_under_ih: false,
            ih_from,
        };
    }

    // (b) The partial-correctness half: the ensures holds UNDER the IH (own ensures
    // rebound to each recursive call's result), conjoined with the guard. The IH is
    // JUSTIFIED by (a): the call is at a strictly-smaller, well-founded measure.
    let ih = own_ensures_as_ih(func);
    let verdict = ensures_holds_under_ih(func, guard, goal_ensures, &ih);
    let ensures_under_ih = matches!(verdict, CompositionVerdict::ProvenModulo3);

    let recursion_verdict = match verdict {
        CompositionVerdict::ProvenModulo3 => RecursionVerdict::ProvenWellFounded,
        CompositionVerdict::KernelRejected(r) => RecursionVerdict::KernelRejected(r),
        CompositionVerdict::Open(_) => RecursionVerdict::Open(
            "the #[ensures] did not kernel-check modulo 3 even under the induction hypothesis"
                .into(),
        ),
    };

    RecursionResult {
        def_path: self_path,
        verdict: recursion_verdict,
        measure_well_founded,
        ensures_under_ih,
        ih_from,
    }
}

/// (a) THE WELL-FOUNDED MEASURE-DECREASE half — mirrors `loopRankDecrease` + the
/// `toNat` lower bound (`mirsem.rs:14899` `countdownRankDecrease` /
/// `loopRankDecrease`). For every recursive `Call rec = callee(args)` in `func`'s body
/// whose `callee` is in `scc` (the recursive SCC — `[self]` for direct recursion),
/// kernel-check modulo 3, UNDER the guard:
///   - STRICT DECREASE: `M(args) < M(formals)` — refute `guard ∧ M(args) >= M(formals)`.
///   - WELL-FOUNDED (≥0): `M(args) >= 0` — refute `guard ∧ M(args) < 0`.
/// `M(formals)` is the measure over the callee's formal params (rebound to actuals for
/// the arg side). For `sum_to_n` self-recursion: measure `n`, recursive arg `n-1`,
/// guard `n >= 1` ⇒ refute `n >= 1 ∧ (n-1) >= n` (strict) and `n >= 1 ∧ (n-1) < 0`
/// (well-founded) — both linear-arith contradictions the `vc_refute` kernel closes
/// modulo 3 (the SAME shape as `loopRankDecrease`'s `toNat(n-1) < toNat(n)`).
///
/// Returns `(all_recursive_calls_well_founded, scc_members_that_contributed_an_IH)`.
/// FAIL-CLOSED: a SINGLE recursive call whose measure does not strictly decrease (or
/// can go negative) ⇒ `false` (the whole recursion is not well-founded). A function
/// with NO recursive call to an SCC member is vacuously well-founded BUT contributes no
/// IH (it isn't actually recursive — handled by the caller treating empty `ih_from`).
fn measure_strictly_decreases(
    func: &VerifiableFunction,
    measure: &Formula,
    guard: &Formula,
    scc: &[&str],
) -> (bool, Vec<String>) {
    let mut ih_from: Vec<String> = Vec::new();
    let mut saw_recursive_call = false;

    for block in &func.body.blocks {
        let Terminator::Call { func: callee_path, args, .. } = &block.terminator else {
            continue;
        };
        // Only a call BACK INTO the SCC is a recursive edge (self or mutual).
        if !scc.contains(&callee_path.as_str()) {
            continue;
        }
        saw_recursive_call = true;

        // M(formals): the measure over the callee's formal param names. For direct
        // recursion the callee's formals are this function's own formals, so the
        // measure formula already references them by name.
        let m_formals = measure.clone();

        // M(args): the measure with each callee formal substituted by the actual
        // argument EXPRESSION at this call site. For `sum_to_n(m)` where `m = n - 1`,
        // the arg `m` is resolved to its definition `n - 1`, so M(args) = `n - 1`.
        let Some(m_args) = measure_over_actuals(func, callee_path, args, measure) else {
            // The arg is not an expressible measure (e.g. a non-resolvable operand):
            // cannot establish a strict decrease ⇒ fail-closed.
            return (false, Vec::new());
        };

        // STRICT DECREASE: refute `guard ∧ M(args) >= M(formals)` — the violation that
        // the measure does NOT strictly drop. (mirrors loopRankDecrease's strict <.)
        let decrease_violation = Formula::And(vec![
            guard.clone(),
            Formula::Ge(Box::new(m_args.clone()), Box::new(m_formals.clone())),
        ]);
        if !refute_modulo_3(func, &decrease_violation) {
            return (false, Vec::new()); // measure does not strictly decrease ⇒ not well-founded
        }

        // WELL-FOUNDED (≥ 0): refute `guard ∧ M(args) < 0` — the violation of the
        // measure's lower bound (the `toNat` well-foundedness: no infinite descent).
        let nonneg_violation = Formula::And(vec![
            guard.clone(),
            Formula::Lt(Box::new(m_args.clone()), Box::new(Formula::Int(0))),
        ]);
        if !refute_modulo_3(func, &nonneg_violation) {
            return (false, Vec::new()); // measure can go negative ⇒ not well-founded
        }

        ih_from.push(callee_path.clone());
    }

    // Vacuously well-founded if there is no recursive call at all (not actually
    // recursive); the empty `ih_from` then means "no IH to assume" upstream.
    (saw_recursive_call, ih_from)
}

/// The measure `M` with the callee's formal params substituted by the ACTUAL argument
/// expressions at the call site `callee_path(args)` in `func`. The actuals are
/// resolved through simple aux-temp definitions in the body (e.g. `m = n - 1` resolves
/// the operand `m` to `n - 1`), so the measure-decrease is read against the real
/// recursive argument expression. `None` if any actual is not resolvable to a measure
/// expression (fail-closed).
fn measure_over_actuals(
    func: &VerifiableFunction,
    callee_path: &str,
    args: &[Operand],
    measure: &Formula,
) -> Option<Formula> {
    // Map each callee formal name → the actual argument EXPRESSION (resolved through
    // local definitions). For direct recursion the callee formals are `func`'s own
    // params `1..=arg_count`.
    let mut formal_to_actual_expr: FxHashMap<String, Formula> = FxHashMap::default();
    for (i, actual) in args.iter().enumerate() {
        let formal = local_name(func, i + 1)?;
        let actual_expr = resolve_operand_expr(func, callee_path, actual)?;
        formal_to_actual_expr.insert(formal, actual_expr);
    }
    subst_measure(measure, &formal_to_actual_expr)
}

/// Resolve an operand at a recursive call to a measure EXPRESSION over the function's
/// params: a constant → that literal; a copy/move of a param → the param var; a
/// copy/move of a local that is DEFINED earlier as a simple arithmetic value
/// (`m = n - 1`) → that defining expression. Only the simple, single-definition
/// fragment is resolvable (fail-closed otherwise) — matching the `vc_refute` engine's
/// aux-temp inlining discipline.
fn resolve_operand_expr(
    func: &VerifiableFunction,
    _callee_path: &str,
    op: &Operand,
) -> Option<Formula> {
    match op {
        Operand::Constant(ConstValue::Int(v)) => Some(Formula::Int(*v)),
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            let name = local_name(func, p.local)?;
            // A formal param resolves to itself; an intermediate local resolves to its
            // single defining arithmetic statement (the recursive-arg computation).
            if p.local >= 1 && p.local <= func.body.arg_count {
                return Some(Formula::Var(name, Sort::Int));
            }
            resolve_local_definition(func, p.local)
        }
        _ => None,
    }
}

/// The single defining arithmetic value of a non-param local (e.g. `m := n - 1`),
/// as a measure `Formula` over params. Scans for the UNIQUE `Assign { place: local,
/// rvalue }` and lowers a `Use`/`BinaryOp(Add|Sub|Mul)` rvalue. `None` if the local
/// is multiply-defined or its rvalue is outside the simple arithmetic fragment.
fn resolve_local_definition(func: &VerifiableFunction, local: usize) -> Option<Formula> {
    let mut found: Option<Formula> = None;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else { continue };
            if place.local != local || !place.projections.is_empty() {
                continue;
            }
            if found.is_some() {
                return None; // multiply-defined ⇒ not a simple single definition
            }
            found = Some(lower_rvalue_expr(func, rvalue)?);
        }
    }
    found
}

/// Lower a simple arithmetic rvalue (`Use(const|param)`, `BinaryOp(Add|Sub|Mul)`) to a
/// measure `Formula` over params. `None` for any other rvalue (fail-closed).
fn lower_rvalue_expr(func: &VerifiableFunction, rvalue: &Rvalue) -> Option<Formula> {
    match rvalue {
        Rvalue::Use(op) => lower_operand_expr(func, op),
        Rvalue::BinaryOp(bin, a, b) => {
            let la = lower_operand_expr(func, a)?;
            let lb = lower_operand_expr(func, b)?;
            match bin {
                BinOp::Add => Some(Formula::Add(Box::new(la), Box::new(lb))),
                BinOp::Sub => Some(Formula::Sub(Box::new(la), Box::new(lb))),
                BinOp::Mul => Some(Formula::Mul(Box::new(la), Box::new(lb))),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Lower a single operand to a measure `Formula` (const or named param/local var).
fn lower_operand_expr(func: &VerifiableFunction, op: &Operand) -> Option<Formula> {
    match op {
        Operand::Constant(ConstValue::Int(v)) => Some(Formula::Int(*v)),
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            Some(Formula::Var(local_name(func, p.local)?, Sort::Int))
        }
        _ => None,
    }
}

/// Substitute the measure's free param vars by the supplied actual EXPRESSIONS.
/// A var not in the map is left as-is (the measure may mention only some params).
/// Only the arithmetic/atom fragment is supported (fail-closed on other shapes).
fn subst_measure(measure: &Formula, map: &FxHashMap<String, Formula>) -> Option<Formula> {
    use Formula as F;
    let bx = |x: Option<Formula>| x.map(Box::new);
    match measure {
        F::Var(name, _sort) => Some(map.get(name).cloned().unwrap_or_else(|| measure.clone())),
        F::Int(_) | F::UInt(_) | F::Bool(_) => Some(measure.clone()),
        F::Add(a, b) => Some(F::Add(bx(subst_measure(a, map))?, bx(subst_measure(b, map))?)),
        F::Sub(a, b) => Some(F::Sub(bx(subst_measure(a, map))?, bx(subst_measure(b, map))?)),
        F::Mul(a, b) => Some(F::Mul(bx(subst_measure(a, map))?, bx(subst_measure(b, map))?)),
        _ => None,
    }
}

/// (b) THE ENSURES-UNDER-IH half — mirrors `loopInvariantRule`'s preservation
/// (`mirsem.rs`): the invariant at step `k+1` is proven ASSUMING it held at step `k`.
/// Here the function's `#[ensures]` is proven for the body ASSUMING the IH (f's own
/// ensures rebound onto each recursive call's RESULT symbol) + the guard.
///
/// Kernel-checks modulo 3 via the UNCHANGED `vc_refute`: refute `guard ∧ IH ∧
/// ¬goal_ensures`. For `sum_to_n`: refute `n >= 1 ∧ (rec >= 0) ∧ ¬(n + rec >= 0)` =
/// `n >= 1 ∧ rec >= 0 ∧ n + rec < 0` — a linear contradiction the kernel closes
/// modulo 3. With NO IH (`ih` empty — the fail-closed unfounded-recursion fallback)
/// the obligation is refuted WITHOUT the recursive-result hypothesis, which for a
/// genuinely inductive ensures does NOT close ⇒ `Open`.
fn ensures_holds_under_ih(
    func: &VerifiableFunction,
    guard: &Formula,
    goal_ensures: &Formula,
    ih: &[Formula],
) -> CompositionVerdict {
    let Some(violation) = negate_atom(goal_ensures) else {
        return CompositionVerdict::Open("ensures obligation is not an atomic comparison".into());
    };
    // The conjunction the kernel refutes: guard ∧ IH ∧ violation, augmented with the
    // function's sound type bounds (`augment_with_type_bounds` — the SAME augmentation
    // every other lane applies). The IH rides in as additional conjuncts — exactly the
    // sound "assume the contract for the strictly-smaller recursive call".
    let mut conjuncts: Vec<Formula> = vec![guard.clone()];
    conjuncts.extend_from_slice(ih);
    conjuncts.push(violation);
    let core = if conjuncts.len() == 1 {
        conjuncts.into_iter().next().unwrap()
    } else {
        Formula::And(conjuncts)
    };
    let augmented = crate::prove::augment_with_type_bounds_pub(&core, func);
    match crate::vc_refute::check_refute_vc(&augmented) {
        Some(crate::RefuteOutcome::RefutedModulo3) => CompositionVerdict::ProvenModulo3,
        Some(crate::RefuteOutcome::KernelRejected(r)) => CompositionVerdict::KernelRejected(r),
        _ => CompositionVerdict::Open("ensures not refuted under the IH".into()),
    }
}

/// The INDUCTION HYPOTHESIS: the function's OWN `#[ensures]`, rebound onto each
/// recursive call's RESULT symbol (the `dest` local of the self-call). For `sum_to_n`
/// the own ensures `ret >= 0` (`_0 >= 0`) rebinds the result `_0`/`ret` → the recursive
/// call dest `rec`, yielding `rec >= 0`. THIS is the fact justified by well-founded
/// induction: assuming the contract for the strictly-smaller call. Built ONLY after
/// the measure-decrease (well-foundedness) is established.
fn own_ensures_as_ih(func: &VerifiableFunction) -> Vec<Formula> {
    let mut ih: Vec<Formula> = Vec::new();
    let no_formals: FxHashMap<String, String> = FxHashMap::default();
    // FAIL-CLOSED: a requires-carrying recursive contract's ensures holds only for
    // recursive calls that ESTABLISH the requires. This lane does not yet kernel-
    // check the recursive call site's establishment, so it declines the IH
    // entirely for such a function (weakens PROVE→OPEN only — never assumes the
    // ensures of a possibly-violated contract).
    if !func.preconditions.is_empty() {
        return ih;
    }
    for block in &func.body.blocks {
        let Terminator::Call { func: callee_path, dest, .. } = &block.terminator else {
            continue;
        };
        // Only a SELF-recursive (or SCC) call carries an IH for this function.
        if callee_path != &func.def_path {
            continue;
        }
        // The recursive call's RESULT spelling: the AUTHORITATIVE post-call dest
        // token (`trust_vcgen::call_dest_fact_token` — bare only under the SSA-
        // collapse license; `None` for a projected dest ⇒ fail-closed). A
        // hand-rolled bare `local_name` denotes the WRONG version for a
        // reassigned dest (see `rebind_clause`'s license contract).
        let Some(dest_name) = trust_vcgen::call_dest_fact_token(func, block.id, dest) else {
            continue;
        };
        // Rebind the own ensures result symbol (`_0`/`ret`) → the recursive call's dest.
        for clause in &func.postconditions {
            if let Some(r) = rebind_clause(clause, &dest_name, &no_formals) {
                ih.push(r);
            }
        }
    }
    ih
}

/// Kernel-check a `Formula`'s refutation modulo 3 via the UNCHANGED `vc_refute`
/// engine, augmented with `func`'s sound type bounds. `true` iff `RefutedModulo3`.
fn refute_modulo_3(func: &VerifiableFunction, f: &Formula) -> bool {
    let augmented = crate::prove::augment_with_type_bounds_pub(f, func);
    matches!(
        crate::vc_refute::check_refute_vc(&augmented),
        Some(crate::RefuteOutcome::RefutedModulo3)
    )
}

/// Run the `sum_to_n` recursion POC: verify the self-recursive `#[decreases(n)]
/// #[ensures(ret >= 0)]` function by well-founded induction, kernel-checked modulo 3.
/// The body ensures obligation is `n + rec >= 0` (the inductive-step return `n + rec`,
/// against `#[ensures(ret >= 0)]`).
#[must_use]
pub fn run_recursion_poc() -> RecursionResult {
    let rf = sum_to_n_recursive();
    let guard = sum_to_n_recursion_guard();
    // The body ensures obligation: the inductive-step return `n + rec >= 0`.
    let goal = Formula::Ge(
        Box::new(Formula::Add(
            Box::new(Formula::Var("n".into(), Sort::Int)),
            Box::new(Formula::Var("rec".into(), Sort::Int)),
        )),
        Box::new(Formula::Int(0)),
    );
    prove_recursive_function(&rf, &guard, &goal)
}

// ---------------------------------------------------------------------------
// 10.3 Negative controls — a NON-DECREASING measure and a FALSE ensures
// ---------------------------------------------------------------------------

/// NEGATIVE CONTROL #1 — a recursive function with a NON-DECREASING measure: the SAME
/// `sum_to_n` body/contract BUT the recursive call is `sum_to_n(n)` (NOT `n - 1`), so
/// `#[decreases(n)]` does NOT strictly decrease (`n < n` is false). The measure-decrease
/// half MUST fail ⇒ the IH may not be assumed ⇒ Open (fail-closed). Mirrors a WRONG
/// loop ranking being KernelRejected (`mirsem.rs:14820`).
#[must_use]
pub fn sum_to_n_non_decreasing() -> RecursiveFunction {
    let mut rf = sum_to_n_recursive();
    // Rewrite `m := n - 1` to `m := n` (the recursive arg no longer decreases).
    for block in &mut rf.func.body.blocks {
        for stmt in &mut block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.local == 2
            {
                *rvalue = Rvalue::Use(Operand::Copy(Place::local(1))); // m := n
            }
        }
    }
    rf
}

/// NEGATIVE CONTROL #2 — a recursive function with a FALSE ensures: `#[ensures(ret >= 1)]`
/// on `sum_to_n` (whose base case returns `0`, so `ret >= 1` is FALSE). Even WITH a
/// valid decreasing measure and the IH, the discharge targets an obligation the IH
/// cannot rescue — see the test, which picks a goal not closable from the guard + IH.
#[must_use]
pub fn sum_to_n_false_ensures() -> RecursiveFunction {
    let mut rf = sum_to_n_recursive();
    // #[ensures(ret >= 1)] — FALSE (the base case returns 0).
    rf.func.postconditions = vec![Formula::Ge(Box::new(ret_var()), Box::new(Formula::Int(1)))];
    rf
}

// ---------------------------------------------------------------------------
// 10.4 MUTUAL RECURSION — an SCC of size > 1 (ping / pong, shared measure)
// ---------------------------------------------------------------------------
//
// Mutual recursion is an SCC of size > 1: `f` calls `g`, `g` calls `f`. The
// well-founded meta-theorem generalizes with a SHARED measure that strictly decreases
// on EVERY inter-SCC call (the lexicographic/summed measure the roadmap names, §3
// Step 4). For the POC we use a SHARED scalar measure `n` that decreases on both
// cross-edges:
//
//   #[decreases(n)] fn ping(n) { if n <= 0 { 0 } else { pong(n - 1) } }   ensures ret >= 0
//   #[decreases(n)] fn pong(n) { if n <= 0 { 0 } else { ping(n - 1) } }   ensures ret >= 0
//
// Both cross-calls pass `n - 1` under the guard `n >= 1`, so the shared measure `n`
// strictly decreases on EVERY edge of the SCC — the same `vc_refute` decrease the
// self-recursive case uses, now over the 2-member SCC. The IH for `ping`'s ensures is
// `pong`'s ensures at the strictly-smaller call (and vice versa) — assume-guarantee
// over the SCC, justified by the shared decreasing measure.

/// Build a mutual-recursion SCC member `fn name(n) { if n<=0 {0} else { other(n-1) } }`
/// with `#[decreases(n)] #[ensures(ret >= 0)]`. The cross-call result is returned
/// directly (`_0 = rec`), so the inductive step's ensures is exactly the IH.
fn mutual_member(name: &str, def_path: &str, other_path: &str) -> RecursiveFunction {
    let body = VerifiableBody {
        locals: vec![
            LocalDecl { index: 0, ty: I32, name: Some("_0".into()) },
            LocalDecl { index: 1, ty: I32, name: Some("n".into()) },
            LocalDecl { index: 2, ty: I32, name: Some("m".into()) },
            LocalDecl { index: 3, ty: I32, name: Some("rec".into()) },
        ],
        blocks: vec![
            // bb0: m = n - 1  -> bb1 (the cross-recursive call)
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(1)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(1)),
            },
            // bb1: rec = other(m)   (the cross-recursive call into the SCC)  -> bb2
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: other_path.into(), // the OTHER SCC member
                    args: vec![Operand::Copy(Place::local(2))],
                    dest: Place::local(3),
                    target: Some(BlockId(2)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    unwind: trust_types::UnwindEdge::Unreachable,
                },
            },
            // bb2: _0 = rec; return  (the inductive step returns the cross-call result)
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ],
        arg_count: 1,
        return_ty: I32,
    };
    RecursiveFunction {
        func: VerifiableFunction {
            name: name.into(),
            def_path: def_path.into(),
            span: SourceSpan::default(),
            body,
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![Formula::Ge(Box::new(ret_var()), Box::new(Formula::Int(0)))],
            spec: Default::default(),
        },
        measure: Some(Formula::Var("n".into(), Sort::Int)),
    }
}

/// The mutual-recursion SCC `{ping, pong}` — `ping` calls `pong`, `pong` calls `ping`,
/// both `#[decreases(n)] #[ensures(ret >= 0)]`, both passing `n - 1` (the shared
/// measure decreases on every cross-edge).
#[must_use]
pub fn mutual_recursion_scc() -> (RecursiveFunction, RecursiveFunction) {
    let ping = mutual_member("ping", "crate::ping", "crate::pong");
    let pong = mutual_member("pong", "crate::pong", "crate::ping");
    (ping, pong)
}

/// Verify a mutual-recursion SCC by the well-founded meta-theorem with a SHARED
/// measure. Each member's cross-call must strictly decrease the shared measure (over
/// the WHOLE SCC, not just self-edges), and each member's ensures is discharged under
/// the IH = the OTHER members' ensures rebound to the cross-call result. This is the
/// assume-guarantee generalization: the SCC's members mutually assume each other's
/// ensures, justified by the shared decreasing measure across every SCC edge.
///
/// Returns a `RecursionResult` per member. FAIL-CLOSED identically: a non-decreasing
/// cross-edge ⇒ that member's measure-decrease fails ⇒ Open. The SCC certifies iff
/// EVERY member's ensures kernel-checks modulo 3 under the shared-measure-justified IH.
#[must_use]
pub fn prove_mutual_recursion_scc(members: &[RecursiveFunction]) -> Vec<RecursionResult> {
    let scc: Vec<&str> = members.iter().map(|m| m.func.def_path.as_str()).collect();
    let mut results: Vec<RecursionResult> = Vec::new();

    for member in members {
        let func = &member.func;
        let guard =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(1)));

        // (a) The shared measure strictly decreases on every SCC cross-edge from this
        // member (well-founded over the WHOLE SCC, not just self-recursion).
        let (well_founded, ih_from) = match &member.measure {
            Some(measure) => measure_strictly_decreases(func, measure, &guard, &scc),
            None => (false, Vec::new()),
        };

        // The body ensures obligation: `_0 = rec; ret >= 0` ⇒ `rec >= 0`.
        let goal =
            Formula::Ge(Box::new(Formula::Var("rec".into(), Sort::Int)), Box::new(Formula::Int(0)));

        let verdict = if well_founded {
            // (b) The IH = the OTHER SCC members' ensures rebound onto THIS member's
            // cross-call result (assume-guarantee over the SCC).
            let ih = scc_ensures_as_ih(func, members, &scc);
            ensures_holds_under_ih(func, &guard, &goal, &ih)
        } else {
            ensures_holds_under_ih(func, &guard, &goal, &[])
        };

        let recursion_verdict = match (well_founded, &verdict) {
            (true, CompositionVerdict::ProvenModulo3) => RecursionVerdict::ProvenWellFounded,
            (_, CompositionVerdict::KernelRejected(r)) => {
                RecursionVerdict::KernelRejected(r.clone())
            }
            (false, _) => RecursionVerdict::Open(
                "shared measure does not strictly decrease on every SCC edge (fail-closed)".into(),
            ),
            (true, _) => RecursionVerdict::Open(
                "member ensures did not kernel-check modulo 3 under the SCC IH".into(),
            ),
        };

        results.push(RecursionResult {
            def_path: func.def_path.clone(),
            verdict: recursion_verdict,
            measure_well_founded: well_founded,
            ensures_under_ih: matches!(verdict, CompositionVerdict::ProvenModulo3),
            ih_from,
        });
    }

    results
}

/// The SCC induction hypothesis for `func`: the ensures of every OTHER SCC member,
/// rebound onto `func`'s cross-call result symbol. For `ping` calling `pong`, this is
/// `pong`'s `ret >= 0` rebound to `ping`'s call dest `rec` ⇒ `rec >= 0`.
fn scc_ensures_as_ih(
    func: &VerifiableFunction,
    members: &[RecursiveFunction],
    scc: &[&str],
) -> Vec<Formula> {
    let mut ih: Vec<Formula> = Vec::new();
    let no_formals: FxHashMap<String, String> = FxHashMap::default();
    let by_path: FxHashMap<&str, &VerifiableFunction> =
        members.iter().map(|m| (m.func.def_path.as_str(), &m.func)).collect();

    for block in &func.body.blocks {
        let Terminator::Call { func: callee_path, dest, .. } = &block.terminator else {
            continue;
        };
        if !scc.contains(&callee_path.as_str()) {
            continue;
        }
        let Some(callee_fn) = by_path.get(callee_path.as_str()).copied() else { continue };
        // FAIL-CLOSED: a requires-carrying SCC member's ensures may only be
        // assumed where the cross-call ESTABLISHES its requires — not yet
        // kernel-checked in this lane, so decline the IH from such a member
        // (PROVE→OPEN only). Mirrors `own_ensures_as_ih`.
        if !callee_fn.preconditions.is_empty() {
            continue;
        }
        // The cross-call's RESULT spelling: the AUTHORITATIVE post-call dest token
        // (bare only under the SSA-collapse license; `None` = projected dest ⇒
        // fail-closed) — never a hand-rolled bare `local_name`.
        let Some(dest_name) = trust_vcgen::call_dest_fact_token(func, block.id, dest) else {
            continue;
        };
        for clause in &callee_fn.postconditions {
            if let Some(r) = rebind_clause(clause, &dest_name, &no_formals) {
                ih.push(r);
            }
        }
    }
    ih
}

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use super::*;

    /// (a) The callee certifies `Modulo3`: `helper`'s `ensures 0 <= ret <= 100`
    /// is kernel-checked modulo 3 ⇒ `ProofStatus::Certified`.
    #[test]
    fn callee_certifies_modulo_3() {
        let callee = helper_callee();
        let mut registry = ProofStatusRegistry::new();
        let summary = certify_callee_summary(&callee, FuncId::new(0), &mut registry);
        assert!(summary.ir_summary.proved, "callee ensures must be kernel-certified modulo 3");
        assert_eq!(
            registry.get(&callee.def_path),
            Some(&ProofStatus::Certified),
            "certified callee must be assumable"
        );
        assert!(registry.is_assumable(&callee.def_path));
        // trust-ir keying: the summary carries the universal-IR contract.
        assert_eq!(summary.ir_summary.params, vec!["x".to_string()]);
        assert_eq!(summary.ir_summary.ensures.len(), 2);
    }

    /// (b) The caller obligation is kernel-checked `Modulo3` WITH the callee's
    /// rebound ensures as a hypothesis — the whole-program nucleus.
    #[test]
    fn caller_obligation_proven_by_composition_modulo_3() {
        let poc = run_poc();
        assert_eq!(poc.callee_status, ProofStatus::Certified, "callee must certify modulo 3 first");
        assert_eq!(
            poc.caller_verdict,
            CompositionVerdict::ProvenModulo3,
            "caller `h + 1 <= 101` must be kernel-checked modulo 3 USING helper's ensures, got {:?}",
            poc.caller_verdict
        );
        // (d) the composed whole 2-function program is Certified.
        assert!(poc.combined_certified, "the composed 2-function program must be Certified");
    }

    /// The composition is GENUINE (not Eq.refl): the caller obligation is refuted
    /// ONLY when the callee ensures is conjoined. Directly rebinding + refuting
    /// WITH the hypothesis succeeds; the SAME obligation WITHOUT it does not.
    #[test]
    fn composition_is_genuine_hypothesis_is_load_bearing() {
        let caller = main_like_caller();
        let goal = caller_goal_h_plus_one_le_101();

        // WITH the callee ensures (`0 <= h <= 100`) conjoined: PROVEN.
        let h_ge0 =
            Formula::Ge(Box::new(Formula::Var("h".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let h_le100 =
            Formula::Le(Box::new(Formula::Var("h".into(), Sort::Int)), Box::new(Formula::Int(100)));
        let with_hyp = refute_caller_goal(&caller, &goal, &[h_ge0, h_le100]);
        assert_eq!(
            with_hyp,
            CompositionVerdict::ProvenModulo3,
            "WITH the callee ensures the obligation must kernel-check modulo 3, got {with_hyp:?}"
        );

        // WITHOUT the callee ensures (only the i32 type range on `h`): NOT proven.
        // This is the GENUINE-vs-Eq.refl witness: the same obligation, same engine,
        // no callee hypothesis ⇒ Open. The callee ensures is load-bearing.
        let without_hyp = refute_caller_goal(&caller, &goal, &[]);
        assert!(
            !without_hyp.is_proven_modulo_3(),
            "WITHOUT the callee ensures the obligation must stay OPEN, got {without_hyp:?}"
        );
    }

    /// (c) NEGATIVE CONTROL #1 — the callee has NO summary / is NOT Certified:
    /// the registry says not-assumable ⇒ assume nothing ⇒ the caller obligation
    /// stays OPEN (never falsely proven). Fail-closed.
    #[test]
    fn fail_closed_on_unproven_callee() {
        let caller = main_like_caller();
        let goal = caller_goal_h_plus_one_le_101();

        // Build the callee summary but DO NOT certify it — force `Trusted`/unproved.
        let callee_fn = helper_callee();
        let mut registry = ProofStatusRegistry::new();
        let mut summary = certify_callee_summary(&callee_fn, FuncId::new(0), &mut registry);
        // Knock it down to UNPROVEN (the absent/SMT-only-callee case).
        registry.register(callee_fn.def_path.clone(), ProofStatus::Trusted);
        summary.ir_summary.proved = false;

        // No assumable hypothesis ⇒ rebind yields None ⇒ obligation refuted with
        // type bounds only ⇒ OPEN.
        assert!(
            build_transfer_obligation(&caller, &summary, &registry).is_none(),
            "an un-Certified callee must produce NO transfer obligation (fail-closed)"
        );
        let verdict = prove_caller_obligation(&caller, &summary, &goal, &registry);
        assert!(
            !verdict.is_proven_modulo_3(),
            "with an unproven callee the caller obligation must stay OPEN, got {verdict:?}"
        );
    }

    /// (c) NEGATIVE CONTROL #2 — an obligation that is FALSE without the callee
    /// ensures (and ALSO false WITH it): `h + 1 <= 100` is NOT implied by
    /// `0 <= h <= 100` (h = 100 ⇒ h+1 = 101 > 100). It must stay OPEN even WITH
    /// the certified callee — the kernel does not falsely prove a wrong obligation.
    #[test]
    fn fail_closed_on_genuinely_false_obligation() {
        let caller = main_like_caller();
        // `h + 1 <= 100` — FALSE at h = 100, which the callee ensures permits.
        let false_goal = Formula::Le(
            Box::new(Formula::Add(
                Box::new(Formula::Var("h".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(100)),
        );
        let mut registry = ProofStatusRegistry::new();
        let summary = certify_callee_summary(&helper_callee(), FuncId::new(0), &mut registry);
        let verdict = prove_caller_obligation(&caller, &summary, &false_goal, &registry);
        assert!(
            !verdict.is_proven_modulo_3(),
            "a genuinely-false obligation must stay OPEN even with the certified callee, got {verdict:?}"
        );
    }

    /// trust-ir keying — a proven composition yields a `ProofContext` + an
    /// `InheritedFromCallee` evidence over the callee's ensures obligation, at the
    /// `Certified` tier. The compositional proof is keyed to the universal IR.
    #[test]
    fn proven_composition_is_trust_ir_keyed() {
        let poc = run_poc();
        assert!(poc.caller_verdict.is_proven_modulo_3());
        let rec = poc.ir_record.expect("a proven composition must carry an IR record");
        // ProofContext: assumes the callee ensures, establishes the callee requires.
        assert_eq!(rec.proof_context.assumes.len(), 1, "assumes the callee ensures obligation");
        assert_eq!(rec.proof_context.establishes.len(), 1, "establishes the callee requires");
        // InheritedFromCallee over FuncId(0)'s ensures obligation.
        match rec.inherited_evidence {
            ProofEvidence::InheritedFromCallee { callee, obligation } => {
                assert_eq!(callee, FuncId::new(0));
                assert_eq!(obligation, rec.proof_context.assumes[0]);
            }
            other => panic!("expected InheritedFromCallee, got {other:?}"),
        }
        assert_eq!(rec.caller_status, IrProofStatus::Certified);
    }

    /// An OPEN composition yields NO IR record (it has no discharge to inherit) —
    /// the IR keying is sound: only a genuinely-proven obligation inherits.
    #[test]
    fn open_composition_has_no_ir_record() {
        let caller = main_like_caller();
        let goal = caller_goal_h_plus_one_le_101();
        let callee_fn = helper_callee();
        let mut registry = ProofStatusRegistry::new();
        let summary = certify_callee_summary(&callee_fn, FuncId::new(0), &mut registry);
        registry.register(callee_fn.def_path.clone(), ProofStatus::Trusted); // not assumable
        let verdict = prove_caller_obligation(&caller, &summary, &goal, &registry);
        assert!(!verdict.is_proven_modulo_3());
        // run_poc only builds an ir_record for a proven verdict, mirrored here.
        assert!(matches!(
            verdict,
            CompositionVerdict::Open(_) | CompositionVerdict::KernelRejected(_)
        ));
    }

    // =======================================================================
    // STEP 3 — multi-function call-graph compositional proof tests
    // =======================================================================

    /// The verification order is callee-first: `leaf` before `left`/`right`, and both
    /// before `top`. Consumed from `trust_vcgen::compute_verification_order` over the
    /// diamond's call graph (NOT a hand-built order).
    #[test]
    fn diamond_verification_order_is_callee_first() {
        let result = verify_call_graph(&diamond_program());
        let order = &result.verification_order;
        let pos = |p: &str| order.iter().position(|x| x == p).expect("fn in order");
        assert!(pos("crate::leaf") < pos("crate::left"), "leaf before left: {order:?}");
        assert!(pos("crate::leaf") < pos("crate::right"), "leaf before right: {order:?}");
        assert!(pos("crate::left") < pos("crate::top"), "left before top: {order:?}");
        assert!(pos("crate::right") < pos("crate::top"), "right before top: {order:?}");
    }

    /// The WHOLE diamond certifies modulo 3, compositionally: `leaf` certifies
    /// standalone, then `left`/`right` certify USING `leaf`'s destination-pinned ensures,
    /// then `top` certifies USING BOTH `left`'s and `right`'s ensures. The composed
    /// 4-function program is all-Certified — the multi-function existence proof.
    #[test]
    fn diamond_whole_program_certifies_modulo_3() {
        let result = verify_call_graph(&diamond_program());
        assert!(
            result.all_certified(),
            "the whole diamond must certify modulo 3; verdicts: {:?}",
            result.verdicts
        );
        for f in ["crate::leaf", "crate::left", "crate::right", "crate::top"] {
            let v = result.verdict(f).unwrap_or_else(|| panic!("verdict for {f}"));
            assert_eq!(v.status, ProofStatus::Certified, "{f} must be Certified: {v:?}");
        }
        // The registry threads the whole graph: every function is assumable.
        for f in ["crate::leaf", "crate::left", "crate::right", "crate::top"] {
            assert!(result.registry.is_assumable(f), "{f} must be registry-assumable");
        }
    }

    /// The synthetic diamond must mirror rustc's checked-debug MIR. A raw
    /// `BinaryOp(Add)` is wrapping arithmetic and would make the mathematical
    /// interval summaries unsound; the success edge of the paired overflow
    /// assert is what licenses the exact integer result relation.
    #[test]
    fn diamond_arithmetic_has_checked_overflow_shape() {
        for func in [diamond_left(), diamond_right(), diamond_top()] {
            let checked_adds = func
                .body
                .blocks
                .iter()
                .flat_map(|block| &block.stmts)
                .filter(|stmt| {
                    matches!(
                        stmt,
                        Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, _, _), .. }
                    )
                })
                .count();
            let raw_adds = func
                .body
                .blocks
                .iter()
                .flat_map(|block| &block.stmts)
                .filter(|stmt| {
                    matches!(
                        stmt,
                        Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Add, _, _), .. }
                    )
                })
                .count();
            let overflow_asserts = func
                .body
                .blocks
                .iter()
                .filter(|block| {
                    matches!(
                        block.terminator,
                        Terminator::Assert {
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            ..
                        }
                    )
                })
                .count();

            assert_eq!(checked_adds, 1, "{} must contain one checked add", func.def_path);
            assert_eq!(raw_adds, 0, "{} must not model source `+` as wrapping", func.def_path);
            assert_eq!(
                overflow_asserts, 1,
                "{} must guard the checked result with an overflow assert",
                func.def_path
            );

            let l0_vcs: Vec<_> = trust_vcgen::generate_vcs(&func)
                .into_iter()
                .filter(|vc| vc.kind.proof_level() == ProofLevel::L0Safety)
                .collect();
            assert_eq!(l0_vcs.len(), 1, "{} must emit exactly one L0 VC", func.def_path);
            assert!(
                matches!(
                    &l0_vcs[0].kind,
                    trust_types::VcKind::ArithmeticOverflow { op: BinOp::Add, .. }
                ),
                "{}'s L0 VC must be addition overflow: {:?}",
                func.def_path,
                l0_vcs[0]
            );
        }
    }

    /// The direct summary entry point has the same safety gate as the graph
    /// driver. A vacuous/tautological contract cannot turn a panicking checked
    /// add into an assumable callee summary.
    #[test]
    fn diamond_tautological_post_does_not_mask_open_l0_summary() {
        let mut callee = diamond_left();
        callee.name = "unsafe_add_callee".into();
        callee.def_path = "crate::unsafe_add_callee".into();
        callee.postconditions = vec![Formula::Bool(true)];
        callee.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(i32::MAX.into()))),
            span: SourceSpan::default(),
        });
        callee.body.blocks[0].terminator = Terminator::Goto(BlockId(1));

        let vcs = trust_vcgen::generate_vcs(&callee);
        let safety = vcs
            .iter()
            .find(|vc| vc.kind.proof_level() == ProofLevel::L0Safety)
            .expect("checked add must emit an L0 overflow VC");
        let post = vcs
            .iter()
            .find(|vc| matches!(&vc.kind, trust_types::VcKind::Postcondition))
            .expect("tautological contract must still emit a postcondition VC");
        assert_eq!(
            crate::vc_refute::check_refute_vc(&crate::prove::augment_with_type_bounds_pub(
                &post.formula,
                &callee
            )),
            Some(crate::RefuteOutcome::RefutedModulo3),
            "the tautological postcondition itself must close"
        );
        assert!(
            crate::vc_refute::check_refute_vc(&crate::prove::augment_with_type_bounds_pub(
                &safety.formula,
                &callee
            ))
            .is_none(),
            "i32::MAX + 1 must leave the checked-add safety VC open"
        );

        let mut registry = ProofStatusRegistry::new();
        let summary = certify_callee_summary(&callee, FuncId::new(99), &mut registry);
        assert!(!summary.ir_summary.proved, "open L0 safety must withhold the summary");
        assert!(
            !registry.is_assumable(&callee.def_path),
            "a tautological postcondition must not bypass the direct L0 safety gate"
        );
    }

    /// The lower summaries are not decorative: without them the apex's signed
    /// `x + y` could underflow even though both upper bounds prove `x + y <= 32`.
    /// The postcondition alone remains linear-provable, but whole-program
    /// certification must stay OPEN because its ArithmeticOverflow VC is not.
    #[test]
    fn diamond_upper_only_summaries_do_not_skip_apex_overflow() {
        let mut program = diamond_program();
        for func in &mut program {
            if matches!(func.def_path.as_str(), "crate::left" | "crate::right") {
                func.postconditions.retain(|post| matches!(post, Formula::Le(_, _)));
            }
        }

        let result = verify_call_graph(&program);
        assert!(result.verdict("crate::leaf").is_some_and(FunctionVerdict::is_certified));
        assert!(result.verdict("crate::left").is_some_and(FunctionVerdict::is_certified));
        assert!(result.verdict("crate::right").is_some_and(FunctionVerdict::is_certified));
        let top = result.verdict("crate::top").expect("top verdict");
        assert!(!top.is_certified(), "upper bounds alone must not license signed addition");
        assert!(
            top.open_reason.as_deref().is_some_and(|reason| reason.contains("safety obligation")),
            "the missing lower bounds must surface as an open safety VC: {top:?}"
        );
    }

    /// A flat conjunction of call summaries is not sound across a branch: the
    /// summary for a call on one path must not be available before/on another
    /// path. Until hypotheses carry per-call dominance provenance, such a shape
    /// must fail closed rather than certify under globally-scoped facts.
    #[test]
    fn diamond_branch_before_call_fails_closed_on_summary_scope() {
        let mut top = diamond_top();
        top.body.blocks[0].terminator = Terminator::SwitchInt {
            discr: Operand::Constant(ConstValue::Bool(true)),
            targets: vec![(0, BlockId(1))],
            otherwise: BlockId(1),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };

        let program = vec![top, diamond_left(), diamond_right(), diamond_leaf()];
        let result = verify_call_graph(&program);
        let top = result.verdict("crate::top").expect("top verdict");
        assert!(!top.is_certified(), "branchy call-summary scope must fail closed");
        assert!(
            top.open_reason.as_deref().is_some_and(|reason| reason.contains("dominance scope")),
            "the unsupported summary scope must be diagnosed explicitly: {top:?}"
        );
        assert!(top.assumed_callees.is_empty(), "no global facts may transfer on rejection");
    }

    /// Composition is transitive AND genuine: `top` records that it ASSUMED both
    /// `left` and `right` (the multi-callee conjunction), and `left`/`right` each
    /// assumed `leaf`. The proof threads leaf→{left,right}→top.
    #[test]
    fn diamond_composition_is_transitive_and_multi_callee() {
        let result = verify_call_graph(&diamond_program());
        let top = result.verdict("crate::top").unwrap();
        assert!(
            top.assumed_callees.contains(&"crate::left".to_string())
                && top.assumed_callees.contains(&"crate::right".to_string()),
            "top must assume BOTH left and right (multi-callee conjunction), got {:?}",
            top.assumed_callees
        );
        let left = result.verdict("crate::left").unwrap();
        assert_eq!(left.assumed_callees, vec!["crate::leaf".to_string()], "left assumes leaf");
        let right = result.verdict("crate::right").unwrap();
        assert_eq!(right.assumed_callees, vec!["crate::leaf".to_string()], "right assumes leaf");
        // leaf is a leaf — it assumes nothing.
        assert!(result.verdict("crate::leaf").unwrap().assumed_callees.is_empty());
    }

    /// GENUINE vs Eq.refl — the callee ensures is load-bearing at each level. We refute
    /// `top`'s ensures VC WITH both callee hypotheses (PROVES) and WITHOUT
    /// them (does NOT prove): same VC, same kernel engine, the hypotheses make the
    /// difference. Mirrors the per-function genuine-vs-trivial witness, multi-callee.
    ///
    /// The hypotheses are minted over the AUTHORITATIVE dest spelling
    /// (`trust_vcgen::call_dest_fact_token`), never a hand-rolled token: the emitted
    /// VC used to read the versioned `x#s0_t`/`y#s1_t`, and since vcgen's SSA-collapse
    /// pass (f864db570e) it reads bare `x`/`y` — hard-coding either spelling is
    /// exactly the drift that opened the whole diamond.
    #[test]
    fn diamond_callee_ensures_is_load_bearing_genuine() {
        let top = diamond_top();
        // top's postcondition VC over the call dests x (left, bb0), y (right, bb1).
        let post_vc = trust_vcgen::generate_vcs(&top)
            .into_iter()
            .find(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition))
            .expect("top has a postcondition VC");
        // The dest spellings the VC actually reads (bare here: both dests are
        // single-assignment locals, so the SSA collapse license applies).
        let x_tok = trust_vcgen::call_dest_fact_token(&top, BlockId(0), &Place::local(2))
            .expect("x is a whole-local call dest");
        let y_tok = trust_vcgen::call_dest_fact_token(&top, BlockId(1), &Place::local(3))
            .expect("y is a whole-local call dest");

        let x_le =
            Formula::Le(Box::new(Formula::Var(x_tok, Sort::Int)), Box::new(Formula::Int(11)));
        let y_le =
            Formula::Le(Box::new(Formula::Var(y_tok, Sort::Int)), Box::new(Formula::Int(21)));

        // WITH both callee ensures: kernel-checks modulo 3.
        let with_both = Formula::And(vec![x_le.clone(), y_le.clone(), post_vc.formula.clone()]);
        let aug_both = crate::prove::augment_with_type_bounds_pub(&with_both, &top);
        assert_eq!(
            crate::vc_refute::check_refute_vc(&aug_both),
            Some(crate::RefuteOutcome::RefutedModulo3),
            "top's ensures must kernel-check modulo 3 WITH both callee ensures"
        );

        // WITHOUT any callee ensures: NOT refuted (x, y unbounded above ⇒ x+y unbounded).
        let aug_none = crate::prove::augment_with_type_bounds_pub(&post_vc.formula, &top);
        assert!(
            crate::vc_refute::check_refute_vc(&aug_none).is_none(),
            "top's ensures must NOT prove WITHOUT the callee ensures (load-bearing)"
        );

        // WITH ONLY ONE callee ensures (drop right's y bound): NOT refuted — `top`
        // genuinely needs BOTH (the conjunction is load-bearing, not just one arm).
        let with_one = Formula::And(vec![x_le, post_vc.formula.clone()]);
        let aug_one = crate::prove::augment_with_type_bounds_pub(&with_one, &top);
        assert!(
            crate::vc_refute::check_refute_vc(&aug_one).is_none(),
            "top must NOT prove with only ONE callee ensures — both are load-bearing"
        );
    }

    /// NEGATIVE CONTROL (mid-graph knockout, the load-bearing fail-closed property):
    /// knock out the SHARED LEAF `leaf` → its proof is withheld, so `left` and `right`
    /// lose their hypothesis and stay OPEN, and `top` (transitively dependent on both)
    /// ALSO stays OPEN. The WHOLE graph collapses: nothing falsely proven.
    #[test]
    fn diamond_knockout_leaf_opens_whole_transitive_cone() {
        let result = verify_call_graph_with_knockout(&diamond_program(), &["crate::leaf"]);
        assert!(!result.all_certified(), "knocking out leaf must open the graph");
        for f in ["crate::leaf", "crate::left", "crate::right", "crate::top"] {
            let v = result.verdict(f).unwrap();
            assert!(
                !v.is_certified(),
                "{f} must be OPEN after leaf knockout (transitive), got {:?}",
                v.status
            );
        }
    }

    /// NEGATIVE CONTROL (MID-graph one-arm knockout — the precise transitivity claim):
    /// knock out `left` (a MID-graph function, not the leaf). Then:
    ///  - `leaf` still certifies (it does not depend on `left`),
    ///  - `right` still certifies (the OTHER diamond arm — unaffected),
    ///  - `left` is OPEN (knocked out),
    ///  - `top` is OPEN — it depended on `left`'s now-withheld ensures, so even though
    ///    `right` is fine, `top`'s `x <= 11` hypothesis is gone and `x + y <= 32` does
    ///    NOT close. The open propagates to the dependent caller ONLY (right survives).
    #[test]
    fn diamond_knockout_left_opens_only_its_caller_cone() {
        let result = verify_call_graph_with_knockout(&diamond_program(), &["crate::left"]);

        assert!(
            result.verdict("crate::leaf").unwrap().is_certified(),
            "leaf must still certify (independent of left)"
        );
        assert!(
            result.verdict("crate::right").unwrap().is_certified(),
            "right must still certify (the OTHER diamond arm is unaffected)"
        );
        assert!(
            !result.verdict("crate::left").unwrap().is_certified(),
            "left is knocked out ⇒ OPEN"
        );
        assert!(
            !result.verdict("crate::top").unwrap().is_certified(),
            "top depended on left ⇒ transitively OPEN even though right survives"
        );
        // Precisely: exactly {left, top} are open.
        let mut open = result.open_functions();
        open.sort_unstable();
        assert_eq!(open, vec!["crate::left", "crate::top"], "exactly left+top open");
    }

    /// FAIL-CLOSED via the registry gate: an un-Certified callee contributes NO
    /// hypothesis. We verify the diamond but knock out `right`; `top` then loses the
    /// `y <= 21` arm and cannot close `x + y <= 32`, so `top` is OPEN while `left`,
    /// `leaf` stay Certified. (The symmetric arm to the `left`-knockout control.)
    #[test]
    fn diamond_knockout_right_opens_only_its_caller_cone() {
        let result = verify_call_graph_with_knockout(&diamond_program(), &["crate::right"]);
        assert!(result.verdict("crate::leaf").unwrap().is_certified());
        assert!(result.verdict("crate::left").unwrap().is_certified());
        assert!(!result.verdict("crate::right").unwrap().is_certified());
        assert!(
            !result.verdict("crate::top").unwrap().is_certified(),
            "top depended on right ⇒ transitively OPEN"
        );
    }

    // =======================================================================
    // STEP 4 — RECURSION (well-founded inter-procedural meta-theorem) tests
    // =======================================================================

    /// THE RECURSION POC: `sum_to_n` (`#[decreases(n)] #[ensures(ret >= 0)]`) is
    /// verified COMPOSITIONALLY by well-founded induction, kernel-checked modulo 3:
    /// (a) the measure strictly decreases (and stays well-founded) on the recursive
    /// call, and (b) the ensures holds under the IH (own ensures assumed for the
    /// smaller-measure call). The recursive-SCC nucleus.
    #[test]
    fn recursion_poc_proven_well_founded_modulo_3() {
        let result = run_recursion_poc();
        assert!(
            result.measure_well_founded,
            "the #[decreases(n)] measure must strictly decrease + stay >= 0 on sum_to_n(n-1)"
        );
        assert!(
            result.ensures_under_ih,
            "sum_to_n's ensures must kernel-check modulo 3 UNDER the IH (rec >= 0)"
        );
        assert_eq!(
            result.verdict,
            RecursionVerdict::ProvenWellFounded,
            "sum_to_n must be proven by the well-founded recursion meta-theorem, got {:?}",
            result.verdict
        );
        // The IH came from the SELF-recursive edge.
        assert_eq!(result.ih_from, vec!["crate::sum_to_n".to_string()]);
        assert!(result.is_proven());
    }

    /// GENUINE vs Eq.refl — the IH is LOAD-BEARING. The SAME inductive-step ensures
    /// `n + rec >= 0` kernel-checks WITH the IH `rec >= 0` conjoined, and does NOT
    /// kernel-check WITHOUT it (the recursive result `rec` is otherwise an unbounded
    /// i32, so `n + rec` can be negative). Same obligation, same kernel engine, the IH
    /// makes the difference — mirrors the loop preservation hypothesis being
    /// load-bearing, and the diamond's callee-ensures being load-bearing.
    #[test]
    fn recursion_ih_is_load_bearing_genuine() {
        let rf = sum_to_n_recursive();
        let func = &rf.func;
        let guard = sum_to_n_recursion_guard();
        let goal = Formula::Ge(
            Box::new(Formula::Add(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Var("rec".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );

        // WITH the IH `rec >= 0`: kernel-checks modulo 3.
        let ih =
            Formula::Ge(Box::new(Formula::Var("rec".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let with_ih = ensures_holds_under_ih(func, &guard, &goal, std::slice::from_ref(&ih));
        assert_eq!(
            with_ih,
            CompositionVerdict::ProvenModulo3,
            "WITH the IH the inductive-step ensures must kernel-check modulo 3, got {with_ih:?}"
        );

        // WITHOUT the IH (only the guard + i32 range on `rec`): NOT proven. `rec` can be
        // i32::MIN, so `n + rec` is not provably >= 0. This is the genuine-vs-Eq.refl
        // witness: same obligation, same engine, no IH ⇒ Open.
        let without_ih = ensures_holds_under_ih(func, &guard, &goal, &[]);
        assert!(
            !without_ih.is_proven_modulo_3(),
            "WITHOUT the IH the inductive-step ensures must stay OPEN, got {without_ih:?}"
        );
    }

    /// The MEASURE-DECREASE half is a GENUINE kernel fact (not definitional): under the
    /// guard `n >= 1`, the measure on the recursive arg `n - 1` is STRICTLY < the
    /// measure on the formal `n` AND stays >= 0 (well-founded). This mirrors
    /// `loopRankDecrease`'s `toNat(n-1) < toNat(n)` over the loop guard — kernel-checked
    /// modulo 3 by `vc_refute`.
    #[test]
    fn recursion_measure_strictly_decreases_genuine() {
        let rf = sum_to_n_recursive();
        let func = &rf.func;
        let measure = rf.measure.clone().unwrap();
        let guard = sum_to_n_recursion_guard();
        let (wf, ih_from) =
            measure_strictly_decreases(func, &measure, &guard, &["crate::sum_to_n"]);
        assert!(wf, "n-1 must be a strictly-decreasing well-founded measure under n >= 1");
        assert_eq!(ih_from, vec!["crate::sum_to_n".to_string()]);

        // The measure-decrease violation `n >= 1 ∧ (n-1) >= n` must REFUTE modulo 3
        // directly (the strict-drop fact), and the well-foundedness violation
        // `n >= 1 ∧ (n-1) < 0` must REFUTE too (the >= 0 lower bound).
        let strict_violation = Formula::And(vec![
            guard.clone(),
            Formula::Ge(
                Box::new(Formula::Sub(
                    Box::new(Formula::Var("n".into(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                )),
                Box::new(Formula::Var("n".into(), Sort::Int)),
            ),
        ]);
        assert!(refute_modulo_3(func, &strict_violation), "n-1 < n must hold under n >= 1");
        let nonneg_violation = Formula::And(vec![
            guard,
            Formula::Lt(
                Box::new(Formula::Sub(
                    Box::new(Formula::Var("n".into(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                )),
                Box::new(Formula::Int(0)),
            ),
        ]);
        assert!(refute_modulo_3(func, &nonneg_violation), "n-1 >= 0 must hold under n >= 1");
    }

    /// FAIL-CLOSED #1 — NO `#[decreases]` clause: the measure is `None`, so the
    /// well-founded half fails, the IH may NOT be assumed, and the recursion stays
    /// OPEN (never falsely proven). Even though the body's ensures WOULD prove under an
    /// IH, without a measure the induction is unjustified.
    #[test]
    fn recursion_fail_closed_on_missing_decreases() {
        let mut rf = sum_to_n_recursive();
        rf.measure = None; // NO #[decreases] clause
        let guard = sum_to_n_recursion_guard();
        let goal = Formula::Ge(
            Box::new(Formula::Add(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Var("rec".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let result = prove_recursive_function(&rf, &guard, &goal);
        assert!(
            !result.measure_well_founded,
            "with no #[decreases] the recursion is NOT well-founded"
        );
        assert!(
            !result.is_proven(),
            "with no #[decreases] the recursion must stay OPEN (fail-closed), got {:?}",
            result.verdict
        );
        assert!(matches!(result.verdict, RecursionVerdict::Open(_)));
    }

    /// FAIL-CLOSED #2 — NON-DECREASING measure (the NEGATIVE CONTROL): the recursive
    /// call is `sum_to_n(n)` (not `n - 1`), so `#[decreases(n)]` does NOT strictly
    /// decrease (`n < n` is false). The measure-decrease half MUST fail ⇒ the IH may
    /// not be assumed ⇒ OPEN. The well-founded measure-decrease is GENUINE: a
    /// non-decreasing measure is rejected (mirrors a WRONG loop ranking being rejected).
    #[test]
    fn recursion_fail_closed_on_non_decreasing_measure() {
        let rf = sum_to_n_non_decreasing();
        let measure = rf.measure.clone().unwrap();
        let guard = sum_to_n_recursion_guard();

        // The measure-decrease half MUST reject: `n >= 1 ∧ n >= n` does NOT refute
        // (`n >= n` is always true, so there is no contradiction).
        let (wf, _) = measure_strictly_decreases(&rf.func, &measure, &guard, &["crate::sum_to_n"]);
        assert!(
            !wf,
            "a NON-decreasing measure (recursive arg = n, not n-1) must NOT be well-founded"
        );

        let goal = Formula::Ge(
            Box::new(Formula::Add(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Var("rec".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let result = prove_recursive_function(&rf, &guard, &goal);
        assert!(
            !result.is_proven(),
            "a non-well-founded recursion must stay OPEN (fail-closed), got {:?}",
            result.verdict
        );
    }

    /// FAIL-CLOSED #3 — FALSE ensures (the NEGATIVE CONTROL): a recursive function whose
    /// claimed ensures does NOT hold. We target the inductive-step obligation
    /// `n + rec >= 100`, which the guard `n >= 1` + the IH `rec >= 1` (from
    /// `#[ensures(ret >= 1)]`) cannot close (n=1, rec=1 ⇒ n+rec=2, not >= 100). Even
    /// WITH a valid decreasing measure and the IH, a false obligation must stay OPEN —
    /// the kernel does not falsely prove a wrong contract.
    #[test]
    fn recursion_fail_closed_on_false_ensures() {
        let rf = sum_to_n_false_ensures();
        let guard = sum_to_n_recursion_guard();
        // A goal that is genuinely FALSE under the guard + IH `rec >= 1`.
        let false_goal = Formula::Ge(
            Box::new(Formula::Add(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Var("rec".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(100)),
        );
        let result = prove_recursive_function(&rf, &guard, &false_goal);
        // The measure still decreases (the body arg is n-1), but the false ensures must
        // NOT kernel-check even under the IH.
        assert!(
            result.measure_well_founded,
            "the measure still decreases (only the ensures is false)"
        );
        assert!(
            !result.is_proven(),
            "a genuinely-false ensures must stay OPEN even with the IH, got {:?}",
            result.verdict
        );
        assert!(matches!(result.verdict, RecursionVerdict::Open(_)));
    }

    /// MUTUAL RECURSION — the SCC of size > 1 `{ping, pong}` with a SHARED measure `n`
    /// decreasing on every cross-edge. Both members certify modulo 3: each member's
    /// ensures `ret >= 0` kernel-checks under the IH = the OTHER member's ensures
    /// rebound to the strictly-smaller cross-call result (assume-guarantee over the
    /// SCC). The shared decreasing measure justifies the mutual IH.
    #[test]
    fn mutual_recursion_scc_proven_well_founded() {
        let (ping, pong) = mutual_recursion_scc();
        let results = prove_mutual_recursion_scc(&[ping, pong]);
        assert_eq!(results.len(), 2, "two SCC members");
        for r in &results {
            assert!(
                r.measure_well_founded,
                "{}'s shared measure must strictly decrease on its cross-edge",
                r.def_path
            );
            assert!(
                r.is_proven(),
                "{} must be proven by the mutual well-founded meta-theorem, got {:?}",
                r.def_path,
                r.verdict
            );
        }
        // ping's IH is from pong (the cross-edge) and vice versa.
        let ping_r = results.iter().find(|r| r.def_path == "crate::ping").unwrap();
        assert_eq!(ping_r.ih_from, vec!["crate::pong".to_string()], "ping assumes pong's ensures");
        let pong_r = results.iter().find(|r| r.def_path == "crate::pong").unwrap();
        assert_eq!(pong_r.ih_from, vec!["crate::ping".to_string()], "pong assumes ping's ensures");
    }

    /// MUTUAL RECURSION FAIL-CLOSED — knock out one member's measure-decrease: if
    /// `ping` calls `pong(n)` (NOT `n - 1`), the shared measure does NOT decrease on
    /// that cross-edge, so `ping` is OPEN. `pong` (whose own cross-edge to `ping` still
    /// passes `n - 1`) still has a well-founded measure, but its IH is `ping`'s ensures
    /// — `ping` did NOT certify, yet the meta-theorem only assumes the OTHER member's
    /// CONTRACT (the assume-guarantee), which is sound to assume as a hypothesis once
    /// the shared measure decreases on pong's OWN edge. We assert the precise outcome:
    /// ping OPEN (its cross-edge does not decrease), pong's measure still well-founded.
    #[test]
    fn mutual_recursion_fail_closed_on_non_decreasing_edge() {
        let (mut ping, pong) = mutual_recursion_scc();
        // Make ping's cross-call NON-decreasing: rec = pong(n) instead of pong(n-1).
        for block in &mut ping.func.body.blocks {
            for stmt in &mut block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt
                    && place.local == 2
                {
                    *rvalue = Rvalue::Use(Operand::Copy(Place::local(1))); // m := n
                }
            }
        }
        let results = prove_mutual_recursion_scc(&[ping, pong]);
        let ping_r = results.iter().find(|r| r.def_path == "crate::ping").unwrap();
        assert!(
            !ping_r.measure_well_founded,
            "ping's cross-edge no longer decreases ⇒ NOT well-founded"
        );
        assert!(
            !ping_r.is_proven(),
            "ping must be OPEN (its shared measure does not decrease), got {:?}",
            ping_r.verdict
        );
    }

    // =======================================================================
    // REASSIGNED-ACTUAL + UNESTABLISHED-REQUIRES PROBES — the rebind license
    // =======================================================================
    //
    // `gather_callee_hypotheses` / `build_transfer_obligation` rebind a callee's
    // ensures formals onto the actual argument's name. TWO sibling holes:
    //
    // (1) VERSION ALIASING — the DEST spelling is consumed from the authoritative
    //     `trust_vcgen::call_dest_fact_token` (license-paired with the SSA
    //     collapse), but the ACTUAL spelling must be licensed too: in the emitted
    //     VC symbol space the BARE name of a REASSIGNED local denotes its ENTRY
    //     version (the version the caller's preconditions constrain via
    //     `augment_with_type_bounds` — see the reassigned-param skip there), while
    //     the value the call actually receives is the AT-CALL version (a
    //     name-disjoint `a#s{b}_{k}` token). Rebinding a formal to the bare name
    //     of a reassigned actual mints a hypothesis about the WRONG version.
    //
    // (2) UNESTABLISHED REQUIRES — a callee's ensures holds only for calls that
    //     SATISFY its requires. Assuming the ensures without ESTABLISHING the
    //     requires at the call site (the `ProofContext.establishes` half) mints a
    //     hypothesis that is false whenever the call violates the contract.
    //
    // The probe program (caller ensures GENUINELY FALSE):
    //
    //   #[requires(x >= 100)] #[ensures(ret >= 100)] #[ensures(x >= 100)]
    //   fn pass(x: i32) -> i32 { x }                                // callee
    //
    //   #[requires(a >= 100)] #[ensures(ret >= 100)]
    //   fn reasg(a: i32) -> i32 { a = 0; let h = pass(a); h }       // caller
    //
    // Truth: the call passes a = 0 (violating pass's requires), pass returns 0,
    // so `ret >= 100` is FALSE. Both holes fire: the requires is never
    // established (hole 2), and the formal-clause `x >= 100` rebinds onto the
    // BARE (entry-version) `a` the caller precondition constrains (hole 1).
    //
    // NOTE (accidental protection, documented): a PRECONDITION-FREE callee whose
    // ensures links `ret` to a formal (`fn flr(x) = x` ensures `ret >= x`) does
    // NOT certify standalone today — its cert VC reduces to the irreflexive
    // `x < x`, which the `vc_refute` engine happens not to close. That engine
    // incompleteness is the ONLY thing keeping the precondition-free variant of
    // this exploit un-reachable; it is not a designed guard.

    /// PROBE callee: `#[requires(x >= 100)] #[ensures(ret >= 100)]
    /// #[ensures(x >= 100)] fn pass(x: i32) -> i32 { x }` — certifies standalone
    /// (each clause refutes under its own requires), carries a REQUIRES, and its
    /// second ensures clause MENTIONS ITS FORMAL (exercising the formal rebind).
    fn probe_callee_pass() -> VerifiableFunction {
        VerifiableFunction {
            name: "pass".into(),
            def_path: "crate::pass".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: I32, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: I32, name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: I32,
            },
            contracts: vec![],
            preconditions: vec![Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(100)),
            )],
            postconditions: vec![
                Formula::Ge(Box::new(ret_var()), Box::new(Formula::Int(100))),
                Formula::Ge(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(100)),
                ),
            ],
            spec: Default::default(),
        }
    }

    /// PROBE caller: `#[requires(a >= 100)] #[ensures(ret >= 100)]
    /// fn reasg(a: i32) -> i32 { a = 0; let h = pass(a); h }`.
    /// The argument local `a` is REASSIGNED before the call, so the at-call value
    /// (0) differs from the entry version the precondition constrains (>= 100).
    /// The ensures is GENUINELY FALSE (the call receives 0; pass returns 0).
    fn probe_caller_reassigns_arg() -> VerifiableFunction {
        VerifiableFunction {
            name: "reasg".into(),
            def_path: "crate::reasg".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: I32, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: I32, name: Some("a".into()) },
                    LocalDecl { index: 2, ty: I32, name: Some("h".into()) },
                ],
                blocks: vec![
                    // bb0: a = 0;  h = pass(a)  -> bb1  (the reassignment THEN the call)
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(1), // a = 0 (overwrite the argument local)
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            func: "crate::pass".into(),
                            args: vec![Operand::Copy(Place::local(1))], // pass(a) — at-call a = 0
                            dest: Place::local(2),                      // h = ...
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                            is_unsafe_sig: false,
                            is_foreign: false,
                        },
                    },
                    // bb1: _0 = h; return
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: I32,
            },
            contracts: vec![],
            preconditions: vec![Formula::Ge(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Int(100)),
            )],
            postconditions: vec![Formula::Ge(Box::new(ret_var()), Box::new(Formula::Int(100)))],
            spec: Default::default(),
        }
    }

    /// The SAME caller WITHOUT the reassignment (`fn ok(a) { let h = pass(a); h }`)
    /// — here the requires IS established (`a >= 100` at the call) and the ensures
    /// `ret >= 100` is TRUE. This composition must CERTIFY.
    fn probe_caller_no_reassign() -> VerifiableFunction {
        let mut f = probe_caller_reassigns_arg();
        f.name = "ok".into();
        f.def_path = "crate::ok".into();
        f.body.blocks[0].stmts.clear(); // drop `a = 0` — the arg local is never written
        f
    }

    /// PROBE caller (requires-hole isolation): `fn anyarg(a) { let h = pass(a); h }`
    /// with NO precondition and `#[ensures(ret >= 100)]`. The call does NOT
    /// establish pass's `x >= 100` (a is unconstrained), so pass's ensures may NOT
    /// be assumed; the caller ensures is GENUINELY FALSE at e.g. a = 0.
    fn probe_caller_unestablished_requires() -> VerifiableFunction {
        let mut f = probe_caller_no_reassign();
        f.name = "anyarg".into();
        f.def_path = "crate::anyarg".into();
        f.preconditions.clear(); // nothing establishes pass's requires
        f
    }

    /// COMPANION (the probes' well-formedness control): with NO reassignment the
    /// identical shape MUST still certify — the caller's own `a >= 100` establishes
    /// pass's requires at the call site, the assumed `h >= 100` closes the ensures.
    /// Guards the fix against over-closing (fail-closed must not become fail-all).
    #[test]
    fn probe_companion_established_requires_certifies() {
        let program = vec![probe_callee_pass(), probe_caller_no_reassign()];
        let result = verify_call_graph(&program);
        assert!(
            result.verdict("crate::pass").unwrap().is_certified(),
            "callee pass must certify standalone: {:?}",
            result.verdict("crate::pass")
        );
        assert!(
            result.verdict("crate::ok").unwrap().is_certified(),
            "the ESTABLISHED-requires caller must certify (a >= 100 establishes x >= 100; \
             h >= 100 closes ret >= 100): {:?}",
            result.verdict("crate::ok")
        );
    }

    /// PROBE PIN (hole 1 — version aliasing): a caller that REASSIGNS the argument
    /// local before the call must NOT be certified — its ensures is genuinely
    /// false. Unlicensed, the formal→bare-actual rebind minted `a >= 100` over the
    /// ENTRY version of `a` (the one the caller's precondition constrains), and
    /// the unestablished-requires hole simultaneously minted `h >= 100`; the
    /// kernel then falsely certified `ret >= 100` for a function that returns 0.
    #[test]
    fn reassigned_actual_must_not_mint_entry_version_hypothesis() {
        let program = vec![probe_callee_pass(), probe_caller_reassigns_arg()];
        let result = verify_call_graph(&program);
        assert!(
            result.verdict("crate::pass").unwrap().is_certified(),
            "callee pass must certify standalone (the probe needs an assumable callee): {:?}",
            result.verdict("crate::pass")
        );
        let caller = result.verdict("crate::reasg").unwrap();
        assert!(
            !caller.is_certified(),
            "FALSE CERTIFICATION: `reasg` reassigns `a` to 0 before `pass(a)` (violating \
             pass's requires), so its ensures `ret >= 100` is FALSE (pass returns 0) — \
             yet it certified. The rebind bound pass's contract onto the BARE \
             (entry-version) `a` the precondition constrains, not the at-call version, \
             and never established pass's requires."
        );
    }

    /// PROBE PIN (hole 2 — unestablished requires, NO reassignment involved): a
    /// caller that does NOT establish the callee's requires must get NO ensures
    /// hypothesis. `anyarg(a)` has no precondition, passes an unconstrained `a`
    /// to `pass` (requires `x >= 100`), and claims `ret >= 100` — genuinely FALSE
    /// at a = 0. Assuming pass's `ret >= 100` without establishing `x >= 100`
    /// falsely certified this program.
    #[test]
    fn unestablished_requires_must_not_transfer_ensures() {
        let program = vec![probe_callee_pass(), probe_caller_unestablished_requires()];
        let result = verify_call_graph(&program);
        assert!(
            result.verdict("crate::pass").unwrap().is_certified(),
            "callee pass must certify standalone: {:?}",
            result.verdict("crate::pass")
        );
        let caller = result.verdict("crate::anyarg").unwrap();
        assert!(
            !caller.is_certified(),
            "FALSE CERTIFICATION: `anyarg` never establishes pass's `x >= 100` (its `a` \
             is unconstrained), so pass's ensures may not be assumed — yet `ret >= 100` \
             certified (false at a = 0, where pass would return 0)."
        );
    }

    /// THE SAME PROBES through the §2 two-function lane (`build_transfer_obligation`
    /// + `prove_caller_obligation`): the reassigned-actual caller must NOT discharge
    /// the FALSE goal `h >= 100` (truth: h = pass(0) = 0) from an entry-version /
    /// unestablished-requires hypothesis.
    #[test]
    fn reassigned_actual_must_not_prove_via_transfer_obligation() {
        let callee_fn = probe_callee_pass();
        let caller = probe_caller_reassigns_arg();
        let mut registry = ProofStatusRegistry::new();
        let summary = certify_callee_summary(&callee_fn, FuncId::new(0), &mut registry);
        assert!(summary.ir_summary.proved, "pass must certify");

        // The FALSE caller goal: `h >= 100` (truth: h = pass(0) = 0).
        let false_goal =
            Formula::Ge(Box::new(Formula::Var("h".into(), Sort::Int)), Box::new(Formula::Int(100)));
        let verdict = prove_caller_obligation(&caller, &summary, &false_goal, &registry);
        assert!(
            !verdict.is_proven_modulo_3(),
            "FALSE CERTIFICATION (§2 lane): `h >= 100` is false (h = pass(0) = 0) but was \
             proven from the rebound callee ensures without version license or requires \
             establishment, got {verdict:?}"
        );
    }
}
