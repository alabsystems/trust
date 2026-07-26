// trust-certify: in-process Certified-tier bridge (de Bruijn criterion).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Turn a real solver UNSAT into a kernel-CHECKED [`trust_ir::ProofEvidence::CleanCic`].
//!
//! The north star: for a `Certified` obligation the SMT solver is **outside
//! the trusted base** — the clean CIC kernel re-checks the reconstructed proof
//! term (`TypeChecker::check_type`, `infer_only = false`); nothing trusts the
//! solver. This is the de Bruijn criterion.
//!
//! Pipeline ([`certify_vc`]):
//!
//! 1. Translate the VC's *violation* formula (which the router asserts and ay
//!    refutes) into a tight, supported fragment: a conjunction of linear
//!    integer order atoms over free `Int` variables, plus direct integer
//!    disequality contradictions that the kernel can close from `Eq`/`Not Eq`.
//! 2. Drive clean-auto's **in-process** ay backend on the same assertions and
//!    confirm `UNSAT`.
//! 3. For order-atom contradictions, reconstruct the native ay proof into a
//!    kernel proof term under a **zero-trust** budget (no `trustedAy` axiom) and
//!    confirm it is `fully_verified`; for direct disequality contradictions,
//!    build the kernel proof directly from `Eq`/`Not Eq`.
//! 4. **Re-check** the reconstructed term with the clean kernel
//!    (`check_type(_, False)`), then serialize term + reduced context and
//!    re-check the *serialized* payload after a round-trip.
//! 5. Emit `ProofEvidence::CleanCic { term, context, lineage, .. }`.
//!
//! The payload is locally kernel-rechecked, but it deliberately carries no
//! `kernel_recheck` publication sidecar.  The pinned TrustIR schema/dispatcher
//! does not have an obligation-bound route for these `NNVerify` Farkas proofs;
//! advertising its law-library module as if it rechecked the per-obligation
//! term would be false.  External Certified-tier publication therefore remains
//! fail-closed until that schema grows a matching dispatcher.
//!
//! Everything is **fail-closed**: any unsupported shape, solver non-`UNSAT`,
//! residual trust, or kernel rejection returns `None`, and the caller records
//! the obligation as `Trusted` (never a false `Certified`). A false `Certified`
//! is the worst possible bug in this crate.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};

use clean_auto::bridge::ay_contract::{
    AyLogic, AyProofBackend, AyProofResult, ReducedContext, ReducedLocalDecl, TrustBudget,
    VariableMapping, deserialize_context, deserialize_term, serialize_context, serialize_term,
};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, FVarId, Level, LocalContext, TypeChecker,
};
use sha2::{Digest, Sha256};
use trust_types::{Formula, Sort, VerificationCondition};

/// Canonical wire encoding used by every closed `CleanCic` lane in this crate.
/// Recheckers compare bytes, not merely the decoded value: a public lineage hash
/// is an integrity checksum and cannot authorize attacker-chosen encodings.
pub(crate) fn canonical_empty_context_bytes() -> Option<Vec<u8>> {
    serialize_context(&ReducedContext { decls: Vec::new() }).ok()
}

pub(crate) fn is_canonical_empty_context(context_bytes: &[u8]) -> bool {
    canonical_empty_context_bytes().as_deref() == Some(context_bytes)
}

/// Require the exact independently regenerated proof encoding.  This is the
/// authority gate for deterministic lanes whose ambient specification contains
/// polymorphic trust markers such as `sorry`.
pub(crate) fn is_canonical_term(term_bytes: &[u8], proof: &Expr) -> bool {
    serialize_term(proof).is_ok_and(|canonical| canonical.as_slice() == term_bytes)
}

/// Install a goal-specific admitted marker for adversarial recheck tests. It
/// models the authority defect of ambient `sorry`/`trusted*` declarations
/// without depending on clean-kernel's crate-private bootstrap helpers.
#[cfg(test)]
pub(crate) fn install_adversarial_trust_marker(env: &mut Environment, goal: &Expr) -> Option<Expr> {
    let name = Name::from_string("trustedAttackerMarker");
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: Vec::new(),
        type_: goal.clone(),
    })
    .ok()?;
    Some(Expr::const_(name, Vec::new()))
}

/// Finite forward-simulation re-check lane (M6 first slice) — a sibling to the
/// QF_LIA lane for the `∀ s b, tstep s b = spec s b` obligation shape.
pub mod finite_dfa;

/// Inductive functional-correctness re-check lane — certifies a correctness
/// property (`∀ n, Nat.add Nat.zero n = n`, the left identity of the kernel's
/// registered `Nat.add`) whose discharge is a genuine `Nat.rec` STRUCTURAL
/// INDUCTION, past the reach of the QF_LIA lane and the finite `casesOn` lane.
pub mod inductive_functional;

/// Checker-core functional-correctness re-check lane — certifies a de Bruijn
/// lemma of the TYPE-CHECKING CORE (`lift_instantiate_swap`: lifting commutes
/// with substitution — the lift/instantiate interchange), discharged by a
/// genuine `KExpr.rec` structural induction. Sources the `DerivedProved` proof
/// term from clean-verify's kernel-checked spec and re-checks it in the clean
/// kernel. Model-level (over the 7-ctor `KExpr` abstraction), the honest rung
/// above the arithmetic `inductive_functional` (`Nat.add`) lane.
pub mod checker_core;

/// Kernel re-check of a compiler-finalized body-bound `ensures` claim — the
/// lane that takes trust-wp's in-process adapter out of a
/// `BodyBoundNativeReplay` row's trusted base. Unlike [`certify_vc`], its input
/// is a POSITIVE postcondition envelope rather than a violation formula, so it
/// builds and discharges the goal directly instead of refuting its negation.
pub mod body_bound_ensures;

/// Trust: `clean { … }` parser-island checking (two-language design E10) —
/// parse the island text with the real Clean parser, elaborate + register
/// each declaration (registration IS the kernel gate), and report failures
/// with island-relative byte offsets for source-accurate Rust diagnostics.
pub mod clean_island;

/// Trust: the kernel half of the zero-authority frontend firewall. The only
/// route by which material from an untrusted frontend (TrustJS/TrustPy/
/// TrustZig) may reach the kernel — as a goal to be discharged, never as a
/// hypothesis, an axiom, or a defining equation.
pub mod frontend_admission;

/// Checker-core lemma lanes spanning model-side infer/check coherence, subject
/// reduction, context-free and `CandModel`-conditional dependent WHNF
/// termination, reflected five-constructor `KernelInferAccepts` inversion, the
/// six-shape bootstrap `KernelInfers` soundness relation, modeled def-eq/WHNF
/// acceptance properties, substitution congruence, and model-specific
/// parallel-star confluence at Clean's concrete `faithful_red_env`. Same
/// authority-closed, canonical-proof CleanCic re-check pipeline as
/// [`checker_core`], each with a negative control; model-level over the 7-ctor
/// `KExpr` abstraction and its explicitly admitted foundational judgment base.
/// Relation-specific subsets omit `let_` where their pinned definitions say so
/// and do not ground the literal Rust decision procedures or deployed reduction
/// environment.
pub mod checker_core_lemma;

pub mod checker_core_infer_sort;
/// Checker-core STRUCTURAL-POSTCONDITION discharge lane (the DISCHARGE half of
/// Gap-A): kernel-discharges the checker-core postcondition `is_whnf(_0)` for a
/// concrete WHNF-returning result by LINKing the return slot to its concrete
/// `KExpr` (fail-closed on non-WHNF heads) and DISCHARGING with the matching
/// `is_whnf.sort/lam/pi` ctor term the clean kernel accepts. Load-bearing
/// negative control: a stuck-`app` result fails closed at LINK. Model-level over
/// the 7-ctor `KExpr` abstraction.
pub mod checker_core_is_whnf;

/// FUNCTION-level grounding of the real Rust `clean_kernel::infer_type` (sort
/// arm): calls the real `TypeChecker::infer_type(Sort l)` and observes its
/// genuine output equals `Sort (l+1)`. Per-input function grounding (evidence,
/// not a for-all proof); retires no fidelity axiom. See the module docs.
pub mod checker_core_infer_type_fn;
pub mod checker_core_is_def_eq_fn;
pub mod checker_core_whnf_fn;

/// Datatype (dis)equality no-confusion reconstruction lane (Brick 3 · Lever A ·
/// STEP 4): reconstructs a FALSE datatype equality between distinct constructors
/// (`Level.succ l = Level.zero`) — refuted by ay's native datatypes theory —
/// into a clean-kernel-CHECKED `∀ l, Eq Level (succ l) zero → False` no-confusion
/// proof (`Eq.rec` + `Level.casesOn` diagonal). STEP-4 INFRASTRUCTURE over a
/// HAND-CONSTRUCTED datatype (World B); grounds nothing / drains no axiom (census
/// stays 16). Load-bearing negative control: a TRUE reflexive equality is
/// rejected on three counts (ay `sat`, no honest proof, kernel `True`≠`False`).
pub mod datatype_no_confusion;

/// Non-recursive datatype functional-equation reconstruction lane. It consumes
/// the exact positive sort-arm equation emitted by
/// `trust_vcgen::datatype_functional` through a dedicated typed entry point;
/// generic violation-formula dispatch must not ingest this positive claim.
pub mod datatype_functional;

/// WALL C — RECURSIVE datatype-function INDUCTION discharge lane: consumes the
/// induction VC bundle trust-vcgen's `recursive_datatype_functional` lane emits
/// for a SELF-recursive extracted datatype function (per-constructor cases with
/// the recursive call replaced by an IH variable + the tagged conclusion) and
/// GENERATES the corresponding `DT.rec` CIC induction term — datatype
/// reconstruction, `.rec`-fold model definition, per-case minor premises
/// (`Eq.refl` base / `congrArg` step consuming the IH) — kernel-checked
/// (Certified tier). The `level_recursive_functional` proof shape, machine-built
/// from the VCs. Grounds nothing in clean-verify / drains no axiom. Load-bearing
/// negative controls: a FALSE postcondition's generated proof is KERNEL-rejected
/// (mint fails closed), and the refl-only pseudo-proof of the true goal is
/// rejected (the IH is load-bearing).
pub mod recursive_datatype_functional;

/// WALL C scaled to MUTUAL SCCs — the mutual-cluster induction discharge lane:
/// consumes the fuel-indexed mutual bundle trust-vcgen's
/// `mutual_recursive_datatype_functional` lane emits for a call-graph SCC of
/// size N > 1 (per-member base/step case VCs whose cluster calls became
/// `[calls=..]`-tagged IH atoms + the joint `[mutual-induction:..]`-tagged
/// conclusion) and GENERATES the joint discharge: ONE `Fuel.rec` induction with
/// a PRODUCT motive (the per-member statements conjoined — the Aristotle-proved
/// MutualCluster.lean `cluster_agrees_assembled` shape), the models encoded as
/// a single fold over a models record so member i's step body reaches member
/// j's previous-fuel approximation, call minors PROJECTING the callee's
/// component out of the product IH (`And.left`/`And.right` chains) into
/// `congrArg` — kernel-checked (Certified tier). Grounds nothing in
/// clean-verify / drains no axiom. Load-bearing negative controls: a FALSE
/// postcondition on ANY ONE member kernel-rejects the WHOLE joint proof
/// (mutual induction is all-or-nothing), the refl-only pseudo-proof is
/// rejected, and projecting the WRONG (caller-self) IH component is rejected —
/// the mutual edges are real.
pub mod mutual_recursive_datatype_functional;

/// SN-vs-fuel RESOLUTION item 1 — the STATE-THREADED numeric-budget discharge
/// lane: consumes trust-vcgen's `threaded_budget_functional` bundle (per-entry
/// decrement, remainder passed to every later callee, model-vs-reference
/// postconditions, remainder-threading IH atoms) and machine-builds the joint
/// kernel discharge via the MAJORANT fold: the models record's fields become
/// fuel-taking functions, ONE `Fuel.rec` on the structural majorant with the
/// product motive quantified over ALL threaded fuels ("the IH applies at any
/// smaller fuel" — instantiated at the dynamic remainders), goal = the
/// motive's diagonal. NO `Acc`. Kernel-checked (Certified tier); refl-only
/// pseudo-proof rejected; a disagreeing reference arm is kernel-rejected.
pub mod threaded_budget_functional;

/// SN-vs-fuel RESOLUTION items 2+3 — fail-closed EXHAUSTION arms with
/// Done-conditional postconditions (`model fuel x = Done r -> P(r)`), the
/// machine-built FUEL-MONOTONICITY lane lemma (Done at f -> same Done at every
/// f' >= f, via a recursively-defined `<=` and iterated succ-monotonicity —
/// no inversion, no `Acc`), and the loop -> fuel-model per-iteration
/// SIMULATION discharge (each loop-path equation is definitional for the SAME
/// rebuilt model that carries the induction bundle — the honest handoff).
/// Kernel-checked; the Exhausted-only postcondition is kernel-rejected
/// unconditionally (the named negative control).
pub mod fuel_outcome_functional;

/// The whnf L+M+F composition coherence check: one fail-closed run over the
/// MIR witnesses, step-fidelity gates, and kernel-attested model theorems.
/// NON-AUTHORITATIVE validation artifact — it emits a coherence report, never
/// `ProofEvidence`, and does not establish the literal-Rust reducer universal
/// (quarantined; see the 2026-07-16 checker-core closure design note).
pub mod reducer_universal_composition;

/// Phase-3 link-3 "auto-sourcing": source a 2D finite-DFA refinement obligation
/// from a real trust-ir program, then feed it to the kernel-checked finite-sim
/// re-check lane (`finite_dfa`).
pub mod finite_dfa_from_ir;

/// First Light engine entry: a real kernel-checked `CleanCic` verdict that the
/// aterm VT parser next-state table refines its reference. The worked example
/// for the finite-simulation lane; see `finite_dfa_from_ir` for why it is
/// public without an in-tree caller.
pub use finite_dfa_from_ir::{
    author_table_step_module, certify_aterm_parser_next_state, extract_2d_matrix,
    recheck_aterm_parser_next_state, recheck_ir_table_refines_spec, verify_ir_table_refines_spec,
};

/// FVarId base for hypothesis free variables. Matches the modest range used by
/// clean-auto's reconstruction fixtures (30–51); kept well clear of the kernel
/// term's internal sentinel allocation.
const HYP_FVAR_BASE: u64 = 100;

/// Lineage domain tag for the `CleanCic` digest. `v3` binds the canonical full
/// serialized VC, including contract metadata, rather than a selected debug
/// projection of its fields.
const LINEAGE_DOMAIN: &str = "trust-certify.cleancic.v3";

/// Stable identity of the obligation a `CleanCic` certificate is evidence for.
/// Folded into the lineage digest so the certificate is bound to *this*
/// obligation and cannot be swapped onto another. Built once from the
/// [`VerificationCondition`] at the public entry point; the formula-only path
/// uses a distinct tag plus the canonical serialized formula.
struct ObligationIdentity {
    encoded: Vec<u8>,
}

impl ObligationIdentity {
    /// Identity for a full obligation: binds every serialized field.
    fn from_vc(vc: &VerificationCondition) -> Option<Self> {
        let mut encoded = b"vc:\0".to_vec();
        encoded.extend_from_slice(&bincode::serialize(vc).ok()?);
        Some(Self { encoded })
    }

    /// Identity for the formula-only path: only the violation formula is known,
    /// so only it is bound (the other fields are empty). Still distinguishes
    /// obligations whose violation formulas differ.
    fn from_violation(violation: &Formula) -> Option<Self> {
        let mut encoded = b"formula:\0".to_vec();
        encoded.extend_from_slice(&bincode::serialize(violation).ok()?);
        Some(Self { encoded })
    }
}

/// A single contradictory hypothesis: one asserted formula of the violation.
#[derive(Clone)]
struct Hyp {
    /// SMT-LIB2 rendering asserted to the in-process solver.
    smt: String,
    /// Kernel proposition (the `Prop` this hypothesis inhabits).
    prop: Expr,
    /// Fresh-variable id this hypothesis is bound to in the proof term.
    fvar: FVarId,
    /// Stable hypothesis name (for the local context / variable map).
    name: String,
}

/// Attempt to mint a kernel-CHECKED `CleanCic` certificate for `vc`.
///
/// Returns `Some(ProofEvidence::CleanCic { .. })` only when the obligation's
/// violation is a supported linear-integer contradiction that ay refutes and
/// the clean kernel re-checks with **zero** residual trust. Returns `None`
/// (→ caller records `Trusted`) for every unsupported, unproved, trust-bearing,
/// or kernel-rejected case. Never produces a false `Certified`.
#[must_use]
pub fn certify_vc(vc: &VerificationCondition) -> Option<trust_ir::ProofEvidence> {
    // Bind every field of the canonical serialized obligation, including
    // contract metadata, so the certificate cannot be swapped onto a different
    // obligation whose proof-driving formula happens to be identical.
    certify_with_identity(&vc.formula, &ObligationIdentity::from_vc(vc)?)
}

// Native-bundle construction runs before the ordinary per-function
// certification budget exists. Keep its one planning-time certificate query
// structurally bounded: a general call to `certify_vc` here can enter expensive
// normalization/solver families on arbitrary compiler VCs.
const NATIVE_PLANNING_MAX_FORMULA_NODES: usize = 96;
const NATIVE_PLANNING_MAX_FORMULA_DEPTH: usize = 16;
const NATIVE_PLANNING_MAX_CONJUNCTS: usize = 24;
const NATIVE_PLANNING_MAX_NODE_FANOUT: usize = 24;
const NATIVE_PLANNING_MAX_STRING_BYTES: usize = 4 * 1024;
const NATIVE_PLANNING_MAX_IDENTITY_BYTES: u64 = 2 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativePlanningPreflightFailure {
    UnsupportedVcKind,
    ContractMetadata,
    UnsupportedFormulaNode,
    FormulaNodes,
    FormulaDepth,
    Conjuncts,
    NodeFanout,
    StringBytes,
    IdentityBytes,
}

/// Preflight the exact, small unsigned-BV guarded-index family admitted during
/// native bundle planning.
///
/// This walk is iterative, so an attacker-controlled deeply nested formula is
/// declined without recursively visiting it. The structural whitelist also
/// rules out every arithmetic, conversion, signed-order, quantified, array,
/// floating-point, datatype, and uninterpreted node before normalization or a
/// solver is invoked. Node, depth, flattened-conjunct, fanout, aggregate-string,
/// and final serialized-identity caps bound all remaining work and allocation.
fn preflight_unsigned_bv_order_vc_for_native_planning(
    vc: &VerificationCondition,
) -> Result<(), NativePlanningPreflightFailure> {
    // This planning exception exists only for the compiler's guarded-index
    // bounds-check lane. Keeping the kind exact also prevents an arbitrary
    // string/vector-bearing VcKind payload from reaching identity serialization.
    if !matches!(vc.kind, trust_types::VcKind::IndexOutOfBounds) {
        return Err(NativePlanningPreflightFailure::UnsupportedVcKind);
    }
    // This compiler-synthesized bounds-check family has no contract metadata.
    // Reject even today's fixed-size metadata representation so future schema
    // growth cannot silently put an unbounded carrier in this planning path.
    if vc.contract_metadata.is_some() {
        return Err(NativePlanningPreflightFailure::ContractMetadata);
    }

    let mut string_bytes = vc
        .function
        .as_str()
        .len()
        .checked_add(vc.location.file.len())
        .ok_or(NativePlanningPreflightFailure::StringBytes)?;
    if string_bytes > NATIVE_PLANNING_MAX_STRING_BYTES {
        return Err(NativePlanningPreflightFailure::StringBytes);
    }

    let mut nodes = 0usize;
    let mut conjuncts = 0usize;
    let mut stack = vec![(&vc.formula, 1usize, true)];
    while let Some((formula, depth, is_conjunct_root)) = stack.pop() {
        nodes = nodes.checked_add(1).ok_or(NativePlanningPreflightFailure::FormulaNodes)?;
        if nodes > NATIVE_PLANNING_MAX_FORMULA_NODES {
            return Err(NativePlanningPreflightFailure::FormulaNodes);
        }
        if depth > NATIVE_PLANNING_MAX_FORMULA_DEPTH {
            return Err(NativePlanningPreflightFailure::FormulaDepth);
        }

        let mut charge_name = |name: &str| {
            string_bytes = string_bytes
                .checked_add(name.len())
                .ok_or(NativePlanningPreflightFailure::StringBytes)?;
            if string_bytes > NATIVE_PLANNING_MAX_STRING_BYTES {
                return Err(NativePlanningPreflightFailure::StringBytes);
            }
            Ok(())
        };
        match formula {
            Formula::Bool(true) | Formula::BitVec { width: 1..=126, .. } => {}
            Formula::Var(name, Sort::Bool) => charge_name(name)?,
            Formula::Var(name, Sort::BitVec(1..=126)) => charge_name(name)?,
            Formula::SymVar(name, Sort::Bool) => charge_name(name.as_str())?,
            Formula::SymVar(name, Sort::BitVec(1..=126)) => {
                charge_name(name.as_str())?;
            }
            Formula::And(children) => {
                if children.len() > NATIVE_PLANNING_MAX_NODE_FANOUT {
                    return Err(NativePlanningPreflightFailure::NodeFanout);
                }
                for child in children.iter().rev() {
                    stack.push((child, depth + 1, is_conjunct_root));
                }
                continue;
            }
            Formula::Eq(left, right) => {
                stack.push((right, depth + 1, false));
                stack.push((left, depth + 1, false));
            }
            Formula::BvULt(left, right, 1..=126) | Formula::BvULe(left, right, 1..=126) => {
                stack.push((right, depth + 1, false));
                stack.push((left, depth + 1, false));
            }
            _ => return Err(NativePlanningPreflightFailure::UnsupportedFormulaNode),
        }

        // `collect_conjuncts` treats every non-And subtree as one conjunct. Its
        // cost, and the cardinality seen by each normalization pass, are bounded
        // independently from the total AST-node budget.
        if is_conjunct_root {
            conjuncts =
                conjuncts.checked_add(1).ok_or(NativePlanningPreflightFailure::Conjuncts)?;
            if conjuncts > NATIVE_PLANNING_MAX_CONJUNCTS {
                return Err(NativePlanningPreflightFailure::Conjuncts);
            }
        }
    }

    // Formula recursion and all variable-sized identity fields are now bounded,
    // so `serialized_size` itself is cheap and non-recursive beyond the shallow
    // cap. Check it before `ObligationIdentity::from_vc` allocates the bytes.
    let encoded_size =
        bincode::serialized_size(vc).map_err(|_| NativePlanningPreflightFailure::IdentityBytes)?;
    if encoded_size > NATIVE_PLANNING_MAX_IDENTITY_BYTES {
        return Err(NativePlanningPreflightFailure::IdentityBytes);
    }
    Ok(())
}

/// Return whether `vc` fits the bounded syntax and work budget of
/// [`certify_vc_for_native_planning`].
///
/// This predicate is a resource/shape gate only. It is **not proof evidence**,
/// does not establish that the violation is unsatisfiable, and must never grant
/// a verdict or transport authority. The certificate API deliberately reruns
/// the same fused preflight before normalization to keep its own safety
/// independent of callers and of any intervening VC mutation.
#[must_use]
pub fn vc_fits_native_planning_certification_budget(vc: &VerificationCondition) -> bool {
    preflight_unsigned_bv_order_vc_for_native_planning(vc).is_ok()
}

/// Attempt the one kernel-certificate family that is safe to query while a
/// native verifier bundle is being planned.
///
/// This is deliberately **not** a bounded wrapper around [`certify_vc`]. It
/// first enforces the small guarded-index preflight above, then normalizes the
/// violation and invokes only the pure unsigned-BV order-contradiction
/// recognizer. That recognizer's only general-certifier re-entry is its fixed
/// four-atom linear-Int synthesis; no part of the caller's arbitrary formula is
/// sent through the broad family dispatcher. Every other VC declines with
/// `None` before a solver is entered. A successful result is still full,
/// obligation-lineage-bound `CleanCic` evidence rechecked by the clean kernel.
#[must_use]
pub fn certify_vc_for_native_planning(
    vc: &VerificationCondition,
) -> Option<trust_ir::ProofEvidence> {
    preflight_unsigned_bv_order_vc_for_native_planning(vc).ok()?;
    let identity = ObligationIdentity::from_vc(vc)?;
    let normalized = normalize_violation(&vc.formula)?;
    let conjuncts = normalized.view();
    match certify_unsigned_bv_order_contradiction(&conjuncts, &identity)? {
        evidence @ trust_ir::ProofEvidence::CleanCic { .. } => Some(evidence),
        _ => None,
    }
}

/// Core of [`certify_vc`], operating directly on the violation formula.
///
/// Binds only the violation formula into the lineage digest (the function,
/// kind, and location are unknown on this path). Prefer [`certify_vc`] when a
/// full [`VerificationCondition`] is available.
#[must_use]
pub fn certify_violation(violation: &Formula) -> Option<trust_ir::ProofEvidence> {
    certify_with_identity(violation, &ObligationIdentity::from_violation(violation)?)
}

// ── Trust (perf): certificate memoization ──────────────────────────────────
//
// `certify_with_identity` is the confirmed clean-kernel hot path — its
// `term`/`context` come from kernel proof reconstruction + `check_type`
// re-check, the dominant cost of Trust verification. The SAME violation formula
// is certified repeatedly per compile: (a) the promote/`certify_all` double-run
// certifies one obligation twice, (b) R1 attribution re-certifies overlapping
// strengthened/caller formulas, and (c) structurally-identical functions repeat
// identical formula shapes. The proof payload is a pure function of the
// *formula*, so cache it keyed on the formula and recompute only the cheap
// per-obligation lineage.
//
// SOUNDNESS: `term`/`context`/`kernel_recheck` never read `identity` (verified:
// across every branch, `identity` flows only into `lineage_digest`). A hit is
// therefore BYTE-IDENTICAL to a fresh `certify_with_identity_uncached` — the
// producer itself IS the in-process soundness gate (it kernel-`check_type`s the
// reconstructed term before returning), so a memo hit inherits that guarantee
// exactly; the memo cannot make the producer accept anything it would otherwise
// reject. (The `recheck_cleancic` consumer re-derives + re-checks independently,
// but only on the cross-boundary proof-BUNDLE import path, not on this in-process
// disposition.) The cache key is the formula's full canonical bincode bytes;
// the hash map compares the whole byte vector, so a hash collision cannot
// alias distinct formulas. This key is intentionally separate from
// `ObligationIdentity::encoded`, whose full-VC form also binds source and
// contract metadata for lineage isolation.

/// Identity-independent payload of a `ProofEvidence::CleanCic`: everything the
/// producer derives from the violation formula alone. The stored `evidence`'s
/// `lineage` is stale by construction and always recomputed on use.
#[derive(Clone)]
struct CachedCleanCic {
    evidence: trust_ir::ProofEvidence,
}

#[allow(clippy::type_complexity)]
fn certify_memo()
-> &'static std::sync::Mutex<std::collections::HashMap<Vec<u8>, Option<CachedCleanCic>>> {
    static MEMO: std::sync::OnceLock<
        std::sync::Mutex<std::collections::HashMap<Vec<u8>, Option<CachedCleanCic>>>,
    > = std::sync::OnceLock::new();
    MEMO.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()))
}

/// Memoization is ON by default; `TRUST_CERTIFY_MEMO=0` disables it (for A/B
/// measurement of the win on the same binary).
fn certify_memo_enabled() -> bool {
    !std::env::var("TRUST_CERTIFY_MEMO").is_ok_and(|value| value == "0")
}

/// Look up the identity-independent payload for a formula key. Outer `None` =
/// key absent (miss); `Some(inner)` = key present (hit), where `inner` is `None`
/// when this formula is not certifiable (independent of identity).
fn certify_memo_lookup(key: &[u8]) -> Option<Option<CachedCleanCic>> {
    certify_memo().lock().ok().and_then(|memo| memo.get(key).cloned())
}

/// Recompute the per-obligation lineage over a cached identity-independent
/// payload — byte-identical to what `finish_certificate` emits fresh.
fn restamp_cleancic(
    parts: &CachedCleanCic,
    identity: &ObligationIdentity,
) -> trust_ir::ProofEvidence {
    match &parts.evidence {
        trust_ir::ProofEvidence::CleanCic { term, context, kernel_recheck, .. } => {
            let lineage = lineage_digest(term, context, identity);
            trust_ir::ProofEvidence::CleanCic {
                term: term.clone(),
                context: context.clone(),
                lineage,
                kernel_recheck: kernel_recheck.clone(),
            }
        }
        // Only `CleanCic` evidence is ever cached (see `certify_memo_store`); any
        // other variant returns as-is rather than fabricate a lineage.
        other => other.clone(),
    }
}

/// Record the identity-independent payload (or `None` = uncertifiable) for a
/// formula key, without holding the lock across the (already-completed) proof.
fn certify_memo_store(key: Vec<u8>, result: &Option<trust_ir::ProofEvidence>) {
    let entry: Option<CachedCleanCic> = match result {
        None => None,
        Some(evidence @ trust_ir::ProofEvidence::CleanCic { .. }) => {
            Some(CachedCleanCic { evidence: evidence.clone() })
        }
        // `Some ⇒ CleanCic` is this crate's documented invariant; if it ever
        // breaks, skip caching rather than poison the key with a wrong `None`.
        Some(_) => return,
    };
    if let Ok(mut memo) = certify_memo().lock() {
        // Bound peak memory: the memo holds full reconstructed proof terms, so an
        // unbounded map on a huge crate (many distinct obligation formulas) is an RSS
        // vector. Past the cap, keep serving existing entries but stop growing — new
        // formulas simply recompute (correctness unaffected; only the hit-rate tail
        // is capped). Override with TRUST_CERTIFY_MEMO_CAP.
        if memo.len() < certify_memo_cap() || memo.contains_key(&key) {
            memo.entry(key).or_insert(entry);
        }
    }
}

/// Clear the certificate memo. Used by the compiler's `TRUST_VERIFY_EQUIV_CHECK`
/// between its serial and parallel harvest runs so the parallel run actually
/// re-executes the concurrent clean-kernel certification (rather than replaying the
/// serial run's memo entries as all-hits). Not for production paths.
pub fn reset_certify_memo() {
    if let Ok(mut memo) = certify_memo().lock() {
        memo.clear();
    }
}

/// Max number of distinct-formula entries retained by the certificate memo.
/// Default 200_000; override with `TRUST_CERTIFY_MEMO_CAP=<n>`.
fn certify_memo_cap() -> usize {
    std::env::var("TRUST_CERTIFY_MEMO_CAP")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(200_000)
}

/// Shared body of [`certify_vc`] / [`certify_violation`]: the violation formula
/// drives the proof, while `identity` is folded into the lineage digest.
///
/// Trust (perf): memoized by the violation formula — see the memoization block
/// above. The cache key is the formula's canonical serialization, not the
/// lineage identity: a full-VC identity deliberately contains fields that do
/// not affect the proof payload.
fn certify_with_identity(
    violation: &Formula,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    if !certify_memo_enabled() {
        return certify_with_identity_uncached(violation, identity);
    }
    let Ok(cache_key) = bincode::serialize(violation) else {
        // Serialization failure must cost only the optimization, never proof
        // availability. The uncached producer still binds `identity` exactly.
        return certify_with_identity_uncached(violation, identity);
    };
    if let Some(cached) = certify_memo_lookup(&cache_key) {
        // HIT: reuse the identity-independent payload, recompute this
        // obligation's lineage. `None` = formula proven un-certifiable.
        return cached.map(|parts| restamp_cleancic(&parts, identity));
    }
    // MISS: run the full producer (no lock held), then record the result.
    let result = certify_with_identity_uncached(violation, identity);
    certify_memo_store(cache_key, &result);
    result
}

/// The uncached certificate producer. See [`certify_with_identity`] for the
/// memoization wrapper and its soundness argument.
fn certify_with_identity_uncached(
    violation: &Formula,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    // Opt-in violation dump (AY_CERT_DUMP=1) for fast certify-shape discovery; the
    // env gate means zero output in normal verification.
    if std::env::var("AY_CERT_DUMP").is_ok_and(|v| v == "1") {
        eprintln!("[CERTDUMP] {violation:?}");
    }
    // 1. Normalize the violation into the supported conjunct pool (recursive-And
    //    split, vacuous-`Bool(true)` drop, entailed-atom derivation, spent-
    //    reification drop) — single-sourced with `recheck_cleancic` via
    //    [`normalize_violation`], so the producer and the consumer certify /
    //    re-check against the IDENTICAL hypothesis environment.
    let normalized = normalize_violation(violation)?;
    let conjuncts = normalized.view();

    if let Some(evidence) = certify_direct_disequality_contradiction(&conjuncts, identity) {
        return Some(evidence);
    }

    // Closed-constant arithmetic contradiction. A range check over compile-time
    // constants — a shift-amount check `Or([2 < 0, 2 >= 32])` or a cast-range
    // check `Or([2 < 0, 2 > u32::MAX])` — has its contradiction inside a
    // DISJUNCTION (or a lone atom) of variable-free order atoms that ALL
    // evaluate to false. The Farkas/order-atom fragment below cannot reach a
    // disjunction, and ay's Farkas reconstruction needs a free variable, so the
    // obligation would otherwise fall through uncertified. Build a genuine
    // kernel refutation directly (`Or.rec` + `Int.lt_of_lt_of_le` +
    // `Int.lt_irrefl` over the `Int.NonNeg.mk` witness of the true reverse
    // inequality), re-checked by the clean kernel — same zero-trust criterion.
    if let Some(evidence) = certify_closed_constant_contradiction(&conjuncts, identity) {
        return Some(evidence);
    }

    // Signed wide-BV add/sub no-overflow (`i128`/widened): the BV overflow check
    // `BvAdd(x,y,w)` / `BvSub(x,y,w)` is bounded by signed-BV guards (`BvSLt`/
    // `BvSLe`) or by 64→128 sign-extensions, and the carry-bit overflow disjunction
    // asserts the signed result is outside `[i_w_min, i_w_max]`. Translate the BV
    // shape into an equivalent linear-Int violation (bounds + `Or([x±y<min,
    // x±y>max])`) and hand it to the existing disjunctive/additive-lift refutation.
    // Tried BEFORE the generic disjunctive path: its `Or` operands are BV, not Int.
    if let Some(evidence) = certify_signed_bv_overflow_safe(&conjuncts, identity) {
        return Some(evidence);
    }

    // Unsigned wide-BV add of bounded division results (the canonical
    // `(a / 2) + (b / 2)` midpoint): derive each quotient's unsigned upper
    // bound, require their sum to fit, and close the resulting linear-Int
    // contradiction through the kernel-checked certificate pipeline.
    if let Some(evidence) = certify_unsigned_bv_div_sum_no_overflow(&conjuncts, identity) {
        return Some(evidence);
    }

    // Pure unsigned-BV ORDER contradiction (the guarded-index in-bounds
    // re-assert `if idx < K { a[idx] }`): the whole pool is unsigned order atoms
    // over one index — range facts `0 ≤u idx ≤u uMAX`, the dominating path guard
    // `idx <u K`, and the violation `K ≤u idx` (plus view-dropped reified
    // copies). Lift the raw-variable reads to Int over a fresh carrier and reuse
    // the Int interval pipeline (`K ≤ c < K ⊢ K < K`, `Int.lt_irrefl`).
    // Fail-closed WHITELIST: any BV arithmetic/extract/concat/signed/conversion
    // operator anywhere in the pool declines — a derived operand could wrap, so
    // only raw reads justify the unsigned-value lift.
    if let Some(evidence) = certify_unsigned_bv_order_contradiction(&conjuncts, identity) {
        return Some(evidence);
    }

    // Branch-merged `Ite`-valued index (`merged_local_index`): the violation is a
    // SwitchInt-join `Or([branch, …])` whose every branch shares an in-bounds
    // contradiction over an index `idx = Ite(c, a, b)` with closed-literal branch
    // values `a, b` (`step = if c {1} else {2}`, then OOB `step ≥ s.len()` under
    // `s.len() > 2`). Reduce to the existing disjunctive refutation by emitting the
    // entailed `Or([idx ≤ a, idx ≤ b])` against the shared branch context. The
    // reduced conjunct list is owned by `reduced`; `reduced_refs` borrows it.
    if let Some(reduced) = ite_index_disjunction_reduction(&conjuncts) {
        let reduced_refs: Vec<&Formula> = reduced.iter().collect();
        if let Some(evidence) = certify_disjunctive_contradiction(&reduced_refs, identity) {
            return Some(evidence);
        }
    }

    // Loop-accumulation no-overflow (`t += addend`): the per-add overflow
    // obligation is `Or([Lt(Add(a,b),0), Gt(Add(a,b),MAX)])` with a DIRECTLY-
    // present tight bound `Le(Add(a,b),bound)` (bound ≤ MAX) and the summand
    // non-negativities `Le(0,a)`, `Le(0,b)`. This EXACT shape closes via the
    // generic disjunctive path for a small obligation (`u64_acc`), but a real
    // shift/nested-loop reduction drags in MANY surrounding conjuncts (BV-shift /
    // discriminant atoms, with duplicates) whose augmented edge set blows the
    // `refute_via_chain_edges` 48-edge cap before the closing chain is found.
    // Discharge it DIRECTLY off the three present facts (two edges, no augmented
    // edge set), so the cap never triggers. Tried before the generic path so it
    // short-circuits the cap-prone DFS for this shape; the wide-`UInt` MAX
    // threshold (`u128::MAX`, which the `ChainAtom` literal renderer rejects) is
    // handled here too. Fail-closed: only the exact shape with all three present
    // facts fires, and finish_certificate's ay UNSAT + kernel re-check are the
    // backstops.
    if let Some(evidence) = certify_accumulator_no_overflow(&conjuncts, identity) {
        return Some(evidence);
    }

    // Two-variable-sum no-overflow whose sum bound is DERIVABLE from per-summand
    // bounds (`a≤A ∧ b≤B ⟹ a+b ≤ A+B`) rather than directly present — the
    // hardened panic-boundary `mir_assert::Overflow(Add)` restatement of the
    // `(a/c)+(b/c)` midpoint (division-range emits `a/c ≤ ⌊U/c⌋` on each summand,
    // never on the sum). After the direct-bound accumulator path; discharges off
    // the four present bound facts so the cap-prone augmented-edge DFS never runs.
    if let Some(evidence) = certify_summand_bounded_accumulator_no_overflow(&conjuncts, identity) {
        return Some(evidence);
    }

    // Same summand-bound-derived no-overflow discharge for the De Morgan DUAL
    // violation shape `Not(And([Le(0,a+b), Le(a+b,MAX)]))` that the HARDENED
    // panic-boundary lane emits (vs the `Or([a+b<0, a+b>MAX])` form above).
    if let Some(evidence) = certify_summand_bounded_not_in_range_no_overflow(&conjuncts, identity) {
        return Some(evidence);
    }

    // Signed two-sided loop-accumulation no-overflow (`s += x as i32` over signed
    // narrow elements): the per-add obligation is `Or([Lt(a+b,MIN), Gt(a+b,MAX)])`
    // with the loop-invariant window `Ge(a+b,lo)`, `Le(a+b,hi)` present as conjuncts
    // (`MIN ≤ lo`, `hi ≤ MAX`). Each disjunct is refuted against a present sum bound.
    // After the unsigned path, so the `Lt(a+b,0)` (nonneg-lift) shape is handled there.
    if let Some(evidence) = certify_bounded_sum_no_overflow(&conjuncts, identity) {
        return Some(evidence);
    }

    // Negated-return postcondition branch (`if x < 0 { -x }` under `ensures
    // result ≥ 0`): the branch VC carries the return relation `_0 = -x`, the
    // dominating guard `x < 0`, the type bounds on `x`, and the violated
    // ensures `¬(_0 ≥ 0)`. The `Neg` relation is outside the linear-atom
    // fragment (`term_to_kernel` has no `Neg` arm), so the generic path below
    // fails closed on it; substitute the relation away (`_0 = -x ∧ _0 < 0 ⟹
    // 0 < x`) and refute the entailed `x < 0 ∧ 0 < x` through the Int interval
    // pipeline. Fail-closed on any non-linear / float / bitvector leakage.
    if let Some(evidence) = certify_negated_return_via_neg_bound(&conjuncts, identity) {
        return Some(evidence);
    }

    // Guarded-arithmetic disjunctive contradiction: `context ∧ Or([d1, …, dn])`
    // where joining each disjunct with the context is a transitive-chain
    // contradiction (e.g. `if x>10 {x-10}` → `x>10 ∧ x≤max ∧ Or([x-10<0,
    // x-10>max])`). Refute by `Or.rec` case-split, each branch closing
    // `context ∧ di` after shifting `x±c` bounds back onto `x`.
    if let Some(evidence) = certify_disjunctive_contradiction(&conjuncts, identity) {
        return Some(evidence);
    }

    // General `a ≠ b` via order totality: a supported integer disequality
    // entails `a < b ∨ b < a` (ℤ trichotomy), so replace the `≠` with exactly
    // that disjunction and let the `Or.rec` engine close each branch against
    // the remaining context (`a ≤ b ∧ b ≤ a ∧ a ≠ b` and friends — equality
    // forced by bounds, with no literal `Eq` for the direct-disequality pair).
    if let Some(evidence) = certify_split_disequality_contradiction(&conjuncts, identity) {
        return Some(evidence);
    }

    // Keep only the conjuncts that lie in the supported linear-Int fragment; the
    // contradiction a real bounds/guard VC carries lives in this subset, wrapped
    // in reified `Bool = (x < y)` conjuncts we soundly drop.
    let (atoms, var_names) = collect_supported_atoms(&conjuncts);
    if atoms.is_empty() {
        return None;
    }

    // 2. Translate each atom into (SMT assertion, kernel prop), binding a fresh
    //    hypothesis fvar. Shared with `recheck_cleancic` so the producer and the
    //    consumer build the IDENTICAL hypothesis context to check the term against.
    let hyps: Vec<Hyp> = supported_hyps_from_atoms(&atoms)?;

    // 2a. Single-variable interval contradiction (e.g. `x ≤ 2 ∧ 4 ≤ x` from a
    //     constant index `arr[2]` or any `x = c ∧ x ≥ bound`). ay's zero-trust
    //     Farkas reconstruction handles bounds that meet at a point (`x<0 ∧ 0<x`)
    //     but NOT a constant GAP (`4 ≤ x ≤ 2`): it cannot synthesize the numeric
    //     `4 ≤ 2` contradiction. Compose the bounds with `Int.le_trans` (etc.)
    //     into the closed false `L ≤ U` / `L < U` and refute it directly — a
    //     genuine kernel proof, re-checked under the same zero-trust criterion.
    if let Some(term) = single_var_interval_refutation(&atoms, &hyps)
        .or_else(|| transitive_chain_refutation(&atoms, &hyps))
        .or_else(|| multi_var_farkas_refutation(&atoms, &hyps))
    {
        if let Some(evidence) = finish_certificate(&hyps, &term, &var_names, identity) {
            return Some(evidence);
        }
    }

    // 3. Build the kernel environment: Int arithmetic + ordering lemmas, plus an
    //    axiom per free variable. (init_int_ord_lemmas transitively provides
    //    False/Not/Eq/Int/LT.lt, mirroring clean-auto's QF_LIA fixture.)
    let env = build_env(&var_names)?;

    // 4. Drive the in-process ay solver on exactly these assertions.
    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
    for name in &var_names {
        backend.add_raw_declaration(&format!("(declare-fun {} () Int)", encoded_var_name(name)));
    }
    for hyp in &hyps {
        backend.assert_formula(&hyp.smt);
    }

    // VariableMapping: each SMT variable → its kernel const; each hypothesis →
    // its fvar + prop. The SMT name == kernel const name == trust var name.
    let int_ty = int_ty();
    let mut map = VariableMapping::new();
    for name in &var_names {
        let encoded = encoded_var_name(name);
        map.register_var(
            &encoded,
            Expr::const_(Name::from_string(&encoded), vec![]),
            int_ty.clone(),
        );
    }
    for hyp in &hyps {
        map.register_hypothesis(&hyp.name, hyp.fvar, Expr::fvar(hyp.fvar), hyp.prop.clone());
    }

    // Trust (parallel verify): serialize ONLY the raw ay solve on the shared
    // `trust_types::ay_exec_lock()` (ay's direct path is non-reentrant). The lock
    // drops at the end of this block — BEFORE the clean-kernel reconstruction /
    // re-check below, which is thread-safe by construction and must stay unlocked
    // so it parallelizes across verification threads.
    match {
        let _ay_guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());
        backend.check_sat()
    } {
        Ok(AyProofResult::Unsat { .. }) => {}
        _ => return None, // SAT / Unknown / solver error → cannot certify
    }

    // 5. Reconstruct under a ZERO-TRUST budget: returns None if any trustedAy
    //    axiom is needed. Belt-and-suspenders: also require fully_verified.
    let candidate = backend.attempt_kernel_reconstruction_with_budget(
        &map,
        &neg_false(),
        TrustBudget::ZeroTrust,
    )?;
    if !candidate.quality().is_fully_verified() {
        return None;
    }

    // 6. The local context the refutation lives in: one decl per hypothesis.
    let ctx = build_ctx(&hyps);

    // Gate (e): full kernel re-check that the reconstructed term : False.
    if !kernel_checks_false(&env, ctx.clone(), candidate.refutation(), &var_names) {
        return None;
    }

    // 7. Serialize term + reduced context (canonical CleanCic payload form).
    let term_bytes = serialize_term(candidate.refutation()).ok()?;
    let reduced = reduced_context(&ctx);
    let context_bytes = serialize_context(&reduced).ok()?;

    // Defense in depth: the *serialized* payload must independently re-check
    // after a full round-trip (this is what an external consumer would do).
    if !payload_roundtrip_rechecks(&var_names, &term_bytes, &context_bytes) {
        return None;
    }

    // 8. Bind term+context+obligation-identity with a lineage digest and emit.
    let lineage = lineage_digest(&term_bytes, &context_bytes, identity);
    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// The conjunct-normalization pipeline shared by the certificate PRODUCER
/// ([`certify_with_identity`]) and the consumer-side re-check
/// ([`recheck_cleancic`]). Every step derives atoms ENTAILED by the obligation's
/// own conjuncts (never by certificate bytes), so a consumer that builds its
/// hypothesis context from this pool preserves the context-substitution-forgery
/// criterion while accepting every certificate the producer can mint. Each step
/// sees the base conjuncts plus everything derived by earlier steps — the same
/// accumulation order the producer historically used inline. Per-step soundness:
/// each emits only logical consequences of its input conjuncts. The table ends
/// with a bounded (exactly-one) SECOND pass of the two Euclidean range
/// emitters, so divisor/dividend bounds that arrive via the equality-class
/// propagation still yield their range facts; the late passes are
/// new-atoms-only ([`retain_new_atoms`]), so they never add duplicate atoms.
///
/// CERTIFICATE-BYTE CANDOR (2026-07-22 widening): pools whose div/mod bounds
/// are spelled in the newly-recognized forms — mirrored orientation
/// (`Le(0, a)`, vcgen's canonical unsigned lower bound), strict spellings,
/// `UInt` literals, `SymVar` leaves — and pools whose bounds arrive only via
/// equality-class propagation now gain range atoms they previously lacked,
/// so THEIR certificate bytes change across this producer version. That is
/// the inherent cost of genuine coverage growth (the new atoms are real,
/// entailed facts; producer and consumer regenerate in lockstep), accepted
/// exactly as for any recognizer addition. Contrast the
/// [`refute_via_var_cycle`] Var-Var restriction, which declined byte drift
/// that bought NO coverage; [`retain_new_atoms`] serves the same purpose
/// here, preventing the no-new-coverage churn of a bare second pass.
const NORMALIZATION_STEPS: [fn(&[&Formula]) -> Vec<Formula>; 14] = [
    // Trust #540: unfold asserted Bool reifications (`_b ⟺ inner; assert(_b)`)
    // into their entailed inner atoms, so a discharge whose contradiction hides
    // behind an asserted Bool (div-by-zero `assert(divisor != 0)` etc.) becomes
    // refutable.
    unfold_asserted_bool_reifications,
    // Propagate constant equalities so a transitive `_4 == 0 ∧ _4 == divisor`
    // yields `divisor == 0`, meeting the disequality refutation directly.
    propagate_constant_equalities,
    // Tighten strict integer bounds (`Lt(y,3) → Le(y,2)`) so the non-strict
    // multiplicative / additive lifts can discharge loop-counter overflows.
    tighten_strict_int_bounds,
    // Membership-disjunction interval bounds: `Or([Eq(v,c0), …, Eq(v,cn)])`
    // entails `min(cᵢ) ≤ v ≤ max(cᵢ)` — every disjunct lies in the interval.
    membership_interval_bounds,
    // Modus ponens on entailed implications: `(ante → cons) ∧ ante ⊢ cons`,
    // emitted only when `ante` is a genuine consequence of present bounds.
    discharge_entailed_implications,
    // Constant-fold closed arithmetic (`Mul(4096,64) → 262144`).
    fold_constant_arith_conjuncts,
    // Euclidean remainder range: `k = a % b` with a positive literal divisor
    // entails `k ≤ b-1` (and `k ≥ 0` for a non-negative dividend) — theorems of
    // Euclidean division for `b > 0`.
    modulo_range_bounds,
    // Euclidean division range: `q = a / c` with a positive literal divisor `c`
    // and a NON-NEGATIVE dividend (`a ≥ 0`) entails `q ≥ ⌊L/c⌋ ≥ 0` and, with a
    // present `a ≤ U`, `q ≤ ⌊U/c⌋` — division is monotone on non-negatives. Lets
    // the additive no-overflow refutation close `(a/c)+(b/c) ≤ 2·⌊U/c⌋ < U` (e.g.
    // the `(a/2)+(b/2)` usize midpoint whose sum can never overflow).
    division_range_bounds,
    // Surface conjuncts COMMON to every disjunct of an `Or` (Or-elimination).
    extract_disjunction_common_conjuncts,
    // Propagate the TIGHTEST integer bound across each var=var equality class.
    propagate_equality_class_bounds,
    // Complete a transitive var=var disequality with the entailed direct one.
    complete_class_disequalities,
    // Bridge masked-low-bits / left-shift BV equalities into linear-Int
    // equalities, GATED on a no-wrap / mask-identity side condition proved by a
    // present bound; fail-closed (nothing emitted) when it is not provable.
    bv_mask_shift_rewrites,
    // SECOND pass of the Euclidean range emitters (new-atoms-only): divisor
    // positivity / dividend bounds established by the equality-class
    // propagation above are invisible to the first pass at table position 7-8.
    modulo_range_bounds_late,
    division_range_bounds_late,
];

/// Owned result of [`normalize_violation`]: `base` borrows the violation's own
/// conjuncts, `pool` owns every derived (entailed) atom.
struct NormalizedConjuncts<'a> {
    base: Vec<&'a Formula>,
    pool: Vec<Formula>,
}

impl NormalizedConjuncts<'_> {
    /// The full normalized conjunct view: base + derived atoms, minus the spent
    /// Bool-reification conjuncts (their content was extracted by the unfold).
    /// Dropping conjuncts is sound for a refutation — it can only weaken the
    /// system, so a SAT obligation stays SAT and fails closed.
    fn view(&self) -> Vec<&Formula> {
        self.base
            .iter()
            .copied()
            .chain(self.pool.iter())
            .filter(|c| !is_bool_reification_conjunct(c))
            .collect()
    }
}

/// Split the violation into conjuncts (recursive And), drop vacuous
/// `Bool(true)` tautologies (they contribute nothing to a refutation but poison
/// the fail-closed special-case paths), then run [`NORMALIZATION_STEPS`].
/// Returns `None` when no conjuncts survive — an empty system is vacuously SAT,
/// so nothing may be certified or re-checked against it.
fn normalize_violation(violation: &Formula) -> Option<NormalizedConjuncts<'_>> {
    let mut base = Vec::new();
    collect_conjuncts(violation, &mut base);
    base.retain(|c| !matches!(c, Formula::Bool(true)));
    if base.is_empty() {
        return None;
    }
    let mut pool: Vec<Formula> = Vec::new();
    for step in NORMALIZATION_STEPS {
        let view: Vec<&Formula> = base.iter().copied().chain(pool.iter()).collect();
        pool.extend(step(&view));
    }
    Some(NormalizedConjuncts { base, pool })
}

/// Consumer-side re-check of a `CleanCic` certificate (the soundness gate for
/// importing a CHC-discharged obligation). It independently regenerates the
/// canonical evidence from this obligation, rerunning the applicable solver
/// gate and clean-CIC kernel check, then requires exact term, context, and
/// lineage equality. Presented `context_bytes` are never treated as authority.
/// This pairs every producer family, including closed-constant, disjunctive,
/// accumulator, bounded-sum, signed-BV/ITE, generic Farkas, and direct
/// disequality lanes. Returns `true` only when canonical regeneration matches,
/// so:
///  * a tampered/forged term fails the kernel check;
///  * a term that genuinely refutes a *different* contradiction over the same
///    variable names (a context-substitution forgery) fails the kernel check
///    because the obligation's own hypotheses cannot type it as `: False`;
///  * a certificate minted for a different obligation fails the lineage binding.
#[must_use]
pub fn recheck_cleancic(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
    obligation_violation: &Formula,
) -> bool {
    let Some(identity) = ObligationIdentity::from_violation(obligation_violation) else {
        return false;
    };
    recheck_cleancic_with_identity(
        term_bytes,
        context_bytes,
        lineage,
        obligation_violation,
        &identity,
    )
}

/// Consumer-side recheck paired with [`certify_vc`].  Unlike the legacy
/// formula-only [`recheck_cleancic`] entry point, this binds and verifies the
/// complete canonical serialized obligation identity, including function, VC
/// kind, source location, violation formula, and contract metadata.
#[must_use]
pub fn recheck_vc_cleancic(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
    vc: &VerificationCondition,
) -> bool {
    let Some(identity) = ObligationIdentity::from_vc(vc) else {
        return false;
    };
    recheck_cleancic_with_identity(term_bytes, context_bytes, lineage, &vc.formula, &identity)
}

/// Replay a certificate against the full obligation identity of `vc` (function,
/// kind, location, violation formula, and contract metadata). This is the
/// consumer counterpart of [`certify_vc`].
#[must_use]
pub fn recheck_vc(
    vc: &VerificationCondition,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    recheck_vc_cleancic(term_bytes, context_bytes, lineage, vc)
}

/// Replay `evidence` against the complete identity of `vc`. Non-kernel evidence
/// is deliberately not authoritative for this lane.
#[must_use]
pub fn replay_vc_evidence(vc: &VerificationCondition, evidence: &trust_ir::ProofEvidence) -> bool {
    match evidence {
        trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } => {
            recheck_vc(vc, term, context, lineage)
        }
        _ => false,
    }
}

fn recheck_cleancic_with_identity(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
    obligation_violation: &Formula,
    identity: &ObligationIdentity,
) -> bool {
    // Regenerate the lane's canonical evidence from the obligation itself. This
    // covers every producer family (generic Farkas, direct disequality,
    // closed-constant, disjunctive, signed-BV/ITE reductions, accumulator and
    // bounded-sum) without trusting the presented context or guessing which
    // producer emitted it. Each producer reruns its solver gate and full clean
    // kernel check before returning these independently regenerated bytes.
    let Some(trust_ir::ProofEvidence::CleanCic {
        term: canonical_term,
        context: canonical_context,
        lineage: canonical_lineage,
        ..
    }) = certify_with_identity(obligation_violation, identity)
    else {
        return false;
    };
    canonical_term.as_slice() == term_bytes
        && canonical_context.as_slice() == context_bytes
        && &canonical_lineage == lineage
}

fn collect_conjuncts<'a>(formula: &'a Formula, out: &mut Vec<&'a Formula>) {
    match formula {
        Formula::And(children) => {
            for child in children {
                collect_conjuncts(child, out);
            }
        }
        // Double-negation elimination: `Not(Not(x)) ≡ x`. R1's caller-discharge VC is
        // `Not(P[σ])` and `P` itself is a `Not(Eq(..))` disequality (`divisor != 0`), so a
        // discharged call site arrives as `Not(Not(Eq(5,0)))` — the inner `Eq(5,0)` is the
        // closed-constant contradiction the checks below already handle. Sound: equivalence.
        Formula::Not(inner) if matches!(inner.as_ref(), Formula::Not(_)) => {
            if let Formula::Not(x) = inner.as_ref() {
                collect_conjuncts(x, out);
            }
        }
        single => out.push(single),
    }
}

/// Trust #540 (R1 discharge certification): unfold ASSERTED Bool reifications into their
/// inner atoms. A MIR safety check lowers to `_b = (inner); assert(_b)`, appearing as the
/// conjuncts `Eq(Var(_b,Bool), inner)` (the definition) and `Var(_b,Bool)` (asserted
/// true) — both OUTSIDE the linear-Int fragment, so `collect_supported_atoms` drops them
/// and the contradiction carried by `inner` (e.g. `_4 == 0` for a div-by-zero discharge)
/// is lost. From `_b` asserted true and `_b ⟺ inner`, `inner` holds; for `Not(_b)`,
/// `¬inner` holds — each a SOUND modus-ponens consequence of the original conjuncts.
///
/// SOUNDNESS: every emitted atom is ENTAILED by the original formula, so the augmented
/// conjunct set is equisatisfiable to it. A satisfiable obligation therefore stays
/// satisfiable (the refutation path's ay-solve still returns SAT and fails closed — see
/// `fails_closed_on_satisfiable_div_by_zero_without_precondition`); only a genuinely
/// UNSAT obligation gains the missing atom needed to expose its contradiction.
fn unfold_asserted_bool_reifications(conjuncts: &[&Formula]) -> Vec<Formula> {
    // Bool definitions `name ⟺ inner` from `Eq(Var(name,Bool), inner)` (either operand).
    let mut defs: Vec<(&str, &Formula)> = Vec::new();
    for &c in conjuncts {
        if let Formula::Eq(a, b) = c {
            if let Formula::Var(name, Sort::Bool) = a.as_ref() {
                defs.push((name.as_str(), b.as_ref()));
            } else if let Formula::Var(name, Sort::Bool) = b.as_ref() {
                defs.push((name.as_str(), a.as_ref()));
            }
        }
    }
    let mut out = Vec::new();
    for &c in conjuncts {
        match c {
            // `_b` asserted true ⇒ its definition body holds.
            Formula::Var(name, Sort::Bool) => {
                if let Some((_, inner)) = defs.iter().find(|(n, _)| *n == name.as_str()) {
                    out.push((*inner).clone());
                }
            }
            // `Not(_b)` asserted ⇒ the negation of its definition body holds.
            Formula::Not(boxed) => {
                if let Formula::Var(name, Sort::Bool) = boxed.as_ref() {
                    if let Some((_, inner)) = defs.iter().find(|(n, _)| *n == name.as_str()) {
                        out.push(Formula::Not(Box::new((*inner).clone())));
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// Trust #540: constant-equality propagation. From Int equalities `a == b` (var/var) and
/// `a == k` (var/const) — e.g. the unfolded `_4 == 0` together with `_4 == divisor` — emit
/// `v == k` for EVERY variable `v` transitively equal to a constant `k`. This lets a
/// disequality `divisor != 0` meet its refutation `divisor == 0` directly (the existing
/// `certify_direct_disequality_contradiction` matches symmetric equalities, not transitive
/// chains). SOUND: each emitted `v == k` is entailed by the equalities (a satisfiable
/// system stays satisfiable), so it only ever exposes a real contradiction.
/// A conjunct that mentions a `Bool`-sorted variable at top level (an asserted reified
/// flag `Var(_b,Bool)`, its negation, or a definition `Eq(Var(_b,Bool), inner)`). These
/// are outside the linear-Int fragment; once [`unfold_asserted_bool_reifications`] has
/// extracted their entailed content they are redundant and safely dropped.
fn is_bool_reification_conjunct(c: &Formula) -> bool {
    match c {
        Formula::Var(_, Sort::Bool) => true,
        Formula::Not(inner) => matches!(inner.as_ref(), Formula::Var(_, Sort::Bool)),
        Formula::Eq(a, b) => {
            matches!(a.as_ref(), Formula::Var(_, Sort::Bool))
                || matches!(b.as_ref(), Formula::Var(_, Sort::Bool))
        }
        _ => false,
    }
}

fn propagate_constant_equalities(conjuncts: &[&Formula]) -> Vec<Formula> {
    use std::collections::BTreeMap;
    // Union-find over Int variable names.
    let mut parent: BTreeMap<String, String> = BTreeMap::new();
    fn find(parent: &mut BTreeMap<String, String>, x: &str) -> String {
        match parent.get(x).cloned() {
            None => x.to_string(),
            Some(p) if p == x => p,
            Some(p) => {
                let root = find(parent, &p);
                parent.insert(x.to_string(), root.clone());
                root
            }
        }
    }
    let mut vars: std::collections::BTreeSet<String> = Default::default();
    // Pass 1: union variable/variable equalities.
    for &c in conjuncts {
        if let Formula::Eq(a, b) = c
            && let (Formula::Var(x, Sort::Int), Formula::Var(y, Sort::Int)) =
                (a.as_ref(), b.as_ref())
        {
            vars.insert(x.clone());
            vars.insert(y.clone());
            parent.entry(x.clone()).or_insert_with(|| x.clone());
            parent.entry(y.clone()).or_insert_with(|| y.clone());
            let (rx, ry) = (find(&mut parent, x), find(&mut parent, y));
            if rx != ry {
                parent.insert(rx, ry);
            }
        }
    }
    // Pass 2: bind a constant to each class root (after all unions are settled).
    let mut class_const: BTreeMap<String, i128> = BTreeMap::new();
    for &c in conjuncts {
        if let Formula::Eq(a, b) = c {
            let (var, lit) = match (a.as_ref(), b.as_ref()) {
                (Formula::Var(x, Sort::Int), Formula::Int(n)) => (x, *n),
                (Formula::Int(n), Formula::Var(x, Sort::Int)) => (x, *n),
                _ => continue,
            };
            vars.insert(var.clone());
            let r = find(&mut parent, var);
            class_const.insert(r, lit);
        }
    }
    // Pass 3: emit `v == k` for every var whose class carries a constant.
    let mut out = Vec::new();
    for v in &vars {
        let r = find(&mut parent, v);
        if let Some(&k) = class_const.get(&r) {
            out.push(Formula::Eq(
                Box::new(Formula::Var(v.clone(), Sort::Int)),
                Box::new(Formula::Int(k)),
            ));
        }
    }
    out
}

/// Propagate the TIGHTEST literal bound across each var=var equality class. Given
/// `_2 = s_len ∧ s_len ≤ isize::MAX ∧ _2 ≤ usize::MAX`, emit `_2 ≤ isize::MAX` (the
/// class-minimum upper bound) for every class member, so the additive lift uses the
/// tight bound and a slice-length sum no-overflow (`_2 + _3 ≤ 2·isize::MAX <
/// usize::MAX`) discharges. SOUND: every emitted bound is entailed — a class member
/// equals its root, so the root's bound holds of the member.
fn propagate_equality_class_bounds(conjuncts: &[&Formula]) -> Vec<Formula> {
    use std::collections::BTreeMap;
    let mut parent: BTreeMap<String, String> = BTreeMap::new();
    fn find(parent: &mut BTreeMap<String, String>, x: &str) -> String {
        match parent.get(x).cloned() {
            None => x.to_string(),
            Some(p) if p == x => p,
            Some(p) => {
                let root = find(parent, &p);
                parent.insert(x.to_string(), root.clone());
                root
            }
        }
    }
    // Union var=var equalities.
    for &c in conjuncts {
        if let Formula::Eq(a, b) = c
            && let (Formula::Var(x, Sort::Int), Formula::Var(y, Sort::Int)) =
                (a.as_ref(), b.as_ref())
        {
            parent.entry(x.clone()).or_insert_with(|| x.clone());
            parent.entry(y.clone()).or_insert_with(|| y.clone());
            let (rx, ry) = (find(&mut parent, x), find(&mut parent, y));
            if rx != ry {
                parent.insert(rx, ry);
            }
        }
    }
    if parent.is_empty() {
        return Vec::new();
    }
    // Collect `(var, literal, is_upper)` bound facts (both operand orders).
    let mut facts: Vec<(String, i128, bool)> = Vec::new();
    for &c in conjuncts {
        match c {
            Formula::Le(a, b) => match (a.as_ref(), b.as_ref()) {
                (Formula::Var(v, Sort::Int), Formula::Int(n)) => facts.push((v.clone(), *n, true)),
                (Formula::Int(n), Formula::Var(v, Sort::Int)) => facts.push((v.clone(), *n, false)),
                _ => {}
            },
            Formula::Ge(a, b) => match (a.as_ref(), b.as_ref()) {
                (Formula::Var(v, Sort::Int), Formula::Int(n)) => facts.push((v.clone(), *n, false)),
                (Formula::Int(n), Formula::Var(v, Sort::Int)) => facts.push((v.clone(), *n, true)),
                _ => {}
            },
            _ => {}
        }
    }
    // Tightest per class root: min upper, max lower.
    let mut upper: BTreeMap<String, i128> = BTreeMap::new();
    let mut lower: BTreeMap<String, i128> = BTreeMap::new();
    for (v, n, is_upper) in &facts {
        if !parent.contains_key(v) {
            continue;
        }
        let r = find(&mut parent, v);
        if *is_upper {
            let e = upper.entry(r).or_insert(*n);
            if *n < *e {
                *e = *n;
            }
        } else {
            let e = lower.entry(r).or_insert(*n);
            if *n > *e {
                *e = *n;
            }
        }
    }
    // Emit the class-tightest bound for every member.
    let members: Vec<String> = parent.keys().cloned().collect();
    let mut out = Vec::new();
    for m in &members {
        let r = find(&mut parent, m);
        if let Some(&u) = upper.get(&r) {
            out.push(Formula::Le(
                Box::new(Formula::Var(m.clone(), Sort::Int)),
                Box::new(Formula::Int(u)),
            ));
        }
        if let Some(&l) = lower.get(&r) {
            out.push(Formula::Le(
                Box::new(Formula::Int(l)),
                Box::new(Formula::Var(m.clone(), Sort::Int)),
            ));
        }
    }
    out
}

/// Extract interval bounds from membership disjunctions. A conjunct
/// `Or([Eq(v,c0), …, Eq(v,cn)])` whose every disjunct equates the SAME Int var `v`
/// to an Int literal entails `min(cᵢ) ≤ v ≤ max(cᵢ)`. Emit `Ge(v,min)` and
/// `Le(v,max)`. Used by enum-discriminant / cast obligations where the variant set
/// `{0,1,2}` bounds the cast result. Sound: every disjunct satisfies the interval,
/// so their disjunction does.
/// Whether a present literal bound proves `name ≥ k` — either orientation,
/// strict or non-strict: `Ge(name, c)` / `Le(c, name)` with `c ≥ k`, or
/// `Gt(name, c)` / `Lt(c, name)` with `c ≥ k-1` (over Int, `c < v ⟺ v ≥ c+1`).
/// `name` matches `Var` or `SymVar` Int leaves (one namespace, exactly as
/// [`int_var_name`] reads them); literals may be `Int` or `UInt`. Callers pass
/// `k ∈ {0, 1}`, so `k - 1` cannot underflow.
fn int_var_lower_bound_at_least(conjuncts: &[&Formula], name: &str, k: i128) -> bool {
    let is_var = |f: &Formula| {
        matches!(f, Formula::Var(n, Sort::Int) if n == name)
            || matches!(f, Formula::SymVar(s, Sort::Int) if s.as_str() == name)
    };
    conjuncts.iter().any(|&c| match c {
        Formula::Ge(a, b) if is_var(a) => int_literal_value(b).is_some_and(|l| l >= k),
        Formula::Le(a, b) if is_var(b) => int_literal_value(a).is_some_and(|l| l >= k),
        Formula::Gt(a, b) if is_var(a) => int_literal_value(b).is_some_and(|l| l >= k - 1),
        Formula::Lt(a, b) if is_var(b) => int_literal_value(a).is_some_and(|l| l >= k - 1),
        _ => false,
    })
}

/// Euclidean remainder range facts (Phase 4). For each conjunct `k = a % b`
/// (`Formula::Rem`, either orientation, `Var` or `SymVar` result leaf) with a
/// positive literal divisor `b`, emit `Le(k, b-1)` — UNCONDITIONALLY sound for
/// Rust's `%` since `|a % b| < |b|` for `b > 0` — and, when a present bound
/// proves the dividend non-negative (either orientation, strict or
/// non-strict — [`int_var_lower_bound_at_least`]), `Ge(k, 0)`. Lets the
/// single-var interval refutation close a dead modulo-guarded
/// `unreachable!()` (`k = n % 4` ⊢ `k ≤ 3`, contradicting the trap's `k ≥ 4`).
fn modulo_range_bounds(conjuncts: &[&Formula]) -> Vec<Formula> {
    let nonneg = |name: &str| int_var_lower_bound_at_least(conjuncts, name, 0);
    // A variable divisor is known STRICTLY positive from a present `d ≥ 1` /
    // `1 ≤ d` (non-strict) or `d > 0` / `0 < d` (strict) fact, either
    // orientation (e.g. `n = num_partitions.max(1)` carries `n ≥ 1`).
    let positive = |name: &str| int_var_lower_bound_at_least(conjuncts, name, 1);
    let mut out = Vec::new();
    for c in conjuncts {
        let Formula::Eq(a, b) = c else { continue };
        let (k_leaf, dividend, divisor) = match (a.as_ref(), b.as_ref()) {
            (leaf, Formula::Rem(d, m)) if int_var_name(leaf).is_some() => (leaf, d, m),
            (Formula::Rem(d, m), leaf) if int_var_name(leaf).is_some() => (leaf, d, m),
            _ => continue,
        };
        let kv = || Box::new(k_leaf.clone());
        match divisor.as_ref() {
            // Literal positive divisor `b`: `k ≤ b-1` UNCONDITIONALLY (|a%b| < |b|).
            Formula::Int(n) if *n > 0 => {
                out.push(Formula::Le(kv(), Box::new(Formula::Int(*n - 1))));
            }
            Formula::UInt(n) if *n > 0 && *n <= i128::MAX as u128 => {
                out.push(Formula::Le(kv(), Box::new(Formula::Int(*n as i128 - 1))));
            }
            // VARIABLE divisor `n` known strictly positive: `k < n` UNCONDITIONALLY
            // (`a % n < n` for every sign of `a` when `n > 0`). Lets a downstream
            // `k < n ≤ N` chain refute a `k > N` cast/index overflow — e.g.
            // `(h % num_partitions.max(1)) as u32` with `n ≤ u32::MAX`. The
            // literal arms above run FIRST, so only a `Var`/`SymVar` divisor
            // reaches this guard.
            leaf if int_var_name(leaf).is_some_and(|n| positive(&n)) => {
                out.push(Formula::Lt(kv(), Box::new(leaf.clone())));
            }
            _ => continue,
        }
        // Non-negative dividend ⇒ k ≥ 0 (Rust `%` keeps the sign of the dividend).
        if let Some(a_name) = int_var_name(dividend.as_ref())
            && nonneg(&a_name)
        {
            out.push(Formula::Ge(kv(), Box::new(Formula::Int(0))));
        }
    }
    out
}

/// Euclidean division range facts (Phase 4 sibling of [`modulo_range_bounds`]).
/// For each conjunct `q = a / c` (`Formula::Div`, either orientation) with a
/// positive literal divisor `c` and a dividend PROVABLY non-negative from the
/// present conjuncts (a `Ge(a, L≥0)` or `Le(L≥0, a)` fact — e.g. the usize
/// type-range `a ≥ 0`), emit the division-monotone bounds:
///
/// * `q ≥ ⌊L/c⌋` from the non-negative lower bound `a ≥ L` (in particular
///   `q ≥ 0`), and
/// * `q ≤ ⌊U/c⌋` when an upper bound `a ≤ U` (`U ≥ 0`) is present.
///
/// SOUNDNESS: each is a THEOREM of Rust integer division `/` on a NON-NEGATIVE
/// dividend with a positive divisor — there `a / c = ⌊a/c⌋` (truncation equals
/// floor) and floor division is monotone, so `L ≤ a ≤ U ⊢ ⌊L/c⌋ ≤ a/c ≤ ⌊U/c⌋`.
/// The non-negativity guard is REQUIRED: Rust `/` truncates toward zero, which
/// is not monotone across sign, so nothing is emitted for a dividend not known
/// `≥ 0`. Like every normalization step, this emits only entailed atoms, so it
/// can never turn a satisfiable obligation UNSAT — a genuinely-overflowing sum
/// carries no such division conjunct (or no non-negative-bounded dividend) and
/// stays unrefuted (fail-closed). Lets the additive-lift / bounded-sum
/// refutation discharge `(a/c)+(b/c) ≤ 2·⌊U/c⌋ < U`.
///
/// VARIABLE-DIVISOR arm: for `q = a / d` with `d` PROVABLY `≥ 1`
/// ([`int_var_lower_bound_at_least`], either orientation, strict or
/// non-strict) and the same non-negative-dividend guard, emit `q ≥ 0` (trunc
/// division of a non-negative by a positive is non-negative) and — with a
/// present `a ≤ U`, `U ≥ 0` — `q ≤ U`, because `d ≥ 1 ⊢ a/d ≤ a ≤ U` on a
/// non-negative `a`. The bound is `U`, not `⌊U/d⌋`: `d` is symbolic (no
/// literal floor exists), the emitted atom must stay in the var-vs-literal
/// fragment the interval/additive consumers read, and `U` is TIGHT
/// (`d = 1, a = U` realizes `q = U`). Result leaves are `Var` or `SymVar`.
fn division_range_bounds(conjuncts: &[&Formula]) -> Vec<Formula> {
    let var_is = |f: &Formula, name: &str| {
        matches!(f, Formula::Var(n, Sort::Int) if n == name)
            || matches!(f, Formula::SymVar(s, Sort::Int) if s.as_str() == name)
    };
    let int_lit = |f: &Formula| -> Option<i128> {
        match f {
            Formula::Int(v) => Some(*v),
            Formula::UInt(v) if *v <= i128::MAX as u128 => Some(*v as i128),
            _ => None,
        }
    };
    // The tightest present literal upper bound on `name` (`name ≤ U`, either
    // `Le(name, U)` or `Ge(U, name)`).
    let upper = |name: &str| -> Option<i128> {
        conjuncts
            .iter()
            .filter_map(|c| match c {
                Formula::Le(l, r) if var_is(l, name) => int_lit(r),
                Formula::Ge(l, r) if var_is(r, name) => int_lit(l),
                _ => None,
            })
            .min()
    };
    // The tightest present literal lower bound on `name` (`name ≥ L`, either
    // `Ge(name, L)` or `Le(L, name)`).
    let lower = |name: &str| -> Option<i128> {
        conjuncts
            .iter()
            .filter_map(|c| match c {
                Formula::Ge(l, r) if var_is(l, name) => int_lit(r),
                Formula::Le(l, r) if var_is(r, name) => int_lit(l),
                _ => None,
            })
            .max()
    };
    let mut out = Vec::new();
    for c in conjuncts {
        let Formula::Eq(a, b) = c else { continue };
        let (q_leaf, dividend, divisor) = match (a.as_ref(), b.as_ref()) {
            (leaf, Formula::Div(d, m)) if int_var_name(leaf).is_some() => (leaf, d, m),
            (Formula::Div(d, m), leaf) if int_var_name(leaf).is_some() => (leaf, d, m),
            _ => continue,
        };
        // The dividend must be an Int variable so its bounds can be consulted.
        let Some(a_name) = int_var_name(dividend.as_ref()) else { continue };
        // REQUIRE a provably non-negative dividend (`a ≥ L ≥ 0`); otherwise the
        // truncation-vs-floor mismatch breaks monotonicity and nothing is sound.
        let Some(l) = lower(&a_name).filter(|l| *l >= 0) else { continue };
        let qv = || Box::new(q_leaf.clone());
        if let Some(cval) = int_lit(divisor).filter(|c| *c > 0) {
            // Positive literal divisor: division-monotone floor bounds.
            // q ≥ ⌊L/c⌋ (≥ 0). div_euclid == floor for the non-negative L, c > 0.
            out.push(Formula::Ge(qv(), Box::new(Formula::Int(l.div_euclid(cval)))));
            // q ≤ ⌊U/c⌋ when a present upper bound `a ≤ U` (U ≥ 0) exists.
            if let Some(u) = upper(&a_name).filter(|u| *u >= 0) {
                out.push(Formula::Le(qv(), Box::new(Formula::Int(u.div_euclid(cval)))));
            }
        } else if let Some(d_name) = int_var_name(divisor.as_ref())
            && int_var_lower_bound_at_least(conjuncts, &d_name, 1)
        {
            // VARIABLE divisor provably ≥ 1 with a non-negative dividend (see
            // the doc): `q ≥ 0`, and `q ≤ U` under a present `a ≤ U`, `U ≥ 0`.
            out.push(Formula::Ge(qv(), Box::new(Formula::Int(0))));
            if let Some(u) = upper(&a_name).filter(|u| *u >= 0) {
                out.push(Formula::Le(qv(), Box::new(Formula::Int(u))));
            }
        }
    }
    out
}

/// Emit only the atoms NOT already present (structurally) in the view, nor
/// duplicated within the emission itself. Duplicates would be semantically
/// harmless downstream (fresh fvar per hyp; ay asserts are idempotent) but
/// would change context/term bytes for every existing certificate whose pool
/// a late pass revisits WITHOUT deriving any new fact — gratuitous,
/// no-new-coverage churn that [`recheck_cleancic`]'s byte-exact regeneration
/// would surface as replay breaks. Pools where the late pass derives a
/// genuinely NEW atom still change bytes — see the certificate-byte candor
/// note on [`NORMALIZATION_STEPS`].
fn retain_new_atoms(view: &[&Formula], emitted: Vec<Formula>) -> Vec<Formula> {
    let mut out: Vec<Formula> = Vec::new();
    for atom in emitted {
        if view.iter().any(|&c| *c == atom) || out.contains(&atom) {
            continue;
        }
        out.push(atom);
    }
    out
}

/// Second pass of [`modulo_range_bounds`] after the equality-class bound
/// propagation: steps run in table order over a growing pool, so divisor
/// positivity / dividend bounds that ARRIVE via
/// `propagate_equality_class_bounds` are invisible to the first pass.
/// New-atoms-only ([`retain_new_atoms`]): the pool is byte-identical whenever
/// this pass derives nothing beyond pass 1.
fn modulo_range_bounds_late(conjuncts: &[&Formula]) -> Vec<Formula> {
    retain_new_atoms(conjuncts, modulo_range_bounds(conjuncts))
}

/// Second pass of [`division_range_bounds`] — see [`modulo_range_bounds_late`].
fn division_range_bounds_late(conjuncts: &[&Formula]) -> Vec<Formula> {
    retain_new_atoms(conjuncts, division_range_bounds(conjuncts))
}

fn membership_interval_bounds(conjuncts: &[&Formula]) -> Vec<Formula> {
    let mut out = Vec::new();
    for &c in conjuncts {
        let Formula::Or(disjuncts) = c else { continue };
        if disjuncts.is_empty() {
            continue;
        }
        let mut var: Option<&str> = None;
        let mut lits: Vec<i128> = Vec::with_capacity(disjuncts.len());
        let mut ok = true;
        for d in disjuncts {
            // Accept either operand order: `Eq(Var, Int)` or `Eq(Int, Var)`.
            let (v, n) = match d {
                Formula::Eq(a, b) => match (a.as_ref(), b.as_ref()) {
                    (Formula::Var(v, Sort::Int), Formula::Int(n)) => (v.as_str(), *n),
                    (Formula::Int(n), Formula::Var(v, Sort::Int)) => (v.as_str(), *n),
                    _ => {
                        ok = false;
                        break;
                    }
                },
                _ => {
                    ok = false;
                    break;
                }
            };
            match var {
                None => var = Some(v),
                Some(prev) if prev == v => {}
                Some(_) => {
                    ok = false;
                    break;
                }
            }
            lits.push(n);
        }
        if !ok {
            continue;
        }
        if let Some(v) = var {
            let lo = lits.iter().copied().min().unwrap();
            let hi = lits.iter().copied().max().unwrap();
            out.push(Formula::Ge(
                Box::new(Formula::Var(v.to_string(), Sort::Int)),
                Box::new(Formula::Int(lo)),
            ));
            out.push(Formula::Le(
                Box::new(Formula::Var(v.to_string(), Sort::Int)),
                Box::new(Formula::Int(hi)),
            ));
        }
    }
    out
}

/// Discharge implications whose antecedent is a numerically-entailed bound. For a
/// conjunct `Implies(ante, cons)` where `ante` is `Ge(v,k)` / `Le(v,k)` over an Int
/// var `v`, check whether the present conjuncts already force the bound (a `Ge(v,b)`
/// with `b ≥ k` for a `Ge` antecedent, a `Le(v,b)` with `b ≤ k` for a `Le`
/// antecedent, or an `Eq(v,c)` literal in range). When entailed, emit the consequent
/// `cons` as a derived fact. The nonneg-widening-cast guard
/// `Implies(Ge(_4,0), Eq(_3,_4))` discharges here because the membership bound
/// `Ge(_4,0)` is present. Sound: modus ponens — `(ante → cons) ∧ ante ⊢ cons`, and
/// `ante` is emitted only when it is a genuine consequence of present bounds.
fn discharge_entailed_implications(conjuncts: &[&Formula]) -> Vec<Formula> {
    // Best-known lower/upper bound for each var from present `Ge`/`Le`/`Eq` literals.
    let mut lower: std::collections::BTreeMap<String, i128> = std::collections::BTreeMap::new();
    let mut upper: std::collections::BTreeMap<String, i128> = std::collections::BTreeMap::new();
    let mut note_lower = |v: &str, n: i128| {
        lower
            .entry(v.to_string())
            .and_modify(|e| {
                if n > *e {
                    *e = n;
                }
            })
            .or_insert(n);
    };
    // (separate closure borrow scoping: build both maps in one pass)
    for &c in conjuncts {
        match c {
            Formula::Ge(a, b) => match (a.as_ref(), b.as_ref()) {
                (Formula::Var(v, Sort::Int), Formula::Int(n)) => note_lower(v, *n),
                (Formula::Int(n), Formula::Var(v, Sort::Int)) => {
                    upper
                        .entry(v.clone())
                        .and_modify(|e| {
                            if *n < *e {
                                *e = *n;
                            }
                        })
                        .or_insert(*n);
                }
                _ => {}
            },
            Formula::Le(a, b) => match (a.as_ref(), b.as_ref()) {
                (Formula::Var(v, Sort::Int), Formula::Int(n)) => {
                    upper
                        .entry(v.clone())
                        .and_modify(|e| {
                            if *n < *e {
                                *e = *n;
                            }
                        })
                        .or_insert(*n);
                }
                (Formula::Int(n), Formula::Var(v, Sort::Int)) => note_lower(v, *n),
                _ => {}
            },
            Formula::Eq(a, b) => match (a.as_ref(), b.as_ref()) {
                (Formula::Var(v, Sort::Int), Formula::Int(n))
                | (Formula::Int(n), Formula::Var(v, Sort::Int)) => {
                    note_lower(v, *n);
                    upper
                        .entry(v.clone())
                        .and_modify(|e| {
                            if *n < *e {
                                *e = *n;
                            }
                        })
                        .or_insert(*n);
                }
                _ => {}
            },
            _ => {}
        }
    }
    let mut out = Vec::new();
    for &c in conjuncts {
        let Formula::Implies(ante, cons) = c else { continue };
        let entailed = match ante.as_ref() {
            // `v ≥ k` entailed iff a known lower bound is ≥ k.
            Formula::Ge(a, b) => match (a.as_ref(), b.as_ref()) {
                (Formula::Var(v, Sort::Int), Formula::Int(k)) => {
                    lower.get(v).is_some_and(|lo| lo >= k)
                }
                (Formula::Int(k), Formula::Var(v, Sort::Int)) => {
                    // `k ≥ v` iff a known upper bound is ≤ k.
                    upper.get(v).is_some_and(|up| up <= k)
                }
                _ => false,
            },
            // `v ≤ k` entailed iff a known upper bound is ≤ k.
            Formula::Le(a, b) => match (a.as_ref(), b.as_ref()) {
                (Formula::Var(v, Sort::Int), Formula::Int(k)) => {
                    upper.get(v).is_some_and(|up| up <= k)
                }
                (Formula::Int(k), Formula::Var(v, Sort::Int)) => {
                    lower.get(v).is_some_and(|lo| lo >= k)
                }
                _ => false,
            },
            _ => false,
        };
        if entailed {
            out.push((**cons).clone());
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Supported fragment: linear-integer order atoms over free Int variables.
// ---------------------------------------------------------------------------

/// The `Int` kernel type.
fn int_ty() -> Expr {
    Expr::const_(Name::from_string("Int"), vec![])
}

/// `False` as the kernel constant `False` (no level args).
fn false_expr() -> Expr {
    Expr::const_(Name::from_string("False"), Vec::new())
}

/// `Not False` — the dummy negated goal passed to reconstruction when the
/// contradiction lives entirely in the asserted hypotheses.
fn neg_false() -> Expr {
    not_prop(false_expr())
}

/// `Int.ofNat n` — a non-negative integer literal as a kernel term.
fn int_ofnat(n: u64) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), Expr::nat_lit(n))
}

/// `Int.ofNat n` for an arbitrary `u128` magnitude (values > `u64::MAX` use the
/// kernel's arbitrary-precision `BigNat`). Needed for `i128`/`u128` type thresholds.
fn int_ofnat_u128(n: u128) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), Expr::nat_lit_u128(n))
}

/// `Int.negSucc n` (= `-(n+1)`) for an arbitrary `u128` index.
fn int_neg_succ_u128(n: u128) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.negSucc"), vec![]), Expr::nat_lit_u128(n))
}

fn int_literal_to_kernel(n: i128) -> Option<Expr> {
    // Full i128 range: the kernel `Nat` is arbitrary-precision (`BigNat`), so a
    // threshold > u64::MAX (e.g. `i128::MAX`/`i128::MIN`) encodes via `nat_lit_u128`.
    if n >= 0 {
        Some(int_ofnat_u128(n as u128))
    } else {
        // `Int.negSucc m = -(m+1) = n`  ⇒  `m = |n| - 1` (fits `u128` for all i128).
        Some(int_neg_succ_u128(n.unsigned_abs() - 1))
    }
}

fn int_literal_to_smt(n: i128) -> Option<String> {
    if n >= 0 { Some(n.to_string()) } else { Some(format!("(- {})", n.unsigned_abs())) }
}

/// `@LT.lt Int instLTInt a b`.
fn lt_int(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]), int_ty()),
                Expr::const_(Name::from_string("instLTInt"), vec![]),
            ),
            a,
        ),
        b,
    )
}

/// `@LE.le Int instLEInt a b`. (`LE.le @Int instLEInt` δ-reduces to `Int.le`.)
fn le_int(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]), int_ty()),
                Expr::const_(Name::from_string("instLEInt"), vec![]),
            ),
            a,
        ),
        b,
    )
}

/// `@HAdd.hAdd.{0,0,0} Int Int Int instHAddInt a b` — the elaborated integer
/// addition clean-auto's reconstruction emits via `translate_term` (`mk_add`).
/// The registered hypothesis prop must use THIS form (not the raw `Int.add`)
/// so `find_hypothesis_by_prop`'s structural match succeeds and the kernel
/// re-check passes. n-ary sums fold left at the call site.
fn hadd_int(a: Expr, b: Expr) -> Expr {
    let int = int_ty();
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("HAdd.hAdd"),
                                vec![Level::zero(), Level::zero(), Level::zero()],
                            ),
                            int.clone(),
                        ),
                        int.clone(),
                    ),
                    int,
                ),
                Expr::const_(Name::from_string("instHAddInt"), vec![]),
            ),
            a,
        ),
        b,
    )
}

/// Register the `HAdd Int Int Int` instance so `hadd_int` props type-check.
/// Mirrors clean-auto's `ensure_int_hadd_support`: `init_hadd` + a reducible
/// `instHAddInt := @HAdd.mk Int Int Int Int.add`. Idempotent. Returns `None`
/// (fail-closed) if any kernel declaration is rejected.
fn ensure_hadd(env: &mut Environment) -> Option<()> {
    env.init_hadd().ok()?;
    if env.get_const(&Name::from_string("instHAddInt")).is_some() {
        return Some(());
    }
    let int = int_ty();
    let levels = vec![Level::zero(), Level::zero(), Level::zero()];
    let inst_type = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("HAdd"), levels.clone()), int.clone()),
            int.clone(),
        ),
        int.clone(),
    );
    let inst_value = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("HAdd.mk"), levels), int.clone()),
                int.clone(),
            ),
            int,
        ),
        Expr::const_(Name::from_string("Int.add"), vec![]),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("instHAddInt"),
        level_params: vec![],
        type_: inst_type,
        value: inst_value,
        is_reducible: true,
    })
    .ok()?;
    Some(())
}

/// `@HMul.hMul.{0,0,0} Int Int Int instHMulInt a b` — the elaborated integer
/// multiplication clean-auto's reconstruction emits via `translate_term`
/// (`mk_mul`). As with `hadd_int`, the registered hypothesis prop must use this
/// HMul form (not raw `Int.mul`) for `find_hypothesis_by_prop` to match. ay
/// normalizes `(* lit var)` to variable-first `(* var lit)`, so callers must
/// pass the variable term as `a` and the literal as `b`.
fn hmul_int(a: Expr, b: Expr) -> Expr {
    let int = int_ty();
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("HMul.hMul"),
                                vec![Level::zero(), Level::zero(), Level::zero()],
                            ),
                            int.clone(),
                        ),
                        int.clone(),
                    ),
                    int,
                ),
                Expr::const_(Name::from_string("instHMulInt"), vec![]),
            ),
            a,
        ),
        b,
    )
}

/// Register the `HMul Int Int Int` instance so `hmul_int` props type-check.
/// Mirrors `ensure_hadd`: `init_hmul` (public) + a reducible
/// `instHMulInt := @HMul.mk Int Int Int Int.mul`. `Int.mul` is provided by
/// `init_int_ord_lemmas` (via `init_int_arith`). Idempotent; fail-closed.
fn ensure_hmul(env: &mut Environment) -> Option<()> {
    env.init_hmul().ok()?;
    if env.get_const(&Name::from_string("instHMulInt")).is_some() {
        return Some(());
    }
    let int = int_ty();
    let levels = vec![Level::zero(), Level::zero(), Level::zero()];
    let inst_type = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("HMul"), levels.clone()), int.clone()),
            int.clone(),
        ),
        int.clone(),
    );
    let inst_value = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("HMul.mk"), levels), int.clone()),
                int.clone(),
            ),
            int,
        ),
        Expr::const_(Name::from_string("Int.mul"), vec![]),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("instHMulInt"),
        level_params: vec![],
        type_: inst_type,
        value: inst_value,
        is_reducible: true,
    })
    .ok()?;
    Some(())
}

/// Split a `Mul` into `(literal_coefficient, variable_term)` iff EXACTLY one
/// operand is an integer literal and the other is a supported non-literal term.
/// Returns `None` for literal×literal (foldable) and var×var (nonlinear NIA,
/// which must fail closed). This keeps the fragment LINEAR.
fn linear_mul_operands<'a>(a: &'a Formula, b: &'a Formula) -> Option<(i128, &'a Formula)> {
    match (int_literal_value(a), int_literal_value(b)) {
        (Some(_), Some(_)) | (None, None) => None,
        (Some(lit), None) => Some((lit, b)),
        (None, Some(lit)) => Some((lit, a)),
    }
}

/// Constant-fold closed integer arithmetic (`Mul`/`Add`/`Sub`/`Neg` over `Int`
/// literals) into a single `Int`, recursing through the boolean / comparison
/// structure. A guarded `cols * 64` lowers its else-branch as the closed-constant
/// overflow check `Or([Lt(Mul(4096,64),0), Gt(Mul(4096,64),MAX)])`; `chain_node`
/// rejects `Mul(Int,Int)` (it models only `Mul(var,lit)` via `ChainNode::Scaled`),
/// so the disjunct's operand never reduces and the obligation stays uncertified.
/// Folding `Mul(4096,64) → 262144` turns it into the variable-free order-atom
/// disjunction that `certify_closed_constant_contradiction` discharges. Sound:
/// `Int.mul`/`Int.add`/`Int.sub` over literals is a definitional reduction the clean
/// kernel performs identically, so the folded form is provably equal; `checked_*`
/// guards keep an overflowing fold from wrapping (it just stays unfolded).
fn fold_constant_arith(f: &Formula) -> Formula {
    use Formula::{Add, And, Eq, Ge, Gt, Int, Le, Lt, Mul, Neg, Not, Or, Sub};
    match f {
        Mul(a, b) => {
            let (fa, fb) = (fold_constant_arith(a), fold_constant_arith(b));
            if let (Int(x), Int(y)) = (&fa, &fb) {
                if let Some(p) = x.checked_mul(*y) {
                    return Int(p);
                }
            }
            Mul(Box::new(fa), Box::new(fb))
        }
        Add(a, b) => {
            let (fa, fb) = (fold_constant_arith(a), fold_constant_arith(b));
            if let (Int(x), Int(y)) = (&fa, &fb) {
                if let Some(p) = x.checked_add(*y) {
                    return Int(p);
                }
            }
            Add(Box::new(fa), Box::new(fb))
        }
        Sub(a, b) => {
            let (fa, fb) = (fold_constant_arith(a), fold_constant_arith(b));
            if let (Int(x), Int(y)) = (&fa, &fb) {
                if let Some(p) = x.checked_sub(*y) {
                    return Int(p);
                }
            }
            Sub(Box::new(fa), Box::new(fb))
        }
        Neg(a) => {
            let fa = fold_constant_arith(a);
            if let Int(x) = &fa {
                if let Some(n) = x.checked_neg() {
                    return Int(n);
                }
            }
            Neg(Box::new(fa))
        }
        Not(x) => Not(Box::new(fold_constant_arith(x))),
        And(cs) => And(cs.iter().map(fold_constant_arith).collect()),
        Or(ds) => Or(ds.iter().map(fold_constant_arith).collect()),
        Lt(a, b) => Lt(Box::new(fold_constant_arith(a)), Box::new(fold_constant_arith(b))),
        Le(a, b) => Le(Box::new(fold_constant_arith(a)), Box::new(fold_constant_arith(b))),
        Gt(a, b) => Gt(Box::new(fold_constant_arith(a)), Box::new(fold_constant_arith(b))),
        Ge(a, b) => Ge(Box::new(fold_constant_arith(a)), Box::new(fold_constant_arith(b))),
        Eq(a, b) => Eq(Box::new(fold_constant_arith(a)), Box::new(fold_constant_arith(b))),
        other => other.clone(),
    }
}

/// Constant-folded copies of any conjuncts whose closed arithmetic actually reduces
/// (`fold_constant_arith` changed something). Only the CHANGED conjuncts are
/// returned, so the unfolded majority is not duplicated. The copies are added
/// alongside the originals; the closed-constant / disjunctive paths then pick up the
/// folded form. `out` owns them.
fn fold_constant_arith_conjuncts(conjuncts: &[&Formula]) -> Vec<Formula> {
    let mut out = Vec::new();
    for &c in conjuncts {
        let folded = fold_constant_arith(c);
        if &folded != c {
            out.push(folded);
        }
    }
    out
}

/// Tighten STRICT integer bounds to their non-strict equivalent: over the integers
/// `v < k ⟺ v ≤ k−1` and `v > k ⟺ v ≥ k+1`. The multiplicative lift
/// (`Int.mul_le_mul_of_nonneg_right`) and the additive lift compose only NON-strict
/// `≤`/`≥` bounds, so a loop counter bounded by `Lt(y,3)` (`for y in 0..3`) never lifts
/// to `y*4 ≤ 8` and its overflow stays uncertified — even though the identical
/// `cols*64` shape certifies from an already-non-strict `Le(cols,4096)`. Emit
/// `Le(v,k−1)` / `Ge(v,k+1)` for every strict literal bound (both operand orders).
/// Sound: an exact integer-order equivalence; `checked_*` guards a wrap at the i128
/// extremes.
fn tighten_strict_int_bounds(conjuncts: &[&Formula]) -> Vec<Formula> {
    let mut out = Vec::new();
    let is_var =
        |f: &Formula| matches!(f, Formula::Var(_, Sort::Int) | Formula::SymVar(_, Sort::Int));
    for &c in conjuncts {
        match c {
            // `v < k`  ⟹  `v ≤ k−1`.
            Formula::Lt(a, b) if is_var(a) => {
                if let Some(k) = int_literal_value(b).and_then(|k| k.checked_sub(1)) {
                    out.push(Formula::Le(a.clone(), Box::new(Formula::Int(k))));
                }
            }
            // `k < v`  ⟹  `v ≥ k+1`.
            Formula::Lt(a, b) if is_var(b) => {
                if let Some(k) = int_literal_value(a).and_then(|k| k.checked_add(1)) {
                    out.push(Formula::Ge(b.clone(), Box::new(Formula::Int(k))));
                }
            }
            // `v > k`  ⟹  `v ≥ k+1`.
            Formula::Gt(a, b) if is_var(a) => {
                if let Some(k) = int_literal_value(b).and_then(|k| k.checked_add(1)) {
                    out.push(Formula::Ge(a.clone(), Box::new(Formula::Int(k))));
                }
            }
            // `k > v`  ⟹  `v ≤ k−1`.
            Formula::Gt(a, b) if is_var(b) => {
                if let Some(k) = int_literal_value(a).and_then(|k| k.checked_sub(1)) {
                    out.push(Formula::Le(b.clone(), Box::new(Formula::Int(k))));
                }
            }
            _ => {}
        }
    }
    out
}

/// Extract the conjuncts COMMON to every disjunct of an `Or` and emit them as
/// entailed top-level facts. If a literal `L` is a (possibly nested) conjunct of
/// EVERY disjunct `Dᵢ` of `Or([D₁,…,Dₙ])`, then `Dᵢ ⊢ L` for each `i`, so
/// `Or([Dᵢ]) ⊢ L` by Or-elimination — emitting `L` is sound.
///
/// A guarded division `n / d` (guard `d != 0`) lowers its failure VC as a path
/// disjunction `Or([pathA, pathB])` where EVERY path conjoins both the guard
/// `Not(Eq(d,0))` AND the divide-by-zero failure `Eq(d,0)` (the failure condition is
/// asserted on every path that reaches the div). The disjuncts themselves are complex
/// conjunctions (reified-bool guards) that `parse_disjunct` cannot refute atom-by-atom,
/// but the COMMON `Eq(d,0)` and `Not(Eq(d,0))` are surfaced here, meeting the
/// `certify_direct_disequality_contradiction` directly. The `Or` is left in place
/// (only weakening it would be unsound; adding entailed facts never is).
fn extract_disjunction_common_conjuncts(conjuncts: &[&Formula]) -> Vec<Formula> {
    let mut out: Vec<Formula> = Vec::new();
    for &c in conjuncts {
        let Formula::Or(disjuncts) = c else { continue };
        if disjuncts.len() < 2 {
            continue;
        }
        // Flatten each disjunct into its (recursive) conjunct set.
        let mut sets: Vec<Vec<&Formula>> = Vec::with_capacity(disjuncts.len());
        for d in disjuncts {
            let mut cs: Vec<&Formula> = Vec::new();
            collect_conjuncts(d, &mut cs);
            sets.push(cs);
        }
        let Some((first, rest)) = sets.split_first() else { continue };
        for &f in first {
            // Common to EVERY disjunct?
            if rest.iter().all(|s| s.iter().any(|&g| g == f))
                && !matches!(f, Formula::Bool(true))
                && !out.iter().any(|o| o == f)
            {
                out.push(f.clone());
            }
        }
    }
    out
}

/// The `i128` value of a `Formula` integer literal (`Int`/`UInt`), else `None`.
fn int_literal_value(f: &Formula) -> Option<i128> {
    match f {
        Formula::Int(n) => Some(*n),
        Formula::UInt(n) if *n <= i128::MAX as u128 => Some(*n as i128),
        _ => None,
    }
}

/// `@Eq Int a b`.
fn eq_int(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                int_ty(),
            ),
            a,
        ),
        b,
    )
}

fn not_prop(prop: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop)
}

/// `@Eq.refl Int a`.
fn eq_refl_int(a: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            int_ty(),
        ),
        a,
    )
}

/// A normalized linear-integer atom: a strict `<` or a non-strict `≤`. Every
/// supported comparison — and its negation, and `=` — reduces to these two via
/// [`normalize_atom`]. These are exactly the bounds ay's Farkas (`la_generic`)
/// proofs reconstruct with ZERO residual trust.
enum Atom<'a> {
    /// `a < b`.
    Lt(&'a Formula, &'a Formula),
    /// `a ≤ b`.
    Le(&'a Formula, &'a Formula),
}

/// Normalize a violation conjunct into one or more supported [`Atom`]s, or
/// `None` if it is outside the fragment (→ fail closed). Over a total integer
/// order: `a>b ≡ b<a`, `a≥b ≡ b≤a`, `¬(a≥b) ≡ a<b`, `¬(a≤b) ≡ b<a`,
/// `¬(a>b) ≡ a≤b`, `¬(a<b) ≡ b≤a`.
///
/// `a = b` is split into `a ≤ b ∧ b ≤ a` — asserting equality as two
/// inequalities (NOT a single `=`) is the crux of zero-trust reconstruction: a
/// raw `=` assumption gets decomposed by ay for the Farkas lemma, and the
/// decomposed literals no longer syntactically match the assumption, forcing a
/// `trustedAy` fallback. Two `≤` assumptions match their lemma literals exactly.
fn normalize_atom(f: &Formula) -> Option<Vec<Atom<'_>>> {
    Some(match f {
        Formula::Lt(a, b) => vec![Atom::Lt(a, b)],
        Formula::Gt(a, b) => vec![Atom::Lt(b, a)],
        Formula::Le(a, b) => vec![Atom::Le(a, b)],
        Formula::Ge(a, b) => vec![Atom::Le(b, a)],
        Formula::Eq(a, b) => vec![Atom::Le(a, b), Atom::Le(b, a)],
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Ge(a, b) => vec![Atom::Lt(a, b)],
            Formula::Le(a, b) => vec![Atom::Lt(b, a)],
            Formula::Gt(a, b) => vec![Atom::Le(a, b)],
            Formula::Lt(a, b) => vec![Atom::Le(b, a)],
            _ => return None,
        },
        _ => return None,
    })
}

/// Keep the conjuncts that lie wholly inside the supported linear-integer atom
/// fragment, DROPPING every conjunct outside it, and return the kept atoms plus
/// their free `Int` variable names. A conjunct is kept only if [`normalize_atom`]
/// accepts it AND all its leaves are supported `Int` terms.
///
/// SOUNDNESS — why dropping conjuncts is safe for a *refutation* (UNSAT) proof.
/// The obligation's violation is the conjunction of all conjuncts; certifying it
/// means proving that conjunction UNSAT (its negation — the safety property —
/// valid). If a SUBSET of the conjuncts is already contradictory, the full
/// conjunction, which only adds constraints, is a fortiori UNSAT (∧-elimination).
/// The converse we depend on is airtight: if the full conjunction were
/// SATISFIABLE — a real violation / buggy obligation — then EVERY subset would be
/// satisfiable too, so the kept subset's ay solve would return SAT and we would
/// fail closed. A certificate is minted ONLY when the kept subset is itself
/// refuted by ay and re-checked by the clean kernel, so a satisfiable obligation
/// can never be certified. Dropping the reified `Bool = (x < y)` equalities and
/// other surrounding non-linear conjuncts a real bounds/guard VC carries is
/// exactly what exposes the linear-Int contradiction at its core to the kernel.
///
/// Producer ([`certify_with_identity`]) and consumer ([`recheck_cleancic`]) MUST
/// call this same function so they agree on the kept subset and its variables.
/// Build the canonical hypothesis list for the supported order-atom fragment:
/// one [`Hyp`] per atom, fvars allocated sequentially from [`HYP_FVAR_BASE`] and
/// names `h_{i}`. Returns `None` if any atom falls outside the SMT/kernel
/// encodable shape (→ fail closed).
///
/// Called IDENTICALLY by the producer ([`certify_with_identity`]) and the
/// consumer ([`recheck_cleancic`]) so the local context the kernel checks the
/// refutation against is the same on both sides — see the soundness note on
/// [`collect_supported_atoms`].
fn supported_hyps_from_atoms(atoms: &[Atom<'_>]) -> Option<Vec<Hyp>> {
    let mut hyps: Vec<Hyp> = Vec::with_capacity(atoms.len());
    for (i, atom) in atoms.iter().enumerate() {
        // Int.sub-aware renderers (superset of atom_to_smt/atom_to_kernel_prop): a
        // guarded-subtraction underflow atom `Sub(a,b) < 0` builds a hypothesis whose
        // kernel prop matches the linear_term_to_kernel Diff-chain edges, keeping
        // guarded_sub / guarded_two_var_sub / scrollback_trim certification consistent.
        // Shared by producer AND recheck_cleancic so both build the IDENTICAL context.
        let smt = linear_atom_smt(atom)?;
        let prop = linear_atom_prop(atom)?;
        let fvar = FVarId::new(HYP_FVAR_BASE + i as u64);
        hyps.push(Hyp { smt, prop, fvar, name: format!("h_{i}") });
    }
    Some(hyps)
}

fn collect_supported_atoms<'a>(conjuncts: &[&'a Formula]) -> (Vec<Atom<'a>>, BTreeSet<String>) {
    let mut atoms: Vec<Atom<'a>> = Vec::new();
    let mut var_names: BTreeSet<String> = BTreeSet::new();
    for &c in conjuncts {
        let Some(normalized) = normalize_atom(c) else {
            continue;
        };
        // Only keep the conjunct if EVERY resulting atom's leaves are supported
        // Int terms; collect its vars into a scratch set first so a rejected
        // conjunct contributes nothing to `var_names`.
        let mut local_vars = BTreeSet::new();
        if normalized.iter().all(|a| collect_int_vars(a, &mut local_vars)) {
            var_names.extend(local_vars);
            atoms.extend(normalized);
        }
    }
    (atoms, var_names)
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum IntTermKey {
    Var(String),
    Lit(i128),
}

#[derive(Clone, PartialEq, Eq)]
struct EqKey {
    lhs: IntTermKey,
    rhs: IntTermKey,
}

struct CanonicalEq<'a> {
    lhs: &'a Formula,
    rhs: &'a Formula,
    key: EqKey,
}

/// A supported integer disequality is generally a disjunction (`a < b ∨ b < a`)
/// and therefore outside the Farkas-only atom fragment. This path accepts only
/// direct contradictions:
///
/// * `a = b ∧ a != b`, after canonicalizing equality symmetry; or
/// * `a != a`, closed by `Eq.refl`.
///
/// All terms must still be in the same supported `Int` term fragment, and every
/// other conjunct must be an already-supported order atom. General `a != b`
/// remains fail-closed.
/// For a disequality `x != y` whose two vars are in the SAME var=var equality class
/// (`x = … = y` via a chain of `Eq` conjuncts), emit the entailed direct `Eq(x, y)`,
/// so `certify_direct_disequality_contradiction` (which matches an `Eq` and a `Not(Eq)`
/// of the SAME canonical key) closes the contradiction. Example: the field-identity
/// `_4 = a.0 ∧ a.0 = v ∧ _4 != v`. SOUND: the union-find only unions vars connected by
/// actual `Eq` conjuncts, so the emitted equality is entailed by the obligation (same
/// basis as `propagate_constant_equalities`); the ay cross-check + clean-kernel re-check
/// in `finish_certificate` are the backstops.
fn complete_class_disequalities(conjuncts: &[&Formula]) -> Vec<Formula> {
    use std::collections::BTreeMap;
    let mut parent: BTreeMap<String, String> = BTreeMap::new();
    fn find(parent: &mut BTreeMap<String, String>, x: &str) -> String {
        match parent.get(x).cloned() {
            None => x.to_string(),
            Some(p) if p == x => p,
            Some(p) => {
                let root = find(parent, &p);
                parent.insert(x.to_string(), root.clone());
                root
            }
        }
    }
    for &c in conjuncts {
        if let Formula::Eq(a, b) = c
            && let (Formula::Var(x, Sort::Int), Formula::Var(y, Sort::Int)) =
                (a.as_ref(), b.as_ref())
        {
            parent.entry(x.clone()).or_insert_with(|| x.clone());
            parent.entry(y.clone()).or_insert_with(|| y.clone());
            let (rx, ry) = (find(&mut parent, x), find(&mut parent, y));
            if rx != ry {
                parent.insert(rx, ry);
            }
        }
    }
    if parent.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    for &c in conjuncts {
        if let Formula::Not(inner) = c
            && let Formula::Eq(a, b) = inner.as_ref()
            && let (Formula::Var(x, Sort::Int), Formula::Var(y, Sort::Int)) =
                (a.as_ref(), b.as_ref())
            && parent.contains_key(x)
            && parent.contains_key(y)
            && find(&mut parent, x) == find(&mut parent, y)
        {
            out.push(Formula::Eq(
                Box::new(Formula::Var(x.clone(), Sort::Int)),
                Box::new(Formula::Var(y.clone(), Sort::Int)),
            ));
        }
    }
    out
}

/// The canonical eq/neq/order hypothesis context of the DIRECT-DISEQUALITY
/// refutation path, built from the (normalized) obligation conjuncts ONLY —
/// single-sourced between the producer
/// ([`certify_direct_disequality_contradiction`]) and the consumer re-check
/// ([`recheck_cleancic`]), which must rebuild the IDENTICAL context (same hyp
/// order, hence the same fvar ids the serialized term references) to re-type a
/// certificate minted by this path.
struct DirectDisequalityHyps {
    hyps: Vec<Hyp>,
    var_names: BTreeSet<String>,
    eq_hyps: Vec<(EqKey, FVarId)>,
    neq_hyps: Vec<(EqKey, FVarId, Expr)>,
}

fn direct_disequality_hyps(conjuncts: &[&Formula]) -> Option<DirectDisequalityHyps> {
    let mut var_names: BTreeSet<String> = BTreeSet::new();
    let mut hyps: Vec<Hyp> = Vec::new();
    let mut eq_hyps: Vec<(EqKey, FVarId)> = Vec::new();
    let mut neq_hyps: Vec<(EqKey, FVarId, Expr)> = Vec::new();

    for conjunct in conjuncts {
        match conjunct {
            Formula::Eq(a, b) => {
                let eq = canonical_int_eq(a, b)?;
                collect_direct_eq_vars(&eq, &mut var_names)?;
                let lhs = term_to_kernel(eq.lhs)?;
                let rhs = term_to_kernel(eq.rhs)?;
                let prop = eq_int(lhs, rhs);
                let fvar = push_hyp(
                    &mut hyps,
                    format!("(= {} {})", term_to_smt(eq.lhs)?, term_to_smt(eq.rhs)?),
                    prop,
                );
                eq_hyps.push((eq.key, fvar));
            }
            Formula::Not(inner) => match inner.as_ref() {
                Formula::Eq(a, b) => {
                    let eq = canonical_int_eq(a, b)?;
                    collect_direct_eq_vars(&eq, &mut var_names)?;
                    let lhs = term_to_kernel(eq.lhs)?;
                    let rhs = term_to_kernel(eq.rhs)?;
                    let prop = not_prop(eq_int(lhs.clone(), rhs));
                    let fvar = push_hyp(
                        &mut hyps,
                        format!("(not (= {} {}))", term_to_smt(eq.lhs)?, term_to_smt(eq.rhs)?),
                        prop,
                    );
                    neq_hyps.push((eq.key, fvar, lhs));
                }
                _ => {
                    // Skip a conjunct outside the eq/neq/order fragment (an `Or`
                    // path-disjunction, a residual nested `And`, a Bool reification):
                    // `push_order_hyps` returns `None` without mutating, and dropping it
                    // only WEAKENS the asserted hypotheses — sound for a refutation that
                    // is closed by the matching eq+neq pair alone (ay still re-checks the
                    // asserted set is UNSAT, and the kernel re-checks the term).
                    let _ = push_order_hyps(*conjunct, &mut hyps, &mut var_names);
                }
            },
            _ => {
                let _ = push_order_hyps(*conjunct, &mut hyps, &mut var_names);
            }
        }
    }

    Some(DirectDisequalityHyps { hyps, var_names, eq_hyps, neq_hyps })
}

fn certify_direct_disequality_contradiction(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let DirectDisequalityHyps { hyps, var_names, eq_hyps, neq_hyps } =
        direct_disequality_hyps(conjuncts)?;

    let proof = direct_disequality_refutation(&eq_hyps, &neq_hyps)?;

    let env = build_env(&var_names)?;

    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
    for name in &var_names {
        backend.add_raw_declaration(&format!("(declare-fun {} () Int)", encoded_var_name(name)));
    }
    for hyp in &hyps {
        backend.assert_formula(&hyp.smt);
    }
    // Trust (parallel verify): serialize ONLY the raw ay solve on the shared
    // `trust_types::ay_exec_lock()` (ay's direct path is non-reentrant). The lock
    // drops at the end of this block — BEFORE the clean-kernel reconstruction /
    // re-check below, which is thread-safe by construction and must stay unlocked
    // so it parallelizes across verification threads.
    match {
        let _ay_guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());
        backend.check_sat()
    } {
        Ok(AyProofResult::Unsat { .. }) => {}
        _ => return None,
    }

    let ctx = build_ctx(&hyps);
    if !kernel_checks_false(&env, ctx.clone(), &proof, &var_names) {
        return None;
    }

    let term_bytes = serialize_term(&proof).ok()?;
    let reduced = reduced_context(&ctx);
    let context_bytes = serialize_context(&reduced).ok()?;
    if !payload_roundtrip_rechecks(&var_names, &term_bytes, &context_bytes) {
        return None;
    }

    let lineage = lineage_digest(&term_bytes, &context_bytes, identity);
    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

fn push_hyp(hyps: &mut Vec<Hyp>, smt: String, prop: Expr) -> FVarId {
    let i = hyps.len();
    let fvar = FVarId::new(HYP_FVAR_BASE + i as u64);
    hyps.push(Hyp { smt, prop, fvar, name: format!("h_{i}") });
    fvar
}

// ---------------------------------------------------------------------------
// Closed-constant arithmetic contradictions (shift-amount / cast-range checks).
// ---------------------------------------------------------------------------

/// A variable-free integer order atom normalized to `Int.lt`/`Int.le`, carried
/// as its two literal operands. Every supported comparison and its negation
/// reduce to one of these two (mirrors [`normalize_atom`] over closed literals).
struct ClosedOrderAtom {
    /// Left operand literal of the normalized `Int.lt`/`Int.le`.
    a: i128,
    /// Right operand literal.
    b: i128,
    /// `true` for `a < b`, `false` for `a ≤ b`.
    is_lt: bool,
}

impl ClosedOrderAtom {
    /// Does this atom evaluate to `false`? `a < b` is false ⟺ `a ≥ b`; `a ≤ b`
    /// is false ⟺ `a > b`. Only a genuinely-false atom is refutable, so this is
    /// the soundness guard: a satisfiable obligation (real violation) has a true
    /// atom and is declined here, never refuted.
    fn is_false(&self) -> bool {
        if self.is_lt { self.a >= self.b } else { self.a > self.b }
    }

    /// The kernel native Int reducers (`Int.add`/`Int.sub`) operate over `i64`,
    /// so both operands must fit for the `Int.NonNeg.mk` witness type to reduce.
    fn operands_fit(&self) -> bool {
        i64::try_from(self.a).is_ok() && i64::try_from(self.b).is_ok()
    }
}

/// Parse a `Formula` into a closed (variable-free) order atom normalized to
/// `Int.lt`/`Int.le`, or `None` if it is not a comparison of two integer
/// literals. Order normalization mirrors [`normalize_atom`]: `a>b ≡ b<a`,
/// `a≥b ≡ b≤a`, and the four negated forms.
/// The non-negative unsigned value (`0..2^width-1`) of a concrete BitVec
/// term, or `None` for a non-literal leaf, a width mismatch, or a width too wide
/// to map into `i128`. Used to lift UNSIGNED BitVec comparisons (`bvult`/
/// `bvule`) onto the closed-Int-order refutation path: the unsigned value
/// compares identically as an `Int`, so no signedness information is lost.
/// Soundness rests on these being the explicitly-UNSIGNED `BvULt`/`BvULe`
/// variants — `BvSLt`/`BvSLe` (signed) are deliberately NOT lifted here, since
/// for a high-bit-set value signed and unsigned order disagree.
///
/// MB milestone-2: also constant-folds concrete `bvadd`/`bvsub` over BitVec
/// literals to their exact two's-complement residue `(a ± b) mod 2^w` (via
/// `rem_euclid`, which is the right primitive for the negative `bvsub`
/// intermediate). This is exact modular arithmetic done at lift time and the
/// resulting closed atom is still kernel-re-checked, so a fold bug can only
/// FAIL to certify, never mint an unsound certificate. Any non-literal (e.g.
/// symbolic `Var`) leaf hits the `_ => None` arm, so the lift is fail-closed on
/// symbolic operands by construction — symbolic `bvadd` needs the (not-yet-
/// proven) carrier adder lemma, NOT this fold.
fn bitvec_unsigned_value(f: &Formula, width: u32) -> Option<i128> {
    // Bound the width so `2^width` (and add/sub intermediates `< 2^{width+1}`)
    // fit the i128 carrier and the residue stays non-negative.
    if width == 0 || width > 126 {
        return None;
    }
    let modulus = 1i128 << width;
    match f {
        Formula::BitVec { value, width: vw } if *vw == width => Some(value.rem_euclid(modulus)),
        Formula::BvAdd(a, b, w) if *w == width => {
            let va = bitvec_unsigned_value(a, width)?;
            let vb = bitvec_unsigned_value(b, width)?;
            Some((va + vb).rem_euclid(modulus))
        }
        Formula::BvSub(a, b, w) if *w == width => {
            let va = bitvec_unsigned_value(a, width)?;
            let vb = bitvec_unsigned_value(b, width)?;
            Some((va - vb).rem_euclid(modulus))
        }
        _ => None,
    }
}

fn closed_order_atom(f: &Formula) -> Option<ClosedOrderAtom> {
    let v = int_literal_value;
    Some(match f {
        Formula::Lt(a, b) => ClosedOrderAtom { a: v(a)?, b: v(b)?, is_lt: true },
        Formula::Gt(a, b) => ClosedOrderAtom { a: v(b)?, b: v(a)?, is_lt: true },
        Formula::Le(a, b) => ClosedOrderAtom { a: v(a)?, b: v(b)?, is_lt: false },
        Formula::Ge(a, b) => ClosedOrderAtom { a: v(b)?, b: v(a)?, is_lt: false },
        // Unsigned BitVec comparisons over concrete literals. `bvult`/`bvule`
        // are the explicit UNSIGNED variants, so mapping the operands' unsigned
        // values (0..2^w-1) onto `Int.lt`/`Int.le` is faithful for ALL widths —
        // there is no signed/unsigned ambiguity. (MB milestone-1: this is what
        // makes the 8-bit `bvult` antisymmetry obligation Certifiable, by
        // refuting its trivially-false conjunct via the existing zero-trust
        // closed-constant kernel path. The signed `BvSLt`/`BvSLe` are NOT lifted.)
        Formula::BvULt(a, b, w) => ClosedOrderAtom {
            a: bitvec_unsigned_value(a, *w)?,
            b: bitvec_unsigned_value(b, *w)?,
            is_lt: true,
        },
        Formula::BvULe(a, b, w) => ClosedOrderAtom {
            a: bitvec_unsigned_value(a, *w)?,
            b: bitvec_unsigned_value(b, *w)?,
            is_lt: false,
        },
        Formula::Not(inner) => match inner.as_ref() {
            // ¬(a≥b) ≡ a<b ; ¬(a≤b) ≡ b<a ; ¬(a>b) ≡ a≤b ; ¬(a<b) ≡ b≤a
            Formula::Ge(a, b) => ClosedOrderAtom { a: v(a)?, b: v(b)?, is_lt: true },
            Formula::Le(a, b) => ClosedOrderAtom { a: v(b)?, b: v(a)?, is_lt: true },
            Formula::Gt(a, b) => ClosedOrderAtom { a: v(a)?, b: v(b)?, is_lt: false },
            Formula::Lt(a, b) => ClosedOrderAtom { a: v(b)?, b: v(a)?, is_lt: false },
            _ => return None,
        },
        _ => return None,
    })
}

/// The two integer-literal operands of a closed `Eq(a, b)`, or `(None, None)`
/// if either side is not an integer literal.
fn closed_int_eq_operands(f: &Formula) -> (Option<i128>, Option<i128>) {
    match f {
        Formula::Eq(a, b) => (int_literal_value(a), int_literal_value(b)),
        _ => (None, None),
    }
}

/// Apply a kernel constant (no level args) to a list of argument terms.
fn const_app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), vec![]), args)
}

/// `@Int.NonNeg.mk k : Int.NonNeg (Int.ofNat k)` — the positive witness whose
/// type def-eq-reduces (via the native `Int.sub`/`Int.add` reducers) to the
/// `Int.le`/`Int.lt` proposition we need.
fn nonneg_mk(k: u64) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]), Expr::nat_lit(k))
}

/// `Int.NonNeg.mk k` for an arbitrary `u128` gap witness (i128-range thresholds).
fn nonneg_mk_u128(k: u128) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]), Expr::nat_lit_u128(k))
}

/// The kernel proposition for a closed order atom, built from the BARE
/// `Int.lt`/`Int.le` constants (not `LT.lt`/`LE.le`) so it matches the
/// `Int.lt_of_lt_of_le` / `Int.lt_irrefl` theorem statements exactly.
fn closed_atom_prop(atom: &ClosedOrderAtom) -> Option<Expr> {
    let a = int_literal_to_kernel(atom.a)?;
    let b = int_literal_to_kernel(atom.b)?;
    Some(const_app(if atom.is_lt { "Int.lt" } else { "Int.le" }, [a, b]))
}

/// SMT-LIB2 rendering of a closed order atom (for the ay cross-check).
fn closed_atom_smt(atom: &ClosedOrderAtom) -> Option<String> {
    let a = int_literal_to_smt(atom.a)?;
    let b = int_literal_to_smt(atom.b)?;
    Some(if atom.is_lt { format!("(< {a} {b})") } else { format!("(<= {a} {b})") })
}

/// Build a kernel term of type `False` from a hypothesis `h : <atom>` for a
/// closed atom that evaluates to FALSE. Refutes via the true reverse inequality:
///
/// * `h : a < b` with `a ≥ b`: `pos := @Int.NonNeg.mk (a-b) : b ≤ a`, then
///   `Int.lt_irrefl a (Int.lt_of_lt_of_le a b a h pos) : False`.
/// * `h : a ≤ b` with `a > b`: `pos := @Int.NonNeg.mk (a-b-1) : b < a`, then
///   `Int.lt_irrefl b (Int.lt_of_lt_of_le b a b pos h) : False`.
///
/// Returns `None` (fail-closed) if the atom is not actually false or the gap
/// witness does not fit `u64`.
/// The non-negative gap `a - b` (with `a ≥ b`) as a `u128`, WITHOUT the
/// intermediate i128 overflow `checked_sub` would suffer at the type extremes.
///
/// When `a ≥ b` the true difference `a - b` is in `[0, u128::MAX]` (e.g.
/// `0 - i128::MIN = 2^127`, which exceeds `i128::MAX` but fits `u128`).
/// Reinterpreting both operands as their `u128` bit-patterns, `a as u128`
/// `wrapping_sub` `b as u128` yields exactly that magnitude in two's complement
/// (the wrap is the borrow that the signed subtraction would have produced), so
/// the witness `Int.NonNeg.mk (a-b)` is encoded faithfully for i128-extreme
/// thresholds. Returns `None` only when `a < b` (caller guards this).
fn nonneg_gap_u128(a: i128, b: i128) -> Option<u128> {
    if a < b {
        return None;
    }
    Some((a as u128).wrapping_sub(b as u128))
}

fn refute_false_atom(atom: &ClosedOrderAtom, h: Expr) -> Option<Expr> {
    if !atom.is_false() {
        return None;
    }
    let a = int_literal_to_kernel(atom.a)?;
    let b = int_literal_to_kernel(atom.b)?;
    if atom.is_lt {
        // a ≥ b ⇒ b ≤ a witnessed by NonNeg.mk (a-b). u128 gap (i128 thresholds).
        // Use the overflow-robust gap: `a - b` can be `2^127` (> i128::MAX) when
        // `b = i128::MIN`, which `checked_sub` rejects but `u128` represents.
        let k = nonneg_gap_u128(atom.a, atom.b)?;
        let pos = nonneg_mk_u128(k);
        let lt_aa = const_app("Int.lt_of_lt_of_le", [a.clone(), b, a.clone(), h, pos]);
        Some(Expr::app(const_app("Int.lt_irrefl", [a]), lt_aa))
    } else {
        // a > b ⇒ b < a witnessed by NonNeg.mk (a-b-1). u128 gap.
        let k = nonneg_gap_u128(atom.a, atom.b)?.checked_sub(1)?;
        let pos = nonneg_mk_u128(k);
        let lt_bb = const_app("Int.lt_of_lt_of_le", [b.clone(), a, b.clone(), pos, h]);
        Some(Expr::app(const_app("Int.lt_irrefl", [b]), lt_bb))
    }
}

/// `@Eq.symm.{1} Int a b (h : Eq a b) : Eq b a`.
fn eq_symm_int(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]),
        [int_ty(), a, b, h],
    )
}

/// `@Eq.subst.{1} Int motive a b (h : Eq a b) (m : motive a) : motive b`.
fn eq_subst_int(motive: Expr, a: Expr, b: Expr, h: Expr, m: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
        [int_ty(), motive, a, b, h, m],
    )
}

/// Build a kernel term of type `False` from a hypothesis `h : Eq a b` for two
/// DISTINCT integer literals (a closed false equality, e.g. the `2 = -1` divisor
/// conjunct of a constant-divisor division-overflow check). Refutes by transporting
/// the true strict inequality through the assumed equality into `Int.lt x x`:
///
/// * `a < b`: `pos := @Int.NonNeg.mk (b-a-1) : a < b`; rewrite `b ↦ a` along
///   `Eq.symm h` over motive `λt. a < t`, yielding `a < a`, then `Int.lt_irrefl a`.
/// * `a > b`: `pos := @Int.NonNeg.mk (a-b-1) : b < a`; rewrite `a ↦ b` along `h`
///   over motive `λt. b < t`, yielding `b < b`, then `Int.lt_irrefl b`.
///
/// Returns `None` (fail-closed) when the literals are equal (a TRUE equality is
/// not a contradiction) or the gap witness does not fit `u64`.
fn refute_false_eq(a: i128, b: i128, h: Expr) -> Option<Expr> {
    if a == b {
        return None;
    }
    let ak = int_literal_to_kernel(a)?;
    let bk = int_literal_to_kernel(b)?;
    if a < b {
        // pos : Int.lt a b ; motive λt. Int.lt a t ; rewrite b↦a via Eq.symm h.
        let k = u64::try_from(b.checked_sub(a)?.checked_sub(1)?).ok()?;
        let pos = nonneg_mk(k);
        let motive = Expr::lam(
            BinderInfo::Default,
            int_ty(),
            const_app("Int.lt", [ak.clone(), Expr::bvar(0)]),
        );
        let symm = eq_symm_int(ak.clone(), bk.clone(), h);
        let lt_aa = eq_subst_int(motive, bk, ak.clone(), symm, pos);
        Some(Expr::app(const_app("Int.lt_irrefl", [ak]), lt_aa))
    } else {
        // pos : Int.lt b a ; motive λt. Int.lt b t ; rewrite a↦b via h.
        let k = u64::try_from(a.checked_sub(b)?.checked_sub(1)?).ok()?;
        let pos = nonneg_mk(k);
        let motive = Expr::lam(
            BinderInfo::Default,
            int_ty(),
            const_app("Int.lt", [bk.clone(), Expr::bvar(0)]),
        );
        let lt_bb = eq_subst_int(motive, ak.clone(), bk.clone(), h, pos);
        Some(Expr::app(const_app("Int.lt_irrefl", [bk]), lt_bb))
    }
}

/// A single supported atom interpreted as a constant bound on one Int variable.
struct VarBound {
    /// `true`: `x ≤/< value` (upper bound); `false`: `value ≤/< x` (lower).
    is_upper: bool,
    /// `true` for a strict (`<`) bound, `false` for non-strict (`≤`).
    strict: bool,
    /// The literal constant bound.
    value: i128,
    /// The variable's name (so two bounds are only combined on the SAME var).
    var: String,
    /// The hypothesis term (an fvar) inhabiting this atom's proposition.
    hyp: Expr,
}

/// The variable name if `f` is an `Int`-sorted variable, else `None`.
fn int_var_name(f: &Formula) -> Option<String> {
    match f {
        Formula::Var(name, Sort::Int) => Some(name.clone()),
        Formula::SymVar(sym, Sort::Int) => Some(sym.as_str().to_string()),
        _ => None,
    }
}

/// Interpret a normalized atom (`x < c`, `c ≤ x`, …) as a constant bound on a
/// single Int variable, or `None` if it is not `variable`-vs-`literal`.
fn atom_var_bound(atom: &Atom<'_>, hyp: Expr) -> Option<VarBound> {
    let (a, b, strict) = match atom {
        Atom::Lt(a, b) => (*a, *b, true),
        Atom::Le(a, b) => (*a, *b, false),
    };
    match (int_var_name(a), int_literal_value(b), int_literal_value(a), int_var_name(b)) {
        // `x ?<= c` — upper bound.
        (Some(var), Some(value), _, _) => {
            Some(VarBound { is_upper: true, strict, value, var, hyp })
        }
        // `c ?<= x` — lower bound.
        (_, _, Some(value), Some(var)) => {
            Some(VarBound { is_upper: false, strict, value, var, hyp })
        }
        _ => None,
    }
}

/// Refute a single-variable interval contradiction: a lower bound `L ?≤ x` and an
/// upper bound `x ?≤ U` on the SAME variable whose constants conflict. Chains
/// them through the variable with the matching transitivity lemma to obtain the
/// closed false `L ≤ U` / `L < U`, then refutes that constant via
/// [`refute_false_atom`]. Returns the first refutable pair, or `None`.
fn single_var_interval_refutation(atoms: &[Atom<'_>], hyps: &[Hyp]) -> Option<Expr> {
    let bounds: Vec<VarBound> = atoms
        .iter()
        .zip(hyps)
        .filter_map(|(atom, hyp)| atom_var_bound(atom, Expr::fvar(hyp.fvar)))
        .collect();
    for lower in bounds.iter().filter(|b| !b.is_upper) {
        for upper in bounds.iter().filter(|b| b.is_upper) {
            if lower.var != upper.var {
                continue;
            }
            if let Some(term) = build_interval_refutation(lower, upper) {
                return Some(term);
            }
        }
    }
    None
}

/// Build a `False` term from conflicting `lower : L ?≤ x` and `upper : x ?≤ U`.
/// The result relation (`L ≤ U` if both non-strict, else `L < U`) is closed and
/// — when the constants conflict — false, so [`refute_false_atom`] closes it.
fn build_interval_refutation(lower: &VarBound, upper: &VarBound) -> Option<Expr> {
    let x = Expr::const_(Name::from_string(&encoded_var_name(&lower.var)), vec![]);
    let l = int_literal_to_kernel(lower.value)?;
    let u = int_literal_to_kernel(upper.value)?;
    let args = [l, x, u, lower.hyp.clone(), upper.hyp.clone()];
    // a := L, b := x, c := U.
    let (derived, result_is_lt) = match (lower.strict, upper.strict) {
        // L ≤ x ≤ U  ⊢  L ≤ U
        (false, false) => (const_app("Int.le_trans", args), false),
        // L < x ≤ U  ⊢  L < U
        (true, false) => (const_app("Int.lt_of_lt_of_le", args), true),
        // L ≤ x < U  ⊢  L < U
        (false, true) => (const_app("Int.lt_of_le_of_lt", args), true),
        // L < x < U  ⊢  L < U
        (true, true) => (const_app("Int.lt_trans", args), true),
    };
    let atom = ClosedOrderAtom { a: lower.value, b: upper.value, is_lt: result_is_lt };
    // `refute_false_atom` returns `None` unless the constants actually conflict,
    // so a satisfiable interval is never falsely refuted (soundness guard).
    refute_false_atom(&atom, derived)
}

/// A canonical key identifying an order-atom endpoint (a variable or a literal),
/// so a transitive chain can match `… ≤ t` to `t ≤ …` structurally.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum ChainNode {
    Var(String),
    Lit(i128),
    /// A variable scaled by a positive literal: `x * c` (a guarded multiplication
    /// overflow term, e.g. `x * 2`). Distinct from `Var(x)` so the chain can carry
    /// both `x`'s bounds and the lifted `x*c` bounds.
    Scaled(String, i128),
    /// A sum of two variables: `a + b` (a guarded two-variable addition overflow
    /// term). Carries the lifted `a+b` bounds from each summand's guard.
    Sum(String, String),
    /// A difference of two variables: `a - b` (a guarded two-variable SUBTRACTION
    /// underflow/overflow term, e.g. `a - b` under a dominating guard `a > b` /
    /// `a >= b`). Carries the lifted `a-b` bounds derived from the guard (`b ≤ a ⟹
    /// 0 ≤ a-b`) and from `a`'s upper bound with `0 ≤ b` (`a-b ≤ a`).
    Diff(String, String),
}

/// One directed order edge `from R to` (`from ≤ to` or `from < to`) carrying its
/// hypothesis proof term — the building block of a transitive refutation chain.
#[derive(Clone)]
struct OrderEdge {
    from: ChainNode,
    to: ChainNode,
    from_expr: Expr,
    to_expr: Expr,
    strict: bool,
    hyp: Expr,
}

/// The `ChainNode` of a supported order term (`Int` variable or literal).
fn chain_node(f: &Formula) -> Option<ChainNode> {
    match f {
        Formula::Var(name, Sort::Int) => Some(ChainNode::Var(name.clone())),
        Formula::SymVar(sym, Sort::Int) => Some(ChainNode::Var(sym.as_str().to_string())),
        Formula::Int(n) => Some(ChainNode::Lit(*n)),
        Formula::UInt(n) if *n <= i128::MAX as u128 => Some(ChainNode::Lit(*n as i128)),
        // `x * c` — a positive-scaled variable (guarded multiplication overflow).
        Formula::Mul(a, b) => {
            let (c, var) = linear_mul_operands(a, b)?;
            if c <= 0 {
                return None;
            }
            Some(ChainNode::Scaled(int_var_name(var)?, c))
        }
        // `a + (-x)` is the MIR lowering of the difference `a - x`: route it to a
        // Diff node (not Sum) so guarded-subtraction obligations whose `a-b` lowers
        // through `Add(_, Neg(_))` still get the subtractive lifts.
        Formula::Add(a, b) => match b.as_ref() {
            Formula::Neg(x) => Some(ChainNode::Diff(int_var_name(a)?, int_var_name(x)?)),
            _ => Some(ChainNode::Sum(int_var_name(a)?, int_var_name(b)?)),
        },
        // `a - b` of two variables (guarded two-variable subtraction under/overflow).
        Formula::Sub(a, b) => Some(ChainNode::Diff(int_var_name(a)?, int_var_name(b)?)),
        _ => None,
    }
}

/// Refute a multi-variable transitive-chain contradiction: order atoms that chain
/// a literal `L` up to a literal `U` (`L R … R U`) whose endpoints conflict
/// (`L > U`, or `L ≥ U` if any link is strict). Generalizes the single-variable
/// interval (a 2-link chain `L ≤ x ≤ U`) to arbitrary length — e.g. a constant
/// index on a guarded symbolic-length slice (`5 < len ≤ _5 ≤ _4 ≤ 3`). Each link
/// is composed with the matching transitivity lemma into the closed false
/// `L R U`, then closed by [`refute_false_atom`]. Fail-closed: only a genuine
/// conflict is refuted, and the kernel re-check is the backstop.
fn transitive_chain_refutation(atoms: &[Atom<'_>], hyps: &[Hyp]) -> Option<Expr> {
    let edges: Vec<OrderEdge> = atoms
        .iter()
        .zip(hyps)
        .flat_map(|(atom, hyp)| {
            let (a, b, strict) = match atom {
                Atom::Lt(a, b) => (*a, *b, true),
                Atom::Le(a, b) => (*a, *b, false),
            };
            build_order_edges(a, b, strict, Expr::fvar(hyp.fvar))
        })
        .collect();
    refute_via_chain_edges(&edges)
}

/// Lift the guard bounds in an edge set onto the scaled (`x*c`) nodes that
/// appear, via `Int.mul_le_mul_of_nonneg_right` — `x ≤ B ⟹ x*c ≤ B*c` and
/// `L ≤ x ⟹ L*c ≤ x*c` for `c > 0`. This is the multiplicative analogue of the
/// additive linear shift, and is what lets a guarded multiplication
/// (`if x<100 { x*2 }`: violation `Or([x*2<0, x*2>255])`) close: `x≤99 ⟹ x*2≤198`
/// contradicts `x*2>255`, and `0≤x ⟹ 0≤x*2` contradicts `x*2<0`.
fn augment_with_multiplicative_lifts(edges: &[OrderEdge]) -> Vec<OrderEdge> {
    let mut scaled: BTreeSet<(String, i128)> = BTreeSet::new();
    for edge in edges {
        for node in [&edge.from, &edge.to] {
            if let ChainNode::Scaled(v, c) = node {
                scaled.insert((v.clone(), *c));
            }
        }
    }
    if scaled.is_empty() {
        return edges.to_vec();
    }
    let mut out = edges.to_vec();
    for edge in edges {
        // Only NON-STRICT bounds lift cleanly (`Int.mul_le_mul_of_nonneg_right`);
        // a strict guard already carries its integer-tightened `≤` form alongside.
        if edge.strict {
            continue;
        }
        match (&edge.from, &edge.to) {
            // upper bound `x ≤ B`  ⟹  `x*c ≤ B*c`
            (ChainNode::Var(v), ChainNode::Lit(b)) => {
                for (_, c) in scaled.iter().filter(|(sv, _)| sv == v) {
                    if let Some(lift) = mul_lift(v, *b, *c, true, &edge.hyp) {
                        out.push(lift);
                    }
                }
            }
            // lower bound `L ≤ x`  ⟹  `L*c ≤ x*c`
            (ChainNode::Lit(l), ChainNode::Var(v)) => {
                for (_, c) in scaled.iter().filter(|(sv, _)| sv == v) {
                    if let Some(lift) = mul_lift(v, *l, *c, false, &edge.hyp) {
                        out.push(lift);
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// Build the lifted edge for a guard bound on `x` scaled by `c > 0`.
/// `upper`: `x ≤ B` → edge `x*c → B*c` (`mul_le_mul_of_nonneg_right x B c`);
/// else `L ≤ x` → edge `L*c → x*c` (`mul_le_mul_of_nonneg_right L x c`). The
/// non-negativity witness is `@Int.NonNeg.mk c` (`≡ Int.le 0 c`).
fn mul_lift(v: &str, bound: i128, c: i128, upper: bool, guard_hyp: &Expr) -> Option<OrderEdge> {
    let product = bound.checked_mul(c)?;
    let x = Expr::const_(Name::from_string(&encoded_var_name(v)), vec![]);
    let ck = int_literal_to_kernel(c)?;
    let bound_k = int_literal_to_kernel(bound)?;
    let nonneg = nonneg_mk(u64::try_from(c).ok()?);
    let xc = hmul_int(x.clone(), ck.clone());
    let bound_c = int_literal_to_kernel(product)?;
    if upper {
        // mul_le_mul_of_nonneg_right x B c (h:x≤B) (0≤c) : x*c ≤ B*c
        let hyp = const_app(
            "Int.mul_le_mul_of_nonneg_right",
            [x, bound_k, ck, guard_hyp.clone(), nonneg],
        );
        Some(OrderEdge {
            from: ChainNode::Scaled(v.to_string(), c),
            to: ChainNode::Lit(product),
            from_expr: xc,
            to_expr: bound_c,
            strict: false,
            hyp,
        })
    } else {
        // mul_le_mul_of_nonneg_right L x c (h:L≤x) (0≤c) : L*c ≤ x*c
        let hyp = const_app(
            "Int.mul_le_mul_of_nonneg_right",
            [bound_k, x, ck, guard_hyp.clone(), nonneg],
        );
        Some(OrderEdge {
            from: ChainNode::Lit(product),
            to: ChainNode::Scaled(v.to_string(), c),
            from_expr: bound_c,
            to_expr: xc,
            strict: false,
            hyp,
        })
    }
}

/// `Int.add a b` (bare), the form the `Int.add_le_add_*` / `Int.le_trans` lemmas
/// produce and consume; def-eq to the `HAdd` form `term_to_kernel(Add)` emits.
fn int_add_expr(a: Expr, b: Expr) -> Expr {
    const_app("Int.add", [a, b])
}

/// A kernel const for an encoded Int variable.
fn chain_var_expr(v: &str) -> Expr {
    Expr::const_(Name::from_string(&encoded_var_name(v)), vec![])
}

/// Lift guard bounds onto the two-variable sum nodes (`a+b`) that appear, via
/// `Int.add_le_add_right`/`_left` + `Int.le_trans`: `a≤A ∧ b≤B ⟹ a+b ≤ A+B` and
/// `La≤a ∧ Lb≤b ⟹ La+Lb ≤ a+b`. This is what lets a guarded two-variable
/// addition (`if a<1000 && b<1000 { a+b }` (u32, Int overflow): violation
/// `Or([a+b<0, a+b>u32::MAX])`) close: `a≤999 ∧ b≤999 ⟹ a+b≤1998 < MAX`.
fn augment_with_additive_lifts(edges: &[OrderEdge]) -> Vec<OrderEdge> {
    let mut sums: BTreeSet<(String, String)> = BTreeSet::new();
    for edge in edges {
        for node in [&edge.from, &edge.to] {
            if let ChainNode::Sum(a, b) = node {
                sums.insert((a.clone(), b.clone()));
            }
        }
    }
    if sums.is_empty() {
        return edges.to_vec();
    }
    // Tightest non-strict bound per variable: min upper, max lower.
    let mut upper: std::collections::BTreeMap<String, (i128, Expr)> = Default::default();
    let mut lower: std::collections::BTreeMap<String, (i128, Expr)> = Default::default();
    for edge in edges {
        if edge.strict {
            continue;
        }
        match (&edge.from, &edge.to) {
            (ChainNode::Var(v), ChainNode::Lit(b)) => {
                let e = upper.entry(v.clone()).or_insert((*b, edge.hyp.clone()));
                if *b < e.0 {
                    *e = (*b, edge.hyp.clone());
                }
            }
            (ChainNode::Lit(l), ChainNode::Var(v)) => {
                let e = lower.entry(v.clone()).or_insert((*l, edge.hyp.clone()));
                if *l > e.0 {
                    *e = (*l, edge.hyp.clone());
                }
            }
            _ => {}
        }
    }
    let mut out = edges.to_vec();
    for (a, b) in &sums {
        if let (Some((ua, ha)), Some((ub, hb))) = (upper.get(a), upper.get(b)) {
            if let Some(e) = add_lift(a, b, *ua, *ub, ha, hb, true) {
                out.push(e);
            }
        }
        if let (Some((la, ha)), Some((lb, hb))) = (lower.get(a), lower.get(b)) {
            if let Some(e) = add_lift(a, b, *la, *lb, ha, hb, false) {
                out.push(e);
            }
        }
    }
    out
}

/// Build the lifted edge for two guard bounds on the summands of `a+b`.
/// `upper`: `a≤A, b≤B` → edge `a+b → A+B`; else `La≤a, Lb≤b` → edge `La+Lb → a+b`.
fn add_lift(
    a: &str,
    b: &str,
    ba: i128,
    bb: i128,
    ha: &Expr,
    hb: &Expr,
    upper: bool,
    // `ha : a≤A`/`La≤a`, `hb : b≤B`/`Lb≤b`.
) -> Option<OrderEdge> {
    let sum_bound = ba.checked_add(bb)?;
    let ax = chain_var_expr(a);
    let bx = chain_var_expr(b);
    let bak = int_literal_to_kernel(ba)?;
    let bbk = int_literal_to_kernel(bb)?;
    let ab = || int_add_expr(ax.clone(), bx.clone());
    let sum_e = int_literal_to_kernel(sum_bound)?;
    let node = ChainNode::Sum(a.to_string(), b.to_string());
    if upper {
        // step1: add_le_add_right a A ha b : a+b ≤ A+b
        let step1 =
            const_app("Int.add_le_add_right", [ax.clone(), bak.clone(), ha.clone(), bx.clone()]);
        // step2: add_le_add_left b B hb A : A+b ≤ A+B
        let step2 =
            const_app("Int.add_le_add_left", [bx.clone(), bbk.clone(), hb.clone(), bak.clone()]);
        // le_trans (a+b) (A+b) (A+B) step1 step2
        let mid = int_add_expr(bak.clone(), bx.clone());
        let top = int_add_expr(bak.clone(), bbk.clone());
        let hyp = const_app("Int.le_trans", [ab(), mid, top, step1, step2]);
        Some(OrderEdge {
            from: node,
            to: ChainNode::Lit(sum_bound),
            from_expr: ab(),
            to_expr: sum_e,
            strict: false,
            hyp,
        })
    } else {
        // step1: add_le_add_right La a ha Lb : La+Lb ≤ a+Lb
        let step1 =
            const_app("Int.add_le_add_right", [bak.clone(), ax.clone(), ha.clone(), bbk.clone()]);
        // step2: add_le_add_left Lb b hb a : a+Lb ≤ a+b
        let step2 =
            const_app("Int.add_le_add_left", [bbk.clone(), bx.clone(), hb.clone(), ax.clone()]);
        // le_trans (La+Lb) (a+Lb) (a+b) step1 step2
        let bot = int_add_expr(bak.clone(), bbk.clone());
        let mid = int_add_expr(ax.clone(), bbk.clone());
        let hyp = const_app("Int.le_trans", [bot, mid, ab(), step1, step2]);
        Some(OrderEdge {
            from: ChainNode::Lit(sum_bound),
            to: node,
            from_expr: sum_e,
            to_expr: ab(),
            strict: false,
            hyp,
        })
    }
}

/// `Int.neg a` (bare), used to build the `a - b ≡ Int.add a (Int.neg b)` rewrites.
fn int_neg_expr(a: Expr) -> Expr {
    const_app("Int.neg", [a])
}

/// `Int.zero` — the reducible abbreviation `Int.ofNat Nat.zero`, def-eq to the
/// `Int.ofNat 0` form `int_literal_to_kernel(0)` emits. The `Int.add_zero` /
/// `Int.add_neg_self` / `Int.neg_add_self` algebra lemmas are stated over it.
fn int_zero_expr() -> Expr {
    Expr::const_(Name::from_string("Int.zero"), vec![])
}

/// LOWER bound on a two-variable difference: from the guard `h : Int.le b a`
/// (`b ≤ a`) build a proof of `Int.le (Int.ofNat 0) (Int.sub a b)` (`0 ≤ a-b`).
///
/// `Int.add_le_add_right b a h (Int.neg b) : Int.le (b + -b) (a + -b)`, whose
/// right operand `a + -b` is *definitionally* `Int.sub a b` (`Int.sub` unfolds to
/// `Int.add _ (Int.neg _)`). Rewriting the left operand `b + -b` to `Int.zero`
/// along `Int.add_neg_self b` via `Eq.subst` yields `Int.le Int.zero (Int.sub a b)`,
/// which is `Int.le (Int.ofNat 0) (Int.sub a b)` up to the `Int.zero ≡ ofNat 0`
/// reducible def. KEY def-eq: `Int.le x y := Int.NonNeg (Int.sub y x)`, so the
/// guard's own witness `NonNeg (a-b)` is exactly the non-negativity content.
fn diff_lower_proof(a: &str, b: &str, guard_hyp: &Expr) -> Expr {
    let ax = chain_var_expr(a);
    let bx = chain_var_expr(b);
    let neg_b = int_neg_expr(bx.clone());
    let sub_ab = const_app("Int.sub", [ax.clone(), bx.clone()]);
    // step1 : Int.le (Int.add b (Int.neg b)) (Int.add a (Int.neg b))  [≡ Int.sub a b]
    let step1 =
        const_app("Int.add_le_add_right", [bx.clone(), ax, guard_hyp.clone(), neg_b.clone()]);
    let b_plus_negb = int_add_expr(bx.clone(), neg_b);
    // motive := λ t : Int => Int.le t (Int.sub a b)
    let motive =
        Expr::lam(BinderInfo::Default, int_ty(), const_app("Int.le", [Expr::bvar(0), sub_ab]));
    // Int.add_neg_self b : Eq (Int.add b (Int.neg b)) Int.zero
    let eq_bnegb = const_app("Int.add_neg_self", [bx]);
    // Eq.subst rewrites the left operand (b + -b) ↦ Int.zero ≡ ofNat 0.
    eq_subst_int(motive, b_plus_negb, int_zero_expr(), eq_bnegb, step1)
}

/// UPPER bound on a two-variable difference: from `hb : Int.le (Int.ofNat 0) b`
/// (`0 ≤ b`) build a proof of `Int.le (Int.sub a b) a` (`a-b ≤ a`). The chain then
/// composes this with `a`'s own upper bound (`a ≤ A`) by transitivity, so the
/// overflow disjunct `a-b > A` closes without needing a `Diff → Lit` edge.
///
/// Two `Int.add_le_add_left` steps with `Eq.subst` rewrites:
///   1. `add_le_add_left 0 b hb (-b) : Int.le (-b + 0) (-b + b)`, rewrite the
///      operands to `Int.le (-b) Int.zero` (`Int.add_zero (-b)`, `Int.neg_add_self b`);
///   2. `add_le_add_left (-b) 0 _ a : Int.le (a + -b) (a + 0)`, whose left operand
///      `a + -b ≡ Int.sub a b`; rewrite the right operand `a + 0 ↦ a`
///      (`Int.add_zero a`), yielding `Int.le (Int.sub a b) a`.
fn diff_upper_proof(a: &str, b: &str, nonneg_b_hyp: &Expr) -> Expr {
    let ax = chain_var_expr(a);
    let bx = chain_var_expr(b);
    let neg_b = int_neg_expr(bx.clone());
    let zero = int_zero_expr();
    let ofnat0 = int_literal_to_kernel(0).expect("ofNat 0");
    // s1 : Int.le (Int.add (Int.neg b) (Int.ofNat 0)) (Int.add (Int.neg b) b)
    let s1 =
        const_app("Int.add_le_add_left", [ofnat0, bx.clone(), nonneg_b_hyp.clone(), neg_b.clone()]);
    // rewrite left operand (-b + 0) ↦ -b via Int.add_zero (-b).
    let negb_plus0 = int_add_expr(neg_b.clone(), int_zero_expr());
    let negb_plus_b = int_add_expr(neg_b.clone(), bx.clone());
    let motive1 = Expr::lam(
        BinderInfo::Default,
        int_ty(),
        const_app("Int.le", [Expr::bvar(0), negb_plus_b.clone()]),
    );
    let eq_negb0 = const_app("Int.add_zero", [neg_b.clone()]);
    let s2 = eq_subst_int(motive1, negb_plus0, neg_b.clone(), eq_negb0, s1);
    // rewrite right operand (-b + b) ↦ Int.zero via Int.neg_add_self b.
    let motive2 = Expr::lam(
        BinderInfo::Default,
        int_ty(),
        const_app("Int.le", [neg_b.clone(), Expr::bvar(0)]),
    );
    let eq_negbb = const_app("Int.neg_add_self", [bx.clone()]);
    // s3 : Int.le (Int.neg b) Int.zero  (≡ Int.le (-b) (ofNat 0))
    let s3 = eq_subst_int(motive2, negb_plus_b, zero.clone(), eq_negbb, s2);
    // s4 : Int.le (Int.add a (Int.neg b)) (Int.add a (Int.ofNat 0))
    //   left operand a + -b ≡ Int.sub a b.
    let s4 = const_app("Int.add_le_add_left", [neg_b.clone(), zero.clone(), s3, ax.clone()]);
    let sub_ab = const_app("Int.sub", [ax.clone(), bx]);
    let a_plus_zero = int_add_expr(ax.clone(), zero);
    // rewrite right operand (a + Int.zero) ↦ a via Int.add_zero a.
    let motive3 =
        Expr::lam(BinderInfo::Default, int_ty(), const_app("Int.le", [sub_ab, Expr::bvar(0)]));
    let eq_a0 = const_app("Int.add_zero", [ax.clone()]);
    eq_subst_int(motive3, a_plus_zero, ax, eq_a0, s4)
}

/// Lift guard bounds onto the two-variable difference nodes (`a-b`) that appear.
/// For each `Diff(a,b)`:
///
/// * LOWER (`0 ≤ a-b`, edge `Lit(0) → Diff(a,b)`): from a guard `b ≤ a` — a
///   non-strict context edge `Var(b) → Var(a)`, or a strict one strengthened by
///   `Int.le_of_lt`. Closes the underflow disjunct `a-b < 0`.
/// * UPPER (`a-b ≤ a`, edge `Diff(a,b) → Var(a)`): from `0 ≤ b` — a non-strict
///   context edge `Lit(0) → Var(b)`. Chains with `a`'s own upper bound `a ≤ A`
///   (already an edge `Var(a) → Lit(A)`) to close the overflow disjunct `a-b > A`.
///
/// SOUNDNESS: every lifted edge is a kernel-checked proof term re-verified by the
/// clean kernel; an unguarded `a-b` keeps no `b ≤ a` edge, so its underflow
/// disjunct stays unrefuted and the whole `Or.rec` fails closed (no certificate).
fn augment_with_subtractive_lifts(edges: &[OrderEdge]) -> Vec<OrderEdge> {
    let mut diffs: BTreeSet<(String, String)> = BTreeSet::new();
    for edge in edges {
        for node in [&edge.from, &edge.to] {
            if let ChainNode::Diff(a, b) = node {
                diffs.insert((a.clone(), b.clone()));
            }
        }
    }
    if diffs.is_empty() {
        return edges.to_vec();
    }
    let mut out = edges.to_vec();
    for (a, b) in &diffs {
        // LOWER: find a guard `b ≤ a` / `b < a` (edge Var(b) → Var(a)).
        if let Some(guard) = edges.iter().find_map(|e| match (&e.from, &e.to) {
            (ChainNode::Var(vb), ChainNode::Var(va)) if vb == b && va == a => {
                if e.strict {
                    // b < a  ⟹  b ≤ a  via Int.le_of_lt b a hyp.
                    Some(const_app(
                        "Int.le_of_lt",
                        [chain_var_expr(b), chain_var_expr(a), e.hyp.clone()],
                    ))
                } else {
                    Some(e.hyp.clone())
                }
            }
            _ => None,
        }) {
            out.push(OrderEdge {
                from: ChainNode::Lit(0),
                to: ChainNode::Diff(a.clone(), b.clone()),
                from_expr: int_literal_to_kernel(0).expect("ofNat 0"),
                to_expr: const_app("Int.sub", [chain_var_expr(a), chain_var_expr(b)]),
                strict: false,
                hyp: diff_lower_proof(a, b, &guard),
            });
        }
        // UPPER: find `0 ≤ b` (a non-strict edge Lit(0) → Var(b)).
        if let Some(nonneg_b) = edges.iter().find_map(|e| match (&e.from, &e.to) {
            (ChainNode::Lit(0), ChainNode::Var(vb)) if vb == b && !e.strict => Some(e.hyp.clone()),
            _ => None,
        }) {
            out.push(OrderEdge {
                from: ChainNode::Diff(a.clone(), b.clone()),
                to: ChainNode::Var(a.clone()),
                from_expr: const_app("Int.sub", [chain_var_expr(a), chain_var_expr(b)]),
                to_expr: chain_var_expr(a),
                strict: false,
                hyp: diff_upper_proof(a, b, &nonneg_b),
            });
        }
    }
    out
}

/// Search a set of order edges for a transitive chain `L R … R U` between
/// conflicting literals and return its kernel `False` refutation, or `None`.
fn refute_via_chain_edges(edges: &[OrderEdge]) -> Option<Expr> {
    let edges = augment_with_multiplicative_lifts(edges);
    let edges = augment_with_additive_lifts(&edges);
    let edges = augment_with_subtractive_lifts(&edges);
    let edges = edges.as_slice();
    // Bound the DFS: a handful of order atoms is typical, and the `visited` set
    // already caps each path at the node count, but cap the edge set so a
    // pathological machine-generated VC cannot drive a super-polynomial search.
    // Fail-closed: an over-large system simply isn't chain-refuted here.
    if edges.len() > 48 {
        return None;
    }
    for start in edges.iter().filter(|e| matches!(e.from, ChainNode::Lit(_))) {
        let ChainNode::Lit(l) = start.from else { continue };
        // `visited` tracks only variable nodes; the head literal is terminal.
        let mut visited = Vec::new();
        if let Some(term) = extend_chain(start, l, edges, &mut visited) {
            return Some(term);
        }
    }
    None
}

/// `x + δ` decomposition of a linear term over one Int variable: `Add(x,c)` /
/// `Add(c,x)` → `(x, c)`; `Sub(x,c)` → `(x, -c)`. `None` for anything else.
fn linear_var_offset(f: &Formula) -> Option<(String, i128)> {
    match f {
        Formula::Add(a, b) => {
            if let (Some(v), Some(c)) = (int_var_name(a), int_literal_value(b)) {
                return Some((v, c));
            }
            if let (Some(c), Some(v)) = (int_literal_value(a), int_var_name(b)) {
                return Some((v, c));
            }
            None
        }
        Formula::Sub(a, b) => Some((int_var_name(a)?, int_literal_value(b)?.checked_neg()?)),
        _ => None,
    }
}

/// `@Int.<lt|le>_of_add_<lt|le>_add_right a b δ h : <R> a b`, given
/// `h : <R> (a+δ) (b+δ)`. The cancellation lemma that turns a bound on a
/// shifted term `x ± c` back into a bound on `x` (its kernel `+` def-eq-reduces
/// through `Int.sub a b ≡ Int.add a (Int.neg b)` and native literal arithmetic).
fn shift_hyp(strict: bool, a: &Expr, b: &Expr, delta: i128, h: Expr) -> Option<Expr> {
    // `Int.<R>_of_add_<R>_add_right a δ c : <R> (a+δ) (c+δ) → <R> a c` — the
    // ADDEND `δ` is the MIDDLE argument; `a`/`c` are the result operands.
    let lemma = if strict { "Int.lt_of_add_lt_add_right" } else { "Int.le_of_add_le_add_right" };
    let d = int_literal_to_kernel(delta)?;
    Some(const_app(lemma, [a.clone(), d, b.clone(), h]))
}

/// Build a directed order edge for `a R b` (`strict` = `<`), shifting a linear
/// `x ± c` endpoint back onto `x` via [`shift_hyp`] so the chain ranges over bare
/// variables. Plain `variable`/`literal` endpoints pass through unchanged.
fn build_order_edge(a: &Formula, b: &Formula, strict: bool, hyp: Expr) -> Option<OrderEdge> {
    // Plain variable/literal (or two-variable `Sub`) on both sides.
    // `linear_term_to_kernel` handles `Int.sub a b` (for a `Diff` endpoint) and
    // otherwise falls back to `term_to_kernel`, so plain var/literal edges are
    // unchanged.
    if let (Some(from), Some(to)) = (chain_node(a), chain_node(b)) {
        return Some(OrderEdge {
            from,
            to,
            from_expr: linear_term_to_kernel(a)?,
            to_expr: linear_term_to_kernel(b)?,
            strict,
            hyp,
        });
    }
    let var_expr = |v: &str| Expr::const_(Name::from_string(&encoded_var_name(v)), vec![]);
    // `(x+δ) R k`  →  `x R (k-δ)`.
    if let (Some((v, delta)), Some(k)) = (linear_var_offset(a), int_literal_value(b)) {
        let kk = k.checked_sub(delta)?;
        let (x, kk_e) = (var_expr(&v), int_literal_to_kernel(kk)?);
        let shifted = shift_hyp(strict, &x, &kk_e, delta, hyp)?;
        return Some(OrderEdge {
            from: ChainNode::Var(v),
            to: ChainNode::Lit(kk),
            from_expr: x,
            to_expr: kk_e,
            strict,
            hyp: shifted,
        });
    }
    // `k R (x+δ)`  →  `(k-δ) R x`.
    if let (Some(k), Some((v, delta))) = (int_literal_value(a), linear_var_offset(b)) {
        let kk = k.checked_sub(delta)?;
        let (x, kk_e) = (var_expr(&v), int_literal_to_kernel(kk)?);
        let shifted = shift_hyp(strict, &kk_e, &x, delta, hyp)?;
        return Some(OrderEdge {
            from: ChainNode::Lit(kk),
            to: ChainNode::Var(v),
            from_expr: kk_e,
            to_expr: x,
            strict,
            hyp: shifted,
        });
    }
    None
}

/// Build the order edge(s) for `a R b`, INCLUDING the integer-tightness
/// strengthening of a strict bound against a literal: over `Int`, `x < c` also
/// gives `x ≤ c-1` and `c < x` also gives `c+1 ≤ x`. Without it a chain like
/// `255 < x ∧ x < 256` (a guarded `x as u8` range check) computes the true
/// `255 < 256` instead of the contradiction `255 < 255`. Both forms are kept so
/// the DFS can pick whichever closes.
fn build_order_edges(a: &Formula, b: &Formula, strict: bool, hyp: Expr) -> Vec<OrderEdge> {
    let Some(edge) = build_order_edge(a, b, strict, hyp) else {
        return Vec::new();
    };
    let mut out = vec![edge.clone()];
    if edge.strict {
        match (&edge.from, &edge.to) {
            // `x < c`  ⟹  `x ≤ c-1`  via `Int.le_of_add_le_add_right x 1 (c-1) h`.
            (ChainNode::Var(_), ChainNode::Lit(c)) => {
                if let (Some(cm1), Some(cm1_e), Some(one)) = (
                    c.checked_sub(1),
                    c.checked_sub(1).and_then(int_literal_to_kernel),
                    int_literal_to_kernel(1),
                ) {
                    let strengthened = const_app(
                        "Int.le_of_add_le_add_right",
                        [edge.from_expr.clone(), one, cm1_e.clone(), edge.hyp.clone()],
                    );
                    out.push(OrderEdge {
                        from: edge.from.clone(),
                        to: ChainNode::Lit(cm1),
                        from_expr: edge.from_expr.clone(),
                        to_expr: cm1_e,
                        strict: false,
                        hyp: strengthened,
                    });
                }
            }
            // `c < x`  ⟹  `c+1 ≤ x`, which is `Int.lt c x` itself (def-eq).
            (ChainNode::Lit(c), ChainNode::Var(_)) => {
                if let (Some(cp1), Some(cp1_e)) =
                    (c.checked_add(1), c.checked_add(1).and_then(int_literal_to_kernel))
                {
                    out.push(OrderEdge {
                        from: ChainNode::Lit(cp1),
                        to: edge.to.clone(),
                        from_expr: cp1_e,
                        to_expr: edge.to_expr.clone(),
                        strict: false,
                        hyp: edge.hyp.clone(),
                    });
                }
            }
            _ => {}
        }
    }
    out
}

/// DFS continuation of a transitive chain whose head literal is `l` and whose
/// accumulated proof is `acc : Int.(le|lt) l <current node>`. When the current
/// node is a literal that conflicts with `l`, close it; otherwise extend by any
/// unvisited outgoing edge.
fn extend_chain(
    acc_edge: &OrderEdge,
    l: i128,
    edges: &[OrderEdge],
    visited: &mut Vec<ChainNode>,
) -> Option<Expr> {
    // Re-fold the chain from scratch each time is avoided by threading the proof:
    // `extend_from` carries the partial proof + relation forward.
    fn extend_from(
        l: i128,
        l_expr: &Expr,
        cur: &ChainNode,
        cur_expr: &Expr,
        acc_proof: Expr,
        acc_strict: bool,
        edges: &[OrderEdge],
        visited: &mut Vec<ChainNode>,
    ) -> Option<Expr> {
        // If the current node is a conflicting literal, close the chain. This
        // fires the FIRST time we reach `cur` (including the head literal `l`,
        // reached via a closing edge `… → l`), before `cur` is marked.
        if let ChainNode::Lit(u) = cur {
            let atom = ClosedOrderAtom { a: l, b: *u, is_lt: acc_strict };
            if atom.is_false() {
                if let Some(term) = refute_false_atom(&atom, acc_proof.clone()) {
                    return Some(term);
                }
            }
        }
        // Mark `cur` on the current path (ALL nodes), so a self-loop `n → n` or a
        // cycle is never re-entered. The head literal `l` is NOT pre-seeded, so a
        // closing edge into it is reached exactly once (its close check above).
        visited.push(cur.clone());
        for idx in 0..edges.len() {
            let edge = &edges[idx];
            if &edge.from != cur || visited.contains(&edge.to) {
                continue;
            }
            let next_strict = acc_strict || edge.strict;
            // Combine `acc : l R_acc cur` with `edge : cur R_edge next` → `l R' next`.
            let combined = chain_step(
                acc_strict,
                edge.strict,
                l_expr,
                cur_expr,
                &edge.to_expr,
                &acc_proof,
                &edge.hyp,
            );
            if let Some(term) = extend_from(
                l,
                l_expr,
                &edge.to,
                &edge.to_expr,
                combined,
                next_strict,
                edges,
                visited,
            ) {
                return Some(term);
            }
        }
        visited.pop();
        None
    }
    extend_from(
        l,
        &acc_edge.from_expr,
        &acc_edge.to,
        &acc_edge.to_expr,
        acc_edge.hyp.clone(),
        acc_edge.strict,
        edges,
        visited,
    )
}

/// Compose `h1 : a R1 b` and `h2 : b R2 c` into `a R' c` via the matching Int
/// transitivity lemma (`R'` is strict iff either input is).
fn chain_step(s1: bool, s2: bool, a: &Expr, b: &Expr, c: &Expr, h1: &Expr, h2: &Expr) -> Expr {
    let args = [a.clone(), b.clone(), c.clone(), h1.clone(), h2.clone()];
    match (s1, s2) {
        (false, false) => const_app("Int.le_trans", args),
        (true, false) => const_app("Int.lt_of_lt_of_le", args),
        (false, true) => const_app("Int.lt_of_le_of_lt", args),
        (true, true) => const_app("Int.lt_trans", args),
    }
}

/// The kernel proposition for a non-empty disjunction of closed atoms, as a
/// right-nested binary `Or d1 (Or d2 (… dn))`.
fn closed_or_prop(disjuncts: &[ClosedOrderAtom]) -> Option<Expr> {
    match disjuncts {
        [] => None,
        [only] => closed_atom_prop(only),
        [first, rest @ ..] => {
            Some(const_app("Or", [closed_atom_prop(first)?, closed_or_prop(rest)?]))
        }
    }
}

/// SMT-LIB2 rendering of a disjunction of closed atoms (for the ay cross-check).
fn closed_or_smt(disjuncts: &[ClosedOrderAtom]) -> Option<String> {
    let parts: Option<Vec<String>> = disjuncts.iter().map(closed_atom_smt).collect();
    let parts = parts?;
    match parts.as_slice() {
        [] => None,
        [only] => Some(only.clone()),
        many => Some(format!("(or {})", many.join(" "))),
    }
}

/// Build a `False` term from a hypothesis `h : Or d1 (Or d2 …)` where EVERY
/// disjunct is a closed false atom, by right-nested `Or.rec` case-analysis.
/// `Or.rec` is a Prop-only eliminator (motive fixed to `Prop`), so it carries
/// no explicit universe argument; the motive is the constant `False`.
fn refute_closed_disjunction(disjuncts: &[ClosedOrderAtom], h_or: Expr) -> Option<Expr> {
    match disjuncts {
        [] => None,
        [only] => refute_false_atom(only, h_or),
        [first, rest @ ..] => {
            let d1 = closed_atom_prop(first)?;
            let rest_prop = closed_or_prop(rest)?;
            let or_ty = const_app("Or", [d1.clone(), rest_prop.clone()]);
            // motive := λ _ : Or d1 rest => False
            let motive = Expr::lam(BinderInfo::Default, or_ty, false_expr());
            // inl := λ h1 : d1 => <refute first using bvar 0>
            let inl = Expr::lam(
                BinderInfo::Default,
                d1.clone(),
                refute_false_atom(first, Expr::bvar(0))?,
            );
            // inr := λ hrest : rest => <refute rest using bvar 0>
            let inr = Expr::lam(
                BinderInfo::Default,
                rest_prop.clone(),
                refute_closed_disjunction(rest, Expr::bvar(0))?,
            );
            Some(const_app("Or.rec", [d1, rest_prop, motive, inl, inr, h_or]))
        }
    }
}

/// Certify a closed-constant arithmetic contradiction: a conjunct that is an
/// unsatisfiable closed order atom, or a disjunction of closed order atoms that
/// ALL evaluate to false. Builds a genuine kernel `False` proof, drives the ay
/// cross-check, re-checks with the clean kernel, and emits `CleanCic`. Returns
/// `None` (→ caller records `Trusted`/`Unknown`) for everything else, and in
/// particular for any satisfiable conjunct — so a real violation is never
/// refuted here (`is_false` is the structural soundness guard).
fn certify_closed_constant_contradiction(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let (hyps, term) = closed_constant_refutation(conjuncts)?;
    finish_closed_certificate(&hyps, &term, identity)
}

/// The single-hypothesis context + refutation term for the FIRST closed-constant
/// contradiction among `conjuncts`.
///
/// SINGLE-SOURCED PRODUCER/CONSUMER SEAM (Trust #540 R1 replay). This is a PURE
/// function of the obligation's own conjuncts, so
/// [`recheck_with_identity`]'s `closed_constant_accepts` branch can re-derive the
/// EXACT hypothesis context the producer certified against — from the obligation
/// alone, never from the certificate's (untrusted) serialized `context_bytes`.
/// Without this seam a closed-constant certificate could be minted but never
/// REPLAYED, and R1's caller-discharge obligations (`¬P[σ]` at a call site with
/// literal actuals, e.g. `¬(5 ≠ 0)`) are exactly closed-constant — so R1 would
/// have no replayable evidence at all.
///
/// SOUNDNESS: every hypothesis emitted here is one of the obligation's OWN
/// conjuncts (rendered into its kernel `Prop` by the same encoders the producer
/// uses), so a context rebuilt from it is obligation-grounded: a term that proves
/// `False` from it witnesses that the obligation is unsatisfiable. `is_false` /
/// `operands_fit` remain the structural guards — a *satisfiable* conjunct never
/// enters here, so a real violation is never refuted.
fn closed_constant_refutation(conjuncts: &[&Formula]) -> Option<(Vec<Hyp>, Expr)> {
    let fits = |n: i128| i64::try_from(n).is_ok();
    let one = |smt: String, prop: Expr, term: Expr| -> Option<(Vec<Hyp>, Expr)> {
        Some((
            vec![Hyp { smt, prop, fvar: FVarId::new(HYP_FVAR_BASE), name: "h_0".to_string() }],
            term,
        ))
    };
    for &conjunct in conjuncts {
        let fvar = FVarId::new(HYP_FVAR_BASE);
        // A lone closed false atom (e.g. a degenerate `2 < 0`).
        if let Some(atom) = closed_order_atom(conjunct) {
            if atom.is_false() && atom.operands_fit() {
                let prop = closed_atom_prop(&atom)?;
                let smt = closed_atom_smt(&atom)?;
                let term = refute_false_atom(&atom, Expr::fvar(fvar))?;
                return one(smt, prop, term);
            }
        }
        // A closed FALSE equality `c1 = c2` (distinct literals) — the divisor
        // conjunct of a constant-divisor division-overflow / div-by-zero check
        // (e.g. `2 = -1`, `2 = 0`), and R1's `¬P[σ]` caller discharge for a
        // literal actual (`5 = 0`). Refute `h : c1 = c2`.
        if let (Some(a), Some(b)) = closed_int_eq_operands(conjunct) {
            if a != b && fits(a) && fits(b) {
                let (ak, bk) = (int_literal_to_kernel(a)?, int_literal_to_kernel(b)?);
                let prop = eq_int(ak, bk);
                let smt = format!("(= {} {})", int_literal_to_smt(a)?, int_literal_to_smt(b)?);
                let term = refute_false_eq(a, b, Expr::fvar(fvar))?;
                return one(smt, prop, term);
            }
        }
        // A closed FALSE disequality `¬(c = c)` (reflexive) — `h : ¬(c = c)`
        // applied to `Eq.refl c` closes to `False`.
        if let Formula::Not(inner) = conjunct {
            if let (Some(a), Some(b)) = closed_int_eq_operands(inner) {
                if a == b && fits(a) {
                    let ak = int_literal_to_kernel(a)?;
                    let prop = not_prop(eq_int(ak.clone(), ak.clone()));
                    let smt = format!("(not (= {0} {0}))", int_literal_to_smt(a)?);
                    let term = Expr::app(Expr::fvar(fvar), eq_refl_int(ak));
                    return one(smt, prop, term);
                }
            }
        }
        // A disjunction of closed false atoms (the shift/cast range check).
        if let Formula::Or(disj) = conjunct {
            let atoms: Option<Vec<ClosedOrderAtom>> = disj.iter().map(closed_order_atom).collect();
            if let Some(atoms) = atoms {
                if !atoms.is_empty() && atoms.iter().all(|a| a.is_false() && a.operands_fit()) {
                    let prop = closed_or_prop(&atoms)?;
                    let smt = closed_or_smt(&atoms)?;
                    let term = refute_closed_disjunction(&atoms, Expr::fvar(fvar))?;
                    return one(smt, prop, term);
                }
            }
        }
    }
    None
}

/// Shared tail for the closed-constant path: confirm ay refutes the asserted
/// hypothesis, re-check the kernel term proves `False`, serialize, round-trip
/// re-check, and emit the lineage-bound `CleanCic`. Mirrors the tails of
/// [`certify_with_identity`] / [`certify_direct_disequality_contradiction`] but
/// over an empty free-variable set (the obligation is closed).
fn finish_closed_certificate(
    hyps: &[Hyp],
    term: &Expr,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    finish_certificate(hyps, term, &BTreeSet::new(), identity)
}

// ---------------------------------------------------------------------------
// Disjunctive contradictions over linear bounds (guarded arithmetic).
// ---------------------------------------------------------------------------

/// A kernel term for an order-atom operand, supporting `Int.sub` (the subtraction
/// a guarded overflow/underflow check carries, e.g. `x - 10`) in addition to the
/// fragment [`term_to_kernel`] handles. Bare `Int.sub` matches the shift lemma.
fn linear_term_to_kernel(f: &Formula) -> Option<Expr> {
    match f {
        Formula::Sub(a, b) => {
            Some(const_app("Int.sub", [linear_term_to_kernel(a)?, linear_term_to_kernel(b)?]))
        }
        _ => term_to_kernel(f),
    }
}

/// SMT rendering of an order-atom operand, supporting `Int.sub`.
fn linear_term_to_smt(f: &Formula) -> Option<String> {
    match f {
        Formula::Sub(a, b) => {
            Some(format!("(- {} {})", linear_term_to_smt(a)?, linear_term_to_smt(b)?))
        }
        _ => term_to_smt(f),
    }
}

/// Kernel proposition for a normalized order atom, supporting `Int.sub` operands.
fn linear_atom_prop(atom: &Atom<'_>) -> Option<Expr> {
    match atom {
        Atom::Lt(a, b) => Some(lt_int(linear_term_to_kernel(a)?, linear_term_to_kernel(b)?)),
        Atom::Le(a, b) => Some(le_int(linear_term_to_kernel(a)?, linear_term_to_kernel(b)?)),
    }
}

/// SMT rendering of a normalized order atom, supporting `Int.sub` operands.
fn linear_atom_smt(atom: &Atom<'_>) -> Option<String> {
    match atom {
        Atom::Lt(a, b) => {
            Some(format!("(< {} {})", linear_term_to_smt(a)?, linear_term_to_smt(b)?))
        }
        Atom::Le(a, b) => {
            Some(format!("(<= {} {})", linear_term_to_smt(a)?, linear_term_to_smt(b)?))
        }
    }
}

/// Collect the `Int` variable names appearing in a formula (through linear
/// `Add`/`Sub`/`Mul` terms), so the ay environment declares them.
fn collect_formula_int_vars(f: &Formula, out: &mut BTreeSet<String>) {
    match f {
        Formula::Var(name, Sort::Int) => {
            out.insert(name.clone());
        }
        Formula::SymVar(sym, Sort::Int) => {
            out.insert(sym.as_str().to_string());
        }
        Formula::Add(a, b) | Formula::Sub(a, b) | Formula::Mul(a, b) => {
            collect_formula_int_vars(a, out);
            collect_formula_int_vars(b, out);
        }
        _ => {}
    }
}

/// Right-nested binary `Or p1 (Or p2 (… pn))` over disjunct propositions.
fn build_or_prop(props: &[Expr]) -> Option<Expr> {
    match props {
        [] => None,
        [only] => Some(only.clone()),
        [first, rest @ ..] => Some(const_app("Or", [first.clone(), build_or_prop(rest)?])),
    }
}

/// How one disjunct's branch is refuted, given its hypothesis.
enum DisjunctRefutation<'a> {
    /// A closed false order atom (`2 < 0`) — refute directly.
    ClosedAtom(ClosedOrderAtom),
    /// A closed false equality (`8 = 0`, the divisor of a `% N` bound) — refute
    /// directly via the equality refutation.
    ClosedEq { a: i128, b: i128 },
    /// An order atom contradicting the conjunctive context (`_3 < 8` vs `_3 ≥ 8`)
    /// — close the transitive chain over `context ∧ this`.
    ChainAtom { a: &'a Formula, b: &'a Formula, strict: bool },
}

/// A disjunct of a disjunctive violation: its kernel prop (for the `Or` / branch
/// binder), its SMT (for the ay cross-check), and how its branch is refuted.
struct Disjunct<'a> {
    prop: Expr,
    smt: String,
    refutation: DisjunctRefutation<'a>,
}

/// Refute one disjunct's branch (hypothesis `h`) against the conjunctive context.
fn refute_disjunct(d: &Disjunct<'_>, context: &[OrderEdge], h: Expr) -> Option<Expr> {
    match &d.refutation {
        DisjunctRefutation::ClosedAtom(atom) => refute_false_atom(atom, h),
        DisjunctRefutation::ClosedEq { a, b } => refute_false_eq(*a, *b, h),
        DisjunctRefutation::ChainAtom { a, b, strict } => {
            let own: Vec<OrderEdge> = build_order_edges(a, b, *strict, h).into_iter().collect();
            // Pure variable cycles (`a < b` against a context `b ≤ a`) have no
            // literal head, so [`refute_via_chain_edges`]' DFS never sees
            // them — close a direct two-edge cycle first.
            for edge in &own {
                if let Some(term) = refute_via_var_cycle(edge, context) {
                    return Some(term);
                }
            }
            let mut edges = context.to_vec();
            edges.extend(own);
            refute_via_chain_edges(&edges)
        }
    }
}

/// Two-edge variable-cycle refutation: the disjunct's own edge `a R₁ b` joined
/// with a REVERSE context edge `b R₂ a` closes into `x < x` / `Int.lt_irrefl`
/// when at least one of the two is strict (`a ≤ b ∧ b ≤ a` alone is
/// satisfiable and must never fire). Complements [`refute_via_chain_edges`],
/// whose DFS starts only from LITERAL heads and therefore cannot reach a pure
/// variable cycle (`a < b ∧ b ≤ a` from the disequality order split against an
/// antisymmetric bound pair). Strictness cases:
///
/// * `h₁ : a < b`, `h₂ : b ≤ a` → `Int.lt_irrefl a (Int.lt_of_lt_of_le a b a h₁ h₂)`
/// * `h₁ : a < b`, `h₂ : b < a` → weaken `h₂` via `Int.le_of_lt`, then as above
/// * `h₁ : a ≤ b`, `h₂ : b < a` → `Int.lt_irrefl b (Int.lt_of_lt_of_le b a b h₂ h₁)`
///
/// The composed term is re-checked by the clean kernel like every certificate,
/// so a mismatched edge/hypothesis can only fail closed.
///
/// RESTRICTED to pure Var-Var cycles: a Var-Lit mirror (`K ≤ idx` against
/// `idx < K`) is already closed by the chain DFS through its literal head, and
/// capturing it here would change the emitted term bytes for pre-existing
/// certificate families — breaking byte-exact replay of persisted
/// certificates (`recheck_cleancic_with_identity` regenerates with the
/// current producer and requires equality) — without adding any coverage.
fn refute_via_var_cycle(edge: &OrderEdge, context: &[OrderEdge]) -> Option<Expr> {
    if !(matches!(edge.from, ChainNode::Var(_)) && matches!(edge.to, ChainNode::Var(_))) {
        return None;
    }
    for reverse in context {
        if reverse.from != edge.to || reverse.to != edge.from {
            continue;
        }
        let (a, b) = (&edge.from_expr, &edge.to_expr);
        if edge.strict {
            let le_back = if reverse.strict {
                const_app("Int.le_of_lt", [b.clone(), a.clone(), reverse.hyp.clone()])
            } else {
                reverse.hyp.clone()
            };
            let lt_aa = const_app(
                "Int.lt_of_lt_of_le",
                [a.clone(), b.clone(), a.clone(), edge.hyp.clone(), le_back],
            );
            return Some(Expr::app(const_app("Int.lt_irrefl", [a.clone()]), lt_aa));
        }
        if reverse.strict {
            let lt_bb = const_app(
                "Int.lt_of_lt_of_le",
                [b.clone(), a.clone(), b.clone(), reverse.hyp.clone(), edge.hyp.clone()],
            );
            return Some(Expr::app(const_app("Int.lt_irrefl", [b.clone()]), lt_bb));
        }
        // Both non-strict: not a contradiction — keep scanning for a strict
        // reverse edge.
    }
    None
}

/// Build a `False` term from `h_or : Or d1 (Or d2 …)` where each disjunct, joined
/// with the conjunctive `context`, is refutable (a closed-false atom/equality, or
/// a chain contradiction against the context). Right-nested `Or.rec`: each branch
/// binds its disjunct as bvar 0.
fn build_disjunctive_false(
    disjuncts: &[Disjunct<'_>],
    context: &[OrderEdge],
    h_or: Expr,
) -> Option<Expr> {
    match disjuncts {
        [] => None,
        [only] => refute_disjunct(only, context, h_or),
        [first, rest @ ..] => {
            let rest_prop =
                build_or_prop(&rest.iter().map(|d| d.prop.clone()).collect::<Vec<_>>())?;
            let or_ty = const_app("Or", [first.prop.clone(), rest_prop.clone()]);
            let motive = Expr::lam(BinderInfo::Default, or_ty, false_expr());
            // inl: λ h1 : d1 => refute(context ∧ d1) with d1 = bvar 0.
            let inl_body = refute_disjunct(first, context, Expr::bvar(0))?;
            let inl = Expr::lam(BinderInfo::Default, first.prop.clone(), inl_body);
            // inr: λ hrest : rest => recurse with hrest = bvar 0.
            let inr_body = build_disjunctive_false(rest, context, Expr::bvar(0))?;
            let inr = Expr::lam(BinderInfo::Default, rest_prop.clone(), inr_body);
            Some(const_app("Or.rec", [first.prop.clone(), rest_prop, motive, inl, inr, h_or]))
        }
    }
}

/// Parse a disjunct `Formula` into its refutation strategy: a closed-false order
/// atom, a closed-false equality, or a context-chain order atom. `None` for
/// anything else (the whole disjunctive certification then declines).
fn parse_disjunct(di: &Formula) -> Option<Disjunct<'_>> {
    let fits = |n: i128| i64::try_from(n).is_ok();
    // Closed false order atom (e.g. `8 < 0`).
    if let Some(atom) = closed_order_atom(di) {
        if atom.is_false() && atom.operands_fit() {
            return Some(Disjunct {
                prop: closed_atom_prop(&atom)?,
                smt: closed_atom_smt(&atom)?,
                refutation: DisjunctRefutation::ClosedAtom(atom),
            });
        }
    }
    // Closed false equality (e.g. `8 = 0`, the divisor==0 disjunct of a `% N`
    // result-bound fact `Or([N = 0, i % N < N])`).
    if let (Some(a), Some(b)) = closed_int_eq_operands(di) {
        if a != b && fits(a) && fits(b) {
            return Some(Disjunct {
                prop: eq_int(int_literal_to_kernel(a)?, int_literal_to_kernel(b)?),
                smt: format!("(= {} {})", int_literal_to_smt(a)?, int_literal_to_smt(b)?),
                refutation: DisjunctRefutation::ClosedEq { a, b },
            });
        }
    }
    // Otherwise a single order atom refuted against the context.
    let atoms = normalize_atom(di)?;
    let [atom] = atoms.as_slice() else { return None };
    let (a, b, strict) = match atom {
        Atom::Lt(a, b) => (*a, *b, true),
        Atom::Le(a, b) => (*a, *b, false),
    };
    Some(Disjunct {
        prop: linear_atom_prop(atom)?,
        smt: linear_atom_smt(atom)?,
        refutation: DisjunctRefutation::ChainAtom { a, b, strict },
    })
}

// ---------------------------------------------------------------------------
// Loop-accumulation no-overflow — direct two-edge discharge (bypasses the
// augmented-edge DFS / 48-edge cap).
// ---------------------------------------------------------------------------

/// An integer *threshold* literal (an upper limit `MAX` or a present bound),
/// carried as a `u128` so a `UInt(u128::MAX)` overflow limit (which EXCEEDS
/// `i128::MAX`) is represented exactly. Non-negative by construction — every
/// type maximum and post-add sum bound is `≥ 0`.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Threshold(u128);

/// The non-negative `Threshold` of a `Formula` integer literal (`Int(n)` with
/// `n ≥ 0`, or any `UInt(n)`), else `None`. A negative `Int` is not a valid
/// overflow limit / post-add bound, so it is rejected (fail-closed).
fn threshold_value(f: &Formula) -> Option<Threshold> {
    match f {
        Formula::Int(n) if *n >= 0 => Some(Threshold(*n as u128)),
        Formula::UInt(n) => Some(Threshold(*n)),
        _ => None,
    }
}

impl Threshold {
    /// `Int.ofNat n` for this threshold (arbitrary `u128` magnitude).
    fn to_kernel(self) -> Expr {
        int_ofnat_u128(self.0)
    }

    /// Non-negative decimal SMT literal.
    fn to_smt(self) -> String {
        self.0.to_string()
    }
}

/// The two free `Int` variables `a, b` of an `Add(a, b)` term (either operand
/// order is the sum `a + b`), or `None` if the term is not a sum of two plain
/// `Int` variables.
fn add_var_pair(f: &Formula) -> Option<(String, String)> {
    if let Formula::Add(x, y) = f {
        if let (Some(a), Some(b)) = (int_var_name(x), int_var_name(y)) {
            return Some((a, b));
        }
    }
    None
}

/// Match the loop-accumulation overflow disjunction
/// `Or([Lt(Add(a,b),0), Gt(Add(a,b),MAX)])` (the per-add no-overflow obligation),
/// returning `(a, b, MAX)` for the sum's two variables and the overflow limit.
/// Both disjunct orders are accepted, and the UPPER disjunct may render as either
/// `Gt(Add,MAX)` or `Lt(MAX,Add)`. `MAX` is a closed non-negative literal
/// (`Int`/`UInt`, including `UInt(u128::MAX)`). `None` for anything else.
fn match_overflow_disjunction(f: &Formula) -> Option<(String, String, Threshold)> {
    let Formula::Or(ds) = f else { return None };
    let [d0, d1] = ds.as_slice() else { return None };
    // A `Lt(Add(a,b), 0)` lower (underflow) disjunct → `(a, b)`.
    let lower = |d: &Formula| -> Option<(String, String)> {
        match d {
            Formula::Lt(s, z) if matches!(z.as_ref(), Formula::Int(0)) => add_var_pair(s),
            _ => None,
        }
    };
    // A `Gt(Add(a,b), MAX)` / `Lt(MAX, Add(a,b))` upper (overflow) disjunct
    // → `(a, b, MAX)`.
    let upper = |d: &Formula| -> Option<(String, String, Threshold)> {
        match d {
            Formula::Gt(s, m) => {
                let (a, b) = add_var_pair(s)?;
                Some((a, b, threshold_value(m)?))
            }
            Formula::Lt(m, s) => {
                let (a, b) = add_var_pair(s)?;
                Some((a, b, threshold_value(m)?))
            }
            _ => None,
        }
    };
    // Accept either disjunct order.
    let try_order = |lo: &Formula, up: &Formula| -> Option<(String, String, Threshold)> {
        let (la, lb) = lower(lo)?;
        let (ua, ub, max) = upper(up)?;
        // The lower and upper disjuncts must be over the SAME sum `a + b`
        // (modulo operand order), so the refutation's three present facts key
        // onto one term.
        if (la == ua && lb == ub) || (la == ub && lb == ua) { Some((ua, ub, max)) } else { None }
    };
    try_order(d0, d1).or_else(|| try_order(d1, d0))
}

/// Match the De Morgan DUAL of the overflow disjunction — the HARDENED
/// panic-boundary (`mir_assert::Overflow(Add)`) violation form
/// `Not(And([Le(0, Add(a,b)), Le(Add(a,b), MAX)]))` (the negation of the in-range
/// predicate `0 ≤ a+b ≤ MAX`). Either And-operand order; `MAX` a non-negative
/// `Int` literal. Returns `(a, b, MAX)`. This is the shape the hardened MIR
/// arithmetic-overflow assert lowers to, distinct from the `Or([Lt,Gt])` form the
/// FullVerification lane emits.
fn match_not_in_range_overflow(f: &Formula) -> Option<(String, String, i128)> {
    let Formula::Not(inner) = f else { return None };
    let Formula::And(cs) = inner.as_ref() else { return None };
    let [c0, c1] = cs.as_slice() else { return None };
    // `Le(0, Add(a,b))` lower-in-range conjunct → `(a,b)`.
    let lower = |c: &Formula| -> Option<(String, String)> {
        match c {
            Formula::Le(z, s) if matches!(z.as_ref(), Formula::Int(0)) => add_var_pair(s),
            _ => None,
        }
    };
    // `Le(Add(a,b), MAX)` upper-in-range conjunct → `(a,b,MAX)`.
    let upper = |c: &Formula| -> Option<(String, String, i128)> {
        match c {
            Formula::Le(s, m) => {
                let (a, b) = add_var_pair(s)?;
                Some((a, b, int_literal_value(m)?))
            }
            _ => None,
        }
    };
    let check = |lo: &Formula, up: &Formula| -> Option<(String, String, i128)> {
        let (la, lb) = lower(lo)?;
        let (ua, ub, max) = upper(up)?;
        if max < 0 || !((la == ua && lb == ub) || (la == ub && lb == ua)) {
            return None;
        }
        Some((ua, ub, max))
    };
    check(c0, c1).or_else(|| check(c1, c0))
}

/// Is the summand non-negativity `0 ≤ v` present among `conjuncts`? Both
/// `Le(0, v)` and `Ge(v, 0)` count. The fact is asserted (and re-checked) via the
/// canonical `Le(0, v)` hypothesis the discharge builds, so only its PRESENCE
/// matters here.
fn has_var_nonneg(conjuncts: &[&Formula], v: &str) -> bool {
    conjuncts.iter().any(|c| match c {
        Formula::Le(z, x) => {
            matches!(z.as_ref(), Formula::Int(0))
                && matches!(x.as_ref(), Formula::Var(n, Sort::Int) if n == v)
        }
        Formula::Ge(x, z) => {
            matches!(z.as_ref(), Formula::Int(0))
                && matches!(x.as_ref(), Formula::Var(n, Sort::Int) if n == v)
        }
        _ => false,
    })
}

/// The tightest present `Le(Add(a,b), bound)` upper bound on the sum `a + b`
/// (either Add-operand order), as a `Threshold`. Only a DIRECTLY-present bound
/// is returned — the bound is NOT synthesized. `None` if absent.
fn find_sum_upper_bound(conjuncts: &[&Formula], a: &str, b: &str) -> Option<Threshold> {
    let mut best: Option<Threshold> = None;
    for &c in conjuncts {
        if let Formula::Le(s, bnd) = c {
            if let Some((sa, sb)) = add_var_pair(s) {
                if (sa == a && sb == b) || (sa == b && sb == a) {
                    if let Some(t) = threshold_value(bnd) {
                        best = Some(match best {
                            Some(p) if p.0 <= t.0 => p,
                            _ => t,
                        });
                    }
                }
            }
        }
    }
    best
}

/// The tightest present `Le(Var(v), lit)` / `Ge(lit, Var(v))` upper bound on a
/// SINGLE variable `v`, as an `i128`. Only a DIRECTLY-present bound is returned
/// — never synthesized. `None` if absent. This is what lets a two-variable sum
/// overflow obligation `Or([a+b<0, a+b>MAX])` close from the SUMMAND bounds
/// `a≤A ∧ b≤B` (deriving `a+b ≤ A+B` additively) when no direct `Le(a+b, bound)`
/// is present — e.g. `(a/c)+(b/c)` where the division-range normalization emits
/// `a/c ≤ ⌊U/c⌋` on each summand but no bound on their sum.
fn find_var_upper_bound(conjuncts: &[&Formula], v: &str) -> Option<i128> {
    let is_v = |f: &Formula| matches!(f, Formula::Var(n, Sort::Int) if n == v);
    let mut best: Option<i128> = None;
    for &c in conjuncts {
        let bound = match c {
            Formula::Le(x, bnd) if is_v(x.as_ref()) => int_literal_value(bnd),
            Formula::Ge(bnd, x) if is_v(x.as_ref()) => int_literal_value(bnd),
            _ => None,
        };
        if let Some(bv) = bound {
            best = Some(best.map_or(bv, |p| p.min(bv)));
        }
    }
    best
}

/// Direct kernel discharge of a loop-accumulation per-add no-overflow obligation,
/// bypassing the augmented-edge DFS (and its 48-edge cap) that the surrounding
/// shift/nested-loop conjuncts would blow.
///
/// Fires ONLY when the flattened conjuncts carry the EXACT shape:
///   (a) the overflow disjunction `Or([Lt(Add(a,b),0), Gt(Add(a,b),MAX)])`
///       (either disjunct/operand order; upper may be `Lt(MAX,Add)`);
///   (b) a DIRECTLY-present tight bound `Le(Add(a,b),bound)` with `bound ≤ MAX`;
///   (c) the summand non-negativities `Le(0,a)` and `Le(0,b)`.
/// Each is a real hypothesis of the obligation. The refutation uses ONLY these
/// present facts:
///   * UPPER (`MAX < a+b`): `Int.lt_of_lt_of_le MAX (a+b) bound h_up h_bnd`
///     gives `MAX < bound`, a closed-false atom (`bound ≤ MAX`) closed by
///     `refute_false_atom`.
///   * LOWER (`a+b < 0`): the additive lift `0 ≤ a+b` (from `0≤a, 0≤b` via
///     `add_lift`) composed with `a+b < 0` gives `0 < 0`, closed likewise.
///   * `Or.rec` case-split (`build_disjunctive_false`) joins the two branches.
/// The result is handed to `finish_certificate` — ay UNSAT cross-check + clean
/// kernel re-check. Fail-closed: any missing fact, `bound > MAX`, or a
/// non-matching shape returns `None` (→ caller records `Trusted`).
fn certify_accumulator_no_overflow(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    // Flatten the (deeply nested) conjunction so the present facts and the
    // overflow `Or` are all visible at one level.
    let mut flat: Vec<&Formula> = Vec::new();
    for &c in conjuncts {
        collect_conjuncts(c, &mut flat);
    }

    // (a) Find the overflow disjunction `Or([a+b<0, a+b>MAX])`.
    let (a, b, max) = flat.iter().copied().find_map(|c| match_overflow_disjunction(c))?;

    // (b) The directly-present tight bound `Le(a+b, bound)` with `bound ≤ MAX`.
    let bound = find_sum_upper_bound(&flat, &a, &b)?;
    if bound.0 > max.0 {
        return None; // bound must not exceed MAX — fail closed.
    }

    // (c) The two summand non-negativities `Le(0,a)`, `Le(0,b)` must be present.
    if !has_var_nonneg(&flat, &a) || !has_var_nonneg(&flat, &b) {
        return None;
    }

    // Build the kernel hypotheses + their props/SMT. Fvars are assigned densely.
    let ax = chain_var_expr(&a);
    let bx = chain_var_expr(&b);
    let sum_k = hadd_int(ax.clone(), bx.clone());
    let sum_bare = int_add_expr(ax.clone(), bx.clone());
    let zero_k = int_literal_to_kernel(0)?;
    let max_k = max.to_kernel();
    let bound_k = bound.to_kernel();

    // h_bnd : Int.le (a+b) bound. (HAdd form — matches the registered hyp prop.)
    let bnd_fvar = FVarId::new(HYP_FVAR_BASE);
    let h_bnd = Hyp {
        smt: format!(
            "(<= (+ {} {}) {})",
            encoded_var_name(&a),
            encoded_var_name(&b),
            bound.to_smt()
        ),
        prop: le_int(sum_k.clone(), bound_k.clone()),
        fvar: bnd_fvar,
        name: "h_0".to_string(),
    };
    // h_a : Int.le 0 a ; h_b : Int.le 0 b.
    let a_fvar = FVarId::new(HYP_FVAR_BASE + 1);
    let h_a = Hyp {
        smt: format!("(<= 0 {})", encoded_var_name(&a)),
        prop: le_int(zero_k.clone(), ax.clone()),
        fvar: a_fvar,
        name: "h_1".to_string(),
    };
    let b_fvar = FVarId::new(HYP_FVAR_BASE + 2);
    let h_b = Hyp {
        smt: format!("(<= 0 {})", encoded_var_name(&b)),
        prop: le_int(zero_k.clone(), bx.clone()),
        fvar: b_fvar,
        name: "h_2".to_string(),
    };

    // The overflow `Or` hypothesis: `Or(Int.lt (a+b) 0) (Int.lt MAX (a+b))`.
    // (`Gt(S,MAX) ≡ Lt(MAX,S)`; the registered prop uses the normalized `Lt`.)
    let lower_prop = lt_int(sum_k.clone(), zero_k.clone());
    let upper_prop = lt_int(max_k.clone(), sum_k.clone());
    let or_prop = const_app("Or", [lower_prop.clone(), upper_prop.clone()]);
    let or_fvar = FVarId::new(HYP_FVAR_BASE + 3);
    let or_smt = format!(
        "(or (< (+ {a} {b}) 0) (< {max} (+ {a} {b})))",
        a = encoded_var_name(&a),
        b = encoded_var_name(&b),
        max = max.to_smt()
    );
    let h_or = Hyp { smt: or_smt, prop: or_prop.clone(), fvar: or_fvar, name: "h_3".to_string() };

    // ---- LOWER branch refutation: `h_lo : a+b < 0` ⊢ False. ----
    // `add_lift(a,b,0,0,h_a,h_b,false)` proves `Int.le (0+0) (a+b)` (def-eq
    // `Int.le 0 (a+b)`); compose with `h_lo` via `Int.lt_of_le_of_lt 0 (a+b) 0`,
    // then `refute_false_atom` on the closed-false `0 < 0`.
    let build_lower = |h_lo: Expr| -> Option<Expr> {
        let lift = add_lift(&a, &b, 0, 0, &Expr::fvar(a_fvar), &Expr::fvar(b_fvar), false)?;
        // lift.hyp : Int.le (0+0) (a+b) ; def-eq Int.le 0 (a+b).
        let nonneg_sum = lift.hyp;
        // Int.lt_of_le_of_lt 0 (a+b) 0 nonneg_sum h_lo : Int.lt 0 0.
        let lt00 = const_app(
            "Int.lt_of_le_of_lt",
            [zero_k.clone(), sum_bare.clone(), zero_k.clone(), nonneg_sum, h_lo],
        );
        refute_false_atom(&ClosedOrderAtom { a: 0, b: 0, is_lt: true }, lt00)
    };

    // ---- UPPER branch refutation: `h_up : MAX < a+b` ⊢ False. ----
    // `Int.lt_of_lt_of_le MAX (a+b) bound h_up h_bnd : Int.lt MAX bound`, a
    // closed-false atom since `bound ≤ MAX`; closed by `refute_false_atom`.
    // The closed atom carries the (non-negative) threshold magnitudes as `i128`
    // when they fit, else the `u128`-encoded form via `refute_false_atom`'s
    // overflow-robust gap (`nonneg_gap_u128`). Require both fit `i128` so the
    // `ClosedOrderAtom` (which keys on `i128`) is faithful; a `UInt(u128::MAX)`
    // MAX exceeds `i128::MAX`, so route the closing through a `u128`-direct
    // witness instead.
    let build_upper = |h_up: Expr| -> Option<Expr> {
        let lt_max_bound = const_app(
            "Int.lt_of_lt_of_le",
            [max_k.clone(), sum_bare.clone(), bound_k.clone(), h_up, Expr::fvar(bnd_fvar)],
        );
        // `MAX < bound` is closed-false (`bound ≤ MAX`). Witness `b < a` by
        // `Int.NonNeg.mk (MAX - bound - 1)` (the gap, ≥ 0 since bound ≤ MAX),
        // built `u128`-direct so a wide `UInt` MAX is faithful.
        // refute pattern (mirrors refute_false_atom's `is_lt` arm with a, b
        // swapped to MAX, bound): Int.lt_irrefl bound (lt_of_lt_of_le bound MAX
        // bound pos lt_max_bound). Here `pos : Int.le MAX bound`? No — we need
        // `MAX < bound` false ⟹ `bound ≤ MAX`. Build directly:
        let gap = max.0.checked_sub(bound.0)?; // MAX - bound ≥ 0.
        // pos : Int.le bound MAX  =  Int.NonNeg (MAX - bound).
        let pos = nonneg_mk_u128(gap);
        // Int.lt_of_lt_of_le bound MAX bound (h:bound<... no). Use the symmetric
        // closed-false refutation: from `lt_max_bound : MAX < bound` and
        // `pos : bound ≤ MAX`, `Int.lt_of_lt_of_le MAX bound MAX lt_max_bound pos
        // : MAX < MAX`, then `Int.lt_irrefl MAX`.
        let lt_max_max = const_app(
            "Int.lt_of_lt_of_le",
            [max_k.clone(), bound_k.clone(), max_k.clone(), lt_max_bound, pos],
        );
        Some(Expr::app(const_app("Int.lt_irrefl", [max_k.clone()]), lt_max_max))
    };

    // `Or.rec` case-split: inl ↦ lower, inr ↦ upper, each binding its disjunct as
    // bvar 0. Mirrors `build_disjunctive_false`'s two-disjunct construction.
    let motive = Expr::lam(BinderInfo::Default, or_prop.clone(), false_expr());
    let inl = Expr::lam(BinderInfo::Default, lower_prop.clone(), build_lower(Expr::bvar(0))?);
    let inr = Expr::lam(BinderInfo::Default, upper_prop.clone(), build_upper(Expr::bvar(0))?);
    let term = const_app("Or.rec", [lower_prop, upper_prop, motive, inl, inr, Expr::fvar(or_fvar)]);

    let hyps = vec![h_bnd, h_a, h_b, h_or];
    let var_names: BTreeSet<String> = [a, b].into_iter().collect();
    finish_certificate(&hyps, &term, &var_names, identity)
}

/// Direct kernel discharge of a two-variable-sum no-overflow obligation whose
/// sum bound is NOT directly present but is DERIVABLE from per-summand bounds —
/// the `(a/c)+(b/c)` midpoint shape as it reaches the kernel from the HARDENED
/// panic-boundary lane (`mir_assert::Overflow(Add)`): the violation is the
/// unsigned `Or([Lt(Add(a,b),0), Gt(Add(a,b),MAX)])` and the present facts are
/// the two summand upper bounds `Le(a,A)`, `Le(b,B)` (here `A=B=⌊MAX/2⌋`, emitted
/// by the division-range normalization) plus the summand non-negativities
/// `Le(0,a)`, `Le(0,b)` — but NO direct `Le(a+b, bound)`. `certify_accumulator_no_overflow`
/// needs that direct bound, and the generic augmented-edge DFS blows its 48-edge
/// cap on the surrounding SSA/bool conjuncts, so this shape would otherwise fall
/// through uncertified (the same span's `arithmetic_safety` BV obligation IS
/// certified via `certify_unsigned_bv_div_sum_no_overflow`, leaving only this
/// redundant hardened restatement `Unknown` → the whole verdict INCONCLUSIVE).
///
/// Refutation uses ONLY the four present bound facts (no augmented edge set):
///   * derive `h_sum_ub : a+b ≤ A+B` from `a≤A, b≤B` via `add_lift` (upper), with
///     `A+B ≤ MAX` checked; UPPER (`MAX < a+b`): `Int.lt_of_lt_of_le MAX (a+b)
///     (A+B) h_up h_sum_ub` gives the closed-false `MAX < A+B`;
///   * LOWER (`a+b < 0`): the additive lift `0 ≤ a+b` (from `0≤a, 0≤b`) composed
///     with `a+b < 0` gives `0 < 0`;
///   * `Or.rec` case-split joins them.
/// Handed to `finish_certificate` (ay UNSAT cross-check + clean kernel re-check).
/// Fail-closed: any missing fact, `A+B > MAX`, or a non-matching shape → `None`.
fn certify_summand_bounded_accumulator_no_overflow(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let mut flat: Vec<&Formula> = Vec::new();
    for &c in conjuncts {
        collect_conjuncts(c, &mut flat);
    }

    // (a) The unsigned overflow disjunction `Or([a+b<0, a+b>MAX])`.
    let (a, b, max) = flat.iter().copied().find_map(match_overflow_disjunction)?;
    // A directly-present sum bound is `certify_accumulator_no_overflow`'s job;
    // only fire here for the summand-bound-only shape.
    if find_sum_upper_bound(&flat, &a, &b).is_some() {
        return None;
    }
    // (b) The two SUMMAND upper bounds `a≤A`, `b≤B`, with `A+B ≤ MAX`.
    let ua = find_var_upper_bound(&flat, &a)?;
    let ub = find_var_upper_bound(&flat, &b)?;
    let sum_hi = ua.checked_add(ub)?;
    // The derived sum bound must be non-negative (it is, given the non-negativity
    // facts below) and must not exceed the unsigned type MAX (`Threshold.0` is
    // `u128`) — otherwise a genuine overflow is possible; fail closed.
    let sum_hi_u = u128::try_from(sum_hi).ok()?;
    if sum_hi_u > max.0 {
        return None;
    }
    // (c) The two summand non-negativities `Le(0,a)`, `Le(0,b)`.
    if !has_var_nonneg(&flat, &a) || !has_var_nonneg(&flat, &b) {
        return None;
    }

    let ax = chain_var_expr(&a);
    let bx = chain_var_expr(&b);
    let sum_k = hadd_int(ax.clone(), bx.clone());
    let sum_bare = int_add_expr(ax.clone(), bx.clone());
    let zero_k = int_literal_to_kernel(0)?;
    let max_k = max.to_kernel();
    let ua_k = int_literal_to_kernel(ua)?;
    let ub_k = int_literal_to_kernel(ub)?;
    let sum_hi_k = int_literal_to_kernel(sum_hi)?;

    // h_a_ub : Int.le a A ; h_b_ub : Int.le b B.
    let a_ub_fvar = FVarId::new(HYP_FVAR_BASE);
    let h_a_ub = Hyp {
        smt: format!("(<= {} {})", encoded_var_name(&a), int_literal_to_smt(ua)?),
        prop: le_int(ax.clone(), ua_k.clone()),
        fvar: a_ub_fvar,
        name: "h_0".to_string(),
    };
    let b_ub_fvar = FVarId::new(HYP_FVAR_BASE + 1);
    let h_b_ub = Hyp {
        smt: format!("(<= {} {})", encoded_var_name(&b), int_literal_to_smt(ub)?),
        prop: le_int(bx.clone(), ub_k.clone()),
        fvar: b_ub_fvar,
        name: "h_1".to_string(),
    };
    // h_a_nn : Int.le 0 a ; h_b_nn : Int.le 0 b.
    let a_nn_fvar = FVarId::new(HYP_FVAR_BASE + 2);
    let h_a_nn = Hyp {
        smt: format!("(<= 0 {})", encoded_var_name(&a)),
        prop: le_int(zero_k.clone(), ax.clone()),
        fvar: a_nn_fvar,
        name: "h_2".to_string(),
    };
    let b_nn_fvar = FVarId::new(HYP_FVAR_BASE + 3);
    let h_b_nn = Hyp {
        smt: format!("(<= 0 {})", encoded_var_name(&b)),
        prop: le_int(zero_k.clone(), bx.clone()),
        fvar: b_nn_fvar,
        name: "h_3".to_string(),
    };

    // The overflow `Or`: `Or(Int.lt (a+b) 0) (Int.lt MAX (a+b))`.
    let lower_prop = lt_int(sum_k.clone(), zero_k.clone());
    let upper_prop = lt_int(max_k.clone(), sum_k.clone());
    let or_prop = const_app("Or", [lower_prop.clone(), upper_prop.clone()]);
    let or_fvar = FVarId::new(HYP_FVAR_BASE + 4);
    let or_smt = format!(
        "(or (< (+ {a} {b}) 0) (< {max} (+ {a} {b})))",
        a = encoded_var_name(&a),
        b = encoded_var_name(&b),
        max = max.to_smt()
    );
    let h_or = Hyp { smt: or_smt, prop: or_prop.clone(), fvar: or_fvar, name: "h_4".to_string() };

    // ---- LOWER branch: `h_lo : a+b < 0` ⊢ False. ----
    // `add_lift(a,b,0,0,h_a_nn,h_b_nn,false)` proves `Int.le (0+0) (a+b)` (def-eq
    // `Int.le 0 (a+b)`); compose with `h_lo` via `Int.lt_of_le_of_lt 0 (a+b) 0`,
    // then close the false `0 < 0`.
    let build_lower = |h_lo: Expr| -> Option<Expr> {
        let lift = add_lift(&a, &b, 0, 0, &Expr::fvar(a_nn_fvar), &Expr::fvar(b_nn_fvar), false)?;
        let nonneg_sum = lift.hyp;
        let lt00 = const_app(
            "Int.lt_of_le_of_lt",
            [zero_k.clone(), sum_bare.clone(), zero_k.clone(), nonneg_sum, h_lo],
        );
        refute_false_atom(&ClosedOrderAtom { a: 0, b: 0, is_lt: true }, lt00)
    };

    // ---- UPPER branch: `h_up : MAX < a+b` ⊢ False. ----
    // Derive `h_sum_ub : a+b ≤ A+B` from `a≤A, b≤B` (`add_lift` upper), then
    // `Int.lt_of_lt_of_le MAX (a+b) (A+B) h_up h_sum_ub : MAX < A+B`, a closed-
    // false atom since `A+B ≤ MAX` — closed via `Int.NonNeg (MAX-(A+B))`.
    let build_upper = |h_up: Expr| -> Option<Expr> {
        let lift = add_lift(&a, &b, ua, ub, &Expr::fvar(a_ub_fvar), &Expr::fvar(b_ub_fvar), true)?;
        let sum_ub = lift.hyp; // Int.le (a+b) (A+B).
        let lt_max_sumhi = const_app(
            "Int.lt_of_lt_of_le",
            [max_k.clone(), sum_bare.clone(), sum_hi_k.clone(), h_up, sum_ub],
        );
        let gap = max.0.checked_sub(sum_hi_u)?; // MAX - (A+B) ≥ 0.
        let pos = nonneg_mk_u128(gap); // pos : Int.le (A+B) MAX.
        let lt_max_max = const_app(
            "Int.lt_of_lt_of_le",
            [max_k.clone(), sum_hi_k.clone(), max_k.clone(), lt_max_sumhi, pos],
        );
        Some(Expr::app(const_app("Int.lt_irrefl", [max_k.clone()]), lt_max_max))
    };

    let motive = Expr::lam(BinderInfo::Default, or_prop.clone(), false_expr());
    let inl = Expr::lam(BinderInfo::Default, lower_prop.clone(), build_lower(Expr::bvar(0))?);
    let inr = Expr::lam(BinderInfo::Default, upper_prop.clone(), build_upper(Expr::bvar(0))?);
    let term = const_app("Or.rec", [lower_prop, upper_prop, motive, inl, inr, Expr::fvar(or_fvar)]);

    let hyps = vec![h_a_ub, h_b_ub, h_a_nn, h_b_nn, h_or];
    let var_names: BTreeSet<String> = [a, b].into_iter().collect();
    finish_certificate(&hyps, &term, &var_names, identity)
}

/// Same summand-bound-derived no-overflow discharge as
/// `certify_summand_bounded_accumulator_no_overflow`, but for the De Morgan DUAL
/// violation shape the HARDENED panic-boundary lane emits:
/// `Not(And([Le(0, a+b), Le(a+b, MAX)]))` instead of `Or([a+b<0, a+b>MAX])`.
/// (`(a/2)+(b/2)` generates BOTH — the FullVerification `arithmetic_safety` in the
/// `Or` form and the hardened `mir_assert::Overflow(Add)` in this `Not(And(..))`
/// form; without this the redundant hardened restatement stays `Unknown` and
/// drags the whole verdict INCONCLUSIVE.)
///
/// Refutation: the violation `h_v : ¬(0 ≤ a+b ∧ a+b ≤ MAX)` is `(0 ≤ a+b ∧ a+b ≤
/// MAX) → False`. Build the in-range proof `hP` from the four summand bound facts
/// — `h_lo : 0 ≤ a+b` (additive lift of `0≤a, 0≤b`) and `h_hi : a+b ≤ MAX`
/// (additive lift of `a≤A, b≤B` composed via `Int.le_trans` with `A+B ≤ MAX`) —
/// combine with `And.intro`, then `h_v hP : False`. Handed to `finish_certificate`
/// (ay UNSAT cross-check + clean kernel re-check). Fail-closed on any missing
/// fact, `A+B > MAX`, or a non-matching shape.
fn certify_summand_bounded_not_in_range_no_overflow(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let mut flat: Vec<&Formula> = Vec::new();
    for &c in conjuncts {
        collect_conjuncts(c, &mut flat);
    }

    // (a) The not-in-range violation `Not(And([Le(0, a+b), Le(a+b, MAX)]))`.
    let (a, b, max_i) = flat.iter().copied().find_map(match_not_in_range_overflow)?;
    // (b) The two SUMMAND upper bounds `a≤A`, `b≤B`, with `A+B ≤ MAX`.
    let ua = find_var_upper_bound(&flat, &a)?;
    let ub = find_var_upper_bound(&flat, &b)?;
    let sum_hi = ua.checked_add(ub)?;
    if sum_hi < 0 || sum_hi > max_i {
        return None;
    }
    // (c) The two summand non-negativities `Le(0,a)`, `Le(0,b)`.
    if !has_var_nonneg(&flat, &a) || !has_var_nonneg(&flat, &b) {
        return None;
    }

    let ax = chain_var_expr(&a);
    let bx = chain_var_expr(&b);
    let sum_k = hadd_int(ax.clone(), bx.clone());
    let sum_bare = int_add_expr(ax.clone(), bx.clone());
    let zero_k = int_literal_to_kernel(0)?;
    let max_k = int_literal_to_kernel(max_i)?;
    let ua_k = int_literal_to_kernel(ua)?;
    let ub_k = int_literal_to_kernel(ub)?;

    // The four summand-bound hypotheses.
    let a_ub_fvar = FVarId::new(HYP_FVAR_BASE);
    let h_a_ub = Hyp {
        smt: format!("(<= {} {})", encoded_var_name(&a), int_literal_to_smt(ua)?),
        prop: le_int(ax.clone(), ua_k.clone()),
        fvar: a_ub_fvar,
        name: "h_0".to_string(),
    };
    let b_ub_fvar = FVarId::new(HYP_FVAR_BASE + 1);
    let h_b_ub = Hyp {
        smt: format!("(<= {} {})", encoded_var_name(&b), int_literal_to_smt(ub)?),
        prop: le_int(bx.clone(), ub_k.clone()),
        fvar: b_ub_fvar,
        name: "h_1".to_string(),
    };
    let a_nn_fvar = FVarId::new(HYP_FVAR_BASE + 2);
    let h_a_nn = Hyp {
        smt: format!("(<= 0 {})", encoded_var_name(&a)),
        prop: le_int(zero_k.clone(), ax.clone()),
        fvar: a_nn_fvar,
        name: "h_2".to_string(),
    };
    let b_nn_fvar = FVarId::new(HYP_FVAR_BASE + 3);
    let h_b_nn = Hyp {
        smt: format!("(<= 0 {})", encoded_var_name(&b)),
        prop: le_int(zero_k.clone(), bx.clone()),
        fvar: b_nn_fvar,
        name: "h_3".to_string(),
    };

    // The in-range predicate `And(Int.le 0 (a+b)) (Int.le (a+b) MAX)` and its
    // negation `h_v`, the violation hypothesis.
    let le0_prop = le_int(zero_k.clone(), sum_k.clone());
    let le_max_prop = le_int(sum_k.clone(), max_k.clone());
    let and_prop = const_app("And", [le0_prop.clone(), le_max_prop.clone()]);
    let v_fvar = FVarId::new(HYP_FVAR_BASE + 4);
    let h_v = Hyp {
        smt: format!(
            "(not (and (<= 0 (+ {a} {b})) (<= (+ {a} {b}) {max})))",
            a = encoded_var_name(&a),
            b = encoded_var_name(&b),
            max = int_literal_to_smt(max_i)?
        ),
        prop: const_app("Not", [and_prop]),
        fvar: v_fvar,
        name: "h_4".to_string(),
    };

    // h_lo : Int.le 0 (a+b), from the additive lift of `0≤a, 0≤b` (def-eq
    // `Int.le (0+0) (a+b)`).
    let h_lo = add_lift(&a, &b, 0, 0, &Expr::fvar(a_nn_fvar), &Expr::fvar(b_nn_fvar), false)?.hyp;
    // h_hi : Int.le (a+b) MAX, from `a≤A, b≤B` (⟹ a+b ≤ A+B) composed with the
    // closed `A+B ≤ MAX` via `Int.le_trans`.
    let sum_ub =
        add_lift(&a, &b, ua, ub, &Expr::fvar(a_ub_fvar), &Expr::fvar(b_ub_fvar), true)?.hyp;
    let sum_bound_e = int_add_expr(ua_k.clone(), ub_k.clone()); // Int.add A B
    let gap = u128::try_from(max_i.checked_sub(sum_hi)?).ok()?; // MAX - (A+B) ≥ 0
    let pos = nonneg_mk_u128(gap); // Int.le (A+B) MAX
    let h_hi =
        const_app("Int.le_trans", [sum_bare.clone(), sum_bound_e, max_k.clone(), sum_ub, pos]);

    // hP : And (Int.le 0 (a+b)) (Int.le (a+b) MAX) ; term : h_v hP : False.
    let hp = const_app("And.intro", [le0_prop, le_max_prop, h_lo, h_hi]);
    let term = Expr::app(Expr::fvar(v_fvar), hp);

    let hyps = vec![h_a_ub, h_b_ub, h_a_nn, h_b_nn, h_v];
    let var_names: BTreeSet<String> = [a, b].into_iter().collect();
    finish_certificate(&hyps, &term, &var_names, identity)
}

/// Match a SIGNED two-sided overflow disjunction
/// `Or([Lt(Add(a,b), MIN), Gt(Add(a,b), MAX)])` (either disjunct order; the upper
/// may render as `Lt(MAX, Add)`), returning `(a, b, MIN, MAX)` with both thresholds
/// as signed `i128`. Distinct from `match_overflow_disjunction`, whose lower disjunct
/// is fixed at the unsigned underflow `Lt(Add,0)`: here the lower threshold is an
/// arbitrary signed literal (`i32::MIN`, `i64::MIN`, …). The `MIN < MAX` guard
/// rejects a degenerate window.
fn match_two_sided_overflow_disjunction(f: &Formula) -> Option<(String, String, i128, i128)> {
    let Formula::Or(ds) = f else { return None };
    let [d0, d1] = ds.as_slice() else { return None };
    // lower: `Lt(Add(a,b), MIN)` → `(a, b, MIN)`.
    let lower = |d: &Formula| -> Option<(String, String, i128)> {
        if let Formula::Lt(s, m) = d {
            let (a, b) = add_var_pair(s)?;
            return Some((a, b, int_literal_value(m)?));
        }
        None
    };
    // upper: `Gt(Add(a,b), MAX)` / `Lt(MAX, Add(a,b))` → `(a, b, MAX)`.
    let upper = |d: &Formula| -> Option<(String, String, i128)> {
        match d {
            Formula::Gt(s, m) => {
                let (a, b) = add_var_pair(s)?;
                Some((a, b, int_literal_value(m)?))
            }
            Formula::Lt(m, s) => {
                let (a, b) = add_var_pair(s)?;
                Some((a, b, int_literal_value(m)?))
            }
            _ => None,
        }
    };
    let try_order = |lo: &Formula, up: &Formula| -> Option<(String, String, i128, i128)> {
        let (la, lb, min) = lower(lo)?;
        let (ua, ub, max) = upper(up)?;
        if ((la == ua && lb == ub) || (la == ub && lb == ua)) && min < max {
            Some((ua, ub, min, max))
        } else {
            None
        }
    };
    try_order(d0, d1).or_else(|| try_order(d1, d0))
}

/// The tightest present `Ge(Add(a,b), lo)` / `Le(lo, Add(a,b))` lower bound on the
/// sum `a + b` (either Add-operand order), as a signed `i128`. Only a DIRECTLY-
/// present bound is returned — never synthesized — and the MAX (tightest) `lo` is
/// kept. `None` if absent.
fn find_sum_lower_bound(conjuncts: &[&Formula], a: &str, b: &str) -> Option<i128> {
    let same = |s: &Formula| -> bool {
        add_var_pair(s).is_some_and(|(sa, sb)| (sa == a && sb == b) || (sa == b && sb == a))
    };
    let mut best: Option<i128> = None;
    for &c in conjuncts {
        let lo = match c {
            Formula::Ge(s, bnd) if same(s) => int_literal_value(bnd),
            Formula::Le(bnd, s) if same(s) => int_literal_value(bnd),
            _ => None,
        };
        if let Some(l) = lo {
            best = Some(best.map_or(l, |p| p.max(l)));
        }
    }
    best
}

/// The tightest present `Le(Add(a,b), hi)` / `Ge(hi, Add(a,b))` upper bound on the
/// sum `a + b`, as a signed `i128` (the MIN, tightest, `hi` is kept). The signed
/// sibling of [`find_sum_upper_bound`] (which keys on the non-negative `Threshold`).
fn find_sum_upper_bound_i128(conjuncts: &[&Formula], a: &str, b: &str) -> Option<i128> {
    let same = |s: &Formula| -> bool {
        add_var_pair(s).is_some_and(|(sa, sb)| (sa == a && sb == b) || (sa == b && sb == a))
    };
    let mut best: Option<i128> = None;
    for &c in conjuncts {
        let hi = match c {
            Formula::Le(s, bnd) if same(s) => int_literal_value(bnd),
            Formula::Ge(bnd, s) if same(s) => int_literal_value(bnd),
            _ => None,
        };
        if let Some(h) = hi {
            best = Some(best.map_or(h, |p| p.min(h)));
        }
    }
    best
}

/// Direct kernel discharge of a SIGNED loop-accumulation per-add no-overflow
/// obligation `Or([Lt(a+b, MIN), Gt(a+b, MAX)])`, the symmetric two-sided sibling of
/// [`certify_accumulator_no_overflow`]. A signed reduction (`s += x as i32` over
/// `&[i8; _]`) carries the loop-invariant window for BOTH the accumulator and the
/// post-add sum as DIRECTLY-present conjuncts: `Ge(a+b, lo)` and `Le(a+b, hi)` with
/// `MIN ≤ lo` and `hi ≤ MAX`. Each overflow disjunct is then refuted against a
/// present sum bound (no additive non-negativity lift needed — both directions are
/// already bounded):
///   * LOWER (`a+b < MIN`): `Int.lt_of_le_of_lt lo (a+b) MIN h_lo h_d : lo < MIN`,
///     a closed-false atom (`MIN ≤ lo`) closed by `refute_false_atom`.
///   * UPPER (`MAX < a+b`): `Int.lt_of_lt_of_le MAX (a+b) hi h_d h_hi : MAX < hi`,
///     a closed-false atom (`hi ≤ MAX`) closed likewise.
///   * `Or.rec` joins the two branches.
/// Fires AFTER the unsigned accumulator path (so the `Lt(a+b,0)` shape, which lacks a
/// present `Ge(a+b,lo)`, is handled there and declined here). Fail-closed: a missing
/// lower/upper sum bound, a window straddling `[MIN,MAX]` (`lo < MIN` or `hi > MAX`),
/// or a non-matching shape returns `None`. Sound: every asserted hypothesis is a
/// present conjunct of the obligation, and the clean kernel re-checks the term.
fn certify_bounded_sum_no_overflow(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let mut flat: Vec<&Formula> = Vec::new();
    for &c in conjuncts {
        collect_conjuncts(c, &mut flat);
    }

    // (a) The two-sided overflow disjunction `Or([a+b<MIN, a+b>MAX])`.
    let (a, b, min, max) = flat.iter().copied().find_map(match_two_sided_overflow_disjunction)?;

    // (b) The directly-present sum window `lo ≤ a+b ≤ hi`, fully inside `[MIN, MAX]`.
    let lo = find_sum_lower_bound(&flat, &a, &b)?;
    let hi = find_sum_upper_bound_i128(&flat, &a, &b)?;
    if lo < min || hi > max {
        return None; // window must sit inside the type range — fail closed.
    }

    let ax = chain_var_expr(&a);
    let bx = chain_var_expr(&b);
    let sum_k = hadd_int(ax.clone(), bx.clone());
    let sum_bare = int_add_expr(ax.clone(), bx.clone());
    let min_k = int_literal_to_kernel(min)?;
    let max_k = int_literal_to_kernel(max)?;
    let lo_k = int_literal_to_kernel(lo)?;
    let hi_k = int_literal_to_kernel(hi)?;
    let (a_smt, b_smt) = (encoded_var_name(&a), encoded_var_name(&b));

    // h_lo : Int.le lo (a+b).
    let lo_fvar = FVarId::new(HYP_FVAR_BASE);
    let h_lo = Hyp {
        smt: format!("(<= {} (+ {} {}))", int_literal_to_smt(lo)?, a_smt, b_smt),
        prop: le_int(lo_k.clone(), sum_k.clone()),
        fvar: lo_fvar,
        name: "h_0".to_string(),
    };
    // h_hi : Int.le (a+b) hi.
    let hi_fvar = FVarId::new(HYP_FVAR_BASE + 1);
    let h_hi = Hyp {
        smt: format!("(<= (+ {} {}) {})", a_smt, b_smt, int_literal_to_smt(hi)?),
        prop: le_int(sum_k.clone(), hi_k.clone()),
        fvar: hi_fvar,
        name: "h_1".to_string(),
    };
    // The overflow `Or`: `Or(Int.lt (a+b) MIN) (Int.lt MAX (a+b))`
    // (`Gt(S,MAX) ≡ Lt(MAX,S)`; the normalized prop uses `Lt`).
    let lower_prop = lt_int(sum_k.clone(), min_k.clone());
    let upper_prop = lt_int(max_k.clone(), sum_k.clone());
    let or_prop = const_app("Or", [lower_prop.clone(), upper_prop.clone()]);
    let or_fvar = FVarId::new(HYP_FVAR_BASE + 2);
    let or_smt = format!(
        "(or (< (+ {a} {b}) {min}) (< {max} (+ {a} {b})))",
        a = a_smt,
        b = b_smt,
        min = int_literal_to_smt(min)?,
        max = int_literal_to_smt(max)?
    );
    let h_or = Hyp { smt: or_smt, prop: or_prop.clone(), fvar: or_fvar, name: "h_2".to_string() };

    // LOWER: `h_d : a+b < MIN` ⊢ `lo < MIN` (closed-false) ⊢ False.
    let build_lower = |h_d: Expr| -> Option<Expr> {
        let lt_lo_min = const_app(
            "Int.lt_of_le_of_lt",
            [lo_k.clone(), sum_bare.clone(), min_k.clone(), Expr::fvar(lo_fvar), h_d],
        );
        refute_false_atom(&ClosedOrderAtom { a: lo, b: min, is_lt: true }, lt_lo_min)
    };
    // UPPER: `h_d : MAX < a+b` ⊢ `MAX < hi` (closed-false) ⊢ False.
    let build_upper = |h_d: Expr| -> Option<Expr> {
        let lt_max_hi = const_app(
            "Int.lt_of_lt_of_le",
            [max_k.clone(), sum_bare.clone(), hi_k.clone(), h_d, Expr::fvar(hi_fvar)],
        );
        refute_false_atom(&ClosedOrderAtom { a: max, b: hi, is_lt: true }, lt_max_hi)
    };

    let motive = Expr::lam(BinderInfo::Default, or_prop.clone(), false_expr());
    let inl = Expr::lam(BinderInfo::Default, lower_prop.clone(), build_lower(Expr::bvar(0))?);
    let inr = Expr::lam(BinderInfo::Default, upper_prop.clone(), build_upper(Expr::bvar(0))?);
    let term = const_app("Or.rec", [lower_prop, upper_prop, motive, inl, inr, Expr::fvar(or_fvar)]);

    let hyps = vec![h_lo, h_hi, h_or];
    let var_names: BTreeSet<String> = [a, b].into_iter().collect();
    finish_certificate(&hyps, &term, &var_names, identity)
}

// ---------------------------------------------------------------------------
// Signed wide-BV add/sub no-overflow (i128 / widened) → linear-Int refutation.
// ---------------------------------------------------------------------------

/// The signed value carried by an overflow-check operand leaf, transparently
/// through a 64→128 (or any) sign-extension. Returns `(name, source_width)`:
///
/// * `Var(n, _)` — a bare BV operand var; its source width is the BV sort width.
/// * `BvSignExt(Var(n, _), _)` — a sign-extended operand; the carrier value is
///   exactly the inner value `n`, so we recurse to it and report the INNER
///   (source) width. `BvSignExt(v, k)` preserves v's signed value, so this is a
///   faithful, lossless unwrap (no signedness information is dropped).
///
/// `None` for any non-variable leaf (a literal, a nested arithmetic term, etc.),
/// so the lift is fail-closed on shapes it cannot bound.
fn bv_overflow_operand(f: &Formula) -> Option<(String, u32)> {
    match f {
        Formula::Var(name, Sort::BitVec(w)) => Some((name.clone(), *w)),
        Formula::Var(name, _) => Some((name.clone(), 0)),
        // Sign-extension preserves the signed value; recurse transparently and
        // keep the INNER source width (which bounds the carrier's signed range).
        Formula::BvSignExt(inner, _) => bv_overflow_operand(inner),
        _ => None,
    }
}

/// The transparent `Int` carrier of a BV `IntToBv(Var/lit, w)` round-trip leaf:
/// the value a `BvToInt`/`IntToBv` pair carries unchanged. Returns the inner
/// `Formula` (an `Int` term) so the caller can re-emit it as a linear-Int term.
/// `None` for any non-`IntToBv` leaf, so the rewrites are fail-closed on shapes
/// they cannot model.
fn int_to_bv_carrier(f: &Formula) -> Option<&Formula> {
    match f {
        Formula::IntToBv(inner, _) => Some(inner.as_ref()),
        _ => None,
    }
}

/// The tightest constant upper bound `v ≤ U` present on Int variable `name`
/// across the conjuncts (from `Le(v, U)`, `Lt(v, U+1)`, `Ge(U, v)`, `Gt(U+1, v)`).
/// Used as the no-wrap / mask-identity gate witness. `None` if no upper bound is
/// present — then the rewrite fails closed (never assumes an unproven identity).
fn int_var_const_upper_bound(conjuncts: &[&Formula], name: &str) -> Option<i128> {
    let is_var = |f: &Formula| matches!(f, Formula::Var(n, Sort::Int) if n == name);
    let mut best: Option<i128> = None;
    let mut tighten = |u: i128| best = Some(best.map_or(u, |p: i128| p.min(u)));
    for &c in conjuncts {
        match c {
            // `v ≤ U`
            Formula::Le(a, b) if is_var(a) => {
                if let Some(u) = int_literal_value(b) {
                    tighten(u);
                }
            }
            // `U ≥ v`  ≡  `v ≤ U`
            Formula::Ge(a, b) if is_var(b) => {
                if let Some(u) = int_literal_value(a) {
                    tighten(u);
                }
            }
            // `v < U`  ⟹  `v ≤ U−1`
            Formula::Lt(a, b) if is_var(a) => {
                if let Some(u) = int_literal_value(b).and_then(|u| u.checked_sub(1)) {
                    tighten(u);
                }
            }
            // `U > v`  ≡  `v < U`  ⟹  `v ≤ U−1`
            Formula::Gt(a, b) if is_var(b) => {
                if let Some(u) = int_literal_value(a).and_then(|u| u.checked_sub(1)) {
                    tighten(u);
                }
            }
            _ => {}
        }
    }
    best
}

/// Whether a present bound proves `0 ≤ v` for Int variable `name` (a non-negative
/// lower bound). A usize index carries `Ge(v, 0)` / `Le(0, v)` as a type bound;
/// we REQUIRE it (never assume non-negativity) so the mask/shift identities — both
/// of which need `v ≥ 0` — only fire when it is established.
fn int_var_is_nonneg(conjuncts: &[&Formula], name: &str) -> bool {
    let is_var = |f: &Formula| matches!(f, Formula::Var(n, Sort::Int) if n == name);
    conjuncts.iter().any(|&c| match c {
        // `v ≥ L` with `L ≥ 0`
        Formula::Ge(a, b) => is_var(a) && int_literal_value(b).is_some_and(|l| l >= 0),
        // `L ≤ v` with `L ≥ 0`
        Formula::Le(a, b) => is_var(b) && int_literal_value(a).is_some_and(|l| l >= 0),
        // `v > L` with `L ≥ −1`  (⟹ `v ≥ L+1 ≥ 0`)
        Formula::Gt(a, b) => is_var(a) && int_literal_value(b).is_some_and(|l| l >= -1),
        // `L < v` with `L ≥ −1`
        Formula::Lt(a, b) => is_var(b) && int_literal_value(a).is_some_and(|l| l >= -1),
        _ => false,
    })
}

/// Trust (mask-to-type-max completeness): the EXACT constant value of Int variable
/// `name` when the present conjuncts pin it to a single value — either a direct
/// `Eq(name, Int(c))` (in either operand order) or matching upper and lower bounds
/// (`int_var_const_upper_bound == lower == c`). `None` when the value is not
/// pinned to a unique constant. Used only to resolve a MASK operand `2^k−1` that
/// is spelled as a variable (e.g. `let m = (1u32 << 8) - 1; x & m`), never to
/// weaken a soundness gate: the caller re-derives a mathematically-unconditional
/// bound from the resolved mask, so a wrong value can only fail to certify.
fn int_var_exact_const(conjuncts: &[&Formula], name: &str, depth: u32) -> Option<i128> {
    let is_var = |f: &Formula| matches!(f, Formula::Var(n, Sort::Int) if n == name);
    // Direct-literal equality first (cheapest, no recursion).
    for &c in conjuncts {
        if let Formula::Eq(a, b) = c {
            if is_var(a) {
                if let Some(v) = int_literal_value(b) {
                    return Some(v);
                }
            }
            if is_var(b) {
                if let Some(v) = int_literal_value(a) {
                    return Some(v);
                }
            }
        }
    }
    // Matching constant upper/lower bounds pin an exact value.
    if let (Some(ub), Some(lb)) =
        (int_var_const_upper_bound(conjuncts, name), int_var_const_lower_bound(conjuncts, name))
    {
        if ub == lb {
            return Some(ub);
        }
    }
    // `Eq(name, <expr>)` where `<expr>` folds to a constant — resolves the
    // `let m = (1<<k)−1; x & m` chain (`_3 = _7.0 = _4 − 1 = (1<<8) − 1`). Bounded
    // by `depth` so a cyclic equality set fails closed instead of looping.
    if depth == 0 {
        return None;
    }
    for &c in conjuncts {
        if let Formula::Eq(a, b) = c {
            let other = if is_var(a) {
                Some(b.as_ref())
            } else if is_var(b) {
                Some(a.as_ref())
            } else {
                None
            };
            if let Some(other) = other {
                // Do not recurse on the trivial `name = name` self-equality.
                if matches!(other, Formula::Var(n, Sort::Int) if n == name) {
                    continue;
                }
                if let Some(v) = mask_const_value(conjuncts, other, depth - 1) {
                    return Some(v);
                }
            }
        }
    }
    None
}

/// Trust (mask-to-type-max completeness): the tightest constant LOWER bound `v ≥ L`
/// present on Int variable `name` (mirror of [`int_var_const_upper_bound`]). Used
/// with the upper bound to pin an exactly-constant mask variable. `None` when no
/// lower bound is present.
fn int_var_const_lower_bound(conjuncts: &[&Formula], name: &str) -> Option<i128> {
    let is_var = |f: &Formula| matches!(f, Formula::Var(n, Sort::Int) if n == name);
    let mut best: Option<i128> = None;
    let mut tighten = |l: i128| best = Some(best.map_or(l, |p: i128| p.max(l)));
    for &c in conjuncts {
        match c {
            // `v ≥ L`
            Formula::Ge(a, b) if is_var(a) => {
                if let Some(l) = int_literal_value(b) {
                    tighten(l);
                }
            }
            // `L ≤ v`  ≡  `v ≥ L`
            Formula::Le(a, b) if is_var(b) => {
                if let Some(l) = int_literal_value(a) {
                    tighten(l);
                }
            }
            // `v > L`  ⟹  `v ≥ L+1`
            Formula::Gt(a, b) if is_var(a) => {
                if let Some(l) = int_literal_value(b).and_then(|l| l.checked_add(1)) {
                    tighten(l);
                }
            }
            // `L < v`  ≡  `v > L`  ⟹  `v ≥ L+1`
            Formula::Lt(a, b) if is_var(b) => {
                if let Some(l) = int_literal_value(a).and_then(|l| l.checked_add(1)) {
                    tighten(l);
                }
            }
            _ => {}
        }
    }
    best
}

/// Trust (mask-to-type-max completeness): recursion-depth cap for `mask_const_value`.
/// A `2^k − 1` mask lowers to at most `Sub(BvToInt(BvShl(IntToBv(1), IntToBv(k))), 1)`
/// (depth ~5) plus a one-hop `Eq`-chain to a named mask, so 12 is ample headroom and
/// bounds the fold work on any deeper/cyclic shape (which fails closed).
const MASK_FOLD_DEPTH: u32 = 12;

/// Trust (mask-to-type-max completeness): evaluate a MASK carrier expression to a
/// concrete constant, when it provably folds to one. Handles exactly the shapes a
/// `2^k − 1` type-max mask lowers to:
///   * a literal `Int(c)` / `UInt(c)`;
///   * a variable pinned to a constant by the present conjuncts
///     (`int_var_exact_const`) — the `let m = …; x & m` form;
///   * `Sub(a, b)` / `Add(a, b)` / `Mul(a, b)` of constant sub-expressions — the
///     `(1 << k) − 1` form;
///   * `BvToInt(BvShl(a, b, w), w, false)` with constant `a`, `b`, no wrap — the
///     `1u32 << 8` lowering.
/// Returns `None` for any shape it cannot fold. Bounded recursion depth caps the
/// work. Purely a value resolver — no soundness gate depends on it (the caller
/// gates on the resolved value being a genuine all-ones window and emits only a
/// mathematically-unconditional bound the clean kernel re-checks).
fn mask_const_value(conjuncts: &[&Formula], f: &Formula, depth: u32) -> Option<i128> {
    if depth == 0 {
        return None;
    }
    if let Some(v) = int_literal_value(f) {
        return Some(v);
    }
    match f {
        Formula::Var(name, Sort::Int) => int_var_exact_const(conjuncts, name, depth - 1),
        Formula::Sub(a, b) => {
            let a = mask_const_value(conjuncts, a, depth - 1)?;
            let b = mask_const_value(conjuncts, b, depth - 1)?;
            a.checked_sub(b)
        }
        Formula::Add(a, b) => {
            let a = mask_const_value(conjuncts, a, depth - 1)?;
            let b = mask_const_value(conjuncts, b, depth - 1)?;
            a.checked_add(b)
        }
        Formula::Mul(a, b) => {
            let a = mask_const_value(conjuncts, a, depth - 1)?;
            let b = mask_const_value(conjuncts, b, depth - 1)?;
            a.checked_mul(b)
        }
        // `1u32 << 8` lowers to an unsigned `BvToInt(BvShl(IntToBv(x), IntToBv(c)))`.
        Formula::BvToInt(inner, w, false) => match inner.as_ref() {
            Formula::BvShl(base, amount, shl_w) if shl_w == w => {
                let base = int_to_bv_carrier(base)
                    .and_then(|b| mask_const_value(conjuncts, b, depth - 1))?;
                let shift = int_to_bv_carrier(amount)
                    .and_then(|a| mask_const_value(conjuncts, a, depth - 1))?;
                // No-wrap gate: `0 ≤ shift < w ≤ 126` and `base · 2^shift < 2^w`.
                if shift < 0 || shift >= i128::from(*w) || *w == 0 || *w > 126 || base < 0 {
                    return None;
                }
                let scale = 1i128.checked_shl(shift as u32)?;
                let val = base.checked_mul(scale)?;
                (val < (1i128 << *w)).then_some(val)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Trust (mask-to-type-max completeness): whether `mask` is a concrete all-ones low
/// window `2^k − 1` that fits the BV width `w` (`0 ≤ mask ≤ 2^w − 1`). Shared gate
/// for the masked-value bound derivation. A value failing this is not a mask window
/// (the AND result is not bounded by it), so nothing is emitted — fail-closed.
fn mask_is_allones_window(mask: i128, w: u32) -> bool {
    if mask < 0 {
        return false;
    }
    // `mask + 1` is a power of two ⟺ the set bits form a contiguous low window.
    let Some(next) = (mask as u128).checked_add(1) else { return false };
    if next.count_ones() != 1 {
        return false;
    }
    let width_max = if w >= 127 { i128::MAX } else { (1i128 << w) - 1 };
    mask <= width_max
}

/// Bridge the two bitvector value-equality shapes into equivalent linear-Int
/// equalities, EACH gated on a no-wrap / mask-identity side condition that a
/// PRESENT bound proves — so the rewrite is emitted only when the identity
/// provably holds, and otherwise nothing is emitted (fail-closed).
///
/// Group (d) — masked low bits (`bitmask_index_guarded`):
///   `Eq(out, BvToInt(BvAnd(IntToBv(i, w), IntToBv(2^k−1, w), w), w, false))`
/// becomes `Eq(out, i)` IFF a present bound proves `0 ≤ i ≤ 2^k − 1` (i.e.
/// `i < 2^k`). For `0 ≤ i < 2^k`, `i & (2^k − 1) = i`: the mask is the all-ones
/// low-`k`-bit window, and `i`'s value already fits in those `k` bits, so the AND
/// is the identity. The `BvToInt(_, _, false)` (unsigned) of a value `< 2^k ≤ 2^w`
/// is that same value. We require BOTH `0 ≤ i` (non-negativity) AND `i ≤ 2^k − 1`;
/// if either is unproven we emit nothing (a larger `i` would have `i & (2^k−1) ≠
/// i`, so assuming the identity there would be UNSOUND).
///
/// Group (c) — left shift by a constant (`shift_reduction` shift VALUE):
///   `Eq(out, BvToInt(BvShl(IntToBv(x, w), IntToBv(c, w), w), w, false))`
/// becomes `Eq(out, x · 2^c)` IFF a present bound proves `0 ≤ x` and
/// `x · 2^c < 2^w` (no wrap). `BvShl(IntToBv(x,w), c, w) = (x · 2^c) mod 2^w`,
/// which equals `x · 2^c` exactly when `0 ≤ x · 2^c < 2^w` — then the unsigned
/// `BvToInt` reads back that exact non-negative value. The `Mul`/`Scaled` chain
/// node handles `x · const` downstream. If the no-wrap bound is absent we emit
/// nothing (the shift could wrap, so the identity would be UNSOUND).
///
/// SOUNDNESS. Each emitted `Eq` is a fact that holds under the obligation's OWN
/// hypotheses (the gating bound is one of the conjuncts), so adding it never
/// enlarges the model set — the synthesized system is equisatisfiable with (a
/// subset of) the original, and the clean kernel re-checks the resulting
/// refutation regardless. A mis-recognized or wrongly-gated shape can therefore
/// only FAIL to certify (the BV equality is dropped, the contradiction is not
/// reached), never mint an unsound certificate.
fn bv_mask_shift_rewrites(conjuncts: &[&Formula]) -> Vec<Formula> {
    let mut out = Vec::new();
    for &c in conjuncts {
        // Both shapes are `Eq(out_var, BvToInt(<bvexpr>, w, false))` (either operand
        // order — the router emits out-on-left, but Eq is symmetric).
        let Formula::Eq(lhs, rhs) = c else { continue };
        let (out_name, bv_inner, to_w) = match (lhs.as_ref(), rhs.as_ref()) {
            (Formula::Var(n, Sort::Int), Formula::BvToInt(inner, w, false)) => (n, inner, w),
            (Formula::BvToInt(inner, w, false), Formula::Var(n, Sort::Int)) => (n, inner, w),
            _ => continue,
        };
        let out_var = || Formula::Var(out_name.clone(), Sort::Int);

        match bv_inner.as_ref() {
            // Group (d): masked low bits `BvAnd(IntToBv(i, w), IntToBv(2^k−1, w), w)`.
            Formula::BvAnd(a, b, and_w) if and_w == to_w => {
                // Identify the (concrete-mask, value-carrier) operand pair — the mask
                // may be on either side of the commutative AND.
                let pair = |m: &Formula, val: &Formula| -> Option<Formula> {
                    let mask = int_to_bv_carrier(m).and_then(int_literal_value)?;
                    // GATE (a): the mask is a concrete all-ones low window `2^k − 1`
                    // (so `mask + 1` is a power of two and `mask ≥ 0`).
                    if mask < 0 || (mask as u128).checked_add(1)?.count_ones() != 1 {
                        return None;
                    }
                    // GATE (a'): the mask fits in the BV width — `2^k − 1 < 2^w` (so
                    // `k ≤ w`). Otherwise the mask literal itself would wrap mod 2^w
                    // and the `i < 2^k` bound would not bound `i` below `2^w`, so the
                    // unsigned read-back `i mod 2^w` could differ from `i`. With `mask
                    // < 2^w` AND `i ≤ mask`, we get `i < 2^w`, so `IntToBv(i,w)` and
                    // `BvToInt(·,w,false)` are both the identity on `i`.
                    let width_max = if *to_w >= 127 {
                        i128::MAX // 2^w − 1 saturates the i128 mask range; any concrete
                    // mask `2^k−1` we accept is ≤ i128::MAX, so it fits.
                    } else {
                        (1i128 << *to_w) - 1
                    };
                    if mask > width_max {
                        return None;
                    }
                    let carrier = int_to_bv_carrier(val)?;
                    let Formula::Var(iname, Sort::Int) = carrier else { return None };
                    // GATE (b): a present bound proves `i ≤ mask` (i.e. `i < 2^k`)…
                    let ub = int_var_const_upper_bound(conjuncts, iname)?;
                    if ub > mask {
                        return None;
                    }
                    // …and (c) `0 ≤ i` (mask identity needs non-negativity).
                    if !int_var_is_nonneg(conjuncts, iname) {
                        return None;
                    }
                    // Under `0 ≤ i ≤ 2^k − 1 < 2^w`, `i & (2^k − 1) = i` and the
                    // unsigned read-back is exact: emit `out = i`.
                    Some(Formula::Eq(Box::new(out_var()), Box::new(carrier.clone())))
                };
                if let Some(eq) = pair(a, b).or_else(|| pair(b, a)) {
                    out.push(eq);
                }
                // Group (e) — UNCONDITIONAL masked-value bound (mask-to-type-max
                // completeness). For `out = (v & (2^k − 1))` the result lies in
                // `[0, 2^k − 1]` for ANY `v`: the AND clears every bit ≥ k, so the
                // value has at most the low `k` bits set. With the mask window
                // `2^k − 1 < 2^w`, the unsigned read-back `BvToInt(·, w, false)` of a
                // value `< 2^k ≤ 2^w` is exact, so `0 ≤ out ≤ 2^k − 1` holds
                // unconditionally — no bound on the value carrier `v` is needed
                // (unlike group (d)'s mask-IDENTITY, which requires `v < 2^k`). This
                // discharges a type-max cast `(x & 0xFF) as u8` (violation `out > 255`)
                // and a masked index `s[i & (len−1)]` against a `len`-sized slice.
                //
                // The mask operand may be a literal `IntToBv(2^k−1, w)` OR a variable
                // pinned to `2^k−1` by the present conjuncts (the `let m = (1<<k)−1;
                // x & m` form) — `mask_const_value` folds both. The value operand `v`
                // is UNCONSTRAINED (any BV expression), so no `int_to_bv_carrier` /
                // bound gate is applied to it.
                //
                // SOUNDNESS: `0 ≤ v & (2^k−1) ≤ 2^k−1` is a theorem of two's-complement
                // AND for a concrete all-ones low window, independent of `v`. The gate
                // (`mask_is_allones_window`) accepts ONLY such a window that fits the
                // width, so the emitted bound always holds; the clean kernel re-checks
                // the resulting refutation regardless. A mis-recognized mask (not a
                // window, or wider than `2^w`) fails the gate and emits nothing —
                // never an unsound fact. A NON-mask AND (e.g. `x & y` with symbolic
                // `y`) does not fold to a constant window, so it is skipped.
                let mask_window = |m: &Formula| -> Option<i128> {
                    // The AND operand is an `IntToBv(<int expr>, w)` round-trip leaf;
                    // peel it to the underlying Int expression the mask value lives in.
                    let carrier = int_to_bv_carrier(m)?;
                    let mask = mask_const_value(conjuncts, carrier, MASK_FOLD_DEPTH)?;
                    mask_is_allones_window(mask, *and_w).then_some(mask)
                };
                if let Some(mask) = mask_window(b).or_else(|| mask_window(a)) {
                    // Emit `0 ≤ out` and `out ≤ mask` as SEPARATE derived atoms so the
                    // downstream conjunct-oriented refutation steps (and the clean
                    // kernel re-check) each see them directly.
                    out.push(Formula::Ge(Box::new(out_var()), Box::new(Formula::Int(0))));
                    out.push(Formula::Le(Box::new(out_var()), Box::new(Formula::Int(mask))));
                }
            }
            // Group (c): left shift `BvShl(IntToBv(x, w), IntToBv(c, w), w)`.
            Formula::BvShl(base, amount, shl_w) if shl_w == to_w => {
                let Some(carrier) = int_to_bv_carrier(base) else { continue };
                let Formula::Var(xname, Sort::Int) = carrier else { continue };
                let Some(shift) = int_to_bv_carrier(amount).and_then(int_literal_value) else {
                    continue;
                };
                // GATE: concrete, in-range shift amount `0 ≤ c < w`, and a width
                // whose modulus `2^w` is a representable POSITIVE i128 (`w ≤ 126`, so
                // `1 << w` cannot reach the i128 sign bit). A `w` past that can't have
                // its no-wrap bound `x·2^c < 2^w` checked against a sound positive
                // modulus, so we fail closed (no real BV index/shift uses `w > 64`).
                if shift < 0 || shift >= i128::from(*shl_w) || *shl_w == 0 || *shl_w > 126 {
                    continue;
                }
                let Some(scale) = 1i128.checked_shl(shift as u32) else { continue };
                // `*shl_w ≤ 126` ⟹ `1 << w` is a positive power of two (no overflow).
                let modulus = 1i128 << *shl_w;
                // GATE: a present bound proves `0 ≤ x` and `x · 2^c < 2^w` (no wrap).
                let Some(ub) = int_var_const_upper_bound(conjuncts, xname) else { continue };
                if !int_var_is_nonneg(conjuncts, xname) {
                    continue;
                }
                let Some(max_val) = ub.checked_mul(scale) else { continue };
                if ub < 0 || max_val >= modulus {
                    continue; // could wrap (or negative) ⟹ identity unproven, fail closed.
                }
                // Under `0 ≤ x` and `x · 2^c < 2^w`, the shift does not wrap and the
                // unsigned read-back is exact: emit `out = x · 2^c`.
                out.push(Formula::Eq(
                    Box::new(out_var()),
                    Box::new(Formula::Mul(
                        Box::new(carrier.clone()),
                        Box::new(Formula::Int(scale)),
                    )),
                ));
            }
            _ => {}
        }
    }
    out
}

/// The closed signed interval `[lo, hi]` of an operand from the present `BvSLt`/
/// `BvSLe` bound atoms over it (mirrors `conjuncts_carry_bv_overflow_safe`'s
/// `bounds` closure on the router side). `BvSLt(c, name)` ⟹ `name > c`;
/// `BvSLt(name, c)` ⟹ `name < c`; non-strict via `BvSLe`. Strict bounds are
/// integer-tightened (`name > c ⟹ name ≥ c+1`). Returns `(Some(lo), Some(hi))`
/// only when BOTH ends are pinned by an explicit guard.
fn bv_signed_guard_bounds(conjuncts: &[&Formula], name: &str) -> (Option<i128>, Option<i128>) {
    let mut lo: Option<i128> = None;
    let mut hi: Option<i128> = None;
    let tighten_lo = |lo: &mut Option<i128>, v: i128| *lo = Some(lo.map_or(v, |p: i128| p.max(v)));
    let tighten_hi = |hi: &mut Option<i128>, v: i128| *hi = Some(hi.map_or(v, |p: i128| p.min(v)));
    for &c in conjuncts {
        let (strict, l, r) = match c {
            Formula::BvSLt(l, r, _) => (true, l, r),
            Formula::BvSLe(l, r, _) => (false, l, r),
            _ => continue,
        };
        // The bounded operand may be reached through a transparent sign-extension.
        let lname = bv_overflow_operand(l).map(|(n, _)| n);
        let rname = bv_overflow_operand(r).map(|(n, _)| n);
        match (l.as_ref(), r.as_ref(), lname.as_deref(), rname.as_deref()) {
            // `c <(=) name`  ⟹  lower bound.
            (Formula::BitVec { value, .. }, _, _, Some(rn)) if rn == name => {
                if strict {
                    if let Some(v) = value.checked_add(1) {
                        tighten_lo(&mut lo, v);
                    }
                } else {
                    tighten_lo(&mut lo, *value);
                }
            }
            // `name <(=) c`  ⟹  upper bound.
            (_, Formula::BitVec { value, .. }, Some(ln), _) if ln == name => {
                if strict {
                    if let Some(v) = value.checked_sub(1) {
                        tighten_hi(&mut hi, v);
                    }
                } else {
                    tighten_hi(&mut hi, *value);
                }
            }
            _ => {}
        }
    }
    (lo, hi)
}

/// A non-negative bitvector literal represented exactly at `width` (rather than
/// a malformed/out-of-range value whose truncation would change its meaning).
fn exact_unsigned_bv_literal(f: &Formula, width: u32) -> Option<i128> {
    let Formula::BitVec { value, width: literal_width } = f else { return None };
    if *literal_width != width || width == 0 || width > 128 || *value < 0 {
        return None;
    }
    if width < 127 && *value >= (1i128 << width) {
        return None;
    }
    Some(*value)
}

/// Whether `f` is exactly the named `width`-bit variable (not a same-spelling
/// Int/Bool variable or a variable carrying a different BV width).
fn is_exact_bv_var(f: &Formula, name: &str, width: u32) -> bool {
    matches!(f, Formula::Var(n, Sort::BitVec(w)) if n == name && *w == width)
}

/// The tightest present UNSIGNED upper bound `U` on the `width`-bit BV variable
/// `name` from a `BvULe(name, U)` or `BvULt(name, U+1)` conjunct (`U` an exact,
/// non-negative `width`-bit literal). `None` if no such bound is present.
fn bv_unsigned_upper_bound(conjuncts: &[&Formula], name: &str, width: u32) -> Option<i128> {
    let mut best: Option<i128> = None;
    for &c in conjuncts {
        let u = match c {
            Formula::BvULe(l, r, w) if *w == width && is_exact_bv_var(l, name, width) => {
                exact_unsigned_bv_literal(r, width)
            }
            Formula::BvULt(l, r, w) if *w == width && is_exact_bv_var(l, name, width) => {
                exact_unsigned_bv_literal(r, width).and_then(|v| v.checked_sub(1))
            }
            _ => None,
        };
        if let Some(u) = u {
            best = Some(best.map_or(u, |p| p.min(u)));
        }
    }
    best
}

/// The Int upper bound on an add-overflow summand `q` (a BV variable):
///
/// * a division summand `q = x / c` (`Eq(q, BvUDiv(x, c, w))`, `c > 0` literal,
///   `x` unsigned-bounded by `Ux`) gives the division-monotone bound `⌊Ux/c⌋`
///   (Euclidean division is monotone on the non-negative unsigned domain), or
/// * a bare unsigned-bounded summand gives its own `BvULe` bound.
///
/// `None` when neither is present — a summand with no known bound is treated as
/// possibly `UMAX`, so the sum may overflow and we must fail closed.
fn bv_unsigned_summand_upper_bound(conjuncts: &[&Formula], q: &str, width: u32) -> Option<i128> {
    for &c in conjuncts {
        let Formula::Eq(a, b) = c else { continue };
        let div = match (a.as_ref(), b.as_ref()) {
            (qv, d @ Formula::BvUDiv(..)) if is_exact_bv_var(qv, q, width) => d,
            (d @ Formula::BvUDiv(..), qv) if is_exact_bv_var(qv, q, width) => d,
            _ => continue,
        };
        let Formula::BvUDiv(x, cdiv, div_width) = div else { continue };
        if *div_width != width {
            continue;
        }
        let Formula::Var(xname, Sort::BitVec(x_width)) = x.as_ref() else {
            continue;
        };
        if *x_width != width {
            continue;
        }
        let cval = exact_unsigned_bv_literal(cdiv, width)?;
        if cval == 0 {
            continue;
        }
        let ux = bv_unsigned_upper_bound(conjuncts, xname, width)?;
        // ux ≥ 0 (bv_unsigned_upper_bound only returns non-negative literals) and
        // cval > 0, so div_euclid is the floor and monotone: x ≤ ux ⊢ x/c ≤ ⌊ux/c⌋.
        return Some(ux.div_euclid(cval));
    }
    // Bare unsigned-bounded summand (e.g. one operand of a guarded add).
    bv_unsigned_upper_bound(conjuncts, q, width)
}

/// Direct kernel discharge of an UNSIGNED wide-BV add-of-divisions no-overflow
/// obligation `bvugt(bvadd(a/cx, b/cy), UMAX)` — in `trust_types` the unsigned
/// `bvugt(sum, UMAX)` violation atom is `BvULt(UMAX, sum, w)`. The `(a/2)+(b/2)`
/// `usize` midpoint is the canonical case: `a/2 ≤ ⌊UMAX/2⌋`, `b/2 ≤ ⌊UMAX/2⌋`,
/// so `a/2 + b/2 ≤ UMAX-1 < UMAX` and the overflow can never fire.
///
/// SOUNDNESS — over-approximation, fail-closed (mirrors
/// [`certify_signed_bv_overflow_safe`]). Each summand's Int upper bound
/// (`bv_unsigned_summand_upper_bound`) is a SOUND over-bound of its true value —
/// a division bound `⌊Ux/c⌋` from the operand's own `BvULe` bound, or the
/// summand's own bound. We synthesize the linear-Int violation
/// `0 ≤ cx ≤ Bx ∧ 0 ≤ cy ≤ By ∧ cx+cy > UMAX` over FRESH carriers (each carrier's
/// `[0, B]` range ⊇ the summand's true range) and require `Bx+By ≤ UMAX` so the
/// synthesized system is UNSAT; the existing additive-lift refutation closes it
/// and the clean kernel re-checks the term. A genuinely-overflowing sum (no
/// division, or a bound too loose) leaves `Bx+By > UMAX`, so the synthesized
/// violation is SAT and we fail closed — never minting an unsound certificate.
/// The certificate is lineage-bound to the ORIGINAL obligation `identity`.
fn certify_unsigned_bv_div_sum_no_overflow(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    // Find the unsigned add-overflow atom `BvULt(UMAX, BvAdd(qx, qy, w), w)` — the
    // `bvult(UMAX, sum)` / `bvugt(sum, UMAX)` "sum exceeds type max" condition — as
    // a TOP-LEVEL conjunct of the (And-flattened) violation. SOUNDNESS requires
    // top-level: the certificate we mint proves the synthesized `cx+cy > UMAX`
    // UNSAT, which discharges the obligation only if `violation ⟹ synth`. That
    // holds when the overflow is conjoined at top level (`bounds ∧ (UMAX < sum)`),
    // but NOT when it is one disjunct of an `Or([underflow, overflow])` whose
    // sibling may be independently satisfiable — so an overflow nested inside an
    // `Or` fails closed here (a genuine two-sided check is the signed path's job).
    let mut target: Option<(String, String, i128, u32)> = None;
    for c in conjuncts {
        if let Formula::BvULt(lo, sum, width) = c
            && *width > 0
            && *width <= 128
            && let Some(umax) = exact_unsigned_bv_literal(lo, *width)
            && let Formula::BvAdd(qa, qb, add_width) = sum.as_ref()
            && *add_width == *width
            && let (
                Formula::Var(qx, Sort::BitVec(qx_width)),
                Formula::Var(qy, Sort::BitVec(qy_width)),
            ) = (qa.as_ref(), qb.as_ref())
            && *qx_width == *width
            && *qy_width == *width
        {
            target = Some((qx.clone(), qy.clone(), umax, *width));
            break;
        }
    }
    let (qx, qy, umax, width) = target?;
    let bx = bv_unsigned_summand_upper_bound(conjuncts, &qx, width)?;
    let by = bv_unsigned_summand_upper_bound(conjuncts, &qy, width)?;
    if bx < 0 || by < 0 || bx.checked_add(by)? > umax {
        return None;
    }
    let cx = format!("__cert_bvdiv_x_{qx}");
    let cy = format!("__cert_bvdiv_y_{qy}");
    let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
    let i = Formula::Int;
    let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
    let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
    let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
    let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
    let synth = Formula::And(vec![
        ge(v(&cx), i(0)),
        le(v(&cx), i(bx)),
        ge(v(&cy), i(0)),
        le(v(&cy), i(by)),
        gt(add(v(&cx), v(&cy)), i(umax)),
    ]);
    certify_with_identity(&synth, identity)
}

/// The `(name, width)` of a `BitVec`-sorted variable leaf (`Var`/`SymVar`), or
/// `None` for anything else — the raw-read operand test of the unsigned-BV
/// order-contradiction recognizer's whitelist.
fn bv_order_operand_var(f: &Formula) -> Option<(String, u32)> {
    match f {
        Formula::Var(name, Sort::BitVec(w)) => Some((name.clone(), *w)),
        Formula::SymVar(sym, Sort::BitVec(w)) => Some((sym.as_str().to_string(), *w)),
        _ => None,
    }
}

/// Direct kernel discharge of the pure UNSIGNED-BV ORDER-CONTRADICTION family —
/// the in-bounds re-assert a guarded literal-length index emits
/// (`if idx < K { a[idx] }`, the `verify_index_oob_safe` shape): the whole
/// conjunct pool is unsigned order atoms over one index variable — the
/// type-range facts `0 ≤u idx` and `idx ≤u uMAX`, (view-dropped) reified
/// `_b = (idx <u K)` copies, the dominating path guard `idx <u K`, and the
/// violation `K ≤u idx`. Guard and violation contradict outright under the
/// total unsigned order.
///
/// SOUNDNESS — exact unsigned-value lift, fail-closed (mirrors
/// [`certify_unsigned_bv_div_sum_no_overflow`]'s lift-to-Int strategy, but the
/// lift here is EXACT, not an over-approximation). Every atom the recognizer
/// admits compares a RAW `w`-bit variable read against a `w`-bit literal (the
/// WHITELIST below accepts nothing else), and on raw reads the unsigned BV
/// order coincides with the Int order of the unsigned values, which inhabit
/// `[0, 2^w-1]`. So any BV model of the violation maps (`idx` ↦ its unsigned
/// value) to an Int model of the synthesized system
/// `0 ≤ c ∧ c ≤ uMAX ∧ c < K ∧ K ≤ c` — each conjunct the Int image of a
/// PRESENT top-level conjunct, nothing invented. The system is handed to the
/// existing pipeline ([`certify_with_identity`]), whose kernel derivation — not
/// any solver label — proves the contradiction via the total order:
/// `Int.lt_of_le_of_lt K c K (K ≤ c) (c < K) : K < K`, closed by
/// `Int.NonNeg.mk 0 : K ≤ K` + `Int.lt_of_lt_of_le` + `Int.lt_irrefl K : False`
/// (the [`single_var_interval_refutation`] + [`refute_false_atom`] steps), with
/// `finish_certificate`'s ay UNSAT cross-check and clean-kernel re-check as
/// backstops. Hence the BV violation is UNSAT a fortiori.
///
/// WHITELIST (fail-closed). Every pool conjunct must be an unsigned order atom
/// (`BvULt`/`BvULe`) over variable/literal leaves, or a reified
/// `Eq(_b, <such atom>)`. ANY BV arithmetic (`BvAdd`/`BvSub`/`BvMul`/`BvUDiv`/
/// shifts/masks/…), extract/concat/extension, conversion, or SIGNED comparison
/// anywhere in the pool declines: a derived operand's unsigned read-back need
/// not equal its Int expression (wrap-around), so the value lift would be
/// unjustified there. Declining is always sound — the obligation records
/// `Trusted`, never a false `Certified`.
fn certify_unsigned_bv_order_contradiction(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    // WHITELIST gate: pure unsigned order atoms over raw-read/literal operands
    // (plus their Bool reifications — normally already dropped from the view),
    // and NOTHING else anywhere in the pool.
    let leaf_ok = |f: &Formula| -> bool {
        matches!(f, Formula::BitVec { .. }) || bv_order_operand_var(f).is_some()
    };
    let unsigned_order_atom = |f: &Formula| -> bool {
        match f {
            Formula::BvULt(a, b, _) | Formula::BvULe(a, b, _) => leaf_ok(a) && leaf_ok(b),
            _ => false,
        }
    };
    let bool_var = |f: &Formula| -> bool {
        matches!(f, Formula::Var(_, Sort::Bool) | Formula::SymVar(_, Sort::Bool))
    };
    for &c in conjuncts {
        let ok = unsigned_order_atom(c)
            || match c {
                Formula::Eq(a, b) => {
                    (bool_var(a) && unsigned_order_atom(b))
                        || (bool_var(b) && unsigned_order_atom(a))
                }
                _ => false,
            };
        if !ok {
            return None; // foreign operator / non-order conjunct — fail closed.
        }
    }

    // The path guard `idx <u K` with its EXACT contradicting violation
    // `K ≤u idx` (same variable, same literal, same width) both present as
    // top-level conjuncts. A wrong-direction (`idx ≤u K`) or different-constant
    // pair does not match and fails closed — so the satisfiable variants
    // (e.g. guard `idx <u 10` with `5 ≤u idx`) can never reach the synthesis.
    let mut target: Option<(String, i128, u32)> = None;
    for &c in conjuncts {
        if let Formula::BvULt(a, b, w) = c
            && let Some((name, vw)) = bv_order_operand_var(a)
            && let Formula::BitVec { value: k, width: kw } = b.as_ref()
            && vw == *w
            && *kw == *w
            && *k >= 0
        {
            let has_violation = conjuncts.iter().any(|&f| {
                if let Formula::BvULe(l, r, lw) = f
                    && let Formula::BitVec { value, width } = l.as_ref()
                    && let Some((rn, rw)) = bv_order_operand_var(r)
                {
                    *lw == *w && *width == *w && rw == *w && rn == name && *value == *k
                } else {
                    false
                }
            });
            if has_violation {
                target = Some((name, *k, *w));
                break;
            }
        }
    }
    let (name, k, w) = target?;

    // Width gate: `2^w - 1` must be a representable positive i128 so the range
    // side-conditions carry the exact type interval (every real index width is
    // ≤ 64; a zero or wider-than-126 width fails closed).
    if w == 0 || w > 126 {
        return None;
    }
    let umax = (1i128 << w) - 1;
    if k > umax {
        return None;
    }

    // The type-range facts `0 ≤u idx` and `idx ≤u uMAX` must be PRESENT — the
    // Int side-conditions below are their images; we never invent them.
    let has_nonneg = conjuncts.iter().any(|&f| {
        if let Formula::BvULe(l, r, lw) = f
            && let Formula::BitVec { value: 0, width } = l.as_ref()
            && let Some((rn, rw)) = bv_order_operand_var(r)
        {
            *lw == w && *width == w && rw == w && rn == name
        } else {
            false
        }
    });
    let has_upper = conjuncts.iter().any(|&f| {
        if let Formula::BvULe(l, r, lw) = f
            && let Some((ln, lvw)) = bv_order_operand_var(l)
            && let Formula::BitVec { value, width } = r.as_ref()
        {
            *lw == w && lvw == w && *width == w && ln == name && *value == umax
        } else {
            false
        }
    });
    if !has_nonneg || !has_upper {
        return None;
    }

    // Translate to the linear-Int violation over a fresh carrier and reuse the
    // Int pipeline; the certificate is lineage-bound to the ORIGINAL `identity`.
    let cvar = format!("__cert_bvord_{name}");
    let c = || Formula::Var(cvar.clone(), Sort::Int);
    let i = Formula::Int;
    let le = |p: Formula, q: Formula| Formula::Le(Box::new(p), Box::new(q));
    let lt = |p: Formula, q: Formula| Formula::Lt(Box::new(p), Box::new(q));
    let synth = Formula::And(vec![
        le(i(0), c()),    // image of the range fact `0 ≤u idx`
        le(c(), i(umax)), // image of the range fact `idx ≤u uMAX`
        lt(c(), i(k)),    // image of the path guard `idx <u K`
        le(i(k), c()),    // image of the violation `K ≤u idx`
    ]);
    certify_with_identity(&synth, identity)
}

/// Direct kernel discharge of the NEGATED-RETURN postcondition branch shape
/// (`abs`-style `if x < 0 { -x }` under `ensures result ≥ 0` — the
/// `verify_postcondition_safe` negative branch): the branch VC carries the
/// return relation `Eq(_0, Neg(x))`, the dominating guard `Lt(x, 0)`, the type
/// bounds `lo ≤ x ≤ hi`, and the violated ensures `Not(Ge(_0, 0))`. The `Neg`
/// relation is outside the generic linear-atom fragment (`term_to_kernel` has
/// no `Neg` arm), so without this recognizer the obligation records `Trusted`.
///
/// SOUNDNESS — entailed substitution, fail-closed. Every synthesized conjunct
/// is a logical consequence of PRESENT top-level conjuncts, so any model of the
/// violation maps (`x` ↦ its value) to a model of the synthesized system, and
/// that system's kernel-proved UNSAT-ness refutes the violation a fortiori:
///  * `lo ≤ c` / `c ≤ hi` — the present type bounds on `x`, verbatim;
///  * `c < 0` — the present guard, verbatim;
///  * `0 < c` — from the relation and the violated ensures: `_0 = -x` and
///    `¬(_0 ≥ 0)` (i.e. `_0 < 0`) give `-x < 0`, hence `0 < x` over the total
///    integer order (the sign flip is the recognizer's only meta step; the
///    contradiction itself is kernel-derived, and a mis-recognized shape can
///    only produce a SATISFIABLE synthesis that ay declines — fail closed).
/// The Int pipeline then derives the contradiction in the kernel — not from
/// any solver label: `Int.lt_trans 0 c 0 (0 < c) (c < 0) : 0 < 0`, closed by
/// `Int.NonNeg.mk 0 : 0 ≤ 0` + `Int.lt_of_lt_of_le` + `Int.lt_irrefl 0 : False`
/// (the [`single_var_interval_refutation`] + [`refute_false_atom`] steps), with
/// `finish_certificate`'s ay UNSAT cross-check and clean-kernel re-check as
/// backstops.
///
/// LEAKAGE GATE (fail-closed): every node of every pool conjunct must stay in
/// the pure linear-Int order/equality fragment (`Int`/`UInt` literals,
/// `Var`/`SymVar`, `Not`, `Eq`, the four order atoms, `Neg`). Any non-linear
/// (`Mul`/`Div`/`Rem`), float (`Fp*`), bitvector (`Bv*`), disjunctive, or
/// quantified node ANYWHERE declines — the pool is no longer the recognized
/// branch family. Declining is always sound (`Trusted`, never a false
/// `Certified`).
fn certify_negated_return_via_neg_bound(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    // Leakage gate over EVERY node of EVERY conjunct.
    for &c in conjuncts {
        let mut foreign = false;
        c.visit(&mut |sub| {
            if !matches!(
                sub,
                Formula::Int(_)
                    | Formula::UInt(_)
                    | Formula::Var(..)
                    | Formula::SymVar(..)
                    | Formula::Not(_)
                    | Formula::Eq(..)
                    | Formula::Lt(..)
                    | Formula::Le(..)
                    | Formula::Gt(..)
                    | Formula::Ge(..)
                    | Formula::Neg(_)
            ) {
                foreign = true;
            }
        });
        if foreign {
            return None;
        }
    }

    let is_named = |f: &Formula, n: &str| int_var_name(f).is_some_and(|v| v == n);
    let is_zero = |f: &Formula| matches!(f, Formula::Int(0));

    // The return relation `Eq(r, Neg(x))` (either orientation) over Int vars…
    for &c in conjuncts {
        let Formula::Eq(a, b) = c else { continue };
        let Some((r, x)) = (match (a.as_ref(), b.as_ref()) {
            (rv, Formula::Neg(xv)) => int_var_name(rv).zip(int_var_name(xv)),
            (Formula::Neg(xv), rv) => int_var_name(rv).zip(int_var_name(xv)),
            _ => None,
        }) else {
            continue;
        };

        // …the dominating negative guard `x < 0`…
        let guard = conjuncts
            .iter()
            .any(|&g| matches!(g, Formula::Lt(l, z) if is_named(l, &x) && is_zero(z)));
        // …the violated ensures `¬(r ≥ 0)` on the SAME return slot (a
        // wrong-direction violation — e.g. `¬(r ≤ 0)` — does not match: that
        // family is satisfiable and must stay uncertified)…
        let violation = conjuncts.iter().any(|&v| {
            matches!(v, Formula::Not(inner)
                if matches!(inner.as_ref(), Formula::Ge(l, z) if is_named(l, &r) && is_zero(z)))
        });
        // …and the present type bounds on `x` (`lo ≤ x ≤ hi`; `lo < 0 ≤ hi` so
        // the negative branch is non-degenerate — the i32 range in the
        // captured family).
        let lo = conjuncts.iter().find_map(|&f| match f {
            Formula::Ge(l, z) if is_named(l, &x) => int_literal_value(z),
            Formula::Le(l, z) if is_named(z, &x) => int_literal_value(l),
            _ => None,
        });
        let hi = conjuncts.iter().find_map(|&f| match f {
            Formula::Le(l, z) if is_named(l, &x) => int_literal_value(z),
            Formula::Ge(l, z) if is_named(z, &x) => int_literal_value(l),
            _ => None,
        });
        let (Some(lo), Some(hi)) = (lo, hi) else { continue };
        if !(guard && violation && lo < 0 && hi >= 0) {
            continue;
        }

        // Synthesize the entailed single-variable system over a fresh carrier
        // and reuse the Int pipeline (interval refutation + ay cross-check +
        // clean-kernel re-check); lineage-bound to the ORIGINAL `identity`.
        let cvar = format!("__cert_negret_{x}");
        let cx = || Formula::Var(cvar.clone(), Sort::Int);
        let i = Formula::Int;
        let le = |p: Formula, q: Formula| Formula::Le(Box::new(p), Box::new(q));
        let lt = |p: Formula, q: Formula| Formula::Lt(Box::new(p), Box::new(q));
        let synth = Formula::And(vec![
            le(i(lo), cx()), // type bound `lo ≤ x`, verbatim
            le(cx(), i(hi)), // type bound `x ≤ hi`, verbatim
            lt(cx(), i(0)),  // path guard `x < 0`, verbatim
            lt(i(0), cx()),  // `0 < x` — entailed by `_0 = -x ∧ ¬(_0 ≥ 0)`
        ]);
        return certify_with_identity(&synth, identity);
    }
    None
}

/// Find the FIRST signed wide-BV overflow target `BvAdd(x,y,w)` / `BvSub(x,y,w)`
/// anywhere in the conjunct tree whose operands are overflow-check leaves
/// (`bv_overflow_operand`). Returns `(x, y, source-bounds-width, w, is_add)`
/// where the source widths bound the operands' signed ranges (the inner width of
/// a sign-extension, else the operand's own width). Mirrors the target search in
/// the router's `conjuncts_carry_bv_overflow_safe`.
fn find_bv_overflow_target(
    conjuncts: &[&Formula],
) -> Option<(String, u32, String, u32, u32, bool)> {
    let mut target: Option<(String, u32, String, u32, u32, bool)> = None;
    for c in conjuncts {
        c.visit(&mut |sub| {
            if target.is_some() {
                return;
            }
            if let Formula::BvAdd(a, b, w) | Formula::BvSub(a, b, w) = sub {
                if let (Some((x, wx)), Some((y, wy))) =
                    (bv_overflow_operand(a), bv_overflow_operand(b))
                {
                    target = Some((x, wx, y, wy, *w, matches!(sub, Formula::BvAdd(..))));
                }
            }
        });
        if target.is_some() {
            break;
        }
    }
    target
}

/// The signed `[min, max]` of a `w`-bit two's-complement integer (`w ≤ 128`).
fn signed_width_range(w: u32) -> (i128, i128) {
    if w >= 128 { (i128::MIN, i128::MAX) } else { (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1) }
}

/// The signed result `BvAdd(x,y,w)` / `BvSub(x,y,w)` of a wide-BV overflow check
/// cannot overflow `[i_w_min, i_w_max]` — certify it by translating to a
/// linear-Int disjunctive contradiction and reusing the existing additive-lift
/// refutation (`certify_disjunctive_contradiction`).
///
/// Recognized shape (the fixtures `i128_guarded_add`, `i128_widened_sub`,
/// `i128_shift_accumulator`): an `BvAdd`/`BvSub(x, y, w)` whose operands carry a
/// closed signed bound — either an explicit `BvSLt`/`BvSLe` guard interval, or
/// the inherent `[-2^(sw-1), 2^(sw-1)-1]` of a `sw→w` sign-extension — plus the
/// carry-bit overflow disjunction over the result. The exact carry encoding is
/// NOT decoded: under the bound hypotheses it is equivalent to "the signed result
/// is outside `[i_w_min, i_w_max]`", which we model as the closed linear-Int
/// disjunction `Or([x±y < i_w_min, x±y > i_w_max])`.
///
/// We do NOT prove that equivalence in the kernel; instead we discharge the
/// STRONGER, structurally-simpler obligation
///   `x ∈ [xlo,xhi] ∧ y ∈ [ylo,yhi] ⟹ ¬(x±y < i_w_min ∨ x±y > i_w_max)`,
/// which the existing additive-lift chain proves and the clean kernel re-checks.
///
/// SOUNDNESS — over-approximation, fail-closed.
///  * Bound translation: each `BvSLt/BvSLe` guard atom (and each sign-extension's
///    inherent range) is a SOUND signed bound on the operand's mathematical value
///    — these only NARROW the operand's range. We use ONLY present guards, so we
///    never invent a tighter bound than the obligation provides.
///  * Carry→Int mapping: we REPLACE the carry-bit disjunction with the Int
///    overflow disjunction `Or([x±y<min, x±y>max])`. The synthesized Int violation
///    we refute is `bounds ∧ Or([...])`. If this Int violation is UNSAT (which is
///    all we ever certify — the kernel re-checks it), then under the SAME bounds
///    the result `x±y` provably lies in `[min,max]`, i.e. no overflow — exactly
///    the safety fact. The original carry-bit overflow assertion is at most this
///    Int disjunction (it fires only when the signed result leaves `[min,max]`),
///    so proving the Int disjunction impossible proves the carry assertion
///    impossible. The mapping can only make the obligation HARDER (we drop any
///    information beyond the operand bounds), so it is impossible to certify a
///    genuinely-overflowing add/sub: without tight enough bounds the Int `Or`
///    stays satisfiable and we fail closed (see the `fails_closed` tests).
///  * Sub via negation carrier: for subtraction we model `x - y` as `x + ny` over
///    a FRESH carrier `ny ∈ [-yhi, -ylo]` (the exact range of `-y`). Treating `ny`
///    as an independent free variable rather than tying it to `y` only ENLARGES
///    the feasible region (it forgets `ny = -y`), so a refutation of the relaxed
///    system refutes the original a fortiori. The additive-lift Sum path then
///    closes `x + ny`'s no-overflow exactly as for a real two-variable add.
///
/// KERNEL-REDUCER LIMIT (scope). The hand-rolled closed-atom refutation compares
/// the additive-lifted result bound against the i128 type extreme, whose
/// `Int.NonNeg.mk` witness the clean kernel reduces via `Int.sub`. The native
/// `Int`/`Nat` reducers only evaluate that subtraction for modest result
/// magnitudes; a result range wider than ~`2^20` leaves the witness type stuck.
/// We therefore guard on the result magnitude and fail closed beyond it — so this
/// arm certifies the small-result guarded/shift `i128` add cases but declines the
/// 64→128 widened sub (±2^64 range). Fail-closed is sound (records `Trusted`).
///
/// The whole thing is fail-closed: the kernel re-check (`finish_certificate`) is
/// the backstop, so a wrong bound or a mis-recognized shape can only FAIL to
/// certify, never mint an unsound `Certified`.
fn certify_signed_bv_overflow_safe(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let (x, wx, y, wy, w, is_add) = find_bv_overflow_target(conjuncts)?;
    if w == 0 || w > 128 {
        return None;
    }

    // Signed bound on each operand: the explicit guard interval if present, else
    // the inherent sign-extension range `[-2^(sw-1), 2^(sw-1)-1]`. A bare same-
    // width operand (sw == w, no guard) has only the full `[min,max]` type range,
    // whose add/sub CAN overflow — so we require a guard there and fail closed.
    let operand_bounds = |name: &str, src_w: u32| -> Option<(i128, i128)> {
        let (glo, ghi) = bv_signed_guard_bounds(conjuncts, name);
        // The sign-extension's inherent range (only when the source is strictly
        // narrower than the result width — that is what makes it informative).
        let ext = (src_w != 0 && src_w < w).then(|| signed_width_range(src_w));
        let lo = glo.or(ext.map(|(l, _)| l))?;
        let hi = ghi.or(ext.map(|(_, h)| h))?;
        Some((lo, hi))
    };
    let (xlo, xhi) = operand_bounds(&x, wx)?;
    let (ylo, yhi) = operand_bounds(&y, wy)?;
    let (min, max) = signed_width_range(w);

    if xlo > xhi || ylo > yhi {
        return None; // empty operand range — degenerate, fail closed.
    }

    // The signed result range `[result_lo, result_hi]` of `x op y`.
    let (result_lo, result_hi) = if is_add {
        (xlo.checked_add(ylo)?, xhi.checked_add(yhi)?)
    } else {
        // sub: `x - y` is minimized at `xlo - yhi`, maximized at `xhi - ylo`.
        (xlo.checked_sub(yhi)?, xhi.checked_sub(ylo)?)
    };

    // RESULT-MAGNITUDE BOUND (fail-closed). The refutation closes each overflow
    // disjunct with a closed atom comparing the additive-lifted result bound
    // (`result_lo`/`result_hi`) against the type extreme (`i_w_min`/`i_w_max`), whose
    // `Int.NonNeg.mk` witness the clean kernel def-eq-reduces via `Int.sub`. The clean
    // kernel's native `Int` reducer (`env::native_reducers_int`) is now arbitrary-
    // i128-magnitude (it reads/encodes Nat operands via the multi-limb
    // `bignat_to_u128`/`nat_lit_u128` path, not the former `u64` cap), so a result
    // range up to the full `i128` no longer stalls the witness reduction — the former
    // `~2^20` ceiling is lifted to `2^120`, which comfortably covers the 64→128
    // widened sub (±2^64). Kept (not removed) so the closing gap against an `i128`
    // extreme (`MAX − result_hi`, `result_lo − MIN`) still fits `i128` (the bound
    // keeps both `≤ 2^127`); a wider result fails closed (sound — `Trusted`, never a
    // false `Certified`, and the kernel re-check is the backstop regardless).
    const RESULT_MAGNITUDE_LIMIT: i128 = 1 << 120;
    if result_lo < -RESULT_MAGNITUDE_LIMIT || result_hi > RESULT_MAGNITUDE_LIMIT {
        return None;
    }

    // Build the linear-Int violation over fresh carriers (treated as free `Int`
    // vars) and refute it via the existing disjunctive/additive-lift machinery.
    // The overflow disjunction `Or([x±y < min, x±y > max])` is the exact carry
    // condition; the additive lift closes both disjuncts from the operand bounds.
    let cx = format!("__cert_bvovf_x_{x}");
    let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
    let i = Formula::Int;
    let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
    let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
    let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
    let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));

    // For subtraction, model `x - y` as `x + ny` over the negation carrier
    // `ny ∈ [-yhi, -ylo]` (exact range of `-y`); for addition use `y` directly.
    // Treating `ny` as an independent free var (forgetting `ny = -y`) only enlarges
    // the feasible region, so a refutation of the relaxed system is a fortiori a
    // refutation of the original (sound over-approximation).
    let (cy, ylo2, yhi2) = if is_add {
        (format!("__cert_bvovf_y_{y}"), ylo, yhi)
    } else {
        (format!("__cert_bvovf_ny_{y}"), yhi.checked_neg()?, ylo.checked_neg()?)
    };

    let sum = || add(v(&cx), v(&cy));
    let synth = Formula::And(vec![
        le(i(xlo), v(&cx)),
        le(v(&cx), i(xhi)),
        le(i(ylo2), v(&cy)),
        le(v(&cy), i(yhi2)),
        Formula::Or(vec![lt(sum(), i(min)), gt(sum(), i(max))]),
    ]);

    // Hand the synthesized Int violation to the existing disjunctive refutation;
    // its kernel re-check + ay cross-check are the soundness backstop, and the
    // certificate is lineage-bound to the ORIGINAL obligation's `identity`.
    let mut synth_conjuncts = Vec::new();
    collect_conjuncts(&synth, &mut synth_conjuncts);
    certify_disjunctive_contradiction(&synth_conjuncts, identity)
}

/// The closed-literal branch values `(a, b)` and index variable of an
/// `Eq(idx, Ite(_, Int(a), Int(b)))` conjunct: the SwitchInt-join fact that an
/// index local is `if c { a } else { b }`. `idx` must be an `Int` variable and
/// BOTH branch values closed integer literals (fail-closed otherwise — a
/// non-literal branch is not reduced). Either `Eq` operand order is accepted.
fn ite_index_branch_values(f: &Formula) -> Option<(String, i128, i128)> {
    let (var, ite) = match f {
        Formula::Eq(a, b) => match (a.as_ref(), b.as_ref()) {
            (Formula::Var(v, Sort::Int), ite @ Formula::Ite(..)) => (v.clone(), ite),
            (ite @ Formula::Ite(..), Formula::Var(v, Sort::Int)) => (v.clone(), ite),
            (Formula::SymVar(v, Sort::Int), ite @ Formula::Ite(..)) => {
                (v.as_str().to_string(), ite)
            }
            (ite @ Formula::Ite(..), Formula::SymVar(v, Sort::Int)) => {
                (v.as_str().to_string(), ite)
            }
            _ => return None,
        },
        _ => return None,
    };
    let Formula::Ite(_, then_v, else_v) = ite else { return None };
    let a = int_literal_value(then_v)?;
    let b = int_literal_value(else_v)?;
    Some((var, a, b))
}

/// Reduce a branch-merged `Ite`-valued index obligation to the form the existing
/// disjunctive refutation ([`certify_disjunctive_contradiction`]) closes.
///
/// SHAPE. The `merged_local_index` violation is `Or([B1, …, Bn])` (the SwitchInt
/// branch-join over the `if c {…} else {…}` that defines the index), where every
/// branch `Bi` is an `And` that flattens to the SAME supported order-atom context
/// (the index-aliasing equalities, the dominating slice-length guard, and the OOB
/// violation `idx ≥ len`) PLUS the branch-merge fact `Eq(idx, Ite(_, a, b))` with
/// closed-literal branch values `a, b`. The contradiction lives inside each
/// branch; the outer `Or` only joins the (identical) branches.
///
/// REDUCTION. Replace the whole violation by `sharedContext ∧ Or([idx ≤ a, idx ≤
/// b])`: the entailed branch-bound disjunction. Each disjunct `idx ≤ a` (an order
/// atom `parse_disjunct` accepts) joins the context `idx ≥ len > 2` into a closed
/// chain contradiction (`2 < len ≤ idx ≤ a` with `a ≤ 2`), so the existing
/// `Or.rec` case-split refutes it — and the clean kernel re-checks the result.
///
/// Returns a fully OWNED, self-contained reduced conjunct list (the shared
/// context, cloned, plus the synthesized branch-bound disjunction); the caller
/// borrows it into the `&[&Formula]` the disjunctive path expects. `None` —
/// fail-closed — unless EVERY branch is an `And` carrying the same `(idx, a, b)`
/// branch-merge fact and flattens to the SAME shared supported context, so the
/// proved core is entailed by every branch alike.
///
/// SOUNDNESS. `idx = Ite(c, a, b)` always equals `a` or `b`, so `idx ≤ a ∨ idx ≤
/// b` is a tautology under the merge fact — adding it never enlarges the model.
/// And the shared context is, by the cross-branch equality check, present in (a
/// subset of) EVERY branch, so refuting `sharedContext ∧ (idx ≤ a ∨ idx ≤ b)`
/// refutes every branch — hence the disjunction `Or([B1, …, Bn])` — a fortiori.
/// A mis-recognized shape can only fail the ay cross-check or the kernel re-check
/// and decline; it can never mint an unsound certificate.
fn ite_index_disjunction_reduction(conjuncts: &[&Formula]) -> Option<Vec<Formula>> {
    // Find the SwitchInt branch-join `Or` whose disjuncts are all `And` branches.
    let branches: &Vec<Formula> = conjuncts.iter().find_map(|&c| match c {
        Formula::Or(ds) if ds.len() >= 2 && ds.iter().all(|d| matches!(d, Formula::And(_))) => {
            Some(ds)
        }
        _ => None,
    })?;

    // Recursively flatten each branch into its supported order-atom conjuncts (the
    // ones `normalize_atom` accepts), and recover its branch-merge `(idx, a, b)`.
    // Require EVERY branch to carry the same merge fact and the same shared atom set.
    let mut shared_atoms: Option<Vec<Formula>> = None;
    let mut merge: Option<(String, i128, i128)> = None;
    for branch in branches {
        let mut flat: Vec<&Formula> = Vec::new();
        collect_conjuncts(branch, &mut flat);

        // The branch-merge fact must be present, with closed-literal branch values.
        let this_merge = flat.iter().find_map(|f| ite_index_branch_values(f))?;
        match &merge {
            None => merge = Some(this_merge),
            Some(prev) if *prev != this_merge => return None,
            Some(_) => {}
        }

        // Shared context: the order atoms this branch flattens to, in source order.
        // Dropping the merge `Eq` (its content is captured by the emitted `Or`) and
        // every non-order conjunct (Bool branch flag, reified `Bool = (…)`) — exactly
        // what `collect_supported_atoms` would keep, but tracked as whole conjuncts so
        // the disjunctive path re-normalizes them itself.
        let this_atoms: Vec<Formula> = flat
            .iter()
            .copied()
            .filter(|f| ite_index_branch_values(f).is_none() && normalize_atom(f).is_some())
            .cloned()
            .collect();
        match &shared_atoms {
            None => shared_atoms = Some(this_atoms),
            Some(prev) if *prev != this_atoms => return None,
            Some(_) => {}
        }
    }

    let (idx, a, b) = merge?;
    let mut reduced = shared_atoms?;
    if reduced.is_empty() {
        return None;
    }

    // Emit the entailed branch-bound disjunction `Or([idx ≤ a, idx ≤ b])`.
    let idx_var = || Formula::Var(idx.clone(), Sort::Int);
    reduced.push(Formula::Or(vec![
        Formula::Le(Box::new(idx_var()), Box::new(Formula::Int(a))),
        Formula::Le(Box::new(idx_var()), Box::new(Formula::Int(b))),
    ]));
    Some(reduced)
}

/// Certify a guarded-arithmetic disjunctive contradiction: a violation
/// `context ∧ Or([d1, …, dn])` where joining EACH disjunct with the conjunctive
/// context yields a transitive-chain contradiction (e.g. `if x>10 {x-10}` →
/// `x>10 ∧ x≤max ∧ Or([x-10<0, x-10>max])`: `x-10<0` shifts to `x<10` vs the
/// guard, `x-10>max` shifts to `x>max+10` vs the bound). Builds the `Or.rec`
/// case-split refutation, drives the ay cross-check, and re-checks with the
/// kernel. Fail-closed: a satisfiable disjunct (no chain) declines the whole.
/// Collect ALL free `Int` variable names anywhere in `f`, descending through
/// boolean connectives and comparisons (unlike [`collect_formula_int_vars`], which
/// stops at the arithmetic layer). Used for relevance-based context pruning.
fn collect_int_vars_deep(f: &Formula, out: &mut BTreeSet<String>) {
    match f {
        Formula::Var(n, Sort::Int) => {
            out.insert(n.clone());
        }
        Formula::SymVar(s, Sort::Int) => {
            out.insert(s.as_str().to_string());
        }
        Formula::Not(a) | Formula::Neg(a) => collect_int_vars_deep(a, out),
        Formula::And(cs) | Formula::Or(cs) => {
            for c in cs {
                collect_int_vars_deep(c, out);
            }
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => {
            collect_int_vars_deep(a, out);
            collect_int_vars_deep(b, out);
        }
        _ => {}
    }
}

/// Prune `context` to the conjuncts relevant to the disjunction's variables, plus any
/// variable-free conjuncts (kept conservatively). A conjunct sharing NO variable with
/// the disjunction cannot appear in a chain refutation of it, so dropping it is SOUND
/// — and it shrinks the augmented edge set below `refute_via_chain_edges`' 48-edge
/// cap, which a large surrounding context (membership / discriminant atoms over
/// unrelated temps) would otherwise blow. The kernel re-check is the backstop.
///
/// `transitive` selects the relevance closure:
///  * `true`  — the full variable-connected component (a conjunct is kept if it shares
///    a variable with the growing set; an equality `a = t` pulls `t`'s bounds in).
///  * `false` — 1-HOP: keep only conjuncts whose variables are a SUBSET of the
///    disjunction's DIRECT operand variables. This drops equality bridges (`_21 =
///    _22.0`) that would otherwise drag a hub of loosely-bounded temps into the
///    component, leaving exactly the operands' own (tight) bounds — the minimal context
///    a bounded-arithmetic overflow obligation needs.
fn relevant_context_conjuncts<'a>(
    disjuncts: &[Formula],
    context: &[&'a Formula],
    transitive: bool,
) -> Vec<&'a Formula> {
    let mut vars: BTreeSet<String> = BTreeSet::new();
    for d in disjuncts {
        collect_int_vars_deep(d, &mut vars);
    }
    if vars.is_empty() {
        return context.to_vec();
    }
    let cvars: Vec<BTreeSet<String>> = context
        .iter()
        .map(|&c| {
            let mut s = BTreeSet::new();
            collect_int_vars_deep(c, &mut s);
            s
        })
        .collect();
    if !transitive {
        // 1-hop: keep a conjunct whose variables all lie within the disjunction's
        // DIRECT operand set (or which is variable-free). No equality expansion.
        return context
            .iter()
            .enumerate()
            .filter(|(idx, _)| {
                cvars[*idx].is_empty() || cvars[*idx].iter().all(|v| vars.contains(v))
            })
            .map(|(_, &c)| c)
            .collect();
    }
    let mut keep = vec![false; context.len()];
    loop {
        let mut changed = false;
        for i in 0..context.len() {
            if keep[i] {
                continue;
            }
            // Keep a variable-free conjunct (a closed fact) or one sharing a var
            // with the growing connected component; absorb its vars into the set.
            if cvars[i].is_empty() || cvars[i].iter().any(|v| vars.contains(v)) {
                keep[i] = true;
                for v in &cvars[i] {
                    vars.insert(v.clone());
                }
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    context.iter().enumerate().filter(|(i, _)| keep[*i]).map(|(_, &c)| c).collect()
}

/// Build the shared conjunctive-context hypotheses + chain edges for the disjunctive
/// refutation from a set of (non-`Or`) context conjuncts. Returns `None` if a
/// supported context atom yields no chain edge (outside the refutable fragment).
fn build_disjunctive_context(
    context_conjuncts: &[&Formula],
) -> Option<(Vec<Hyp>, Vec<OrderEdge>, BTreeSet<String>)> {
    let (context_atoms, base_var_names) = collect_supported_atoms(context_conjuncts);
    let mut hyps: Vec<Hyp> = Vec::new();
    let mut context_edges: Vec<OrderEdge> = Vec::new();
    for atom in &context_atoms {
        let (a, b, strict) = match atom {
            Atom::Lt(a, b) => (*a, *b, true),
            Atom::Le(a, b) => (*a, *b, false),
        };
        let fvar = FVarId::new(HYP_FVAR_BASE + hyps.len() as u64);
        let edges = build_order_edges(a, b, strict, Expr::fvar(fvar));
        if edges.is_empty() {
            return None;
        }
        hyps.push(Hyp {
            smt: linear_atom_smt(atom)?,
            prop: linear_atom_prop(atom)?,
            fvar,
            name: format!("h_{}", hyps.len()),
        });
        context_edges.extend(edges);
    }
    Some((hyps, context_edges, base_var_names))
}

fn certify_disjunctive_contradiction(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    // Collect ALL `Or` conjuncts as candidates; the non-`Or` conjuncts form the
    // shared conjunctive context. The violation is a CONJUNCTION of the `Or`s, so a
    // refutation of `context ∧ (one Or)` refutes the whole a fortiori — dropping the
    // other conjoined `Or`s only WEAKENS the system, never unsound. We try each `Or`
    // as the refuted disjunction and accept the first that fully kernel-certifies.
    // (parse_disjunct rejects discriminant `Eq`-disjuncts — they normalize to two
    // order atoms — so only the genuine arithmetic-overflow `Or` is ever selected,
    // never a match/range discriminant `Or` that happens to share the conjunction.)
    let mut or_candidates: Vec<&Vec<Formula>> = Vec::new();
    let mut context_conjuncts: Vec<&Formula> = Vec::new();
    for &c in conjuncts {
        match c {
            Formula::Or(ds) => or_candidates.push(ds),
            other => context_conjuncts.push(other),
        }
    }
    if or_candidates.is_empty() {
        return None;
    }

    // Attempt 1 — FULL context (preserves prior behavior exactly): supported order
    // atoms → hypotheses (fvars) + chain edges, shared across every candidate `Or`.
    // Try each candidate as the refuted disjunction; accept the first that fully
    // kernel-certifies.
    if let Some((hyps, context_edges, base_var_names)) =
        build_disjunctive_context(&context_conjuncts)
    {
        for disjuncts in &or_candidates {
            if disjuncts.is_empty() {
                continue;
            }
            let mut cand_hyps = hyps.clone();
            let mut var_names = base_var_names.clone();
            if let Some(ev) = build_disjunctive_certificate(
                disjuncts,
                &context_edges,
                &mut cand_hyps,
                &mut var_names,
                identity,
            ) {
                return Some(ev);
            }
        }
    }

    // Attempt 2 — RELEVANCE-PRUNED fallback. A large surrounding context (membership
    // / discriminant atoms over unrelated temps — e.g. a nested-loop flattened index
    // `g[y*4+x]` drags in bounds on every loop var and discriminant) inflates the
    // augmented edge set past `refute_via_chain_edges`' 48-edge cap, so Attempt 1
    // fails on a refutation that is actually simple. Retry each candidate against a
    // context pruned to the disjunction's variable-connected component (SOUND — a
    // variable-disjoint conjunct cannot appear in a chain refutation; the kernel
    // re-checks the result). Only fires when pruning actually removed something.
    // Two pruning closures, tried in order of decreasing context: the variable-
    // connected component (`transitive`), then 1-HOP (only the disjunction's direct
    // operand bounds). The 1-hop pass drops equality bridges (`_21 = _22.0`,
    // `x = _13`) that link the operands to a hub of loosely-bounded temps — which keep
    // the connected component (and its augmented edge set) over the cap even after
    // Attempt 2 — leaving exactly the operands' own tight bounds.
    for transitive in [true, false] {
        for disjuncts in &or_candidates {
            if disjuncts.is_empty() {
                continue;
            }
            let pruned = relevant_context_conjuncts(disjuncts, &context_conjuncts, transitive);
            if pruned.len() == context_conjuncts.len() {
                continue; // nothing pruned → identical to Attempt 1, already tried.
            }
            if let Some((mut hyps, context_edges, mut var_names)) =
                build_disjunctive_context(&pruned)
            {
                if let Some(ev) = build_disjunctive_certificate(
                    disjuncts,
                    &context_edges,
                    &mut hyps,
                    &mut var_names,
                    identity,
                ) {
                    return Some(ev);
                }
            }
        }
    }
    None
}

/// Build a kernel-checked `CleanCic` for a single candidate disjunction against the
/// already-built conjunctive context (`hyps` carries the context hypotheses;
/// `context_edges` the chain edges). Returns `None` if any disjunct is outside the
/// supported refutable shapes or the kernel re-check fails, so the caller can move on
/// to the next candidate `Or`.
fn build_disjunctive_certificate(
    disjuncts: &[Formula],
    context_edges: &[OrderEdge],
    hyps: &mut Vec<Hyp>,
    var_names: &mut BTreeSet<String>,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    // Disjuncts: each is a closed-false atom/equality, or an order atom refuted
    // against the context. A disjunct outside these shapes declines the whole.
    let mut parsed: Vec<Disjunct<'_>> = Vec::new();
    let mut disjunct_smts: Vec<String> = Vec::new();
    for di in disjuncts {
        let disjunct = parse_disjunct(di)?;
        if let DisjunctRefutation::ChainAtom { a, b, .. } = &disjunct.refutation {
            collect_formula_int_vars(a, var_names);
            collect_formula_int_vars(b, var_names);
        }
        disjunct_smts.push(disjunct.smt.clone());
        parsed.push(disjunct);
    }

    let or_prop = build_or_prop(&parsed.iter().map(|d| d.prop.clone()).collect::<Vec<_>>())?;
    let or_fvar = FVarId::new(HYP_FVAR_BASE + hyps.len() as u64);
    let term = build_disjunctive_false(&parsed, context_edges, Expr::fvar(or_fvar))?;
    hyps.push(Hyp {
        smt: format!("(or {})", disjunct_smts.join(" ")),
        prop: or_prop,
        fvar: or_fvar,
        name: format!("h_{}", hyps.len()),
    });

    finish_certificate(hyps, &term, var_names, identity)
}

/// General integer disequality via order totality: a supported `a ≠ b`
/// conjunct (the direct-`Int` operand fragment of [`canonical_int_eq`] — free
/// vars / literals, the same gate as the direct-disequality path) entails
/// `a < b ∨ b < a` — trichotomy of the linear order on ℤ. A general
/// disequality IS a disjunction over the order (see
/// [`certify_direct_disequality_contradiction`]'s doc for why it sits outside
/// the Farkas atom fragment), so hand exactly that disjunction to the
/// disjunctive `Or.rec` engine: the split replaces the spent `≠` conjunct and
/// each branch must close against the REMAINING context. Covers e.g.
/// `a ≤ b ∧ b ≤ a ∧ a ≠ b`, where antisymmetry forces the equality without
/// any literal `Eq` conjunct for the direct path to pair with.
///
/// The split stays LOCAL to this recognizer (the shared normalization pool is
/// untouched), so no other recognizer ever sees the synthesized `Or` — in
/// particular the negated-return leakage gate, which declines on any
/// disjunction in view. Fail-closed by construction: either the `Or.rec`
/// engine declines (the failure mode regardless of satisfiability — the
/// engine is deliberately incomplete), or, when a term IS built for a system
/// that is actually satisfiable, the ay UNSAT cross-check and the
/// clean-kernel re-check in [`finish_certificate`] refuse the certificate.
fn certify_split_disequality_contradiction(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    for (spent, &conjunct) in conjuncts.iter().enumerate() {
        let Formula::Not(inner) = conjunct else { continue };
        let Formula::Eq(a, b) = inner.as_ref() else { continue };
        if canonical_int_eq(a, b).is_none() {
            continue;
        }
        let split =
            Formula::Or(vec![Formula::Lt(a.clone(), b.clone()), Formula::Lt(b.clone(), a.clone())]);
        let mut augmented: Vec<&Formula> = conjuncts
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != spent)
            .map(|(_, other)| *other)
            .collect();
        augmented.push(&split);
        if let Some(evidence) = certify_disjunctive_contradiction(&augmented, identity) {
            return Some(evidence);
        }
    }
    None
}

// ===========================================================================
// General multi-variable linear-integer Farkas refutation.
//
// The transitive-chain path ([`transitive_chain_refutation`]) only closes
// contradictions expressible as a chain of order edges between structurally
// matching endpoints, and its lifts scale by NON-NEGATIVE constants only. A
// genuine multi-variable Farkas combination with NEGATIVE coefficients — e.g.
// `x0 ≤ 1 ∧ 2·x0 − x1 ≥ −3 ∧ x1 ≥ 10`, refuted by the witness λ=(2,1,1) whose
// combination is the closed false `5 ≤ 0` — falls outside it.
//
// This path handles the general case. Each supported atom is an inequality
// `A ⋈ B` between linear-Int terms; we compute an exact non-negative integer
// Farkas witness `λ` (Fourier–Motzkin elimination, [`find_farkas_multipliers`])
// such that `Σ λ_i (B_i − A_i)` is a closed NEGATIVE constant `q`. We then build
// the kernel proof term:
//   * per row, `g_i : 0 ≤ B_i − A_i` (the `diff_lower_proof` shape:
//     `Int.add_le_add_right` + `Int.add_neg_self` rewrite);
//   * fold `λ_i` copies of each `g_i` with a binary `add_le_add` into
//     `0 ≤ Σ λ_i (B_i − A_i)` (repetition avoids introducing a scaling `Int.mul`);
//   * NORMALIZE the summed linear term to the closed literal `q` with a proof
//     `Eq TOTAL q`, built bottom-up from the Int ring lemmas ([`NormTerm`]);
//   * transport `0 ≤ TOTAL` along that equality to `0 ≤ q` and refute it
//     ([`refute_false_atom`], which fires only when `q < 0`).
//
// SOUNDNESS. The witness finder returns `None` on a satisfiable system (no
// contradiction row), so a real model is never refuted. The normalizer only
// EMITS a term; the emitted term is fully re-checked by the clean kernel in
// [`finish_certificate`] (and again over the serialized payload), so a
// normalizer bug can only FAIL to certify, never mint an unsound certificate.
// Every arithmetic step is `checked_*`; overflow or any unhandled shape fails
// closed.
// ===========================================================================

/// A linear form `Σ terms[v]·v + c` over Int variables (nonzero coefficients
/// only). Used both to find the Farkas witness and to track the canonical form
/// each [`NormTerm`] represents.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LinForm {
    terms: BTreeMap<String, i128>,
    c: i128,
}

impl LinForm {
    fn constant(c: i128) -> Self {
        LinForm { terms: BTreeMap::new(), c }
    }

    fn add_term(&mut self, v: &str, coeff: i128) -> Option<()> {
        if coeff == 0 {
            return Some(());
        }
        let slot = self.terms.entry(v.to_string()).or_insert(0);
        *slot = slot.checked_add(coeff)?;
        if *slot == 0 {
            self.terms.remove(v);
        }
        Some(())
    }

    fn add(&self, other: &LinForm) -> Option<LinForm> {
        let mut out = self.clone();
        for (v, c) in &other.terms {
            out.add_term(v, *c)?;
        }
        out.c = out.c.checked_add(other.c)?;
        Some(out)
    }

    fn sub(&self, other: &LinForm) -> Option<LinForm> {
        let mut out = self.clone();
        for (v, c) in &other.terms {
            out.add_term(v, c.checked_neg()?)?;
        }
        out.c = out.c.checked_sub(other.c)?;
        Some(out)
    }
}

/// Parse a `Formula` linear-Int TERM (the operand of an order atom) into its
/// [`LinForm`], or `None` if it leaves the linear fragment (fail closed). Mirrors
/// the shapes `term_to_kernel` accepts: bare `Var`, `Int`/`UInt` literals,
/// `Add`, and `Mul(literal, var)` (either operand order).
fn formula_linform(f: &Formula) -> Option<LinForm> {
    match f {
        Formula::Var(name, Sort::Int) => {
            let mut l = LinForm::constant(0);
            l.add_term(name, 1)?;
            Some(l)
        }
        Formula::SymVar(sym, Sort::Int) => {
            let mut l = LinForm::constant(0);
            l.add_term(sym.as_str(), 1)?;
            Some(l)
        }
        Formula::Int(n) => Some(LinForm::constant(*n)),
        Formula::UInt(n) if *n <= i128::MAX as u128 => Some(LinForm::constant(*n as i128)),
        Formula::Add(a, b) => formula_linform(a)?.add(&formula_linform(b)?),
        Formula::Mul(a, b) => {
            let (coeff, var) = linear_mul_operands(a, b)?;
            let name = int_var_name(var)?;
            let mut l = LinForm::constant(0);
            l.add_term(&name, coeff)?;
            Some(l)
        }
        _ => None,
    }
}

/// The key identifying a canonical part: a variable (ordered by name), or the
/// trailing constant (which sorts AFTER every variable).
#[derive(Clone, PartialEq, Eq)]
enum PartKey {
    Var(String),
    Const,
}

fn part_key_cmp(a: &PartKey, b: &PartKey) -> std::cmp::Ordering {
    use std::cmp::Ordering::*;
    match (a, b) {
        (PartKey::Var(x), PartKey::Var(y)) => x.cmp(y),
        (PartKey::Var(_), PartKey::Const) => Less,
        (PartKey::Const, PartKey::Var(_)) => Greater,
        (PartKey::Const, PartKey::Const) => Equal,
    }
}

/// One atomic summand of a canonical linear form: `coeff·v` (a `Int.mul v coeff`)
/// or the constant `coeff` (a bare literal).
#[derive(Clone)]
struct Part {
    key: PartKey,
    coeff: i128,
}

fn intlit(n: i128) -> Expr {
    int_literal_to_kernel(n).expect("i128 always encodes to a kernel Int literal")
}

fn int_mul_expr(a: Expr, b: Expr) -> Expr {
    const_app("Int.mul", [a, b])
}

fn le_bare(a: Expr, b: Expr) -> Expr {
    const_app("Int.le", [a, b])
}

fn part_expr(p: &Part) -> Expr {
    match &p.key {
        PartKey::Var(x) => int_mul_expr(chain_var_expr(x), intlit(p.coeff)),
        PartKey::Const => intlit(p.coeff),
    }
}

/// Right-folded `Int.add` of the parts' exprs (parts must be non-empty).
fn fold_parts(parts: &[Part]) -> Expr {
    let mut iter = parts.iter().rev();
    let mut acc = part_expr(iter.next().expect("fold_parts on empty parts"));
    for p in iter {
        acc = int_add_expr(part_expr(p), acc);
    }
    acc
}

// --- small Eq combinators over Int (all via the kernel `Eq.subst`/`Eq.refl`) ---

/// `Eq.trans` over Int: from `pab : Eq a b` and `pbc : Eq b c` build `Eq a c`.
fn eq_trans_int(a: Expr, b: Expr, c: Expr, pab: Expr, pbc: Expr) -> Expr {
    // motive `λt. Eq a t`; subst along `pbc : Eq b c` transports `pab : Eq a b`.
    let motive = Expr::lam(BinderInfo::Default, int_ty(), eq_int(a, Expr::bvar(0)));
    eq_subst_int(motive, b, c, pbc, pab)
}

/// Congruence under a unary Int operator `mk`: from `pab : Eq a b` build
/// `Eq (mk a) (mk b)`.
fn eq_congr_un(mk: &dyn Fn(Expr) -> Expr, a: Expr, b: Expr, pab: Expr) -> Expr {
    let motive = Expr::lam(BinderInfo::Default, int_ty(), eq_int(mk(a.clone()), mk(Expr::bvar(0))));
    eq_subst_int(motive, a.clone(), b, pab, eq_refl_int(mk(a)))
}

/// Congruence under a binary Int operator `mk`: from `p1 : Eq a1 b1` and
/// `p2 : Eq a2 b2` build `Eq (mk a1 a2) (mk b1 b2)`.
fn eq_congr_bin(
    mk: &dyn Fn(Expr, Expr) -> Expr,
    a1: Expr,
    a2: Expr,
    b1: Expr,
    b2: Expr,
    p1: Expr,
    p2: Expr,
) -> Expr {
    let lhs = mk(a1.clone(), a2.clone());
    // Rewrite the first operand a1 ↦ b1.
    let motive1 = Expr::lam(
        BinderInfo::Default,
        int_ty(),
        eq_int(lhs.clone(), mk(Expr::bvar(0), a2.clone())),
    );
    let s1 = eq_subst_int(motive1, a1, b1.clone(), p1, eq_refl_int(lhs.clone()));
    // Rewrite the second operand a2 ↦ b2.
    let motive2 = Expr::lam(BinderInfo::Default, int_ty(), eq_int(lhs, mk(b1, Expr::bvar(0))));
    eq_subst_int(motive2, a2, b2, p2, s1)
}

fn mk_add(a: Expr, b: Expr) -> Expr {
    int_add_expr(a, b)
}

/// A linear expression paired with the canonical parts it equals and a kernel
/// proof of that equality (`proof : Eq expr (fold_parts(parts))`). The building
/// blocks compose these so the top-level `TOTAL` carries a proof it equals its
/// canonical closed constant.
#[derive(Clone)]
struct NormTerm {
    expr: Expr,
    parts: Vec<Part>,
    proof: Expr,
}

/// Leaf: a bare Int variable `x` (coefficient 1). Canonical part is `Int.mul x 1`,
/// so the proof is `Eq.symm (Int.mul_one x)`.
fn nt_var(x: &str) -> NormTerm {
    let vx = chain_var_expr(x);
    let canon = int_mul_expr(vx.clone(), intlit(1));
    let mul_one = const_app("Int.mul_one", [vx.clone()]);
    let proof = eq_symm_int(canon.clone(), vx.clone(), mul_one);
    NormTerm { expr: vx, parts: vec![Part { key: PartKey::Var(x.to_string()), coeff: 1 }], proof }
}

/// Leaf: an integer literal `n`.
fn nt_lit(n: i128) -> NormTerm {
    let e = intlit(n);
    NormTerm {
        expr: e.clone(),
        parts: vec![Part { key: PartKey::Const, coeff: n }],
        proof: eq_refl_int(e),
    }
}

/// Leaf: a monomial `coeff·x` (from `Mul(literal, var)`), emitted variable-first
/// as `Int.mul x coeff` — already the canonical part shape, so the proof is refl.
/// A zero coefficient collapses to the constant `0` via `Int.mul_zero`.
fn nt_mul(coeff: i128, x: &str) -> NormTerm {
    let vx = chain_var_expr(x);
    let expr = int_mul_expr(vx.clone(), intlit(coeff));
    if coeff == 0 {
        let mul_zero = const_app("Int.mul_zero", [vx]);
        return NormTerm {
            expr,
            parts: vec![Part { key: PartKey::Const, coeff: 0 }],
            proof: mul_zero,
        };
    }
    NormTerm {
        expr: expr.clone(),
        parts: vec![Part { key: PartKey::Var(x.to_string()), coeff }],
        proof: eq_refl_int(expr),
    }
}

/// Negate a NormTerm: `Eq (Int.neg e) (fold (neg_parts parts))`.
fn nt_neg(nt: NormTerm) -> Option<NormTerm> {
    let neg = |e: Expr| int_neg_expr(e);
    let canon_in = fold_parts(&nt.parts);
    // Int.neg e = Int.neg (fold parts)  [congr on nt.proof]
    let congr = eq_congr_un(&neg, nt.expr.clone(), canon_in.clone(), nt.proof);
    // Int.neg (fold parts) = fold (neg_parts)  [structural, no re-merge]
    let (neg_parts, negc) = neg_canon_parts(&nt.parts)?;
    let expr = int_neg_expr(nt.expr);
    let neg_canon_in = int_neg_expr(canon_in);
    let proof = eq_trans_int(expr.clone(), neg_canon_in, fold_parts(&neg_parts), congr, negc);
    Some(NormTerm { expr, parts: neg_parts, proof })
}

/// `Eq (Int.neg (fold parts)) (fold (neg_parts parts))`. Negation preserves the
/// part structure (keys/order), so no re-merge is needed: distribute `Int.neg`
/// across the sum (`Int.neg_add`) and into each part (`Int.neg_mul_right` for a
/// monomial, closed reduction for the constant).
fn neg_canon_parts(parts: &[Part]) -> Option<(Vec<Part>, Expr)> {
    let (head, rest) = parts.split_first()?;
    let neg_head_part = Part { key: head.key.clone(), coeff: head.coeff.checked_neg()? };
    let head_e = part_expr(head);
    if rest.is_empty() {
        // Single part.
        let proof = match &head.key {
            PartKey::Var(x) => {
                // Int.neg (Int.mul x c) = Int.mul x (Int.neg c) ≡ Int.mul x (-c)
                const_app("Int.neg_mul_right", [chain_var_expr(x), intlit(head.coeff)])
            }
            PartKey::Const => {
                // Int.neg (lit c) reduces to lit (-c): refl at the target type.
                eq_refl_int(intlit(neg_head_part.coeff))
            }
        };
        return Some((vec![neg_head_part], proof));
    }
    let rf = fold_parts(rest);
    let neg_head_e = int_neg_expr(head_e.clone());
    let neg_rf = int_neg_expr(rf.clone());
    // Int.neg (head + rf) = (Int.neg head) + (Int.neg rf)
    let neg_add = const_app("Int.neg_add", [head_e.clone(), rf.clone()]);
    // Recurse on head (single) and rest.
    let (_, head_proof) = neg_canon_parts(std::slice::from_ref(head))?;
    let (neg_rest_parts, rest_proof) = neg_canon_parts(rest)?;
    let canon_neg_head = part_expr(&neg_head_part);
    let canon_neg_rest = fold_parts(&neg_rest_parts);
    let congr = eq_congr_bin(
        &mk_add,
        neg_head_e.clone(),
        neg_rf.clone(),
        canon_neg_head.clone(),
        canon_neg_rest.clone(),
        head_proof,
        rest_proof,
    );
    let mut out_parts = vec![neg_head_part];
    out_parts.extend(neg_rest_parts);
    let neg_sum = int_neg_expr(int_add_expr(head_e, rf));
    let mid = int_add_expr(neg_head_e, neg_rf);
    let target = fold_parts(&out_parts);
    let proof = eq_trans_int(neg_sum, mid, target, neg_add, congr);
    Some((out_parts, proof))
}

/// Add two NormTerms: `Eq (Int.add e1 e2) (fold merged)`.
fn nt_add(nt1: NormTerm, nt2: NormTerm) -> Option<NormTerm> {
    let c1 = fold_parts(&nt1.parts);
    let c2 = fold_parts(&nt2.parts);
    // Int.add e1 e2 = Int.add (fold p1) (fold p2)  [congr]
    let congr = eq_congr_bin(
        &mk_add,
        nt1.expr.clone(),
        nt2.expr.clone(),
        c1.clone(),
        c2.clone(),
        nt1.proof,
        nt2.proof,
    );
    // Int.add (fold p1) (fold p2) = fold merged  [merge]
    let (merged, merge_proof) = add_canon_parts(&nt1.parts, &nt2.parts)?;
    let expr = int_add_expr(nt1.expr, nt2.expr);
    let mid = int_add_expr(c1, c2);
    let proof = eq_trans_int(expr.clone(), mid, fold_parts(&merged), congr, merge_proof);
    Some(NormTerm { expr, parts: merged, proof })
}

/// `Eq (Int.add (fold p1) (fold p2)) (fold merged)` — merge two canonical part
/// lists by inserting each part of `p2` into `p1` in turn.
fn add_canon_parts(p1: &[Part], p2: &[Part]) -> Option<(Vec<Part>, Expr)> {
    let (a, rest) = p2.split_first()?;
    let c1 = fold_parts(p1);
    if rest.is_empty() {
        return insert_part(p1, a);
    }
    let rf = fold_parts(rest);
    let a_e = part_expr(a);
    // add C1 (add a rf) = add (add C1 a) rf   [Eq.symm add_assoc]
    let assoc = const_app("Int.add_assoc", [c1.clone(), a_e.clone(), rf.clone()]);
    let lhs = int_add_expr(c1.clone(), int_add_expr(a_e.clone(), rf.clone()));
    let reassoc_rhs = int_add_expr(int_add_expr(c1.clone(), a_e.clone()), rf.clone());
    // `Int.add_assoc` proves `Eq reassoc_rhs lhs`; symm gives `Eq lhs reassoc_rhs`.
    let s_assoc = eq_symm_int(reassoc_rhs.clone(), lhs.clone(), assoc);
    // insert a into p1: add C1 a = fold p1a
    let (p1a, ins_proof) = insert_part(p1, a)?;
    let fold_p1a = fold_parts(&p1a);
    // congr: add (add C1 a) rf = add (fold p1a) rf
    let congr = eq_congr_bin(
        &mk_add,
        int_add_expr(c1, a_e),
        rf.clone(),
        fold_p1a.clone(),
        rf.clone(),
        ins_proof,
        eq_refl_int(rf.clone()),
    );
    let after_congr = int_add_expr(fold_p1a, rf);
    // recurse: add (fold p1a) rf = fold final
    let (final_parts, rec_proof) = add_canon_parts(&p1a, rest)?;
    let target = fold_parts(&final_parts);
    let step1 = eq_trans_int(lhs, reassoc_rhs, after_congr.clone(), s_assoc, congr);
    let proof = eq_trans_int(
        int_add_expr(fold_parts(p1), fold_parts(p2)),
        after_congr,
        target,
        step1,
        rec_proof,
    );
    Some((final_parts, proof))
}

/// Merge two same-key parts. Returns the resulting proof
/// `Eq (Int.add head.expr p.expr) rhs` and, when the variable coefficients do
/// NOT cancel, the surviving part (`rhs = its expr`); on cancellation to zero
/// (`None`), `rhs = Int.zero`.
fn merge_two(head: &Part, p: &Part) -> Option<(Expr, Option<Part>)> {
    debug_assert!(part_key_cmp(&head.key, &p.key) == std::cmp::Ordering::Equal);
    let sum = head.coeff.checked_add(p.coeff)?;
    let lhs = int_add_expr(part_expr(head), part_expr(p));
    match &head.key {
        PartKey::Var(x) => {
            let vx = chain_var_expr(x);
            // Int.left_distrib x c1 c2 : x*(c1+c2) = x*c1 + x*c2 ; symm gives the merge.
            let distrib =
                const_app("Int.left_distrib", [vx.clone(), intlit(head.coeff), intlit(p.coeff)]);
            let combined =
                int_mul_expr(vx.clone(), int_add_expr(intlit(head.coeff), intlit(p.coeff)));
            let split = int_add_expr(
                int_mul_expr(vx.clone(), intlit(head.coeff)),
                int_mul_expr(vx.clone(), intlit(p.coeff)),
            );
            // symm distrib : (x*c1 + x*c2) = x*(c1+c2)
            let merge_to_combined = eq_symm_int(combined.clone(), split, distrib);
            if sum == 0 {
                // x*(c1+c2) = x*0 = 0   [Int.mul_zero], transported through combined.
                let mul_zero = const_app("Int.mul_zero", [vx.clone()]);
                let proof =
                    eq_trans_int(lhs, combined, int_zero_expr(), merge_to_combined, mul_zero);
                Some((proof, None))
            } else {
                // `combined` (x*(c1+c2)) is def-eq to the canonical `x*(sum)`, so the
                // symm-distrib proof already has the target type.
                let part = Part { key: PartKey::Var(x.clone()), coeff: sum };
                Some((merge_to_combined, Some(part)))
            }
        }
        PartKey::Const => {
            // (lit c1 + lit c2) reduces to lit (c1+c2): refl at the target type.
            let proof = eq_refl_int(intlit(sum));
            let _ = lhs;
            Some((proof, Some(Part { key: PartKey::Const, coeff: sum })))
        }
    }
}

/// Insert a single canonical part `p` into a canonical part list `p1`,
/// returning the new canonical list and `Eq (Int.add (fold p1) p.expr) (fold new)`.
fn insert_part(p1: &[Part], p: &Part) -> Option<(Vec<Part>, Expr)> {
    use std::cmp::Ordering::*;
    let (head, rest1) = p1.split_first()?;
    let c1 = fold_parts(p1);
    let p_e = part_expr(p);
    match part_key_cmp(&p.key, &head.key) {
        Less => {
            // p sorts before everything: add C1 p = add p C1  [Int.add_comm]
            let comm = const_app("Int.add_comm", [c1.clone(), p_e.clone()]);
            let mut out = vec![p.clone()];
            out.extend_from_slice(p1);
            Some((out, comm))
        }
        Equal => {
            if rest1.is_empty() {
                let (proof, kept) = merge_two(head, p)?;
                let out = match kept {
                    Some(part) => vec![part],
                    None => vec![Part { key: PartKey::Const, coeff: 0 }],
                };
                Some((out, proof))
            } else {
                // rest1 nonempty ⟹ head is a Var (the Const is always last).
                let rf = fold_parts(rest1);
                let head_e = part_expr(head);
                // add (add head rf) p
                //   = add head (add rf p)        [add_assoc]
                //   = add head (add p rf)        [congr add_comm rf p]
                //   = add (add head p) rf        [Eq.symm add_assoc]
                let s1 = const_app("Int.add_assoc", [head_e.clone(), rf.clone(), p_e.clone()]);
                let t0 = int_add_expr(int_add_expr(head_e.clone(), rf.clone()), p_e.clone());
                let t1 = int_add_expr(head_e.clone(), int_add_expr(rf.clone(), p_e.clone()));
                let comm = const_app("Int.add_comm", [rf.clone(), p_e.clone()]);
                let s2 = eq_congr_bin(
                    &mk_add,
                    head_e.clone(),
                    int_add_expr(rf.clone(), p_e.clone()),
                    head_e.clone(),
                    int_add_expr(p_e.clone(), rf.clone()),
                    eq_refl_int(head_e.clone()),
                    comm,
                );
                let t2 = int_add_expr(head_e.clone(), int_add_expr(p_e.clone(), rf.clone()));
                let assoc2 = const_app("Int.add_assoc", [head_e.clone(), p_e.clone(), rf.clone()]);
                let t3 = int_add_expr(int_add_expr(head_e.clone(), p_e.clone()), rf.clone());
                // `assoc2 : Eq t3 t2`; symm gives `Eq t2 t3`.
                let s3 = eq_symm_int(t3.clone(), t2.clone(), assoc2);
                let (merge_proof, kept) = merge_two(head, p)?;
                let merged_e = match &kept {
                    Some(part) => part_expr(part),
                    None => int_zero_expr(),
                };
                // congr: add (add head p) rf = add merged_e rf
                let s4 = eq_congr_bin(
                    &mk_add,
                    int_add_expr(head_e.clone(), p_e.clone()),
                    rf.clone(),
                    merged_e.clone(),
                    rf.clone(),
                    merge_proof,
                    eq_refl_int(rf.clone()),
                );
                let after_merge = int_add_expr(merged_e.clone(), rf.clone());
                // Chain s1..s4.
                let a01 = eq_trans_int(t0.clone(), t1.clone(), t2.clone(), s1, s2);
                let a013 = eq_trans_int(t0.clone(), t2, t3.clone(), a01, s3);
                let chained = eq_trans_int(t0, t3, after_merge.clone(), a013, s4);
                match kept {
                    Some(part) => {
                        let mut out = vec![part];
                        out.extend_from_slice(rest1);
                        Some((out, chained))
                    }
                    None => {
                        // add 0 rf = rf  [Int.zero_add]
                        let zero_add = const_app("Int.zero_add", [rf.clone()]);
                        let proof =
                            eq_trans_int(int_add_expr(c1, p_e), after_merge, rf, chained, zero_add);
                        Some((rest1.to_vec(), proof))
                    }
                }
            }
        }
        Greater => {
            if rest1.is_empty() {
                // add head p is already canonical [head, p]: refl.
                let out = vec![head.clone(), p.clone()];
                Some((out, eq_refl_int(int_add_expr(part_expr(head), p_e))))
            } else {
                let rf = fold_parts(rest1);
                let head_e = part_expr(head);
                // add (add head rf) p = add head (add rf p)   [add_assoc]
                let assoc = const_app("Int.add_assoc", [head_e.clone(), rf.clone(), p_e.clone()]);
                let lhs = int_add_expr(int_add_expr(head_e.clone(), rf.clone()), p_e.clone());
                let mid = int_add_expr(head_e.clone(), int_add_expr(rf.clone(), p_e.clone()));
                // recurse into rest1
                let (r2, rec_proof) = insert_part(rest1, p)?;
                let fold_r2 = fold_parts(&r2);
                let congr = eq_congr_bin(
                    &mk_add,
                    head_e.clone(),
                    int_add_expr(rf.clone(), p_e.clone()),
                    head_e.clone(),
                    fold_r2.clone(),
                    eq_refl_int(head_e.clone()),
                    rec_proof,
                );
                let after = int_add_expr(head_e.clone(), fold_r2);
                let proof = eq_trans_int(lhs, mid, after, assoc, congr);
                let mut out = vec![head.clone()];
                out.extend(r2);
                Some((out, proof))
            }
        }
    }
}

/// Translate a linear-Int `Formula` TERM into a [`NormTerm`] whose `expr` is
/// definitionally equal to `term_to_kernel(f)` (the shape the asserted hypothesis
/// prop uses), so the `g_i` derivation type-checks against the hypothesis fvar.
fn formula_to_normterm(f: &Formula) -> Option<NormTerm> {
    match f {
        Formula::Var(name, Sort::Int) => Some(nt_var(name)),
        Formula::SymVar(sym, Sort::Int) => Some(nt_var(sym.as_str())),
        Formula::Int(n) => Some(nt_lit(*n)),
        Formula::UInt(n) if *n <= i128::MAX as u128 => Some(nt_lit(*n as i128)),
        Formula::Add(a, b) => nt_add(formula_to_normterm(a)?, formula_to_normterm(b)?),
        Formula::Mul(a, b) => {
            let (coeff, var) = linear_mul_operands(a, b)?;
            let name = int_var_name(var)?;
            Some(nt_mul(coeff, &name))
        }
        _ => None,
    }
}

/// Build `add_le_add`: from `h1 : Int.le a b` and `h2 : Int.le c d` derive
/// `Int.le (a+c) (b+d)` (two one-sided monotonicity steps composed by
/// transitivity).
fn add_le_add(a: Expr, b: Expr, h1: Expr, c: Expr, d: Expr, h2: Expr) -> Expr {
    let step1 = const_app("Int.add_le_add_right", [a.clone(), b.clone(), h1, c.clone()]);
    let step2 = const_app("Int.add_le_add_left", [c.clone(), d.clone(), h2, b.clone()]);
    let ac = int_add_expr(a, c.clone());
    let bc = int_add_expr(b.clone(), c);
    let bd = int_add_expr(b, d);
    const_app("Int.le_trans", [ac, bc, bd, step1, step2])
}

/// Non-negative-integer Farkas witness over the `poslin` rows (`0 ≤ row_i`):
/// multipliers `λ ≥ 0` with `Σ λ_i·row_i` a NEGATIVE constant. Fourier–Motzkin
/// elimination tracking the multiplier combination; `None` if no contradiction
/// row is derivable (a satisfiable system) or the search leaves the safety caps
/// (fail closed). All arithmetic is checked.
fn find_farkas_multipliers(rows: &[LinForm]) -> Option<Vec<i128>> {
    const ROW_CAP: usize = 4000;
    const MULT_SUM_CAP: i128 = 200;
    let n = rows.len();

    #[derive(Clone)]
    struct FmRow {
        coeffs: BTreeMap<String, i128>,
        cst: i128,
        mult: Vec<i128>,
    }

    fn reduce(r: &mut FmRow) {
        let mut g: i128 = 0;
        let gcd = |mut a: i128, mut b: i128| {
            a = a.abs();
            b = b.abs();
            while b != 0 {
                let t = a % b;
                a = b;
                b = t;
            }
            a
        };
        for v in r.coeffs.values() {
            g = gcd(g, *v);
        }
        g = gcd(g, r.cst);
        for m in &r.mult {
            g = gcd(g, *m);
        }
        if g > 1 {
            for v in r.coeffs.values_mut() {
                *v /= g;
            }
            r.cst /= g;
            for m in &mut r.mult {
                *m /= g;
            }
        }
    }

    // Collect every variable appearing anywhere.
    let mut vars: BTreeSet<String> = BTreeSet::new();
    for r in rows {
        for v in r.terms.keys() {
            vars.insert(v.clone());
        }
    }

    let mut current: Vec<FmRow> = Vec::with_capacity(n);
    for (i, r) in rows.iter().enumerate() {
        let mut mult = vec![0i128; n];
        mult[i] = 1;
        let mut row = FmRow { coeffs: r.terms.clone(), cst: r.c, mult };
        // An immediately-constant contradictory row.
        if row.coeffs.is_empty() && row.cst < 0 {
            reduce(&mut row);
            if row.mult.iter().sum::<i128>() <= MULT_SUM_CAP {
                return Some(row.mult);
            }
        }
        current.push(row);
    }

    for v in &vars {
        let mut pos: Vec<&FmRow> = Vec::new();
        let mut neg: Vec<&FmRow> = Vec::new();
        let mut zero: Vec<FmRow> = Vec::new();
        for r in &current {
            match r.coeffs.get(v).copied().unwrap_or(0) {
                x if x > 0 => pos.push(r),
                x if x < 0 => neg.push(r),
                _ => zero.push(r.clone()),
            }
        }
        let mut next: Vec<FmRow> = zero;
        for p in &pos {
            for nn in &neg {
                let ap = p.coeffs.get(v).copied().unwrap_or(0); // > 0
                let an = nn.coeffs.get(v).copied().unwrap_or(0).checked_neg()?; // > 0
                // combined = an·p + ap·n  (coefficient on `v` cancels)
                let mut coeffs: BTreeMap<String, i128> = BTreeMap::new();
                for key in p.coeffs.keys().chain(nn.coeffs.keys()) {
                    if key == v {
                        continue;
                    }
                    if coeffs.contains_key(key) {
                        continue;
                    }
                    let cp = p.coeffs.get(key).copied().unwrap_or(0);
                    let cn = nn.coeffs.get(key).copied().unwrap_or(0);
                    let val = an.checked_mul(cp)?.checked_add(ap.checked_mul(cn)?)?;
                    if val != 0 {
                        coeffs.insert(key.clone(), val);
                    }
                }
                let cst = an.checked_mul(p.cst)?.checked_add(ap.checked_mul(nn.cst)?)?;
                let mut mult = vec![0i128; n];
                for i in 0..n {
                    mult[i] =
                        an.checked_mul(p.mult[i])?.checked_add(ap.checked_mul(nn.mult[i])?)?;
                }
                let mut row = FmRow { coeffs, cst, mult };
                reduce(&mut row);
                if row.coeffs.is_empty() {
                    if row.cst < 0 && row.mult.iter().sum::<i128>() <= MULT_SUM_CAP {
                        return Some(row.mult);
                    }
                    // A non-negative constant row is redundant; drop it.
                    continue;
                }
                next.push(row);
                if next.len() > ROW_CAP {
                    return None;
                }
            }
        }
        current = next;
    }

    // Any surviving all-constant contradiction row.
    for r in &current {
        if r.coeffs.is_empty() && r.cst < 0 && r.mult.iter().sum::<i128>() <= MULT_SUM_CAP {
            return Some(r.mult.clone());
        }
    }
    None
}

/// General multi-variable linear-integer Farkas refutation — see the module
/// banner. Returns a kernel term of type `False` in the hypothesis context, or
/// `None` (fail closed) on any unsupported shape, missing witness, or overflow.
fn multi_var_farkas_refutation(atoms: &[Atom<'_>], hyps: &[Hyp]) -> Option<Expr> {
    if atoms.len() != hyps.len() {
        return None;
    }
    // Row per atom: `poslin = linform(B) − linform(A)` with meaning `0 ≤ poslin`.
    let mut rows: Vec<LinForm> = Vec::with_capacity(atoms.len());
    let mut meta: Vec<(&Formula, &Formula, bool, Expr)> = Vec::with_capacity(atoms.len());
    for (atom, hyp) in atoms.iter().zip(hyps) {
        let (a, b, is_lt) = match atom {
            Atom::Le(a, b) => (*a, *b, false),
            Atom::Lt(a, b) => (*a, *b, true),
        };
        let la = formula_linform(a)?;
        let lb = formula_linform(b)?;
        rows.push(lb.sub(&la)?);
        meta.push((a, b, is_lt, Expr::fvar(hyp.fvar)));
    }
    // Only engage when there is a genuine multi-variable / negative-coefficient
    // combination; the single-variable and unit-chain paths run first.
    if !rows.iter().any(|r| r.terms.len() >= 2 || r.terms.values().any(|c| *c < 0)) {
        return None;
    }

    let mult = find_farkas_multipliers(&rows)?;

    // Build the `λ_i` copies of each `g_i : 0 ≤ B_i − A_i`.
    let mut contribs: Vec<(Expr, Expr, NormTerm)> = Vec::new();
    for (i, &m) in mult.iter().enumerate() {
        if m <= 0 {
            continue;
        }
        let (a, b, is_lt, fvar) = &meta[i];
        let n_a = formula_to_normterm(a)?;
        let n_b = formula_to_normterm(b)?;
        let neg_a = int_neg_expr(n_a.expr.clone());
        let posexpr = int_add_expr(n_b.expr.clone(), neg_a.clone());
        // h : Int.le A B  (weaken a strict `<` via Int.le_of_lt).
        let h = if *is_lt {
            const_app("Int.le_of_lt", [n_a.expr.clone(), n_b.expr.clone(), fvar.clone()])
        } else {
            fvar.clone()
        };
        // step1 : Int.le (A + -A) (B + -A)
        let step1 = const_app(
            "Int.add_le_add_right",
            [n_a.expr.clone(), n_b.expr.clone(), h, neg_a.clone()],
        );
        // Rewrite the LHS (A + -A) ↦ Int.zero via Int.add_neg_self A.
        let a_plus_nega = int_add_expr(n_a.expr.clone(), neg_a.clone());
        let motive =
            Expr::lam(BinderInfo::Default, int_ty(), le_bare(Expr::bvar(0), posexpr.clone()));
        let eq_anega = const_app("Int.add_neg_self", [n_a.expr.clone()]);
        let g = eq_subst_int(motive, a_plus_nega, int_zero_expr(), eq_anega, step1);
        // NormTerm for posexpr = B + (-A).
        let nt = nt_add(n_b, nt_neg(n_a)?)?;
        for _ in 0..m {
            contribs.push((posexpr.clone(), g.clone(), nt.clone()));
        }
    }
    if contribs.is_empty() {
        return None;
    }

    // Fold: `0 ≤ Σ posexpr` (repetition realizes the multipliers), and the
    // parallel NormTerm fold that proves the sum equals its canonical constant.
    let (total_expr, total_proof) = {
        let (last_e, last_g, _) = contribs.last().unwrap();
        let mut total = last_e.clone();
        let mut proof = last_g.clone();
        for (e, g, _) in contribs[..contribs.len() - 1].iter().rev() {
            proof = add_le_add(
                int_zero_expr(),
                e.clone(),
                g.clone(),
                int_zero_expr(),
                total.clone(),
                proof,
            );
            total = int_add_expr(e.clone(), total);
        }
        (total, proof)
    };

    let nt_total = {
        let (_, _, last_nt) = contribs.last().unwrap();
        let mut acc = last_nt.clone();
        for (_, _, nt) in contribs[..contribs.len() - 1].iter().rev() {
            acc = nt_add(nt.clone(), acc)?;
        }
        acc
    };

    // The combination must collapse to a single NEGATIVE closed constant.
    if nt_total.parts.len() != 1 {
        return None;
    }
    let part = &nt_total.parts[0];
    if !matches!(part.key, PartKey::Const) || part.coeff >= 0 {
        return None;
    }
    let q = part.coeff;

    // Transport `0 ≤ TOTAL` along `Eq TOTAL q` to `0 ≤ q`.
    let motive2 = Expr::lam(BinderInfo::Default, int_ty(), le_bare(int_zero_expr(), Expr::bvar(0)));
    let refuted = eq_subst_int(motive2, total_expr, intlit(q), nt_total.proof, total_proof);

    // Refute the false closed `0 ≤ q` (fires only because `q < 0`).
    let atom = ClosedOrderAtom { a: 0, b: q, is_lt: false };
    refute_false_atom(&atom, refuted)
}

/// Shared certificate tail: confirm ay refutes the asserted hypotheses, re-check
/// the kernel term proves `False` under an environment with the given free Int
/// variables, serialize, round-trip re-check, and emit the lineage-bound
/// `CleanCic`. Used by both the closed-constant path (empty `var_names`) and the
/// single-variable interval path.
fn finish_certificate(
    hyps: &[Hyp],
    term: &Expr,
    var_names: &BTreeSet<String>,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let env = build_env(var_names)?;

    // Defense in depth: ay must independently refute the asserted hypotheses.
    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
    for name in var_names {
        backend.add_raw_declaration(&format!("(declare-fun {} () Int)", encoded_var_name(name)));
    }
    for hyp in hyps {
        backend.assert_formula(&hyp.smt);
    }
    // Trust (parallel verify): serialize ONLY the raw ay solve on the shared
    // `trust_types::ay_exec_lock()` (ay's direct path is non-reentrant). The lock
    // drops at the end of this block — BEFORE the clean-kernel reconstruction /
    // re-check below, which is thread-safe by construction and must stay unlocked
    // so it parallelizes across verification threads.
    match {
        let _ay_guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());
        backend.check_sat()
    } {
        Ok(AyProofResult::Unsat { .. }) => {}
        _ => return None,
    }

    let ctx = build_ctx(hyps);
    if !kernel_checks_false(&env, ctx.clone(), term, var_names) {
        return None;
    }

    let term_bytes = serialize_term(term).ok()?;
    let reduced = reduced_context(&ctx);
    let context_bytes = serialize_context(&reduced).ok()?;
    if !payload_roundtrip_rechecks(var_names, &term_bytes, &context_bytes) {
        return None;
    }

    let lineage = lineage_digest(&term_bytes, &context_bytes, identity);
    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

fn push_order_hyps(
    conjunct: &Formula,
    hyps: &mut Vec<Hyp>,
    var_names: &mut BTreeSet<String>,
) -> Option<()> {
    for atom in normalize_atom(conjunct)? {
        if !collect_int_vars(&atom, var_names) {
            return None;
        }
        let smt = atom_to_smt(&atom)?;
        let prop = atom_to_kernel_prop(&atom)?;
        push_hyp(hyps, smt, prop);
    }
    Some(())
}

fn direct_disequality_refutation(
    eq_hyps: &[(EqKey, FVarId)],
    neq_hyps: &[(EqKey, FVarId, Expr)],
) -> Option<Expr> {
    for (neq_key, neq_fvar, lhs) in neq_hyps {
        if let Some((_, eq_fvar)) = eq_hyps.iter().find(|(eq_key, _)| eq_key == neq_key) {
            return Some(Expr::app(Expr::fvar(*neq_fvar), Expr::fvar(*eq_fvar)));
        }
        if neq_key.lhs == neq_key.rhs {
            return Some(Expr::app(Expr::fvar(*neq_fvar), eq_refl_int(lhs.clone())));
        }
    }
    None
}

fn canonical_int_eq<'a>(a: &'a Formula, b: &'a Formula) -> Option<CanonicalEq<'a>> {
    let a_key = int_term_key(a)?;
    let b_key = int_term_key(b)?;
    if a_key <= b_key {
        Some(CanonicalEq { lhs: a, rhs: b, key: EqKey { lhs: a_key, rhs: b_key } })
    } else {
        Some(CanonicalEq { lhs: b, rhs: a, key: EqKey { lhs: b_key, rhs: a_key } })
    }
}

fn int_term_key(f: &Formula) -> Option<IntTermKey> {
    match f {
        Formula::Var(name, Sort::Int) => Some(IntTermKey::Var(name.clone())),
        Formula::SymVar(sym, Sort::Int) => Some(IntTermKey::Var(sym.as_str().to_string())),
        Formula::Int(n) if int_literal_to_kernel(*n).is_some() => Some(IntTermKey::Lit(*n)),
        Formula::UInt(n) if *n <= u64::MAX as u128 => Some(IntTermKey::Lit(*n as i128)),
        _ => None,
    }
}

fn collect_direct_eq_vars(eq: &CanonicalEq<'_>, out: &mut BTreeSet<String>) -> Option<()> {
    (collect_term_vars(eq.lhs, out) && collect_term_vars(eq.rhs, out)).then_some(())
}

/// A supported integer *term*: a free `Int` variable or a non-negative literal.
/// Returns the kernel `Expr` for the term, or `None` if outside the fragment.
fn term_to_kernel(f: &Formula) -> Option<Expr> {
    match f {
        Formula::Var(name, Sort::Int) => {
            Some(Expr::const_(Name::from_string(&encoded_var_name(name)), vec![]))
        }
        Formula::SymVar(sym, Sort::Int) => {
            Some(Expr::const_(Name::from_string(&encoded_var_name(sym.as_str())), vec![]))
        }
        Formula::Int(n) => int_literal_to_kernel(*n),
        Formula::UInt(n) if *n <= u64::MAX as u128 => Some(int_ofnat(*n as u64)),
        // Linear sum term: ay reconstructs Farkas over `(+ ..)` zero-trust and
        // its translate_term emits the HAdd form, so we mirror it (left-folded).
        Formula::Add(a, b) => Some(hadd_int(term_to_kernel(a)?, term_to_kernel(b)?)),
        // Linear mul-by-constant: only literal×var / var×literal (var×var is
        // nonlinear → None). Emit variable-first to match ay's normalization.
        Formula::Mul(a, b) => {
            let (lit, var) = linear_mul_operands(a, b)?;
            Some(hmul_int(term_to_kernel(var)?, int_literal_to_kernel(lit)?))
        }
        _ => None,
    }
}

/// SMT-LIB2 rendering of a supported integer term.
fn term_to_smt(f: &Formula) -> Option<String> {
    match f {
        Formula::Var(name, Sort::Int) => Some(encoded_var_name(name)),
        Formula::SymVar(sym, Sort::Int) => Some(encoded_var_name(sym.as_str())),
        Formula::Int(n) => int_literal_to_smt(*n),
        Formula::UInt(n) if *n <= u64::MAX as u128 => Some(n.to_string()),
        Formula::Add(a, b) => Some(format!("(+ {} {})", term_to_smt(a)?, term_to_smt(b)?)),
        Formula::Mul(a, b) => {
            let (lit, var) = linear_mul_operands(a, b)?;
            Some(format!("(* {} {})", term_to_smt(var)?, int_literal_to_smt(lit)?))
        }
        _ => None,
    }
}

fn encoded_var_name(raw: &str) -> String {
    if is_simple_smt_symbol(raw) {
        return raw.to_string();
    }
    let mut encoded = String::from("trust_var_");
    for byte in raw.as_bytes() {
        encoded.push_str(&format!("{byte:02x}"));
    }
    encoded
}

fn is_simple_smt_symbol(raw: &str) -> bool {
    let mut chars = raw.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '_' | '-' | '.'))
}

/// Kernel proposition for a normalized atom.
fn atom_to_kernel_prop(atom: &Atom<'_>) -> Option<Expr> {
    match atom {
        Atom::Lt(a, b) => Some(lt_int(term_to_kernel(a)?, term_to_kernel(b)?)),
        Atom::Le(a, b) => Some(le_int(term_to_kernel(a)?, term_to_kernel(b)?)),
    }
}

/// SMT-LIB2 rendering of a normalized atom (consistent with [`atom_to_kernel_prop`]).
fn atom_to_smt(atom: &Atom<'_>) -> Option<String> {
    match atom {
        Atom::Lt(a, b) => Some(format!("(< {} {})", term_to_smt(a)?, term_to_smt(b)?)),
        Atom::Le(a, b) => Some(format!("(<= {} {})", term_to_smt(a)?, term_to_smt(b)?)),
    }
}

/// Collect free `Int` variable names from a normalized atom, returning `false`
/// if either term falls outside the supported fragment.
fn collect_int_vars(atom: &Atom<'_>, out: &mut BTreeSet<String>) -> bool {
    let (a, b) = match atom {
        Atom::Lt(a, b) | Atom::Le(a, b) => (a, b),
    };
    collect_term_vars(a, out) && collect_term_vars(b, out)
}

fn collect_term_vars(f: &Formula, out: &mut BTreeSet<String>) -> bool {
    match f {
        Formula::Var(name, Sort::Int) => {
            out.insert(name.clone());
            true
        }
        Formula::SymVar(sym, Sort::Int) => {
            out.insert(sym.as_str().to_string());
            true
        }
        Formula::Int(n) => int_literal_to_kernel(*n).is_some(),
        Formula::UInt(n) => *n <= u64::MAX as u128,
        Formula::Add(a, b) => collect_term_vars(a, out) && collect_term_vars(b, out),
        // Difference / negation are supported Int terms (a `Diff` chain node + the
        // `Int.sub`/`Int.neg` kernel reconstruction): keep an atom like the guarded
        // underflow `Sub(a,b) < 0` so it reaches the subtractive-lift chain instead
        // of being dropped by `collect_supported_atoms`.
        Formula::Sub(a, b) => collect_term_vars(a, out) && collect_term_vars(b, out),
        Formula::Neg(a) => collect_term_vars(a, out),
        Formula::Mul(a, b) => match linear_mul_operands(a, b) {
            Some((lit, var)) => int_literal_to_kernel(lit).is_some() && collect_term_vars(var, out),
            None => false,
        },
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Kernel environment / context / re-check helpers.
// ---------------------------------------------------------------------------

/// The shared lemma environment (no per-obligation variable axioms): Int order +
/// arithmetic lemmas and the `HAdd`/`HMul Int` instances. Building it is
/// relatively expensive (`init_rat_field_inst` in particular, ~1s), so it is
/// constructed ONCE process-wide and cloned cheaply for each obligation
/// ([`build_env`]). It is a pure superset of the previous `init_int_ord_lemmas`
/// environment: `init_rat_field_inst` pulls in `init_int_arith_lemmas`, which
/// supplies the Int ring lemmas (`Int.mul_one`/`Int.mul_zero` and the
/// commutative/monoid/distributive siblings) the multi-variable Farkas
/// normalizer ([`multi_var_farkas_refutation`]) uses to reduce a scaled linear
/// combination to a closed constant. Every added declaration is a sorry-free
/// constructive theorem, so this only widens the accepted-lemma set; each emitted
/// term is still fully kernel-re-checked.
fn build_base_env() -> Option<Environment> {
    // `Environment::new()` installs polymorphic `sorry`, `trustedArith`, and
    // `trustedAy`.  A consumer rechecker must not make those ambient authority
    // sources available to attacker-supplied proof bytes.
    let mut env = Environment::default();
    env.init_int_ord_lemmas().ok()?;
    env.init_rat_field_inst().ok()?;
    ensure_hadd(&mut env)?;
    ensure_hmul(&mut env)?;
    Some(env)
}

fn base_env() -> Option<&'static Environment> {
    static BASE_ENV: std::sync::OnceLock<Option<Environment>> = std::sync::OnceLock::new();
    BASE_ENV.get_or_init(build_base_env).as_ref()
}

/// Build the kernel environment: the shared lemma env plus a typed axiom for each
/// free variable. Returns `None` if any declaration is rejected (e.g. a variable
/// name colliding with a library declaration) — fail-closed.
fn build_env(var_names: &BTreeSet<String>) -> Option<Environment> {
    // Clone the memoized (process-global) lemma env — cheap — and add one axiom
    // per free Int variable. Producer and consumer share this, so the typing
    // context is identical on each side.
    let mut env = base_env()?.clone();
    for name in var_names {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&encoded_var_name(name)),
            level_params: vec![],
            type_: int_ty(),
        })
        .ok()?;
    }
    Some(env)
}

/// The local context the refutation is checked against: one declaration per
/// hypothesis, in binding order.
fn build_ctx(hyps: &[Hyp]) -> LocalContext {
    let mut ctx = LocalContext::new();
    for hyp in hyps {
        ctx.push_with_id(
            hyp.fvar,
            Name::from_string(&hyp.name),
            hyp.prop.clone(),
            BinderInfo::Default,
        );
    }
    ctx
}

/// Project a [`LocalContext`] to the serializable [`ReducedContext`] (decls
/// only), mirroring clean-auto's canonical `CertifiedPayload` context form.
fn reduced_context(ctx: &LocalContext) -> ReducedContext {
    ReducedContext {
        decls: ctx
            .iter()
            .map(|d| ReducedLocalDecl {
                id: d.id.as_u64(),
                name: d.name.clone(),
                type_: d.type_.clone(),
                // Trust: preserve let-binding values (clean-kernel LocalDecl grew
                // `value` for definitional locals) — replay must reconstruct the
                // SAME typing context that was certified, mirroring clean-auto's
                // canonical CertifiedPayload projection.
                value: d.value.clone(),
                bi: d.bi,
            })
            .collect(),
    }
}

/// Full kernel re-check (`infer_only = false`) that `term : False` in `ctx`,
/// plus a strict transitive axiom-closure check.
///
/// Typing alone proves only that the term is accepted in this environment. If
/// an ambient `sorry`/`trusted*` oracle is present, the kernel can type a
/// one-node inhabitant of `False`. The closure check below restricts proof
/// dependencies to obligation-local Int skolems and the Clean kernel's
/// foundational axiom base.
fn kernel_checks_false(
    env: &Environment,
    ctx: LocalContext,
    term: &Expr,
    obligation_vars: &BTreeSet<String>,
) -> bool {
    TypeChecker::with_context(env, ctx).check_type(term, &false_expr()).is_ok()
        && proof_axiom_closure_is_clean(env, term, obligation_vars)
}

/// Collect every constant name in an expression. Unknown expression forms fail
/// closed so a new kernel node cannot silently bypass the closure audit.
/// Free variables are permitted: their declarations come from the exact local
/// obligation context passed to the independent kernel check above.
fn collect_const_names(e: &Expr, out: &mut Vec<Name>) -> bool {
    use clean_kernel::expr::ExprKind;
    match e.kind() {
        ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => true,
        ExprKind::Const(name, _) => {
            out.push(name.clone());
            true
        }
        ExprKind::App(function, argument) => {
            collect_const_names(function, out) && collect_const_names(argument, out)
        }
        ExprKind::Lam(_, type_, body) | ExprKind::Pi(_, type_, body) => {
            collect_const_names(type_, out) && collect_const_names(body, out)
        }
        ExprKind::Let(_, type_, value, body, _) => {
            collect_const_names(type_, out)
                && collect_const_names(value, out)
                && collect_const_names(body, out)
        }
        ExprKind::Proj(name, _, inner) => {
            out.push(name.clone());
            collect_const_names(inner, out)
        }
        ExprKind::MData(_, inner) => collect_const_names(inner, out),
        _ => false,
    }
}

/// The Clean kernel's consistency-preserving foundational axiom residue. A
/// certificate may depend on these declarations, but never on an unguarded
/// oracle such as `sorry`, `trustedAy`, or `trustedArith`.
const FOUNDATIONAL_AXIOMS: [&str; 6] =
    ["Classical.choice", "propext", "Quot", "Quot.mk", "Quot.lift", "Quot.sound"];

/// Require the complete transitive constant closure of a proof to contain only
/// declared definitions, obligation-local Int skolems, and the foundational
/// Clean axioms above. Declaration types and values are traversed as well as the
/// submitted term, so an oracle cannot hide behind a reducible definition.
fn proof_axiom_closure_is_clean(
    env: &Environment,
    term: &Expr,
    obligation_vars: &BTreeSet<String>,
) -> bool {
    use clean_kernel::env::ConstantKind;

    let int = int_ty();
    let allowed_int_skolems = obligation_vars
        .iter()
        .map(|raw| Name::from_string(&encoded_var_name(raw)))
        .collect::<BTreeSet<_>>();
    let mut work = Vec::new();
    if !collect_const_names(term, &mut work) {
        return false;
    }
    let mut seen: BTreeSet<Name> = BTreeSet::new();
    while let Some(name) = work.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(info) = env.get_const(&name) else {
            return false;
        };
        if info.kind == ConstantKind::Axiom {
            let is_int_skolem = info.type_ == int && allowed_int_skolems.contains(&name);
            let is_foundational =
                FOUNDATIONAL_AXIOMS.iter().any(|allowed| name == Name::from_string(allowed));
            if !is_int_skolem && !is_foundational {
                return false;
            }
        }
        if !collect_const_names(&info.type_, &mut work) {
            return false;
        }
        if let Some(value) = &info.value
            && !collect_const_names(value, &mut work)
        {
            return false;
        }
    }
    true
}

/// Deserialize the serialized payload and independently re-check it against a
/// freshly rebuilt environment + context — the check an external consumer runs.
fn payload_roundtrip_rechecks(
    var_names: &BTreeSet<String>,
    term_bytes: &[u8],
    context_bytes: &[u8],
) -> bool {
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    let Ok(reduced): Result<ReducedContext, _> = deserialize_context(context_bytes) else {
        return false;
    };
    let Some(env) = build_env(var_names) else {
        return false;
    };
    kernel_checks_false(&env, reduced.into_context(), &term, var_names)
}

/// SHA-256 lineage digest binding the serialized term + context **and** the
/// obligation's stable identity (function, kind tag, location, violation
/// formula). Each component is length-prefixed (`u64` LE) in a fixed order so
/// the encoding is injective — no two distinct component tuples collide, and in
/// particular a certificate for one obligation cannot be reused for another
/// whose identity differs (witness-swap defense).
fn lineage_digest(
    term_bytes: &[u8],
    context_bytes: &[u8],
    identity: &ObligationIdentity,
) -> trust_ir::ProofDigest {
    let mut hasher = Sha256::new();
    hasher.update(LINEAGE_DOMAIN.as_bytes());
    // Fixed order, each field length-prefixed for an injective encoding.
    for field in [term_bytes, context_bytes, identity.encoded.as_slice()] {
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    let digest = hasher.finalize();
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&digest);
    trust_ir::ProofDigest::sha256(bytes)
}

#[cfg(test)]
mod tests {
    use trust_ir::ProofEvidence;
    use trust_types::{SourceSpan, VcKind};

    use super::*;

    /// A `VerificationCondition` whose *violation* is `x < 0 ∧ 0 < x` — a real
    /// QF_LIA contradiction. The router would assert this and expect `UNSAT`.
    fn contradiction_vc() -> VerificationCondition {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let zero = || Formula::Int(0);
        VerificationCondition {
            kind: VcKind::Assertion { message: "x bounded".to_string() },
            function: "demo".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::Lt(Box::new(x()), Box::new(zero())),
                Formula::Lt(Box::new(zero()), Box::new(x())),
            ]),
            contract_metadata: None,
        }
    }

    fn assert_formula_certificate_pairs(violation: &Formula) {
        let ProofEvidence::CleanCic { term, context, lineage, .. } =
            certify_violation(violation).expect("producer family must certify")
        else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            recheck_cleancic(&term, &context, &lineage, violation),
            "every honest formula-only producer family must pair with its public rechecker"
        );

        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "special producer pairing".to_string() },
            function: "special_producer_pairing".into(),
            location: SourceSpan::default(),
            formula: violation.clone(),
            contract_metadata: None,
        };
        let ProofEvidence::CleanCic { term, context, lineage, .. } =
            certify_vc(&vc).expect("full-VC producer family must certify")
        else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            recheck_vc_cleancic(&term, &context, &lineage, &vc),
            "every representative producer family must pair through the full-VC API"
        );
    }

    #[test]
    fn certifies_qf_lia_contradiction_and_payload_rechecks_to_false() {
        let vc = contradiction_vc();
        let evidence = certify_vc(&vc).expect("supported QF_LIA contradiction must certify");

        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, kernel_recheck } = evidence
        else {
            panic!("expected CleanCic evidence");
        };
        assert!(!term.is_empty(), "term bytes must be non-empty");
        assert!(!context.is_empty(), "context bytes must be non-empty");
        assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must bind the payload");
        assert!(
            recheck_vc_cleancic(&term, &context, &lineage, &vc),
            "certify_vc output must recheck through the full-VC consumer API"
        );
        assert!(
            kernel_recheck.is_none(),
            "QF evidence must not claim the unsupported TrustIR Farkas dispatcher"
        );

        // Independently re-check the serialized payload: deserialize and run the
        // clean kernel against a freshly rebuilt env+ctx. This is the de Bruijn
        // criterion — the SMT solver is outside the trusted base.
        let mut vars = BTreeSet::new();
        vars.insert("x".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "serialized CleanCic payload must re-check to False via the clean kernel"
        );
    }

    #[test]
    fn vc_recheck_binds_function_kind_location_and_formula() {
        let vc = contradiction_vc();
        let ProofEvidence::CleanCic { term, context, lineage, .. } =
            certify_vc(&vc).expect("full VC must certify")
        else {
            panic!("expected CleanCic evidence");
        };
        assert!(recheck_vc_cleancic(&term, &context, &lineage, &vc));

        let mut drifted = vc.clone();
        drifted.function = "other_function".into();
        assert!(!recheck_vc_cleancic(&term, &context, &lineage, &drifted));

        let mut drifted = vc.clone();
        drifted.kind = VcKind::Assertion { message: "other assertion".to_string() };
        assert!(!recheck_vc_cleancic(&term, &context, &lineage, &drifted));

        let mut drifted = vc.clone();
        drifted.location.file = "other.rs".to_string();
        drifted.location.line_start = 17;
        assert!(!recheck_vc_cleancic(&term, &context, &lineage, &drifted));

        // Normalization drops this tautology, so the same proof/context remain
        // kernel-valid; only the full formula identity gate may reject it.
        let mut drifted = vc.clone();
        drifted.formula = Formula::And(vec![Formula::Bool(true), vc.formula.clone()]);
        assert!(!recheck_vc_cleancic(&term, &context, &lineage, &drifted));

        let mut drifted = vc.clone();
        drifted.contract_metadata = Some(trust_types::ContractMetadata {
            source_contract_index: Some(7),
            ..trust_types::ContractMetadata::default()
        });
        assert!(!recheck_vc_cleancic(&term, &context, &lineage, &drifted));
    }

    #[test]
    fn formula_only_producer_and_rechecker_remain_paired() {
        let violation = contradiction_vc().formula;
        let ProofEvidence::CleanCic { term, context, lineage, .. } =
            certify_violation(&violation).expect("formula-only contradiction must certify")
        else {
            panic!("expected CleanCic evidence");
        };
        assert!(recheck_cleancic(&term, &context, &lineage, &violation));
    }

    #[test]
    fn recheck_rejects_relineaged_ambient_sorry_and_noncanonical_context() {
        let violation = contradiction_vc().formula;
        let normalized = normalize_violation(&violation).expect("supported contradiction");
        let conjuncts = normalized.view();
        let (atoms, var_names) = collect_supported_atoms(&conjuncts);
        let hyps = supported_hyps_from_atoms(&atoms).expect("supported hypotheses");
        let ctx = build_ctx(&hyps);
        let context =
            serialize_context(&reduced_context(&ctx)).expect("canonical obligation context");

        let mut ambient = build_env(&var_names).expect("constructive arithmetic env");
        let goal = false_expr();
        let sorry = install_adversarial_trust_marker(&mut ambient, &goal)
            .expect("install adversarial trusted marker");
        assert!(
            TypeChecker::with_context(&ambient, ctx.clone())
                .check_type(&sorry, &false_expr())
                .is_ok(),
            "non-vacuity: the raw kernel accepts ambient @sorry False"
        );
        assert!(
            !kernel_checks_false(&ambient, ctx, &sorry, &var_names),
            "the production gate must reject the ambient oracle"
        );
        let sorry_bytes = serialize_term(&sorry).expect("serialize sorry");
        let identity = ObligationIdentity::from_violation(&violation).expect("identity");
        let sorry_lineage = lineage_digest(&sorry_bytes, &context, &identity);
        assert!(!recheck_cleancic(&sorry_bytes, &context, &sorry_lineage, &violation,));

        let ProofEvidence::CleanCic { term, mut context, .. } =
            certify_violation(&violation).expect("honest proof")
        else {
            panic!("expected CleanCic evidence");
        };
        context.push(0);
        let relined = lineage_digest(&term, &context, &identity);
        assert!(!recheck_cleancic(&term, &context, &relined, &violation,));
    }

    #[test]
    fn axiom_closure_rejects_oracle_even_when_kernel_accepts_it() {
        let mut env = Environment::new();
        env.init_int_ord_lemmas().expect("logical base");
        for marker in ["sorry", "trustedAy", "trustedArith"] {
            assert!(
                env.get_const(&Name::from_string(marker)).is_some(),
                "control: Environment::new must register {marker}"
            );
            let term = Expr::app(
                Expr::const_(Name::from_string(marker), vec![Level::zero()]),
                false_expr(),
            );
            assert!(
                TypeChecker::with_context(&env, LocalContext::new())
                    .check_type(&term, &false_expr())
                    .is_ok(),
                "control: typing alone accepts {marker} False"
            );
            assert!(
                !proof_axiom_closure_is_clean(&env, &term, &BTreeSet::new()),
                "the transitive closure must reject {marker}"
            );
            assert!(
                !kernel_checks_false(&env, LocalContext::new(), &term, &BTreeSet::new()),
                "the production gate must reject {marker}"
            );
        }
    }

    #[test]
    fn axiom_closure_follows_definition_values_to_hidden_oracles() {
        let mut env = Environment::new();
        env.init_int_ord_lemmas().expect("logical base");
        let hidden =
            Expr::app(Expr::const_(Name::from_string("sorry"), vec![Level::zero()]), false_expr());
        let wrapper = Name::from_string("wrapped_oracle");
        env.add_decl(Declaration::Definition {
            name: wrapper.clone(),
            level_params: Vec::new(),
            type_: false_expr(),
            value: hidden,
            is_reducible: true,
        })
        .expect("the raw environment accepts an oracle-backed definition");
        let term = Expr::const_(wrapper, Vec::new());

        assert!(
            TypeChecker::with_context(&env, LocalContext::new())
                .check_type(&term, &false_expr())
                .is_ok(),
            "control: the raw kernel unfolds the hidden oracle"
        );
        assert!(
            !proof_axiom_closure_is_clean(&env, &term, &BTreeSet::new()),
            "the closure must traverse definition values"
        );
    }

    #[test]
    fn axiom_closure_allows_only_named_obligation_skolems_and_foundations() {
        let obligation_vars = BTreeSet::from(["x".to_string(), "encoded var".to_string()]);
        let env = build_env(&obligation_vars).expect("constructive obligation environment");

        for allowed in FOUNDATIONAL_AXIOMS {
            let name = Name::from_string(allowed);
            assert!(env.get_const(&name).is_some(), "missing foundational axiom {allowed}");
            assert!(
                proof_axiom_closure_is_clean(
                    &env,
                    &Expr::const_(name, Vec::new()),
                    &obligation_vars,
                ),
                "foundational axiom {allowed} must remain admissible"
            );
        }
        for raw in &obligation_vars {
            let name = Name::from_string(&encoded_var_name(raw));
            assert!(
                proof_axiom_closure_is_clean(
                    &env,
                    &Expr::const_(name, Vec::new()),
                    &obligation_vars,
                ),
                "the exact obligation skolem for {raw:?} must remain admissible"
            );
        }

        let mut hostile = env;
        let foreign = Name::from_string("foreign_int_axiom");
        hostile
            .add_decl(Declaration::Axiom {
                name: foreign.clone(),
                level_params: Vec::new(),
                type_: int_ty(),
            })
            .expect("declare foreign Int axiom");
        assert!(
            !proof_axiom_closure_is_clean(
                &hostile,
                &Expr::const_(foreign, Vec::new()),
                &obligation_vars,
            ),
            "an Int-typed axiom absent from the exact obligation variable set must be rejected"
        );
    }

    #[test]
    fn axiom_closure_preserves_honest_foundational_refutations() {
        let vc = contradiction_vc();
        assert!(
            certify_vc(&vc).is_some(),
            "the closure gate must retain honest arithmetic certification"
        );
    }

    #[test]
    fn certifies_qf_lia_contradiction_with_encoded_smt_variable_name() {
        let raw_name = "x) :: injected";
        let x = || Formula::Var(raw_name.to_string(), Sort::Int);
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "encoded variable".to_string() },
            function: "encoded_var".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
            ]),
            contract_metadata: None,
        };

        assert_eq!(term_to_smt(&x()).as_deref(), Some("trust_var_7829203a3a20696e6a6563746564"));
        let evidence = certify_vc(&vc).expect("encoded QF_LIA contradiction must certify");

        let trust_ir::ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut vars = BTreeSet::new();
        vars.insert(raw_name.to_string());
        assert!(payload_roundtrip_rechecks(&vars, &term, &context));
    }

    /// The real loop-invariant *initiation* VC shape that trust-vcgen emits for
    /// `#[loop_invariant(sum >= 0)]` with `sum == 0` at entry. Its violation is
    /// `sum == 0 ∧ ¬(sum ≥ 0)`, which normalizes to the QF_LIA contradiction
    /// `Eq(sum, 0) ∧ Lt(sum, 0)`. This is a Sort::Int obligation a real Rust
    /// function produces (unlike BitVec machine-int VCs).
    fn loop_invariant_initiation_vc() -> VerificationCondition {
        let sum = || Formula::Var("sum".to_string(), Sort::Int);
        VerificationCondition {
            kind: VcKind::LoopInvariantInitiation {
                invariant: "sum >= 0".to_string(),
                header_block: 0,
            },
            function: "sum_loop".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::Eq(Box::new(sum()), Box::new(Formula::Int(0))),
                Formula::Not(Box::new(Formula::Ge(Box::new(sum()), Box::new(Formula::Int(0))))),
            ]),
            contract_metadata: None,
        }
    }

    #[test]
    fn certifies_real_loop_invariant_initiation_shape() {
        // The bridge normalizes this real Sort::Int VC `Eq(sum,0) ∧ ¬(sum≥0)`
        // into `(sum≤0) ∧ (0≤sum) ∧ (sum<0)`. Splitting the equality into two
        // `≤` inequalities (rather than asserting a raw `=`) keeps ay's Farkas
        // lemma literals matched to the assumptions, so the contradiction
        // `0≤sum ∧ sum<0` reconstructs with ZERO residual trust and the clean
        // kernel re-checks the term to False. This is the first REAL provable
        // obligation class (loop invariants) certified end-to-end.
        let vc = loop_invariant_initiation_vc();
        let evidence = certify_vc(&vc).expect("loop-invariant initiation VC must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut vars = BTreeSet::new();
        vars.insert("sum".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "loop-invariant CleanCic payload must re-check to False via the clean kernel"
        );
    }

    #[test]
    fn certifies_negative_non_strict_lia_boundary() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let minus_one = || Formula::Int(-1);
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "negative bound".to_string() },
            function: "negative_bound".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::Ge(Box::new(x()), Box::new(minus_one())),
                Formula::Lt(Box::new(x()), Box::new(minus_one())),
            ]),
            contract_metadata: None,
        };

        assert_eq!(term_to_smt(&minus_one()).as_deref(), Some("(- 1)"));
        let evidence = certify_vc(&vc).expect("negative LIA boundary must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut vars = BTreeSet::new();
        vars.insert("x".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "negative-bound CleanCic payload must re-check to False via the clean kernel"
        );
    }

    #[test]
    fn certifies_nested_conjunction_lia_contradiction() {
        // Several VC producers wrap assumptions around an existing conjunction
        // (`And([env_formula, vc_formula])`). Flattening preserves the same
        // supported atom set instead of failing closed on the inner `And`.
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let viol = Formula::And(vec![
            Formula::And(vec![
                Formula::Le(Box::new(Formula::Int(0)), Box::new(x())),
                Formula::Le(Box::new(x()), Box::new(Formula::Int(10))),
            ]),
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
        ]);
        let evidence = certify_violation(&viol).expect("nested LIA conjunction must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut vars = BTreeSet::new();
        vars.insert("x".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "nested-conjunction CleanCic payload must re-check to False via the clean kernel"
        );
    }

    #[test]
    fn certifies_linear_int_contradiction_wrapped_in_bool_reifications() {
        // The REAL shape a guard-bounded slice index VC emits (verified end-to-end
        // via -Ztrust-dump=mir:<dir> on `if i < s.len() { s[i] }`): a linear-Int
        // contradiction `i < len ∧ _5 = len ∧ i ≥ _5` wrapped in reified Bool
        // equalities `_3 = (i < len)` that are OUTSIDE the linear fragment. The
        // bridge must DROP the Bool conjuncts and certify the Int contradiction
        // subset — this is what makes clean's Certified tier fire on real bounds
        // checks (which were previously only `Trusted`).
        let i = || Formula::Var("i".to_string(), Sort::Int);
        let len = || Formula::Var("s__slice_len".to_string(), Sort::Int);
        let five = || Formula::Var("_5".to_string(), Sort::Int);
        let viol = Formula::And(vec![
            // Reified Bool equality — unsupported, must be dropped.
            Formula::Eq(
                Box::new(Formula::Var("_3".to_string(), Sort::Bool)),
                Box::new(Formula::Lt(Box::new(i()), Box::new(len()))),
            ),
            Formula::Lt(Box::new(i()), Box::new(len())), // guard: i < len
            Formula::Eq(Box::new(five()), Box::new(len())), // _5 = len
            Formula::Ge(Box::new(i()), Box::new(five())), // violation: i ≥ _5
        ]);

        let evidence = certify_violation(&viol)
            .expect("linear-Int contradiction wrapped in Bool reifications must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut vars = BTreeSet::new();
        vars.insert("i".to_string());
        vars.insert("s__slice_len".to_string());
        vars.insert("_5".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "subset-certified payload must re-check to False via the clean kernel"
        );
        // The consumer re-check applies the SAME conjunct-dropping, so it accepts
        // the subset certificate against the FULL violation formula.
        assert!(
            recheck_cleancic(&term, &context, &lineage, &viol),
            "recheck_cleancic must accept a subset-certified obligation against its full violation"
        );
    }

    #[test]
    fn recheck_rejects_context_substituted_certificate() {
        // SOUNDNESS (consumer-side de Bruijn criterion): a `CleanCic` payload that
        // genuinely refutes ONE contradiction must NOT be accepted as evidence for
        // a DIFFERENT, satisfiable obligation that merely shares variable names.
        //
        // Mint a real certificate for the contradiction `x < 0 ∧ 0 < x` — its term
        // kernel-proves `False` from hypotheses {x<0, 0<x}.
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let zero = || Formula::Int(0);
        let contradiction = Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(zero())),
            Formula::Lt(Box::new(zero()), Box::new(x())),
        ]);
        let evidence = certify_violation(&contradiction)
            .expect("x<0 ∧ 0<x is a real QF_LIA contradiction and must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };

        // Present that payload for a SATISFIABLE obligation whose violation is just
        // `x < 0` (true at x = -1, so it is NOT UNSAT and must never be Certified),
        // with the lineage recomputed for this obligation's identity — exactly what
        // a forger controls.
        let satisfiable = Formula::Lt(Box::new(x()), Box::new(zero()));
        let forged_lineage = lineage_digest(
            &term,
            &context,
            &ObligationIdentity::from_violation(&satisfiable).expect("identity"),
        );

        assert!(
            !recheck_cleancic(&term, &context, &forged_lineage, &satisfiable),
            "a term refuting `x<0 ∧ 0<x` must NOT certify the satisfiable obligation `x<0`; \
             the kernel re-check must run against the obligation's own hypothesis context"
        );
    }

    #[test]
    fn fails_closed_on_satisfiable_obligation_with_unsupported_conjuncts() {
        // T-CERTIFY-CORRECT (the soundness backstop for conjunct-dropping): a
        // SATISFIABLE obligation `i ≥ len` (no contradiction) carrying an
        // unsupported Bool-reification conjunct must NOT certify. Dropping
        // conjuncts is sound ONLY because a satisfiable obligation has every
        // subset satisfiable, so the kept subset's ay solve returns SAT and we
        // fail closed — never a false `Certified` for a real violation.
        let i = || Formula::Var("i".to_string(), Sort::Int);
        let len = || Formula::Var("len".to_string(), Sort::Int);
        let viol = Formula::And(vec![
            Formula::Eq(
                Box::new(Formula::Var("_3".to_string(), Sort::Bool)),
                Box::new(Formula::Lt(Box::new(i()), Box::new(len()))),
            ),
            Formula::Ge(Box::new(i()), Box::new(len())), // satisfiable on its own
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "a satisfiable obligation must fail closed even with unsupported conjuncts dropped"
        );
    }

    #[test]
    fn fails_closed_when_no_conjunct_is_supported() {
        // If EVERY conjunct is outside the linear-Int fragment there is no kept
        // atom to refute, so we must fail closed (never vacuously certify).
        let viol = Formula::And(vec![Formula::Eq(
            Box::new(Formula::Var("b".to_string(), Sort::Bool)),
            Box::new(Formula::Var("c".to_string(), Sort::Bool)),
        )]);
        assert!(
            certify_violation(&viol).is_none(),
            "an obligation with no supported conjunct must fail closed"
        );
    }

    #[test]
    fn certifies_div_by_zero_discharge_via_bool_unfold() {
        // The strengthened div-by-zero discharge R1 emits: precondition `divisor != 0`
        // plus the reified violation `_4 = divisor; _5 = (_4 == 0); assert(_5)`. The
        // contradiction (`divisor != 0 ∧ divisor == 0`) hides behind the asserted Bool
        // `_5`, dropped by collect_supported_atoms. The unfold must expose it ⇒ certify.
        let divisor = || Formula::Var("divisor".to_string(), Sort::Int);
        let four = || Formula::Var("_4".to_string(), Sort::Int);
        let five = || Formula::Var("_5".to_string(), Sort::Bool);
        let viol = Formula::And(vec![
            Formula::Not(Box::new(Formula::Eq(Box::new(divisor()), Box::new(Formula::Int(0))))),
            Formula::Eq(Box::new(four()), Box::new(divisor())),
            Formula::Eq(
                Box::new(five()),
                Box::new(Formula::Eq(Box::new(four()), Box::new(Formula::Int(0)))),
            ),
            five(),
        ]);
        let evidence = certify_violation(&viol).expect(
            "div-by-zero discharge (divisor != 0) must certify after Bool-reification unfold",
        );
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        // The consumer re-check must accept the certificate against the FULL violation
        // (it applies the same unfold/propagate/drop), or the compiler would reject it.
        assert!(
            recheck_cleancic(&term, &context, &lineage, &viol),
            "recheck_cleancic must accept the div-by-zero discharge certificate"
        );
    }

    #[test]
    fn fails_closed_on_satisfiable_div_by_zero_without_precondition() {
        // SAME reified violation but WITHOUT the precondition: `divisor == 0` is
        // satisfiable ⇒ no contradiction ⇒ must fail closed. Guards the unfold against
        // manufacturing a false Certified (the soundness backstop for the new atom).
        let divisor = || Formula::Var("divisor".to_string(), Sort::Int);
        let four = || Formula::Var("_4".to_string(), Sort::Int);
        let five = || Formula::Var("_5".to_string(), Sort::Bool);
        let viol = Formula::And(vec![
            Formula::Eq(Box::new(four()), Box::new(divisor())),
            Formula::Eq(
                Box::new(five()),
                Box::new(Formula::Eq(Box::new(four()), Box::new(Formula::Int(0)))),
            ),
            five(),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "a satisfiable div-by-zero (no precondition) must fail closed"
        );
    }

    #[test]
    fn certifies_caller_discharge_double_negated_closed_const() {
        // R1's caller-discharge VC for `helper(_, 5)` against precondition `divisor != 0`
        // (= `Not(Eq(divisor,0))`): the producer emits `Not(P[σ])` = `Not(Not(Eq(5,0)))`.
        // 5 == 0 is a false closed constant ⇒ the VC is UNSAT ⇒ must certify.
        let viol = Formula::Not(Box::new(Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Int(5)),
            Box::new(Formula::Int(0)),
        )))));
        assert!(
            certify_violation(&viol).is_some(),
            "double-negated false closed-constant caller discharge must certify"
        );
    }

    #[test]
    fn fails_closed_on_satisfiable_double_negated_disequality() {
        // A caller that does NOT establish P: `helper(_, d)` with `d` unconstrained gives
        // `Not(Not(Eq(d,0)))` = `Eq(d,0)`, satisfiable ⇒ must fail closed (no flip).
        let viol = Formula::Not(Box::new(Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("d".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )))));
        assert!(
            certify_violation(&viol).is_none(),
            "a satisfiable (var) double-negated disequality must fail closed"
        );
    }

    // -----------------------------------------------------------------------
    // Trust #540 (R1 replay authority). A caller-propagation verdict flip may
    // only be authorized by evidence that REPLAYS: the kernel must re-check the
    // certificate's term against a context rebuilt from the obligation's own
    // atoms, bound to the obligation's full identity, under the axiom gate.
    // -----------------------------------------------------------------------

    /// The R1 helper VC: `x / divisor` with the inferred precondition `divisor != 0`.
    fn r1_strengthened_vc() -> VerificationCondition {
        let divisor = || Formula::Var("divisor".to_string(), Sort::Int);
        let four = || Formula::Var("_4".to_string(), Sort::Int);
        let five = || Formula::Var("_5".to_string(), Sort::Bool);
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "helper".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::Not(Box::new(Formula::Eq(Box::new(divisor()), Box::new(Formula::Int(0))))),
                Formula::Eq(Box::new(four()), Box::new(divisor())),
                Formula::Eq(
                    Box::new(five()),
                    Box::new(Formula::Eq(Box::new(four()), Box::new(Formula::Int(0)))),
                ),
                five(),
            ]),
            contract_metadata: None,
        }
    }

    /// The R1 caller-discharge VC at `helper(10, 5)`: `¬P[σ]` = `¬¬(5 = 0)`.
    fn r1_caller_discharge_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Precondition { callee: "helper".into() },
            function: "main".into(),
            location: SourceSpan::default(),
            formula: Formula::Not(Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Int(5)),
                Box::new(Formula::Int(0)),
            ))))),
            contract_metadata: None,
        }
    }

    /// Both certificates R1's sealed token binds must REPLAY — the strengthened
    /// VC (generic supported-atom context) and the caller-discharge VC (the
    /// CLOSED-CONSTANT context). Before `closed_constant_refutation` was made a
    /// producer/consumer seam the latter was mint-only: it certified but did not
    /// re-check, so R1 had no replayable caller evidence and could not be enabled.
    #[test]
    fn r1_strengthened_and_caller_discharge_certificates_both_replay() {
        for (name, vc) in
            [("strengthened", r1_strengthened_vc()), ("caller-discharge", r1_caller_discharge_vc())]
        {
            let evidence =
                certify_vc(&vc).unwrap_or_else(|| panic!("{name} VC must kernel-certify"));
            assert!(
                replay_vc_evidence(&vc, &evidence),
                "{name} VC's certificate must REPLAY (kernel re-check + identity binding)"
            );
        }
    }

    /// WITNESS-SWAP CONTROL: a certificate minted for one obligation must not
    /// replay as evidence for a DIFFERENT obligation, even when the violation
    /// formula is identical. This is what `recheck_vc`'s full-identity binding
    /// (function + kind + location + formula) buys over the formula-only
    /// `recheck_cleancic`.
    #[test]
    fn certificate_does_not_replay_against_a_different_obligation() {
        let vc = r1_caller_discharge_vc();
        let evidence = certify_vc(&vc).expect("must certify");
        assert!(replay_vc_evidence(&vc, &evidence), "must replay against its OWN obligation");

        let mut other_function = vc.clone();
        other_function.function = "someone_else".into();
        assert!(
            !replay_vc_evidence(&other_function, &evidence),
            "a certificate must NOT replay against a different FUNCTION"
        );

        let mut other_kind = vc.clone();
        other_kind.kind = VcKind::DivisionByZero;
        assert!(
            !replay_vc_evidence(&other_kind, &evidence),
            "a certificate must NOT replay against a different VC KIND"
        );

        let mut other_location = vc.clone();
        other_location.location =
            SourceSpan { line_start: 42, ..VerificationCondition::clone(&vc).location };
        assert!(
            !replay_vc_evidence(&other_location, &evidence),
            "a certificate must NOT replay against a different LOCATION"
        );
    }

    /// A SATISFIABLE caller discharge (the `reject_unconstrained_caller` shape:
    /// `helper(10, d)` with `d` free) must mint no certificate at all — so R1's
    /// mint fails and the flip never happens. The fail-closed oracle.
    #[test]
    fn satisfiable_caller_discharge_has_no_replayable_evidence() {
        let mut vc = r1_caller_discharge_vc();
        vc.formula = Formula::Not(Box::new(Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("d".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )))));
        assert!(
            certify_vc(&vc).is_none(),
            "an unconstrained caller (`helper(10, d)`) must yield NO certificate"
        );
    }

    /// DISCRIMINATING CONTROL for [`proof_axiom_closure_is_clean`]: the gate is
    /// load-bearing, not cosmetic. A `sorry`-shaped oracle axiom (`{α : Sort u} →
    /// α`, exactly what the clean prelude ships as `sorry` / `trustedAy` /
    /// `trustedArith`) makes `sorry False` a one-node term the KERNEL ITSELF
    /// ACCEPTS as a proof of `False` — i.e. a forged certificate for ANY
    /// obligation, satisfiable ones included. Assert BOTH halves: the kernel
    /// accepts the forgery, and the axiom gate rejects it.
    #[test]
    fn axiom_forgery_is_rejected_even_though_the_kernel_accepts_it() {
        let mut env = build_env(&BTreeSet::new()).expect("base env");
        // `forged_oracle : {α : Sort u} → α` — the `sorry` shape.
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("forged_oracle"),
            level_params: vec![Name::from_string("u")],
            type_: Expr::pi(
                BinderInfo::Implicit,
                Expr::sort(Level::param(Name::from_string("u"))),
                Expr::bvar(0),
            ),
        })
        .expect("declare the oracle");
        // `forged_oracle.{0} False : False` (`False : Prop = Sort 0`).
        let term = Expr::app(
            Expr::const_(Name::from_string("forged_oracle"), vec![Level::zero()]),
            false_expr(),
        );

        assert!(
            TypeChecker::with_context(&env, LocalContext::new())
                .check_type(&term, &false_expr())
                .is_ok(),
            "control precondition: the kernel ALONE accepts the `sorry`-shaped forgery"
        );
        assert!(
            !proof_axiom_closure_is_clean(&env, &term, &BTreeSet::new()),
            "the axiom-closure gate MUST reject an oracle-backed proof of False"
        );
        assert!(
            !kernel_checks_false(&env, LocalContext::new(), &term, &BTreeSet::new()),
            "kernel_checks_false must fail closed on the forgery (gate is wired in)"
        );
    }

    /// The gate must still ADMIT the kernel's foundational axiom base — a real
    /// classical arithmetic refutation legitimately reaches `Classical.choice` /
    /// `propext` / `Quot.*`, and rejecting those would silently kill every
    /// certificate (a fail-closed but capability-destroying outcome).
    #[test]
    fn foundational_axioms_are_admitted() {
        let vc = r1_strengthened_vc();
        assert!(
            certify_vc(&vc).is_some(),
            "a real refutation reaching the kernel's foundational axioms must still certify"
        );
    }

    #[test]
    fn certifies_direct_integer_disequality_contradiction() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let zero = || Formula::Int(0);
        let viol = Formula::And(vec![
            Formula::Eq(Box::new(x()), Box::new(zero())),
            Formula::Not(Box::new(Formula::Eq(Box::new(zero()), Box::new(x())))),
        ]);

        let evidence =
            certify_violation(&viol).expect("direct integer equality/disequality must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut vars = BTreeSet::new();
        vars.insert("x".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "integer disequality CleanCic payload must re-check to False via the clean kernel"
        );
    }

    #[test]
    fn certifies_reflexive_integer_disequality_contradiction() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let viol = Formula::Not(Box::new(Formula::Eq(Box::new(x()), Box::new(x()))));

        let evidence =
            certify_violation(&viol).expect("reflexive integer disequality must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut vars = BTreeSet::new();
        vars.insert("x".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "reflexive-disequality CleanCic payload must re-check to False via the clean kernel"
        );
    }

    #[test]
    fn certifies_linear_sum_term_contradiction() {
        // Violation with an arithmetic SUM term: `(a + b) < 0 ∧ 0 < (a + b)`.
        // Exercises the HAdd-form encoding that matches clean-auto's
        // reconstruction (translate_term), so the kernel re-check passes.
        let sum = || {
            Formula::Add(
                Box::new(Formula::Var("a".to_string(), Sort::Int)),
                Box::new(Formula::Var("b".to_string(), Sort::Int)),
            )
        };
        let viol = Formula::And(vec![
            Formula::Lt(Box::new(sum()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(sum())),
        ]);
        let evidence = certify_violation(&viol).expect("linear-sum contradiction must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut vars = BTreeSet::new();
        vars.insert("a".to_string());
        vars.insert("b".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "linear-sum CleanCic payload must re-check to False via the clean kernel"
        );
    }

    #[test]
    fn certifies_mul_by_constant_contradiction() {
        // Linear mul-by-constant: `(2*x) < 0 ∧ 0 < (2*x)` — ay closes it via a
        // weighted Farkas lemma and the kernel re-checks zero-trust. Written
        // literal-first; the bridge canonicalizes to ay's variable-first form.
        let two_x = || {
            Formula::Mul(
                Box::new(Formula::Int(2)),
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
            )
        };
        let viol = Formula::And(vec![
            Formula::Lt(Box::new(two_x()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(two_x())),
        ]);
        let evidence =
            certify_violation(&viol).expect("mul-by-constant contradiction must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut vars = BTreeSet::new();
        vars.insert("x".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "mul-by-constant CleanCic payload must re-check to False via the clean kernel"
        );
    }

    #[test]
    fn certifies_nested_linear_combination() {
        // Multi-variable linear combination `(a + 2*b)` — exercises the
        // recursive composition of Add over Mul-by-constant (the shape real
        // VCs use, e.g. `i + stride*k`). Violation: `t < 0 ∧ 0 < t`.
        let t = || {
            Formula::Add(
                Box::new(Formula::Var("a".to_string(), Sort::Int)),
                Box::new(Formula::Mul(
                    Box::new(Formula::Int(2)),
                    Box::new(Formula::Var("b".to_string(), Sort::Int)),
                )),
            )
        };
        let viol = Formula::And(vec![
            Formula::Lt(Box::new(t()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(t())),
        ]);
        let evidence = certify_violation(&viol).expect("nested linear combination must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut vars = BTreeSet::new();
        vars.insert("a".to_string());
        vars.insert("b".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "nested linear-combination CleanCic payload must re-check to False via the clean kernel"
        );
    }

    #[test]
    fn fails_closed_on_nonlinear_var_times_var() {
        // var×var is nonlinear (NIA); the linear bridge must fail closed,
        // never fabricate a Certified.
        let xy = || {
            Formula::Mul(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )
        };
        let viol = Formula::And(vec![
            Formula::Lt(Box::new(xy()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(xy())),
        ]);
        assert!(certify_violation(&viol).is_none(), "nonlinear var*var must fail closed");
    }

    #[test]
    fn fails_closed_on_unsupported_bitvector_violation() {
        // Real machine-int VCs are BitVec; the QF_LIA bridge does not support
        // them and must fail closed (→ Trusted), never fabricate a certificate.
        let bv_vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "bv".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::BitVec { value: 2, width: 64 }),
                Box::new(Formula::BitVec { value: 0, width: 64 }),
            ),
            contract_metadata: None,
        };
        assert!(certify_vc(&bv_vc).is_none(), "BitVec violation must fail closed");
    }

    #[test]
    fn certifies_bvult_antisymmetry_8bit() {
        // MB milestone-1: `(bvult 3 7) ∧ (bvult 7 3)` is unsatisfiable because
        // `bvult 7 3` is false. The unsigned-literal comparison lifts onto the
        // existing zero-trust closed-Int-order refutation → a kernel-checked
        // CleanCic certificate, with NO new TCB and NO bit-blasting.
        let bv = |v: i128| Box::new(Formula::BitVec { value: v, width: 8 });
        let violation =
            Formula::And(vec![Formula::BvULt(bv(3), bv(7), 8), Formula::BvULt(bv(7), bv(3), 8)]);
        let ev = certify_violation(&violation).expect("bvult antisymmetry must certify");
        assert!(
            matches!(ev, trust_ir::ProofEvidence::CleanCic { .. }),
            "bvult antisymmetry must be a kernel-checked CleanCic certificate, got {ev:?}"
        );
    }

    #[test]
    fn lone_false_bvult_certifies_but_true_bvult_declines() {
        let bv = |v: i128| Box::new(Formula::BitVec { value: v, width: 8 });
        // A closed-false `bvult 7 3` is refutable.
        assert!(
            certify_violation(&Formula::BvULt(bv(7), bv(3), 8)).is_some(),
            "a closed-false bvult must certify"
        );
        // A satisfiable `bvult 3 7` (true) must NOT be refuted — soundness guard:
        // a real violation has a true atom and is declined, never fabricated.
        assert!(
            certify_violation(&Formula::BvULt(bv(3), bv(7), 8)).is_none(),
            "a true bvult is satisfiable and must not be refuted"
        );
    }

    #[test]
    fn signed_bvslt_is_not_lifted_to_unsigned() {
        // The SIGNED variant must NOT route through the unsigned lift; it fails
        // closed (declined), never mis-certified as unsigned — a wrong sign
        // mapping for a high-bit-set value would be a false-PROVE.
        let bv = |v: i128| Box::new(Formula::BitVec { value: v, width: 8 });
        let violation =
            Formula::And(vec![Formula::BvSLt(bv(3), bv(7), 8), Formula::BvSLt(bv(7), bv(3), 8)]);
        assert!(
            certify_violation(&violation).is_none(),
            "signed bvslt must not certify via the unsigned path"
        );
    }

    /// MB milestone-2 (2a): a concrete unsigned-add no-overflow obligation
    /// `bvult(bvadd(a,b), a)` with `a+b` not wrapping is unsatisfiable and
    /// certifies — the BvAdd folds to a literal and the closed-Int-order path
    /// refutes the false comparison. ZERO new TCB (the fold is exact; the term
    /// is kernel-re-checked).
    #[test]
    fn certifies_concrete_bvadd_no_overflow_width4() {
        let bv = |v: i128| Box::new(Formula::BitVec { value: v, width: 4 });
        // 5 + 3 = 8 (no wrap at width 4); bvult(8, 5) is false → no overflow.
        let violation = Formula::BvULt(Box::new(Formula::BvAdd(bv(5), bv(3), 4)), bv(5), 4);
        let ev = certify_violation(&violation).expect("concrete no-overflow add must certify");
        assert!(matches!(ev, trust_ir::ProofEvidence::CleanCic { .. }));
    }

    /// A concrete add that REALLY overflows (`14 + 5 = 19 ≡ 3 mod 16`, and
    /// `bvult(3, 14)` is true) is a SATISFIABLE violation — overflow genuinely
    /// occurs — and must be DECLINED, never certified as no-overflow.
    #[test]
    fn concrete_bvadd_real_overflow_declines() {
        let bv = |v: i128| Box::new(Formula::BitVec { value: v, width: 4 });
        let violation = Formula::BvULt(Box::new(Formula::BvAdd(bv(14), bv(5), 4)), bv(14), 4);
        assert!(
            certify_violation(&violation).is_none(),
            "a real overflow (14+5 wraps to 3 < 14) must not be certified as no-overflow"
        );
    }

    /// Symbolic add fails closed: a non-literal operand declines (the fold needs
    /// concrete literals; symbolic add needs the not-yet-proven carrier lemma).
    #[test]
    fn symbolic_bvadd_declines_fail_closed() {
        let bv = |v: i128| Box::new(Formula::BitVec { value: v, width: 4 });
        let x = Box::new(Formula::Var("x".to_string(), trust_types::Sort::Int));
        let violation = Formula::BvULt(Box::new(Formula::BvAdd(x, bv(3), 4)), bv(5), 4);
        assert!(
            certify_violation(&violation).is_none(),
            "symbolic bvadd must fail closed (no concrete fold)"
        );
    }

    #[test]
    fn modulo_variable_divisor_positivity_in_mirrored_orientation_certifies() {
        // The strict-positivity fact arrives as `1 ≤ n` (literal on the LEFT) —
        // the orientation the closures previously missed. `k = a % n ∧ 1 ≤ n`
        // emits `k < n`; with `n ≤ 8` present, the chain closes `k < 8`
        // against the trap's `k ≥ 8`.
        let k = || Formula::Var("k".to_string(), Sort::Int);
        let a = || Formula::Var("a".to_string(), Sort::Int);
        let n = || Formula::Var("n".to_string(), Sort::Int);
        let viol = Formula::And(vec![
            Formula::Eq(Box::new(k()), Box::new(Formula::Rem(Box::new(a()), Box::new(n())))),
            Formula::Le(Box::new(Formula::Int(1)), Box::new(n())),
            Formula::Le(Box::new(n()), Box::new(Formula::Int(8))),
            Formula::Ge(Box::new(k()), Box::new(Formula::Int(8))),
        ]);
        assert_formula_certificate_pairs(&viol);
    }

    #[test]
    fn division_variable_divisor_bounds_certify_end_to_end() {
        // `q = a / d` with `d ≥ 1`, `0 ≤ a ≤ 100`: the variable-divisor arm
        // emits `q ≥ 0` and `q ≤ 100` (tight at d = 1), refuting `q ≥ 101`.
        let q = || Formula::Var("q".to_string(), Sort::Int);
        let a = || Formula::Var("a".to_string(), Sort::Int);
        let d = || Formula::Var("d".to_string(), Sort::Int);
        let viol = Formula::And(vec![
            Formula::Eq(Box::new(q()), Box::new(Formula::Div(Box::new(a()), Box::new(d())))),
            Formula::Ge(Box::new(d()), Box::new(Formula::Int(1))),
            Formula::Ge(Box::new(a()), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(a()), Box::new(Formula::Int(100))),
            Formula::Ge(Box::new(q()), Box::new(Formula::Int(101))),
        ]);
        assert_formula_certificate_pairs(&viol);
    }

    #[test]
    fn division_variable_divisor_requires_strict_positivity() {
        // Only `d ≥ 0` (not strictly positive): the arm must not fire — the
        // bounds cannot exclude d = 0 — and the asserted hypothesis set stays
        // satisfiable, so nothing certifies (fail-closed).
        let q = || Formula::Var("q".to_string(), Sort::Int);
        let a = || Formula::Var("a".to_string(), Sort::Int);
        let d = || Formula::Var("d".to_string(), Sort::Int);
        let viol = Formula::And(vec![
            Formula::Eq(Box::new(q()), Box::new(Formula::Div(Box::new(a()), Box::new(d())))),
            Formula::Ge(Box::new(d()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(a()), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(a()), Box::new(Formula::Int(100))),
            Formula::Ge(Box::new(q()), Box::new(Formula::Int(101))),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "a merely non-negative divisor must fail closed out of the variable-divisor arm"
        );
    }

    #[test]
    fn division_variable_divisor_requires_nonnegative_dividend() {
        // No dividend lower bound: the arm must not fire — the documented
        // scope requires the non-negativity guard (truncation-vs-floor breaks
        // monotonicity across sign) and the conservative decline is pinned.
        let q = || Formula::Var("q".to_string(), Sort::Int);
        let a = || Formula::Var("a".to_string(), Sort::Int);
        let d = || Formula::Var("d".to_string(), Sort::Int);
        let viol = Formula::And(vec![
            Formula::Eq(Box::new(q()), Box::new(Formula::Div(Box::new(a()), Box::new(d())))),
            Formula::Ge(Box::new(d()), Box::new(Formula::Int(1))),
            Formula::Le(Box::new(a()), Box::new(Formula::Int(100))),
            Formula::Ge(Box::new(q()), Box::new(Formula::Int(101))),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "an unbounded-below dividend must fail closed out of the variable-divisor arm"
        );
    }

    #[test]
    fn class_propagated_divisor_positivity_reaches_the_late_modulo_pass() {
        // Positivity arrives ONLY via the var=var equality class (`d = e`,
        // `e ≥ 1`), which propagates at table position 10 — AFTER the first
        // modulo pass. The late pass sees the propagated `d ≥ 1`, emits
        // `k < d`, and the chain closes `k < d ≤ 8` against `k ≥ 8`.
        let k = || Formula::Var("k".to_string(), Sort::Int);
        let a = || Formula::Var("a".to_string(), Sort::Int);
        let d = || Formula::Var("d".to_string(), Sort::Int);
        let e = || Formula::Var("e".to_string(), Sort::Int);
        let viol = Formula::And(vec![
            Formula::Eq(Box::new(k()), Box::new(Formula::Rem(Box::new(a()), Box::new(d())))),
            Formula::Eq(Box::new(d()), Box::new(e())),
            Formula::Ge(Box::new(e()), Box::new(Formula::Int(1))),
            Formula::Le(Box::new(d()), Box::new(Formula::Int(8))),
            Formula::Ge(Box::new(k()), Box::new(Formula::Int(8))),
        ]);
        assert_formula_certificate_pairs(&viol);
    }

    #[test]
    fn antisymmetric_bounds_disequality_certifies_via_order_split() {
        // `a ≤ b ∧ b ≤ a ∧ a ≠ b`: antisymmetry forces `a = b`, but no literal
        // `Eq` conjunct exists for the direct-disequality pair — the split
        // recognizer rewrites the `≠` into `a < b ∨ b < a` and each branch is
        // refuted against the opposite bound.
        let a = || Formula::Var("a".to_string(), Sort::Int);
        let b = || Formula::Var("b".to_string(), Sort::Int);
        let viol = Formula::And(vec![
            Formula::Le(Box::new(a()), Box::new(b())),
            Formula::Le(Box::new(b()), Box::new(a())),
            Formula::Not(Box::new(Formula::Eq(Box::new(a()), Box::new(b())))),
        ]);

        assert_formula_certificate_pairs(&viol);

        let trust_ir::ProofEvidence::CleanCic { term, context, .. } =
            certify_violation(&viol).expect("antisymmetric-bounds disequality must certify")
        else {
            panic!("expected CleanCic evidence");
        };
        let mut vars = BTreeSet::new();
        vars.insert("a".to_string());
        vars.insert("b".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "order-split disequality CleanCic payload must re-check to False via the clean kernel"
        );
    }

    #[test]
    fn bounded_zero_disequality_certifies_via_order_split() {
        // `0 ≤ d ∧ d ≤ 0 ∧ d ≠ 0`: the bounds pin `d = 0` and the disequality
        // (against a LITERAL operand) contradicts. Branch `d < 0` closes
        // against `0 ≤ d`; branch `0 < d` closes against `d ≤ 0`.
        let d = || Formula::Var("d".to_string(), Sort::Int);
        let zero = || Formula::Int(0);
        let viol = Formula::And(vec![
            Formula::Le(Box::new(zero()), Box::new(d())),
            Formula::Le(Box::new(d()), Box::new(zero())),
            Formula::Not(Box::new(Formula::Eq(Box::new(d()), Box::new(zero())))),
        ]);

        assert_formula_certificate_pairs(&viol);
    }

    #[test]
    fn split_disequality_fails_closed_when_one_branch_is_open() {
        // `0 ≤ d ∧ d ≠ 0` is satisfiable (d = 1): the `0 < d` branch of the
        // split cannot be refuted, the engine declines, and the ay cross-check
        // over context + split is SAT — nothing may certify.
        let d = || Formula::Var("d".to_string(), Sort::Int);
        let sat = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(d())),
            Formula::Not(Box::new(Formula::Eq(Box::new(d()), Box::new(Formula::Int(0))))),
        ]);
        assert!(
            certify_violation(&sat).is_none(),
            "a disequality with an open branch must fail closed"
        );
    }

    #[test]
    fn split_disequality_fails_closed_on_unsupported_operands() {
        // `x·x ≠ 0` is outside the direct-`Int` operand fragment
        // (`canonical_int_eq` rejects the nonlinear term), so the split
        // recognizer never fires and the violation fails closed even with
        // bounds that would close a linear split.
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let viol = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(x())),
            Formula::Le(Box::new(x()), Box::new(Formula::Int(0))),
            Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Mul(Box::new(x()), Box::new(x()))),
                Box::new(Formula::Int(0)),
            ))),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "a nonlinear disequality operand must fail closed out of the split lane"
        );
    }

    #[test]
    fn fails_closed_on_frame_condition_disequality_boundary() {
        // `ContractKind::Modifies` frame VCs emit `¬(old(var) = new(var))`.
        // Standalone disequality is a disjunction over a linear order, not a
        // single Farkas atom. The order-split recognizer rewrites it into
        // `old < new ∨ new < old`, but with NO other conjuncts neither branch
        // is refutable and the system is satisfiable — so it must still fail
        // closed (the ay UNSAT cross-check is the backstop).
        let old_x = || Formula::Var("x__old".to_string(), Sort::Int);
        let new_x = || Formula::Var("x".to_string(), Sort::Int);
        let frame_violation =
            Formula::Not(Box::new(Formula::Eq(Box::new(old_x()), Box::new(new_x()))));

        assert!(
            certify_violation(&frame_violation).is_none(),
            "standalone frame-condition disequality must fail closed"
        );
    }

    #[test]
    fn fails_closed_on_unsupported_disequality_term_shape() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let unsupported = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Add(Box::new(x()), Box::new(Formula::Int(1)))),
            Box::new(Formula::Int(0)),
        )));

        assert!(
            certify_violation(&unsupported).is_none(),
            "disequality over unsupported arithmetic terms must fail closed"
        );
    }

    #[test]
    fn fails_closed_on_satisfiable_violation() {
        // `0 < x` alone is satisfiable: there is no contradiction, so ay returns
        // SAT and we must NOT certify.
        let sat =
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(Formula::Var("x".into(), Sort::Int)));
        assert!(certify_violation(&sat).is_none(), "satisfiable violation must fail closed");
    }

    #[test]
    fn kernel_rejects_non_false_term() {
        // T-CERTIFY-CORRECT: kernel gate accepts a term ONLY if it checks as ': False'.
        // Int.ofNat 0 has type Int (not False) -> must be rejected.
        let env = build_env(&BTreeSet::new()).expect("base env builds");
        let term = int_ofnat(0);
        assert!(
            !kernel_checks_false(&env, LocalContext::new(), &term, &BTreeSet::new()),
            "a non-False term must be rejected by the kernel gate"
        );
    }

    #[test]
    fn roundtrip_rejects_undeserializable_payload() {
        // T-CERTIFY-CORRECT: the payload round-trip re-check fails closed on corrupt/forged bytes.
        let vars = BTreeSet::new();
        assert!(
            !payload_roundtrip_rechecks(&vars, b"not-a-term", b"not-a-ctx"),
            "undeserializable payload must fail the round-trip re-check"
        );
    }

    #[test]
    fn lineage_binds_obligation_identity() {
        // T-CERTIFY-CORRECT: a CleanCic certificate is bound to its obligation's
        // identity. Two VCs with the SAME contradiction formula but DIFFERENT
        // function names must produce DIFFERENT lineage digests, so a witness
        // minted for one obligation cannot be presented as evidence for another.
        let make = |func: &str| VerificationCondition {
            kind: VcKind::Assertion { message: "x bounded".to_string() },
            function: func.into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::Lt(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Lt(
                    Box::new(Formula::Int(0)),
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                ),
            ]),
            contract_metadata: None,
        };

        let vc_a = make("func_a");
        let vc_b = make("func_b");

        let trust_ir::ProofEvidence::CleanCic { lineage: lineage_a, .. } =
            certify_vc(&vc_a).expect("obligation A must certify")
        else {
            panic!("expected CleanCic evidence");
        };
        let trust_ir::ProofEvidence::CleanCic { lineage: lineage_b, .. } =
            certify_vc(&vc_b).expect("obligation B must certify")
        else {
            panic!("expected CleanCic evidence");
        };

        assert_ne!(
            lineage_a, lineage_b,
            "VCs differing only in function name must yield different lineage digests"
        );
    }

    /// The ShiftOverflow / CastOverflow violation shape: a shift-amount or
    /// cast-range check over a compile-time constant. The contradiction lives in
    /// a DISJUNCTION of closed order atoms that all evaluate to false, which the
    /// Farkas/order-atom fragment cannot reach. The closed-constant path must
    /// kernel-certify it (the strict-verification accounting gap, task #35).
    #[test]
    fn certifies_closed_constant_shift_and_cast_range_checks() {
        let imin = || Formula::Int(i64::MIN as i128);
        let imax = || Formula::Int(i64::MAX as i128);
        let two = || Formula::Int(2);
        let bounds = || {
            Formula::And(vec![
                Formula::Le(Box::new(imin()), Box::new(two())),
                Formula::Le(Box::new(two()), Box::new(imax())),
            ])
        };
        // `a >> 2` (i32): shift amount in `0..32`. Violation: 2<0 ∨ 2≥32.
        let shift = Formula::And(vec![
            bounds(),
            Formula::Or(vec![
                Formula::Lt(Box::new(two()), Box::new(Formula::Int(0))),
                Formula::Ge(Box::new(two()), Box::new(Formula::Int(32))),
            ]),
        ]);
        // `2 as u32`-style range check. Violation: 2<0 ∨ 2>u32::MAX.
        let cast = Formula::And(vec![
            bounds(),
            Formula::Or(vec![
                Formula::Lt(Box::new(two()), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(two()), Box::new(Formula::Int(4_294_967_295))),
            ]),
        ]);
        assert!(certify_violation(&shift).is_some(), "shift-amount range check must certify");
        assert!(certify_violation(&cast).is_some(), "cast range check must certify");
        assert_formula_certificate_pairs(&shift);
        assert_formula_certificate_pairs(&cast);
    }

    /// SOUNDNESS: the closed-constant path refutes ONLY genuinely-false atoms.
    /// A satisfiable closed atom (a real, possible violation) — or a disjunction
    /// with any satisfiable disjunct — must fail closed, never be refuted.
    #[test]
    fn closed_constant_path_fails_closed_on_satisfiable_obligations() {
        let lt =
            |a: i128, b: i128| Formula::Lt(Box::new(Formula::Int(a)), Box::new(Formula::Int(b)));
        let ge =
            |a: i128, b: i128| Formula::Ge(Box::new(Formula::Int(a)), Box::new(Formula::Int(b)));
        // True atoms — satisfiable, must NOT certify.
        assert!(certify_violation(&lt(0, 2)).is_none(), "0<2 is true (sat) — must fail closed");
        assert!(certify_violation(&ge(32, 2)).is_none(), "32≥2 is true (sat) — must fail closed");
        // `a ≤ a` is true (not a contradiction) — must fail closed.
        assert!(
            certify_violation(&Formula::Le(Box::new(Formula::Int(3)), Box::new(Formula::Int(3))))
                .is_none(),
            "3≤3 is true (sat) — must fail closed"
        );
        // Disjunction with a satisfiable disjunct (2<0 false, 5≥2 true) — sat.
        assert!(
            certify_violation(&Formula::Or(vec![lt(2, 0), ge(5, 2)])).is_none(),
            "Or with a true disjunct is satisfiable — must fail closed"
        );
    }

    /// Closed false equalities certify (the divisor conjunct of a
    /// constant-divisor division-overflow / div-by-zero check), and satisfiable
    /// (true) equalities fail closed.
    #[test]
    fn certifies_closed_false_equalities_and_declines_true_ones() {
        let eq =
            |a: i128, b: i128| Formula::Eq(Box::new(Formula::Int(a)), Box::new(Formula::Int(b)));
        // `2 = -1` (div-overflow divisor==-1) and `2 = 0` (div-by-zero) — false.
        assert!(certify_violation(&eq(2, -1)).is_some(), "2 = -1 is false — must certify");
        assert!(certify_violation(&eq(2, 0)).is_some(), "2 = 0 is false — must certify");
        assert!(certify_violation(&eq(-5, 7)).is_some(), "-5 = 7 is false — must certify");
        // SOUNDNESS: a TRUE equality is satisfiable — must NOT certify.
        assert!(certify_violation(&eq(3, 3)).is_none(), "3 = 3 is true (sat) — must fail closed");
        // `¬(c = c)` is false — must certify; `¬(c = d)` (c≠d) is true — must not.
        assert!(
            certify_violation(&Formula::Not(Box::new(eq(4, 4)))).is_some(),
            "¬(4 = 4) is false — must certify"
        );
        assert!(
            certify_violation(&Formula::Not(Box::new(eq(4, 5)))).is_none(),
            "¬(4 = 5) is true (sat) — must fail closed"
        );
    }

    /// The full constant-divisor division-overflow violation shape: the closed
    /// false `2 = -1` divisor conjunct is refuted even though the surrounding
    /// conjunction mentions program variables (`x`, the reified bools).
    #[test]
    fn certifies_const_divisor_division_overflow_shape() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let int = |n: i128| Formula::Int(n);
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        // …∧ (x = i32::MIN) ∧ (2 = -1) — the second equality is the closed
        // contradiction; `2 = -1` is constant-false so the whole product is UNSAT.
        let violation = Formula::And(vec![eq(x(), int(-2147483648)), eq(int(2), int(-1))]);
        assert!(
            certify_violation(&violation).is_some(),
            "constant-divisor division-overflow violation must certify on `2 = -1`"
        );
    }

    /// Single-variable interval contradictions with a constant GAP — the shape
    /// a constant index `arr[2]` (`_2 = 2 ∧ _2 ≥ 4`) and any `x = c ∧ x ≥ bound`
    /// produce. ay's Farkas reconstruction handles bounds meeting at a point but
    /// not a gap; the interval refutation closes it.
    #[test]
    fn certifies_single_var_interval_contradictions_with_gap() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        // `x ≤ 2 ∧ 4 ≤ x` — non-strict gap.
        assert!(certify_violation(&Formula::And(vec![le(x(), i(2)), le(i(4), x())])).is_some());
        // `x < 3 ∧ 4 ≤ x` — mixed strict/non-strict.
        assert!(certify_violation(&Formula::And(vec![lt(x(), i(3)), le(i(4), x())])).is_some());
        // The actual constant-index bounds shape: `x = 2 ∧ x ≥ 4` plus a reified
        // bool conjunct (soundly dropped).
        let const_index = Formula::And(vec![
            eq(x(), i(2)),
            eq(Formula::Var("_3".into(), Sort::Bool), lt(x(), i(4))),
            ge(x(), i(4)),
        ]);
        assert!(
            certify_violation(&const_index).is_some(),
            "constant-index bounds VC `x=2 ∧ x≥4` must certify"
        );
    }

    /// Guarded-arithmetic disjunctive contradiction (`if x>10 {x-10}` /
    /// `if x<100 {x+10}`): `context ∧ Or([linear<0, linear>max])` where each
    /// disjunct, shifted back onto `x`, contradicts the guard/bounds.
    #[test]
    fn certifies_guarded_arithmetic_disjunctive_contradiction() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let i = Formula::Int;
        let sub = |a: Formula, b: Formula| Formula::Sub(Box::new(a), Box::new(b));
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let max = 4_294_967_295i128;
        // `if x > 10 { x - 10 }` (u32): guard x>10, bound x≤max; violation
        // Or([x-10 < 0, x-10 > max]). Branch 1: x-10<0 → x<10 vs x>10. Branch 2:
        // x-10>max → x>max+10 vs x≤max.
        let guarded_sub = Formula::And(vec![
            gt(x(), i(10)),
            le(x(), i(max)),
            Formula::Or(vec![lt(sub(x(), i(10)), i(0)), gt(sub(x(), i(10)), i(max))]),
        ]);
        assert!(
            certify_violation(&guarded_sub).is_some(),
            "guarded subtraction `if x>10 {{x-10}}` must certify"
        );
        assert_formula_certificate_pairs(&guarded_sub);
        // `if x < 100 { x + 10 }` (i32-ish): guard x<100, bound x≥0; violation
        // Or([x+10 < 0, x+10 > max]). Branch 2: x+10>max → x>max-10 vs x<100.
        let guarded_add = Formula::And(vec![
            lt(x(), i(100)),
            le(i(0), x()),
            Formula::Or(vec![lt(add(x(), i(10)), i(0)), gt(add(x(), i(10)), i(max))]),
        ]);
        assert!(
            certify_violation(&guarded_add).is_some(),
            "guarded addition `if x<100 {{x+10}}` must certify"
        );
        assert_formula_certificate_pairs(&guarded_add);
    }

    /// A modulo-index `s[i % 8]` on `[i32; 8]`: the VC conjoins the modulo
    /// result-bound fact `Or([8 = 0, _3 < 8])` (where `_3 = i % 8`) with the
    /// violation `_3 >= 8`. The `8 = 0` disjunct is a closed-false equality; the
    /// `_3 < 8` disjunct chains against `_3 >= 8` (`8 ≤ _3 < 8 ⊢ 8 < 8`).
    /// A dead modulo-guarded `unreachable!()`: `let k = n % 4; if k >= 4 {
    /// unreachable!() }` over an unsigned `n`. Refuted purely by the Euclidean range
    /// `k = n%4 ⊢ k ≤ 3` (Phase 4 `modulo_range_bounds`), which contradicts the trap's
    /// `k ≥ 4` — no `Or([b=0, k<b])` guard needed (the real VC's bool-temp nesting
    /// defeats the guard path).
    #[test]
    fn certifies_modulo_unreachable_via_euclidean_range() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let violation = Formula::And(vec![
            ge(v("n"), i(0)),
            le(v("n"), i(4_294_967_295)),
            eq(v("k"), Formula::Rem(Box::new(v("n")), Box::new(i(4)))),
            ge(v("k"), i(4)),
        ]);
        assert!(
            certify_violation(&violation).is_some(),
            "dead modulo trap `k = n%4 ∧ k>=4` must certify via the Euclidean range k<=3"
        );
    }

    /// The Euclidean range must NOT over-fire: a genuinely reachable `k = n%4 ∧ k>=2`
    /// (k can be 2 or 3) is SAT, so it must stay unrefuted (fail-closed).
    #[test]
    fn modulo_range_does_not_overfire_when_reachable() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let violation = Formula::And(vec![
            ge(v("n"), i(0)),
            eq(v("k"), Formula::Rem(Box::new(v("n")), Box::new(i(4)))),
            ge(v("k"), i(2)),
        ]);
        assert!(
            certify_violation(&violation).is_none(),
            "reachable `k = n%4 ∧ k>=2` (k in 2..=3) must NOT certify"
        );
    }

    /// The `(a/2)+(b/2)` usize midpoint: the add-overflow violation
    /// `Gt(_4+_6, usize::MAX)` on `_4 = a/2`, `_6 = b/2` (both `a, b : usize` so
    /// `0 ≤ a,b ≤ usize::MAX`) is refuted by the Euclidean division range
    /// `_4, _6 ≤ ⌊usize::MAX/2⌋` (`division_range_bounds`), whose sum
    /// `2·⌊usize::MAX/2⌋ = usize::MAX-1 < usize::MAX` contradicts the overflow.
    #[test]
    fn certifies_usize_midpoint_no_overflow_via_division_range() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let div = |a: Formula, b: Formula| Formula::Div(Box::new(a), Box::new(b));
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let umax = 18_446_744_073_709_551_615_i128; // usize::MAX = 2^64 - 1
        let violation = Formula::And(vec![
            ge(v("a"), i(0)),
            le(v("a"), i(umax)),
            ge(v("b"), i(0)),
            le(v("b"), i(umax)),
            eq(v("_4"), div(v("a"), i(2))),
            eq(v("_6"), div(v("b"), i(2))),
            gt(add(v("_4"), v("_6")), i(umax)),
        ]);
        assert!(
            certify_violation(&violation).is_some(),
            "`(a/2)+(b/2)` on usize can never overflow — must certify via the division range"
        );
    }

    /// The division range must NOT over-fire: an UNGUARDED usize add
    /// `Gt(a+b, usize::MAX)` with `0 ≤ a,b ≤ usize::MAX` and NO division is a
    /// genuine overflow (`a=b=usize::MAX`), so it must stay unrefuted.
    #[test]
    fn division_range_does_not_overfire_on_plain_add() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let umax = 18_446_744_073_709_551_615_i128;
        let violation = Formula::And(vec![
            ge(v("a"), i(0)),
            le(v("a"), i(umax)),
            ge(v("b"), i(0)),
            le(v("b"), i(umax)),
            gt(add(v("a"), v("b")), i(umax)),
        ]);
        assert!(
            certify_violation(&violation).is_none(),
            "plain `a+b` on usize CAN overflow (a=b=MAX) — must NOT certify"
        );
    }

    /// The division range must NOT fire without a non-negative dividend bound:
    /// a signed `q = a/2` with no `a ≥ 0` fact leaves `q` unbounded (Rust `/`
    /// truncates toward zero, breaking monotonicity across sign), so a
    /// `q ≥ huge` claim stays unrefuted.
    #[test]
    fn division_range_requires_nonnegative_dividend() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        // No lower bound on `a`; claim `q ≥ 10^12` — SAT (a can be very large).
        let violation = Formula::And(vec![
            eq(v("q"), Formula::Div(Box::new(v("a")), Box::new(i(2)))),
            ge(v("q"), i(1_000_000_000_000)),
        ]);
        assert!(
            certify_violation(&violation).is_none(),
            "unbounded signed `a/2` must NOT be range-bounded (no non-negative dividend)"
        );
    }

    /// The BITVECTOR form the compiler actually emits for `(a/2)+(b/2)` on
    /// `usize` (modeled in 128-bit BV to catch the widened overflow): the
    /// violation `bvugt(bvadd(a/2, b/2), usize::MAX)` — `BvULt(UMAX, sum)` — over
    /// `_4 = bvudiv a 2`, `_6 = bvudiv b 2` with `0 ≤ a,b ≤ usize::MAX` must
    /// certify via `certify_unsigned_bv_div_sum_no_overflow`.
    #[test]
    fn certifies_usize_midpoint_bitvector_form() {
        let bvw = 128;
        let v = |n: &str| Formula::Var(n.to_string(), Sort::BitVec(bvw));
        let bv = |val: i128| Box::new(Formula::BitVec { value: val, width: bvw });
        let bvv = |n: &str| Box::new(v(n));
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ule = |a: Box<Formula>, b: Box<Formula>| Formula::BvULe(a, b, bvw);
        let umax = 18_446_744_073_709_551_615_i128; // usize::MAX
        let violation = Formula::And(vec![
            ule(bv(0), bvv("a")),
            ule(bvv("a"), bv(umax)),
            ule(bv(0), bvv("b")),
            ule(bvv("b"), bv(umax)),
            eq(v("_4"), Formula::BvUDiv(bvv("a"), bv(2), bvw)),
            eq(v("_6"), Formula::BvUDiv(bvv("b"), bv(2), bvw)),
            // bvugt(bvadd(_4,_6), UMAX)  ==  BvULt(UMAX, bvadd(_4,_6))
            Formula::BvULt(bv(umax), Box::new(Formula::BvAdd(bvv("_4"), bvv("_6"), bvw)), bvw),
        ]);
        assert!(
            certify_violation(&violation).is_some(),
            "the bitvector `(a/2)+(b/2)` usize midpoint must certify via the unsigned BV division path"
        );
    }

    /// SOUNDNESS: bounds, quotient definitions, add, and overflow comparison
    /// must all inhabit the SAME BV width. Formula is a public serialized
    /// surface, so a malformed mixed-width tuple must not borrow a tight bound
    /// from one sort to certify an overflow assertion in another.
    #[test]
    fn unsigned_bv_div_sum_rejects_mixed_width_facts() {
        let target_width = 128;
        let v = |n: &str| Formula::Var(n.to_string(), Sort::BitVec(target_width));
        let bv = |value: i128, width: u32| Box::new(Formula::BitVec { value, width });
        let bvv = |n: &str| Box::new(v(n));
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let umax = 18_446_744_073_709_551_615_i128;

        let mixed_bound_width = Formula::And(vec![
            Formula::BvULe(bv(0, 64), bvv("a"), 64),
            Formula::BvULe(bvv("a"), bv(umax, 64), 64),
            Formula::BvULe(bv(0, 64), bvv("b"), 64),
            Formula::BvULe(bvv("b"), bv(umax, 64), 64),
            eq(v("_4"), Formula::BvUDiv(bvv("a"), bv(2, target_width), target_width)),
            eq(v("_6"), Formula::BvUDiv(bvv("b"), bv(2, target_width), target_width)),
            Formula::BvULt(
                bv(umax, target_width),
                Box::new(Formula::BvAdd(bvv("_4"), bvv("_6"), target_width)),
                target_width,
            ),
        ]);
        assert!(
            certify_violation(&mixed_bound_width).is_none(),
            "64-bit operator/literals must not bound 128-bit variables"
        );

        let mixed_div_width = Formula::And(vec![
            Formula::BvULe(bv(0, target_width), bvv("a"), target_width),
            Formula::BvULe(bvv("a"), bv(umax, target_width), target_width),
            Formula::BvULe(bv(0, target_width), bvv("b"), target_width),
            Formula::BvULe(bvv("b"), bv(umax, target_width), target_width),
            eq(v("_4"), Formula::BvUDiv(bvv("a"), bv(2, 64), 64)),
            eq(v("_6"), Formula::BvUDiv(bvv("b"), bv(2, 64), 64)),
            Formula::BvULt(
                bv(umax, target_width),
                Box::new(Formula::BvAdd(bvv("_4"), bvv("_6"), target_width)),
                target_width,
            ),
        ]);
        assert!(
            certify_violation(&mixed_div_width).is_none(),
            "a quotient relation at another BV width must not bound the target summand"
        );

        let mixed_add_width = Formula::And(vec![
            Formula::BvULe(bv(0, target_width), bvv("a"), target_width),
            Formula::BvULe(bvv("a"), bv(umax, target_width), target_width),
            Formula::BvULe(bv(0, target_width), bvv("b"), target_width),
            Formula::BvULe(bvv("b"), bv(umax, target_width), target_width),
            eq(v("_4"), Formula::BvUDiv(bvv("a"), bv(2, target_width), target_width)),
            eq(v("_6"), Formula::BvUDiv(bvv("b"), bv(2, target_width), target_width)),
            Formula::BvULt(
                bv(umax, target_width),
                Box::new(Formula::BvAdd(bvv("_4"), bvv("_6"), 64)),
                target_width,
            ),
        ]);
        assert!(
            certify_violation(&mixed_add_width).is_none(),
            "a mixed-width BvAdd target must fail closed"
        );
    }

    /// The unsigned BV division path must NOT over-fire: a bitvector `a + b`
    /// (no division) with `0 ≤ a,b ≤ usize::MAX` is a genuine overflow
    /// (`a=b=usize::MAX`), so its `BvULt(UMAX, a+b)` violation must stay
    /// unrefuted (`Ba+Bb = 2·UMAX > UMAX`).
    #[test]
    fn unsigned_bv_div_path_does_not_overfire_on_plain_add() {
        let bvw = 128;
        let v = |n: &str| Formula::Var(n.to_string(), Sort::BitVec(bvw));
        let bv = |val: i128| Box::new(Formula::BitVec { value: val, width: bvw });
        let bvv = |n: &str| Box::new(v(n));
        let ule = |a: Box<Formula>, b: Box<Formula>| Formula::BvULe(a, b, bvw);
        let umax = 18_446_744_073_709_551_615_i128;
        let violation = Formula::And(vec![
            ule(bv(0), bvv("a")),
            ule(bvv("a"), bv(umax)),
            ule(bv(0), bvv("b")),
            ule(bvv("b"), bv(umax)),
            Formula::BvULt(bv(umax), Box::new(Formula::BvAdd(bvv("a"), bvv("b"), bvw)), bvw),
        ]);
        assert!(
            certify_violation(&violation).is_none(),
            "bitvector `a+b` on usize CAN overflow (a=b=MAX) — must NOT certify"
        );
    }

    /// The pure unsigned-BV ORDER-CONTRADICTION family — the exact captured
    /// `verify_index_oob_safe` shape (`if idx < 10 { a[idx] }`, in-bounds
    /// re-assert): range facts `0 ≤u idx ≤u u64::MAX`, reified
    /// `_b = (idx <u 10)` copies, the path guard `idx <u 10`, and the violation
    /// `10 ≤u idx` — must certify via `certify_unsigned_bv_order_contradiction`.
    #[test]
    fn certifies_unsigned_bv_order_contradiction_guarded_index() {
        let bvw = 64;
        let idx = || Box::new(Formula::Var("idx".to_string(), Sort::BitVec(bvw)));
        let bv = |val: i128| Box::new(Formula::BitVec { value: val, width: bvw });
        let ult = |a: Box<Formula>, b: Box<Formula>| Formula::BvULt(a, b, bvw);
        let ule = |a: Box<Formula>, b: Box<Formula>| Formula::BvULe(a, b, bvw);
        let reify = |n: &str| {
            Formula::Eq(
                Box::new(Formula::Var(n.to_string(), Sort::Bool)),
                Box::new(ult(idx(), bv(10))),
            )
        };
        let umax = u64::MAX as i128;
        // Nested-And structure mirroring the captured MIR path conjunction.
        let violation = Formula::And(vec![
            Formula::And(vec![ule(bv(0), idx()), ule(idx(), bv(umax))]),
            reify("_3"),
            ult(idx(), bv(10)),
            Formula::And(vec![reify("_4"), ule(bv(10), idx())]),
        ]);
        assert!(
            certify_violation(&violation).is_some(),
            "unsigned-BV order contradiction `idx <u 10 ∧ 10 ≤u idx` must certify"
        );
    }

    /// FAIL-CLOSED: ANY BV arithmetic or signed operator anywhere in the pool
    /// declines the unsigned-BV order recognizer — a derived operand's unsigned
    /// read-back can wrap, so only raw variable reads justify the Int lift.
    /// (The guard/violation pair is still present and the system still UNSAT;
    /// declining records `Trusted`, never an unsound `Certified`.)
    #[test]
    fn unsigned_bv_order_fails_closed_on_foreign_bv_operator() {
        let bvw = 64;
        let idx = || Box::new(Formula::Var("idx".to_string(), Sort::BitVec(bvw)));
        let bv = |val: i128| Box::new(Formula::BitVec { value: val, width: bvw });
        let ult = |a: Box<Formula>, b: Box<Formula>| Formula::BvULt(a, b, bvw);
        let ule = |a: Box<Formula>, b: Box<Formula>| Formula::BvULe(a, b, bvw);
        let umax = u64::MAX as i128;
        let base = |extra: Formula| {
            Formula::And(vec![
                ule(bv(0), idx()),
                ule(idx(), bv(umax)),
                ult(idx(), bv(10)),
                ule(bv(10), idx()),
                extra,
            ])
        };
        // BV ARITHMETIC operand (`idx + 1 <u 11`) — outside the raw-read family.
        let with_arith = base(ult(Box::new(Formula::BvAdd(idx(), bv(1), bvw)), bv(11)));
        assert!(
            certify_violation(&with_arith).is_none(),
            "a BvAdd operand anywhere in the pool must fail the whitelist (decline)"
        );
        // SIGNED comparison (`0 ≤s idx`) — outside the unsigned order family.
        let with_signed = base(Formula::BvSLe(bv(0), idx(), bvw));
        assert!(
            certify_violation(&with_signed).is_none(),
            "a signed BvSLe conjunct anywhere in the pool must fail the whitelist (decline)"
        );
    }

    /// SOUNDNESS: a wrong-DIRECTION order atom is not the contradiction family —
    /// `idx <u 10 ∧ idx ≤u 10` is satisfiable (idx = 3), so it must decline.
    #[test]
    fn unsigned_bv_order_fails_closed_on_wrong_direction_violation() {
        let bvw = 64;
        let idx = || Box::new(Formula::Var("idx".to_string(), Sort::BitVec(bvw)));
        let bv = |val: i128| Box::new(Formula::BitVec { value: val, width: bvw });
        let ult = |a: Box<Formula>, b: Box<Formula>| Formula::BvULt(a, b, bvw);
        let ule = |a: Box<Formula>, b: Box<Formula>| Formula::BvULe(a, b, bvw);
        let umax = u64::MAX as i128;
        let sat = Formula::And(vec![
            ule(bv(0), idx()),
            ule(idx(), bv(umax)),
            ult(idx(), bv(10)),
            // Wrong direction: `idx ≤u 10` instead of the violation `10 ≤u idx`.
            ule(idx(), bv(10)),
        ]);
        assert!(
            certify_violation(&sat).is_none(),
            "satisfiable `idx <u 10 ∧ idx ≤u 10` must NOT certify"
        );
    }

    /// SOUNDNESS: a violation constant BELOW the guard is satisfiable —
    /// `idx <u 10 ∧ 5 ≤u idx` (idx ∈ [5, 9]) — and must decline (the recognizer
    /// requires the guard and violation to share the SAME literal).
    #[test]
    fn unsigned_bv_order_fails_closed_on_mismatched_constant() {
        let bvw = 64;
        let idx = || Box::new(Formula::Var("idx".to_string(), Sort::BitVec(bvw)));
        let bv = |val: i128| Box::new(Formula::BitVec { value: val, width: bvw });
        let ult = |a: Box<Formula>, b: Box<Formula>| Formula::BvULt(a, b, bvw);
        let ule = |a: Box<Formula>, b: Box<Formula>| Formula::BvULe(a, b, bvw);
        let umax = u64::MAX as i128;
        let sat = Formula::And(vec![
            ule(bv(0), idx()),
            ule(idx(), bv(umax)),
            ult(idx(), bv(10)),
            ule(bv(5), idx()),
        ]);
        assert!(
            certify_violation(&sat).is_none(),
            "satisfiable `idx <u 10 ∧ 5 ≤u idx` must NOT certify"
        );
    }

    fn native_planning_unsigned_bv_vc(
        variable_name: &str,
        violation_bound: i128,
    ) -> VerificationCondition {
        let bvw = 64;
        let idx = || Box::new(Formula::Var(variable_name.to_string(), Sort::BitVec(bvw)));
        let bv = |value: i128| Box::new(Formula::BitVec { value, width: bvw });
        let ult = |left: Box<Formula>, right: Box<Formula>| Formula::BvULt(left, right, bvw);
        let ule = |left: Box<Formula>, right: Box<Formula>| Formula::BvULe(left, right, bvw);
        VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "demo::guarded_index".into(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 12,
                col_start: 4,
                line_end: 12,
                col_end: 10,
            },
            formula: Formula::And(vec![
                Formula::And(vec![ule(bv(0), idx()), ule(idx(), bv(u64::MAX as i128))]),
                ult(idx(), bv(10)),
                ule(bv(violation_bound), idx()),
            ]),
            contract_metadata: None,
        }
    }

    /// The native-planning entry point admits the exact guarded-index family,
    /// emits deterministic full-VC-lineage evidence, and pairs with the public
    /// full-VC rechecker.
    #[test]
    fn native_planning_bv_order_exact_certifies_deterministically_and_rechecks() {
        let vc = native_planning_unsigned_bv_vc("idx", 10);
        assert_eq!(preflight_unsigned_bv_order_vc_for_native_planning(&vc), Ok(()));
        assert!(vc_fits_native_planning_certification_budget(&vc));

        let first = certify_vc_for_native_planning(&vc)
            .expect("the exact bounded guarded-index contradiction must certify");
        let second = certify_vc_for_native_planning(&vc)
            .expect("repeated bounded certification must succeed deterministically");
        let ProofEvidence::CleanCic {
            term: first_term,
            context: first_context,
            lineage: first_lineage,
            ..
        } = &first
        else {
            panic!("native planning may return only CleanCic evidence");
        };
        let ProofEvidence::CleanCic {
            term: second_term,
            context: second_context,
            lineage: second_lineage,
            ..
        } = &second
        else {
            panic!("native planning may return only CleanCic evidence");
        };
        assert_eq!(first_term, second_term, "proof serialization must be deterministic");
        assert_eq!(first_context, second_context, "proof context must be deterministic");
        assert_eq!(first_lineage, second_lineage, "lineage must be deterministic");
        assert!(recheck_vc(&vc, first_term, first_context, first_lineage));
        assert!(replay_vc_evidence(&vc, &first));

        let mut other_vc = vc.clone();
        other_vc.location.line_start += 1;
        assert!(
            !recheck_vc(&other_vc, first_term, first_context, first_lineage),
            "the planning certificate must remain bound to the exact source VC"
        );
    }

    /// A satisfiable member of the same bounded syntax stays fail-closed.
    #[test]
    fn native_planning_bv_order_satisfiable_declines() {
        let vc = native_planning_unsigned_bv_vc("idx", 5);
        assert_eq!(preflight_unsigned_bv_order_vc_for_native_planning(&vc), Ok(()));
        assert!(
            vc_fits_native_planning_certification_budget(&vc),
            "the resource predicate must not pretend to be a satisfiability verdict"
        );
        assert!(
            certify_vc_for_native_planning(&vc).is_none(),
            "idx = 7 satisfies `idx <u 10 ∧ 5 ≤u idx`"
        );
    }

    /// Even a tiny contradiction supported by the general certifier is outside
    /// the planning lane unless it is the exact unsigned-BV bounds-check family.
    #[test]
    fn native_planning_declines_other_certifier_families_before_solver() {
        let mut vc = contradiction_vc();
        vc.kind = VcKind::IndexOutOfBounds;
        assert!(certify_vc(&vc).is_some(), "negative control must be generally certifiable");
        assert_eq!(
            preflight_unsigned_bv_order_vc_for_native_planning(&vc),
            Err(NativePlanningPreflightFailure::UnsupportedFormulaNode)
        );
        assert!(certify_vc_for_native_planning(&vc).is_none());
    }

    /// Oversized formulas are rejected by the iterative node budget before
    /// normalization. The balanced tree remains shallow and has one top-level
    /// conjunct, isolating the node cap from the depth/conjunct caps.
    #[test]
    fn native_planning_oversized_formula_declines_in_preflight() {
        fn balanced_eq(depth: usize) -> Formula {
            if depth == 0 {
                Formula::Bool(true)
            } else {
                Formula::Eq(Box::new(balanced_eq(depth - 1)), Box::new(balanced_eq(depth - 1)))
            }
        }

        let mut vc = native_planning_unsigned_bv_vc("idx", 10);
        vc.formula = balanced_eq(7); // 255 nodes, depth 8.
        assert_eq!(
            preflight_unsigned_bv_order_vc_for_native_planning(&vc),
            Err(NativePlanningPreflightFailure::FormulaNodes)
        );
        assert!(certify_vc_for_native_planning(&vc).is_none());
    }

    /// Deep nesting is rejected iteratively before the recursive normalizer can
    /// observe it.
    #[test]
    fn native_planning_deep_formula_declines_in_preflight() {
        let mut formula = Formula::Bool(true);
        for _ in 0..NATIVE_PLANNING_MAX_FORMULA_DEPTH {
            formula = Formula::And(vec![formula]);
        }
        let mut vc = native_planning_unsigned_bv_vc("idx", 10);
        vc.formula = formula;
        assert_eq!(
            preflight_unsigned_bv_order_vc_for_native_planning(&vc),
            Err(NativePlanningPreflightFailure::FormulaDepth)
        );
        assert!(certify_vc_for_native_planning(&vc).is_none());
    }

    /// Aggregate identifier bytes are charged before identity serialization,
    /// normalization, fresh-carrier formatting, or solver entry.
    #[test]
    fn native_planning_huge_variable_name_declines_in_preflight() {
        let huge_name = "x".repeat(NATIVE_PLANNING_MAX_STRING_BYTES + 1);
        let vc = native_planning_unsigned_bv_vc(&huge_name, 10);
        assert_eq!(
            preflight_unsigned_bv_order_vc_for_native_planning(&vc),
            Err(NativePlanningPreflightFailure::StringBytes)
        );
        assert!(!vc_fits_native_planning_certification_budget(&vc));
        assert!(certify_vc_for_native_planning(&vc).is_none());
    }

    /// A single wide `And` is rejected independently of the aggregate node
    /// budget, bounding per-node iteration and normalization fanout.
    #[test]
    fn native_planning_wide_fanout_declines_in_preflight() {
        let mut vc = native_planning_unsigned_bv_vc("idx", 10);
        vc.formula = Formula::And(vec![Formula::Bool(true); NATIVE_PLANNING_MAX_NODE_FANOUT + 1]);
        assert_eq!(
            preflight_unsigned_bv_order_vc_for_native_planning(&vc),
            Err(NativePlanningPreflightFailure::NodeFanout)
        );
        assert!(certify_vc_for_native_planning(&vc).is_none());
    }

    /// A balanced tree isolates the flattened-conjunct/pair-scan budget: it is
    /// shallow, binary-fanout, and well below the total node cap.
    #[test]
    fn native_planning_too_many_conjuncts_declines_in_preflight() {
        fn balanced_and(leaves: usize) -> Formula {
            if leaves == 1 {
                Formula::Bool(true)
            } else {
                let left = leaves / 2;
                Formula::And(vec![balanced_and(left), balanced_and(leaves - left)])
            }
        }

        let mut vc = native_planning_unsigned_bv_vc("idx", 10);
        vc.formula = balanced_and(NATIVE_PLANNING_MAX_CONJUNCTS + 1);
        assert_eq!(
            preflight_unsigned_bv_order_vc_for_native_planning(&vc),
            Err(NativePlanningPreflightFailure::Conjuncts)
        );
        assert!(certify_vc_for_native_planning(&vc).is_none());
    }

    #[test]
    fn native_planning_rejects_wrong_kind_width_and_direction() {
        let mut wrong_kind = native_planning_unsigned_bv_vc("idx", 10);
        wrong_kind.kind = VcKind::SliceBoundsCheck;
        assert_eq!(
            preflight_unsigned_bv_order_vc_for_native_planning(&wrong_kind),
            Err(NativePlanningPreflightFailure::UnsupportedVcKind)
        );

        let mut wrong_width = native_planning_unsigned_bv_vc("idx", 10);
        wrong_width.formula = Formula::Var("idx".to_string(), Sort::BitVec(127));
        assert_eq!(
            preflight_unsigned_bv_order_vc_for_native_planning(&wrong_width),
            Err(NativePlanningPreflightFailure::UnsupportedFormulaNode)
        );

        let w = 64;
        let idx = || Box::new(Formula::Var("idx".to_string(), Sort::BitVec(w)));
        let bv = |value: i128| Box::new(Formula::BitVec { value, width: w });
        let ule = |left: Box<Formula>, right: Box<Formula>| Formula::BvULe(left, right, w);
        let ult = |left: Box<Formula>, right: Box<Formula>| Formula::BvULt(left, right, w);
        let mut wrong_direction = native_planning_unsigned_bv_vc("idx", 10);
        wrong_direction.formula = Formula::And(vec![
            ule(bv(0), idx()),
            ule(idx(), bv(u64::MAX as i128)),
            ult(idx(), bv(10)),
            ule(idx(), bv(10)),
        ]);
        assert_eq!(
            preflight_unsigned_bv_order_vc_for_native_planning(&wrong_direction),
            Ok(()),
            "direction is the recognizer's semantic gate, not a preflight size concern"
        );
        assert!(
            certify_vc_for_native_planning(&wrong_direction).is_none(),
            "satisfiable wrong-direction order atoms must decline"
        );
    }

    /// Identity allocation has its own byte cap after the cheaper aggregate
    /// string budget; contract metadata is excluded explicitly before either
    /// identity sizing or serialization.
    #[test]
    fn native_planning_identity_and_metadata_decline_before_serialization() {
        let mut oversized_identity = native_planning_unsigned_bv_vc("idx", 10);
        oversized_identity.location.file = "f".repeat(NATIVE_PLANNING_MAX_IDENTITY_BYTES as usize);
        assert_eq!(
            preflight_unsigned_bv_order_vc_for_native_planning(&oversized_identity),
            Err(NativePlanningPreflightFailure::IdentityBytes)
        );
        assert!(certify_vc_for_native_planning(&oversized_identity).is_none());

        let mut metadata = native_planning_unsigned_bv_vc("idx", 10);
        metadata.contract_metadata = Some(trust_types::ContractMetadata::default());
        assert_eq!(
            preflight_unsigned_bv_order_vc_for_native_planning(&metadata),
            Err(NativePlanningPreflightFailure::ContractMetadata)
        );
        assert!(certify_vc_for_native_planning(&metadata).is_none());
    }

    /// The NEGATED-RETURN postcondition branch — the exact captured
    /// `verify_postcondition_safe` negative-branch VC (`if x < 0 { -x }` under
    /// `ensures result ≥ 0`): i32 bounds on `x`, reified branch flags, the path
    /// guards, the return relation `_0 = -x` (+ aliases), and the violated
    /// ensures `¬(_0 ≥ 0)` — must certify via
    /// `certify_negated_return_via_neg_bound`.
    #[test]
    fn certifies_negated_return_postcondition_branch() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let ret = || Formula::Var("_0".to_string(), Sort::Int);
        let i = Formula::Int;
        let i32_min = -2_147_483_648i128;
        let i32_max = 2_147_483_647i128;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let not = |f: Formula| Formula::Not(Box::new(f));
        let neg_x = || Formula::Neg(Box::new(x()));
        let bool_var = |n: &str| Formula::Var(n.to_string(), Sort::Bool);
        let violation = Formula::And(vec![
            Formula::And(vec![ge(x(), i(i32_min)), le(x(), i(i32_max))]),
            // Reified branch flags (view-dropped Bool reifications).
            eq(bool_var("_4"), eq(x(), i(i32_min))),
            eq(bool_var("_5"), lt(x(), i(0))),
            // Path guards: not the MIN branch; the negative branch taken.
            not(eq(x(), i(i32_min))),
            lt(x(), i(0)),
            not(bool_var("_6")),
            // Return relation + aliases.
            eq(ret(), neg_x()),
            eq(Formula::Var("_3".to_string(), Sort::Int), neg_x()),
            eq(ret(), Formula::Var("__ret#s4_0".to_string(), Sort::Int)),
            // The violated ensures `¬(result ≥ 0)`.
            not(ge(ret(), i(0))),
        ]);
        assert!(
            certify_violation(&violation).is_some(),
            "`_0 = -x ∧ x < 0 ∧ ¬(_0 ≥ 0)` (abs negative branch) must certify"
        );
    }

    /// FAIL-CLOSED: non-linear / bitvector leakage anywhere in the pool declines
    /// the negated-return recognizer (the pool is no longer the recognized
    /// branch family), even though the core contradiction is still present.
    #[test]
    fn negated_return_fails_closed_on_foreign_leakage() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let ret = || Formula::Var("_0".to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let not = |f: Formula| Formula::Not(Box::new(f));
        let base = |extra: Formula| {
            Formula::And(vec![
                ge(x(), i(-2_147_483_648)),
                le(x(), i(2_147_483_647)),
                lt(x(), i(0)),
                eq(ret(), Formula::Neg(Box::new(x()))),
                not(ge(ret(), i(0))),
                extra,
            ])
        };
        // NON-LINEAR leakage: `_9 = x * x`.
        let with_mul = base(eq(
            Formula::Var("_9".to_string(), Sort::Int),
            Formula::Mul(Box::new(x()), Box::new(x())),
        ));
        assert!(
            certify_violation(&with_mul).is_none(),
            "a non-linear `x * x` conjunct must fail the leakage gate (decline)"
        );
        // BITVECTOR leakage: an unsigned BV order atom in the pool.
        let with_bv = base(Formula::BvULe(
            Box::new(Formula::BitVec { value: 0, width: 32 }),
            Box::new(Formula::Var("bvi".to_string(), Sort::BitVec(32))),
            32,
        ));
        assert!(
            certify_violation(&with_bv).is_none(),
            "a bitvector conjunct must fail the leakage gate (decline)"
        );
    }

    /// SOUNDNESS: the WRONG GUARD SIGN is a satisfiable family — `_0 = -x ∧
    /// 0 < x ∧ ¬(_0 ≥ 0)` holds at x = 5, _0 = -5 — and must decline.
    #[test]
    fn negated_return_fails_closed_on_wrong_guard_sign() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let ret = || Formula::Var("_0".to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let not = |f: Formula| Formula::Not(Box::new(f));
        let sat = Formula::And(vec![
            ge(x(), i(-2_147_483_648)),
            le(x(), i(2_147_483_647)),
            // Wrong sign: `0 < x` instead of the negative-branch guard `x < 0`.
            lt(i(0), x()),
            eq(ret(), Formula::Neg(Box::new(x()))),
            not(ge(ret(), i(0))),
        ]);
        assert!(
            certify_violation(&sat).is_none(),
            "satisfiable `_0 = -x ∧ 0 < x ∧ ¬(_0 ≥ 0)` must NOT certify"
        );
    }

    /// SOUNDNESS: a wrong-DIRECTION violation is a satisfiable family —
    /// `_0 = -x ∧ x < 0 ∧ ¬(_0 ≤ 0)` holds at x = -3, _0 = 3 — and must decline
    /// (the recognizer matches only the `¬(r ≥ 0)` ensures shape).
    #[test]
    fn negated_return_fails_closed_on_wrong_direction_violation() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let ret = || Formula::Var("_0".to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let not = |f: Formula| Formula::Not(Box::new(f));
        let sat = Formula::And(vec![
            ge(x(), i(-2_147_483_648)),
            le(x(), i(2_147_483_647)),
            lt(x(), i(0)),
            eq(ret(), Formula::Neg(Box::new(x()))),
            // Wrong direction: `¬(_0 ≤ 0)` instead of `¬(_0 ≥ 0)`.
            not(le(ret(), i(0))),
        ]);
        assert!(
            certify_violation(&sat).is_none(),
            "satisfiable `_0 = -x ∧ x < 0 ∧ ¬(_0 ≤ 0)` must NOT certify"
        );
    }

    /// `(h % num_partitions.max(1)) as u32`: the cast-overflow violation
    /// `Or([_5<0, _5>u32::MAX])` on `_5 = h % n` is refuted by the VARIABLE-divisor
    /// Euclidean range `_5 < n` chained with `n ≤ u32::MAX` (and `_5 ≥ 0` from `h ≥ 0`).
    #[test]
    fn certifies_variable_divisor_modulo_cast_bound() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let u32_max = 4_294_967_295;
        let violation = Formula::And(vec![
            ge(v("h"), i(0)),
            ge(v("n"), i(1)),
            le(v("n"), i(u32_max)),
            eq(v("k"), Formula::Rem(Box::new(v("h")), Box::new(v("n")))),
            Formula::Or(vec![lt(v("k"), i(0)), gt(v("k"), i(u32_max))]),
        ]);
        assert!(
            certify_violation(&violation).is_some(),
            "cast overflow on `k = h%n`, `1≤n≤u32::MAX` must certify via `k<n≤u32::MAX`"
        );
    }

    #[test]
    fn certifies_modulo_index_result_bound() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        // `Or([8 = 0, _3 < 8]) ∧ _3 >= 8` (+ the `_3 = i%8` binding, dropped).
        let violation = Formula::And(vec![
            Formula::Or(vec![eq(i(8), i(0)), lt(v("_3"), i(8))]),
            eq(v("_3"), Formula::Rem(Box::new(v("i")), Box::new(i(8)))),
            ge(v("_3"), i(8)),
        ]);
        assert!(
            certify_violation(&violation).is_some(),
            "modulo-index result-bound `Or([8=0, _3<8]) ∧ _3>=8` must certify"
        );
    }

    /// SOUNDNESS: a disjunctive fact whose disjuncts are BOTH satisfiable against
    /// the context must decline — `Or([8=0, _3<8]) ∧ _3>=4` (the violation `_3>=4`
    /// is consistent with `_3<8`, e.g. `_3=5`).
    #[test]
    fn modulo_disjunctive_fails_closed_when_consistent() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let sat = Formula::And(vec![
            Formula::Or(vec![eq(i(8), i(0)), lt(v("_3"), i(8))]),
            ge(v("_3"), i(4)),
        ]);
        assert!(
            certify_violation(&sat).is_none(),
            "`Or([8=0, _3<8]) ∧ _3>=4` is satisfiable (_3=5) — must NOT certify"
        );
    }

    /// A guarded narrowing cast `if 0<=x && x<256 { x as u8 }`: violation
    /// `x>=0 ∧ x<256 ∧ Or([x<0, x>255])`. The `x>255` disjunct vs guard `x<256`
    /// needs INTEGER tightness — `x<256 ⟹ x≤255`, giving `255<x≤255 ⊢ 255<255`.
    #[test]
    fn certifies_guarded_narrowing_cast_with_integer_tightness() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let i = Formula::Int;
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let guarded_cast = Formula::And(vec![
            ge(x(), i(0)),
            lt(x(), i(256)),
            Formula::Or(vec![lt(x(), i(0)), gt(x(), i(255))]),
        ]);
        assert!(
            certify_violation(&guarded_cast).is_some(),
            "guarded narrowing cast `if 0<=x && x<256 {{x as u8}}` must certify"
        );
    }

    /// SOUNDNESS: integer tightness must not over-strengthen — `100 < x ∧ x < 256`
    /// is satisfiable (x ∈ 101..=255), so it must decline.
    #[test]
    fn integer_tightness_fails_closed_on_satisfiable_strict_bounds() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let i = Formula::Int;
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        // `100 < x ∧ x < 256` — satisfiable; must NOT certify.
        let sat = Formula::And(vec![gt(x(), i(100)), lt(x(), i(256))]);
        assert!(
            certify_violation(&sat).is_none(),
            "satisfiable strict interval `100 < x < 256` must NOT certify"
        );
    }

    /// Guarded TWO-VARIABLE addition `if a<1000 && b<1000 { a+b }` (u32, Int
    /// overflow): violation `a<1000 ∧ b<1000 ∧ 0<=a ∧ 0<=b ∧ Or([a+b<0, a+b>MAX])`.
    /// The lift `a<=999 ∧ b<=999 ⟹ a+b<=1998` contradicts `a+b>MAX`; `0<=a ∧ 0<=b
    /// ⟹ 0<=a+b` contradicts `a+b<0`.
    #[test]
    fn certifies_guarded_two_variable_addition() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let max = 4_294_967_295i128;
        let guarded_add = Formula::And(vec![
            lt(v("a"), i(1000)),
            lt(v("b"), i(1000)),
            le(i(0), v("a")),
            le(i(0), v("b")),
            Formula::Or(vec![lt(add(v("a"), v("b")), i(0)), gt(add(v("a"), v("b")), i(max))]),
        ]);
        assert!(
            certify_violation(&guarded_add).is_some(),
            "guarded two-variable addition `if a<1000 && b<1000 {{a+b}}` must certify"
        );
    }

    /// SOUNDNESS: weak two-variable guards do NOT rule out the sum overflowing —
    /// `a<3000000000 ∧ b<3000000000 ∧ … ∧ Or([a+b<0, a+b>MAX])` is SAT (the sum can
    /// exceed u32::MAX), so it must decline.
    #[test]
    fn guarded_two_variable_addition_fails_closed_when_guards_weak() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let max = 4_294_967_295i128;
        let weak = Formula::And(vec![
            lt(v("a"), i(3_000_000_000)),
            lt(v("b"), i(3_000_000_000)),
            le(i(0), v("a")),
            le(i(0), v("b")),
            Formula::Or(vec![lt(add(v("a"), v("b")), i(0)), gt(add(v("a"), v("b")), i(max))]),
        ]);
        assert!(
            certify_violation(&weak).is_none(),
            "weak guards `a,b < 3e9` do NOT rule out `a+b > u32::MAX` — must fail closed"
        );
    }

    /// MB milestone-2b: SYMBOLIC unsigned-add no-overflow at width 4. The LIVE
    /// pipeline routes symbolic `a + b` to the Int/LIA path, so a guarded 4-bit
    /// add `if a<8 && b<8 { a+b }` (a+b ≤ 14 ≤ u4::MAX=15, no wrap) certifies its
    /// no-overflow obligation `a<8 ∧ b<8 ∧ 0<=a ∧ 0<=b ∧ Or([a+b<0, a+b>15])` as
    /// UNSAT via the additive-lift chain (a<=7,b<=7 ⟹ a+b<=14<15; 0<=a,0<=b ⟹
    /// 0<=a+b), kernel-re-checked. GENUINELY PROVEN — zero new axioms, no
    /// bit-blasting: clean's BitVec is the Nat/Int carrier, so the existing Int
    /// additive lift (Int.add_le_add_left/right + Int.lt_irrefl, constructive
    /// Theorems) subsumes the adder argument the bit-blasting bridge would prove.
    #[test]
    fn certifies_milestone_2b_width4_symbolic_add() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        // u4::MAX = 15; guard a<8 ∧ b<8 ⟹ a+b ≤ 14, no wrap.
        let guarded = Formula::And(vec![
            lt(v("a"), i(8)),
            lt(v("b"), i(8)),
            le(i(0), v("a")),
            le(i(0), v("b")),
            Formula::Or(vec![lt(add(v("a"), v("b")), i(0)), gt(add(v("a"), v("b")), i(15))]),
        ]);
        assert!(
            certify_violation(&guarded).is_some(),
            "width-4 guarded symbolic add `if a<8 && b<8 {{a+b}}` must certify no-overflow"
        );
    }

    /// Without a no-wrap guard, width-4 symbolic add CAN overflow: `a<16 ∧ b<16`
    /// allows a+b up to 30 > 15, so the obligation is SAT and must fail closed —
    /// the soundness guard for the adder milestone.
    #[test]
    fn milestone_2b_width4_add_fails_closed_without_nowrap_guard() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let weak = Formula::And(vec![
            lt(v("a"), i(16)),
            lt(v("b"), i(16)),
            le(i(0), v("a")),
            le(i(0), v("b")),
            Formula::Or(vec![lt(add(v("a"), v("b")), i(0)), gt(add(v("a"), v("b")), i(15))]),
        ]);
        assert!(
            certify_violation(&weak).is_none(),
            "weak guards `a,b < 16` do NOT rule out `a+b > 15` — must fail closed"
        );
    }

    /// Guarded MULTIPLICATION `if x<100 { x*2 }` (u8): violation
    /// `x<100 ∧ 0<=x ∧ Or([x*2<0, x*2>255])`. The lift `x<=99 ⟹ x*2<=198` (via
    /// `Int.mul_le_mul_of_nonneg_right`) contradicts `x*2>255`; `0<=x ⟹ 0<=x*2`
    /// contradicts `x*2<0`.
    #[test]
    fn certifies_guarded_multiplication() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let i = Formula::Int;
        let mul = |a: Formula, c: i128| Formula::Mul(Box::new(a), Box::new(i(c)));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let guarded_mul = Formula::And(vec![
            lt(x(), i(100)),
            le(i(0), x()),
            Formula::Or(vec![lt(mul(x(), 2), i(0)), gt(mul(x(), 2), i(255))]),
        ]);
        assert!(
            certify_violation(&guarded_mul).is_some(),
            "guarded multiplication `if x<100 {{x*2}}` must certify"
        );
    }

    /// SOUNDNESS: an unguarded multiplication (or one whose guard is too weak)
    /// has a satisfiable overflow disjunct — `x<200 ∧ 0<=x ∧ Or([x*2<0, x*2>255])`
    /// is SAT (e.g. x=150 ⟹ x*2=300>255), so it must decline.
    #[test]
    fn guarded_multiplication_fails_closed_when_guard_too_weak() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let i = Formula::Int;
        let mul = |a: Formula, c: i128| Formula::Mul(Box::new(a), Box::new(i(c)));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let weak = Formula::And(vec![
            lt(x(), i(200)),
            le(i(0), x()),
            Formula::Or(vec![lt(mul(x(), 2), i(0)), gt(mul(x(), 2), i(255))]),
        ]);
        assert!(
            certify_violation(&weak).is_none(),
            "weak guard `x<200` does NOT rule out `x*2>255` — must fail closed"
        );
    }

    /// SOUNDNESS: an UNGUARDED arithmetic op (no guard ruling out overflow) has a
    /// satisfiable disjunct, so the disjunctive path must decline.
    #[test]
    fn disjunctive_path_fails_closed_on_unguarded_arithmetic() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let i = Formula::Int;
        let sub = |a: Formula, b: Formula| Formula::Sub(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let max = 4_294_967_295i128;
        // No guard on x (only the u32 range): `x - 10 < 0` is SAT (x ∈ [0,9]),
        // so the underflow disjunct cannot be refuted → must fail closed.
        let unguarded = Formula::And(vec![
            le(i(0), x()),
            le(x(), i(max)),
            Formula::Or(vec![lt(sub(x(), i(10)), i(0)), gt(sub(x(), i(10)), i(max))]),
        ]);
        assert!(
            certify_violation(&unguarded).is_none(),
            "unguarded subtraction must NOT certify (real underflow risk)"
        );
    }

    /// Multi-variable transitive chain — the shape a constant index on a guarded
    /// symbolic-length slice (`if s.len() > 5 { s[3] }`) produces:
    /// `_4 = 3 ∧ _5 = len ∧ _4 ≥ _5 ∧ len > 5` chains `5 < len ≤ _5 ≤ _4 ≤ 3`
    /// to the closed false `5 < 3`. ay's Farkas can't (symbolic endpoints) and the
    /// single-var path can't (multiple vars); the chain refutation closes it.
    #[test]
    fn certifies_multi_var_transitive_chain_contradiction() {
        let var = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let violation = Formula::And(vec![
            eq(var("a"), i(3)),       // a = 3
            eq(var("b"), var("len")), // b = len
            ge(var("a"), var("b")),   // a >= b   (3 >= len)
            gt(var("len"), i(5)),     // len > 5
        ]);
        assert!(
            certify_violation(&violation).is_some(),
            "multi-variable transitive chain `5 < len ≤ b ≤ a ≤ 3` must certify"
        );
    }

    /// SOUNDNESS: the transitive chain must not refute a SATISFIABLE multi-var
    /// system (no conflicting constant endpoints).
    #[test]
    fn transitive_chain_fails_closed_on_satisfiable_system() {
        let var = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        // `a = 3 ∧ b = len ∧ a ≤ b ∧ len ≥ 2` — satisfiable (len ≥ 3); must decline.
        let sat = Formula::And(vec![
            eq(var("a"), i(3)),
            eq(var("b"), var("len")),
            le(var("a"), var("b")),
            Formula::Ge(Box::new(var("len")), Box::new(i(2))),
        ]);
        assert!(certify_violation(&sat).is_none(), "satisfiable multi-var chain must NOT certify");
    }

    /// A genuine multi-variable Farkas combination with NEGATIVE coefficients —
    /// `x0 ≤ 1 ∧ 2·x0 − x1 ≥ −3 ∧ x1 ≥ 10`, witness λ=(2,1,1) giving the closed
    /// false `5 ≤ 0` — certifies via [`multi_var_farkas_refutation`]. This shape
    /// is refutable by NEITHER the single-variable interval NOR the transitive
    /// chain path (both scale by non-negative constants only).
    #[test]
    fn certifies_multi_var_negative_coefficient_farkas() {
        let var = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let mul = |c: i128, v: &str| Formula::Mul(Box::new(i(c)), Box::new(var(v)));
        // 2·x0 − x1 ≥ −3, encoded as the bridge does (coeff −1 → Mul(-1, x1)).
        let violation = Formula::And(vec![
            Formula::Le(Box::new(var("x0")), Box::new(i(1))),
            Formula::Ge(
                Box::new(Formula::Add(Box::new(mul(2, "x0")), Box::new(mul(-1, "x1")))),
                Box::new(i(-3)),
            ),
            Formula::Ge(Box::new(var("x1")), Box::new(i(10))),
        ]);
        let evidence = certify_violation(&violation)
            .expect("multi-var negative-coefficient Farkas must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(!term.is_empty());
        assert!(!context.is_empty());
        assert_ne!(lineage, trust_ir::ProofDigest::zero());
        // Independently re-check the serialized payload through the clean kernel.
        let mut vars = BTreeSet::new();
        vars.insert("x0".to_string());
        vars.insert("x1".to_string());
        assert!(
            payload_roundtrip_rechecks(&vars, &term, &context),
            "serialized multi-var Farkas payload must re-check to False"
        );
        assert!(recheck_cleancic(&term, &context, &lineage, &violation));
    }

    /// SOUNDNESS: a SATISFIABLE multi-variable system with negative coefficients
    /// must NEVER be certified. `2·x0 − x1 ≥ −3 ∧ x0 ≤ 5 ∧ 0 ≤ x1 ≤ 4` has the
    /// model `x0 = 0, x1 = 0`; the Farkas witness finder returns no contradiction
    /// row, so [`multi_var_farkas_refutation`] fails closed and the end-to-end
    /// path declines.
    #[test]
    fn multi_var_farkas_fails_closed_on_satisfiable_system() {
        let var = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let mul = |c: i128, v: &str| Formula::Mul(Box::new(i(c)), Box::new(var(v)));
        let sat = Formula::And(vec![
            Formula::Ge(
                Box::new(Formula::Add(Box::new(mul(2, "x0")), Box::new(mul(-1, "x1")))),
                Box::new(i(-3)),
            ),
            Formula::Le(Box::new(var("x0")), Box::new(i(5))),
            Formula::Ge(Box::new(var("x1")), Box::new(i(0))),
            Formula::Le(Box::new(var("x1")), Box::new(i(4))),
        ]);
        assert!(
            certify_violation(&sat).is_none(),
            "satisfiable multi-var negative-coefficient system must NOT certify"
        );
        // Belt-and-suspenders: the refutation builder itself fails closed at the
        // source (no Farkas witness), independent of the ay SAT backstop.
        let mut conjuncts: Vec<&Formula> = Vec::new();
        collect_conjuncts(&sat, &mut conjuncts);
        let (atoms, _) = collect_supported_atoms(&conjuncts);
        let hyps = supported_hyps_from_atoms(&atoms).expect("hyps");
        assert!(
            multi_var_farkas_refutation(&atoms, &hyps).is_none(),
            "multi_var_farkas_refutation must return None on a satisfiable system"
        );
    }

    /// SOUNDNESS: a SATISFIABLE single-variable interval (no real conflict) must
    /// never be refuted by the interval path.
    #[test]
    fn single_var_interval_path_fails_closed_on_satisfiable_bounds() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        // `2 ≤ x ∧ x ≤ 4` — satisfiable (x ∈ {2,3,4}); must fail closed.
        assert!(
            certify_violation(&Formula::And(vec![le(i(2), x()), le(x(), i(4))])).is_none(),
            "satisfiable interval `2 ≤ x ≤ 4` must NOT certify"
        );
        // `0 ≤ x ∧ x ≤ 0` — satisfiable (x = 0); must fail closed.
        assert!(
            certify_violation(&Formula::And(vec![le(i(0), x()), le(x(), i(0))])).is_none(),
            "satisfiable point interval `0 ≤ x ≤ 0` must NOT certify"
        );
    }

    /// The closed refutation extends to the strict-false boundary `a < a`, and a
    /// lone false atom certifies just like the disjunction.
    #[test]
    fn certifies_lone_closed_false_atom_and_strict_boundary() {
        assert!(
            certify_violation(&Formula::Lt(Box::new(Formula::Int(3)), Box::new(Formula::Int(3))))
                .is_some(),
            "3<3 is false — must certify"
        );
        assert!(
            certify_violation(&Formula::Lt(Box::new(Formula::Int(2)), Box::new(Formula::Int(0))))
                .is_some(),
            "lone 2<0 must certify"
        );
    }

    /// Guarded single-variable subtraction `if x > 10 { x - 10 }` (u32): violation
    /// `x>10 ∧ x<=MAX ∧ Or([x-10<0, x-10>MAX])`. Handled by the existing
    /// The REAL `guarded_subtraction.rs` shape (from a CERTDUMP of the live
    /// compiler): a CONJUNCTION of u8 type bounds + the guard `a >= b` + the
    /// SINGLE underflow atom `Sub(a,b) < 0` — NO `Or` disjunction (a u8 `a-b`
    /// under `a>=b` has only the underflow obligation, no overflow disjunct). This
    /// exercises the transitive-chain (conjunction) path, NOT the disjunctive one.
    #[test]
    fn certifies_real_guarded_subtraction_conjunction_shape() {
        let a = || Formula::Var("a".to_string(), Sort::Int);
        let b = || Formula::Var("b".to_string(), Sort::Int);
        let i = Formula::Int;
        let viol = Formula::And(vec![
            Formula::Ge(Box::new(a()), Box::new(b())), // guard a >= b
            Formula::Le(Box::new(i(0)), Box::new(a())),
            Formula::Le(Box::new(a()), Box::new(i(255))),
            Formula::Le(Box::new(i(0)), Box::new(b())),
            Formula::Le(Box::new(b()), Box::new(i(255))),
            Formula::Lt(Box::new(Formula::Sub(Box::new(a()), Box::new(b()))), Box::new(i(0))),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "real guarded u8 subtraction underflow (conjunction, single Sub<0 atom) must certify"
        );
    }

    /// The REAL `merged_local_index.rs` violation, reproduced verbatim from the
    /// `AY_CERT_DUMP=1 trustc` dump (`step = if c {1} else
    /// {2}; if s.len() > 2 { s[step] }`). Outer `Or([branch_¬c, branch_c])`; each
    /// branch carries the merge fact `Eq(step, Ite(¬c, 2, 1))`, the guard
    /// `s_len > 2`, the index/length aliases, and the OOB violation `_6 ≥ _7`. The
    /// `Ite`-index reduction emits `Or([step ≤ 2, step ≤ 1])`, which the
    /// disjunctive refutation closes (`2 < s_len ≤ step ≤ 2/1`). Kernel re-checked.
    #[test]
    fn certifies_real_merged_local_index_ite_shape() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let bv = |n: &str| Formula::Var(n.to_string(), Sort::Bool);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let not = |f: Formula| Formula::Not(Box::new(f));
        // `step = Ite(¬c, 2, 1)` — the SwitchInt-join merge fact (identical in both branches).
        let ite_merge = || {
            eq(
                v("step#s1_0_s2_0"),
                Formula::Ite(Box::new(not(bv("c"))), Box::new(i(2)), Box::new(i(1))),
            )
        };
        let inner = || {
            Formula::And(vec![
                eq(v("_6#s4_0"), v("step#s1_0_s2_0")),
                eq(v("_7#s4_1"), v("s__slice_len")),
                eq(bv("_8#s4_2"), lt(v("_6#s4_0"), v("_7#s4_1"))),
                ge(v("_6#s4_0"), v("_7#s4_1")),
            ])
        };
        let branch = |flag: Formula| {
            Formula::And(vec![
                flag,
                gt(v("s__slice_len"), i(2)),
                Formula::And(vec![
                    ite_merge(),
                    eq(v("_5#s3_0"), v("s__slice_len")),
                    eq(bv("_4#s3_1"), gt(v("_5#s3_0"), i(2))),
                    inner(),
                ]),
            ])
        };
        let viol = Formula::And(vec![
            Formula::Bool(true),
            Formula::Or(vec![branch(not(bv("c"))), branch(bv("c"))]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "real merged_local_index Ite-index shape must kernel-certify"
        );
        assert_formula_certificate_pairs(&viol);
    }

    /// FAIL-CLOSED: the same `Ite`-index branch shape WITHOUT the dominating
    /// `s.len() > 2` guard. Then `step ∈ {1, 2}` is consistent with `step ≥ s_len`
    /// (e.g. `s_len = 1`, `step = 1`), so the obligation is genuinely satisfiable —
    /// the reduction must emit the disjunction but the ay cross-check / kernel
    /// re-check then declines (no contradiction to close).
    #[test]
    fn ite_index_fails_closed_without_dominating_guard() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let bv = |n: &str| Formula::Var(n.to_string(), Sort::Bool);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let not = |f: Formula| Formula::Not(Box::new(f));
        let ite_merge =
            || eq(v("step"), Formula::Ite(Box::new(not(bv("c"))), Box::new(i(2)), Box::new(i(1))));
        // Branch: merge fact + alias + OOB, but NO `s_len > 2` guard.
        let branch = |flag: Formula| {
            Formula::And(vec![
                flag,
                ite_merge(),
                eq(v("_6"), v("step")),
                eq(v("_7"), v("s_len")),
                ge(v("_6"), v("_7")),
            ])
        };
        let viol = Formula::Or(vec![branch(not(bv("c"))), branch(bv("c"))]);
        assert!(
            certify_violation(&viol).is_none(),
            "Ite-index OOB WITHOUT the `s.len() > 2` guard is satisfiable — must fail closed"
        );
    }

    /// FAIL-CLOSED: an `Ite` index whose ELSE branch value is a NON-literal term
    /// (`Ite(¬c, 2, len)`), so `ite_index_branch_values` rejects it (the branch
    /// bound is not a closed integer). The reduction does not fire and, with the
    /// outer-`Or` branches carrying an `Ite`-merge fact the disjunctive path can't
    /// otherwise close, the obligation declines.
    #[test]
    fn ite_index_fails_closed_on_nonliteral_branch() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let bv = |n: &str| Formula::Var(n.to_string(), Sort::Bool);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let not = |f: Formula| Formula::Not(Box::new(f));
        // ELSE branch is `len` (a variable), NOT a closed literal.
        let ite_merge = || {
            eq(v("step"), Formula::Ite(Box::new(not(bv("c"))), Box::new(i(2)), Box::new(v("len"))))
        };
        let branch = |flag: Formula| {
            Formula::And(vec![
                flag,
                gt(v("s_len"), i(2)),
                ite_merge(),
                eq(v("_6"), v("step")),
                eq(v("_7"), v("s_len")),
                ge(v("_6"), v("_7")),
            ])
        };
        let viol = Formula::Or(vec![branch(not(bv("c"))), branch(bv("c"))]);
        assert!(
            certify_violation(&viol).is_none(),
            "Ite index with a non-literal branch value must fail closed (not reduced)"
        );
    }

    /// The real `slice_len_sum.rs` shape (`s.len() + s.len()`): `_2 = _3 = s_len`,
    /// `s_len ≤ isize::MAX` (the slice-length bound) but `_2,_3 ≤ usize::MAX` (loose),
    /// and `Or([_2+_3 < 0, _2+_3 > usize::MAX])`. Certifies only once the tight
    /// `isize::MAX` bound is propagated across the equality class onto `_2,_3`
    /// (`2·isize::MAX = usize::MAX − 1 < usize::MAX`).
    #[test]
    fn certifies_slice_len_sum_via_equality_bound_propagation() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let isize_max = 9_223_372_036_854_775_807i128;
        let usize_max = 18_446_744_073_709_551_615i128;
        let sum = || Formula::Add(Box::new(v("_2")), Box::new(v("_3")));
        let viol = Formula::And(vec![
            Formula::Ge(Box::new(v("s_len")), Box::new(i(0))),
            Formula::Le(Box::new(v("s_len")), Box::new(i(isize_max))),
            Formula::Le(Box::new(i(0)), Box::new(v("_2"))),
            Formula::Le(Box::new(v("_2")), Box::new(i(usize_max))),
            Formula::Le(Box::new(i(0)), Box::new(v("_3"))),
            Formula::Le(Box::new(v("_3")), Box::new(i(usize_max))),
            Formula::Eq(Box::new(v("_2")), Box::new(v("s_len"))),
            Formula::Eq(Box::new(v("_3")), Box::new(v("s_len"))),
            Formula::Or(vec![
                Formula::Lt(Box::new(sum()), Box::new(i(0))),
                Formula::Gt(Box::new(sum()), Box::new(i(usize_max))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "slice_len_sum (equality-class bound propagation) must certify"
        );
    }

    /// `i128_guarded_add` (`if a,b ∈ (-1000,1000) {a+b}`): the type thresholds
    /// `i128::MIN`/`i128::MAX` exceed `u64`, so this exercises the arbitrary-precision
    /// `nat_lit_u128` literal encoding + the kernel reducing `Int` comparison against a
    /// `BigNat::Large` literal. The additive lift uses the tightened guards (`a≤999`),
    /// and the overflow disjunct `a+b > i128::MAX` closes via `1998 < i128::MAX`.
    #[test]
    fn certifies_i128_guarded_add_big_literal() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let imin = i128::MIN;
        let imax = i128::MAX;
        let sum = || Formula::Add(Box::new(v("a")), Box::new(v("b")));
        let viol = Formula::And(vec![
            Formula::Le(Box::new(i(imin)), Box::new(v("a"))),
            Formula::Le(Box::new(v("a")), Box::new(i(imax))),
            Formula::Le(Box::new(i(imin)), Box::new(v("b"))),
            Formula::Le(Box::new(v("b")), Box::new(i(imax))),
            Formula::Lt(Box::new(i(-1000)), Box::new(v("a"))),
            Formula::Lt(Box::new(v("a")), Box::new(i(1000))),
            Formula::Lt(Box::new(i(-1000)), Box::new(v("b"))),
            Formula::Lt(Box::new(v("b")), Box::new(i(1000))),
            Formula::Or(vec![
                Formula::Lt(Box::new(sum()), Box::new(i(imin))),
                Formula::Gt(Box::new(sum()), Box::new(i(imax))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "i128 guarded add with i128::MIN/MAX big literals must certify"
        );
    }

    /// Isolate: does the KERNEL reduce an `Int` comparison against a `BigNat::Large`
    /// literal? Minimal closed-false atom `i128::MAX < 5` (false ⇒ refutable). If this
    /// fails, the kernel needs BigNat arithmetic reduction (not just literal encoding).
    #[test]
    fn big_literal_closed_false_refutes() {
        let viol = Formula::Lt(Box::new(Formula::Int(i128::MAX)), Box::new(Formula::Int(5)));
        assert!(
            certify_violation(&viol).is_some(),
            "closed-false big-literal atom i128::MAX < 5 must certify"
        );
    }

    /// The real `assert_mut_field_identity` shape: a TRANSITIVE var=var disequality
    /// `_4 = a.0 ∧ a.0 = val ∧ _4 != val`. The two vars of the disequality share an
    /// equality class, so `complete_class_disequalities` emits the entailed direct
    /// `_4 = val` and the disequality refutation closes the contradiction.
    #[test]
    fn certifies_transitive_equality_disequality() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let viol = Formula::And(vec![
            Formula::Eq(Box::new(v("_4")), Box::new(v("a.0"))),
            Formula::Eq(Box::new(v("a.0")), Box::new(v("val"))),
            Formula::Not(Box::new(Formula::Eq(Box::new(v("_4")), Box::new(v("val"))))),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "transitive-equality disequality (_4 = a.0 = val ∧ _4 != val) must certify"
        );
    }

    /// Fail-closed: a disequality whose vars are NOT in the same class is genuinely
    /// satisfiable and must decline.
    #[test]
    fn transitive_equality_disequality_fails_closed_when_unrelated() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let viol = Formula::And(vec![
            Formula::Eq(Box::new(v("_4")), Box::new(v("a.0"))),
            Formula::Not(Box::new(Formula::Eq(Box::new(v("_4")), Box::new(v("val"))))),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "unrelated disequality (_4 = a.0 ∧ _4 != val) must NOT certify"
        );
    }

    /// `linear_var_offset` shift (`Sub(x,const)`), NOT the new `Diff` lift — this
    /// is a regression guard that adding the `Diff` arm to `chain_node` did not
    /// disturb the single-variable path.
    #[test]
    fn certifies_guarded_single_variable_subtraction() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let i = Formula::Int;
        let sub = |a: Formula, b: Formula| Formula::Sub(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let max = 4_294_967_295i128;
        let guarded = Formula::And(vec![
            gt(x(), i(10)),
            le(x(), i(max)),
            Formula::Or(vec![lt(sub(x(), i(10)), i(0)), gt(sub(x(), i(10)), i(max))]),
        ]);
        assert!(
            certify_violation(&guarded).is_some(),
            "guarded single-variable subtraction `if x>10 {{x-10}}` must certify"
        );
    }

    /// Guarded TWO-VARIABLE subtraction `if a > b { a - b }` (u32): violation
    /// `b<a ∧ 0<=a ∧ a<=MAX ∧ 0<=b ∧ b<=MAX ∧ Or([a-b<0, a-b>MAX])`. The dominating
    /// guard `a>b` (≡ `b<a`) lifts to `0<=a-b` (closing the underflow disjunct), and
    /// `0<=b` lifts to `a-b<=a<=MAX` (closing the vacuous overflow disjunct). Mirrors
    /// `certifies_guarded_two_variable_addition`. (`guarded_two_var_sub.rs` fixture.)
    #[test]
    fn certifies_guarded_two_variable_subtraction() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let sub = |a: Formula, b: Formula| Formula::Sub(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let max = 4_294_967_295i128;
        let guarded = Formula::And(vec![
            gt(v("a"), v("b")),
            le(i(0), v("a")),
            le(v("a"), i(max)),
            le(i(0), v("b")),
            le(v("b"), i(max)),
            Formula::Or(vec![lt(sub(v("a"), v("b")), i(0)), gt(sub(v("a"), v("b")), i(max))]),
        ]);
        assert!(
            certify_violation(&guarded).is_some(),
            "guarded two-variable subtraction `if a>b {{a-b}}` must certify"
        );
    }

    /// Guarded two-variable subtraction with a NON-STRICT guard `if a >= b { a - b }`
    /// (u8): violation `b<=a ∧ 0<=a ∧ a<=255 ∧ 0<=b ∧ b<=255 ∧ Or([a-b<0, a-b>255])`.
    /// The guard `a>=b` (≡ `b<=a`) is reused directly (no `Int.le_of_lt`).
    /// (`guarded_subtraction.rs` fixture.)
    #[test]
    fn certifies_guarded_two_variable_subtraction_nonstrict_guard() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let sub = |a: Formula, b: Formula| Formula::Sub(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let guarded = Formula::And(vec![
            ge(v("a"), v("b")),
            le(i(0), v("a")),
            le(v("a"), i(255)),
            le(i(0), v("b")),
            le(v("b"), i(255)),
            Formula::Or(vec![lt(sub(v("a"), v("b")), i(0)), gt(sub(v("a"), v("b")), i(255))]),
        ]);
        assert!(
            certify_violation(&guarded).is_some(),
            "guarded two-variable subtraction `if a>=b {{a-b}}` must certify"
        );
    }

    /// SOUNDNESS: an UNGUARDED two-variable subtraction (no `a>=b`/`a>b` dominating
    /// guard) leaves the underflow disjunct `a-b<0` satisfiable (e.g. a=0, b=1), so
    /// it must fail closed — the soundness guard for the `Diff` lift.
    #[test]
    fn guarded_two_variable_subtraction_fails_closed_when_unguarded() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let sub = |a: Formula, b: Formula| Formula::Sub(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let max = 4_294_967_295i128;
        // No `a>b`/`a>=b` guard — only the u32 ranges. `a-b<0` is SAT (a=0,b=1).
        let unguarded = Formula::And(vec![
            le(i(0), v("a")),
            le(v("a"), i(max)),
            le(i(0), v("b")),
            le(v("b"), i(max)),
            Formula::Or(vec![lt(sub(v("a"), v("b")), i(0)), gt(sub(v("a"), v("b")), i(max))]),
        ]);
        assert!(
            certify_violation(&unguarded).is_none(),
            "unguarded two-variable subtraction must NOT certify (real underflow risk)"
        );
    }

    // -----------------------------------------------------------------------
    // Signed wide-BV add/sub no-overflow → linear-Int refutation.
    // These use the EXACT shapes the `i128_guarded_add` / `i128_widened_sub` /
    // `i128_shift_accumulator` fixtures dump (`AY_CERT_DUMP=1`), so they exercise
    // `certify_signed_bv_overflow_safe` end-to-end through the clean kernel.
    // -----------------------------------------------------------------------

    /// Helpers building the BV overflow shapes the router emits.
    fn bv(value: i128, width: u32) -> Formula {
        Formula::BitVec { value, width }
    }
    fn bvvar(name: &str, width: u32) -> Formula {
        Formula::Var(name.to_string(), Sort::BitVec(width))
    }
    /// `i128::MIN` rendered as the unsigned threshold the carry test compares
    /// against (`2^127`), exactly as the dump shows (`value: i128::MIN`).
    fn imin_threshold() -> Formula {
        bv(i128::MIN, 128)
    }
    fn bvult(a: Formula, b: Formula) -> Formula {
        Formula::BvULt(Box::new(a), Box::new(b), 128)
    }
    fn bvslt(a: Formula, b: Formula) -> Formula {
        Formula::BvSLt(Box::new(a), Box::new(b), 128)
    }
    fn bvsle(a: Formula, b: Formula) -> Formula {
        Formula::BvSLe(Box::new(a), Box::new(b), 128)
    }
    fn not(f: Formula) -> Formula {
        Formula::Not(Box::new(f))
    }

    /// The carry-bit overflow disjunction the router emits over `result`:
    /// `Or([ result <u MIN ∧ ¬(x <u MIN), ¬(result <u MIN) ∧ x <u MIN ])`.
    fn carry_overflow_or(result: Formula, x: Formula) -> Formula {
        Formula::Or(vec![
            Formula::And(vec![
                bvult(result.clone(), imin_threshold()),
                not(bvult(x.clone(), imin_threshold())),
            ]),
            Formula::And(vec![not(bvult(result, imin_threshold())), bvult(x, imin_threshold())]),
        ])
    }

    /// `i128_guarded_add`: `if a>-1000 && a<1000 && b>-1000 && b<1000 { a+b }`.
    /// Signed-BV guards `BvSLt(-1000,a) ∧ BvSLt(a,1000) ∧ …` + the carry-bit
    /// overflow disjunction over `BvAdd(a,b,128)`. Bounded sum ∈ (-1998,1998) ⊂
    /// i128 ⇒ no overflow ⇒ UNSAT.
    #[test]
    fn certifies_i128_guarded_add_bv_carry_shape() {
        let a = bvvar("__trust_ovf_bv_lhs_a", 128);
        let b = bvvar("__trust_ovf_bv_rhs_b", 128);
        let sum = Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 128);
        let viol = Formula::And(vec![
            bvslt(bv(-1000, 128), a.clone()),
            bvslt(a.clone(), bv(1000, 128)),
            bvslt(bv(-1000, 128), b.clone()),
            bvslt(b.clone(), bv(1000, 128)),
            // The carry_in test is `Not(Or([...]))` — irrelevant to the bound, so
            // we keep ONLY the carry_out overflow disjunction (the conjunct that
            // asserts overflow). Dropping the `Not(carry_in)` conjunct is sound
            // (it only weakens the asserted violation).
            carry_overflow_or(sum, a),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "i128 guarded add (signed-BV carry overflow shape) must certify"
        );
        assert_formula_certificate_pairs(&viol);
    }

    /// `i128_widened_sub`: `(b as i128) - (a as i128)` over two i64 values widened
    /// by 64→128 sign-extension. The arm RECOGNIZES the shape (the operands are
    /// transparent sign-extensions in `[i64::MIN, i64::MAX]`, difference in
    /// `[-2^64, 2^64] ⊂ i128`). Its result range `±2^64` once exceeded the clean
    /// kernel's native-`Int`-reducer reach (the former `u64` magnitude cap left the
    /// `Int.NonNeg.mk` overflow-witness against the i128 extreme stuck, so the arm
    /// failed closed). With the kernel's `Int` reducer widened to arbitrary i128
    /// magnitude (`env::native_reducers_int`) and `RESULT_MAGNITUDE_LIMIT` lifted to
    /// `2^120`, the witness `Int.sub` now reduces natively and the obligation
    /// kernel-CERTIFIES — the widest Rust integer's sub no-overflow, end to end.
    #[test]
    fn certifies_i128_widened_sub_bv_carry_shape() {
        let sx = Formula::BvSignExt(Box::new(bvvar("__trust_ovf_bv_lhs__3", 64)), 64);
        let sy = Formula::BvSignExt(Box::new(bvvar("__trust_ovf_bv_rhs__4", 64)), 64);
        let diff = Formula::BvSub(Box::new(sx.clone()), Box::new(sy.clone()), 128);
        let viol = Formula::And(vec![
            // Type bounds on the (post-widen) operands, as the dump carries them
            // on the Int carriers — present but redundant with the sign-extension.
            Formula::Ge(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Int(i64::MIN as i128)),
            ),
            Formula::Le(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Int(i64::MAX as i128)),
            ),
            carry_overflow_or(diff, sx),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "i128 widened sub (±2^64 range) must kernel-certify with the widened Int reducer"
        );
    }

    /// Companion to the above: a NARROW (16→128) signed-extension sub, whose
    /// difference range `±(2^16-1)` is within the kernel-reducer reach, DOES
    /// certify — confirming the sign-extension recognition + subtraction path is
    /// correct and only the i128-wide result magnitude (not the sub shape) is the
    /// limiter. Operands are `i16` sign-extended to 128.
    #[test]
    fn certifies_narrow_widened_sub_bv_carry_shape() {
        // 16→128: BvSignExt adds 112 bits to a 16-bit source.
        let sx = Formula::BvSignExt(Box::new(bvvar("__trust_ovf_bv_lhs__3", 16)), 112);
        let sy = Formula::BvSignExt(Box::new(bvvar("__trust_ovf_bv_rhs__4", 16)), 112);
        let diff = Formula::BvSub(Box::new(sx.clone()), Box::new(sy.clone()), 128);
        let viol = Formula::And(vec![carry_overflow_or(diff, sx)]);
        assert!(
            certify_violation(&viol).is_some(),
            "narrow (16→128) widened sub must certify (within reducer reach)"
        );
    }

    /// `i128_shift_accumulator` per-add obligation: `t ∈ [0,65280]`, `_9 ∈ [0,4080]`
    /// in SIGNED BV (`BvSLe`), plus the carry-bit overflow disjunction over
    /// `BvAdd(t,_9,128)`. Sum ≤ 69360 ⊂ i128 ⇒ no overflow ⇒ UNSAT. (The fixture's
    /// shift-amount obligation is certified by `certify_closed_constant_contradiction`
    /// already; this is the ADD obligation.)
    #[test]
    fn certifies_i128_shift_accumulator_add_bv_carry_shape() {
        let t = bvvar("__trust_ovf_bv_lhs_t", 128);
        let n = bvvar("__trust_ovf_bv_rhs__9", 128);
        let sum = Formula::BvAdd(Box::new(t.clone()), Box::new(n.clone()), 128);
        let viol = Formula::And(vec![
            bvsle(bv(0, 128), t.clone()),
            bvsle(t.clone(), bv(65280, 128)),
            bvsle(bv(0, 128), n.clone()),
            bvsle(n.clone(), bv(4080, 128)),
            carry_overflow_or(sum, t),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "i128 shift-accumulator add (signed-BV ≤ guard carry overflow shape) must certify"
        );
    }

    /// SOUNDNESS: an UNGUARDED wide-BV add (operands at the full 128-bit type
    /// range, no `BvSLt`/`BvSLe` narrowing, no sign-extension) CAN overflow, so
    /// the carry obligation is genuinely SAT — must fail closed.
    #[test]
    fn signed_bv_overflow_fails_closed_when_unguarded_add() {
        let a = bvvar("__trust_ovf_bv_lhs_a", 128);
        let b = bvvar("__trust_ovf_bv_rhs_b", 128);
        let sum = Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 128);
        // No guard, no sign-extension: only the implicit full type range.
        let viol = Formula::And(vec![carry_overflow_or(sum, a)]);
        assert!(
            certify_violation(&viol).is_none(),
            "unguarded wide-BV add (real overflow risk) must NOT certify"
        );
    }

    /// SOUNDNESS: a wide-BV add whose signed guards are TOO WEAK to rule out
    /// overflow (`a,b < 2^127` only on the low side, unbounded high) leaves the
    /// sum possibly outside i128 — must fail closed. Here we give a lower bound but
    /// NO upper bound, so the upper extreme is unpinned and the Int `Or` stays SAT.
    #[test]
    fn signed_bv_overflow_fails_closed_when_guard_one_sided() {
        let a = bvvar("__trust_ovf_bv_lhs_a", 128);
        let b = bvvar("__trust_ovf_bv_rhs_b", 128);
        let sum = Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 128);
        let viol = Formula::And(vec![
            // Only lower bounds — upper extreme of `a+b` is unbounded.
            bvsle(bv(0, 128), a.clone()),
            bvsle(bv(0, 128), b.clone()),
            carry_overflow_or(sum, a),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "one-sided signed-BV guard (unpinned upper extreme) must NOT certify"
        );
    }

    // -----------------------------------------------------------------------
    // Phase 6 group (d)/(c): masked-low-bits / left-shift BV value bridges
    // (`bv_mask_shift_rewrites`). The clean kernel re-checks the resulting
    // linear-Int refutation, so these can only certify a genuinely-UNSAT shape.
    // -----------------------------------------------------------------------

    /// The REAL `bitmask_index_guarded` violation shape (group d), as the router
    /// emits it (verified via `AY_CERT_DUMP`): `if i < 16 { s[i & 31] }` over
    /// `[i32; 16]` yields
    ///   `0 ≤ i ≤ u64::MAX ∧ i < 16 ∧ _4 ≤ 31 ∧
    ///    _4 = BvToInt(BvAnd(IntToBv(i,64), IntToBv(31,64), 64), 64, false) ∧
    ///    _4 ≥ 16`.
    /// The mask `31 = 2^5−1` and the guard `i < 16 < 32` prove `i & 31 = i`, so the
    /// bridge emits `_4 = i`; then `16 ≤ _4 = i < 16` is a closed transitive-chain
    /// contradiction the existing machinery refutes and the kernel re-checks.
    #[test]
    fn certifies_real_bitmask_index_guarded_shape() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let mask_term = Formula::BvToInt(
            Box::new(Formula::BvAnd(
                Box::new(Formula::IntToBv(Box::new(v("i")), 64)),
                Box::new(Formula::IntToBv(Box::new(i(31)), 64)),
                64,
            )),
            64,
            false,
        );
        let viol = Formula::And(vec![
            Formula::Ge(Box::new(v("i")), Box::new(i(0))),
            Formula::Le(Box::new(v("i")), Box::new(i(18446744073709551615))),
            Formula::Lt(Box::new(v("i")), Box::new(i(16))),
            Formula::Le(Box::new(v("_4")), Box::new(i(31))),
            Formula::Eq(Box::new(v("_4")), Box::new(mask_term)),
            Formula::Ge(Box::new(v("_4")), Box::new(i(16))),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "guarded masked index (i & 31 under i < 16) must certify via the mask bridge"
        );
    }

    /// SOUNDNESS (group d, fail-closed): the SAME masked-index shape WITHOUT the
    /// dominating guard `i < 16`. Then `i & 31` is NOT the identity (e.g. `i = 47`
    /// gives `47 & 31 = 15`, and `i = 16` gives `16`, but `i = 48` gives `16` while
    /// `i ≥ 16` is satisfiable) — the OOB obligation is genuinely SAT (a real free
    /// index `i ≥ 16` with `i & 31 ≥ 16`), so the bridge must NOT fire and the
    /// obligation must NOT certify.
    #[test]
    fn bitmask_index_fails_closed_without_guard() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let mask_term = Formula::BvToInt(
            Box::new(Formula::BvAnd(
                Box::new(Formula::IntToBv(Box::new(v("i")), 64)),
                Box::new(Formula::IntToBv(Box::new(i(31)), 64)),
                64,
            )),
            64,
            false,
        );
        let viol = Formula::And(vec![
            // usize non-negativity + full type bound only — NO `i < 16` guard.
            Formula::Ge(Box::new(v("i")), Box::new(i(0))),
            Formula::Le(Box::new(v("i")), Box::new(i(18446744073709551615))),
            Formula::Eq(Box::new(v("_4")), Box::new(mask_term)),
            Formula::Ge(Box::new(v("_4")), Box::new(i(16))),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "unguarded masked index (real OOB risk) must NOT certify"
        );
    }

    /// The shift-VALUE sub-obligation of `shift_reduction` (group c): `_9 = x << 4`
    /// over `x ≤ 255` (`x as u16`), width 16. The bound `255·16 = 4080 < 65536 =
    /// 2^16` proves no wrap, so the bridge emits `_9 = x·16`; combined with `0 ≤ x`
    /// the overflow disjunction `Or([_9 < 0, _9 > 4080])` is refuted (`x·16 ∈
    /// [0,4080]`) by the existing additive/multiplicative-lift disjunctive path.
    /// (This is the shift-value half; the loop-accumulation overflow obligation
    /// `Or([t+_9<0, t+_9>65535])` is a SEPARATE loop-invariant category, not here.)
    #[test]
    fn certifies_shift_reduction_shift_value_shape() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let shl_term = Formula::BvToInt(
            Box::new(Formula::BvShl(
                Box::new(Formula::IntToBv(Box::new(v("_10")), 16)),
                Box::new(Formula::IntToBv(Box::new(i(4)), 16)),
                16,
            )),
            16,
            false,
        );
        let viol = Formula::And(vec![
            Formula::Le(Box::new(i(0)), Box::new(v("_10"))),
            Formula::Le(Box::new(v("_10")), Box::new(i(255))),
            Formula::Le(Box::new(i(0)), Box::new(v("_9"))),
            Formula::Le(Box::new(v("_9")), Box::new(i(65535))),
            Formula::Eq(Box::new(v("_9")), Box::new(shl_term)),
            // The shift-value range obligation: `_9` must lie in `[0, 4080]`.
            Formula::Or(vec![
                Formula::Lt(Box::new(v("_9")), Box::new(i(0))),
                Formula::Gt(Box::new(v("_9")), Box::new(i(4080))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "no-wrap shift value (x << 4, x ≤ 255, w = 16) must certify via the shift bridge"
        );
    }

    /// SOUNDNESS (group c, fail-closed): the SAME shift shape WITHOUT a no-wrap
    /// bound on `x` (only the loose 16-bit type range `x ≤ 65535`). Then
    /// `x · 2^4` can exceed `2^16` and the BV shift WRAPS, so `_9 = x·16` is NOT a
    /// valid identity and the `_9 > 4080` overflow disjunct is genuinely reachable
    /// — the bridge must NOT fire and the obligation must NOT certify.
    #[test]
    fn shift_value_fails_closed_without_nowrap_bound() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let shl_term = Formula::BvToInt(
            Box::new(Formula::BvShl(
                Box::new(Formula::IntToBv(Box::new(v("_10")), 16)),
                Box::new(Formula::IntToBv(Box::new(i(4)), 16)),
                16,
            )),
            16,
            false,
        );
        let viol = Formula::And(vec![
            // Only the loose 16-bit range: 65535·16 = 1048560 ≥ 2^16 ⟹ wrap possible.
            Formula::Le(Box::new(i(0)), Box::new(v("_10"))),
            Formula::Le(Box::new(v("_10")), Box::new(i(65535))),
            Formula::Le(Box::new(i(0)), Box::new(v("_9"))),
            Formula::Le(Box::new(v("_9")), Box::new(i(65535))),
            Formula::Eq(Box::new(v("_9")), Box::new(shl_term)),
            Formula::Or(vec![
                Formula::Lt(Box::new(v("_9")), Box::new(i(0))),
                Formula::Gt(Box::new(v("_9")), Box::new(i(4080))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "shift value with no no-wrap bound (wrap possible) must NOT certify"
        );
    }

    // -----------------------------------------------------------------------
    // Loop-accumulation no-overflow direct discharge
    // (`certify_accumulator_no_overflow`).
    // -----------------------------------------------------------------------

    /// The MINIMAL loop-accumulation no-overflow core the direct discharge keys
    /// on: `Or([t+x < 0, t+x > MAX])` with the present tight bound `t+x ≤ bound`
    /// (`bound ≤ MAX`) and the summand non-negativities `0 ≤ t`, `0 ≤ x`. This is
    /// exactly the shape `wide_unsigned_accumulator::u64_acc` reaches (here
    /// `bound = 16320`, `MAX = u64::MAX`), and which the generic disjunctive path
    /// also closes — the direct discharge must accept it too.
    #[test]
    fn certifies_accumulator_no_overflow_core_shape() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = || Formula::Add(Box::new(v("t")), Box::new(v("x")));
        let viol = Formula::And(vec![
            Formula::Le(Box::new(i(0)), Box::new(v("t"))),
            Formula::Le(Box::new(i(0)), Box::new(v("x"))),
            Formula::Le(Box::new(add()), Box::new(i(16320))),
            Formula::Or(vec![
                Formula::Lt(Box::new(add()), Box::new(i(0))),
                // u64::MAX (fits i128).
                Formula::Gt(Box::new(add()), Box::new(i(18446744073709551615))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "minimal loop-accumulation no-overflow core must kernel-certify"
        );
        assert_formula_certificate_pairs(&viol);
    }

    /// The REAL `shift_reduction` loop-accumulation overflow obligation, modelled
    /// on the `AY_CERT_DUMP=1 trustc` dump: the overflow disjunction
    /// `Or([t+_9<0, t+_9>65535])` with the present tight bound `t+_9 ≤ 65280`
    /// (`≤ 65535 = u16::MAX`), the summand non-negativities, AND the MANY
    /// surrounding conjuncts (discriminant `Or`s, BV-shift atoms, duplicated
    /// bounds) that inflate the augmented edge set past the 48-edge cap. The
    /// direct two-edge discharge bypasses that cap.
    #[test]
    fn certifies_shift_reduction_loop_accumulation_shape() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let bv = |n: &str| Formula::Var(n.to_string(), Sort::Bool);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let or = Formula::Or;
        let add = || Formula::Add(Box::new(v("t#s0_0_s8_0")), Box::new(v("_9#s7_0")));
        // discriminant disjunctions repeated several times (as in the dump).
        let discr = || or(vec![eq(v("_7"), i(0)), eq(v("_7"), i(1))]);
        let viol = Formula::And(vec![
            // Surrounding type-range bounds (with duplicates), like the dump.
            le(i(0), v("_11#s5_3")),
            le(v("_11#s5_3"), i(4294967295)),
            le(i(0), v("x#s5_1")),
            le(v("x#s5_1"), i(255)),
            le(i(0), v("_10#s5_2")),
            le(v("_10#s5_2"), i(65535)),
            le(i(-9223372036854775808), v("_7")),
            le(v("_7"), i(9223372036854775807)),
            Formula::Bool(true),
            eq(v("_7"), i(1)),
            bv("_12#s5_4"),
            discr(),
            discr(),
            discr(),
            or(vec![eq(v("discr__5"), i(0)), eq(v("discr__5"), i(1))]),
            // shift-value BV round-trip equality (un-modeled; dropped by the
            // supported-atom collector but still inflates the conjunct set).
            eq(
                v("_9#s7_0"),
                Formula::BvToInt(
                    Box::new(Formula::BvShl(
                        Box::new(Formula::IntToBv(Box::new(v("_10#s5_2")), 16)),
                        Box::new(Formula::IntToBv(Box::new(i(4)), 16)),
                        16,
                    )),
                    16,
                    false,
                ),
            ),
            le(v("_9#s7_0"), i(4080)),
            // The three present facts the discharge keys on.
            le(i(0), v("t#s0_0_s8_0")),
            le(v("t#s0_0_s8_0"), i(65535)),
            le(i(0), v("_9#s7_0")),
            le(v("_9#s7_0"), i(65535)),
            le(add(), i(65280)), // tight bound (≤ MAX).
            // The overflow obligation.
            or(vec![lt(add(), i(0)), gt(add(), i(65535))]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "real shift_reduction loop-accumulation overflow must kernel-certify"
        );
    }

    /// The REAL `nest2d_grid_reduction` loop-accumulation overflow obligation
    /// (`Or([t+_17<0, t+_17>65535])` with tight bound `t+_17 ≤ 4080`), again with
    /// the nested-loop discriminant `Or`s / index-range atoms that overflow the
    /// edge cap. Direct discharge.
    #[test]
    fn certifies_nest2d_grid_reduction_loop_accumulation_shape() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let or = Formula::Or;
        let add = || Formula::Add(Box::new(v("t#s0_0_s13_0")), Box::new(v("_17#s12_1")));
        let viol = Formula::And(vec![
            le(i(0), v("_17#s12_1")),
            le(v("_17#s12_1"), i(255)),
            le(i(0), v("_18#s12_0")),
            le(v("_18#s12_0"), i(255)),
            le(i(0), v("i#s5_0")),
            le(v("i#s5_0"), i(18446744073709551615)),
            le(i(0), v("j#s10_0")),
            le(v("j#s10_0"), i(18446744073709551615)),
            eq(v("_8"), i(1)),
            eq(v("_15"), i(1)),
            or(vec![eq(v("_8"), i(0)), eq(v("_8"), i(1))]),
            or(vec![eq(v("_15"), i(0)), eq(v("_15"), i(1))]),
            or(vec![eq(v("discr__6"), i(0)), eq(v("discr__6"), i(1))]),
            or(vec![eq(v("discr__13"), i(0)), eq(v("discr__13"), i(1))]),
            // nested-loop index range atoms.
            ge(v("i#s5_0"), i(0)),
            lt(v("i#s5_0"), i(4)),
            ge(v("j#s10_0"), i(0)),
            lt(v("j#s10_0"), i(4)),
            eq(v("_18#s12_0"), v("a*[_9][_16]")),
            eq(v("_17#s12_1"), v("_18#s12_0")),
            // The three present facts.
            le(i(0), v("t#s0_0_s13_0")),
            le(v("t#s0_0_s13_0"), i(65535)),
            le(i(0), v("_17#s12_1")),
            le(v("_17#s12_1"), i(65535)),
            le(add(), i(4080)),
            or(vec![lt(add(), i(0)), gt(add(), i(65535))]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "real nest2d_grid_reduction loop-accumulation overflow must kernel-certify"
        );
    }

    /// The `wide_unsigned_accumulator::u128_shift` loop-accumulation overflow,
    /// whose threshold is `UInt(u128::MAX)` — EXCEEDING `i128::MAX`. The direct
    /// discharge handles the wide-`UInt` MAX via the `u128`-encoded `Int.ofNat`
    /// witness; the generic `ChainAtom` literal renderer (capped at `u64::MAX`)
    /// cannot, which is one reason u128_shift declines via the existing path.
    /// Bound `t+_9 ≤ 65280 < u128::MAX`.
    #[test]
    fn certifies_wide_unsigned_u128_shift_uint_threshold_shape() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let u = Formula::UInt;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let add = || Formula::Add(Box::new(v("t#s0_0_s8_0")), Box::new(v("_9#s7_0")));
        let viol = Formula::And(vec![
            // Wide-UInt type bounds (u128::MAX).
            le(i(0), v("t#s0_0_s8_0")),
            le(v("t#s0_0_s8_0"), u(u128::MAX)),
            le(i(0), v("_9#s7_0")),
            le(v("_9#s7_0"), u(u128::MAX)),
            le(v("_9#s7_0"), i(4080)),
            le(add(), i(65280)), // tight bound (≤ u128::MAX).
            // Overflow obligation with a `UInt(u128::MAX)` threshold.
            Formula::Or(vec![lt(add(), i(0)), gt(add(), u(u128::MAX))]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "wide-unsigned u128 accumulator (UInt(u128::MAX) threshold) must kernel-certify"
        );
    }

    /// FAIL-CLOSED: the overflow `Or` and the summand non-negativities are present
    /// but the tight bound `Le(t+x, bound)` is ABSENT — so `t+x > MAX` is genuinely
    /// reachable (an UNBOUNDED accumulator really can overflow). The discharge must
    /// NOT synthesize a bound and must decline.
    #[test]
    fn accumulator_no_overflow_fails_closed_without_present_bound() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = || Formula::Add(Box::new(v("t")), Box::new(v("x")));
        let viol = Formula::And(vec![
            Formula::Le(Box::new(i(0)), Box::new(v("t"))),
            Formula::Le(Box::new(i(0)), Box::new(v("x"))),
            // NO `Le(t+x, bound)` present.
            Formula::Or(vec![
                Formula::Lt(Box::new(add()), Box::new(i(0))),
                Formula::Gt(Box::new(add()), Box::new(i(65535))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "unbounded accumulator (no present sum bound) must NOT certify"
        );
    }

    /// Regression guard for the `trust-ny-bridge` non-strict-bound case.
    /// Reconstruction of this contradiction passes through the Prop-valued
    /// `Int.NonNeg.casesOn` recursor, which has no universe parameters.  The
    /// resulting CleanCIC payload must independently re-check to `False`.
    #[test]
    fn certifies_two_non_strict_le_bound_contradiction() {
        let x = || Formula::Var("x".to_string(), Sort::Int);
        let violation = Formula::And(vec![
            Formula::Le(Box::new(x()), Box::new(Formula::Int(1))),
            Formula::Ge(Box::new(x()), Box::new(Formula::Int(2))),
        ]);
        let evidence =
            certify_violation(&violation).expect("two non-strict bounds with a gap must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut variables = BTreeSet::new();
        variables.insert("x".to_string());
        assert!(
            payload_roundtrip_rechecks(&variables, &term, &context),
            "two-non-strict-bound CleanCic payload must re-check through the clean kernel"
        );
    }

    /// FAIL-CLOSED: the present sum bound EXCEEDS the overflow threshold
    /// (`Le(t+x, 70000)` vs `MAX = 65535`), so `t+x > MAX` is reachable within the
    /// bound — the obligation is genuinely satisfiable and must decline.
    #[test]
    fn accumulator_no_overflow_fails_closed_when_bound_exceeds_max() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = || Formula::Add(Box::new(v("t")), Box::new(v("x")));
        let viol = Formula::And(vec![
            Formula::Le(Box::new(i(0)), Box::new(v("t"))),
            Formula::Le(Box::new(i(0)), Box::new(v("x"))),
            Formula::Le(Box::new(add()), Box::new(i(70000))), // bound > MAX.
            Formula::Or(vec![
                Formula::Lt(Box::new(add()), Box::new(i(0))),
                Formula::Gt(Box::new(add()), Box::new(i(65535))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "accumulator whose present bound exceeds MAX must NOT certify"
        );
    }

    /// FAIL-CLOSED: a summand non-negativity is MISSING (`0 ≤ x` absent), so
    /// `t+x < 0` (underflow) is reachable — the lower disjunct cannot be refuted
    /// and the discharge declines.
    #[test]
    fn accumulator_no_overflow_fails_closed_without_summand_nonneg() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = || Formula::Add(Box::new(v("t")), Box::new(v("x")));
        let viol = Formula::And(vec![
            Formula::Le(Box::new(i(0)), Box::new(v("t"))),
            // NO `0 ≤ x`.
            Formula::Le(Box::new(add()), Box::new(i(16320))),
            Formula::Or(vec![
                Formula::Lt(Box::new(add()), Box::new(i(0))),
                Formula::Gt(Box::new(add()), Box::new(i(65535))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "accumulator missing a summand non-negativity must NOT certify"
        );
    }

    /// Mut-borrow field identity (`assert_mut_field_identity`): the FAITHFUL dumped
    /// shape has the disequality NESTED in `And([Not(Eq(..)), Bool(true)])` (the
    /// `if true {..}` branch guard). After `collect_conjuncts` flattens it, a bare
    /// `Bool(true)` conjunct sits alongside the transitive-equality chain. The
    /// `Bool(true)` must be dropped so `certify_direct_disequality_contradiction`'s
    /// strict per-conjunct path does not fail closed on it.
    #[test]
    fn certifies_mut_field_identity_with_nested_true_guard() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let viol = Formula::And(vec![
            eq(v("_4#s0_1"), v("a.0#s0_0")),
            eq(v("a.0#s0_0"), v("v")),
            Formula::And(vec![
                Formula::Not(Box::new(eq(v("_4#s0_1"), v("v")))),
                Formula::Bool(true),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "transitive mut-borrow identity (with nested Bool(true) guard) must kernel-certify"
        );
        assert_formula_certificate_pairs(&viol);
    }

    /// Enum-discriminant nonneg-widening cast (`enumdf_i8_nonneg`): the FAITHFUL
    /// dumped shape carries the membership disjunction `_4 ∈ {0,1,2}`, the cast guard
    /// `Implies(Ge(_4,0), Eq(_3,_4))`, and the negated goal `Ge(_3,3)`. The
    /// membership bound entails `_4 ≥ 0`, discharging the implication to `_3 = _4`;
    /// with `_4 ≤ 2` propagated across the class, `_3 ≤ 2` contradicts `_3 ≥ 3`.
    #[test]
    fn certifies_enum_discriminant_nonneg_widening_cast() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let member = || Formula::Or(vec![eq(v("_4"), i(0)), eq(v("_4"), i(1)), eq(v("_4"), i(2))]);
        let viol = Formula::And(vec![
            member(),
            Formula::And(vec![
                member(),
                Formula::Or(vec![
                    eq(v("discr_e"), i(0)),
                    eq(v("discr_e"), i(1)),
                    eq(v("discr_e"), i(2)),
                ]),
                Formula::And(vec![
                    // Nonneg-widening cast guard: `_4 ≥ 0 → _3 = _4`.
                    Formula::Implies(Box::new(ge(v("_4"), i(0))), Box::new(eq(v("_3"), v("_4")))),
                    // Reified bool (dropped by retain): `_5 ⟺ _3 < 3`.
                    eq(v("_5#s0_3"), Formula::Lt(Box::new(v("_3")), Box::new(i(3)))),
                    // Negated goal: the OOB path requires `_3 ≥ 3`.
                    ge(v("_3"), i(3)),
                ]),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "enum-discriminant nonneg-widening cast must kernel-certify"
        );
    }

    /// Signed two-sided accumulator (`signed_accumulator::sum_i8`): the i32 add
    /// overflow `Or([Lt(s+x,i32::MIN), Gt(s+x,i32::MAX)])` with the loop-invariant
    /// window `Ge(s+x,-1024)`, `Le(s+x,1016)` present. Both disjuncts refute against
    /// a present sum bound (`-1024 ≥ i32::MIN`, `1016 ≤ i32::MAX`).
    #[test]
    fn certifies_signed_two_sided_accumulator_i8_to_i32() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = || Formula::Add(Box::new(v("s")), Box::new(v("x")));
        let viol = Formula::And(vec![
            Formula::Ge(Box::new(add()), Box::new(i(-1024))),
            Formula::Le(Box::new(add()), Box::new(i(1016))),
            Formula::Or(vec![
                Formula::Lt(Box::new(add()), Box::new(i(-2147483648))),
                Formula::Gt(Box::new(add()), Box::new(i(2147483647))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "signed i8→i32 accumulator (two-sided window inside i32) must kernel-certify"
        );
        assert_formula_certificate_pairs(&viol);
    }

    /// Signed two-sided accumulator (`sum_i16`): i64 thresholds (full `i64::MIN`/MAX).
    #[test]
    fn certifies_signed_two_sided_accumulator_i16_to_i64() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = || Formula::Add(Box::new(v("s")), Box::new(v("x")));
        let viol = Formula::And(vec![
            Formula::Ge(Box::new(add()), Box::new(i(-1048576))),
            Formula::Le(Box::new(add()), Box::new(i(1048544))),
            Formula::Or(vec![
                Formula::Lt(Box::new(add()), Box::new(i(-9223372036854775808))),
                Formula::Gt(Box::new(add()), Box::new(i(9223372036854775807))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "signed i16→i64 accumulator (two-sided window inside i64) must kernel-certify"
        );
    }

    /// FAIL-CLOSED: the present upper sum bound EXCEEDS i32::MAX (`Le(s+x, 3e9)`),
    /// so `s+x > i32::MAX` is reachable within the window — genuinely satisfiable,
    /// must decline.
    #[test]
    fn signed_two_sided_accumulator_fails_closed_when_window_exceeds_max() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = || Formula::Add(Box::new(v("s")), Box::new(v("x")));
        let viol = Formula::And(vec![
            Formula::Ge(Box::new(add()), Box::new(i(-1024))),
            Formula::Le(Box::new(add()), Box::new(i(3000000000))), // > i32::MAX.
            Formula::Or(vec![
                Formula::Lt(Box::new(add()), Box::new(i(-2147483648))),
                Formula::Gt(Box::new(add()), Box::new(i(2147483647))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "two-sided accumulator whose window exceeds i32::MAX must NOT certify"
        );
    }

    /// FAIL-CLOSED: only the UPPER sum bound is present (no `Ge(s+x, lo)`), so the
    /// underflow disjunct `s+x < MIN` cannot be refuted and the discharge declines.
    #[test]
    fn signed_two_sided_accumulator_fails_closed_without_lower_bound() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = || Formula::Add(Box::new(v("s")), Box::new(v("x")));
        let viol = Formula::And(vec![
            // NO `Ge(s+x, lo)`.
            Formula::Le(Box::new(add()), Box::new(i(1016))),
            Formula::Or(vec![
                Formula::Lt(Box::new(add()), Box::new(i(-2147483648))),
                Formula::Gt(Box::new(add()), Box::new(i(2147483647))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "two-sided accumulator missing the lower sum bound must NOT certify"
        );
    }

    /// cell_grid_stride else-branch (`4096 * 64`): the closed-constant overflow
    /// check `Or([Lt(Mul(4096,64),0), Gt(Mul(4096,64),u32::MAX)])`. Constant-folding
    /// `Mul(4096,64) → 262144` reduces it to the variable-free order-atom disjunction
    /// the closed-constant refutation discharges (`262144 < 0` false, `262144 > MAX`
    /// false).
    /// Hub-connected overflow (the grid_flattened OBL3 hazard generalized): the
    /// add-overflow's operands are transitively equality-linked to a long chain of
    /// unrelated bounded temps, so connected-component pruning keeps everything and
    /// still blows the 48-edge cap. The 1-hop (direct-operand-var) pruning keeps only
    /// the operands' own bounds and closes.
    #[test]
    fn certifies_overflow_with_hub_connected_context_via_one_hop_pruning() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let add = || Formula::Add(Box::new(v("a")), Box::new(v("b")));
        let mut cs = vec![
            le(i(0), v("a")),
            le(v("a"), i(8)),
            le(i(0), v("b")),
            Formula::Lt(Box::new(v("b")), Box::new(i(4))),
            // a is equality-linked to h0, which chains to many unrelated bounded temps.
            eq(v("a"), v("h0")),
        ];
        for k in 0..60 {
            cs.push(eq(v(&format!("h{k}")), v(&format!("h{}", k + 1))));
            cs.push(le(i(0), v(&format!("h{k}"))));
            cs.push(le(v(&format!("h{k}")), i(1_000_000)));
        }
        cs.push(Formula::Or(vec![
            Formula::Lt(Box::new(add()), Box::new(i(0))),
            Formula::Gt(Box::new(add()), Box::new(i(18446744073709551615))),
        ]));
        let viol = Formula::And(cs);
        assert!(
            certify_violation(&viol).is_some(),
            "hub-connected overflow must certify via 1-hop (direct-operand) pruning"
        );
    }

    #[test]
    fn certifies_const_mul_overflow_closed() {
        let i = Formula::Int;
        let mul = || Formula::Mul(Box::new(i(4096)), Box::new(i(64)));
        let viol = Formula::And(vec![Formula::Or(vec![
            Formula::Lt(Box::new(mul()), Box::new(i(0))),
            Formula::Gt(Box::new(mul()), Box::new(i(4294967295))),
        ])]);
        assert!(
            certify_violation(&viol).is_some(),
            "const*const overflow check (folds to 262144) must kernel-certify"
        );
    }

    /// cell_grid_stride guarded branch (`cols * 64` under `cols ≤ 4096`): the
    /// var*const overflow check refutes via the existing multiplicative lift
    /// (`cols ≤ 4096 ⟹ cols*64 ≤ 262144 < u32::MAX`; `0 ≤ cols ⟹ 0 ≤ cols*64`).
    #[test]
    fn certifies_var_const_mul_overflow_guarded() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let mul = || Formula::Mul(Box::new(v("cols")), Box::new(i(64)));
        let viol = Formula::And(vec![
            Formula::Le(Box::new(i(0)), Box::new(v("cols"))),
            Formula::Le(Box::new(v("cols")), Box::new(i(4294967295))),
            Formula::Le(Box::new(v("cols")), Box::new(i(4096))),
            Formula::Or(vec![
                Formula::Lt(Box::new(mul()), Box::new(i(0))),
                Formula::Gt(Box::new(mul()), Box::new(i(4294967295))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "guarded var*const overflow (cols≤4096) must kernel-certify"
        );
    }

    /// Guarded-division div-by-zero (`waveform_scale_div`): the failure VC is a path
    /// disjunction `Or([pathA, pathB])` where EVERY path conjoins both the guard
    /// `Not(Eq(d,0))` and the divide-by-zero failure `Eq(d,0)` (nested under reified
    /// bools). Common-conjunct extraction surfaces both → direct disequality.
    #[test]
    fn certifies_guarded_div_common_conjunct_disequality() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let vb = |n: &str| Formula::Var(n.to_string(), Sort::Bool);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let not = |a: Formula| Formula::Not(Box::new(a));
        // Each path: guard d!=0, some path-specific atoms, reif defs, and the
        // failure Eq(d,0) nested in an inner And — mirroring the real lowering.
        let path = |extra: Formula| {
            Formula::And(vec![
                not(eq(v("d"), i(0))),
                extra,
                not(vb("_6")),
                Formula::And(vec![eq(vb("_6"), eq(v("d"), i(0))), eq(v("d"), i(0))]),
            ])
        };
        let viol = Formula::And(vec![
            Formula::Ge(Box::new(v("d")), Box::new(i(-2147483648))),
            Formula::Le(Box::new(v("d")), Box::new(i(2147483647))),
            Formula::And(vec![
                Formula::Bool(true),
                Formula::Or(vec![
                    path(not(eq(v("n"), i(-2147483648)))),
                    path(eq(v("n"), i(-2147483648))),
                ]),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "guarded-div failure (every path carries d!=0 and d=0) must kernel-certify"
        );
    }

    /// grid_flattened_index mul-overflow (`y*4` under `for y in 0..3`): the bound is
    /// STRICT `Lt(y,3)`, so the multiplicative lift (non-strict only) never fired.
    /// Tightening to `Le(y,2)` lets `y*4 ≤ 8 < usize::MAX` discharge (and `0≤y ⟹ 0≤y*4`).
    #[test]
    fn certifies_strict_bounded_var_const_mul_overflow() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let mul = || Formula::Mul(Box::new(v("y")), Box::new(i(4)));
        let viol = Formula::And(vec![
            Formula::Le(Box::new(i(0)), Box::new(v("y"))),
            Formula::Lt(Box::new(v("y")), Box::new(i(3))), // STRICT bound y<3.
            Formula::Or(vec![
                Formula::Lt(Box::new(mul()), Box::new(i(0))),
                Formula::Gt(Box::new(mul()), Box::new(i(18446744073709551615))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "strict-bounded var*const overflow (y<3 ⟹ y*4≤8) must kernel-certify"
        );
    }

    /// grid_flattened_index add-overflow (`_21 + x`, `_21≤8`, `x<4`): the strict
    /// `Lt(x,4)` tightens to `Le(x,3)`, then the additive lift gives `_21+x ≤ 11 <
    /// usize::MAX` (and `0≤_21, 0≤x ⟹ 0≤_21+x`).
    #[test]
    fn certifies_strict_bounded_two_var_add_overflow() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = || Formula::Add(Box::new(v("a")), Box::new(v("x")));
        let viol = Formula::And(vec![
            Formula::Le(Box::new(i(0)), Box::new(v("a"))),
            Formula::Le(Box::new(v("a")), Box::new(i(8))),
            Formula::Le(Box::new(i(0)), Box::new(v("x"))),
            Formula::Lt(Box::new(v("x")), Box::new(i(4))), // STRICT bound x<4.
            Formula::Or(vec![
                Formula::Lt(Box::new(add()), Box::new(i(0))),
                Formula::Gt(Box::new(add()), Box::new(i(18446744073709551615))),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "strict-bounded two-var add overflow (x<4 ⟹ a+x≤11) must kernel-certify"
        );
    }

    /// Relevance pruning (grid_flattened_index): the add-overflow `Or([Lt(a+b,0),
    /// Gt(a+b,usize::MAX)])` with its relevant window (`a≤8`, `b<4`, nonnegs) is
    /// SWAMPED by many unrelated bound conjuncts (loop-var/discriminant temps), whose
    /// augmented edge set blows the 48-edge cap so the full-context attempt fails. The
    /// relevance-pruned fallback keeps only the `{a,b}`-connected conjuncts and closes.
    #[test]
    fn certifies_overflow_under_large_unrelated_context_via_pruning() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let add = || Formula::Add(Box::new(v("a")), Box::new(v("b")));
        let mut cs = vec![
            Formula::Le(Box::new(i(0)), Box::new(v("a"))),
            Formula::Le(Box::new(v("a")), Box::new(i(8))),
            Formula::Le(Box::new(i(0)), Box::new(v("b"))),
            Formula::Lt(Box::new(v("b")), Box::new(i(4))),
            Formula::Or(vec![
                Formula::Lt(Box::new(add()), Box::new(i(0))),
                Formula::Gt(Box::new(add()), Box::new(i(18446744073709551615))),
            ]),
        ];
        // Swamp with unrelated bounds on distinct temps to blow the 48-edge cap.
        for k in 0..60 {
            let u = format!("u_{k}");
            cs.push(Formula::Le(Box::new(i(0)), Box::new(v(&u))));
            cs.push(Formula::Le(Box::new(v(&u)), Box::new(i(100))));
        }
        let viol = Formula::And(cs);
        assert!(
            certify_violation(&viol).is_some(),
            "add-overflow swamped by unrelated context must certify via relevance pruning"
        );
    }

    /// FAIL-CLOSED: the failure `Eq(d,0)` appears in only ONE disjunct, so it is NOT
    /// entailed by the `Or` and no common-conjunct contradiction is surfaced.
    #[test]
    fn common_conjunct_extraction_fails_closed_when_not_in_all_disjuncts() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let not = |a: Formula| Formula::Not(Box::new(a));
        let viol = Formula::And(vec![Formula::Or(vec![
            // only THIS disjunct has the contradiction; the other does not.
            Formula::And(vec![not(eq(v("d"), i(0))), eq(v("d"), i(0))]),
            Formula::And(vec![not(eq(v("d"), i(0)))]),
        ])]);
        assert!(
            certify_violation(&viol).is_none(),
            "a contradiction in only one disjunct must NOT certify the disjunction"
        );
    }

    /// FAIL-CLOSED: the implication's antecedent is NOT entailed (no membership
    /// bound forces `_4 ≥ 0`), so the cast equality `_3 = _4` must NOT be assumed
    /// and the obligation declines.
    #[test]
    fn implication_discharge_fails_closed_without_entailed_antecedent() {
        let v = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let i = Formula::Int;
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let viol = Formula::And(vec![
            // NO membership / lower bound on `_4` → antecedent `_4 ≥ 0` unprovable.
            Formula::Implies(Box::new(ge(v("_4"), i(0))), Box::new(eq(v("_3"), v("_4")))),
            ge(v("_3"), i(3)),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "implication with un-entailed antecedent must NOT discharge / certify"
        );
    }

    // Trust (mask-to-type-max completeness) test helpers.
    fn m_var(n: &str) -> Formula {
        Formula::Var(n.to_string(), Sort::Int)
    }

    fn summand_overflow_violation(
        bounds: [Option<i128>; 2],
        nonnegative: [bool; 2],
        max: Formula,
        sums: [(&str, &str); 2],
        reverse_disjuncts: bool,
    ) -> Formula {
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let add = |(a, b): (&str, &str)| Formula::Add(Box::new(m_var(a)), Box::new(m_var(b)));
        let mut conjuncts = Vec::new();
        if nonnegative[0] {
            conjuncts.push(le(i(0), m_var("a")));
        }
        if let Some(bound) = bounds[0] {
            conjuncts.push(le(m_var("a"), i(bound)));
        }
        if nonnegative[1] {
            conjuncts.push(le(i(0), m_var("b")));
        }
        if let Some(bound) = bounds[1] {
            conjuncts.push(le(m_var("b"), i(bound)));
        }
        let lower = Formula::Lt(Box::new(add(sums[0])), Box::new(i(0)));
        let upper = Formula::Gt(Box::new(add(sums[1])), Box::new(max));
        let disjuncts = if reverse_disjuncts { vec![upper, lower] } else { vec![lower, upper] };
        conjuncts.push(Formula::Or(disjuncts));
        Formula::And(conjuncts)
    }

    fn summand_lane_certificate(violation: &Formula) -> Option<ProofEvidence> {
        let identity = ObligationIdentity::from_violation(violation)?;
        let normalized = normalize_violation(violation)?;
        certify_summand_bounded_accumulator_no_overflow(&normalized.view(), &identity)
    }

    fn m_masked(out: &str, val: Formula, mask: Formula, w: u32) -> Formula {
        // out = (val & mask) as unsigned, i.e. `Eq(out, BvToInt(BvAnd(IntToBv(val),
        // IntToBv(mask)), w, false))` — the exact shape vcgen lowers `val & mask` to.
        Formula::Eq(
            Box::new(m_var(out)),
            Box::new(Formula::BvToInt(
                Box::new(Formula::BvAnd(
                    Box::new(Formula::IntToBv(Box::new(val), w)),
                    Box::new(Formula::IntToBv(Box::new(mask), w)),
                    w,
                )),
                w,
                false,
            )),
        )
    }

    /// WIN: `(x & 0xFF) as u8` — a LITERAL type-max mask. The cast violation
    /// `out > 255` is UNSAT because `x & 255 ∈ [0, 255]` unconditionally (for ANY
    /// `x`, no bound on `x` needed). Certifies via the unconditional masked-value
    /// bound (group (e)).
    #[test]
    fn masked_cast_literal_mask_type_max_certifies() {
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let viol = Formula::And(vec![
            // x is an arbitrary u32 — NO bound tighter than the type range.
            ge(m_var("x"), i(0)),
            le(m_var("x"), i(4294967295)),
            m_masked("out", m_var("x"), i(255), 32),
            // cast-to-u8 violation: out < 0 ∨ out > 255.
            Formula::Or(vec![lt(m_var("out"), i(0)), gt(m_var("out"), i(255))]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "`(x & 0xFF) as u8` masked-cast bound must certify (out ∈ [0,255] unconditionally)"
        );
    }

    /// WIN: the `let m = (1u32 << 8) - 1; x & m` chain — the mask is a VARIABLE
    /// pinned to `255` through `m = _s − 1`, `_s = 1 << 8`. `mask_const_value`
    /// folds the chain and the unconditional bound certifies.
    #[test]
    fn masked_cast_chained_mask_type_max_certifies() {
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        // shifted = (1u32 << 8) = 256, lowered as BvToInt(BvShl(IntToBv(1), IntToBv(8))).
        let shifted = Formula::BvToInt(
            Box::new(Formula::BvShl(
                Box::new(Formula::IntToBv(Box::new(i(1)), 32)),
                Box::new(Formula::IntToBv(Box::new(i(8)), 32)),
                32,
            )),
            32,
            false,
        );
        let viol = Formula::And(vec![
            ge(m_var("x"), i(0)),
            le(m_var("x"), i(4294967295)),
            eq(m_var("_s"), shifted), // _s = 256
            eq(m_var("m"), Formula::Sub(Box::new(m_var("_s")), Box::new(i(1)))), // m = 255
            m_masked("out", m_var("x"), m_var("m"), 32),
            Formula::Or(vec![lt(m_var("out"), i(0)), gt(m_var("out"), i(255))]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "chained `let m=(1<<8)-1; (x & m) as u8` masked-cast bound must certify"
        );
    }

    /// WIN: the `(a/2)+(b/2)` midpoint as it reaches the kernel from the HARDENED
    /// panic-boundary lane (`mir_assert::Overflow(Add)`) — the violation
    /// `Or([_4+_6<0, _4+_6>u32::MAX])` with per-summand bounds `_4≤⌊u32::MAX/2⌋`,
    /// `_6≤⌊u32::MAX/2⌋` (from the division-range normalization) and `_4,_6≥0`,
    /// but NO direct bound on the sum. Certifies because
    /// `2147483647 + 2147483647 = 4294967294 < 4294967295 = u32::MAX`.
    #[test]
    fn summand_bounded_midpoint_no_overflow_certifies() {
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let half_max = 2147483647; // ⌊u32::MAX/2⌋
        let u32_max = 4294967295;
        let viol = Formula::And(vec![
            le(i(0), m_var("_4")),
            le(m_var("_4"), i(half_max)),
            le(i(0), m_var("_6")),
            le(m_var("_6"), i(half_max)),
            Formula::Or(vec![
                lt(add(m_var("_4"), m_var("_6")), i(0)),
                gt(add(m_var("_4"), m_var("_6")), i(u32_max)),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "`(a/2)+(b/2)` midpoint no-overflow must certify from per-summand bounds"
        );
    }

    /// SOUND / fail-closed: loose summand bounds whose SUM can overflow must NOT
    /// certify. `_4≤u32::MAX ∧ _6≤u32::MAX` permits `_4+_6 = 2·u32::MAX >
    /// u32::MAX`, so `_4+_6 > u32::MAX` is SATISFIABLE — no certificate.
    #[test]
    fn summand_bounded_sum_genuine_overflow_does_not_certify() {
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let u32_max = 4294967295;
        let viol = Formula::And(vec![
            le(i(0), m_var("_4")),
            le(m_var("_4"), i(u32_max)),
            le(i(0), m_var("_6")),
            le(m_var("_6"), i(u32_max)),
            Formula::Or(vec![
                lt(add(m_var("_4"), m_var("_6")), i(0)),
                gt(add(m_var("_4"), m_var("_6")), i(u32_max)),
            ]),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "genuinely-overflowing summand bounds must NOT certify (2·u32::MAX > u32::MAX)"
        );
    }

    #[test]
    fn summand_bounded_exact_boundary_certifies_but_max_plus_one_rejects() {
        let exact = summand_overflow_violation(
            [Some(4), Some(5)],
            [true, true],
            Formula::Int(9),
            [("a", "b"), ("a", "b")],
            false,
        );
        assert!(certify_violation(&exact).is_some(), "A+B == MAX is safe and must kernel-certify");

        let too_large = summand_overflow_violation(
            [Some(5), Some(5)],
            [true, true],
            Formula::Int(9),
            [("a", "b"), ("a", "b")],
            false,
        );
        assert!(
            certify_violation(&too_large).is_none(),
            "A+B == MAX+1 permits a real overflow and must fail closed"
        );
    }

    #[test]
    fn summand_bounded_missing_each_required_fact_fails_closed() {
        let cases = [
            ("a upper bound", [None, Some(5)], [true, true]),
            ("b upper bound", [Some(4), None], [true, true]),
            ("a non-negativity", [Some(4), Some(5)], [false, true]),
            ("b non-negativity", [Some(4), Some(5)], [true, false]),
        ];
        for (missing, bounds, nonnegative) in cases {
            let violation = summand_overflow_violation(
                bounds,
                nonnegative,
                Formula::Int(9),
                [("a", "b"), ("a", "b")],
                false,
            );
            assert!(
                certify_violation(&violation).is_none(),
                "missing {missing} must not mint a certificate"
            );
        }
    }

    #[test]
    fn summand_bounded_checked_add_overflow_fails_closed() {
        let violation = summand_overflow_violation(
            [Some(i128::MAX), Some(1)],
            [true, true],
            Formula::UInt(u128::MAX),
            [("a", "b"), ("a", "b")],
            false,
        );
        assert!(
            summand_lane_certificate(&violation).is_none(),
            "overflow while computing A+B in i128 must decline the specialized lane"
        );
    }

    #[test]
    fn summand_bounded_reversed_disjuncts_and_swapped_addends_certify() {
        let violation = summand_overflow_violation(
            [Some(4), Some(5)],
            [true, true],
            Formula::Int(9),
            [("b", "a"), ("a", "b")],
            true,
        );
        assert!(
            certify_violation(&violation).is_some(),
            "equivalent disjunct/addend orderings must preserve certification"
        );
    }

    #[test]
    fn summand_bounded_mismatched_lower_and_upper_sums_reject() {
        let violation = summand_overflow_violation(
            [Some(4), Some(5)],
            [true, true],
            Formula::Int(9),
            [("a", "b"), ("a", "c")],
            false,
        );
        assert!(
            certify_violation(&violation).is_none(),
            "overflow disjuncts over different sums must not be combined"
        );
    }

    #[test]
    fn summand_bounded_bypasses_more_than_48_irrelevant_edges() {
        let Formula::And(mut conjuncts) = summand_overflow_violation(
            [Some(4), Some(5)],
            [true, true],
            Formula::Int(9),
            [("a", "b"), ("a", "b")],
            false,
        ) else {
            unreachable!("helper always returns a conjunction");
        };
        for index in 0..64 {
            let noise = m_var(&format!("noise_{index}"));
            conjuncts.push(Formula::Le(Box::new(Formula::Int(0)), Box::new(noise.clone())));
            conjuncts.push(Formula::Le(Box::new(noise), Box::new(Formula::Int(1000))));
        }
        let violation = Formula::And(conjuncts);
        assert!(
            certify_violation(&violation).is_some(),
            "the summand-specific proof must ignore a context larger than the 48-edge DFS cap"
        );
    }

    /// The FULL `(a/2)+(b/2)` hardened panic-boundary violation as it reaches the
    /// kernel — transcribed from the real `AY_CERT_DUMP` (division defs `_4=a/2`,
    /// `_6=b/2`, reified div-by-zero bools `_3/_5`, a branch-phi
    /// `Or([_4+_6>MAX, _0=_4+_6])`, both loose (`≤u32::MAX`) and tight
    /// (`≤⌊u32::MAX/2⌋`) summand bounds, the temp `_0≤u32::MAX-1`, and the overflow
    /// `Or([_4+_6<0, _4+_6>u32::MAX])`). Must certify despite the SSA noise.
    #[test]
    fn full_hardened_midpoint_panic_boundary_certifies() {
        let i = Formula::Int;
        let v = m_var;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let div = |a: Formula, b: Formula| Formula::Div(Box::new(a), Box::new(b));
        let boolvar = |n: &str| Formula::Var(n.to_string(), Sort::Bool);
        let not = |f: Formula| Formula::Not(Box::new(f));
        let umax = 4294967295;
        let half = 2147483647;
        let sum = || add(v("_4"), v("_6"));
        let viol = Formula::And(vec![
            ge(v("a"), i(0)),
            le(v("a"), i(umax)),
            ge(v("b"), i(0)),
            le(v("b"), i(umax)),
            le(i(0), v("_4")),
            le(v("_4"), i(umax)), // loose bound
            le(i(0), v("_6")),
            le(v("_6"), i(umax)), // loose bound
            eq(boolvar("_3"), eq(i(2), i(0))),
            eq(v("_4"), div(v("a"), i(2))),
            eq(boolvar("_5"), eq(i(2), i(0))),
            not(boolvar("_3")),
            not(boolvar("_5")),
            // branch-phi disjunction (overflow flag OR the sum temp def).
            Formula::Or(vec![gt(sum(), i(umax)), eq(v("_0"), sum())]),
            le(v("_0"), i(4294967294)),
            le(v("_4"), i(half)), // tight division-range bound
            le(v("_6"), i(half)), // tight division-range bound
            eq(v("_6"), div(v("b"), i(2))),
            // the overflow violation disjunction.
            Formula::Or(vec![lt(sum(), i(0)), gt(sum(), i(umax))]),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "full hardened `(a/2)+(b/2)` panic-boundary violation must certify"
        );
    }

    /// WIN: the hardened `mir_assert::Overflow(Add)` violation for `(a/2)+(b/2)`
    /// in its ACTUAL De Morgan form `Not(And([Le(0, _4+_6), Le(_4+_6, u32::MAX)]))`
    /// (NOT the `Or([_4+_6<0, _4+_6>MAX])` form) with per-summand division-range
    /// bounds `_4,_6 ≤ ⌊u32::MAX/2⌋` and `_4,_6 ≥ 0`. Must certify.
    #[test]
    fn not_in_range_midpoint_no_overflow_certifies() {
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let not = |f: Formula| Formula::Not(Box::new(f));
        let half = 2147483647;
        let umax = 4294967295;
        let sum = || add(m_var("_4"), m_var("_6"));
        let viol = Formula::And(vec![
            le(i(0), m_var("_4")),
            le(m_var("_4"), i(half)),
            le(i(0), m_var("_6")),
            le(m_var("_6"), i(half)),
            not(Formula::And(vec![le(i(0), sum()), le(sum(), i(umax))])),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "hardened `Not(And([0≤a+b, a+b≤MAX]))` midpoint violation must certify"
        );
    }

    /// SOUND / fail-closed: loose summand bounds whose sum can leave `[0, MAX]`
    /// must NOT certify the `Not(And([0≤a+b, a+b≤MAX]))` form (2·u32::MAX > MAX).
    #[test]
    fn not_in_range_genuine_overflow_does_not_certify() {
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let not = |f: Formula| Formula::Not(Box::new(f));
        let umax = 4294967295;
        let sum = || add(m_var("_4"), m_var("_6"));
        let viol = Formula::And(vec![
            le(i(0), m_var("_4")),
            le(m_var("_4"), i(umax)),
            le(i(0), m_var("_6")),
            le(m_var("_6"), i(umax)),
            not(Formula::And(vec![le(i(0), sum()), le(sum(), i(umax))])),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "genuinely-overflowing summand bounds must NOT certify the Not(And) form"
        );
    }

    /// The FULL hardened `(a/2)+(b/2)` panic-boundary violation transcribed from
    /// the real `AY_CERT_DUMP` — the `Not(And([..]))` violation buried among the
    /// SSA branch-phi `Or([_4+_6>MAX, _0=_4+_6])`, the reified bool
    /// `_7.1 ⟺ (_4+_6<0 ∨ _4+_6>MAX)`, div defs `_4=a/2, _6=b/2`, and both loose
    /// (`≤MAX`) and tight (`≤⌊MAX/2⌋`) summand bounds. Must certify despite all of it.
    #[test]
    fn full_hardened_not_in_range_panic_boundary_certifies() {
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let add = |a: Formula, b: Formula| Formula::Add(Box::new(a), Box::new(b));
        let div = |a: Formula, b: Formula| Formula::Div(Box::new(a), Box::new(b));
        let not = |f: Formula| Formula::Not(Box::new(f));
        let bv = |n: &str| Formula::Var(n.to_string(), Sort::Bool);
        let umax = 4294967295;
        let half = 2147483647;
        let sum = || add(m_var("_4"), m_var("_6"));
        let viol = Formula::And(vec![
            ge(m_var("a"), i(0)),
            le(m_var("a"), i(umax)),
            ge(m_var("b"), i(0)),
            le(m_var("b"), i(umax)),
            le(i(0), m_var("a")),
            le(i(0), m_var("b")),
            not(bv("_3")),
            not(bv("_5")),
            // branch-phi disjunction from the checked-add lowering.
            Formula::Or(vec![gt(sum(), i(umax)), eq(m_var("_0"), sum())]),
            le(m_var("_0"), i(4294967294)),
            le(m_var("_4"), i(half)), // tight division-range bound
            le(m_var("_6"), i(half)),
            // reified overflow flag `_7.1 ⟺ (a+b<0 ∨ a+b>MAX)`.
            eq(m_var("_7.0"), sum()),
            eq(bv("_7.1"), Formula::Or(vec![lt(sum(), i(0)), gt(sum(), i(umax))])),
            le(i(0), m_var("_4")),
            le(m_var("_4"), i(umax)), // loose bound
            le(i(0), m_var("_6")),
            le(m_var("_6"), i(umax)),
            eq(m_var("_4"), div(m_var("a"), i(2))),
            eq(m_var("_6"), div(m_var("b"), i(2))),
            // the actual hardened De Morgan violation.
            not(Formula::And(vec![le(i(0), sum()), le(sum(), i(umax))])),
        ]);
        assert!(
            certify_violation(&viol).is_some(),
            "full hardened Not(And) `(a/2)+(b/2)` panic-boundary violation must certify"
        );
    }

    /// SOUND / fail-closed: a genuinely-OVERFLOWING masked cast must NOT certify.
    /// `(x & 0x1FF) as u8` yields `out ∈ [0, 511]`, so `out > 255` is SATISFIABLE
    /// (e.g. out = 256) — the unconditional bound is `out ≤ 511`, which does NOT
    /// contradict the violation. No certificate.
    #[test]
    fn masked_cast_mask_wider_than_target_does_not_certify() {
        let i = Formula::Int;
        let le = |a: Formula, b: Formula| Formula::Le(Box::new(a), Box::new(b));
        let ge = |a: Formula, b: Formula| Formula::Ge(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
        let lt = |a: Formula, b: Formula| Formula::Lt(Box::new(a), Box::new(b));
        let viol = Formula::And(vec![
            ge(m_var("x"), i(0)),
            le(m_var("x"), i(4294967295)),
            m_masked("out", m_var("x"), i(511), 32), // 0x1FF: window is [0,511]
            Formula::Or(vec![lt(m_var("out"), i(0)), gt(m_var("out"), i(255))]),
        ]);
        assert!(
            certify_violation(&viol).is_none(),
            "`(x & 0x1FF) as u8` genuinely overflows (out up to 511) — must NOT certify"
        );
    }

    /// SOUND / fail-closed: a NON-window mask (`0b1010` = 10, bits not contiguous
    /// from bit 0) is not a `2^k−1` window, so no bound is emitted and a violation
    /// over the masked value cannot be discharged from a spurious `out ≤ 10`.
    #[test]
    fn masked_value_non_window_mask_emits_no_bound() {
        let i = Formula::Int;
        let conj = Formula::And(vec![m_masked("out", m_var("x"), i(10), 32)]);
        let conjuncts: Vec<&Formula> = collect_and_view(&conj);
        let derived = bv_mask_shift_rewrites(&conjuncts);
        assert!(
            derived.is_empty(),
            "a non-window mask (0b1010) must emit no masked-value bound, got {derived:?}"
        );
    }

    /// The unconditional masked-value bound is emitted for a valid window mask and
    /// carries BOTH `out ≥ 0` and `out ≤ mask`.
    #[test]
    fn masked_value_window_mask_emits_both_bounds() {
        let i = Formula::Int;
        let conj = Formula::And(vec![m_masked("out", m_var("x"), i(255), 32)]);
        let conjuncts: Vec<&Formula> = collect_and_view(&conj);
        let derived = bv_mask_shift_rewrites(&conjuncts);
        let has_lb = derived.iter().any(|f| {
            matches!(f, Formula::Ge(a, b)
                if matches!(a.as_ref(), Formula::Var(n, Sort::Int) if n == "out")
                    && matches!(b.as_ref(), Formula::Int(0)))
        });
        let has_ub = derived.iter().any(|f| {
            matches!(f, Formula::Le(a, b)
                if matches!(a.as_ref(), Formula::Var(n, Sort::Int) if n == "out")
                    && matches!(b.as_ref(), Formula::Int(255)))
        });
        assert!(
            has_lb && has_ub,
            "window mask must emit `out ≥ 0` and `out ≤ 255`, got {derived:?}"
        );
    }

    // Flatten the top-level And into a conjunct view for the rewrite-unit tests.
    fn collect_and_view(f: &Formula) -> Vec<&Formula> {
        match f {
            Formula::And(cs) => cs.iter().collect(),
            other => vec![other],
        }
    }
}
