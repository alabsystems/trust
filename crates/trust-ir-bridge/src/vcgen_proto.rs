//! Phase-2: trust-ir-native VC generation, shadow mode — FULL L0 safety.
//!
//! `docs/TRUST_IR_SPINE.md` Phase 2 ("VC generation on trust-ir (shadow
//! mode)") asks us to prove that verification conditions can be generated
//! *from trust-ir as the source of record* — not round-tripped back to
//! `trust_types::VerifiableFunction` (which would be the Principle-8 band-aid).
//! This module generalizes the first slice (which walked only `Inst::Assert`)
//! to a VC generator that walks EVERY L0 safety-bearing trust-ir node and emits
//! one VC per L0 safety obligation, using ONLY trust-ir as input.
//!
//! Scope and discipline:
//!
//! * **Input is `&trust_ir::Function` and nothing else.** The generator never
//!   consults `trust-types`, `VerifiableFunction`, or `trust-vcgen`. Those
//!   appear only in the `#[cfg(test)]` parity assertions below, where the
//!   trust-vcgen safety VC set is the differential oracle (exactly as
//!   `parity.rs` already uses it).
//! * **L0 safety only.** We cover the panic-class obligations the MIR→trust-ir
//!   lowering surfaces. There are THREE safety-bearing trust-ir node kinds, and
//!   the generator walks all of them:
//!   - **`Inst::Assert`** — the dominant shape. rustc lowers overflow / bounds /
//!     div-by-zero / shift-range / negation / null-deref / generic-panic checks
//!     to `Terminator::Assert`, which the bridge lowers to `Inst::Assert` with a
//!     faithful `ProofAnnotation`. The kind is recovered from that annotation.
//!   - **`Inst::Overflow`** — the bridge lowers `Rvalue::CheckedBinaryOp`
//!     (`checked_add`/`overflowing_*`) to `Inst::Overflow` carrying
//!     `ProofAnnotation::NoOverflow`. This node *independently* represents an
//!     arithmetic-safety obligation (the "did it overflow" lane), so it yields an
//!     `ArithmeticSafety` VC even on the (rare) paths where no separate
//!     `Overflow(op)` assert follows.
//!   - **`Inst::Unreachable`** — a control-flow terminator the lowering emits for
//!     proven-infeasible points (e.g. a diverging panic-intrinsic call, paired
//!     with `assert(false)`). It maps to `PanicFreedom`, covering trust-vcgen's
//!     `Unreachable` safety VcKind.
//!   Functional (L1) and domain (L2) obligations arrive through contracts/specs
//!   and are out of scope — the same boundary `parity.rs` draws.
//! * **Generation is PURELY from trust-ir.** The obligation kind is recovered
//!   from the node's own `Inst` discriminant + its `ProofAnnotation`s; nothing
//!   is read from trust-types to GENERATE. trust-types is consulted only in the
//!   `#[cfg(test)]` oracle to establish ground truth.
//!
//! ## Integer-cast policy invariant
//!
//! Rust integer `as` casts are total, defined conversions: they truncate,
//! extend, or reinterpret rather than panic on an out-of-range source value.
//! Since trust-vcgen policy commit `9f4b2c8417`, such casts therefore carry no
//! `CastOverflow` safety VC. The MIR bridge follows the same policy: an
//! `Rvalue::Cast` lowers to a typed `Inst::Cast` without `NoOverflow` or a
//! module-level `ArithmeticSafety` obligation. This is load-bearing because
//! module obligations enter authoritative native TrustMc request inventories;
//! retaining the old losslessness check could refute valid truncating Rust.
//! `defined_integer_casts_are_obligation_free_end_to_end` pins all three
//! surfaces (vcgen, lowered module, and native safety generation).
//!
//! ## Open decision D2.1 (noted, NOT resolved here)
//!
//! `docs/TRUST_IR_SPINE_BACKLOG.md` Phase-2 item D2.1 asks whether the
//! production trust-ir VC engine should be a **consolidated trust-ir VC
//! engine** (recommended) or a 46-module port of `trust-vcgen`. This is evidence
//! FOR the consolidated approach — a single traversal of trust-ir's own
//! node/annotation surface generates the L0 safety VC set — but it does NOT
//! decide D2.1. See the architecture note in the module-level test comment for
//! the one place where the trust-ir node carries LESS than the trust-types side
//! (the rich per-obligation `ProofFormula`/source span lives on the
//! module-level `proof_obligations`, not on the assert node).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_ir::Function;
use trust_ir::inst::Inst;
use trust_ir::proof::{ObligationKind, ProofAnnotation};
use trust_ir::value::ValueId;

/// A single L0-safety verification condition generated *natively* from
/// trust-ir — i.e. from a `trust_ir::Function`'s `Inst::Assert` nodes, with no
/// reference to `trust-types`.
///
/// This is intentionally a *small* VC: enough to prove that trust-ir carries
/// the information a safety VC needs (a panic-class obligation kind, a source
/// description, and the asserted condition value), without reimplementing the
/// production VC payload (`trust_types::Formula`). The production engine (D2.1)
/// would attach a real formula; the prototype attaches the structural facts
/// that survive on the trust-ir spine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustIrSafetyVc {
    /// The trust-ir routing-grade obligation kind for this safety check,
    /// recovered from the assert node's `ProofAnnotation` (item T1 enriched the
    /// taxonomy so this is `ArithmeticSafety` / `BoundsCheck` / `PanicFreedom`,
    /// not a coarse single kind).
    pub kind: ObligationKind,
    /// A deterministic source location / description for the obligation,
    /// derived from the assert's position in the function and its faithful
    /// `ProofAnnotation`. This is the trust-ir-native stand-in for the
    /// trust-types obligation `description` — see the architecture note about
    /// what does and does not survive on the assert node.
    pub desc: String,
    /// The `ValueId` of the asserted condition, if available. `Inst::Assert`
    /// always carries one (the predicate to prove). `Inst::Overflow` and
    /// `Inst::Unreachable` have no single boolean condition value, so this is
    /// `None` for them — the obligation there is structural (the node's mere
    /// presence is the obligation). This is the hook a production engine would
    /// feed to a backend as "prove this value is true on every reaching path".
    pub cond: Option<ValueId>,
}

/// Classify the L0-safety obligation kind of an `Inst::Assert` purely from the
/// `ProofAnnotation`s the lowering attached to it.
///
/// This is the trust-ir-NATIVE counterpart to `lower::assert_obligation_kind`
/// (which classifies the *trust-types* `AssertMessage`). The faithful sub-kind
/// the lowering computed from the `AssertMessage` survives on the trust-ir side
/// as the assert node's `ProofAnnotation`, so we can re-derive the same
/// routing-grade `ObligationKind` from trust-ir alone:
///
/// | assert `ProofAnnotation`        | trust-ir `ObligationKind` |
/// |---------------------------------|---------------------------|
/// | `InBounds`                      | `BoundsCheck`             |
/// | `NoOverflow` / `ShiftInRange` / `DivNonZero` | `ArithmeticSafety` |
/// | `NotNull` / `NoPanic` / none / other | `PanicFreedom`       |
///
/// This is exactly the documented bounds↔BoundsCheck, overflow/div↔ArithmeticSafety
/// correspondence `parity.rs` pins. An assert with no recognized safety
/// annotation falls back to the generic panic-class `PanicFreedom` (fail-safe:
/// a check is never dropped — at worst it is classified coarser, never lost).
fn assert_safety_kind(proofs: &[ProofAnnotation]) -> ObligationKind {
    // A single assert carries at most one faithful safety annotation today, but
    // we scan defensively and take the most specific classification present.
    for proof in proofs {
        match proof {
            ProofAnnotation::InBounds => return ObligationKind::BoundsCheck,
            ProofAnnotation::NoOverflow
            | ProofAnnotation::ShiftInRange
            | ProofAnnotation::DivNonZero => return ObligationKind::ArithmeticSafety,
            _ => {}
        }
    }
    // No arithmetic/bounds sub-kind — generic panic-class obligation
    // (`NotNull`, `NoPanic`, an unannotated assert, etc.).
    ObligationKind::PanicFreedom
}

/// A short, deterministic description of the panic-class check an assert
/// guards, derived from its `ProofAnnotation` (or "unclassified" when none of
/// the recognized safety annotations is present).
fn assert_desc(proofs: &[ProofAnnotation]) -> &'static str {
    for proof in proofs {
        match proof {
            ProofAnnotation::InBounds => return "array/slice bounds check",
            ProofAnnotation::NoOverflow => return "arithmetic overflow check",
            ProofAnnotation::ShiftInRange => return "shift-amount-in-range check",
            ProofAnnotation::DivNonZero => return "division/remainder by-zero check",
            ProofAnnotation::NotNull => return "null-pointer-dereference check",
            ProofAnnotation::NoPanic => return "panic-freedom check",
            _ => {}
        }
    }
    "unclassified panic-freedom check"
}

/// The L0-safety obligation a single trust-ir node carries, if any.
///
/// This is the heart of the FULL-coverage generalization: instead of matching
/// only `Inst::Assert`, it dispatches on the `Inst` discriminant and recovers
/// the obligation kind purely from trust-ir (node kind + its `ProofAnnotation`s).
/// Returns `None` for nodes that carry no L0 safety obligation.
///
/// | trust-ir node       | recovered `ObligationKind`           | `cond` |
/// |---------------------|--------------------------------------|--------|
/// | `Inst::Assert`      | from `ProofAnnotation` (see `assert_safety_kind`) | the predicate |
/// | `Inst::Overflow`    | `ArithmeticSafety` (checked add/sub/mul) | none   |
/// | `Inst::Unreachable` | `PanicFreedom` (path must be infeasible) | none   |
/// | explicitly annotated `Inst::Cast` + `NoOverflow` | `ArithmeticSafety` | none |
///
/// A normal MIR-lowered `Inst::Cast` has no `NoOverflow` annotation and carries
/// no obligation. The annotated form remains supported for an explicit TrustIr
/// producer that deliberately requests a separate losslessness property; the
/// Rust MIR bridge never manufactures one from `as` syntax.
fn node_safety_vc(node: &trust_ir::node::InstrNode) -> Option<TrustIrSafetyVc> {
    match &node.inst {
        // The dominant shape: a checked panic-class assert. Kind + description
        // are recovered from the faithful `ProofAnnotation` the lowering
        // attached (overflow/shift/div → ArithmeticSafety, bounds → BoundsCheck,
        // everything else → PanicFreedom).
        Inst::Assert { cond } => Some(TrustIrSafetyVc {
            kind: assert_safety_kind(&node.proofs),
            desc: assert_desc(&node.proofs).to_string(),
            cond: Some(*cond),
        }),

        // A checked-arithmetic node (`Rvalue::CheckedBinaryOp` → `Inst::Overflow`,
        // `lower.rs:3868`). It carries `ProofAnnotation::NoOverflow` and is the
        // trust-ir-native representation of "this add/sub/mul may overflow", so it
        // is an arithmetic-safety obligation in its own right — recovered from the
        // node kind, with the annotation confirming the classification.
        Inst::Overflow { .. } => Some(TrustIrSafetyVc {
            kind: ObligationKind::ArithmeticSafety,
            desc: "checked-arithmetic overflow obligation".to_string(),
            cond: None,
        }),

        // A proven-infeasible point: the lowering emits `Inst::Unreachable` for a
        // diverging panic-intrinsic call (paired with `assert(false)`,
        // `lower.rs:4876`) and for `Terminator::Unreachable`. The obligation is
        // that this point is never reached — a panic-freedom / reachability
        // obligation, matching trust-vcgen's `Unreachable` safety VcKind.
        Inst::Unreachable => Some(TrustIrSafetyVc {
            kind: ObligationKind::PanicFreedom,
            desc: "unreachable-code reachability obligation".to_string(),
            cond: None,
        }),

        // An explicitly annotated TrustIr cast can request a separate
        // losslessness proof. MIR-lowered Rust `as` casts never receive this
        // annotation because the conversion itself is total and defined.
        Inst::Cast { .. } if node.proofs.contains(&ProofAnnotation::NoOverflow) => {
            Some(TrustIrSafetyVc {
                kind: ObligationKind::ArithmeticSafety,
                desc: "cast range/overflow check".to_string(),
                cond: None,
            })
        }

        // Coroutine / exception-handling structural nodes carry NO L0 *safety*
        // obligation, so each yields `None` here — exactly like the existing
        // `Inst::Call` / `Inst::Store` / `Inst::Return` nodes that already fall
        // through the catch-all. This engine emits a VC only for a panic-class
        // obligation (overflow / bounds / div / unreachable-
        // reachability), never for control flow or a call as such; manufacturing
        // a VC for any of these would FABRICATE a false obligation on a safe
        // construct. They are listed explicitly — not swept into the catch-all —
        // so the "intentionally not safety-bearing" decision is auditable and a
        // future safety obligation on one of them cannot be dropped silently.
        //
        // * `CoroSuspend` macro-expands to `GEP(frame, state_slot) +
        //   Store(next_state) + Return(value)`; none of those primitives is a
        //   safety-bearing node in this engine, so the suspend point is not one
        //   either (its store/return safety, if any, is the lowered primitives').
        // * `Invoke` is call-like (`Call(callee, args)` + a branch to
        //   `normal_dest`); like `Inst::Call`/`Inst::CallIndirect` it carries no
        //   L0 panic-class obligation in this VC set (the callee's own
        //   obligations live in the callee).
        // * `LandingPad` supplies unwinder-provided results (havoc) and LSDA
        //   metadata; it is not a checked operation.
        // * `Resume` re-raises via `_Unwind_Resume(exn)` (divergent); no
        //   postcondition obligation flows to any successor.
        Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. } => None,

        _ => None,
    }
}

/// Generate the L0-safety VC set for `func` **natively from trust-ir**.
///
/// Walks every block and every instruction node of the `Function` and, for each
/// L0 safety-bearing node (`Inst::Assert` / `Inst::Overflow` / `Inst::Unreachable`
/// — see [`node_safety_vc`]), emits one [`TrustIrSafetyVc`] whose `kind` is
/// recovered purely from trust-ir. The order is deterministic: block declaration
/// order, then node order within a block.
///
/// This consults ONLY the `trust_ir::Function` — no trust-types, no
/// VerifiableFunction, no trust-vcgen. That is the whole point: proving trust-ir
/// is a sufficient source of record for L0 safety VC generation (Phase 2,
/// shadow mode).
pub fn safety_vcs_from_trust_ir(func: &Function) -> Vec<TrustIrSafetyVc> {
    let mut vcs = Vec::new();
    for block in &func.blocks {
        for node in &block.body {
            if let Some(vc) = node_safety_vc(node) {
                vcs.push(vc);
            }
        }
    }
    vcs
}

/// A trust-ir-native L0 safety obligation carrying a SOLVABLE, SMT-bearing
/// formula — the piece that lets trust-ir be the verdict source of record.
///
/// Where [`TrustIrSafetyVc`] proves the *kind* and *condition value* survive on
/// the spine, this proves the *solvable formula* does: the MIR→trust-ir lowering
/// stamps the core safety predicate (overflow out-of-range, divisor-is-zero) onto
/// the obligation's `ProofFormula` (`lower.rs`,
/// `ObligationSourceMetadata::safety_into_formula`), equivalent to the one
/// `trust_vcgen` produces. This struct surfaces that formula, read PURELY from
/// the lowered `trust_ir::Module` (its `proof_obligations`) — no trust-types, no
/// trust-vcgen at generation time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustIrSafetyObligation {
    /// The routing-grade obligation kind (`ArithmeticSafety` / `BoundsCheck` /
    /// `PanicFreedom`).
    pub kind: ObligationKind,
    /// The human-facing description carried by the obligation.
    pub desc: String,
    /// The solvable formula's SMT-LIB2 rendering, when one was reconstructed
    /// faithfully at lowering time. Present for the reconstructed L0 safety
    /// classes: Add/Sub overflow, div/rem-by-zero, DIRECT-COMPARISON bounds
    /// (`Ge(idx,len)` / `Or(Lt(idx,0),Ge(idx,len))`), and shift overflow
    /// (`And([range(amount), invalid_shift(amount)])`). `None` (fail-closed) when
    /// the obligation carries only source metadata — a safety class outside the
    /// faithful reconstruction envelope: MULTIPLY overflow (trust-vcgen uses the
    /// bitvector encoding), the negation ASSERT path (trust-vcgen uses an
    /// abstract-flag formula with no operand content), the abstract-flag bounds
    /// shape, or the function-level panic-freedom aggregate.
    pub smtlib: Option<String>,
    /// The solvable formula's serialized `trust_types::Formula` JSON payload
    /// (schema `trust-types.Formula@1`), when present. The same `Formula` AST
    /// `trust_vcgen` builds, so a consumer can deserialize it without re-parsing.
    pub formula_json: Option<String>,
    /// The SMT sort of the formula (`Bool` for a reconstructed safety predicate),
    /// when a solvable formula is present.
    pub sort: Option<String>,
}

/// The schema a reconstructed solvable safety formula is stamped under — the
/// same `trust-types.Formula@1` schema the contract-predicate enrichment uses,
/// so a router indexes safety and contract formulas identically.
const SAFETY_FORMULA_SCHEMA: &str = "trust-types.Formula@1";

/// Collect the trust-ir-native L0 safety obligations carrying SOLVABLE formulas
/// from a lowered [`trust_ir::Module`], reading ONLY `module.proof_obligations`.
///
/// Returns one [`TrustIrSafetyObligation`] per safety obligation (`ArithmeticSafety`
/// / `BoundsCheck`; the `PanicFreedom` function-level aggregate is included too so
/// callers see the full panic-class set), each carrying the stamped solvable
/// formula when one was reconstructed. This is the spine-native counterpart to
/// reading a `trust_vcgen::VerificationCondition`'s `formula` — the proof that a
/// future verdict flip can read a solvable formula straight off trust-ir.
///
/// Generation consults ONLY trust-ir: no trust-types, no VerifiableFunction, no
/// trust-vcgen (those appear only in the `#[cfg(test)]` parity oracle).
pub fn safety_obligations_from_trust_ir_module(
    module: &trust_ir::Module,
) -> Vec<TrustIrSafetyObligation> {
    let mut obligations = Vec::new();
    for ob in &module.proof_obligations {
        // L0 safety classes only (skip contract pre/post/invariant/refinement).
        if !matches!(
            ob.kind,
            ObligationKind::ArithmeticSafety
                | ObligationKind::BoundsCheck
                | ObligationKind::PanicFreedom
        ) {
            continue;
        }
        // A solvable formula is present only when the stamped `ProofFormula` uses
        // the `trust-types.Formula@1` schema (the reconstructed-predicate schema);
        // the source-metadata schema carries no solvable formula.
        let (smtlib, formula_json, sort) = match &ob.formula {
            Some(f) if f.schema == SAFETY_FORMULA_SCHEMA => {
                (f.smtlib.clone(), Some(f.payload.clone()), f.sort.clone())
            }
            _ => (None, None, None),
        };
        obligations.push(TrustIrSafetyObligation {
            kind: ob.kind.clone(),
            desc: ob.description.clone(),
            smtlib,
            formula_json,
            sort,
        });
    }
    obligations
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use trust_ir::proof::ObligationKind;

    use super::*;
    use crate::lower::lower_to_trust_ir;
    // Reuse the EXACT representative fixtures and the trust-vcgen oracle helpers
    // from the Phase-0/dimension-(B) parity harness (`parity.rs`), so the
    // trust-ir-native VC set is checked against the same ground truth.
    use crate::parity::tests as oracle;

    // ===================================================================
    // Architecture note for D2.1 (the consolidated trust-ir VC engine)
    // ===================================================================
    //
    // Can a VC be generated PURELY from trust-ir, with no trust-types info?
    // For the L0 *safety* obligation KIND and the asserted CONDITION: YES. The
    // MIR→trust-ir lowering classifies each `Terminator::Assert` by its
    // `AssertMessage` and stores BOTH (a) a routing-grade `ObligationKind` in
    // the module-level `proof_obligations`, AND (b) the faithful sub-kind as the
    // assert node's `ProofAnnotation` (`InBounds` / `NoOverflow` / `DivNonZero`
    // / `ShiftInRange` / `NotNull`). Because the annotation rides on the node,
    // a `&Function`-only walk re-derives the same `ObligationKind` the
    // trust-types/router path uses — which is what these tests verify.
    //
    // The ONE thing the trust-ir *node* carries less of than the trust-types
    // side: the rich per-obligation `ProofFormula` (source_id / assertion_id /
    // span, schema `trust.trust_ir.obligation-source.v1`) is attached to the
    // module-level `proof_obligations`, NOT to the `Inst::Assert` node (the
    // lowering does not call `.with_span()` on the assert). So a *function*-only
    // engine reconstructs `desc` from position+annotation (as this prototype
    // does); a production engine wanting the exact source span would either
    // (i) walk the module's `proof_obligations` alongside the function, or
    // (ii) have the lowering also stamp the span onto the assert node. Neither
    // is a trust-types dependency — both stay on the trust-ir spine — which is
    // precisely why the consolidated trust-ir VC engine (D2.1, recommended) is
    // feasible. This prototype does NOT resolve D2.1; it is evidence for it.

    /// The deterministic multiset of trust-ir-native VC kinds for `func`, keyed
    /// by the `ObligationKind`'s canonical `Display` name with a count — the
    /// trust-ir-native analogue of `parity.rs`'s obligation/vcgen summaries.
    fn native_vc_kind_summary(func: &trust_ir::Function) -> BTreeMap<String, usize> {
        let mut summary = BTreeMap::new();
        for vc in safety_vcs_from_trust_ir(func) {
            *summary.entry(vc.kind.to_string()).or_insert(0) += 1;
        }
        summary
    }

    /// Lower a fixture to trust-ir and return the trust-ir-native VC kind
    /// summary for its single (entry) function.
    fn native_vc_kinds_for(func: &trust_types::VerifiableFunction) -> BTreeMap<String, usize> {
        let module =
            lower_to_trust_ir(func).expect("representative fixture must lower to trust-ir");
        // Each fixture lowers to exactly one function; sum across all to be safe.
        let mut summary = BTreeMap::new();
        for f in &module.functions {
            for (k, v) in native_vc_kind_summary(f) {
                *summary.entry(k).or_insert(0) += v;
            }
        }
        summary
    }

    /// Regression (trust-ir#coroutines / #exceptions): the four structural opcodes
    /// `CoroSuspend` / `Invoke` / `LandingPad` / `Resume` are control flow and
    /// unwinder-supplied values, NOT panic-class safety obligations — like
    /// `Inst::Call` / `Inst::Store` / `Inst::Return` they must yield NO L0 safety VC.
    /// A future edit that swept one into a manufactured VC would FABRICATE a false
    /// obligation on a safe construct (the over-flagging the cast/widening soundness
    /// guard forbids), so guard the `None` decision here.
    #[test]
    fn coroutine_and_exception_opcodes_carry_no_l0_safety_vc() {
        use trust_ir::node::InstrNode;
        use trust_ir::value::{BlockId, FuncId};

        let opcodes = [
            Inst::CoroSuspend {
                frame: ValueId::new(0),
                state_slot: 0,
                next_state: 1,
                value: ValueId::new(1),
            },
            Inst::Invoke {
                callee: FuncId::new(0),
                args: vec![],
                normal_dest: BlockId::new(1),
                normal_args: vec![],
                unwind_dest: BlockId::new(2),
            },
            Inst::LandingPad { is_cleanup: false, catch_type_indices: vec![] },
            Inst::Resume { exn: ValueId::new(0) },
        ];

        for inst in opcodes {
            let desc = format!("{inst:?}");
            assert!(
                node_safety_vc(&InstrNode::new(inst)).is_none(),
                "structural opcode {desc} must carry no L0 safety obligation",
            );
        }
    }

    // -----------------------------------------------------------------
    // (a) The trust-ir-native VC set's kinds equal what the oracle expects.
    //
    // GROUND TRUTH (recorded; matches the `parity.rs` dimension-(B) table):
    //   overflow → arithmetic_safety   (one Overflow(Add) assert)
    //   bounds   → bounds_check        (one BoundsCheck assert)
    //   div      → arithmetic_safety   (one DivisionByZero assert)
    // Each fixture has exactly one `Terminator::Assert`, so exactly one VC.
    // (The function-level aggregate `PanicFreedom` obligation lives on the
    // module, NOT on any assert node, so it is correctly absent here: this
    // engine walks ASSERTS, and there is one per fixture.)
    // -----------------------------------------------------------------

    #[test]
    fn overflow_native_vc_is_arithmetic_safety() {
        let kinds = native_vc_kinds_for(&oracle::overflow_checked_add());
        assert_eq!(
            kinds,
            BTreeMap::from([(ObligationKind::ArithmeticSafety.to_string(), 1)]),
            "overflow fixture must yield exactly one trust-ir-native ArithmeticSafety VC: {kinds:?}"
        );
    }

    #[test]
    fn bounds_native_vc_is_bounds_check() {
        let kinds = native_vc_kinds_for(&oracle::array_index_bounds());
        assert_eq!(
            kinds,
            BTreeMap::from([(ObligationKind::BoundsCheck.to_string(), 1)]),
            "bounds fixture must yield exactly one trust-ir-native BoundsCheck VC: {kinds:?}"
        );
    }

    #[test]
    fn div_native_vc_is_arithmetic_safety() {
        let kinds = native_vc_kinds_for(&oracle::division_by_zero_guard());
        assert_eq!(
            kinds,
            BTreeMap::from([(ObligationKind::ArithmeticSafety.to_string(), 1)]),
            "div fixture must yield exactly one trust-ir-native ArithmeticSafety VC: {kinds:?}"
        );
    }

    #[test]
    fn native_vc_carries_assert_condition_value() {
        // The prototype VC exposes the asserted condition `ValueId`, the hook a
        // production backend would discharge. Every assert-derived VC has one.
        let module = lower_to_trust_ir(&oracle::overflow_checked_add()).expect("lowers");
        let vcs: Vec<_> = module.functions.iter().flat_map(safety_vcs_from_trust_ir).collect();
        assert_eq!(vcs.len(), 1, "one assert → one VC: {vcs:?}");
        assert!(vcs[0].cond.is_some(), "assert VC must carry its condition value: {vcs:?}");
    }

    // -----------------------------------------------------------------
    // (b) The trust-ir-native kinds match the trust-vcgen safety VcKind set,
    //     via the SAME documented mapping `parity.rs` uses
    //     (bounds↔BoundsCheck, overflow/div↔ArithmeticSafety), AND the
    //     "fail on unmapped safety kind" property is preserved so a gap can
    //     never be silently masked.
    // -----------------------------------------------------------------

    /// For `func`: every trust-vcgen **safety** VcKind that the documented T1
    /// mapping says is a panic-class obligation is COVERED by a trust-ir-native
    /// VC of the corresponding `ObligationKind`; and every safety VcKind that
    /// maps to `None` (a documented carve-out, e.g. `UnsupportedMir`) must be in
    /// `expected_carve_outs` — otherwise the test FAILS (cannot mask a gap).
    fn assert_native_vcs_cover_vcgen_safety(
        func: &trust_types::VerifiableFunction,
        expected_carve_outs: &[&str],
    ) {
        let vcgen = oracle::vcgen_safety_kind_multiset(func);
        let native = native_vc_kinds_for(func);

        for (variant, count) in &vcgen {
            assert!(*count >= 1);
            match oracle::vcgen_kind_to_trust_ir_obligation(variant) {
                Some(ob) => {
                    // The documented mapping: this trust-vcgen safety VcKind must
                    // be covered by a trust-ir-native VC of the same kind (≥ 1).
                    let ob_name = ob.to_string();
                    let native_count = native.get(&ob_name).copied().unwrap_or(0);
                    assert!(
                        native_count >= 1,
                        "trust-vcgen emitted safety VcKind `{variant}` (×{count}) but the \
                         trust-ir-NATIVE VC set has no covering `{ob_name}` VC: \
                         vcgen={vcgen:?} native={native:?}"
                    );
                }
                None => {
                    // A safety VcKind that intentionally does NOT lower to a
                    // trust-ir assert obligation must be a documented carve-out;
                    // an unaccounted unmapped kind fails the test.
                    assert!(
                        expected_carve_outs.contains(&variant.as_str()),
                        "trust-vcgen safety VcKind `{variant}` has no trust-ir VC mapping and is \
                         NOT in the documented carve-outs {expected_carve_outs:?}; this is an \
                         unaccounted parity gap: vcgen={vcgen:?} native={native:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn overflow_native_matches_vcgen_safety() {
        // `UnsupportedMir` is the fail-closed proof-gap sentinel carve-out the
        // dimension-(B) oracle documents — NOT a dropped panic obligation.
        assert_native_vcs_cover_vcgen_safety(&oracle::overflow_checked_add(), &["UnsupportedMir"]);
    }

    #[test]
    fn bounds_native_matches_vcgen_safety() {
        assert_native_vcs_cover_vcgen_safety(&oracle::array_index_bounds(), &[]);
    }

    #[test]
    fn div_native_matches_vcgen_safety() {
        assert_native_vcs_cover_vcgen_safety(&oracle::division_by_zero_guard(), &[]);
    }

    // =================================================================
    // (c) BROADER L0-safety corpus (trust-ir-spine Phase 2, FULL L0).
    //
    // Every fixture below is checked with the SAME `assert_native_vcs_cover_vcgen_safety`
    // helper as (b): for each trust-vcgen *safety* VcKind, either the documented
    // T1 mapping covers it with a trust-ir-native VC of the corresponding kind,
    // or it is an explicit carve-out — an unmapped, un-carved kind FAILS the
    // test, so a coverage gap can never be silently masked.
    //
    // Ground truth captured empirically from `trust_vcgen::generate_vcs` (default
    // pipeline-v2) on these exact fixtures:
    //
    //   fixture             trust-vcgen safety VcKinds                      trust-ir-native VCs
    //   ----------------    -------------------------------------------     -------------------------------
    //   checked_add_tuple   ArithmeticOverflow                              arithmetic_safety x2  (Overflow node + assert)
    //   shift               ArithmeticOverflow, UnsupportedMir              arithmetic_safety x1
    //   neg                 ArithmeticOverflow, UnsupportedMir              arithmetic_safety x1
    //   null                UnsupportedMir                                  panic_freedom x1
    //   misaligned          UnsupportedMir                                  panic_freedom x1
    //   multi               ArithmeticOverflow, DivisionByZero, IndexOutOfBounds   arithmetic_safety x1, bounds_check x1
    //   cast (narrowing)    (none; defined Rust conversion)                 (none)
    //   cast (widening)     (none)                                          (none)
    // =================================================================

    #[test]
    fn checked_binop_overflow_node_yields_arithmetic_safety_vc() {
        // The CANONICAL checked-add shape lowers to BOTH an `Inst::Overflow`
        // node AND an `Overflow(Add)` assert, so the engine emits exactly two
        // ArithmeticSafety VCs — one structural (the Overflow node, `cond: None`)
        // and one assert-backed (`cond: Some`). This proves the engine walks the
        // checked-overflow rvalue node, not just asserts.
        let module = lower_to_trust_ir(&oracle::checked_add_overflow_tuple()).expect("lowers");
        let vcs: Vec<_> = module.functions.iter().flat_map(safety_vcs_from_trust_ir).collect();
        assert_eq!(
            vcs.iter().filter(|v| v.kind == ObligationKind::ArithmeticSafety).count(),
            2,
            "checked-add lowers to an Overflow node + an Overflow assert, both arithmetic: {vcs:?}"
        );
        // Exactly one of the two is the structural Overflow-node VC (no cond).
        assert_eq!(
            vcs.iter().filter(|v| v.cond.is_none()).count(),
            1,
            "the Inst::Overflow VC is structural (cond: None); the assert VC carries a cond: {vcs:?}"
        );
    }

    #[test]
    fn checked_add_tuple_native_matches_vcgen_safety() {
        assert_native_vcs_cover_vcgen_safety(&oracle::checked_add_overflow_tuple(), &[]);
    }

    #[test]
    fn shift_overflow_native_matches_vcgen_safety() {
        // `UnsupportedMir` is the fail-closed sentinel carve-out (the const-false
        // overflow-flag shape vcgen cannot model into a faithful overflow VC).
        assert_native_vcs_cover_vcgen_safety(&oracle::shift_overflow_guard(), &["UnsupportedMir"]);
    }

    #[test]
    fn negation_overflow_native_matches_vcgen_safety() {
        assert_native_vcs_cover_vcgen_safety(
            &oracle::negation_overflow_guard(),
            &["UnsupportedMir"],
        );
    }

    #[test]
    fn null_deref_native_matches_vcgen_safety() {
        // trust-vcgen emits ONLY an `UnsupportedMir` sentinel for null-deref —
        // it does not model it as a faithful safety VcKind — so the carve-out
        // covers it. The trust-ir side is actually MORE faithful: the bridge
        // lowers it to a `PanicFreedom` obligation (a covering native VC exists).
        assert_native_vcs_cover_vcgen_safety(&oracle::null_deref_guard(), &["UnsupportedMir"]);
        // Pin that the trust-ir-native engine does emit a covering PanicFreedom VC.
        let native = native_vc_kinds_for(&oracle::null_deref_guard());
        assert_eq!(
            native.get(&ObligationKind::PanicFreedom.to_string()).copied(),
            Some(1),
            "null-deref must surface a trust-ir-native PanicFreedom VC (check not dropped): {native:?}"
        );
    }

    #[test]
    fn misaligned_deref_native_matches_vcgen_safety() {
        assert_native_vcs_cover_vcgen_safety(
            &oracle::misaligned_deref_guard(),
            &["UnsupportedMir"],
        );
        // Misaligned-deref has no faithful trust-ir annotation, but the
        // `PanicFreedom` obligation still covers it — the check is never lost.
        let native = native_vc_kinds_for(&oracle::misaligned_deref_guard());
        assert_eq!(
            native.get(&ObligationKind::PanicFreedom.to_string()).copied(),
            Some(1),
            "misaligned-deref must surface a coarse PanicFreedom VC (check not dropped): {native:?}"
        );
    }

    #[test]
    fn multiple_asserts_native_matches_vcgen_safety() {
        // Two distinct safety asserts (bounds + div) in one function. vcgen also
        // surfaces the signed-div `INT_MIN/-1` ArithmeticOverflow; all map to the
        // two trust-ir kinds present.
        assert_native_vcs_cover_vcgen_safety(&oracle::multiple_asserts_one_function(), &[]);
        let native = native_vc_kinds_for(&oracle::multiple_asserts_one_function());
        assert_eq!(
            native.get(&ObligationKind::BoundsCheck.to_string()).copied(),
            Some(1),
            "multi-assert function must surface a BoundsCheck VC: {native:?}"
        );
        assert_eq!(
            native.get(&ObligationKind::ArithmeticSafety.to_string()).copied(),
            Some(1),
            "multi-assert function must surface an ArithmeticSafety VC: {native:?}"
        );
    }

    #[test]
    fn unreachable_node_yields_panic_freedom_vc() {
        // A `Terminator::Unreachable` lowers to `Inst::Unreachable`
        // (`lower.rs:4720`); the engine recovers a PanicFreedom reachability
        // obligation from the node kind alone (no annotation, no condition). This
        // proves the engine covers the third safety-bearing node kind.
        use trust_ir::inst::Inst as TInst;
        let module = lower_to_trust_ir(&oracle::unreachable_terminator()).expect("lowers");
        // Sanity: the lowered module actually contains an Inst::Unreachable node.
        let has_unreachable = module.functions.iter().any(|f| {
            f.blocks.iter().any(|b| b.body.iter().any(|n| matches!(n.inst, TInst::Unreachable)))
        });
        assert!(has_unreachable, "fixture must lower to an Inst::Unreachable node");
        let vcs: Vec<_> = module.functions.iter().flat_map(safety_vcs_from_trust_ir).collect();
        assert!(
            vcs.iter().any(|v| v.kind == ObligationKind::PanicFreedom && v.cond.is_none()),
            "unreachable node must yield a structural PanicFreedom VC: {vcs:?}"
        );
    }

    // -----------------------------------------------------------------
    // (d) CastOverflow — POLICY UPDATE (9f4b2c8417, owner decision 2026-07-06).
    //
    // trust-vcgen used to emit `VcKind::CastOverflow` directly from a narrowing
    // integer `Rvalue::Cast` statement. The owner decision made int→int `as`
    // casts obligation-FREE (they are DEFINED Rust — truncate / sign-extend /
    // reinterpret, never a trap); vcgen type-tracks the result to its target
    // range instead (`guards::narrowing_cast_result_range`). The bridge must not
    // retain the retired losslessness obligation: module proof obligations feed
    // authoritative native TrustMc request inventories and can affect verdicts.
    // -----------------------------------------------------------------

    #[test]
    fn defined_integer_casts_are_obligation_free_end_to_end() {
        let func = oracle::cast_overflow_narrowing();
        let vcgen = oracle::vcgen_safety_kind_multiset(&func);

        // Ground truth (post-9f4b2c8417): trust-vcgen emits NO CastOverflow for a
        // defined int→int `as` cast. (The kind still maps to ArithmeticSafety in
        // the T1 table for any VC that does carry it.)
        assert_eq!(
            vcgen.get("CastOverflow").copied(),
            None,
            "a defined int→int `as` cast must NOT surface a trust-vcgen CastOverflow \
             VC (9f4b2c8417 policy): {vcgen:?}"
        );
        assert_eq!(
            oracle::vcgen_kind_to_trust_ir_obligation("CastOverflow"),
            Some(ObligationKind::ArithmeticSafety),
        );

        // The normal parity check remains exact and vacuous for the cast.
        assert_native_vcs_cover_vcgen_safety(&func, &[]);

        // No native node VC may be generated for ordinary Rust cast syntax.
        let native = native_vc_kinds_for(&func);
        assert!(
            native.is_empty(),
            "a defined narrowing cast must not become native ArithmeticSafety: {native:?}"
        );

        // The authoritative module inventory is also empty: no NoOverflow node
        // marker and no module-level ArithmeticSafety proof obligation can enter
        // a native TrustMc request.
        let module = lower_to_trust_ir(&func).expect("lowers");
        assert!(
            module.proof_obligations.iter().all(|obligation| {
                obligation.kind != ObligationKind::ArithmeticSafety
                    && obligation.description != "cast range/overflow check"
            }),
            "defined casts must not enter the module proof inventory: {:?}",
            module.proof_obligations
        );
        let cast_nodes: Vec<_> = module
            .functions
            .iter()
            .flat_map(|function| &function.blocks)
            .flat_map(|block| &block.body)
            .filter(|node| matches!(node.inst, Inst::Cast { .. }))
            .collect();
        assert_eq!(cast_nodes.len(), 1, "fixture contains exactly one typed cast node");
        assert!(
            cast_nodes[0].proofs.is_empty(),
            "MIR-lowered `as` cast must carry no proof annotation: {:?}",
            cast_nodes[0].proofs
        );

        let generated = crate::lower::generate_native_safety_vcs(&func)
            .expect("cast-only function is fully representable");
        assert!(
            generated.is_empty(),
            "native safety generation must not resurrect retired CastOverflow: {generated:?}"
        );
    }

    #[test]
    fn widening_cast_yields_no_spurious_vc() {
        // SOUNDNESS GUARD (no over-flagging): a widening/lossless integer cast
        // (`i8 as i32`) has every source value fitting the target, so trust-vcgen
        // emits NO CastOverflow VC, and the bridge stamps NO annotation. The
        // trust-ir-native VC set must therefore be EMPTY — emitting a VC here would
        // be a FALSE obligation on a safe cast.
        let func = oracle::cast_widening_lossless();

        // Ground truth: trust-vcgen emits no CastOverflow (no safety VC at all).
        let vcgen = oracle::vcgen_safety_kind_multiset(&func);
        assert_eq!(
            vcgen.get("CastOverflow").copied(),
            None,
            "a widening/lossless cast must NOT surface a trust-vcgen CastOverflow VC: {vcgen:?}"
        );

        // The trust-ir-native engine emits nothing — no false obligation.
        let native = native_vc_kinds_for(&func);
        assert!(
            native.is_empty(),
            "a widening/lossless cast must yield NO trust-ir-native VC (no false \
             obligation on a safe cast): native={native:?}"
        );

        // And the strict coverage check still passes (vacuously: there is no
        // vcgen safety VcKind to cover), confirming no parity divergence.
        assert_native_vcs_cover_vcgen_safety(&func, &[]);

        // Belt-and-braces: the lowered cast node carries NO NoOverflow annotation,
        // so the over-flagging is impossible by construction at the node level.
        let module = lower_to_trust_ir(&func).expect("lowers");
        let cast_has_no_overflow_annotation = module.functions.iter().any(|f| {
            f.blocks.iter().any(|b| {
                b.body.iter().any(|n| {
                    matches!(n.inst, Inst::Cast { .. })
                        && n.proofs.contains(&ProofAnnotation::NoOverflow)
                })
            })
        });
        assert!(
            !cast_has_no_overflow_annotation,
            "a widening cast's Inst::Cast must NOT carry a NoOverflow annotation"
        );
    }

    // =================================================================
    // (e) SOLVABLE SAFETY FORMULAS on the spine (trust-ir-spine Phase 2/3).
    //
    // The headline requirement: the trust-ir-native L0 safety obligation must
    // carry a SOLVABLE, SMT-bearing formula EQUIVALENT to the one trust-vcgen
    // produces, so a future verdict flip (trust-ir → source of record) cannot
    // regress `proved → unknown`. The MIR→trust-ir lowering now reconstructs the
    // core safety predicate (overflow out-of-range / divisor-is-zero) and STAMPS
    // it onto the obligation's `ProofFormula` (`lower.rs`); these tests prove the
    // stamp is present AND equal/equivalent to trust-vcgen's solvable formula.
    //
    // TWO EQUIVALENCE STANDARDS, applied per case:
    //
    //  * DIV-BY-ZERO — BYTE-EXACT. trust-vcgen's div-by-zero core is the bare
    //    `(= b 0)` with no arg-range wrapping, so the block-def-free
    //    `direct_div_by_zero_no_guard` fixture lets us assert SMT-LIB `==`.
    //
    //  * OVERFLOW — BYTE-EXACT against trust-vcgen's INNERMOST `body` subterm, and
    //    LOGICALLY EQUIVALENT to trust-vcgen's full emitted formula. trust-vcgen
    //    wraps `body` in TWO further layers of the SAME (idempotent) parameter
    //    type-range conjuncts (block-def pass + `conjoin_arg_type_ranges`), built
    //    by PRIVATE helpers we cannot call. Since `range(p) ∧ range(p) ≡ range(p)`,
    //    the full formula and the stamped `body` have identical models — identical
    //    verdict. We assert: (i) the stamp equals the `body` we extract from
    //    trust-vcgen's own AST by stripping the redundant arg-range wrappers, and
    //    (ii) trust-vcgen's full formula is exactly those wrappers around our stamp.
    // =================================================================

    /// The single solvable safety obligation of `kind` in the lowered module,
    /// or a panic with a helpful message. Reads ONLY the trust-ir module via the
    /// production `safety_obligations_from_trust_ir_module` (no trust-vcgen).
    fn stamped_safety_smtlib(
        func: &trust_types::VerifiableFunction,
        kind: ObligationKind,
    ) -> String {
        let module = lower_to_trust_ir(func).expect("fixture must lower");
        let obs = safety_obligations_from_trust_ir_module(&module);
        let with_formula: Vec<_> =
            obs.iter().filter(|o| o.kind == kind && o.smtlib.is_some()).collect();
        assert_eq!(
            with_formula.len(),
            1,
            "expected exactly one {kind} obligation carrying a solvable formula: {obs:?}"
        );
        // The stamp uses the shared `trust-types.Formula@1` schema with a Bool sort.
        assert_eq!(with_formula[0].sort.as_deref(), Some("Bool"));
        assert!(with_formula[0].formula_json.is_some(), "JSON payload must be present");
        with_formula[0].smtlib.clone().unwrap()
    }

    /// Deserialize the stamped JSON payload of the single solvable safety
    /// obligation of `kind` back into a `trust_types::Formula` — proving the
    /// machine-readable AST round-trips, not just the SMT-LIB string.
    fn stamped_safety_formula(
        func: &trust_types::VerifiableFunction,
        kind: ObligationKind,
    ) -> trust_types::Formula {
        let module = lower_to_trust_ir(func).expect("fixture must lower");
        let obs = safety_obligations_from_trust_ir_module(&module);
        let json = obs
            .iter()
            .find(|o| o.kind == kind && o.formula_json.is_some())
            .and_then(|o| o.formula_json.clone())
            .expect("a solvable obligation with a JSON payload");
        // The payload is `{ "formula": <Formula JSON>, "source": {...} }`.
        let value: serde_json::Value = serde_json::from_str(&json).expect("payload is JSON");
        serde_json::from_value(value["formula"].clone()).expect("formula field deserializes")
    }

    /// Descend a trust-vcgen overflow formula's redundant arg-range `And`
    /// wrappers to its innermost `body` — the `And([range, range, Or([...])])`
    /// whose last conjunct is the out-of-range `Or`. trust-vcgen's emitted formula
    /// is `And([range_a, range_b, <recurse>])`; the `body` is the first nested
    /// `And` whose final element is an `Or`.
    fn innermost_overflow_body(f: &trust_types::Formula) -> trust_types::Formula {
        use trust_types::Formula;
        if let Formula::And(conjuncts) = f
            && let Some(last) = conjuncts.last()
        {
            // `body` is the And whose last conjunct is the out-of-range Or.
            if matches!(last, Formula::Or(_)) {
                return f.clone();
            }
            // Otherwise the last conjunct is the next (inner) wrapped formula.
            return innermost_overflow_body(last);
        }
        f.clone()
    }

    #[test]
    fn div_stamp_smtlib_equals_vcgen_core_byte_exact() {
        // The GUARDED div-by-zero fixture gets a stamped ArithmeticSafety formula.
        let stamped = stamped_safety_smtlib(
            &oracle::division_by_zero_guard(),
            ObligationKind::ArithmeticSafety,
        );
        // GROUND TRUTH: the block-def-free direct-div fixture makes trust-vcgen
        // emit EXACTLY its core `(= b 0)` as the DivisionByZero VC.
        let vcgen_cores = oracle::vcgen_safety_formula_smtlibs(
            &oracle::direct_div_by_zero_no_guard(),
            "DivisionByZero",
        );
        assert_eq!(
            vcgen_cores.len(),
            1,
            "block-def-free direct div must emit exactly one DivisionByZero VC: {vcgen_cores:?}"
        );
        // BYTE-EXACT equivalence.
        assert_eq!(
            stamped, vcgen_cores[0],
            "trust-ir div-by-zero stamp must byte-equal trust-vcgen's core divisor-zero formula"
        );
        assert_eq!(stamped, "(= b 0)");
    }

    #[test]
    fn div_stamp_formula_ast_round_trips() {
        // The machine-readable `Formula` AST round-trips (not just the SMT-LIB).
        use trust_types::{Formula, Sort};
        let f = stamped_safety_formula(
            &oracle::division_by_zero_guard(),
            ObligationKind::ArithmeticSafety,
        );
        assert_eq!(
            f,
            Formula::Eq(Box::new(Formula::var("b", Sort::Int)), Box::new(Formula::Int(0)),),
            "the stamped div formula AST must be `b == 0`"
        );
    }

    #[test]
    fn overflow_stamp_equals_vcgen_innermost_body() {
        // The GUARDED overflow fixture gets a stamped ArithmeticSafety formula.
        let stamped_smt = stamped_safety_smtlib(
            &oracle::overflow_checked_add(),
            ObligationKind::ArithmeticSafety,
        );
        let stamped_ast = stamped_safety_formula(
            &oracle::overflow_checked_add(),
            ObligationKind::ArithmeticSafety,
        );

        // GROUND TRUTH: trust-vcgen's direct-add ArithmeticOverflow VC.
        let vcgen_vcs: Vec<_> = trust_vcgen::generate_vcs(&oracle::direct_add_overflow_no_guard())
            .into_iter()
            .filter(|vc| format!("{:?}", vc.kind).starts_with("ArithmeticOverflow"))
            .collect();
        assert_eq!(vcgen_vcs.len(), 1, "one ArithmeticOverflow VC expected");
        let vcgen_full = &vcgen_vcs[0].formula;

        // The stamp equals trust-vcgen's INNERMOST `body` subterm — byte-exact on
        // both the AST and its SMT-LIB. This is the documented overflow
        // equivalence: trust-vcgen wraps this exact `body` in idempotent arg-range
        // layers we deliberately don't reproduce.
        let body = innermost_overflow_body(vcgen_full);
        assert_eq!(
            stamped_ast, body,
            "trust-ir overflow stamp AST must equal trust-vcgen's innermost overflow body"
        );
        assert_eq!(
            stamped_smt,
            body.to_smtlib(),
            "trust-ir overflow stamp SMT-LIB must equal trust-vcgen's innermost body SMT-LIB"
        );

        // And concretely the expected solvable predicate.
        assert_eq!(
            stamped_smt,
            "(and (and (<= (- 2147483648) a) (<= a 2147483647)) \
             (and (<= (- 2147483648) b) (<= b 2147483647)) \
             (or (< (+ a b) (- 2147483648)) (> (+ a b) 2147483647)))"
        );

        // LOGICAL EQUIVALENCE to the FULL trust-vcgen formula: the full formula is
        // EXACTLY the (idempotent) arg-range wrappers around our stamped body, so
        // descending those wrappers recovers our stamp — confirming the full
        // formula and the stamp have identical models (no verdict difference).
        assert_eq!(
            innermost_overflow_body(vcgen_full),
            stamped_ast,
            "trust-vcgen's full overflow formula must be idempotent arg-range \
             wrappers around the stamped body (logically equivalent)"
        );
    }

    #[test]
    fn multi_assert_div_stamp_is_solvable_and_bounds_is_gap() {
        // A function with two asserts (bounds + div): the div obligation carries
        // the solvable `(= b 0)` stamp; the bounds obligation is a documented gap
        // (no stamp). This proves per-obligation stamping across multiple asserts.
        let stamped = stamped_safety_smtlib(
            &oracle::multiple_asserts_one_function(),
            ObligationKind::ArithmeticSafety,
        );
        assert_eq!(stamped, "(= b 0)");

        // The bounds obligation in the SAME function carries NO solvable formula
        // (the honest TODO gap), so it is fail-closed, not fabricated.
        let module = lower_to_trust_ir(&oracle::multiple_asserts_one_function()).expect("lowers");
        let obs = safety_obligations_from_trust_ir_module(&module);
        let bounds: Vec<_> = obs.iter().filter(|o| o.kind == ObligationKind::BoundsCheck).collect();
        assert_eq!(bounds.len(), 1, "one bounds obligation: {obs:?}");
        assert!(
            bounds[0].smtlib.is_none(),
            "bounds-check carries no solvable formula yet (documented gap, fail-closed): {:?}",
            bounds[0]
        );
    }

    #[test]
    fn bounds_obligation_is_fail_closed_not_fabricated() {
        // SOUNDNESS: the bounds case is not yet reconstructed. The obligation must
        // exist (the check is never dropped) but carry NO solvable formula — a
        // fabricated bounds formula would be worse than none. The fail-closed
        // audit marker is recorded in the obligation's source-metadata payload.
        let module = lower_to_trust_ir(&oracle::array_index_bounds()).expect("lowers");
        let obs = safety_obligations_from_trust_ir_module(&module);
        let bounds: Vec<_> = obs.iter().filter(|o| o.kind == ObligationKind::BoundsCheck).collect();
        assert_eq!(bounds.len(), 1, "bounds obligation present (check not dropped): {obs:?}");
        assert!(
            bounds[0].smtlib.is_none() && bounds[0].formula_json.is_none(),
            "bounds obligation must NOT carry a fabricated formula: {:?}",
            bounds[0]
        );
        // The raw module obligation records WHY (fail-closed audit marker).
        let raw = module
            .proof_obligations
            .iter()
            .find(|o| o.kind == ObligationKind::BoundsCheck)
            .expect("bounds obligation present");
        let payload = raw.formula.as_ref().expect("source metadata present").payload.clone();
        assert!(
            payload.contains("safety_formula_not_reconstructed"),
            "bounds obligation must record the fail-closed audit marker: {payload}"
        );
    }

    #[test]
    fn widening_cast_carries_no_safety_obligation_formula() {
        // A widening/lossless cast emits no safety VC in trust-vcgen and no
        // arithmetic obligation in the bridge — so there is nothing to stamp, and
        // no spurious solvable formula appears (the over-flagging soundness guard,
        // at the obligation level this time).
        let module = lower_to_trust_ir(&oracle::cast_widening_lossless()).expect("lowers");
        let obs = safety_obligations_from_trust_ir_module(&module);
        assert!(
            obs.iter().all(|o| o.smtlib.is_none()),
            "a lossless cast must yield no solvable safety formula: {obs:?}"
        );
    }

    #[test]
    fn assert_bearing_fn_surfaces_no_function_aggregate_panic_freedom() {
        // An `Assert`-bearing function (overflow/bounds/div) surfaces ONLY the
        // faithful per-site obligation kind and NO function-level `PanicFreedom`
        // aggregate: the lowering emits that aggregate only for diverging-panic
        // `Call` terminators, never for `Assert` sites (the w01/w13/w16/w19
        // completeness fix — a weaker whole-function transport CHC would regress
        // provably-safe arithmetic/bounds to INCONCLUSIVE). So zero aggregates here.
        let module = lower_to_trust_ir(&oracle::overflow_checked_add()).expect("lowers");
        let obs = safety_obligations_from_trust_ir_module(&module);
        let aggregate: Vec<_> =
            obs.iter().filter(|o| o.kind == ObligationKind::PanicFreedom).collect();
        assert!(
            aggregate.is_empty(),
            "an Assert-bearing fn surfaces no function-level PanicFreedom aggregate: {obs:?}"
        );
    }
}
