// trust-types/formula/vc: Verification condition and related types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use super::Formula;
use super::contracts::ContractMetadata;
use super::vc_kind::VcKind;
use crate::Symbol;
use crate::model::SourceSpan;

/// A verification condition — the thing we send to solvers.
///
/// # Examples
///
/// ```
/// use trust_types::{VerificationCondition, VcKind, Formula, Sort, SourceSpan, Symbol};
///
/// // Division-by-zero check: denominator != 0
/// let denom = Formula::Var("d".into(), Sort::Int);
/// let vc = VerificationCondition {
///     kind: VcKind::DivisionByZero,
///     function: Symbol::intern("my_crate::div"),
///     location: SourceSpan::default(),
///     formula: Formula::Eq(Box::new(denom), Box::new(Formula::Int(0))),
///     contract_metadata: None,
///     obligation: None,
/// };
///
/// assert_eq!(vc.kind.proof_level(), trust_types::ProofLevel::L0Safety);
/// assert!(!vc.has_contracts());
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationCondition {
    pub kind: VcKind,
    // Interned function name — reduces heap allocations for repeated
    // function names across verification conditions.
    pub function: Symbol,
    pub location: SourceSpan,
    /// The formula to check. Convention: we assert this formula and check SAT.
    /// If UNSAT, the property holds (no violation exists).
    /// If SAT, the model is a counterexample.
    pub formula: Formula,
    // Trust: Contract metadata for deductive verification routing.
    #[serde(default)]
    pub contract_metadata: Option<ContractMetadata>,
    /// Trust: authenticated-obligation record (the emitter's own account of WHICH
    /// sub-formula of `formula` is the obligation, plus the wrappers it applied and,
    /// where the kind implies them, the subject/width). This is a CLAIM checked by
    /// recomputation at consumption (reconstruct-and-equate against `formula`, and
    /// MIR cross-check for subject/width) — NEVER trusted. `#[serde(default)]` keeps
    /// every existing fixture dump byte-compatible: they deserialize this as `None`.
    /// Populated today only for the vertical-slice arms (div/rem-by-zero, negation
    /// overflow); every other producer leaves it `None`.
    #[serde(default)]
    pub obligation: Option<ObligationRecord>,
}

impl VerificationCondition {
    /// Returns true if this VC has any contract annotations.
    #[must_use]
    pub fn has_contracts(&self) -> bool {
        self.contract_metadata.as_ref().is_some_and(|m| m.has_any())
    }
}

// Serializable VC for serde boundaries (JSON proof certificates, caches).
//
// When `arena-formula` is enabled, `VerificationCondition` holds a `FormulaRef`.
// `SerializableVc` always holds an owned `Formula` and implements Serialize/Deserialize,
// used at persistence boundaries (proof certificates, JSON output).

/// A serializable verification condition — always holds an owned `Formula`.
///
/// Use this at persistence boundaries (proof certificates, JSON caches) where
/// the `FormulaArena` is not available. Convert using `from_vc()` / `into_vc()`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SerializableVc {
    pub kind: VcKind,
    // Interned function name for consistency with VerificationCondition.
    pub function: Symbol,
    pub location: SourceSpan,
    /// The formula to check (always an owned `Formula` for serialization).
    pub formula: Formula,
    #[serde(default)]
    pub contract_metadata: Option<ContractMetadata>,
    /// Trust: mirror of [`VerificationCondition::obligation`] across the serde
    /// boundary. Threaded explicitly through `from_vc`/`into_vc` (both enumerate
    /// every field) so the authenticated-obligation record survives a
    /// certificate/cache round-trip instead of being silently dropped.
    #[serde(default)]
    pub obligation: Option<ObligationRecord>,
}

impl SerializableVc {
    /// Create from a `VerificationCondition`.
    #[must_use]
    pub fn from_vc(vc: &VerificationCondition) -> Self {
        Self {
            kind: vc.kind.clone(),
            function: vc.function,
            location: vc.location.clone(),
            formula: vc.formula.clone(),
            contract_metadata: vc.contract_metadata,
            obligation: vc.obligation.clone(),
        }
    }

    /// Convert back to a `VerificationCondition`.
    #[must_use]
    pub fn into_vc(self) -> VerificationCondition {
        VerificationCondition {
            kind: self.kind,
            function: self.function,
            location: self.location,
            formula: self.formula,
            contract_metadata: self.contract_metadata,
            obligation: self.obligation,
        }
    }
}

/// Trust: the emitter's authenticated account of the obligation carried by a
/// [`VerificationCondition`]. This is a **claim**, checked by recomputation at
/// consumption — it is never a grant. The soundness of the mechanism rests on
/// the consumer authenticating it, not on this data being trusted:
///
/// * `body` + `wrappers` are authenticated by pure **reconstruct-and-equate**:
///   replaying every wrapper (innermost-first) onto `body` must reproduce
///   `vc.formula` *structurally, bit-for-bit* (including `#token` version stamps).
///   Any wrapper spelling outside the closed vocabulary, or any rename mismatch,
///   makes reconstruction diverge from `formula` and the consumer DECLINES —
///   fail-closed, costing certificates but never soundness.
/// * `subject` / `width`, where the kind implies them, are authenticated against
///   the function's MIR (the type that DEFINES the width), not against a literal
///   inside `body` — the [10]-class width-forgery guard.
///
/// The emitter records these from what it is already building at the point it
/// KNOWS them (the raw violation, the negated operand, `ty.int_width()`), never by
/// re-parsing the finished formula.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObligationRecord {
    /// The raw violation predicate — the SAME versioning that appears inside
    /// `formula`. Replaying `wrappers` onto this must reproduce `formula`.
    pub body: Formula,
    /// The wrappers the emitter applied to `body`, innermost-first. Replaying them
    /// in order onto `body` reconstructs `formula`.
    pub wrappers: Vec<ObligationWrapper>,
    /// The negated/shifted operand, where the kind implies one (negation, shift);
    /// cross-checked against MIR at consumption. `None` for div/rem (payload-free).
    #[serde(default)]
    pub subject: Option<Formula>,
    /// The TRUE UB width the certificate is about, where the kind implies one;
    /// cross-checked against the MIR type width at consumption, NOT against `body`.
    /// `None` for div/rem (payload-free).
    #[serde(default)]
    pub width: Option<u32>,
}

/// Trust: the CLOSED vocabulary of wrappers a safety emitter applies to a raw
/// violation body. There are exactly two shapes, and that is the point: every
/// conjoining site pushes the body LAST (one shape), and the sole non-conjoining
/// wrapper is the dominating path-guard map (the other shape). There is deliberately
/// **no** `Implies`, **no** `Not`, and **no** free-disjunct variant — that omission
/// is what structurally closes the `Implies(Not(decoy), core)` twin and the mixed
/// `Or([core, decoy])` decoy: no sequence of these wrappers can reconstruct such a
/// spelling, so reconstruct-and-equate DECLINES it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ObligationWrapper {
    /// `inner ↦ And([facts.., inner])` — the body is conjoined LAST. Reproduces
    /// every block-def / guard-fact / precondition / semantic-guard conjoin site.
    ConjoinFactsLast { facts: Vec<Formula> },
    /// `inner ↦ Or([per-path term..])` — the dominating path-guard map. Each term is
    /// `Raw` (`inner` whole) or `Guarded { guards }` (`And([guards.., <inner spliced
    /// flat>])`). Collapses to the single term when there is one path, and to `inner`
    /// when there are none — mirroring `v2_formula_with_path_guards`.
    PathGuardOr { paths: Vec<PathGuardTerm> },
}

/// Trust: one path term of a [`ObligationWrapper::PathGuardOr`]. `Raw` carries the
/// body whole (an unguarded path); `Guarded` conjoins the (already version-renamed)
/// path guards and splices the body flat (mirroring the `And`-flatten in
/// `v2_formula_with_path_guards`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum PathGuardTerm {
    Raw,
    Guarded { guards: Vec<Formula> },
}

/// Trust: #178 Ownership metadata extracted from VCs for trust-vc-enriched encoding.
///
/// Carries region identifiers, borrow relationships, lifetime outlives relations,
/// and provenance tracking flags. Used by the trust_vc backend to generate
/// ownership axioms (region non-aliasing, Stacked Borrows permissions, borrow
/// validity constraints) instead of plain SMT-LIB2.
///
/// Not stored on VerificationCondition directly (that would break 477+ existing
/// construction sites). Instead, trust_vc extracts this from VcKind::Assertion
/// messages tagged with the `[memory:region]` prefix by region_encoding.rs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OwnershipMetadata {
    /// Region identifiers involved in this VC (e.g., "region_0", "region_1").
    pub regions: Vec<String>,
    /// Active borrow relationships (e.g., "region_1 borrows region_0").
    pub borrows: Vec<String>,
    /// Lifetime outlives relations (e.g., "'a: 'b" encoded as "a outlives b").
    #[serde(default)]
    pub lifetime_constraints: Vec<String>,
    /// Whether provenance tracking is needed (raw pointer casts, addr_of).
    #[serde(default)]
    pub has_provenance: bool,
}

impl OwnershipMetadata {
    /// Trust: Returns true if this metadata has any ownership-related content.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.regions.is_empty() && self.borrows.is_empty() && self.lifetime_constraints.is_empty()
    }
}

#[cfg(test)]
mod obligation_field_backward_compat_tests {
    use super::*;
    use crate::Sort;

    // A legacy VC dump minted BEFORE the `obligation` field existed: it carries no
    // `obligation` key. `#[serde(default)]` must deserialize it as `None` — the
    // backward-compat guarantee every one of the committed fixture dumps relies on.
    // Falsified by removing `#[serde(default)]` on the field (deserialization then
    // errors on the missing key).
    #[test]
    fn legacy_vc_json_without_obligation_deserializes_as_none() {
        // A pre-`obligation` dump is EXACTLY a current dump with the `obligation` key
        // removed. Build one that way (so every OTHER field — SourceSpan shape, etc. —
        // is authentic) and prove `#[serde(default)]` fills it as None rather than
        // erroring on the missing key. Falsified by dropping `#[serde(default)]`.
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: crate::Symbol::intern("my_crate::div"),
            location: crate::model::SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("d".into(), crate::Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };
        let mut value: serde_json::Value = serde_json::to_value(&vc).unwrap();
        assert!(value.as_object_mut().unwrap().remove("obligation").is_some());
        let legacy = serde_json::to_string(&value).unwrap();

        let back: VerificationCondition =
            serde_json::from_str(&legacy).expect("legacy VC dump (no obligation key) must deserialize");
        assert!(back.obligation.is_none(), "missing obligation must default to None, not error");

        // Same guarantee for the persistence-boundary twin.
        let svc: SerializableVc =
            serde_json::from_str(&legacy).expect("legacy SerializableVc dump must deserialize");
        assert!(svc.obligation.is_none());
    }

    // A populated obligation survives a serialize -> deserialize round-trip, and
    // rides through the `from_vc`/`into_vc` conversion instead of being dropped at
    // the serde boundary. Falsified by omitting `obligation` from either conversion.
    #[test]
    fn populated_obligation_roundtrips_and_threads_through_conversions() {
        let body = Formula::Eq(
            Box::new(Formula::Var("d".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: crate::Symbol::intern("my_crate::div"),
            location: crate::model::SourceSpan::default(),
            formula: body.clone(),
            contract_metadata: None,
            obligation: Some(ObligationRecord {
                body: body.clone(),
                wrappers: vec![ObligationWrapper::ConjoinFactsLast {
                    facts: vec![Formula::Bool(true)],
                }],
                subject: None,
                width: None,
            }),
        };

        // JSON round-trip preserves the record.
        let text = serde_json::to_string(&vc).unwrap();
        let back: VerificationCondition = serde_json::from_str(&text).unwrap();
        assert_eq!(back.obligation, vc.obligation);

        // from_vc / into_vc must carry it, not drop it.
        let svc = SerializableVc::from_vc(&vc);
        assert_eq!(svc.obligation, vc.obligation);
        let vc2 = svc.into_vc();
        assert_eq!(vc2.obligation, vc.obligation);
    }
}
