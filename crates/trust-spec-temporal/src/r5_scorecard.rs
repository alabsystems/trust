// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//
//! D0 machine-checkable capability scorecard for the `trust_model!` /
//! `temporal_model!` compatibility macros.
//!
//! This module is the **gate for the staged `trust_model!` retirement (D0-D3)**.
//! It enumerates every capability the macro surface exposes and records, for
//! each, whether the landed Clean temporal `Model` lane already replaces it:
//!
//!   - [`CapabilityReplacementStatus::FullyReplaced`] — a live, routed
//!     replacement exists for the exercised subset (advisory deprecation may
//!     nudge users toward it);
//!   - [`CapabilityReplacementStatus::Partial`] — a replacement exists but does
//!     not yet cover the whole legacy domain;
//!   - [`CapabilityReplacementStatus::NotYet`] — no routed replacement exists.
//!
//! The scorecard drives the **warning-first (D0)** deprecation policy: a macro
//! surface emits its `#[deprecated]` nudge **only when every capability it
//! inherently exercises is `FullyReplaced`** — any exercised `Partial` *or*
//! `NotYet` capability suppresses the nudge. This is exactly the PRIME RULE:
//! never nudge a user off a capability whose replacement cannot reproduce the
//! macro's verdict for their model.
//!
//! Under this rule **both** compatibility macros now emit the nudge (owner
//! policy flip 2026-07-21): the bounded scalar-safety core is `FullyReplaced`.
//! The former gap — three Clean-only resource caps plus process-global
//! name-interner exhaustion — is closed mechanically and evidenced
//! end-to-end: the interner and its distinct-name/interned-name caps were
//! DELETED (the certification core is name-representation generic), the
//! expression-depth cap was widened to a 65_536-level decode-cost guard over
//! fully iterative walks (the model-item cap is likewise a 65_536-element
//! decode-cost-only guard), and five positive near-cap vectors — a 300-node
//! chain past the old depth cap, end-to-end deep-chain certifications
//! (including the pinned ty-transport ceiling), a 4_205-distinct-name model,
//! and 110 conversions crossing the old cumulative interner budget — pass
//! with kernel recheck, legacy byte parity, and fresh replay where certified
//! (the D1 evidence requirement). The residual ceilings are decode-cost/DoS
//! guards and the producer-side ty-certificate transport depth, which fail
//! closed (a decline, never false authority) and bound both lanes, so they
//! are not capability differences; identifier grammar is shared across lanes
//! and was never part of the gap. `temporal_model!`'s former
//! extra capability — automatic link-time model inventory — was deleted as
//! extraneous (owner ruling 2026-07-20): the live gates never trusted the
//! linked registry, so the item macro now expands to the constructor fn only
//! and no longer carries an inventory row.
//!
//! The scalar admission-domain / interner gaps closed, the two rows are
//! `FullyReplaced` (2026-07-21), the derived policy flips both macros to
//! warning, and the source-attribute cross-check requires the `#[deprecated]`
//! attribute on both proc-macro fns — the intended D1+ ratchet, now ENGAGED.
//!
//! The tests below assert the *current* status of each capability, so a future
//! regression that removes a replacement — or a macro change that grows a new,
//! unreplaced capability — flips the scorecard red before it can ship. The
//! scorecard is implementation status, never proof evidence.

use crate::r5_parity::R5TemporalParityBlocker;

/// Schema identifier for the serialized capability scorecard.
pub const R5_MACRO_CAPABILITY_SCORECARD_SCHEMA_V1: &str =
    "trust.r5-temporal-macro-capability-scorecard/v1";

/// The two public compatibility-macro surfaces whose deprecation is decided
/// independently, per the capabilities each one inherently exercises.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R5MacroSurface {
    /// Expression-position `trust_model! { Name { .. } }` — yields a `Model`.
    TrustModel,
    /// Item-position `temporal_model! { Name { .. } }` — yields a `Model`
    /// constructor fn (its former link-time inventory registration was deleted
    /// as extraneous, owner ruling 2026-07-20).
    TemporalModel,
}

impl R5MacroSurface {
    /// The public macro path this surface corresponds to, for source checks.
    pub const fn macro_name(self) -> &'static str {
        match self {
            R5MacroSurface::TrustModel => "trust_model",
            R5MacroSurface::TemporalModel => "temporal_model",
        }
    }
}

/// Replacement status of one macro-surface capability with respect to the
/// landed Clean temporal `Model` lane.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CapabilityReplacementStatus {
    /// A live, routed replacement exists for the exercised subset.
    FullyReplaced,
    /// A replacement exists but does not cover the whole legacy domain.
    Partial,
    /// No routed replacement exists yet.
    NotYet,
}

/// Stable identifiers for each enumerated capability.
///
/// The first group is expressible through the `trust_model!`/`temporal_model!`
/// grammar. The trailing group is *not* reachable from the macro grammar (the
/// macro hard-codes `fn_vars: vec![]` and has no temporal-operator syntax); per
/// the owner override of 2026-07-20 those rows track non-gating Model-ABI
/// ambitions (`R5_MODEL_ABI_AMBITION_BLOCKERS`) — they gate neither the
/// per-macro warning decision nor macro RETIREMENT, which is scoped to the
/// macro domain. They are kept as rows so the information is preserved.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R5MacroCapability {
    /// Bounded single-scalar-variable `□`-safety machine.
    ScalarSafetySingleVar,
    /// Bounded multi-scalar-variable `□`-safety machine.
    ScalarSafetyMultiVar,
    /// The `Buggy = 1` non-vacuity counterexample ratchet required for credit.
    BuggyNonVacuityRatchet,
    /// Integer expression grammar + guarded/unguarded actions + `□`-invariants.
    GuardedActionExprGrammar,
    /// Function-valued variables / access / update / comprehension (`Model` ABI
    /// only — not expressible through the macro grammar).
    FunctionValuedModelVars,
    /// `◇P` liveness under weak fairness (separate lane — not macro-reachable).
    LivenessWeakFairness,
    /// Arbitrary `F ~> G` leads-to discharge (not macro-reachable).
    ArbitraryLeadsTo,
}

/// One scorecard row: a capability, whether the macro grammar can express it,
/// which macro surfaces inherently exercise it, its replacement status, the
/// tracked `r5_parity` gaps (if any) that keep a specific model from fully
/// migrating, and a pointer at the live replacement (when one exists).
#[derive(Debug, Clone, Copy)]
pub struct R5CapabilityRow {
    /// Stable identifier.
    pub capability: R5MacroCapability,
    /// Human-readable summary.
    pub title: &'static str,
    /// Whether the `trust_model!`/`temporal_model!` grammar can express it.
    pub macro_expressible: bool,
    /// Macro surfaces that inherently exercise this capability. Empty for
    /// `Model`-ABI-only rows, which therefore never gate a macro's warning.
    pub surfaces: &'static [R5MacroSurface],
    /// Current replacement status.
    pub status: CapabilityReplacementStatus,
    /// Tracked migration gaps that apply to this capability (documentation +
    /// cross-check against `r5_parity`; never affects `status`).
    pub migration_blockers: &'static [R5TemporalParityBlocker],
    /// Where to migrate, when a live replacement exists.
    pub replacement: Option<&'static str>,
}

/// The canonical, machine-checkable capability scorecard.
///
/// Ordered: macro-expressible capabilities first (in the order a reader meets
/// them in the grammar), then the `Model`-ABI-only rows that document the
/// remaining non-gating Model-ABI ambitions.
pub const R5_MACRO_CAPABILITY_SCORECARD: &[R5CapabilityRow] = &[
    R5CapabilityRow {
        capability: R5MacroCapability::ScalarSafetySingleVar,
        title: "bounded single-scalar-variable safety machine (□ invariant over reachable states)",
        macro_expressible: true,
        surfaces: &[R5MacroSurface::TrustModel, R5MacroSurface::TemporalModel],
        // FULLY REPLACED (owner policy flip 2026-07-21): the Clean scalar lane
        // certifies byte-identically, and its formerly narrower admission
        // domain now covers the owner-ratified operational macro-parity
        // domain. Mechanically: the process-global name interner and its
        // MAX_MODEL_NAMES / MAX_INTERNED_NAMES caps are DELETED (the
        // certification core is name-representation generic and feeds
        // certify_model owned String-named models directly), and
        // MAX_EXPR_DEPTH was widened to 65_536 over fully iterative
        // expression walks. The D1 evidence requirement — "the bridge
        // admission domain is widened + an end-to-end CERTIFIED proof of a
        // near-cap model exists" — is met by five positive vectors pinned in
        // clean_model_lane's test module (fc4b8b1858): a 300-node add chain
        // past the old 256 depth cap (extract + convert + shared preflight +
        // legacy byte parity + replay), end-to-end deep-chain certifications
        // including the 55-node pinned ty-transport ceiling vector (opt-in
        // `#[ignore]`, ~640s in debug), a
        // 4_205-distinct-name model, and 110 conversions crossing the old
        // 16_384 cumulative interner budget — with kernel recheck and exact
        // configuration binding where certified. Residual ceilings
        // (MAX_MODEL_ITEMS / MAX_EXPR_DEPTH as 65_536 decode-cost/DoS guards;
        // the producer-side ty-certificate JSON transport depth, which
        // declines fail-closed past ~55 nodes) bound BOTH lanes and never
        // grant false authority, and are explicitly scoped as non-parity per
        // the owner rulings of 2026-07-20/21. Identifier grammar is NOT part
        // of the story: the legacy lane's certification preflight enforces
        // the same no-leading-underscore / name-length / reserved-token rules
        // (shared validate_model_for_certification — proven by the
        // legacy_lane_rejects_underscore_and_oversized_names_at_certification
        // differential test), and that stricter grammar is ratified as the
        // parity target itself per owner ruling 2026-07-20 —
        // valid_tla_identifier is the TLA+ anti-injection guard and will not
        // be relaxed — while the Clean lane's nonnegative (Nat) value domain
        // matches the macro DSL's own LitInt restriction.
        status: CapabilityReplacementStatus::FullyReplaced,
        migration_blockers: &[],
        replacement: Some(
            "author a temporal Model (or a `clean { … }` island) and certify with \
             certify_clean_scalar_model_with_ty (closed scalar lane)",
        ),
    },
    R5CapabilityRow {
        capability: R5MacroCapability::ScalarSafetyMultiVar,
        title: "bounded multi-scalar-variable safety machine (□ invariant, S4 finite keystone)",
        macro_expressible: true,
        surfaces: &[R5MacroSurface::TrustModel, R5MacroSurface::TemporalModel],
        // FULLY REPLACED for the same reasons as the single-var row above
        // (owner policy flip 2026-07-21; see its evidence note): the
        // caps/interner gap is closed mechanically and evidenced end-to-end,
        // and multi-var models route through the same admission surface to
        // the finite keystone. Identifier grammar and the Nat value domain
        // are the shared, ratified parity target, not gaps (owner ruling
        // 2026-07-20).
        status: CapabilityReplacementStatus::FullyReplaced,
        migration_blockers: &[],
        replacement: Some(
            "author a temporal Model (or a `clean { … }` island) and certify with \
             certify_clean_scalar_model_with_ty (routes >1 var to the finite keystone)",
        ),
    },
    R5CapabilityRow {
        capability: R5MacroCapability::BuggyNonVacuityRatchet,
        title: "Buggy = 1 non-vacuity counterexample ratchet (mandatory for Certified credit)",
        macro_expressible: true,
        surfaces: &[R5MacroSurface::TrustModel, R5MacroSurface::TemporalModel],
        status: CapabilityReplacementStatus::FullyReplaced,
        migration_blockers: &[],
        replacement: Some(
            "preserved identically: certify_model downgrades a dial-less model to \
             ModelVerdict::Unknown in both the macro and Clean lanes",
        ),
    },
    R5CapabilityRow {
        capability: R5MacroCapability::GuardedActionExprGrammar,
        title: "integer expression grammar + guarded/unguarded actions + □-invariants",
        macro_expressible: true,
        surfaces: &[R5MacroSurface::TrustModel, R5MacroSurface::TemporalModel],
        status: CapabilityReplacementStatus::FullyReplaced,
        migration_blockers: &[],
        replacement: Some(
            "the Clean ScalarModel authoring surface emits byte-identical TLA+/config \
             for the same guarded-action grammar",
        ),
    },
    R5CapabilityRow {
        capability: R5MacroCapability::FunctionValuedModelVars,
        title: "function-valued variables / access / update / comprehension (Model ABI only)",
        macro_expressible: false,
        surfaces: &[],
        status: CapabilityReplacementStatus::NotYet,
        migration_blockers: &[R5TemporalParityBlocker::FunctionValuedModelReplacementMissing],
        replacement: None,
    },
    R5CapabilityRow {
        capability: R5MacroCapability::LivenessWeakFairness,
        title: "◇P liveness under weak fairness (separate certify_liveness_with_ty lane)",
        macro_expressible: false,
        surfaces: &[],
        status: CapabilityReplacementStatus::Partial,
        migration_blockers: &[],
        replacement: Some(
            "selected recognized classes are certified by certify_liveness_with_ty; \
             not reachable from the macro grammar",
        ),
    },
    R5CapabilityRow {
        capability: R5MacroCapability::ArbitraryLeadsTo,
        title: "arbitrary F ~> G leads-to discharge with general fairness (Model/temporal ABI)",
        macro_expressible: false,
        surfaces: &[],
        status: CapabilityReplacementStatus::NotYet,
        migration_blockers: &[R5TemporalParityBlocker::ArbitraryLeadsToDischargeMissing],
        replacement: None,
    },
];

/// Look up one capability row.
pub fn capability_row(capability: R5MacroCapability) -> &'static R5CapabilityRow {
    R5_MACRO_CAPABILITY_SCORECARD
        .iter()
        .find(|row| row.capability == capability)
        .expect("every capability has exactly one scorecard row")
}

/// D0 warning-first policy: a macro surface emits its advisory `#[deprecated]`
/// nudge **only when every capability it inherently exercises is
/// `FullyReplaced`**. Any exercised capability that is `Partial` or `NotYet`
/// suppresses the nudge, so we never point users away from a capability whose
/// replacement is not fully live (the PRIME RULE).
pub fn macro_surface_emits_deprecation(surface: R5MacroSurface) -> bool {
    let exercised = R5_MACRO_CAPABILITY_SCORECARD
        .iter()
        .filter(|row| row.surfaces.contains(&surface))
        .collect::<Vec<_>>();
    // A surface with no capability at all would vacuously "warn"; every real
    // surface exercises at least the scalar-safety core, but guard anyway.
    !exercised.is_empty()
        && exercised.iter().all(|row| row.status == CapabilityReplacementStatus::FullyReplaced)
}

/// Owned, serializable mirror of one [`R5CapabilityRow`].
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct R5MacroCapabilityRecord {
    pub capability: R5MacroCapability,
    pub title: String,
    pub macro_expressible: bool,
    pub surfaces: Vec<R5MacroSurface>,
    pub status: CapabilityReplacementStatus,
    pub migration_blockers: Vec<R5TemporalParityBlocker>,
    pub replacement: Option<String>,
}

impl From<&R5CapabilityRow> for R5MacroCapabilityRecord {
    fn from(row: &R5CapabilityRow) -> Self {
        Self {
            capability: row.capability,
            title: row.title.to_owned(),
            macro_expressible: row.macro_expressible,
            surfaces: row.surfaces.to_vec(),
            status: row.status,
            migration_blockers: row.migration_blockers.to_vec(),
            replacement: row.replacement.map(str::to_owned),
        }
    }
}

/// Public, serializable snapshot of the whole capability scorecard plus the
/// derived per-macro warning decisions.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct R5MacroCapabilityScorecard {
    /// Versioned schema.
    pub schema: String,
    /// Every enumerated capability, in canonical order.
    pub capabilities: Vec<R5MacroCapabilityRecord>,
    /// Whether `trust_model!` emits its advisory deprecation nudge.
    pub trust_model_emits_deprecation: bool,
    /// Whether `temporal_model!` emits its advisory deprecation nudge.
    pub temporal_model_emits_deprecation: bool,
}

/// Errors returned when validating a serialized scorecard.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum R5MacroCapabilityScorecardError {
    SchemaMismatch { found: String },
    CapabilitiesMismatch,
    WarningDecisionMismatch { surface: R5MacroSurface },
}

impl std::fmt::Display for R5MacroCapabilityScorecardError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SchemaMismatch { found } => {
                write!(formatter, "unsupported R5 macro capability scorecard schema `{found}`")
            }
            Self::CapabilitiesMismatch => formatter.write_str(
                "scorecard capabilities do not match the current implementation snapshot",
            ),
            Self::WarningDecisionMismatch { surface } => write!(
                formatter,
                "scorecard warning decision for `{}!` contradicts its capabilities",
                surface.macro_name()
            ),
        }
    }
}

impl std::error::Error for R5MacroCapabilityScorecardError {}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct R5MacroCapabilityScorecardWire {
    schema: String,
    capabilities: Vec<R5MacroCapabilityRecord>,
    trust_model_emits_deprecation: bool,
    temporal_model_emits_deprecation: bool,
}

impl R5MacroCapabilityScorecard {
    /// Validate the schema, capability set, and derived warning decisions
    /// against the current in-tree implementation snapshot.
    pub fn validate(&self) -> Result<(), R5MacroCapabilityScorecardError> {
        if self.schema != R5_MACRO_CAPABILITY_SCORECARD_SCHEMA_V1 {
            return Err(R5MacroCapabilityScorecardError::SchemaMismatch {
                found: self.schema.clone(),
            });
        }
        let canonical = R5_MACRO_CAPABILITY_SCORECARD
            .iter()
            .map(R5MacroCapabilityRecord::from)
            .collect::<Vec<_>>();
        if self.capabilities != canonical {
            return Err(R5MacroCapabilityScorecardError::CapabilitiesMismatch);
        }
        for (surface, decision) in [
            (R5MacroSurface::TrustModel, self.trust_model_emits_deprecation),
            (R5MacroSurface::TemporalModel, self.temporal_model_emits_deprecation),
        ] {
            if decision != macro_surface_emits_deprecation(surface) {
                return Err(R5MacroCapabilityScorecardError::WarningDecisionMismatch { surface });
            }
        }
        Ok(())
    }
}

impl<'de> serde::Deserialize<'de> for R5MacroCapabilityScorecard {
    fn deserialize<Deserializer>(deserializer: Deserializer) -> Result<Self, Deserializer::Error>
    where
        Deserializer: serde::Deserializer<'de>,
    {
        let wire =
            <R5MacroCapabilityScorecardWire as serde::Deserialize>::deserialize(deserializer)?;
        let scorecard = Self {
            schema: wire.schema,
            capabilities: wire.capabilities,
            trust_model_emits_deprecation: wire.trust_model_emits_deprecation,
            temporal_model_emits_deprecation: wire.temporal_model_emits_deprecation,
        };
        scorecard.validate().map_err(serde::de::Error::custom)?;
        Ok(scorecard)
    }
}

/// Return the current public capability scorecard.
pub fn r5_macro_capability_scorecard() -> R5MacroCapabilityScorecard {
    let scorecard = R5MacroCapabilityScorecard {
        schema: R5_MACRO_CAPABILITY_SCORECARD_SCHEMA_V1.to_owned(),
        capabilities: R5_MACRO_CAPABILITY_SCORECARD
            .iter()
            .map(R5MacroCapabilityRecord::from)
            .collect(),
        trust_model_emits_deprecation: macro_surface_emits_deprecation(R5MacroSurface::TrustModel),
        temporal_model_emits_deprecation: macro_surface_emits_deprecation(
            R5MacroSurface::TemporalModel,
        ),
    };
    debug_assert_eq!(scorecard.validate(), Ok(()));
    scorecard
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r5_parity::{
        R5_MODEL_ABI_AMBITION_BLOCKERS, R5_TEMPORAL_PARITY_BLOCKERS,
        R5_TEMPORAL_RETIREMENT_BLOCKERS,
    };

    const MACRO_IMPLEMENTATION_SOURCE: &str =
        include_str!("../../trust-spec-temporal-macros/src/lib.rs");

    fn row(capability: R5MacroCapability) -> &'static R5CapabilityRow {
        capability_row(capability)
    }

    #[test]
    fn every_capability_has_exactly_one_row_in_canonical_order() {
        use R5MacroCapability::*;
        let expected = [
            ScalarSafetySingleVar,
            ScalarSafetyMultiVar,
            BuggyNonVacuityRatchet,
            GuardedActionExprGrammar,
            FunctionValuedModelVars,
            LivenessWeakFairness,
            ArbitraryLeadsTo,
        ];
        let actual = R5_MACRO_CAPABILITY_SCORECARD.iter().map(|r| r.capability).collect::<Vec<_>>();
        assert_eq!(actual, expected, "scorecard rows must stay stable and complete");
    }

    /// THE regression gate: the exact replacement status of each capability. A
    /// future change that removes a replacement, or grows a new unreplaced macro
    /// capability, must fail here before it can ship.
    #[test]
    fn each_capability_has_its_current_replacement_status() {
        use CapabilityReplacementStatus::*;
        use R5MacroCapability::*;
        // The two macro scalar-safety rows are FullyReplaced (owner policy
        // flip 2026-07-21): the interner + name caps are deleted, the depth
        // cap is a decode-cost guard, and near-cap vectors certify end-to-end.
        assert_eq!(row(ScalarSafetySingleVar).status, FullyReplaced);
        assert_eq!(row(ScalarSafetyMultiVar).status, FullyReplaced);
        assert_eq!(row(BuggyNonVacuityRatchet).status, FullyReplaced);
        assert_eq!(row(GuardedActionExprGrammar).status, FullyReplaced);
        // The two Model-ABI-only NotYet rows below stay NotYet but no longer
        // gate macro retirement (owner override 2026-07-20): they reference the
        // non-gating R5_MODEL_ABI_AMBITION_BLOCKERS tracker.
        assert_eq!(row(FunctionValuedModelVars).status, NotYet);
        assert_eq!(row(LivenessWeakFairness).status, Partial);
        assert_eq!(row(ArbitraryLeadsTo).status, NotYet);
    }

    #[test]
    fn fully_replaced_capabilities_point_at_a_live_replacement() {
        for row in R5_MACRO_CAPABILITY_SCORECARD {
            if row.status == CapabilityReplacementStatus::FullyReplaced {
                assert!(
                    row.replacement.is_some(),
                    "{:?} is FullyReplaced but names no replacement",
                    row.capability
                );
            }
        }
    }

    /// A `NotYet` row must name no replacement and track its gap. WHERE the gap
    /// is tracked follows the owner override of 2026-07-20: a row exercised by a
    /// macro surface must reference a RETIREMENT blocker (it gates deleting the
    /// macros), while a Model-ABI-only row (empty `surfaces`, not
    /// macro-expressible) must reference the non-gating ambition tracker — a
    /// capability the macros cannot express cannot gate macro deletion.
    #[test]
    fn not_yet_capabilities_have_no_replacement_and_track_their_owner_scoped_gap() {
        for row in R5_MACRO_CAPABILITY_SCORECARD {
            if row.status == CapabilityReplacementStatus::NotYet {
                assert!(
                    row.replacement.is_none(),
                    "{:?} is NotYet but claims a replacement",
                    row.capability
                );
                assert!(
                    !row.migration_blockers.is_empty(),
                    "{:?} is NotYet but tracks no blocker",
                    row.capability
                );
                for blocker in row.migration_blockers {
                    if row.surfaces.is_empty() {
                        assert!(
                            R5_MODEL_ABI_AMBITION_BLOCKERS.contains(blocker),
                            "{:?} is Model-ABI-only and must reference the non-gating \
                             ambition tracker, not a gating blocker; found {blocker:?}",
                            row.capability
                        );
                    } else {
                        assert!(
                            R5_TEMPORAL_RETIREMENT_BLOCKERS.contains(blocker),
                            "{:?} references untracked blocker {blocker:?}",
                            row.capability
                        );
                    }
                }
            }
        }
    }

    /// Classification-honesty guard, symmetric to the `NotYet` guard above: a
    /// `FullyReplaced` row must carry **no** open migration blocker. A blocker is
    /// exactly "the replacement does not cover this part of the legacy domain",
    /// which is the definition of `Partial` — so a `FullyReplaced` row that still
    /// tracks a blocker is mislabelled and would silently drive a deprecation
    /// nudge onto an unreplaced case (the loophole this D0 fix closes).
    #[test]
    fn fully_replaced_capabilities_track_no_open_blocker() {
        for row in R5_MACRO_CAPABILITY_SCORECARD {
            if row.status == CapabilityReplacementStatus::FullyReplaced {
                assert!(
                    row.migration_blockers.is_empty(),
                    "{:?} is FullyReplaced but still tracks migration blockers {:?}; \
                     a replacement with an open domain gap is Partial, not FullyReplaced",
                    row.capability,
                    row.migration_blockers,
                );
            }
        }
    }

    /// The `Partial` invariant: a partial replacement, by definition, both exists
    /// (names a replacement to author toward) and has at least one tracked gap.
    #[test]
    fn partial_capabilities_name_a_replacement_and_track_a_blocker() {
        for row in R5_MACRO_CAPABILITY_SCORECARD {
            if row.status == CapabilityReplacementStatus::Partial {
                assert!(
                    row.replacement.is_some(),
                    "{:?} is Partial but names no replacement to migrate toward",
                    row.capability,
                );
                // The macro-exercised scalar rows document their exact gap; the
                // Model-ABI-only liveness row is a recognized-class partial with
                // no macro-migration blocker to track, so only require a tracked
                // blocker when the row gates a macro surface.
                if !row.surfaces.is_empty() {
                    assert!(
                        !row.migration_blockers.is_empty(),
                        "{:?} is a Partial macro capability but tracks no gap blocker",
                        row.capability,
                    );
                }
            }
        }
    }

    /// The deleted-inventory ratchet: `temporal_model!` and `trust_model!` now
    /// exercise exactly the same capability rows — the item macro carries no
    /// extra (inventory) capability, so no row may reintroduce one silently.
    #[test]
    fn both_macro_surfaces_exercise_the_same_capability_rows() {
        let exercised = |surface: R5MacroSurface| {
            R5_MACRO_CAPABILITY_SCORECARD
                .iter()
                .filter(|row| row.surfaces.contains(&surface))
                .map(|row| row.capability)
                .collect::<Vec<_>>()
        };
        assert_eq!(exercised(R5MacroSurface::TrustModel), exercised(R5MacroSurface::TemporalModel));
    }

    #[test]
    fn model_abi_only_capabilities_belong_to_no_macro_surface() {
        use R5MacroCapability::*;
        for capability in [FunctionValuedModelVars, LivenessWeakFairness, ArbitraryLeadsTo] {
            let row = row(capability);
            assert!(!row.macro_expressible, "{capability:?} is not macro-expressible");
            assert!(
                row.surfaces.is_empty(),
                "{capability:?} must gate the Model ABI, not the macro warning surface",
            );
        }
    }

    /// The core D1+ outcome (owner policy flip 2026-07-21): BOTH macros warn.
    /// Every capability either macro exercises is `FullyReplaced`, so per the
    /// PRIME RULE the advisory nudge fires — it points users at a replacement
    /// that reproduces the macro's verdict for their model.
    #[test]
    fn derived_per_macro_warning_policy_is_content_correct() {
        assert!(
            macro_surface_emits_deprecation(R5MacroSurface::TrustModel),
            "trust_model!'s exercised capabilities are all FullyReplaced (2026-07-21 \
             flip), so the advisory nudge must fire",
        );
        assert!(
            macro_surface_emits_deprecation(R5MacroSurface::TemporalModel),
            "temporal_model! exercises the same FullyReplaced capability set and must warn",
        );
    }

    /// The PRIME RULE, phrased over the scorecard at the honest granularity: a
    /// warned macro surface may exercise **only** `FullyReplaced` capabilities.
    /// A `Partial` capability (a documented, tracked non-parity that the
    /// replacement cannot fully reproduce) suppresses the nudge just as a
    /// `NotYet` one does — this is the granularity fix at the heart of D0.
    #[test]
    fn no_warned_surface_nudges_off_an_unreplaced_capability() {
        for surface in [R5MacroSurface::TrustModel, R5MacroSurface::TemporalModel] {
            if macro_surface_emits_deprecation(surface) {
                for row in R5_MACRO_CAPABILITY_SCORECARD {
                    if row.surfaces.contains(&surface) {
                        assert_eq!(
                            row.status,
                            CapabilityReplacementStatus::FullyReplaced,
                            "warned surface {surface:?} nudges off not-fully-replaced {:?} \
                             (status {:?})",
                            row.capability,
                            row.status,
                        );
                    }
                }
            }
        }
    }

    /// Tie the derived policy to the actual proc-macro source: a surface warns
    /// iff its `#[proc_macro]` fn carries `#[deprecated(`.
    #[test]
    fn warning_policy_matches_the_proc_macro_source_attributes() {
        fn has_deprecation_attribute(function: &str) -> bool {
            let marker = format!("pub fn {function}");
            let function_offset = MACRO_IMPLEMENTATION_SOURCE
                .find(&marker)
                .unwrap_or_else(|| panic!("missing proc-macro function `{function}`"));
            let prefix = &MACRO_IMPLEMENTATION_SOURCE[..function_offset];
            let proc_macro_offset = prefix
                .rfind("#[proc_macro]")
                .unwrap_or_else(|| panic!("missing #[proc_macro] before `{function}`"));
            prefix[proc_macro_offset..].contains("#[deprecated(")
        }

        for surface in [R5MacroSurface::TrustModel, R5MacroSurface::TemporalModel] {
            assert_eq!(
                has_deprecation_attribute(surface.macro_name()),
                macro_surface_emits_deprecation(surface),
                "`{}!` deprecation attribute must match the scorecard-derived policy",
                surface.macro_name(),
            );
        }
    }

    /// `trust_model!` carries the per-use `#[deprecated]` nudge (owner policy
    /// flip 2026-07-21) AND its documentation still points users at the live
    /// Clean replacement as forward-authoring guidance (temporal Model +
    /// `clean { … }` island + certifier) — the migration signposting survives
    /// in both channels.
    #[test]
    fn macro_docs_point_at_the_replacement_and_the_nudge_fires() {
        // Guidance is preserved in prose ...
        assert!(
            MACRO_IMPLEMENTATION_SOURCE.contains("certify_clean_scalar_model_with_ty"),
            "macro docs must name the certifier as the forward-authoring path",
        );
        assert!(
            MACRO_IMPLEMENTATION_SOURCE.contains("clean {"),
            "macro docs must point at the clean {{ … }} island surface",
        );
        // ... and the per-use `#[deprecated]` nudge fires now that the scalar
        // core is FullyReplaced.
        assert!(
            macro_surface_emits_deprecation(R5MacroSurface::TrustModel),
            "trust_model! must carry the advisory nudge now that its core is FullyReplaced",
        );
    }

    /// Cross-check with `r5_parity`: the migration gaps recorded against the
    /// macro-exercised capabilities are exactly the advisory-migration blocker
    /// set. A regression in either file breaks this.
    #[test]
    fn macro_migration_blockers_match_r5_parity() {
        let mut from_scorecard = R5_MACRO_CAPABILITY_SCORECARD
            .iter()
            .filter(|row| !row.surfaces.is_empty())
            .flat_map(|row| row.migration_blockers.iter().copied())
            .collect::<Vec<_>>();
        from_scorecard.sort();
        from_scorecard.dedup();

        let mut expected = R5_TEMPORAL_PARITY_BLOCKERS.to_vec();
        expected.sort();
        expected.dedup();

        assert_eq!(
            from_scorecard, expected,
            "scorecard macro-migration gaps must equal R5_TEMPORAL_PARITY_BLOCKERS",
        );
    }

    #[test]
    fn scorecard_serializes_with_derived_decisions() {
        let value = serde_json::to_value(r5_macro_capability_scorecard()).expect("serializes");
        assert_eq!(value["schema"], R5_MACRO_CAPABILITY_SCORECARD_SCHEMA_V1);
        // Both macros warn since the 2026-07-21 policy flip.
        assert_eq!(value["trust_model_emits_deprecation"], true);
        assert_eq!(value["temporal_model_emits_deprecation"], true);
        assert_eq!(value["capabilities"].as_array().expect("array").len(), 7);
        assert_eq!(value["capabilities"][0]["capability"], "scalar_safety_single_var");
        assert_eq!(value["capabilities"][0]["status"], "fully_replaced");
        assert_eq!(value["capabilities"][4]["capability"], "function_valued_model_vars");
        assert_eq!(value["capabilities"][4]["status"], "not_yet");
    }

    #[test]
    fn scorecard_round_trips_and_rejects_tampering() {
        let baseline = serde_json::to_value(r5_macro_capability_scorecard()).unwrap();
        let round_trip: R5MacroCapabilityScorecard =
            serde_json::from_value(baseline.clone()).expect("round-trips");
        assert_eq!(round_trip, r5_macro_capability_scorecard());

        // Wrong schema is rejected.
        let mut wrong_schema = baseline.clone();
        wrong_schema["schema"] =
            serde_json::json!("trust.r5-temporal-macro-capability-scorecard/v0");
        assert!(serde_json::from_value::<R5MacroCapabilityScorecard>(wrong_schema).is_err());

        // A forged "temporal_model does not warn" decision is rejected: the
        // derived decision is true since the 2026-07-21 flip.
        let mut forged_temporal = baseline.clone();
        forged_temporal["temporal_model_emits_deprecation"] = serde_json::json!(false);
        assert!(serde_json::from_value::<R5MacroCapabilityScorecard>(forged_temporal).is_err());

        // A forged "trust_model does not warn" decision is rejected too.
        let mut forged_trust = baseline.clone();
        forged_trust["trust_model_emits_deprecation"] = serde_json::json!(false);
        assert!(serde_json::from_value::<R5MacroCapabilityScorecard>(forged_trust).is_err());

        // Flipping a capability's status away from the snapshot is rejected.
        let mut forged_status = baseline.clone();
        forged_status["capabilities"][4]["status"] = serde_json::json!("fully_replaced");
        assert!(serde_json::from_value::<R5MacroCapabilityScorecard>(forged_status).is_err());

        // Re-labelling the FullyReplaced scalar core back to Partial (silently
        // reopening the closed gap) is rejected against the snapshot.
        let mut forged_scalar = baseline.clone();
        forged_scalar["capabilities"][0]["status"] = serde_json::json!("partial");
        assert!(serde_json::from_value::<R5MacroCapabilityScorecard>(forged_scalar).is_err());
    }

    #[test]
    fn validate_reports_specific_errors() {
        let mut bad_schema = r5_macro_capability_scorecard();
        bad_schema.schema = "nope".to_owned();
        assert_eq!(
            bad_schema.validate(),
            Err(R5MacroCapabilityScorecardError::SchemaMismatch { found: "nope".to_owned() }),
        );

        let mut bad_decision = r5_macro_capability_scorecard();
        // Since the 2026-07-21 flip the derived decision is TRUE, so the
        // contradictory forgery is now false.
        bad_decision.temporal_model_emits_deprecation = false;
        assert_eq!(
            bad_decision.validate(),
            Err(R5MacroCapabilityScorecardError::WarningDecisionMismatch {
                surface: R5MacroSurface::TemporalModel,
            }),
        );

        let mut bad_caps = r5_macro_capability_scorecard();
        bad_caps.capabilities.pop();
        assert_eq!(bad_caps.validate(), Err(R5MacroCapabilityScorecardError::CapabilitiesMismatch),);
    }
}
