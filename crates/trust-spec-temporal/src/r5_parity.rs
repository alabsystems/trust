//! Machine-readable R5 migration and macro-retirement gates.
//!
//! These are deliberately separate decisions.  The Clean scalar lane is a
//! byte-for-byte replacement for the bounded scalar subset it *admits*, so
//! advisory migration guidance may point users at that live path in prose.
//! Whether the per-use `#[deprecated]` attribute actually fires is a finer,
//! per-capability decision owned by `r5_scorecard` (a surface warns only when
//! every capability it exercises is `FullyReplaced`).  Macro-domain migration
//! parity is CLOSED (owner policy flip 2026-07-21): the process-global legacy
//! interner and its distinct-name/interned-name caps were deleted, the
//! expression-depth cap was widened to a 65_536-level decode-cost guard over
//! fully iterative walks, and positive near-cap vectors passed (past-old-cap
//! conversion with byte parity + replay; end-to-end certification up to the
//! pinned ty-transport ceiling, at 4_205 names, and across 110
//! interner-budget-crossing conversions) —
//! the scalar capability is `FullyReplaced`, so both macros now carry the
//! advisory `#[deprecated]` attribute (the D1+ ratchet, engaged).  The item
//! macro's automatic link-time inventory
//! was deleted as extraneous (owner ruling 2026-07-20, "no deprecation
//! limbo") — the live gates never trusted the linked registry, callers own
//! their explicit definition list, and the former
//! `AutomaticModelInventoryReplacementMissing` gap is historical-only.
//! Identifier grammar is NOT among the gaps: both
//! lanes share the same certification preflight, and that stricter grammar is
//! the ratified parity target (owner ruling 2026-07-20).
//! Malformed values that the permissive macro parser happened to construct are
//! rejected after Clean parsing/elaboration and value decoding but before
//! TLA+/ty lowering; accepting them is not parity.
//! Macro retirement is gated on the MACRO domain only (owner override,
//! 2026-07-20, "no deprecation limbo"): the earlier in-tree "stronger target"
//! also held retirement hostage to function-valued model vocabulary and
//! arbitrary `~>` discharge, but the macros provably cannot express either
//! (`macro_expressible: false`, empty surfaces, guard-test-pinned in
//! `r5_scorecard`), so those Model-ABI ambitions cannot gate deleting the
//! macros.  They are now tracked, non-gating, in
//! [`R5_MODEL_ABI_AMBITION_BLOCKERS`].  The applied Clean proposition bridge
//! remains a retirement blocker pending a separate owner decision.  This
//! report is implementation status, never proof evidence.

/// Legacy schema identifier retained so stored v1 reports can still be named.
///
/// V1 overloaded `status` and `blockers` between advisory deprecation and final
/// macro retirement.  New reports are always emitted as V2 and do not reproduce
/// those ambiguous fields.
pub const R5_TEMPORAL_PARITY_REPORT_SCHEMA_V1: &str = "trust.r5-temporal-parity/v1";

/// Current schema identifier for the public R5 temporal migration report.
pub const R5_TEMPORAL_PARITY_REPORT_SCHEMA_V2: &str = "trust.r5-temporal-parity/v2";

/// Stable R5 gap identifiers.
///
/// Some variants describe already-closed historical gaps so their stable
/// blocker IDs remain deserializable.  The V2 report shape intentionally does
/// not deserialize the old, ambiguous V1 object shape.  A gap is active only
/// when it appears in one of the public blocker constants below.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R5TemporalParityBlocker {
    /// Historical blocker ID: no router elaborated an authored Clean temporal
    /// proposition into the exact semantic input passed to `ty certify`.
    CleanPropositionNotRoutedToTyCertify,
    /// Historical blocker ID: the ty certificate was not bound to its authored
    /// Clean theorem statement.
    TyCertificateNotBoundToCleanProposition,
    /// Historical coarse ID for incomplete certified temporal property classes.
    CertifiedTemporalPropertyClassesIncomplete,
    /// `Init` and `Next` still come from a hand-written macro model, with no
    /// kernel-checked refinement from the literal program transition system.
    LiteralProgramTransitionRefinementMissing,
    /// No trustc-authenticated manifest binds semantic inputs, checker and output
    /// identity, and the final program artifact into one evidence chain.
    AuthenticatedCompilerEvidenceMissing,
    /// Historical blocker ID: production certificates lacked an exact
    /// kernel-closed route for their actual explicit-fixpoint evidence.
    ProductionExactKernelClosedCertificateMissing,
    /// Historical blocker ID: no Clean replacement preserved and bound the
    /// macro lane's `Buggy = 1` counterexample ratchet.
    CleanReplacementBuggyOneRatchetMissing,
    /// The legacy `Model` union also supports function-valued variables and
    /// function access/update/comprehension expressions; the Clean v1 model
    /// decoder is deliberately scalar-only.  Not macro-expressible, so it does
    /// not gate macro retirement (owner override 2026-07-20); tracked in
    /// [`R5_MODEL_ABI_AMBITION_BLOCKERS`].
    FunctionValuedModelReplacementMissing,
    /// The decoded scalar data model is not yet accompanied by a kernel theorem
    /// tying it to the exact applied Clean `StateMachine` proposition.
    AppliedCleanPropositionBindingMissing,
    /// Certified liveness handles selected recognized classes, not an arbitrary
    /// authored `F ~> G` proposition with general fairness assumptions.  Not
    /// macro-expressible, so it does not gate macro retirement (owner override
    /// 2026-07-20); tracked in [`R5_MODEL_ABI_AMBITION_BLOCKERS`].
    ArbitraryLeadsToDischargeMissing,
    /// Historical blocker ID (closed by the owner policy flip 2026-07-21).
    /// The Clean scalar decoder used to impose three Clean-only resource caps
    /// the legacy macro/certifier did not share: `MAX_EXPR_DEPTH` (expression
    /// nesting), `MAX_MODEL_NAMES` (distinct names per model), and
    /// `MAX_INTERNED_NAMES` (total interner occupancy).  The two name caps
    /// were deleted with the process-global interner (2026-07-20), and
    /// `MAX_EXPR_DEPTH` was widened to 65_536 over fully iterative expression
    /// walks — surviving, like `MAX_MODEL_ITEMS` (65_536), purely as a
    /// decode-cost (DoS) guard: the macro lane's implicit bound is
    /// compile-time source size, so neither is a practical parity gap.  The
    /// D1 evidence requirement is met by positive near-cap vectors
    /// (2026-07-20): past-old-cap conversion with legacy byte parity and
    /// replay, end-to-end certification up to the pinned ty-transport
    /// ceiling, a 4_205-name model, and 110 interner-budget-crossing
    /// conversions.  Identifier grammar was never part of
    /// the gap: both lanes share the same certification preflight
    /// (`validate_model_for_certification` / `validate_temporal_identifier`),
    /// so a leading-underscore or over-`MAX_NAME_BYTES` name is
    /// macro-constructible but not macro-CERTIFIABLE, and only certifiable
    /// models define the parity domain.  That shared stricter grammar — no
    /// leading underscore, the `MAX_NAME_BYTES` length cap, reserved-token
    /// rejection — is ratified as the parity target itself (owner ruling
    /// 2026-07-20): `valid_tla_identifier` is the TLA+ anti-injection guard
    /// and will not be relaxed.  Likewise the Clean lane's nonnegative
    /// (`Nat`) value domain matches the macro DSL's own `LitInt` restriction
    /// and is not a parity gap (same ruling).  The ID remains only so stored
    /// reports stay deserializable.
    ScalarModelAdmissionDomainParityMissing,
    /// Historical blocker ID (closed by the owner policy flip 2026-07-21).
    /// Converting a decoded Clean model through the legacy `Model` ABI used to
    /// consume a process-global finite name-interner budget, so a later small
    /// migration could fail solely because unrelated earlier conversions used
    /// the budget.  The interner and its caps were deleted (2026-07-20): the
    /// certification core is name-representation generic and
    /// `CleanScalarModel::to_model` feeds `certify_model` an owned
    /// `String`-named `Model` directly, so no process-wide budget can decline
    /// an otherwise valid model — evidenced by the 110-conversion
    /// budget-crossing vector certifying end-to-end.  The ID remains only so
    /// stored reports stay deserializable.
    ProcessGlobalNameInterningParityMissing,
    /// Historical blocker ID: `temporal_model!` used to register item-position
    /// models into a legacy link-time package inventory with no explicit
    /// replacement.  That inventory was deleted as extraneous (owner ruling
    /// 2026-07-20): the live gates never trusted the linked registry as
    /// program evidence, and callers/build integration own the explicit
    /// definition list they certify — so this gap no longer exists and the ID
    /// is retained only so stored reports remain deserializable.
    AutomaticModelInventoryReplacementMissing,
}

/// Gaps in advisory migration parity for well-formed, certifiable scalar models
/// authored with `trust_model!` and `temporal_model!`.
///
/// Empty means every scalar macro model in the owner-ratified operational parity
/// domain has a Clean migration. That domain excludes only malformed models and
/// the `MAX_MODEL_ITEMS = 65_536` decode-cost/DoS ceiling; this is an explicit
/// practical source-size scope, not literal unbounded parser-domain equality.
/// EMPTY since the owner policy flip of 2026-07-21: the replacement-only
/// admission limits and the process-history-dependent interner failures are
/// gone (interner + name caps deleted, depth cap widened to a decode-cost
/// guard, positive near-cap vectors passed — conversion past the old depth
/// cap with byte parity + replay, end-to-end certification through the
/// shared transport ceiling — 2026-07-20).  The
/// exercised bounded
/// subset still generates byte-identical TLA+/config text and retains the real
/// `Buggy = 1` ratchet.  Macro-accepted malformed structures (for example,
/// missing model sections or duplicate/unknown updates) remain outside parity.
pub const R5_TEMPORAL_PARITY_BLOCKERS: &[R5TemporalParityBlocker] = &[];

/// Whether advisory deprecation and bounded-subset migration guidance may be shown.
///
/// This policy is intentionally independent of complete migration parity.  A
/// deprecation warning points to the supported Clean path while the compatibility
/// macros remain available; it does not assert that every legacy model migrates
/// or that either macro may be deleted.
pub const R5_TEMPORAL_MACRO_DEPRECATION_ALLOWED: bool = true;

/// Macro-domain gaps that prevent deleting the deprecated macros.
///
/// Scoped to the MACRO domain (owner override 2026-07-20): a capability the
/// macro grammar provably cannot express cannot gate deleting the macros, so
/// the function-valued and arbitrary-`~>` Model-ABI ambitions live in the
/// non-gating [`R5_MODEL_ABI_AMBITION_BLOCKERS`] tracker instead.
/// `AppliedCleanPropositionBindingMissing` stays pending a separate owner
/// decision — since the 2026-07-21 policy flip closed the two scalar
/// migration prerequisites, it is the SOLE remaining retirement blocker.
/// Literal-program refinement is separately graded in both the
/// legacy and target surfaces, so it is not a macro-retirement prerequisite.
/// Likewise, final-artifact authentication belongs to compiler/build evidence
/// rather than the explicit in-process model API.
pub const R5_TEMPORAL_RETIREMENT_BLOCKERS: &[R5TemporalParityBlocker] =
    &[R5TemporalParityBlocker::AppliedCleanPropositionBindingMissing];

/// Non-gating tracker for Model-ABI ambitions beyond the macro domain.
///
/// These gaps are real (the broader `Model`/temporal ABI still lacks a
/// function-valued replacement and arbitrary `F ~> G` discharge) but the
/// compatibility macros provably cannot express either capability
/// (`macro_expressible: false`, empty surfaces, guard-test-pinned in
/// `r5_scorecard`), so per the owner override of 2026-07-20 they gate
/// NOTHING — not migration, not deprecation, not macro retirement.  They are
/// recorded here only so the ambition remains tracked under a stable ID.
pub const R5_MODEL_ABI_AMBITION_BLOCKERS: &[R5TemporalParityBlocker] = &[
    R5TemporalParityBlocker::FunctionValuedModelReplacementMissing,
    R5TemporalParityBlocker::ArbitraryLeadsToDischargeMissing,
];

/// Whether the compatibility macros may be removed from the public surface.
pub const R5_TEMPORAL_MACRO_RETIREMENT_ALLOWED: bool = R5_TEMPORAL_RETIREMENT_BLOCKERS.is_empty();

/// State of one explicitly named R5 gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R5TemporalParityStatus {
    /// The named gate has no active blocker.
    Ready,
    /// The named gate has at least one active blocker.
    Blocked,
}

/// Public, serializable snapshot of the three distinct R5 decisions:
/// advisory deprecation, complete migration, and compatibility-surface retirement.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct R5TemporalParityReport {
    /// Versioned report schema.  New reports always use V2.
    pub schema: String,
    /// Parity status for migrating well-formed, certifiable scalar models off
    /// the legacy macro grammar.
    pub macro_migration_status: R5TemporalParityStatus,
    /// Whether the macros may emit their advisory deprecation warning.  This is
    /// independent of complete migration parity.
    pub macro_deprecation_allowed: bool,
    /// Exact gaps in valid legacy-grammar migration coverage.
    pub macro_migration_blockers: Vec<R5TemporalParityBlocker>,
    /// Full-target status that gates deletion of the compatibility macros.
    pub macro_retirement_status: R5TemporalParityStatus,
    /// Whether the transitional compatibility macros may be deleted.
    pub macro_retirement_allowed: bool,
    /// Exact full-target gaps preventing macro deletion.
    pub macro_retirement_blockers: Vec<R5TemporalParityBlocker>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum R5TemporalParityReportValidationError {
    SchemaMismatch { found: String },
    BlockerSetMismatch { gate: &'static str },
    StatusMismatch { gate: &'static str },
    DeprecationAllowedMismatch,
    RetirementAllowedMismatch,
    DuplicateBlocker { gate: &'static str, blocker: R5TemporalParityBlocker },
    RetirementOmitsMigrationBlocker { blocker: R5TemporalParityBlocker },
}

impl std::fmt::Display for R5TemporalParityReportValidationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SchemaMismatch { found } => {
                write!(formatter, "unsupported R5 temporal parity report schema `{found}`")
            }
            Self::BlockerSetMismatch { gate } => write!(
                formatter,
                "R5 temporal {gate} blockers do not match the current implementation snapshot"
            ),
            Self::StatusMismatch { gate } => {
                write!(formatter, "R5 temporal {gate} status contradicts its blockers")
            }
            Self::DeprecationAllowedMismatch => formatter.write_str(
                "R5 temporal deprecation permission contradicts the current implementation policy",
            ),
            Self::RetirementAllowedMismatch => {
                formatter.write_str("R5 temporal retirement permission contradicts its blockers")
            }
            Self::DuplicateBlocker { gate, blocker } => {
                write!(formatter, "duplicate R5 temporal {gate} blocker `{blocker:?}`")
            }
            Self::RetirementOmitsMigrationBlocker { blocker } => write!(
                formatter,
                "R5 temporal retirement blockers omit migration prerequisite `{blocker:?}`"
            ),
        }
    }
}

impl std::error::Error for R5TemporalParityReportValidationError {}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct R5TemporalParityReportWire {
    schema: String,
    macro_migration_status: R5TemporalParityStatus,
    macro_deprecation_allowed: bool,
    macro_migration_blockers: Vec<R5TemporalParityBlocker>,
    macro_retirement_status: R5TemporalParityStatus,
    macro_retirement_allowed: bool,
    macro_retirement_blockers: Vec<R5TemporalParityBlocker>,
}

impl R5TemporalParityReport {
    /// Validate the schema and every aggregate field in a serialized report.
    pub fn validate(&self) -> Result<(), R5TemporalParityReportValidationError> {
        if self.schema != R5_TEMPORAL_PARITY_REPORT_SCHEMA_V2 {
            return Err(R5TemporalParityReportValidationError::SchemaMismatch {
                found: self.schema.clone(),
            });
        }
        for (gate, blockers) in [
            ("migration", &self.macro_migration_blockers),
            ("retirement", &self.macro_retirement_blockers),
        ] {
            let mut seen = std::collections::BTreeSet::new();
            for &blocker in blockers {
                if !seen.insert(blocker) {
                    return Err(R5TemporalParityReportValidationError::DuplicateBlocker {
                        gate,
                        blocker,
                    });
                }
            }
        }
        for &blocker in &self.macro_migration_blockers {
            if !self.macro_retirement_blockers.contains(&blocker) {
                return Err(
                    R5TemporalParityReportValidationError::RetirementOmitsMigrationBlocker {
                        blocker,
                    },
                );
            }
        }
        if self.macro_migration_blockers.as_slice() != R5_TEMPORAL_PARITY_BLOCKERS {
            return Err(R5TemporalParityReportValidationError::BlockerSetMismatch {
                gate: "migration",
            });
        }
        if self.macro_retirement_blockers.as_slice() != R5_TEMPORAL_RETIREMENT_BLOCKERS {
            return Err(R5TemporalParityReportValidationError::BlockerSetMismatch {
                gate: "retirement",
            });
        }
        if self.macro_migration_status != status(&self.macro_migration_blockers) {
            return Err(R5TemporalParityReportValidationError::StatusMismatch {
                gate: "migration",
            });
        }
        if self.macro_retirement_status != status(&self.macro_retirement_blockers) {
            return Err(R5TemporalParityReportValidationError::StatusMismatch {
                gate: "retirement",
            });
        }
        if self.macro_deprecation_allowed != R5_TEMPORAL_MACRO_DEPRECATION_ALLOWED {
            return Err(R5TemporalParityReportValidationError::DeprecationAllowedMismatch);
        }
        if self.macro_retirement_allowed != self.macro_retirement_blockers.is_empty() {
            return Err(R5TemporalParityReportValidationError::RetirementAllowedMismatch);
        }
        Ok(())
    }
}

impl<'de> serde::Deserialize<'de> for R5TemporalParityReport {
    fn deserialize<Deserializer>(deserializer: Deserializer) -> Result<Self, Deserializer::Error>
    where
        Deserializer: serde::Deserializer<'de>,
    {
        let wire = <R5TemporalParityReportWire as serde::Deserialize>::deserialize(deserializer)?;
        let report = Self {
            schema: wire.schema,
            macro_migration_status: wire.macro_migration_status,
            macro_deprecation_allowed: wire.macro_deprecation_allowed,
            macro_migration_blockers: wire.macro_migration_blockers,
            macro_retirement_status: wire.macro_retirement_status,
            macro_retirement_allowed: wire.macro_retirement_allowed,
            macro_retirement_blockers: wire.macro_retirement_blockers,
        };
        report.validate().map_err(serde::de::Error::custom)?;
        Ok(report)
    }
}

fn status(blockers: &[R5TemporalParityBlocker]) -> R5TemporalParityStatus {
    if blockers.is_empty() {
        R5TemporalParityStatus::Ready
    } else {
        R5TemporalParityStatus::Blocked
    }
}

/// Return the current public R5 temporal migration and retirement report.
pub fn r5_temporal_parity_report() -> R5TemporalParityReport {
    let report = R5TemporalParityReport {
        schema: R5_TEMPORAL_PARITY_REPORT_SCHEMA_V2.to_owned(),
        macro_migration_status: status(R5_TEMPORAL_PARITY_BLOCKERS),
        macro_deprecation_allowed: R5_TEMPORAL_MACRO_DEPRECATION_ALLOWED,
        macro_migration_blockers: R5_TEMPORAL_PARITY_BLOCKERS.to_vec(),
        macro_retirement_status: status(R5_TEMPORAL_RETIREMENT_BLOCKERS),
        macro_retirement_allowed: R5_TEMPORAL_MACRO_RETIREMENT_ALLOWED,
        macro_retirement_blockers: R5_TEMPORAL_RETIREMENT_BLOCKERS.to_vec(),
    };
    debug_assert_eq!(report.validate(), Ok(()));
    report
}

#[cfg(test)]
mod tests {
    use super::*;

    const MACRO_IMPLEMENTATION_SOURCE: &str =
        include_str!("../../trust-spec-temporal-macros/src/lib.rs");

    #[test]
    fn current_report_migration_ready_deprecation_live_retirement_still_blocked() {
        let report = r5_temporal_parity_report();
        assert_eq!(report.schema, R5_TEMPORAL_PARITY_REPORT_SCHEMA_V2);
        // Migration parity closed by the 2026-07-21 owner policy flip.
        assert_eq!(report.macro_migration_status, R5TemporalParityStatus::Ready);
        assert!(report.macro_deprecation_allowed);
        assert!(report.macro_migration_blockers.is_empty());
        assert!(R5_TEMPORAL_MACRO_DEPRECATION_ALLOWED);

        // Retirement (macro DELETION) stays honestly blocked on the applied
        // Clean proposition binding — a separate, still-pending owner decision.
        assert_eq!(report.macro_retirement_status, R5TemporalParityStatus::Blocked);
        assert!(!report.macro_retirement_allowed);
        assert_eq!(
            report.macro_retirement_blockers,
            vec![R5TemporalParityBlocker::AppliedCleanPropositionBindingMissing],
        );
        assert!(!R5_TEMPORAL_MACRO_RETIREMENT_ALLOWED);
    }

    #[test]
    fn serialized_v2_report_never_overloads_status_or_blockers() {
        let value = serde_json::to_value(r5_temporal_parity_report()).expect("report serializes");
        assert_eq!(value["schema"], R5_TEMPORAL_PARITY_REPORT_SCHEMA_V2);
        assert_eq!(value["macro_migration_status"], "ready");
        assert_eq!(value["macro_deprecation_allowed"], true);
        assert_eq!(value["macro_migration_blockers"], serde_json::json!([]));
        assert_eq!(value["macro_retirement_status"], "blocked");
        assert_eq!(value["macro_retirement_allowed"], false);
        assert_eq!(
            value["macro_retirement_blockers"],
            serde_json::json!(["applied_clean_proposition_binding_missing"])
        );
        assert!(value.get("status").is_none(), "v2 must not emit ambiguous `status`");
        assert!(value.get("blockers").is_none(), "v2 must not emit ambiguous `blockers`");
    }

    /// Pin the owner override of 2026-07-20: the Model-ABI ambition tracker is
    /// exactly the two non-macro-expressible gaps, and its IDs appear in NO
    /// gating constant and NO emitted report field.
    #[test]
    fn model_abi_ambition_tracker_gates_nothing() {
        assert_eq!(
            R5_MODEL_ABI_AMBITION_BLOCKERS,
            &[
                R5TemporalParityBlocker::FunctionValuedModelReplacementMissing,
                R5TemporalParityBlocker::ArbitraryLeadsToDischargeMissing,
            ],
        );
        let report = r5_temporal_parity_report();
        for blocker in R5_MODEL_ABI_AMBITION_BLOCKERS {
            assert!(!R5_TEMPORAL_PARITY_BLOCKERS.contains(blocker));
            assert!(!R5_TEMPORAL_RETIREMENT_BLOCKERS.contains(blocker));
            assert!(!report.macro_migration_blockers.contains(blocker));
            assert!(!report.macro_retirement_blockers.contains(blocker));
        }
    }

    #[test]
    fn aggregate_status_and_retirement_decisions_are_derived_consistently() {
        let report = r5_temporal_parity_report();
        assert!(report.macro_deprecation_allowed);
        // Migration blockers emptied by the 2026-07-21 flip; retirement still
        // carries the applied-proposition-binding blocker.
        assert!(report.macro_migration_blockers.is_empty());
        assert!(!report.macro_retirement_blockers.is_empty());
        assert_eq!(report.macro_migration_status, status(&report.macro_migration_blockers));
        assert_eq!(report.macro_retirement_allowed, report.macro_retirement_blockers.is_empty());
        assert_eq!(report.macro_retirement_status, status(&report.macro_retirement_blockers));

        for blockers in [&report.macro_migration_blockers, &report.macro_retirement_blockers] {
            let mut unique = blockers.clone();
            unique.sort();
            unique.dedup();
            assert_eq!(unique.len(), blockers.len(), "blocker IDs must be unique");
        }
    }

    #[test]
    fn legacy_schema_name_remains_available_but_is_not_emitted() {
        assert_eq!(R5_TEMPORAL_PARITY_REPORT_SCHEMA_V1, "trust.r5-temporal-parity/v1");
        assert_ne!(r5_temporal_parity_report().schema, R5_TEMPORAL_PARITY_REPORT_SCHEMA_V1);

        let legacy_shape = serde_json::json!({
            "schema": R5_TEMPORAL_PARITY_REPORT_SCHEMA_V1,
            "status": "blocked",
            "blockers": ["certified_temporal_property_classes_incomplete"]
        });
        assert!(
            serde_json::from_value::<R5TemporalParityReport>(legacy_shape).is_err(),
            "V1 overloaded fields are not silently interpreted as a V2 report"
        );

        let historical_id: R5TemporalParityBlocker = serde_json::from_value(serde_json::json!(
            "certified_temporal_property_classes_incomplete"
        ))
        .expect("stable historical blocker IDs remain readable");
        assert_eq!(
            historical_id,
            R5TemporalParityBlocker::CertifiedTemporalPropertyClassesIncomplete
        );

        // The deleted automatic link-time inventory (owner ruling 2026-07-20):
        // its wire ID stays readable for stored reports but gates nothing.
        let inventory_id: R5TemporalParityBlocker = serde_json::from_value(serde_json::json!(
            "automatic_model_inventory_replacement_missing"
        ))
        .expect("historical inventory blocker ID remains readable");
        assert_eq!(
            inventory_id,
            R5TemporalParityBlocker::AutomaticModelInventoryReplacementMissing
        );
        assert!(!R5_TEMPORAL_PARITY_BLOCKERS.contains(&inventory_id));
        assert!(!R5_TEMPORAL_RETIREMENT_BLOCKERS.contains(&inventory_id));
        assert!(!R5_MODEL_ABI_AMBITION_BLOCKERS.contains(&inventory_id));
    }

    #[test]
    fn deserialization_rejects_wrong_schema_hybrid_and_contradictory_reports() {
        let baseline = serde_json::to_value(r5_temporal_parity_report()).unwrap();

        for schema in [R5_TEMPORAL_PARITY_REPORT_SCHEMA_V1, "trust.r5-temporal-parity/v999"] {
            let mut wrong_schema = baseline.clone();
            wrong_schema["schema"] = serde_json::json!(schema);
            assert!(serde_json::from_value::<R5TemporalParityReport>(wrong_schema).is_err());
        }

        let mut hybrid = baseline.clone();
        hybrid["status"] = serde_json::json!("blocked");
        hybrid["blockers"] = serde_json::json!([]);
        assert!(serde_json::from_value::<R5TemporalParityReport>(hybrid).is_err());

        for (field, contradictory) in [
            ("macro_migration_status", serde_json::json!("blocked")),
            ("macro_deprecation_allowed", serde_json::json!(false)),
            ("macro_retirement_status", serde_json::json!("ready")),
            ("macro_retirement_allowed", serde_json::json!(true)),
        ] {
            let mut value = baseline.clone();
            value[field] = contradictory;
            assert!(
                serde_json::from_value::<R5TemporalParityReport>(value).is_err(),
                "contradictory `{field}` was accepted"
            );
        }

        let mut duplicate = baseline.clone();
        let blockers = duplicate["macro_retirement_blockers"].as_array_mut().unwrap();
        let first = blockers[0].clone();
        blockers.push(first);
        assert!(serde_json::from_value::<R5TemporalParityReport>(duplicate).is_err());

        let mut duplicate_report = r5_temporal_parity_report();
        let duplicate_blocker = duplicate_report.macro_retirement_blockers[0];
        duplicate_report.macro_retirement_blockers.push(duplicate_blocker);
        assert_eq!(
            duplicate_report.validate(),
            Err(R5TemporalParityReportValidationError::DuplicateBlocker {
                gate: "retirement",
                blocker: duplicate_blocker,
            })
        );

        let mut dropped_retirement = baseline.clone();
        dropped_retirement["macro_retirement_blockers"].as_array_mut().unwrap().remove(0);
        assert!(
            serde_json::from_value::<R5TemporalParityReport>(dropped_retirement).is_err(),
            "retirement accepted while dropping its remaining blocker"
        );

        let mut dropped_report = r5_temporal_parity_report();
        dropped_report.macro_retirement_blockers.clear();
        assert_eq!(
            dropped_report.validate(),
            Err(R5TemporalParityReportValidationError::BlockerSetMismatch { gate: "retirement" })
        );

        // The subset invariant (every migration blocker must reappear in the
        // retirement set) still has teeth on a fabricated report even though
        // the canonical migration set is empty since the 2026-07-21 flip.
        let mut omitted_report = r5_temporal_parity_report();
        omitted_report.macro_migration_blockers =
            vec![R5TemporalParityBlocker::AppliedCleanPropositionBindingMissing];
        omitted_report.macro_retirement_blockers.clear();
        assert_eq!(
            omitted_report.validate(),
            Err(R5TemporalParityReportValidationError::BlockerSetMismatch { gate: "retirement" })
        );

        // Keep the subset-validation error live even while the current
        // migration set is empty.
        let mut omitted_prerequisite_report = r5_temporal_parity_report();
        let historical = R5TemporalParityBlocker::ScalarModelAdmissionDomainParityMissing;
        omitted_prerequisite_report.macro_migration_blockers.push(historical);
        assert_eq!(
            omitted_prerequisite_report.validate(),
            Err(R5TemporalParityReportValidationError::RetirementOmitsMigrationBlocker {
                blocker: historical,
            })
        );

        // Resurrecting a closed (historical) blocker must be rejected against
        // the snapshot — the exact regression the 2026-07-21 flip must not
        // silently absorb. Push it into BOTH gates so the subset invariant
        // passes and the rejection is attributable to the MIGRATION-gate
        // set-mismatch itself (pinned by error identity on the validate twin).
        let mut resurrected = baseline.clone();
        for gate in ["macro_migration_blockers", "macro_retirement_blockers"] {
            resurrected[gate]
                .as_array_mut()
                .unwrap()
                .push(serde_json::json!("scalar_model_admission_domain_parity_missing"));
        }
        assert!(
            serde_json::from_value::<R5TemporalParityReport>(resurrected).is_err(),
            "current-schema report accepted a resurrected closed blocker"
        );

        let mut resurrected_report = r5_temporal_parity_report();
        resurrected_report
            .macro_migration_blockers
            .push(R5TemporalParityBlocker::ScalarModelAdmissionDomainParityMissing);
        resurrected_report
            .macro_retirement_blockers
            .push(R5TemporalParityBlocker::ScalarModelAdmissionDomainParityMissing);
        assert_eq!(
            resurrected_report.validate(),
            Err(R5TemporalParityReportValidationError::BlockerSetMismatch { gate: "migration" })
        );

        let mut replaced = baseline.clone();
        replaced["macro_retirement_blockers"][0] =
            serde_json::json!("certified_temporal_property_classes_incomplete");
        assert!(
            serde_json::from_value::<R5TemporalParityReport>(replaced).is_err(),
            "current-schema report accepted a stale replacement blocker"
        );

        // Canonical ORDER is enforced by exact-slice equality against the
        // public constants; with at most one element per gate today there is
        // no distinct order left to reject, so the former reorder vectors are
        // subsumed by the exact-set checks above.

        let round_trip: R5TemporalParityReport = serde_json::from_value(baseline).unwrap();
        assert_eq!(round_trip, r5_temporal_parity_report());
    }

    #[test]
    fn macro_deprecation_attributes_follow_the_per_capability_advisory_policy() {
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

        // Advisory migration guidance is permitted in principle
        // (`R5_TEMPORAL_MACRO_DEPRECATION_ALLOWED`, the coarse "may point users at
        // the Clean lane" flag). Whether the per-use `#[deprecated]` ATTRIBUTE
        // fires is a finer, per-capability decision owned by the scorecard: the
        // nudge fires only for a macro surface whose EVERY exercised capability is
        // FullyReplaced. Since the owner policy flip of 2026-07-21 BOTH macros
        // qualify — the scalar-safety core is FullyReplaced (admission-domain +
        // interner gaps closed, positive near-cap vectors certified end-to-end)
        // — so the PRIME RULE is satisfied and both proc-macro fns must carry
        // the attribute: the D1+ ratchet this cross-check enforces.
        assert!(R5_TEMPORAL_MACRO_DEPRECATION_ALLOWED);
        assert!(
            has_deprecation_attribute("trust_model"),
            "`trust_model!`'s scalar-safety core is FullyReplaced (2026-07-21 flip), so the \
             advisory nudge attribute must be present",
        );
        assert!(
            has_deprecation_attribute("temporal_model"),
            "`temporal_model!` exercises the same FullyReplaced scalar-safety core and must \
             carry the advisory nudge",
        );

        // The attribute presence must equal the machine-checkable scorecard's
        // per-surface decision, so the two can never silently diverge.
        use crate::r5_scorecard::{R5MacroSurface, macro_surface_emits_deprecation};
        assert_eq!(
            has_deprecation_attribute("trust_model"),
            macro_surface_emits_deprecation(R5MacroSurface::TrustModel),
        );
        assert_eq!(
            has_deprecation_attribute("temporal_model"),
            macro_surface_emits_deprecation(R5MacroSurface::TemporalModel),
        );
    }
}
