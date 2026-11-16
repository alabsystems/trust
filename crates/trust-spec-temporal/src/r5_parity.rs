//! Machine-readable R5 migration and macro-retirement gates.
//!
//! The compatibility macros were physically retired after the automatic Clean
//! proof bridge closed every certifiable family in their grammar. Finite models
//! regenerate an exact reachable-row strengthening and kernel-check its
//! initiation, consecution, and preservation legs. TY's three live unbounded
//! families—single affine, affine tuple, and relational lockstep—regenerate
//! exact parametric Clean proofs instead of inventing a finite cutoff. Fresh
//! replay re-derives the TY evidence and generated Clean source byte-for-byte,
//! rejects source/model/action/invariant drift, and rejects witness, proof, and
//! cross-family splices.
//!
//! The stable historical blocker IDs and V2 report schema remain readable for
//! artifact compatibility. Arbitrary authored `F ~> G` proofs and indexed
//! mixtures of weak/strong fairness now replay through the Clean kernel. That
//! proof-carrying surface is the complete general lane: no sound checker can
//! automatically discover proofs of arbitrary propositions. TY remains an
//! optional producer for recognized decidable classes. This report is
//! implementation status, never proof evidence. Whole-project automatic
//! integration is tracked separately and remains fail-closed until the compiler
//! authenticates the semantic inputs, checker identity, and final artifact.

/// Legacy schema identifier retained so stored v1 reports can still be named.
///
/// V1 overloaded `status` and `blockers` between advisory deprecation and final
/// macro retirement.  New reports are always emitted as V2 and do not reproduce
/// those ambiguous fields.
pub const R5_TEMPORAL_PARITY_REPORT_SCHEMA_V1: &str = "trust.r5-temporal-parity/v1";

/// Current schema identifier for the public R5 temporal migration report.
pub const R5_TEMPORAL_PARITY_REPORT_SCHEMA_V2: &str = "trust.r5-temporal-parity/v2";

/// Separate, non-gating automatic project-integration report schema.
pub const TEMPORAL_AUTOMATIC_INTEGRATION_REPORT_SCHEMA_V1: &str =
    "trust.temporal-automatic-integration/v1";

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
    /// Historical blocker ID. General indexed weak/strong fairness is accepted
    /// through authored, kernel-checked Clean proofs; TY's selected automatic
    /// producers are an optimization and no longer define semantic coverage.
    CertifiedTemporalPropertyClassesIncomplete,
    /// Historical blocker ID. Exact literal refinement now retains canonical,
    /// fully validated TrustIR bytes, regenerates the supported scalar EvalIR
    /// `Program`, `Init`, and universal `Next`, kernel-checks the fixed
    /// transition-theorem set, and rejects invalid modules, input, source,
    /// proof, and cross-artifact splices on fresh replay. Constructs whose
    /// operational outcomes differ (including assertions and ordered Boolean
    /// comparisons), plus unchecked casts into `Char`, decline fail-closed.
    /// The wire ID remains deserializable for older status artifacts.
    LiteralProgramTransitionRefinementMissing,
    /// Active blocker for the separate automatic project-integration route: the
    /// compiler does not yet bind temporal semantic inputs, resolved dependencies,
    /// checker/output identity, and the final program artifact into one evidence
    /// chain. It is historical/non-gating only for macro migration and retirement,
    /// whose replacement is the explicit caller-owned Clean certification API.
    AuthenticatedCompilerEvidenceMissing,
    /// Historical blocker ID: production certificates lacked an exact
    /// kernel-closed route for their actual explicit-fixpoint evidence.
    ProductionExactKernelClosedCertificateMissing,
    /// Historical blocker ID: no Clean replacement preserved and bound the
    /// macro lane's `Buggy = 1` counterexample ratchet.
    CleanReplacementBuggyOneRatchetMissing,
    /// Historical blocker ID: the Clean v1 decoder was scalar-only. The v2
    /// finite-model ABI now supports function-valued variables and
    /// access/update/comprehension expressions.
    FunctionValuedModelReplacementMissing,
    /// Historical blocker ID for automatic exact applied-proposition proof
    /// production. Closed by the deterministic automatic Clean proof bridge:
    /// finite reachable rows and all three TY unbounded scalar families now
    /// produce and freshly replay exact model-bound inhabitants. The wire ID is
    /// retained so stored V2 reports remain deserializable.
    AppliedCleanPropositionBindingMissing,
    /// Historical blocker ID. Arbitrary authored `F ~> G` propositions and
    /// general fairness assumptions are proved in Clean and freshly
    /// kernel-replayed. Requiring an automatic proof searcher for arbitrary
    /// propositions would be an impossible completeness criterion.
    ArbitraryLeadsToDischargeMissing,
    /// Historical blocker ID (closed by the policy flip of 2026-07-21).
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
    /// rejection — is ratified as the parity target itself (ruled
    /// 2026-07-20): `valid_tla_identifier` is the TLA+ anti-injection guard
    /// and will not be relaxed.  Likewise the Clean lane's nonnegative
    /// (`Nat`) value domain matches the macro DSL's own `LitInt` restriction
    /// and is not a parity gap (same ruling).  The ID remains only so stored
    /// reports stay deserializable.
    ScalarModelAdmissionDomainParityMissing,
    /// Historical blocker ID (closed by the policy flip of 2026-07-21).
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
    /// replacement.  That inventory was deleted as extraneous (ruled
    /// 2026-07-20): the live gates never trusted the linked registry as
    /// program evidence, and callers/build integration own the explicit
    /// definition list they certify — so this gap no longer exists and the ID
    /// is retained only so stored reports remain deserializable.
    AutomaticModelInventoryReplacementMissing,
}

/// Gaps in advisory migration parity for well-formed, certifiable scalar models
/// authored with the now-retired `trust_model!` and `temporal_model!` DSLs.
///
/// Empty means every scalar macro model in the ratified operational parity
/// domain has a Clean migration. That domain excludes only malformed models and
/// the `MAX_MODEL_ITEMS = 65_536` decode-cost/DoS ceiling; this is an explicit
/// practical source-size scope, not literal unbounded parser-domain equality.
/// EMPTY since the policy flip of 2026-07-21: the replacement-only
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

/// Whether the completed advisory-deprecation phase was permitted.
///
/// This policy is intentionally independent of complete migration parity.
/// Kept as a stable V2 report field after physical retirement, it records that
/// the earlier warning phase was allowed; no macro remains to emit a warning.
pub const R5_TEMPORAL_MACRO_DEPRECATION_ALLOWED: bool = true;

/// Macro-domain gaps that prevent deleting the deprecated macros.
///
/// Empty since the automatic Clean proof bridge closed finite reachable-row
/// models and every live TY unbounded scalar family. Exact literal-program
/// refinement is independently available under
/// `trust.literal-evalir-refinement/v2`. Hand-written finite abstractions bind
/// to that concrete machine through the proof-carrying
/// `trust.model-program-refinement/v2` forward-simulation lane, which transports
/// runs and arbitrary temporal formulas. Wider concrete-language or backend
/// semantics require their own checked refinement edges; automatic proof
/// discovery for arbitrary liveness remains impossible in general. Neither
/// concern was expressible by the retired macros.
pub const R5_TEMPORAL_RETIREMENT_BLOCKERS: &[R5TemporalParityBlocker] = &[];

/// Remaining Model-ABI semantic ambitions beyond the retired macro domain.
///
/// Empty: the general surface is proof-carrying rather than proof-search
/// complete. Clean accepts arbitrary authored `F ~> G` proofs and indexed
/// weak/strong fairness families, rejects notation shadowing, requires an empty
/// domain-axiom closure, audits reachable declaration provenance, and freshly
/// kernel-replays exact source/type/proof bytes. TY's recognized automatic
/// safety/countdown classes remain useful producers, but a producer decline
/// cannot erase an independently checked proof.
pub const R5_MODEL_ABI_AMBITION_BLOCKERS: &[R5TemporalParityBlocker] = &[];

/// Blockers for automatic whole-project temporal discovery/execution. This is
/// separate from macro migration/retirement: explicit Clean certification is
/// complete while `targo trust temporal` intentionally remains fail-closed.
pub const TEMPORAL_AUTOMATIC_INTEGRATION_BLOCKERS: &[R5TemporalParityBlocker] =
    &[R5TemporalParityBlocker::AuthenticatedCompilerEvidenceMissing];

pub const TEMPORAL_AUTOMATIC_INTEGRATION_READY: bool =
    TEMPORAL_AUTOMATIC_INTEGRATION_BLOCKERS.is_empty();

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
    /// Whether the historical advisory-deprecation phase was allowed. This is
    /// retained for V2 report compatibility after physical retirement.
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

/// Non-proof status of automatic project integration. This report is separate
/// so an integration gap cannot be mistaken for a macro-retirement blocker.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct TemporalAutomaticIntegrationReport {
    pub schema: String,
    pub status: R5TemporalParityStatus,
    pub ready: bool,
    pub blockers: Vec<R5TemporalParityBlocker>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TemporalAutomaticIntegrationReportValidationError {
    SchemaMismatch { found: String },
    DuplicateBlocker { blocker: R5TemporalParityBlocker },
    BlockerSetMismatch,
    StatusMismatch,
    ReadyMismatch,
}

impl std::fmt::Display for TemporalAutomaticIntegrationReportValidationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SchemaMismatch { found } => write!(
                formatter,
                "unsupported temporal automatic-integration report schema `{found}`"
            ),
            Self::DuplicateBlocker { blocker } => {
                write!(formatter, "duplicate temporal automatic-integration blocker `{blocker:?}`")
            }
            Self::BlockerSetMismatch => formatter.write_str(
                "temporal automatic-integration blockers do not match the implementation snapshot",
            ),
            Self::StatusMismatch => formatter
                .write_str("temporal automatic-integration status contradicts its blockers"),
            Self::ReadyMismatch => formatter
                .write_str("temporal automatic-integration readiness contradicts its blockers"),
        }
    }
}

impl std::error::Error for TemporalAutomaticIntegrationReportValidationError {}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TemporalAutomaticIntegrationReportWire {
    schema: String,
    status: R5TemporalParityStatus,
    ready: bool,
    blockers: Vec<R5TemporalParityBlocker>,
}

impl TemporalAutomaticIntegrationReport {
    pub fn validate(&self) -> Result<(), TemporalAutomaticIntegrationReportValidationError> {
        if self.schema != TEMPORAL_AUTOMATIC_INTEGRATION_REPORT_SCHEMA_V1 {
            return Err(TemporalAutomaticIntegrationReportValidationError::SchemaMismatch {
                found: self.schema.clone(),
            });
        }
        let mut seen = std::collections::BTreeSet::new();
        for &blocker in &self.blockers {
            if !seen.insert(blocker) {
                return Err(TemporalAutomaticIntegrationReportValidationError::DuplicateBlocker {
                    blocker,
                });
            }
        }
        if self.blockers.as_slice() != TEMPORAL_AUTOMATIC_INTEGRATION_BLOCKERS {
            return Err(TemporalAutomaticIntegrationReportValidationError::BlockerSetMismatch);
        }
        if self.status != status(&self.blockers) {
            return Err(TemporalAutomaticIntegrationReportValidationError::StatusMismatch);
        }
        if self.ready != self.blockers.is_empty() {
            return Err(TemporalAutomaticIntegrationReportValidationError::ReadyMismatch);
        }
        Ok(())
    }
}

impl<'de> serde::Deserialize<'de> for TemporalAutomaticIntegrationReport {
    fn deserialize<Deserializer>(deserializer: Deserializer) -> Result<Self, Deserializer::Error>
    where
        Deserializer: serde::Deserializer<'de>,
    {
        let wire = <TemporalAutomaticIntegrationReportWire as serde::Deserialize>::deserialize(
            deserializer,
        )?;
        let report = Self {
            schema: wire.schema,
            status: wire.status,
            ready: wire.ready,
            blockers: wire.blockers,
        };
        report.validate().map_err(serde::de::Error::custom)?;
        Ok(report)
    }
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

/// Return the current automatic project-integration status.
pub fn temporal_automatic_integration_report() -> TemporalAutomaticIntegrationReport {
    let report = TemporalAutomaticIntegrationReport {
        schema: TEMPORAL_AUTOMATIC_INTEGRATION_REPORT_SCHEMA_V1.to_owned(),
        status: status(TEMPORAL_AUTOMATIC_INTEGRATION_BLOCKERS),
        ready: TEMPORAL_AUTOMATIC_INTEGRATION_READY,
        blockers: TEMPORAL_AUTOMATIC_INTEGRATION_BLOCKERS.to_vec(),
    };
    debug_assert_eq!(report.validate(), Ok(()));
    report
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn current_report_records_completed_migration_and_retirement() {
        let report = r5_temporal_parity_report();
        assert_eq!(report.schema, R5_TEMPORAL_PARITY_REPORT_SCHEMA_V2);
        assert_eq!(report.macro_migration_status, R5TemporalParityStatus::Ready);
        assert!(report.macro_deprecation_allowed);
        assert!(report.macro_migration_blockers.is_empty());
        assert!(R5_TEMPORAL_MACRO_DEPRECATION_ALLOWED);

        assert_eq!(report.macro_retirement_status, R5TemporalParityStatus::Ready);
        assert!(report.macro_retirement_allowed);
        assert!(report.macro_retirement_blockers.is_empty());
        assert!(R5_TEMPORAL_MACRO_RETIREMENT_ALLOWED);
    }

    #[test]
    fn automatic_project_integration_is_separate_and_fails_closed() {
        let report = temporal_automatic_integration_report();
        assert_eq!(report.schema, TEMPORAL_AUTOMATIC_INTEGRATION_REPORT_SCHEMA_V1);
        assert_eq!(report.status, R5TemporalParityStatus::Blocked);
        assert!(!report.ready);
        assert!(!TEMPORAL_AUTOMATIC_INTEGRATION_READY);
        assert_eq!(
            report.blockers,
            vec![R5TemporalParityBlocker::AuthenticatedCompilerEvidenceMissing]
        );
        let blocker = R5TemporalParityBlocker::AuthenticatedCompilerEvidenceMissing;
        assert!(!R5_TEMPORAL_PARITY_BLOCKERS.contains(&blocker));
        assert!(!R5_TEMPORAL_RETIREMENT_BLOCKERS.contains(&blocker));

        let temporal_cli = include_str!("../../../targo-trust/src/temporal_cli.rs");
        assert!(temporal_cli.contains("UNBOUND_TEMPORAL_EVIDENCE"));
        assert!(temporal_cli.contains("authenticated input/output manifest"));
        assert!(temporal_cli.contains("ExitCode::from(2)"));
    }

    #[test]
    fn automatic_integration_report_rejects_schema_status_and_blocker_drift() {
        let baseline = serde_json::to_value(temporal_automatic_integration_report()).unwrap();
        assert_eq!(baseline["status"], "blocked");
        assert_eq!(baseline["ready"], false);
        assert_eq!(
            baseline["blockers"],
            serde_json::json!(["authenticated_compiler_evidence_missing"])
        );

        for (field, value) in [
            ("schema", serde_json::json!("trust.temporal-automatic-integration/v999")),
            ("status", serde_json::json!("ready")),
            ("ready", serde_json::json!(true)),
            ("blockers", serde_json::json!([])),
        ] {
            let mut drifted = baseline.clone();
            drifted[field] = value;
            assert!(
                serde_json::from_value::<TemporalAutomaticIntegrationReport>(drifted).is_err(),
                "contradictory automatic-integration field `{field}` was accepted"
            );
        }

        let mut duplicate = baseline.clone();
        duplicate["blockers"] = serde_json::json!([
            "authenticated_compiler_evidence_missing",
            "authenticated_compiler_evidence_missing"
        ]);
        assert!(serde_json::from_value::<TemporalAutomaticIntegrationReport>(duplicate).is_err());
        let mut unknown = baseline.clone();
        unknown["proof"] = serde_json::json!(true);
        assert!(serde_json::from_value::<TemporalAutomaticIntegrationReport>(unknown).is_err());

        let round_trip: TemporalAutomaticIntegrationReport =
            serde_json::from_value(baseline).unwrap();
        assert_eq!(round_trip, temporal_automatic_integration_report());
    }

    #[test]
    fn serialized_v2_report_never_overloads_status_or_blockers() {
        let value = serde_json::to_value(r5_temporal_parity_report()).expect("report serializes");
        assert_eq!(value["schema"], R5_TEMPORAL_PARITY_REPORT_SCHEMA_V2);
        assert_eq!(value["macro_migration_status"], "ready");
        assert_eq!(value["macro_deprecation_allowed"], true);
        assert_eq!(value["macro_migration_blockers"], serde_json::json!([]));
        assert_eq!(value["macro_retirement_status"], "ready");
        assert_eq!(value["macro_retirement_allowed"], true);
        assert_eq!(value["macro_retirement_blockers"], serde_json::json!([]));
        assert!(value.get("status").is_none(), "v2 must not emit ambiguous `status`");
        assert!(value.get("blockers").is_none(), "v2 must not emit ambiguous `blockers`");
    }

    /// The two former automatic-discharge ambitions are historical IDs. The
    /// complete general surface consumes authored proof objects; it does not
    /// promise an impossible decision procedure for arbitrary propositions.
    #[test]
    fn model_abi_ambition_tracker_is_complete() {
        assert!(R5_MODEL_ABI_AMBITION_BLOCKERS.is_empty());
        let report = r5_temporal_parity_report();
        for blocker in [
            R5TemporalParityBlocker::CertifiedTemporalPropertyClassesIncomplete,
            R5TemporalParityBlocker::ArbitraryLeadsToDischargeMissing,
        ] {
            assert!(!R5_TEMPORAL_PARITY_BLOCKERS.contains(&blocker));
            assert!(!R5_TEMPORAL_RETIREMENT_BLOCKERS.contains(&blocker));
            assert!(!report.macro_migration_blockers.contains(&blocker));
            assert!(!report.macro_retirement_blockers.contains(&blocker));
        }
    }

    #[test]
    fn aggregate_status_and_retirement_decisions_are_derived_consistently() {
        let report = r5_temporal_parity_report();
        assert!(report.macro_deprecation_allowed);
        assert!(report.macro_migration_blockers.is_empty());
        assert!(report.macro_retirement_blockers.is_empty());
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

        // The deleted automatic link-time inventory (2026-07-20):
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
            ("macro_retirement_status", serde_json::json!("blocked")),
            ("macro_retirement_allowed", serde_json::json!(false)),
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
        let historical = serde_json::json!("applied_clean_proposition_binding_missing");
        blockers.push(historical.clone());
        blockers.push(historical);
        assert!(serde_json::from_value::<R5TemporalParityReport>(duplicate).is_err());

        let mut duplicate_report = r5_temporal_parity_report();
        let duplicate_blocker = R5TemporalParityBlocker::AppliedCleanPropositionBindingMissing;
        duplicate_report.macro_retirement_blockers.push(duplicate_blocker);
        duplicate_report.macro_retirement_blockers.push(duplicate_blocker);
        assert_eq!(
            duplicate_report.validate(),
            Err(R5TemporalParityReportValidationError::DuplicateBlocker {
                gate: "retirement",
                blocker: duplicate_blocker,
            })
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
            Err(R5TemporalParityReportValidationError::RetirementOmitsMigrationBlocker {
                blocker: R5TemporalParityBlocker::AppliedCleanPropositionBindingMissing,
            })
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

        let round_trip: R5TemporalParityReport = serde_json::from_value(baseline).unwrap();
        assert_eq!(round_trip, r5_temporal_parity_report());
    }

    #[test]
    fn physical_macro_surface_stays_retired() {
        let manifest = include_str!("../Cargo.toml");
        let library = include_str!("lib.rs");
        // Workspace unification retired crates/Cargo.toml. Check the current
        // root workspace and this package's own standalone workspace instead.
        let root_workspace = include_str!("../../../Cargo.toml");
        assert!(!manifest.contains("trust-spec-temporal-macros"));
        assert!(!library.contains("pub use trust_spec_temporal_macros"));
        assert!(!root_workspace.contains("trust-spec-temporal-macros"));
        assert!(R5_TEMPORAL_MACRO_RETIREMENT_ALLOWED);
    }
}
