// trust_vcgen/symbolic_formula: schema-aware consumer for preserved symbolic payloads.
//
// `trust_symbolic.formula` lowering preserves a typed `trust_types::Formula`
// payload. VC generation must either consume that schema explicitly or emit a
// proof-grade blocker; it must never replace the payload with Undef.

use trust_types::{Formula, Sort, stable_sha256_hex};

pub const SYMBOLIC_FORMULA_SCHEMA: &str = "trust-types.Formula@1";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolicFormulaConsumerStatus {
    Consumed,
    Rejected,
}

impl SymbolicFormulaConsumerStatus {
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Consumed => "consumed",
            Self::Rejected => "rejected",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolicFormulaConsumptionRecord {
    pub schema: String,
    pub status: SymbolicFormulaConsumerStatus,
    pub content: String,
    pub digest: String,
    pub smtlib: String,
    pub sort: Sort,
    pub smtlib_sort: String,
    pub debug: String,
}

impl SymbolicFormulaConsumptionRecord {
    #[must_use]
    pub fn diagnostic(&self, context: &str) -> String {
        format!(
            "{context}: symbolic-formula-proof-consumer=accepted; trust_symbolic.formula=consumed; formula.schema={}; formula.status={}; formula_json={}; formula.sha256={}; formula.smtlib2={}; formula.sort={}; formula.debug={}",
            self.schema,
            self.status.as_str(),
            self.content,
            self.digest,
            self.smtlib,
            self.smtlib_sort,
            self.debug
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolicFormulaRejectionKind {
    UnknownSchema { schema: String },
    JsonRoundTripFailed { detail: String },
    MissingStrictSort,
    UnsupportedTopLevelSort { sort: Sort },
}

impl SymbolicFormulaRejectionKind {
    #[must_use]
    fn code(&self) -> &'static str {
        match self {
            Self::UnknownSchema { .. } => "unknown-schema",
            Self::JsonRoundTripFailed { .. } => "json-roundtrip-failed",
            Self::MissingStrictSort => "missing-strict-sort",
            Self::UnsupportedTopLevelSort { .. } => "unsupported-top-level-sort",
        }
    }

    #[must_use]
    fn reason(&self) -> String {
        match self {
            Self::UnknownSchema { schema } => {
                format!("unknown formula schema `{schema}`; expected `{SYMBOLIC_FORMULA_SCHEMA}`")
            }
            Self::JsonRoundTripFailed { detail } => {
                format!("trust-types Formula JSON did not round-trip through schema: {detail}")
            }
            Self::MissingStrictSort => {
                "missing strict SMT sort metadata for trust-types Formula schema".to_string()
            }
            Self::UnsupportedTopLevelSort { sort } => format!(
                "unsupported top-level symbolic formula sort {}; supported proof values are Bool, Int, and BitVec",
                sort.to_smtlib()
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolicFormulaRejection {
    pub schema: String,
    pub status: SymbolicFormulaConsumerStatus,
    pub kind: SymbolicFormulaRejectionKind,
    pub content: Option<String>,
    pub digest: Option<String>,
    pub smtlib: String,
    pub sort: Option<Sort>,
    pub debug: String,
}

impl SymbolicFormulaRejection {
    #[must_use]
    pub fn unsupported_vc_kind(&self) -> &'static str {
        match &self.kind {
            SymbolicFormulaRejectionKind::MissingStrictSort => "TrustSymbolicFormulaSortMissing",
            _ => "TrustSymbolicFormulaNotProofConsumed",
        }
    }

    #[must_use]
    pub fn diagnostic(&self, context: &str) -> String {
        let content = self.content.as_deref().unwrap_or("<unserializable>");
        let digest = self.digest.as_deref().unwrap_or("<unavailable>");
        let sort = self.sort.as_ref().map_or_else(|| "<unknown>".to_string(), Sort::to_smtlib);

        format!(
            "{context}: trust_symbolic.formula=not-consumed; symbolic-formula-proof-consumer={}; proof-grade=false; formula.schema={}; formula.schema_error={}; formula.schema_error_detail={}; formula_json={}; formula.sha256={}; formula.smtlib2={}; formula.sort={}; formula.debug={}; structured formula payload is preserved but no schema-aware proof consumer accepted it; rejecting instead of Undef",
            self.status.as_str(),
            self.schema,
            self.kind.code(),
            self.kind.reason(),
            content,
            digest,
            self.smtlib,
            sort,
            self.debug
        )
    }
}

#[expect(
    clippy::result_large_err,
    reason = "symbolic rejection records intentionally preserve full proof-grade diagnostics"
)]
pub fn consume_symbolic_formula(
    formula: &Formula,
) -> Result<SymbolicFormulaConsumptionRecord, SymbolicFormulaRejection> {
    consume_symbolic_formula_with_schema(SYMBOLIC_FORMULA_SCHEMA, formula)
}

#[expect(
    clippy::result_large_err,
    reason = "symbolic rejection records intentionally preserve full proof-grade diagnostics"
)]
pub fn consume_symbolic_formula_with_schema(
    schema: &str,
    formula: &Formula,
) -> Result<SymbolicFormulaConsumptionRecord, SymbolicFormulaRejection> {
    let serialized = serialized_payload(formula);
    if schema != SYMBOLIC_FORMULA_SCHEMA {
        return Err(rejection(
            schema,
            formula,
            serialized,
            None,
            SymbolicFormulaRejectionKind::UnknownSchema { schema: schema.to_string() },
        ));
    }

    let sort = match crate::formula_sort(formula) {
        Some(sort) => sort,
        None => {
            return Err(rejection(
                schema,
                formula,
                serialized,
                None,
                SymbolicFormulaRejectionKind::MissingStrictSort,
            ));
        }
    };

    if !matches!(&sort, Sort::Bool | Sort::Int | Sort::BitVec(_)) {
        return Err(rejection(
            schema,
            formula,
            serialized,
            Some(sort.clone()),
            SymbolicFormulaRejectionKind::UnsupportedTopLevelSort { sort },
        ));
    }

    let (content, digest) = match serialized {
        Ok((content, digest)) => {
            match serde_json::from_str::<Formula>(&content) {
                Ok(round_trip) if round_trip == *formula => {}
                Ok(round_trip) => {
                    return Err(rejection(
                        schema,
                        formula,
                        Ok((content, digest)),
                        Some(sort),
                        SymbolicFormulaRejectionKind::JsonRoundTripFailed {
                            detail: format!(
                                "round-tripped payload changed from {formula:?} to {round_trip:?}"
                            ),
                        },
                    ));
                }
                Err(error) => {
                    return Err(rejection(
                        schema,
                        formula,
                        Ok((content, digest)),
                        Some(sort),
                        SymbolicFormulaRejectionKind::JsonRoundTripFailed {
                            detail: error.to_string(),
                        },
                    ));
                }
            }
            (content, digest)
        }
        Err(detail) => {
            return Err(rejection(
                schema,
                formula,
                Err(detail.clone()),
                Some(sort),
                SymbolicFormulaRejectionKind::JsonRoundTripFailed { detail },
            ));
        }
    };

    Ok(SymbolicFormulaConsumptionRecord {
        schema: schema.to_string(),
        status: SymbolicFormulaConsumerStatus::Consumed,
        content,
        digest,
        smtlib: formula.to_smtlib(),
        sort: sort.clone(),
        smtlib_sort: sort.to_smtlib(),
        debug: format!("{formula:?}"),
    })
}

fn serialized_payload(formula: &Formula) -> Result<(String, String), String> {
    let content = serde_json::to_string(formula).map_err(|error| error.to_string())?;
    let digest = stable_sha256_hex(content.as_bytes());
    Ok((content, digest))
}

fn rejection(
    schema: &str,
    formula: &Formula,
    serialized: Result<(String, String), String>,
    sort: Option<Sort>,
    kind: SymbolicFormulaRejectionKind,
) -> SymbolicFormulaRejection {
    let (content, digest) = match serialized {
        Ok((content, digest)) => (Some(content), Some(digest)),
        Err(_) => (None, None),
    };

    SymbolicFormulaRejection {
        schema: schema.to_string(),
        status: SymbolicFormulaConsumerStatus::Rejected,
        kind,
        content,
        digest,
        smtlib: formula.to_smtlib(),
        sort,
        debug: format!("{formula:?}"),
    }
}
