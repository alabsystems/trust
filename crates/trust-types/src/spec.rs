// trust-types/spec.rs: Specification clause types and representation
//
// Higher-level API for native clauses and compatibility-desugared attributes
// that wraps the lower-level
// Contract/ContractKind types and parse_spec_expr parser. Provides types for
// representing requires/ensures/invariant/decreases specifications.
//
// Two API layers:
// - SpecAttribute / FunctionSpec: string-based, used by compiler frontend
// - RawSpec / ParsedSpec / ParsedFunctionSpec: formula-based, used by vcgen
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::{ContractKind, Formula, SourceSpan, parse_spec_expr_result};

// SpecKind alias removed — use ContractKind directly.

// ---------------------------------------------------------------------------
// SpecAttribute — string-based API for compiler frontend
// ---------------------------------------------------------------------------

/// A parsed specification attribute from source code.
///
/// Represents one `#[requires(expr)]`, `#[ensures(expr)]`, etc. attribute
/// with its raw expression text and optional source location.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpecAttribute {
    /// What kind of spec this is (requires, ensures, invariant, decreases).
    pub kind: ContractKind,
    /// The raw expression text from the attribute body.
    pub expression: String,
    /// Source location of the attribute, if available.
    pub span: Option<SourceSpan>,
}

impl SpecAttribute {
    /// Parse the expression into a solver Formula.
    ///
    /// Returns an error if the expression cannot be parsed (for example,
    /// because it uses unsupported syntax). Callers must handle every clause;
    /// an invalid contract is never silently discarded.
    pub fn to_formula(&self) -> Result<Formula, SpecParseError> {
        parse_spec_expr_result(&self.expression)
    }

    /// Convert to a Contract for pipeline compatibility.
    #[must_use]
    pub fn to_contract(&self) -> crate::Contract {
        crate::Contract {
            kind: self.kind,
            span: self.span.clone().unwrap_or_default(),
            body: self.expression.clone(),
        }
    }
}

/// Collected specifications for a single function (string-based).
///
/// Aggregates all spec attributes found on a function definition.
/// This is the type that flows from the compiler frontend through
/// to the verification pipeline.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionSpec {
    /// Preconditions: `#[requires(expr)]`
    pub requires: Vec<String>,
    /// Postconditions: `#[ensures(expr)]`
    pub ensures: Vec<String>,
    /// Invariants: `#[invariant(expr)]`
    pub invariants: Vec<String>,
}

impl FunctionSpec {
    /// Returns true if no specifications are present.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.requires.is_empty() && self.ensures.is_empty() && self.invariants.is_empty()
    }

    /// Total number of spec clauses.
    #[must_use]
    pub fn len(&self) -> usize {
        self.requires.len() + self.ensures.len() + self.invariants.len()
    }

    /// Parse all requires clauses into Formulas.
    pub fn parse_requires(&self) -> Result<Vec<Formula>, SpecParseError> {
        self.requires.iter().map(|expr| parse_spec_expr_result(expr)).collect()
    }

    /// Parse all ensures clauses into Formulas.
    pub fn parse_ensures(&self) -> Result<Vec<Formula>, SpecParseError> {
        self.ensures.iter().map(|expr| parse_spec_expr_result(expr)).collect()
    }

    /// Parse all invariant clauses into Formulas.
    pub fn parse_invariants(&self) -> Result<Vec<Formula>, SpecParseError> {
        self.invariants.iter().map(|expr| parse_spec_expr_result(expr)).collect()
    }

    /// Convert all specs to SpecAttribute list.
    #[must_use]
    pub fn to_attributes(&self) -> Vec<SpecAttribute> {
        let mut attrs = Vec::with_capacity(self.len());
        for expr in &self.requires {
            attrs.push(SpecAttribute {
                kind: ContractKind::Requires,
                expression: expr.clone(),
                span: None,
            });
        }
        for expr in &self.ensures {
            attrs.push(SpecAttribute {
                kind: ContractKind::Ensures,
                expression: expr.clone(),
                span: None,
            });
        }
        for expr in &self.invariants {
            attrs.push(SpecAttribute {
                kind: ContractKind::Invariant,
                expression: expr.clone(),
                span: None,
            });
        }
        attrs
    }

    /// Build from a list of SpecAttributes.
    #[must_use]
    pub fn from_attributes(attrs: &[SpecAttribute]) -> Self {
        let mut spec = FunctionSpec::default();
        for attr in attrs {
            match attr.kind {
                ContractKind::Requires => spec.requires.push(attr.expression.clone()),
                ContractKind::Ensures => spec.ensures.push(attr.expression.clone()),
                ContractKind::Invariant => spec.invariants.push(attr.expression.clone()),
                ContractKind::Decreases => {} // handled separately by termination checking
                // trust-wp-style contract extensions — routed to invariants
                // or handled by dedicated subsystems.
                ContractKind::LoopInvariant => spec.invariants.push(attr.expression.clone()),
                ContractKind::TypeRefinement | ContractKind::Modifies => {}
            }
        }
        spec
    }

    // Build from extracted Contract structs (trust-mir-extract output).
    /// Build a `FunctionSpec` from a slice of `Contract` values.
    ///
    /// This bridges the compiler's attribute extraction (which produces
    /// `Vec<Contract>`) to the verification pipeline's `FunctionSpec`.
    /// Supported clauses are retained even when their trimmed body is empty so
    /// that the fallible `parse_*` methods report `SpecParseError::Empty`.
    /// Silently dropping an empty contract would turn malformed source into an
    /// absent verification obligation.
    #[must_use]
    pub fn from_contracts(contracts: &[crate::Contract]) -> Self {
        let mut spec = FunctionSpec::default();
        for contract in contracts {
            let body = contract.body.trim().to_string();
            match contract.kind {
                ContractKind::Requires => spec.requires.push(body),
                ContractKind::Ensures => spec.ensures.push(body),
                ContractKind::Invariant => spec.invariants.push(body),
                ContractKind::Decreases => {} // handled separately by termination checking
                // trust-wp-style contract extensions.
                ContractKind::LoopInvariant => spec.invariants.push(body),
                ContractKind::TypeRefinement | ContractKind::Modifies => {}
            }
        }
        spec
    }

    // Build ContractMetadata from this spec for VC annotation.
    /// Convert to `ContractMetadata` for attaching to verification conditions.
    #[must_use]
    pub fn to_contract_metadata(&self) -> crate::formula::ContractMetadata {
        crate::formula::ContractMetadata {
            has_requires: !self.requires.is_empty(),
            has_ensures: !self.ensures.is_empty(),
            has_invariant: !self.invariants.is_empty(),
            has_variant: false, // decreases not tracked in FunctionSpec
            // trust-wp-style contract extension flags.
            has_loop_invariant: false,
            has_type_refinement: false,
            has_modifies: false,
            source_contract_index: None,
        }
    }
}

/// Parse a specification attribute from its name and body text.
///
/// This is the entry point for the compiler frontend: when it encounters
/// `#[requires(x > 0)]`, it calls `parse_spec_attribute("requires", "x > 0")`.
///
/// Returns None if the attribute name is not a known spec kind.
#[must_use]
pub fn parse_spec_attribute(attr_name: &str, attr_body: &str) -> Option<SpecAttribute> {
    let kind = ContractKind::from_attr_name(attr_name)?;
    Some(SpecAttribute { kind, expression: attr_body.to_string(), span: None })
}

// ---------------------------------------------------------------------------
// RawSpec / ParsedSpec / ParsedFunctionSpec — formula-based API for vcgen
// ---------------------------------------------------------------------------

/// A raw (unparsed) specification attribute extracted from source.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RawSpec {
    /// What kind of spec this is.
    pub kind: ContractKind,
    /// The expression string from inside the attribute, e.g. `"x > 0"`.
    pub expression: String,
    /// Source location of the attribute.
    pub span: SourceSpan,
}

impl RawSpec {
    /// Create a new raw spec.
    pub fn new(kind: ContractKind, expression: impl Into<String>, span: SourceSpan) -> Self {
        Self { kind, expression: expression.into(), span }
    }

    /// Parse this raw spec into a `ParsedSpec`, converting the expression to a `Formula`.
    ///
    /// Returns `Err(SpecParseError)` if the expression cannot be parsed.
    pub fn parse(&self) -> Result<ParsedSpec, SpecParseError> {
        let formula = crate::spec_parse::parse_spec_expr_result(&self.expression)?;
        Ok(ParsedSpec {
            kind: self.kind,
            expression: self.expression.clone(),
            formula,
            span: self.span.clone(),
        })
    }

    /// Format back to attribute form.
    pub fn to_attribute(&self) -> String {
        self.kind.format_attr(&self.expression)
    }
}

/// A parsed specification with both the original expression and its formula.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ParsedSpec {
    /// What kind of spec this is.
    pub kind: ContractKind,
    /// The original expression string.
    pub expression: String,
    /// The parsed formula.
    pub formula: Formula,
    /// Source location of the attribute.
    pub span: SourceSpan,
}

impl ParsedSpec {
    /// Create a parsed spec directly (e.g., when constructing programmatically).
    pub fn new(
        kind: ContractKind,
        expression: impl Into<String>,
        formula: Formula,
        span: SourceSpan,
    ) -> Self {
        Self { kind, expression: expression.into(), formula, span }
    }
}

/// All parsed specifications on a single function (formula-based).
///
/// Unlike [`FunctionSpec`] which stores expression strings, this stores
/// parsed `Formula` values ready for verification condition generation.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ParsedFunctionSpec {
    /// Preconditions (`requires <predicate>`).
    pub requires: Vec<ParsedSpec>,
    /// Postconditions (`ensures <predicate>`).
    pub ensures: Vec<ParsedSpec>,
    /// Invariant clauses.
    pub invariants: Vec<ParsedSpec>,
    /// Termination measures (`decreases <measure>`).
    pub decreases: Vec<ParsedSpec>,
}

impl ParsedFunctionSpec {
    /// Returns true if no specs are attached.
    pub fn is_empty(&self) -> bool {
        self.requires.is_empty()
            && self.ensures.is_empty()
            && self.invariants.is_empty()
            && self.decreases.is_empty()
    }

    /// Total number of spec clauses.
    pub fn len(&self) -> usize {
        self.requires.len() + self.ensures.len() + self.invariants.len() + self.decreases.len()
    }

    /// Add a parsed spec, routing it to the correct collection by kind.
    pub fn add(&mut self, spec: ParsedSpec) {
        match spec.kind {
            ContractKind::Requires => self.requires.push(spec),
            ContractKind::Ensures => self.ensures.push(spec),
            ContractKind::Invariant | ContractKind::LoopInvariant => self.invariants.push(spec),
            ContractKind::Decreases => self.decreases.push(spec),
            // TypeRefinement and Modifies handled by dedicated subsystems.
            ContractKind::TypeRefinement | ContractKind::Modifies => {}
        }
    }

    /// Parse and add a raw spec. Returns error if parsing fails.
    pub fn add_raw(&mut self, raw: &RawSpec) -> Result<(), SpecParseError> {
        let parsed = raw.parse()?;
        self.add(parsed);
        Ok(())
    }

    /// Collect all precondition formulas.
    pub fn precondition_formulas(&self) -> Vec<&Formula> {
        self.requires.iter().map(|s| &s.formula).collect()
    }

    /// Collect all postcondition formulas.
    pub fn postcondition_formulas(&self) -> Vec<&Formula> {
        self.ensures.iter().map(|s| &s.formula).collect()
    }

    /// Conjoin all preconditions into a single formula (or `true` if empty).
    pub fn combined_precondition(&self) -> Formula {
        combine_formulas(self.precondition_formulas())
    }

    /// Conjoin all postconditions into a single formula (or `true` if empty).
    pub fn combined_postcondition(&self) -> Formula {
        combine_formulas(self.postcondition_formulas())
    }
}

/// Conjoin a list of formulas. Returns `Bool(true)` for empty list.
fn combine_formulas(formulas: Vec<&Formula>) -> Formula {
    match formulas.len() {
        0 => Formula::Bool(true),
        1 => formulas[0].clone(),
        _ => Formula::And(formulas.into_iter().cloned().collect()),
    }
}

// ---------------------------------------------------------------------------
// SpecParseError
// ---------------------------------------------------------------------------

/// Error type for spec expression parsing failures.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum SpecParseError {
    /// The expression string is empty.
    #[error("empty spec expression")]
    Empty,

    /// Unexpected character in the expression.
    #[error("unexpected character '{ch}' at position {position}")]
    UnexpectedChar { ch: char, position: usize },

    /// Unexpected token during parsing.
    #[error("unexpected token at position {position}: expected {expected}")]
    UnexpectedToken { position: usize, expected: String },

    /// Unexpected end of expression.
    #[error("unexpected end of expression: expected {expected}")]
    UnexpectedEof { expected: String },

    /// Trailing tokens after a complete expression.
    #[error("trailing tokens after expression")]
    TrailingTokens,

    /// Quantifier syntax error.
    #[error("invalid quantifier syntax: {detail}")]
    InvalidQuantifier { detail: String },

    /// Method call not supported.
    #[error("unsupported method call: {method}")]
    UnsupportedMethod { method: String },
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Formula, Sort};

    fn default_span() -> SourceSpan {
        SourceSpan::default()
    }

    // --- ContractKind tests ---

    #[test]
    fn test_spec_kind_attr_name() {
        assert_eq!(ContractKind::Requires.attr_name(), "requires");
        assert_eq!(ContractKind::Ensures.attr_name(), "ensures");
        assert_eq!(ContractKind::Invariant.attr_name(), "invariant");
        assert_eq!(ContractKind::Decreases.attr_name(), "decreases");
    }

    #[test]
    fn test_spec_kind_format_attr() {
        assert_eq!(ContractKind::Requires.format_attr("x > 0"), "#[requires(\"x > 0\")]");
        assert_eq!(ContractKind::Ensures.format_attr("result >= 0"), "#[ensures(\"result >= 0\")]");
    }

    #[test]
    fn test_spec_kind_display() {
        assert_eq!(format!("{}", ContractKind::Requires), "requires");
        assert_eq!(format!("{}", ContractKind::Invariant), "invariant");
    }

    #[test]
    fn test_spec_kind_from_attr_name() {
        assert_eq!(ContractKind::from_attr_name("requires"), Some(ContractKind::Requires));
        assert_eq!(ContractKind::from_attr_name("ensures"), Some(ContractKind::Ensures));
        assert_eq!(ContractKind::from_attr_name("invariant"), Some(ContractKind::Invariant));
        assert_eq!(ContractKind::from_attr_name("decreases"), Some(ContractKind::Decreases));
        assert_eq!(ContractKind::from_attr_name("other"), None);
    }

    // test_spec_kind_aliases_contract_kind removed (alias removed).

    // --- SpecAttribute / parse_spec_attribute tests ---

    #[test]
    fn test_parse_spec_attribute_requires() {
        let attr = parse_spec_attribute("requires", "x > 0").expect("should parse");
        assert_eq!(attr.kind, ContractKind::Requires);
        assert_eq!(attr.expression, "x > 0");
        assert!(attr.span.is_none());
    }

    #[test]
    fn test_parse_spec_attribute_ensures() {
        let attr = parse_spec_attribute("ensures", "result > x").expect("should parse");
        assert_eq!(attr.kind, ContractKind::Ensures);
        assert_eq!(attr.expression, "result > x");
    }

    #[test]
    fn test_parse_spec_attribute_invariant() {
        let attr = parse_spec_attribute("invariant", "n >= 0").expect("should parse");
        assert_eq!(attr.kind, ContractKind::Invariant);
    }

    #[test]
    fn test_parse_spec_attribute_decreases() {
        let attr = parse_spec_attribute("decreases", "n").expect("should parse");
        assert_eq!(attr.kind, ContractKind::Decreases);
    }

    #[test]
    fn test_parse_spec_attribute_unknown_kind() {
        assert!(parse_spec_attribute("unknown", "x > 0").is_none());
        assert!(parse_spec_attribute("", "x > 0").is_none());
        assert!(parse_spec_attribute("REQUIRES", "x > 0").is_none());
    }

    #[test]
    fn test_spec_attribute_to_formula() {
        let attr = parse_spec_attribute("requires", "x > 0").unwrap();
        let formula = attr.to_formula().expect("formula should parse");
        assert_eq!(
            formula,
            Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    #[test]
    fn test_spec_attribute_to_formula_complex() {
        let attr = parse_spec_attribute("ensures", "result >= a + b").unwrap();
        let formula = attr.to_formula().expect("formula should parse");
        assert_eq!(
            formula,
            Formula::Ge(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".to_string(), Sort::Int)),
                    Box::new(Formula::Var("b".to_string(), Sort::Int)),
                )),
            )
        );
    }

    #[test]
    fn test_spec_attribute_unparseable_expression() {
        let attr = parse_spec_attribute("requires", "???").unwrap();
        assert!(attr.to_formula().is_err());
    }

    #[test]
    fn test_spec_attribute_to_contract() {
        let attr = SpecAttribute {
            kind: ContractKind::Requires,
            expression: "x > 0".to_string(),
            span: Some(SourceSpan {
                file: "test.rs".to_string(),
                line_start: 5,
                col_start: 1,
                line_end: 5,
                col_end: 20,
            }),
        };
        let contract = attr.to_contract();
        assert!(matches!(contract.kind, ContractKind::Requires));
        assert_eq!(contract.body, "x > 0");
        assert_eq!(contract.span.file, "test.rs");
    }

    #[test]
    fn test_spec_attribute_serialization_roundtrip() {
        let attr = SpecAttribute {
            kind: ContractKind::Ensures,
            expression: "result > 0 && result < 100".to_string(),
            span: Some(SourceSpan {
                file: "lib.rs".to_string(),
                line_start: 10,
                col_start: 0,
                line_end: 10,
                col_end: 40,
            }),
        };
        let json = serde_json::to_string(&attr).expect("serialize");
        let round: SpecAttribute = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, attr);
    }

    // --- FunctionSpec (string-based) tests ---

    #[test]
    fn test_function_spec_empty() {
        let spec = FunctionSpec::default();
        assert!(spec.is_empty());
        assert_eq!(spec.len(), 0);
    }

    #[test]
    fn test_function_spec_with_clauses() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string(), "y > 0".to_string()],
            ensures: vec!["result >= x".to_string()],
            invariants: vec![],
        };
        assert!(!spec.is_empty());
        assert_eq!(spec.len(), 3);
    }

    #[test]
    fn test_function_spec_parse_requires() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string(), "???".to_string()],
            ensures: vec![],
            invariants: vec![],
        };
        assert!(spec.parse_requires().is_err(), "an invalid precondition must fail closed");
    }

    #[test]
    fn test_function_spec_parse_ensures() {
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec!["result > 0".to_string()],
            invariants: vec![],
        };
        let formulas = spec.parse_ensures().expect("valid ensures clauses");
        assert_eq!(formulas.len(), 1);
    }

    #[test]
    fn test_function_spec_parse_invariants() {
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec![],
            invariants: vec!["n >= 0".to_string()],
        };
        let formulas = spec.parse_invariants().expect("valid invariant clauses");
        assert_eq!(formulas.len(), 1);
    }

    #[test]
    fn test_function_spec_to_attributes_roundtrip() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["result >= x".to_string()],
            invariants: vec!["n >= 0".to_string()],
        };
        let attrs = spec.to_attributes();
        assert_eq!(attrs.len(), 3);
        assert_eq!(attrs[0].kind, ContractKind::Requires);
        assert_eq!(attrs[1].kind, ContractKind::Ensures);
        assert_eq!(attrs[2].kind, ContractKind::Invariant);

        let roundtrip = FunctionSpec::from_attributes(&attrs);
        assert_eq!(roundtrip, spec);
    }

    #[test]
    fn test_function_spec_from_attributes_skips_decreases() {
        let attrs = vec![
            SpecAttribute {
                kind: ContractKind::Requires,
                expression: "x > 0".to_string(),
                span: None,
            },
            SpecAttribute {
                kind: ContractKind::Decreases,
                expression: "n".to_string(),
                span: None,
            },
        ];
        let spec = FunctionSpec::from_attributes(&attrs);
        assert_eq!(spec.requires.len(), 1);
        assert!(spec.ensures.is_empty());
        assert!(spec.invariants.is_empty());
    }

    #[test]
    fn test_function_spec_from_contracts_preserves_empty_supported_clauses() {
        let contracts = [
            crate::Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: String::new(),
            },
            crate::Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "   \t".to_string(),
            },
            crate::Contract {
                kind: ContractKind::Invariant,
                span: SourceSpan::default(),
                body: "\n".to_string(),
            },
            crate::Contract {
                kind: ContractKind::LoopInvariant,
                span: SourceSpan::default(),
                body: "  ".to_string(),
            },
        ];

        let spec = FunctionSpec::from_contracts(&contracts);
        assert_eq!(spec.len(), 4, "malformed supported clauses must not disappear");
        assert!(matches!(spec.parse_requires(), Err(SpecParseError::Empty)));
        assert!(matches!(spec.parse_ensures(), Err(SpecParseError::Empty)));
        assert!(matches!(spec.parse_invariants(), Err(SpecParseError::Empty)));
    }

    #[test]
    fn test_function_spec_serialization_roundtrip() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["result >= x".to_string()],
            invariants: vec![],
        };
        let json = serde_json::to_string(&spec).expect("serialize");
        let round: FunctionSpec = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, spec);
    }

    // --- RawSpec / ParsedSpec / ParsedFunctionSpec tests ---

    #[test]
    fn test_raw_spec_parse_success() {
        let raw = RawSpec::new(ContractKind::Requires, "x > 0", default_span());
        let parsed = raw.parse().expect("should parse");
        assert_eq!(parsed.kind, ContractKind::Requires);
        assert_eq!(parsed.expression, "x > 0");
        assert!(matches!(parsed.formula, Formula::Gt(..)));
    }

    #[test]
    fn test_raw_spec_parse_failure() {
        let raw = RawSpec::new(ContractKind::Ensures, "", default_span());
        let err = raw.parse().unwrap_err();
        assert!(matches!(err, SpecParseError::Empty));
    }

    #[test]
    fn test_raw_spec_to_attribute() {
        let raw = RawSpec::new(ContractKind::Requires, "n > 0", default_span());
        assert_eq!(raw.to_attribute(), "#[requires(\"n > 0\")]");
    }

    #[test]
    fn test_parsed_function_spec_empty() {
        let spec = ParsedFunctionSpec::default();
        assert!(spec.is_empty());
        assert_eq!(spec.len(), 0);
    }

    #[test]
    fn test_parsed_function_spec_add_and_len() {
        let mut spec = ParsedFunctionSpec::default();
        let raw_req = RawSpec::new(ContractKind::Requires, "x > 0", default_span());
        let raw_ens = RawSpec::new(ContractKind::Ensures, "result >= 0", default_span());

        spec.add_raw(&raw_req).expect("parse requires");
        spec.add_raw(&raw_ens).expect("parse ensures");

        assert!(!spec.is_empty());
        assert_eq!(spec.len(), 2);
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_parsed_function_spec_combined_precondition_empty() {
        let spec = ParsedFunctionSpec::default();
        assert_eq!(spec.combined_precondition(), Formula::Bool(true));
    }

    #[test]
    fn test_parsed_function_spec_combined_precondition_single() {
        let mut spec = ParsedFunctionSpec::default();
        let raw = RawSpec::new(ContractKind::Requires, "x > 0", default_span());
        spec.add_raw(&raw).expect("parse");
        assert!(matches!(spec.combined_precondition(), Formula::Gt(..)));
    }

    #[test]
    fn test_parsed_function_spec_combined_precondition_multiple() {
        let mut spec = ParsedFunctionSpec::default();
        spec.add_raw(&RawSpec::new(ContractKind::Requires, "x > 0", default_span())).unwrap();
        spec.add_raw(&RawSpec::new(ContractKind::Requires, "y > 0", default_span())).unwrap();
        let combined = spec.combined_precondition();
        assert!(matches!(combined, Formula::And(ref v) if v.len() == 2));
    }

    #[test]
    fn test_parsed_function_spec_add_raw_error_propagates() {
        let mut spec = ParsedFunctionSpec::default();
        let raw = RawSpec::new(ContractKind::Requires, "", default_span());
        assert!(spec.add_raw(&raw).is_err());
        assert!(spec.is_empty());
    }

    #[test]
    fn test_spec_parse_error_display() {
        let err = SpecParseError::UnexpectedChar { ch: '@', position: 5 };
        assert_eq!(err.to_string(), "unexpected character '@' at position 5");

        let err = SpecParseError::Empty;
        assert_eq!(err.to_string(), "empty spec expression");
    }

    #[test]
    fn test_parsed_spec_serialization_roundtrip() {
        let spec = ParsedSpec::new(
            ContractKind::Requires,
            "x > 0",
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            default_span(),
        );
        let json = serde_json::to_string(&spec).expect("serialize");
        let round: ParsedSpec = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.kind, ContractKind::Requires);
        assert_eq!(round.expression, "x > 0");
    }

    #[test]
    fn test_parsed_function_spec_routes_by_kind() {
        let mut spec = ParsedFunctionSpec::default();
        let kinds = [
            ContractKind::Requires,
            ContractKind::Ensures,
            ContractKind::Invariant,
            ContractKind::Decreases,
        ];
        for kind in kinds {
            let raw = RawSpec::new(kind, "x > 0", default_span());
            spec.add_raw(&raw).unwrap();
        }
        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(spec.invariants.len(), 1);
        assert_eq!(spec.decreases.len(), 1);
        assert_eq!(spec.len(), 4);
    }
}
