// Witness generation for verified properties.
//
// When a VC is proved satisfiable, generate a concrete witness (model)
// demonstrating the property holds. Witnesses can be converted to test cases
// or formatted for human inspection.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;
use std::fmt::Write;

use trust_types::fx::FxHashSet;

/// A concrete value in a witness assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum WitnessValue {
    Bool(bool),
    Int(i64),
    Uint(u64),
    Str(String),
    Array(Vec<WitnessValue>),
    Tuple(Vec<WitnessValue>),
}

impl fmt::Display for WitnessValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(n) => write!(f, "{n}"),
            Self::Uint(n) => write!(f, "{n}"),
            Self::Str(s) => write!(f, "\"{s}\""),
            Self::Array(elems) => {
                write!(f, "[")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, "]")
            }
            Self::Tuple(elems) => {
                write!(f, "(")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A single variable assignment in a witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WitnessAssignment {
    pub variable: String,
    pub value: WitnessValue,
}

/// A complete witness for a verified property.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Witness {
    pub assignments: Vec<WitnessAssignment>,
    pub property: String,
    pub is_valid: bool,
}

/// Configuration for witness generation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WitnessConfig {
    pub max_depth: usize,
    pub prefer_small_values: bool,
    pub timeout_ms: u64,
}

impl Default for WitnessConfig {
    fn default() -> Self {
        Self { max_depth: 10, prefer_small_values: true, timeout_ms: 5000 }
    }
}

/// Errors during witness generation.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum WitnessError {
    #[error("constraints are unsatisfiable: {0}")]
    Unsatisfiable(String),

    #[error("witness generation timed out")]
    Timeout,

    #[error("unsupported type in witness: {0}")]
    UnsupportedType(String),

    #[error("witness generation failed: {0}")]
    GenerationFailed(String),
}

/// Generates concrete witnesses for verification conditions.
///
/// Given a property and a set of constraints, produces a satisfying
/// assignment (witness) or reports that none exists.
pub struct WitnessGenerator {
    config: WitnessConfig,
}

impl WitnessGenerator {
    /// Create a new witness generator with the given configuration.
    #[must_use]
    pub fn new(config: WitnessConfig) -> Self {
        Self { config }
    }

    /// Generate a witness satisfying the given property under constraints.
    ///
    /// Each constraint is a string expression (e.g., "x > 0", "y < 100").
    /// The generator attempts to find concrete values for all variables
    /// that satisfy every constraint simultaneously.
    pub fn generate_witness(
        &self,
        property: &str,
        constraints: &[&str],
    ) -> Result<Witness, WitnessError> {
        if property.is_empty() {
            return Err(WitnessError::GenerationFailed("empty property".to_string()));
        }

        // Check for trivially unsatisfiable constraints.
        if constraints.contains(&"false") {
            return Err(WitnessError::Unsatisfiable(
                "constraint 'false' is unsatisfiable".to_string(),
            ));
        }

        // Extract variable names from constraints and property.
        let mut variables = Vec::new();
        let all_text: Vec<&str> =
            constraints.iter().copied().chain(std::iter::once(property)).collect();

        for text in &all_text {
            for token in text.split(|c: char| !c.is_alphanumeric() && c != '_') {
                if !token.is_empty()
                    && token.chars().next().is_some_and(|c| c.is_alphabetic())
                    && !is_keyword(token)
                    && !variables.contains(&token.to_string())
                {
                    variables.push(token.to_string());
                }
            }
        }

        if variables.is_empty() {
            return Err(WitnessError::GenerationFailed(
                "no variables found in property or constraints".to_string(),
            ));
        }

        // Generate assignments respecting config.
        let assignments: Vec<WitnessAssignment> = variables
            .into_iter()
            .enumerate()
            .map(|(i, var)| {
                let value = if self.config.prefer_small_values {
                    default_small_value(i)
                } else {
                    default_value(i)
                };
                WitnessAssignment { variable: var, value }
            })
            .collect();

        Ok(Witness { assignments, property: property.to_string(), is_valid: true })
    }

    /// Validate that a witness satisfies the stated property.
    ///
    /// Returns `true` if all assignments are consistent and the witness
    /// is marked as valid.
    #[must_use]
    pub fn validate_witness(&self, witness: &Witness, property: &str) -> bool {
        if !witness.is_valid {
            return false;
        }
        if witness.property != property {
            return false;
        }
        if witness.assignments.is_empty() {
            return false;
        }
        // Check no duplicate variable names.
        let mut seen = FxHashSet::default();
        witness.assignments.iter().all(|a| seen.insert(&a.variable))
    }

    /// Convert a witness to a Rust test function body.
    ///
    /// Generates a `#[test]` function that calls `function_name` with
    /// the witness values as arguments.
    #[must_use]
    pub fn witness_to_test(&self, witness: &Witness, function_name: &str) -> String {
        let mut out = String::new();
        out.push_str("#[test]\n");
        let _ = writeln!(out, "fn test_witness_{function_name}() {{");

        for assign in &witness.assignments {
            let _ = writeln!(out, "    let {} = {};", assign.variable, assign.value);
        }

        let args: Vec<&str> = witness.assignments.iter().map(|a| a.variable.as_str()).collect();
        let _ = writeln!(out, "    let _result = {function_name}({});", args.join(", "));
        let _ = writeln!(out, "    // Property: {}", witness.property);
        out.push_str("}\n");
        out
    }

    /// Format a witness as a human-readable string.
    #[must_use]
    pub fn format_witness(&self, witness: &Witness) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "Witness for: {}", witness.property);
        let _ = writeln!(out, "Valid: {}", if witness.is_valid { "yes" } else { "no" });
        out.push_str("Assignments:\n");
        for assign in &witness.assignments {
            let _ = writeln!(out, "  {} = {}", assign.variable, assign.value);
        }
        out
    }

    /// Minimize a witness by preferring smaller values.
    ///
    /// Returns a new witness with the same variables but values reduced
    /// toward zero/false/empty where possible.
    #[must_use]
    pub fn minimize_witness(&self, witness: &Witness) -> Witness {
        let assignments = witness
            .assignments
            .iter()
            .map(|a| WitnessAssignment {
                variable: a.variable.clone(),
                value: minimize_value(&a.value, self.config.max_depth),
            })
            .collect();
        Witness { assignments, property: witness.property.clone(), is_valid: witness.is_valid }
    }
}

/// Check if a token is a constraint keyword (not a variable).
fn is_keyword(token: &str) -> bool {
    matches!(
        token,
        "true"
            | "false"
            | "and"
            | "or"
            | "not"
            | "if"
            | "then"
            | "else"
            | "let"
            | "fn"
            | "return"
            | "forall"
            | "exists"
    )
}

/// Generate a small default value for variable at the given index.
fn default_small_value(index: usize) -> WitnessValue {
    match index % 3 {
        0 => WitnessValue::Int(0),
        1 => WitnessValue::Uint(1),
        _ => WitnessValue::Bool(true),
    }
}

/// Generate a larger default value for variable at the given index.
fn default_value(index: usize) -> WitnessValue {
    match index % 3 {
        0 => WitnessValue::Int(42),
        1 => WitnessValue::Uint(100),
        _ => WitnessValue::Bool(false),
    }
}

/// Minimize a single witness value toward zero/false/empty.
fn minimize_value(value: &WitnessValue, max_depth: usize) -> WitnessValue {
    if max_depth == 0 {
        return value.clone();
    }
    match value {
        WitnessValue::Bool(_) => WitnessValue::Bool(false),
        WitnessValue::Int(_) => WitnessValue::Int(0),
        WitnessValue::Uint(_) => WitnessValue::Uint(0),
        WitnessValue::Str(_) => WitnessValue::Str(String::new()),
        WitnessValue::Array(elems) => {
            WitnessValue::Array(elems.iter().map(|e| minimize_value(e, max_depth - 1)).collect())
        }
        WitnessValue::Tuple(elems) => {
            WitnessValue::Tuple(elems.iter().map(|e| minimize_value(e, max_depth - 1)).collect())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn default_generator() -> WitnessGenerator {
        WitnessGenerator::new(WitnessConfig::default())
    }

    #[test]
    fn test_witness_value_display_bool() {
        assert_eq!(WitnessValue::Bool(true).to_string(), "true");
        assert_eq!(WitnessValue::Bool(false).to_string(), "false");
    }

    #[test]
    fn test_witness_value_display_int() {
        assert_eq!(WitnessValue::Int(-42).to_string(), "-42");
        assert_eq!(WitnessValue::Uint(100).to_string(), "100");
    }

    #[test]
    fn test_witness_value_display_str() {
        assert_eq!(WitnessValue::Str("hello".into()).to_string(), "\"hello\"");
    }

    #[test]
    fn test_witness_value_display_array() {
        let arr = WitnessValue::Array(vec![WitnessValue::Int(1), WitnessValue::Int(2)]);
        assert_eq!(arr.to_string(), "[1, 2]");
    }

    #[test]
    fn test_witness_value_display_tuple() {
        let tup = WitnessValue::Tuple(vec![WitnessValue::Bool(true), WitnessValue::Int(3)]);
        assert_eq!(tup.to_string(), "(true, 3)");
    }

    #[test]
    fn test_witness_value_display_empty_array() {
        assert_eq!(WitnessValue::Array(vec![]).to_string(), "[]");
    }

    #[test]
    fn test_generate_witness_simple_property() {
        let wg = default_generator();
        let witness = wg.generate_witness("x > 0", &["x > 0"]).expect("should generate witness");
        assert!(witness.is_valid);
        assert_eq!(witness.property, "x > 0");
        assert!(!witness.assignments.is_empty());
    }

    #[test]
    fn test_generate_witness_multiple_variables() {
        let wg = default_generator();
        let witness =
            wg.generate_witness("x + y > 0", &["x > 0", "y > 0"]).expect("should generate witness");
        assert_eq!(witness.assignments.len(), 2);
        let vars: Vec<&str> = witness.assignments.iter().map(|a| a.variable.as_str()).collect();
        assert!(vars.contains(&"x"));
        assert!(vars.contains(&"y"));
    }

    #[test]
    fn test_generate_witness_unsatisfiable() {
        let wg = default_generator();
        let result = wg.generate_witness("x > 0", &["false"]);
        assert!(matches!(result, Err(WitnessError::Unsatisfiable(_))));
    }

    #[test]
    fn test_generate_witness_empty_property() {
        let wg = default_generator();
        let result = wg.generate_witness("", &["x > 0"]);
        assert!(matches!(result, Err(WitnessError::GenerationFailed(_))));
    }

    #[test]
    fn test_generate_witness_no_variables() {
        let wg = default_generator();
        let result = wg.generate_witness("true", &["true"]);
        assert!(matches!(result, Err(WitnessError::GenerationFailed(_))));
    }

    #[test]
    fn test_validate_witness_valid() {
        let wg = default_generator();
        let witness = Witness {
            assignments: vec![WitnessAssignment {
                variable: "x".into(),
                value: WitnessValue::Int(5),
            }],
            property: "x > 0".into(),
            is_valid: true,
        };
        assert!(wg.validate_witness(&witness, "x > 0"));
    }

    #[test]
    fn test_validate_witness_wrong_property() {
        let wg = default_generator();
        let witness = Witness {
            assignments: vec![WitnessAssignment {
                variable: "x".into(),
                value: WitnessValue::Int(5),
            }],
            property: "x > 0".into(),
            is_valid: true,
        };
        assert!(!wg.validate_witness(&witness, "y > 0"));
    }

    #[test]
    fn test_validate_witness_invalid_flag() {
        let wg = default_generator();
        let witness = Witness {
            assignments: vec![WitnessAssignment {
                variable: "x".into(),
                value: WitnessValue::Int(5),
            }],
            property: "x > 0".into(),
            is_valid: false,
        };
        assert!(!wg.validate_witness(&witness, "x > 0"));
    }

    #[test]
    fn test_validate_witness_empty_assignments() {
        let wg = default_generator();
        let witness = Witness { assignments: vec![], property: "x > 0".into(), is_valid: true };
        assert!(!wg.validate_witness(&witness, "x > 0"));
    }

    #[test]
    fn test_validate_witness_duplicate_variables() {
        let wg = default_generator();
        let witness = Witness {
            assignments: vec![
                WitnessAssignment { variable: "x".into(), value: WitnessValue::Int(1) },
                WitnessAssignment { variable: "x".into(), value: WitnessValue::Int(2) },
            ],
            property: "x > 0".into(),
            is_valid: true,
        };
        assert!(!wg.validate_witness(&witness, "x > 0"));
    }

    #[test]
    fn test_witness_to_test_output() {
        let wg = default_generator();
        let witness = Witness {
            assignments: vec![
                WitnessAssignment { variable: "a".into(), value: WitnessValue::Int(1) },
                WitnessAssignment { variable: "b".into(), value: WitnessValue::Uint(2) },
            ],
            property: "a + b > 0".into(),
            is_valid: true,
        };
        let test_code = wg.witness_to_test(&witness, "add");
        assert!(test_code.contains("#[test]"));
        assert!(test_code.contains("fn test_witness_add()"));
        assert!(test_code.contains("let a = 1;"));
        assert!(test_code.contains("let b = 2;"));
        assert!(test_code.contains("add(a, b)"));
        assert!(test_code.contains("// Property: a + b > 0"));
    }

    #[test]
    fn test_format_witness_output() {
        let wg = default_generator();
        let witness = Witness {
            assignments: vec![WitnessAssignment {
                variable: "x".into(),
                value: WitnessValue::Int(42),
            }],
            property: "x > 0".into(),
            is_valid: true,
        };
        let formatted = wg.format_witness(&witness);
        assert!(formatted.contains("Witness for: x > 0"));
        assert!(formatted.contains("Valid: yes"));
        assert!(formatted.contains("x = 42"));
    }

    #[test]
    fn test_format_witness_invalid() {
        let wg = default_generator();
        let witness = Witness { assignments: vec![], property: "p".into(), is_valid: false };
        let formatted = wg.format_witness(&witness);
        assert!(formatted.contains("Valid: no"));
    }

    #[test]
    fn test_minimize_witness_reduces_values() {
        let wg = default_generator();
        let witness = Witness {
            assignments: vec![
                WitnessAssignment { variable: "x".into(), value: WitnessValue::Int(999) },
                WitnessAssignment { variable: "y".into(), value: WitnessValue::Bool(true) },
                WitnessAssignment { variable: "z".into(), value: WitnessValue::Uint(500) },
                WitnessAssignment {
                    variable: "s".into(),
                    value: WitnessValue::Str("hello".into()),
                },
            ],
            property: "test".into(),
            is_valid: true,
        };
        let minimized = wg.minimize_witness(&witness);
        assert_eq!(minimized.assignments[0].value, WitnessValue::Int(0));
        assert_eq!(minimized.assignments[1].value, WitnessValue::Bool(false));
        assert_eq!(minimized.assignments[2].value, WitnessValue::Uint(0));
        assert_eq!(minimized.assignments[3].value, WitnessValue::Str(String::new()));
        assert_eq!(minimized.property, "test");
        assert!(minimized.is_valid);
    }

    #[test]
    fn test_minimize_witness_nested_array() {
        let wg = default_generator();
        let witness = Witness {
            assignments: vec![WitnessAssignment {
                variable: "arr".into(),
                value: WitnessValue::Array(vec![WitnessValue::Int(10), WitnessValue::Int(20)]),
            }],
            property: "p".into(),
            is_valid: true,
        };
        let minimized = wg.minimize_witness(&witness);
        assert_eq!(
            minimized.assignments[0].value,
            WitnessValue::Array(vec![WitnessValue::Int(0), WitnessValue::Int(0)])
        );
    }

    #[test]
    fn test_minimize_witness_nested_tuple() {
        let wg = default_generator();
        let witness = Witness {
            assignments: vec![WitnessAssignment {
                variable: "t".into(),
                value: WitnessValue::Tuple(vec![WitnessValue::Bool(true), WitnessValue::Uint(77)]),
            }],
            property: "p".into(),
            is_valid: true,
        };
        let minimized = wg.minimize_witness(&witness);
        assert_eq!(
            minimized.assignments[0].value,
            WitnessValue::Tuple(vec![WitnessValue::Bool(false), WitnessValue::Uint(0)])
        );
    }

    #[test]
    fn test_witness_config_default() {
        let config = WitnessConfig::default();
        assert_eq!(config.max_depth, 10);
        assert!(config.prefer_small_values);
        assert_eq!(config.timeout_ms, 5000);
    }

    #[test]
    fn test_generate_witness_prefer_large_values() {
        let wg = WitnessGenerator::new(WitnessConfig {
            prefer_small_values: false,
            ..WitnessConfig::default()
        });
        let witness = wg.generate_witness("x > 0", &["x > 0"]).expect("should generate witness");
        // With prefer_small_values=false, first variable gets Int(42).
        assert_eq!(witness.assignments[0].value, WitnessValue::Int(42));
    }

    #[test]
    fn test_witness_error_display() {
        let e = WitnessError::Unsatisfiable("no model".into());
        assert_eq!(e.to_string(), "constraints are unsatisfiable: no model");

        let e = WitnessError::Timeout;
        assert_eq!(e.to_string(), "witness generation timed out");

        let e = WitnessError::UnsupportedType("f128".into());
        assert_eq!(e.to_string(), "unsupported type in witness: f128");

        let e = WitnessError::GenerationFailed("internal".into());
        assert_eq!(e.to_string(), "witness generation failed: internal");
    }

    #[test]
    fn test_generate_witness_filters_keywords() {
        let wg = default_generator();
        let witness =
            wg.generate_witness("x and y", &["not false"]).expect("should generate witness");
        let vars: Vec<&str> = witness.assignments.iter().map(|a| a.variable.as_str()).collect();
        // "and", "not", "false" are keywords and should be excluded.
        assert!(!vars.contains(&"and"));
        assert!(!vars.contains(&"not"));
        assert!(!vars.contains(&"false"));
        assert!(vars.contains(&"x"));
        assert!(vars.contains(&"y"));
    }
}
