// trust-strengthen/spec_mining.rs: Specification mining from test cases
//
// Mines specifications from existing test cases. Tests encode implicit
// specifications -- assertions capture expected behavior. This module extracts
// those implicit specs and converts them into formal specifications.
//
// Inspired by Daikon (M. Ernst et al., "Dynamically discovering likely program
// invariants to support program evolution", IEEE TSE 2001) and QuickSpec
// (N. Smallbone et al., "Quick specifications for the busy programmer", JFP 2017).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A concrete value observed in a test case.
#[derive(Debug, Clone, PartialEq)]
pub enum TestValue {
    /// Signed integer value.
    Int(i64),
    /// Unsigned integer value.
    Uint(u64),
    /// Boolean value.
    Bool(bool),
    /// String value.
    Str(String),
    /// Floating-point value (no Eq -- PartialEq only).
    FloatVal(f64),
    /// A list of values.
    List(Vec<TestValue>),
    /// Absence of a value (None / null / unit).
    Nothing,
}

impl TestValue {
    /// Returns `true` if this value is a numeric zero.
    fn is_zero(&self) -> bool {
        match self {
            Self::Int(0) => true,
            Self::Uint(0) => true,
            Self::FloatVal(f) => *f == 0.0,
            _ => false,
        }
    }

    /// Returns this value as an i64 if it is an integer type.
    fn as_i64(&self) -> Option<i64> {
        match self {
            Self::Int(n) => Some(*n),
            Self::Uint(n) => i64::try_from(*n).ok(),
            _ => None,
        }
    }
}

/// The kind of assertion observed in a test.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AssertionKind {
    /// `assert_eq!` style equality check.
    Equality,
    /// `assert_ne!` style inequality check.
    Inequality,
    /// `assert!(a < b)` less-than check.
    LessThan,
    /// `assert!(a > b)` greater-than check.
    GreaterThan,
    /// `assert!(collection.contains(...))` containment check.
    Contains,
    /// `assert!(opt.is_none())` check.
    IsNone,
    /// `assert!(opt.is_some())` check.
    IsSome,
    /// `assert!(result.is_ok())` check.
    IsOk,
    /// `assert!(result.is_err())` check.
    IsErr,
    /// `#[should_panic]` or panic-expecting test.
    Panics,
}

/// A single assertion mined from a test.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MinedAssertion {
    /// The kind of assertion.
    pub kind: AssertionKind,
    /// The textual expression being asserted.
    pub expression: String,
    /// Source line number of the assertion.
    pub line: usize,
}

/// A test case from which specs are mined.
#[derive(Debug, Clone, PartialEq)]
pub struct TestCase {
    /// Name of the test function.
    pub name: String,
    /// Name of the function under test.
    pub function_under_test: String,
    /// Input values passed to the function.
    pub inputs: Vec<TestValue>,
    /// Expected output, if known.
    pub expected_output: Option<TestValue>,
    /// Assertions made in the test body.
    pub assertions: Vec<MinedAssertion>,
}

/// A specification mined from test observations.
///
/// Note: contains `f64` field (`confidence`) -- only derives `PartialEq`, not `Eq`.
#[derive(Debug, Clone, PartialEq)]
pub struct MinedSpec {
    /// The function this spec applies to.
    pub function_name: String,
    /// Precondition expressions (for native `requires ...` clauses).
    pub preconditions: Vec<String>,
    /// Postcondition expressions (for native `ensures ...` clauses).
    pub postconditions: Vec<String>,
    /// Confidence score in [0.0, 1.0].
    pub confidence: f64,
    /// Names of tests that support this spec.
    pub source_tests: Vec<String>,
}

// ---------------------------------------------------------------------------
// SpecMiner
// ---------------------------------------------------------------------------

/// Mines specifications from test case data.
///
/// Groups tests by function under test, extracts preconditions and
/// postconditions from assertion patterns, and generalizes across tests.
#[derive(Debug, Clone)]
pub struct SpecMiner {
    /// Minimum confidence threshold for emitted specs.
    min_confidence: f64,
}

impl SpecMiner {
    /// Creates a new `SpecMiner` with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self { min_confidence: 0.3 }
    }

    /// Mine specifications from a slice of test cases.
    ///
    /// Groups tests by `function_under_test`, extracts pre/postconditions,
    /// and generalizes across multiple tests.
    #[must_use]
    pub fn mine_from_tests(&self, tests: &[TestCase]) -> Vec<MinedSpec> {
        // Group tests by function under test
        let mut by_function: BTreeMap<&str, Vec<&TestCase>> = BTreeMap::new();
        for tc in tests {
            by_function.entry(&tc.function_under_test).or_default().push(tc);
        }

        let mut specs = Vec::new();

        for (func_name, func_tests) in by_function {
            let mut preconditions = Vec::new();
            let mut postconditions = Vec::new();
            let mut source_tests = Vec::new();

            for tc in &func_tests {
                preconditions.extend(self.extract_preconditions(tc));
                postconditions.extend(self.extract_postconditions(tc));
                source_tests.push(tc.name.clone());
            }

            // Deduplicate
            preconditions.sort();
            preconditions.dedup();
            postconditions.sort();
            postconditions.dedup();

            if preconditions.is_empty() && postconditions.is_empty() {
                continue;
            }

            let confidence = self.compute_confidence(&func_tests);

            if confidence >= self.min_confidence {
                specs.push(MinedSpec {
                    function_name: func_name.to_string(),
                    preconditions,
                    postconditions,
                    confidence,
                    source_tests,
                });
            }
        }

        specs
    }

    /// Extract precondition expressions from a single test case.
    ///
    /// Preconditions are inferred from:
    /// - Input values that are consistently non-zero across tests
    /// - Panic-expecting tests (negated panic condition)
    /// - Input bounds (positive values, bounded ranges)
    #[must_use]
    pub fn extract_preconditions(&self, test: &TestCase) -> Vec<String> {
        let mut preconds = Vec::new();

        // Check for panic-expecting assertions => negated panic is a precondition
        for assertion in &test.assertions {
            if assertion.kind == AssertionKind::Panics && !assertion.expression.is_empty() {
                preconds.push(format!("!({})", assertion.expression));
            }
        }

        // Infer non-zero preconditions from inputs when test expects errors
        let has_error_assertion = test
            .assertions
            .iter()
            .any(|a| a.kind == AssertionKind::Panics || a.kind == AssertionKind::IsErr);

        if has_error_assertion {
            for (idx, input) in test.inputs.iter().enumerate() {
                if input.is_zero() {
                    preconds.push(format!("param_{idx} != 0"));
                }
            }
        }

        // Infer positivity from input values
        for (idx, input) in test.inputs.iter().enumerate() {
            if let Some(val) = input.as_i64()
                && val > 0
                && !has_error_assertion
            {
                preconds.push(format!("param_{idx} > 0"));
            }
        }

        // Non-empty list preconditions
        for (idx, input) in test.inputs.iter().enumerate() {
            if let TestValue::List(items) = input
                && !items.is_empty()
                && !has_error_assertion
            {
                preconds.push(format!("param_{idx}.len() > 0"));
            }
        }

        preconds
    }

    /// Extract postcondition expressions from a single test case.
    ///
    /// Postconditions come from:
    /// - Equality assertions involving `result`
    /// - is_ok / is_some assertions
    /// - Comparison assertions (result > 0, etc.)
    #[must_use]
    pub fn extract_postconditions(&self, test: &TestCase) -> Vec<String> {
        let mut postconds = Vec::new();

        for assertion in &test.assertions {
            match &assertion.kind {
                AssertionKind::Equality if assertion.expression.contains("result") => {
                    // If expression mentions "result", it is a postcondition
                    postconds.push(assertion.expression.clone());
                }
                AssertionKind::IsOk => {
                    postconds.push("result.is_ok()".to_string());
                }
                AssertionKind::IsSome => {
                    postconds.push("result.is_some()".to_string());
                }
                AssertionKind::IsNone => {
                    postconds.push("result.is_none()".to_string());
                }
                AssertionKind::IsErr => {
                    postconds.push("result.is_err()".to_string());
                }
                AssertionKind::GreaterThan if assertion.expression.contains("result") => {
                    postconds.push(assertion.expression.clone());
                }
                AssertionKind::LessThan if assertion.expression.contains("result") => {
                    postconds.push(assertion.expression.clone());
                }
                AssertionKind::Contains if assertion.expression.contains("result") => {
                    postconds.push(assertion.expression.clone());
                }
                _ => {}
            }
        }

        // If there is an expected output, generate an equality postcondition
        if let Some(expected) = &test.expected_output {
            let val_str = format_test_value(expected);
            postconds.push(format!("result == {val_str}"));
        }

        postconds
    }

    /// Generalize specs by merging those that apply to the same function
    /// and removing overly-specific postconditions.
    #[must_use]
    pub fn generalize_specs(&self, specs: &[MinedSpec]) -> Vec<MinedSpec> {
        let mut by_function: BTreeMap<&str, Vec<&MinedSpec>> = BTreeMap::new();
        for spec in specs {
            by_function.entry(&spec.function_name).or_default().push(spec);
        }

        let mut result = Vec::new();

        for (func_name, func_specs) in by_function {
            if func_specs.len() == 1 {
                result.push(func_specs[0].clone());
                continue;
            }

            // Merge all specs for this function
            let mut merged = func_specs[0].clone();
            for spec in &func_specs[1..] {
                if let Some(m) = merge_specs(&merged, spec) {
                    merged = m;
                } else {
                    // Cannot merge -- keep function name consistent
                    merged.preconditions.extend(spec.preconditions.iter().cloned());
                    merged.postconditions.extend(spec.postconditions.iter().cloned());
                    merged.source_tests.extend(spec.source_tests.iter().cloned());
                    merged.confidence = (merged.confidence + spec.confidence) / 2.0;
                }
            }

            // Deduplicate
            merged.preconditions.sort();
            merged.preconditions.dedup();
            merged.postconditions.sort();
            merged.postconditions.dedup();
            merged.source_tests.sort();
            merged.source_tests.dedup();

            // Remove overly-specific postconditions (literal equality with constants)
            // if there are more general ones
            let has_general = merged
                .postconditions
                .iter()
                .any(|p| !p.starts_with("result == ") || p.contains("param_"));

            if has_general {
                merged.postconditions.retain(|p| {
                    !p.starts_with("result == ") || p.contains("param_") || p.contains("input")
                });
            }

            merged.function_name = func_name.to_string();
            result.push(merged);
        }

        result
    }

    /// Rank specs by confidence (descending). Returns indices into the input slice.
    #[must_use]
    pub fn rank_by_confidence(&self, specs: &[MinedSpec]) -> Vec<usize> {
        let mut indices: Vec<usize> = (0..specs.len()).collect();
        indices.sort_by(|&a, &b| {
            specs[b]
                .confidence
                .partial_cmp(&specs[a].confidence)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| compare_mined_specs(&specs[a], &specs[b]))
        });
        indices
    }

    /// Compute confidence for a set of tests for the same function.
    fn compute_confidence(&self, tests: &[&TestCase]) -> f64 {
        let test_count = tests.len() as f64;
        let assertion_count: usize = tests.iter().map(|t| t.assertions.len()).sum();

        // Base confidence from number of tests
        let test_factor = (test_count / 5.0).min(1.0) * 0.5;

        // Boost from assertions
        let assertion_factor = (assertion_count as f64 / 10.0).min(1.0) * 0.3;

        // Boost from having expected outputs
        let output_count = tests.iter().filter(|t| t.expected_output.is_some()).count() as f64;
        let output_factor = (output_count / test_count.max(1.0)).min(1.0) * 0.2;

        (test_factor + assertion_factor + output_factor).min(1.0)
    }
}

fn compare_mined_specs(a: &MinedSpec, b: &MinedSpec) -> std::cmp::Ordering {
    a.confidence
        .partial_cmp(&b.confidence)
        .unwrap_or(std::cmp::Ordering::Equal)
        .then_with(|| a.function_name.cmp(&b.function_name))
        .then_with(|| a.preconditions.cmp(&b.preconditions))
        .then_with(|| a.postconditions.cmp(&b.postconditions))
        .then_with(|| a.source_tests.cmp(&b.source_tests))
}

impl Default for SpecMiner {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Free functions
// ---------------------------------------------------------------------------

/// Merge two `MinedSpec`s for the same function.
///
/// Returns `Some(merged)` if both specs refer to the same function,
/// `None` otherwise.
#[must_use]
pub fn merge_specs(a: &MinedSpec, b: &MinedSpec) -> Option<MinedSpec> {
    if a.function_name != b.function_name {
        return None;
    }

    let mut preconditions = a.preconditions.clone();
    preconditions.extend(b.preconditions.iter().cloned());
    preconditions.sort();
    preconditions.dedup();

    let mut postconditions = a.postconditions.clone();
    postconditions.extend(b.postconditions.iter().cloned());
    postconditions.sort();
    postconditions.dedup();

    let mut source_tests = a.source_tests.clone();
    source_tests.extend(b.source_tests.iter().cloned());
    source_tests.sort();
    source_tests.dedup();

    // Average confidence weighted by number of source tests
    let total = (a.source_tests.len() + b.source_tests.len()).max(1) as f64;
    let confidence = (a.confidence * a.source_tests.len() as f64
        + b.confidence * b.source_tests.len() as f64)
        / total;

    Some(MinedSpec {
        function_name: a.function_name.clone(),
        preconditions,
        postconditions,
        confidence,
        source_tests,
    })
}

/// Format a `MinedSpec`'s preconditions as native signature clauses.
#[must_use]
pub fn format_as_requires(spec: &MinedSpec) -> Vec<String> {
    spec.preconditions.iter().map(|pre| format!("requires {}", pre.trim())).collect()
}

/// Format a `MinedSpec`'s postconditions as native signature clauses.
#[must_use]
pub fn format_as_ensures(spec: &MinedSpec) -> Vec<String> {
    spec.postconditions.iter().map(|post| format!("ensures {}", post.trim())).collect()
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Format a `TestValue` as a string for use in spec expressions.
fn format_test_value(val: &TestValue) -> String {
    match val {
        TestValue::Int(n) => n.to_string(),
        TestValue::Uint(n) => n.to_string(),
        TestValue::Bool(b) => b.to_string(),
        TestValue::Str(s) => format!("\"{s}\""),
        TestValue::FloatVal(f) => format!("{f}"),
        TestValue::List(items) => {
            let inner: Vec<String> = items.iter().map(format_test_value).collect();
            format!("[{}]", inner.join(", "))
        }
        TestValue::Nothing => "None".to_string(),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_test_case(
        name: &str,
        func: &str,
        inputs: Vec<TestValue>,
        expected: Option<TestValue>,
        assertions: Vec<MinedAssertion>,
    ) -> TestCase {
        TestCase {
            name: name.to_string(),
            function_under_test: func.to_string(),
            inputs,
            expected_output: expected,
            assertions,
        }
    }

    fn make_assertion(kind: AssertionKind, expr: &str, line: usize) -> MinedAssertion {
        MinedAssertion { kind, expression: expr.to_string(), line }
    }

    // --- SpecMiner::new ---

    #[test]
    fn test_miner_new_default() {
        let miner = SpecMiner::new();
        assert!(miner.min_confidence > 0.0);
        assert!(miner.min_confidence < 1.0);
    }

    // --- mine_from_tests ---

    #[test]
    fn test_mine_from_empty_tests() {
        let miner = SpecMiner::new();
        let specs = miner.mine_from_tests(&[]);
        assert!(specs.is_empty());
    }

    #[test]
    fn test_mine_from_single_test_with_equality() {
        let miner = SpecMiner::new();
        let tests = vec![make_test_case(
            "test_double",
            "double",
            vec![TestValue::Int(3)],
            Some(TestValue::Int(6)),
            vec![make_assertion(AssertionKind::Equality, "result == 2 * x", 10)],
        )];

        let specs = miner.mine_from_tests(&tests);
        assert!(!specs.is_empty());
        assert_eq!(specs[0].function_name, "double");
        assert!(!specs[0].postconditions.is_empty());
    }

    #[test]
    fn test_mine_groups_by_function() {
        let miner = SpecMiner::new();
        let tests = vec![
            make_test_case(
                "test_add_1",
                "add",
                vec![TestValue::Int(1), TestValue::Int(2)],
                Some(TestValue::Int(3)),
                vec![make_assertion(AssertionKind::IsOk, "", 5)],
            ),
            make_test_case(
                "test_sub_1",
                "sub",
                vec![TestValue::Int(5), TestValue::Int(3)],
                Some(TestValue::Int(2)),
                vec![make_assertion(AssertionKind::IsOk, "", 10)],
            ),
        ];

        let specs = miner.mine_from_tests(&tests);
        let func_names: Vec<&str> = specs.iter().map(|s| s.function_name.as_str()).collect();

        // Should have separate specs for each function
        assert!(func_names.contains(&"add") || func_names.contains(&"sub"));
    }

    #[test]
    fn test_mine_multiple_tests_for_same_function() {
        let miner = SpecMiner::new();
        let tests = vec![
            make_test_case(
                "test_abs_positive",
                "abs",
                vec![TestValue::Int(5)],
                Some(TestValue::Int(5)),
                vec![make_assertion(AssertionKind::GreaterThan, "result >= 0", 5)],
            ),
            make_test_case(
                "test_abs_negative",
                "abs",
                vec![TestValue::Int(-3)],
                Some(TestValue::Int(3)),
                vec![make_assertion(AssertionKind::GreaterThan, "result >= 0", 5)],
            ),
        ];

        let specs = miner.mine_from_tests(&tests);
        assert!(!specs.is_empty());

        let abs_spec = specs.iter().find(|s| s.function_name == "abs").unwrap();
        assert_eq!(abs_spec.source_tests.len(), 2);
    }

    // --- extract_preconditions ---

    #[test]
    fn test_extract_preconditions_from_panic() {
        let miner = SpecMiner::new();
        let tc = make_test_case(
            "test_div_by_zero",
            "divide",
            vec![TestValue::Int(10), TestValue::Int(0)],
            None,
            vec![make_assertion(AssertionKind::Panics, "division by zero", 15)],
        );

        let preconds = miner.extract_preconditions(&tc);
        assert!(preconds.iter().any(|p| p.contains("!(division by zero)")));
        // Also should detect zero input => param_1 != 0
        assert!(preconds.iter().any(|p| p.contains("param_1 != 0")));
    }

    #[test]
    fn test_extract_preconditions_positive_inputs() {
        let miner = SpecMiner::new();
        let tc = make_test_case(
            "test_sqrt",
            "sqrt",
            vec![TestValue::Int(9)],
            Some(TestValue::Int(3)),
            vec![],
        );

        let preconds = miner.extract_preconditions(&tc);
        assert!(preconds.iter().any(|p| p.contains("param_0 > 0")));
    }

    #[test]
    fn test_extract_preconditions_nonempty_list() {
        let miner = SpecMiner::new();
        let tc = make_test_case(
            "test_first",
            "first",
            vec![TestValue::List(vec![TestValue::Int(1), TestValue::Int(2)])],
            Some(TestValue::Int(1)),
            vec![],
        );

        let preconds = miner.extract_preconditions(&tc);
        assert!(preconds.iter().any(|p| p.contains("param_0.len() > 0")));
    }

    // --- extract_postconditions ---

    #[test]
    fn test_extract_postconditions_equality() {
        let miner = SpecMiner::new();
        let tc = make_test_case(
            "test_identity",
            "identity",
            vec![TestValue::Int(42)],
            None,
            vec![make_assertion(AssertionKind::Equality, "result == input", 10)],
        );

        let postconds = miner.extract_postconditions(&tc);
        assert!(postconds.iter().any(|p| p == "result == input"));
    }

    #[test]
    fn test_extract_postconditions_is_ok() {
        let miner = SpecMiner::new();
        let tc = make_test_case(
            "test_parse",
            "parse",
            vec![TestValue::Str("42".into())],
            None,
            vec![make_assertion(AssertionKind::IsOk, "", 8)],
        );

        let postconds = miner.extract_postconditions(&tc);
        assert!(postconds.contains(&"result.is_ok()".to_string()));
    }

    #[test]
    fn test_extract_postconditions_from_expected_output() {
        let miner = SpecMiner::new();
        let tc =
            make_test_case("test_constant", "get_answer", vec![], Some(TestValue::Int(42)), vec![]);

        let postconds = miner.extract_postconditions(&tc);
        assert!(postconds.iter().any(|p| p == "result == 42"));
    }

    // --- generalize_specs ---

    #[test]
    fn test_generalize_merges_same_function() {
        let miner = SpecMiner::new();
        let specs = vec![
            MinedSpec {
                function_name: "foo".into(),
                preconditions: vec!["x > 0".into()],
                postconditions: vec!["result >= 0".into()],
                confidence: 0.8,
                source_tests: vec!["test_1".into()],
            },
            MinedSpec {
                function_name: "foo".into(),
                preconditions: vec!["x < 100".into()],
                postconditions: vec!["result >= 0".into()],
                confidence: 0.7,
                source_tests: vec!["test_2".into()],
            },
        ];

        let generalized = miner.generalize_specs(&specs);
        assert_eq!(generalized.len(), 1);
        assert_eq!(generalized[0].function_name, "foo");
        assert!(generalized[0].preconditions.contains(&"x > 0".to_string()));
        assert!(generalized[0].preconditions.contains(&"x < 100".to_string()));
        assert_eq!(generalized[0].source_tests.len(), 2);
    }

    // --- rank_by_confidence ---

    #[test]
    fn test_rank_by_confidence_descending() {
        let miner = SpecMiner::new();
        let specs = vec![
            MinedSpec {
                function_name: "low".into(),
                preconditions: vec![],
                postconditions: vec!["result > 0".into()],
                confidence: 0.3,
                source_tests: vec!["t1".into()],
            },
            MinedSpec {
                function_name: "high".into(),
                preconditions: vec![],
                postconditions: vec!["result > 0".into()],
                confidence: 0.9,
                source_tests: vec!["t2".into()],
            },
            MinedSpec {
                function_name: "mid".into(),
                preconditions: vec![],
                postconditions: vec!["result > 0".into()],
                confidence: 0.6,
                source_tests: vec!["t3".into()],
            },
        ];

        let indices = miner.rank_by_confidence(&specs);
        assert_eq!(indices, vec![1, 2, 0]);
    }

    // --- merge_specs ---

    #[test]
    fn test_merge_specs_same_function() {
        let a = MinedSpec {
            function_name: "foo".into(),
            preconditions: vec!["x > 0".into()],
            postconditions: vec!["result > 0".into()],
            confidence: 0.8,
            source_tests: vec!["t1".into()],
        };
        let b = MinedSpec {
            function_name: "foo".into(),
            preconditions: vec!["x < 100".into()],
            postconditions: vec!["result < 200".into()],
            confidence: 0.6,
            source_tests: vec!["t2".into()],
        };

        let merged = merge_specs(&a, &b).unwrap();
        assert_eq!(merged.function_name, "foo");
        assert!(merged.preconditions.contains(&"x > 0".to_string()));
        assert!(merged.preconditions.contains(&"x < 100".to_string()));
        assert!(merged.postconditions.contains(&"result > 0".to_string()));
        assert!(merged.postconditions.contains(&"result < 200".to_string()));
        assert_eq!(merged.source_tests.len(), 2);
        // Weighted average: (0.8*1 + 0.6*1) / 2 = 0.7
        assert!((merged.confidence - 0.7).abs() < 0.01);
    }

    #[test]
    fn test_merge_specs_different_function_returns_none() {
        let a = MinedSpec {
            function_name: "foo".into(),
            preconditions: vec![],
            postconditions: vec![],
            confidence: 0.5,
            source_tests: vec![],
        };
        let b = MinedSpec {
            function_name: "bar".into(),
            preconditions: vec![],
            postconditions: vec![],
            confidence: 0.5,
            source_tests: vec![],
        };

        assert!(merge_specs(&a, &b).is_none());
    }

    // --- format_as_requires / format_as_ensures ---

    #[test]
    fn test_format_as_requires() {
        let spec = MinedSpec {
            function_name: "divide".into(),
            preconditions: vec!["divisor != 0".into(), "dividend >= 0".into()],
            postconditions: vec![],
            confidence: 0.9,
            source_tests: vec!["t1".into()],
        };

        let requires = format_as_requires(&spec);
        assert_eq!(requires.len(), 2);
        assert_eq!(requires[0], "requires divisor != 0");
        assert_eq!(requires[1], "requires dividend >= 0");
    }

    #[test]
    fn test_format_as_ensures() {
        let spec = MinedSpec {
            function_name: "abs".into(),
            preconditions: vec![],
            postconditions: vec!["result >= 0".into()],
            confidence: 0.85,
            source_tests: vec!["t1".into()],
        };

        let ensures = format_as_ensures(&spec);
        assert_eq!(ensures.len(), 1);
        assert_eq!(ensures[0], "ensures result >= 0");
    }

    #[test]
    fn test_format_empty_spec() {
        let spec = MinedSpec {
            function_name: "noop".into(),
            preconditions: vec![],
            postconditions: vec![],
            confidence: 0.5,
            source_tests: vec![],
        };

        assert!(format_as_requires(&spec).is_empty());
        assert!(format_as_ensures(&spec).is_empty());
    }

    // --- TestValue helpers ---

    #[test]
    fn test_value_is_zero() {
        assert!(TestValue::Int(0).is_zero());
        assert!(TestValue::Uint(0).is_zero());
        assert!(TestValue::FloatVal(0.0).is_zero());
        assert!(!TestValue::Int(1).is_zero());
        assert!(!TestValue::Bool(false).is_zero());
        assert!(!TestValue::Nothing.is_zero());
    }

    #[test]
    fn test_format_test_value() {
        assert_eq!(format_test_value(&TestValue::Int(42)), "42");
        assert_eq!(format_test_value(&TestValue::Uint(7)), "7");
        assert_eq!(format_test_value(&TestValue::Bool(true)), "true");
        assert_eq!(format_test_value(&TestValue::Str("hello".into())), "\"hello\"");
        assert_eq!(format_test_value(&TestValue::Nothing), "None");
        assert_eq!(
            format_test_value(&TestValue::List(vec![TestValue::Int(1), TestValue::Int(2)])),
            "[1, 2]"
        );
    }

    // --- Integration-style test: end-to-end mining ---

    #[test]
    fn test_end_to_end_divide_function() {
        let miner = SpecMiner::new();
        let tests = vec![
            make_test_case(
                "test_divide_ok",
                "divide",
                vec![TestValue::Int(10), TestValue::Int(2)],
                Some(TestValue::Int(5)),
                vec![make_assertion(AssertionKind::IsOk, "", 5)],
            ),
            make_test_case(
                "test_divide_by_zero_panics",
                "divide",
                vec![TestValue::Int(10), TestValue::Int(0)],
                None,
                vec![make_assertion(AssertionKind::Panics, "division by zero", 12)],
            ),
            make_test_case(
                "test_divide_negative",
                "divide",
                vec![TestValue::Int(-6), TestValue::Int(3)],
                Some(TestValue::Int(-2)),
                vec![make_assertion(AssertionKind::IsOk, "", 18)],
            ),
        ];

        let specs = miner.mine_from_tests(&tests);
        assert!(!specs.is_empty());

        let div_spec = specs.iter().find(|s| s.function_name == "divide").unwrap();
        assert_eq!(div_spec.source_tests.len(), 3);

        // Should have some preconditions (from panic test)
        assert!(
            !div_spec.preconditions.is_empty(),
            "should mine preconditions from panic test: {:?}",
            div_spec,
        );

        // Should have postconditions (from is_ok assertions and expected outputs)
        assert!(!div_spec.postconditions.is_empty(), "should mine postconditions: {:?}", div_spec,);

        // Formatting should work
        let requires = format_as_requires(div_spec);
        let ensures = format_as_ensures(div_spec);
        assert!(requires.iter().all(|r| r.starts_with("requires ")));
        assert!(ensures.iter().all(|e| e.starts_with("ensures ")));
    }
}
