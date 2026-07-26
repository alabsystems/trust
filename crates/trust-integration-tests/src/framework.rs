// trust-integration-tests/framework.rs: Integration test framework
//
// Provides a structured framework for writing cross-crate integration tests.
// Includes test harness, result collection, and assertion helpers.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::{
    Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition, VerificationResult,
};

// ---------------------------------------------------------------------------
// Test case types
// ---------------------------------------------------------------------------

/// A verification test case.
#[derive(Debug, Clone)]
pub(crate) struct VerificationTestCase {
    /// Name of the test case.
    pub name: String,
    /// Description.
    pub description: String,
    /// VCs to verify.
    pub vcs: Vec<VerificationCondition>,
    /// Expected outcomes per VC index.
    pub expected: Vec<ExpectedOutcome>,
}

/// Expected outcome for a VC.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpectedOutcome {
    /// VC should be proved.
    Proved,
    /// VC should fail (counterexample found).
    Failed,
    /// VC outcome is unknown/timeout.
    Unknown,
    /// Any outcome is acceptable.
    Any,
}

impl VerificationTestCase {
    /// Create a new test case with no expected outcomes (defaults to Any).
    pub(crate) fn new(name: impl Into<String>, description: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            description: description.into(),
            vcs: Vec::new(),
            expected: Vec::new(),
        }
    }

    /// Add a VC with an expected outcome.
    pub(crate) fn add_vc(&mut self, vc: VerificationCondition, expected: ExpectedOutcome) {
        self.vcs.push(vc);
        self.expected.push(expected);
    }

    /// Number of VCs in this test case.
    #[must_use]
    pub(crate) fn vc_count(&self) -> usize {
        self.vcs.len()
    }
}

// ---------------------------------------------------------------------------
// Test runner
// ---------------------------------------------------------------------------

/// Runs verification test cases and collects results.
pub(crate) struct TestRunner {
    /// Registered test cases.
    cases: Vec<VerificationTestCase>,
    /// Mock results (for testing the framework itself).
    injected_results: FxHashMap<String, Vec<VerificationResult>>,
}

impl TestRunner {
    pub(crate) fn new() -> Self {
        Self { cases: Vec::new(), injected_results: FxHashMap::default() }
    }

    /// Register a test case.
    pub(crate) fn add_case(&mut self, case: VerificationTestCase) {
        self.cases.push(case);
    }

    /// Set mock results for a test case name.
    pub(crate) fn set_injected_results(&mut self, name: &str, results: Vec<VerificationResult>) {
        self.injected_results.insert(name.to_string(), results);
    }

    /// Run all test cases and return results.
    pub(crate) fn run(&self) -> TestSuiteResult {
        let mut suite = TestSuiteResult {
            total: self.cases.len(),
            passed: 0,
            failed: 0,
            skipped: 0,
            results: Vec::new(),
        };

        for case in &self.cases {
            let result = self.run_case(case);
            if result.passed {
                suite.passed += 1;
            } else {
                suite.failed += 1;
            }
            suite.results.push(result);
        }

        suite
    }

    fn run_case(&self, case: &VerificationTestCase) -> TestCaseResult {
        let mock = self.injected_results.get(&case.name);

        let mut vc_results = Vec::new();
        let mut all_passed = true;

        for (i, (vc, expected)) in case.vcs.iter().zip(case.expected.iter()).enumerate() {
            let actual = mock.and_then(|m| m.get(i)).cloned().unwrap_or_else(|| {
                VerificationResult::Unknown {
                    solver: "constant-folder".into(),
                    time_ms: 0,
                    reason: "no mock result".into(),
                }
            });

            let matches = match expected {
                ExpectedOutcome::Any => true,
                ExpectedOutcome::Proved => matches!(actual, VerificationResult::Proved { .. }),
                ExpectedOutcome::Failed => matches!(actual, VerificationResult::Failed { .. }),
                ExpectedOutcome::Unknown => matches!(
                    actual,
                    VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. }
                ),
            };

            if !matches {
                all_passed = false;
            }

            vc_results.push(VcResult {
                vc_index: i,
                vc_kind: vc.kind.description().to_string(),
                expected: expected.clone(),
                actual,
                matches,
            });
        }

        TestCaseResult {
            name: case.name.clone(),
            description: case.description.clone(),
            passed: all_passed,
            vc_results,
        }
    }

    /// Number of registered test cases.
    #[must_use]
    pub(crate) fn case_count(&self) -> usize {
        self.cases.len()
    }
}

impl Default for TestRunner {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Result of running the entire test suite.
#[derive(Debug, Clone)]
pub struct TestSuiteResult {
    pub total: usize,
    pub passed: usize,
    pub failed: usize,
    pub skipped: usize,
    pub results: Vec<TestCaseResult>,
}

impl TestSuiteResult {
    /// Whether all tests passed.
    #[must_use]
    pub(crate) fn all_passed(&self) -> bool {
        self.failed == 0
    }

    /// Format a summary string.
    #[must_use]
    pub(crate) fn summary(&self) -> String {
        format!(
            "{} tests: {} passed, {} failed, {} skipped",
            self.total, self.passed, self.failed, self.skipped
        )
    }
}

/// Result of a single test case.
#[derive(Debug, Clone)]
pub struct TestCaseResult {
    pub name: String,
    pub description: String,
    pub passed: bool,
    pub vc_results: Vec<VcResult>,
}

/// Result of checking a single VC against expectations.
#[derive(Debug, Clone)]
pub struct VcResult {
    pub vc_index: usize,
    pub vc_kind: String,
    pub expected: ExpectedOutcome,
    pub actual: VerificationResult,
    pub matches: bool,
}

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

/// Create a simple VC for testing.
pub(crate) fn test_vc(kind: VcKind, function: &str) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    }
}

/// Create a "proved" result.
pub(crate) fn proved_result() -> VerificationResult {
    VerificationResult::Proved {
        solver: "test".into(),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

/// Create a "failed" result.
pub(crate) fn failed_result() -> VerificationResult {
    VerificationResult::Failed { solver: "test".into(), time_ms: 1, counterexample: None }
}

/// Create an "unknown" result.
pub(crate) fn unknown_result() -> VerificationResult {
    VerificationResult::Unknown { solver: "test".into(), time_ms: 1, reason: "test".into() }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_runner() {
        let runner = TestRunner::new();
        let result = runner.run();
        assert!(result.all_passed());
        assert_eq!(result.total, 0);
    }

    #[test]
    fn test_case_with_mock_proved() {
        let mut runner = TestRunner::new();
        let mut case = VerificationTestCase::new("div_test", "Test division safety");
        case.add_vc(test_vc(VcKind::DivisionByZero, "safe_div"), ExpectedOutcome::Proved);
        runner.add_case(case);
        runner.set_injected_results("div_test", vec![proved_result()]);

        let result = runner.run();
        assert!(result.all_passed());
        assert_eq!(result.passed, 1);
    }

    #[test]
    fn test_case_expected_fail_actual_proved() {
        let mut runner = TestRunner::new();
        let mut case = VerificationTestCase::new("fail_test", "Expect failure");
        case.add_vc(test_vc(VcKind::DivisionByZero, "f"), ExpectedOutcome::Failed);
        runner.add_case(case);
        runner.set_injected_results("fail_test", vec![proved_result()]);

        let result = runner.run();
        assert!(!result.all_passed());
        assert_eq!(result.failed, 1);
    }

    #[test]
    fn test_case_any_outcome() {
        let mut runner = TestRunner::new();
        let mut case = VerificationTestCase::new("any_test", "Any outcome");
        case.add_vc(test_vc(VcKind::DivisionByZero, "f"), ExpectedOutcome::Any);
        runner.add_case(case);
        runner.set_injected_results("any_test", vec![failed_result()]);

        let result = runner.run();
        assert!(result.all_passed());
    }

    #[test]
    fn test_multiple_vcs_in_case() {
        let mut runner = TestRunner::new();
        let mut case = VerificationTestCase::new("multi", "Multiple VCs");
        case.add_vc(test_vc(VcKind::DivisionByZero, "f"), ExpectedOutcome::Proved);
        case.add_vc(test_vc(VcKind::IndexOutOfBounds, "g"), ExpectedOutcome::Failed);
        assert_eq!(case.vc_count(), 2);

        runner.add_case(case);
        runner.set_injected_results("multi", vec![proved_result(), failed_result()]);

        let result = runner.run();
        assert!(result.all_passed());
    }

    #[test]
    fn test_no_mock_defaults_to_unknown() {
        let mut runner = TestRunner::new();
        let mut case = VerificationTestCase::new("no_mock", "No mock");
        case.add_vc(test_vc(VcKind::DivisionByZero, "f"), ExpectedOutcome::Unknown);
        runner.add_case(case);
        // No mock results set — defaults to Unknown

        let result = runner.run();
        assert!(result.all_passed());
    }

    #[test]
    fn test_suite_summary() {
        let mut runner = TestRunner::new();
        let mut c1 = VerificationTestCase::new("pass", "Should pass");
        c1.add_vc(test_vc(VcKind::DivisionByZero, "f"), ExpectedOutcome::Proved);
        runner.add_case(c1);

        let mut c2 = VerificationTestCase::new("fail", "Should fail");
        c2.add_vc(test_vc(VcKind::DivisionByZero, "g"), ExpectedOutcome::Failed);
        runner.add_case(c2);

        runner.set_injected_results("pass", vec![proved_result()]);
        runner.set_injected_results("fail", vec![proved_result()]); // Wrong — expect Failed

        let result = runner.run();
        assert_eq!(result.total, 2);
        assert_eq!(result.passed, 1);
        assert_eq!(result.failed, 1);
        let summary = result.summary();
        assert!(summary.contains("1 passed"));
        assert!(summary.contains("1 failed"));
    }

    #[test]
    fn test_case_count() {
        let mut runner = TestRunner::new();
        runner.add_case(VerificationTestCase::new("a", "A"));
        runner.add_case(VerificationTestCase::new("b", "B"));
        assert_eq!(runner.case_count(), 2);
    }

    #[test]
    fn test_helper_functions() {
        let vc = test_vc(VcKind::IndexOutOfBounds, "lookup");
        assert_eq!(vc.function, "lookup");

        assert!(matches!(proved_result(), VerificationResult::Proved { .. }));
        assert!(matches!(failed_result(), VerificationResult::Failed { .. }));
        assert!(matches!(unknown_result(), VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_vc_result_details() {
        let mut runner = TestRunner::new();
        let mut case = VerificationTestCase::new("detail", "Detail check");
        case.add_vc(test_vc(VcKind::DivisionByZero, "f"), ExpectedOutcome::Proved);
        runner.add_case(case);
        runner.set_injected_results("detail", vec![proved_result()]);

        let result = runner.run();
        let case_result = &result.results[0];
        assert!(case_result.passed);
        assert_eq!(case_result.vc_results.len(), 1);
        assert!(case_result.vc_results[0].matches);
    }
}
