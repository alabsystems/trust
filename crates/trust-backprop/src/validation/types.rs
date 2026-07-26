//! Core types for rewrite validation.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;
use std::time::Duration;

use serde::{Deserialize, Serialize};

/// Default timeout for `cargo test` execution during `TestsPass` validation.
pub(crate) const DEFAULT_TEST_TIMEOUT: Duration = Duration::from_secs(120);

/// Default timeout for `cargo check` execution during `SyntaxValid` validation.
pub(crate) const DEFAULT_COMPILE_CHECK_TIMEOUT: Duration = Duration::from_secs(60);

/// Configuration for rewrite validation.
///
/// Controls whether `TestsPass` validation uses actual `cargo test` execution
/// (when `crate_path` is set) or falls back to heuristic-only analysis.
/// Also controls whether `SyntaxValid` validation runs `cargo check` after
/// syn parsing succeeds.
#[derive(Debug, Clone)]
pub struct ValidationConfig {
    /// Path to the crate root directory (containing `Cargo.toml`).
    /// When set, `TestsPass` validation runs `cargo test` on this crate,
    /// and `SyntaxValid` validation runs `cargo check` after syn parsing.
    /// When `None`, falls back to heuristic/syn-only analysis.
    pub crate_path: Option<PathBuf>,
    /// Timeout for `cargo test` execution. Defaults to 120 seconds.
    /// If the test run exceeds this timeout, validation fails (fail-closed).
    pub test_timeout: Duration,
    /// Whether to run `cargo check` for `SyntaxValid` validation.
    /// Defaults to `true`. Set to `false` for performance-sensitive contexts
    /// where syn-only parsing is sufficient.
    pub compile_check_enabled: bool,
    /// Timeout for `cargo check` execution. Defaults to 60 seconds.
    pub compile_check_timeout: Duration,
}

impl Default for ValidationConfig {
    fn default() -> Self {
        Self {
            crate_path: None,
            test_timeout: DEFAULT_TEST_TIMEOUT,
            compile_check_enabled: true,
            compile_check_timeout: DEFAULT_COMPILE_CHECK_TIMEOUT,
        }
    }
}

impl ValidationConfig {
    /// Create a config with a crate path for actual test and compile-check execution.
    #[must_use]
    pub fn with_crate_path(crate_path: impl Into<PathBuf>) -> Self {
        Self {
            crate_path: Some(crate_path.into()),
            test_timeout: DEFAULT_TEST_TIMEOUT,
            compile_check_enabled: true,
            compile_check_timeout: DEFAULT_COMPILE_CHECK_TIMEOUT,
        }
    }

    /// Set the test execution timeout.
    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.test_timeout = timeout;
        self
    }

    /// Disable `cargo check` for `SyntaxValid` validation.
    ///
    /// Use this in performance-sensitive contexts where syn-only parsing
    /// is sufficient (e.g., tight inner loops of the backprop pipeline).
    #[must_use]
    pub fn without_compile_check(mut self) -> Self {
        self.compile_check_enabled = false;
        self
    }

    /// Set the `cargo check` execution timeout.
    #[must_use]
    pub fn with_compile_check_timeout(mut self, timeout: Duration) -> Self {
        self.compile_check_timeout = timeout;
        self
    }
}

/// A check that can be performed on a proposed rewrite.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ValidationCheck {
    /// The rewritten source must be syntactically valid Rust.
    SyntaxValid,
    /// The rewrite must not change the function's type signature.
    TypesPreserved,
    /// Tests must still pass after the rewrite.
    TestsPass,
    /// The rewrite must only strengthen specs (add preconditions/postconditions),
    /// never weaken them.
    SpecsStrengthen,
    /// The rewrite must not introduce new compiler warnings.
    NoNewWarnings,
    /// All spec formula bodies must parse into valid `Formula` values.
    FormulaValid,
    /// Inserted specs must only reference identifiers present in the function signature.
    TypeConsistency,
    /// Rewrites must be conservative: only add constraints, never modify or remove
    /// existing non-spec code.
    ConservativeStrengthening,
}

/// Result of validating a single check.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckResult {
    /// Which check was performed.
    pub check: ValidationCheck,
    /// Whether the check passed.
    pub passed: bool,
    /// Details about why it passed or failed.
    pub detail: String,
}

/// Result of validating a proposed rewrite.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationResult {
    /// Checks that passed.
    pub passed_checks: Vec<CheckResult>,
    /// Checks that failed.
    pub failed_checks: Vec<CheckResult>,
    /// Non-fatal warnings.
    pub warnings: Vec<String>,
}

impl ValidationResult {
    /// Whether all checks passed (no failures).
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.failed_checks.is_empty()
    }

    /// Total number of checks performed.
    #[must_use]
    pub fn total_checks(&self) -> usize {
        self.passed_checks.len() + self.failed_checks.len()
    }
}

/// A simplified AST node for structural comparison.
///
/// This is not a full Rust AST -- it captures the structural elements
/// relevant to semantic preservation: function signatures, control flow,
/// and expressions (excluding spec attributes and assertions).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AstNode {
    /// A function definition.
    Function { name: String, params: Vec<String>, return_type: Option<String>, body: Vec<AstNode> },
    /// An attribute (e.g., `#[requires(...)]`).
    Attribute { text: String },
    /// A statement (simplified: just the text).
    Statement { text: String },
    /// A block expression `{ ... }`.
    Block { children: Vec<AstNode> },
    /// An if expression.
    If { condition: String, then_branch: Box<AstNode>, else_branch: Option<Box<AstNode>> },
    /// A loop/while/for expression.
    Loop { body: Box<AstNode> },
    /// A return expression.
    Return { expr: Option<String> },
    /// An expression that does not fit the other categories.
    Expr { text: String },
}

/// Result of a semantic preservation check.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SemanticDiff {
    /// Nodes added in the rewrite (not present in original).
    pub added: Vec<AstNode>,
    /// Nodes removed in the rewrite (present in original but not rewrite).
    pub removed: Vec<AstNode>,
    /// Whether the diff preserves semantics (only additive spec changes).
    pub preserves_semantics: bool,
    /// Human-readable summary of the diff.
    pub summary: String,
}
