// trust-strengthen/spec_quality.rs: Specification quality metrics
//
// Metrics for evaluating specification quality across multiple dimensions:
// completeness, precision, minimality, consistency, and coverage.
// Used by the strengthen loop to assess and improve generated specifications.
//
// Part of #352
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// The kind of quality metric being measured.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MetricKind {
    /// Does the spec cover all relevant behaviors?
    Completeness,
    /// Is the spec tight enough to reject invalid inputs?
    Precision,
    /// Is the spec free of redundant clauses?
    Minimality,
    /// Are preconditions and postconditions mutually consistent?
    Consistency,
    /// What fraction of execution paths does the spec address?
    Coverage,
}

impl MetricKind {
    /// Return all metric kinds in canonical order.
    #[must_use]
    pub fn all() -> &'static [MetricKind] {
        &[
            MetricKind::Completeness,
            MetricKind::Precision,
            MetricKind::Minimality,
            MetricKind::Consistency,
            MetricKind::Coverage,
        ]
    }

    /// Human-readable label for this metric.
    #[must_use]
    pub fn label(&self) -> &'static str {
        match self {
            MetricKind::Completeness => "completeness",
            MetricKind::Precision => "precision",
            MetricKind::Minimality => "minimality",
            MetricKind::Consistency => "consistency",
            MetricKind::Coverage => "coverage",
        }
    }
}

/// A single quality score for one metric dimension.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QualityScore {
    /// Which metric this score measures.
    pub kind: MetricKind,
    /// Achieved value (0..=max_value).
    pub value: u32,
    /// Maximum possible value for this metric.
    pub max_value: u32,
    /// Human-readable explanation of how the score was computed.
    pub details: String,
}

impl QualityScore {
    /// Create a new quality score.
    #[must_use]
    pub fn new(kind: MetricKind, value: u32, max_value: u32, details: impl Into<String>) -> Self {
        Self { kind, value: value.min(max_value), max_value, details: details.into() }
    }

    /// Score as a percentage (0..=100).
    #[must_use]
    pub fn percentage(&self) -> u32 {
        if self.max_value == 0 {
            return 0;
        }
        (self.value * 100) / self.max_value
    }
}

/// Aggregated quality metrics across all dimensions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QualityMetrics {
    /// Individual dimension scores.
    pub scores: Vec<QualityScore>,
    /// Sum of all dimension values.
    pub overall_score: u32,
    /// Sum of all dimension max values.
    pub max_score: u32,
}

impl QualityMetrics {
    /// Build metrics from a list of scores, computing aggregates.
    #[must_use]
    pub fn from_scores(scores: Vec<QualityScore>) -> Self {
        let overall_score = scores.iter().map(|s| s.value).sum();
        let max_score = scores.iter().map(|s| s.max_value).sum();
        Self { scores, overall_score, max_score }
    }

    /// Overall percentage (0..=100).
    #[must_use]
    pub fn overall_percentage(&self) -> u32 {
        if self.max_score == 0 {
            return 0;
        }
        (self.overall_score * 100) / self.max_score
    }

    /// Look up a score by metric kind.
    #[must_use]
    pub fn score_for(&self, kind: MetricKind) -> Option<&QualityScore> {
        self.scores.iter().find(|s| s.kind == kind)
    }
}

/// Coverage analysis result for a specification against execution paths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecCoverage {
    /// Total number of execution paths analyzed.
    pub total_paths: usize,
    /// Number of paths addressed by the specification.
    pub covered_paths: usize,
    /// Variables that appear in execution paths but not in the specification.
    pub uncovered_variables: Vec<String>,
}

impl SpecCoverage {
    /// Fraction of paths covered (0..=100 as u32).
    #[must_use]
    pub fn coverage_percentage(&self) -> u32 {
        if self.total_paths == 0 {
            return 0;
        }
        ((self.covered_paths * 100) / self.total_paths) as u32
    }
}

/// Configuration for quality evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QualityConfig {
    /// Whether to evaluate completeness.
    pub check_completeness: bool,
    /// Whether to evaluate precision.
    pub check_precision: bool,
    /// Whether to evaluate minimality.
    pub check_minimality: bool,
    /// Minimum acceptable overall score (0..=100).
    pub min_acceptable_score: u32,
}

impl Default for QualityConfig {
    fn default() -> Self {
        Self {
            check_completeness: true,
            check_precision: true,
            check_minimality: true,
            min_acceptable_score: 50,
        }
    }
}

/// Report summarizing the quality of a specification for one function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QualityReport {
    /// Name of the function being evaluated.
    pub function_name: String,
    /// Aggregated quality metrics.
    pub metrics: QualityMetrics,
    /// Suggested improvements.
    pub suggestions: Vec<String>,
    /// Whether the spec meets the configured threshold.
    pub passes_threshold: bool,
}

/// Evaluates specification quality across multiple dimensions.
#[derive(Debug, Clone)]
pub struct QualityEvaluator {
    config: QualityConfig,
}

impl QualityEvaluator {
    /// Create a new evaluator with the given configuration.
    #[must_use]
    pub fn new(config: QualityConfig) -> Self {
        Self { config }
    }

    /// Evaluate the quality of a specification against a function body.
    ///
    /// The `spec` is the specification text (requires/ensures clauses).
    /// The `function_body` is the source of the function being specified.
    #[must_use]
    pub fn evaluate_spec(&self, spec: &str, function_body: &str) -> QualityReport {
        let mut scores = Vec::new();

        if self.config.check_completeness {
            scores.push(self.completeness_score(spec, function_body));
        }
        if self.config.check_precision {
            scores.push(self.precision_score(spec, function_body));
        }
        if self.config.check_minimality {
            scores.push(self.minimality_score(spec));
        }

        // Always check consistency and coverage.
        scores.push(self.consistency_score(spec));
        scores.push(self.coverage_score_from_body(spec, function_body));

        let metrics = QualityMetrics::from_scores(scores);
        let passes_threshold = metrics.overall_percentage() >= self.config.min_acceptable_score;

        let report = QualityReport {
            function_name: String::new(),
            metrics,
            suggestions: Vec::new(),
            passes_threshold,
        };

        let suggestions = self.suggest_improvements(&report);
        QualityReport { suggestions, ..report }
    }

    /// Analyze how well a specification covers the given execution paths.
    ///
    /// Each path is a string describing a branch (e.g., "x > 0", "x == 0").
    /// A path is "covered" if the spec mentions any variable from that path.
    #[must_use]
    pub fn coverage_analysis(&self, spec: &str, paths: &[&str]) -> SpecCoverage {
        let spec_lower = spec.to_lowercase();
        let mut covered = 0;
        let mut all_vars: Vec<String> = Vec::new();

        for path in paths {
            // Extract variable-like tokens from the path.
            let vars: Vec<String> = extract_identifiers(path);
            let path_covered = vars.iter().any(|v| spec_lower.contains(&v.to_lowercase()));
            if path_covered {
                covered += 1;
            }
            for v in &vars {
                if !spec_lower.contains(&v.to_lowercase()) && !all_vars.contains(v) {
                    all_vars.push(v.clone());
                }
            }
        }

        SpecCoverage {
            total_paths: paths.len(),
            covered_paths: covered,
            uncovered_variables: all_vars,
        }
    }

    /// Check for redundant preconditions.
    ///
    /// Returns pairs of indices into `preconditions` where one implies the other
    /// (textual subsumption heuristic: if one clause is a substring of another).
    #[must_use]
    pub fn redundancy_check(&self, preconditions: &[&str]) -> Vec<(usize, usize)> {
        let mut pairs = Vec::new();
        for i in 0..preconditions.len() {
            for j in (i + 1)..preconditions.len() {
                let a = preconditions[i].trim();
                let b = preconditions[j].trim();
                // Textual subsumption or exact duplicate after normalization.
                if a.contains(b) || b.contains(a) || normalize_clause(a) == normalize_clause(b) {
                    pairs.push((i, j));
                }
            }
        }
        pairs
    }

    /// Compute the minimality score for a specification.
    ///
    /// Penalizes long specs, duplicate clauses, and redundant conjuncts.
    #[must_use]
    pub fn minimality_score(&self, spec: &str) -> QualityScore {
        let clauses: Vec<&str> = spec
            .split("&&")
            .chain(spec.split(','))
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .collect();

        let max_val = 100u32;

        if clauses.is_empty() {
            return QualityScore::new(MetricKind::Minimality, 0, max_val, "Empty specification");
        }

        // Check for duplicates.
        let mut normalized: Vec<String> = clauses.iter().map(|c| normalize_clause(c)).collect();
        let total = normalized.len() as u32;
        normalized.sort();
        normalized.dedup();
        let unique = normalized.len() as u32;
        let dup_penalty = (total - unique) * 15;

        // Penalize excessive length (diminishing returns past 5 clauses).
        let length_penalty = if total > 5 { (total - 5) * 10 } else { 0 };

        let score = max_val.saturating_sub(dup_penalty).saturating_sub(length_penalty);

        let details = format!(
            "{total} clauses ({unique} unique), dup_penalty={dup_penalty}, length_penalty={length_penalty}"
        );
        QualityScore::new(MetricKind::Minimality, score, max_val, details)
    }

    /// Compare two specifications and return a brief description of which is stronger.
    ///
    /// "Stronger" means more clauses (higher completeness) without redundancy.
    #[must_use]
    pub fn compare_specs(&self, a: &str, b: &str) -> String {
        let score_a = self.minimality_score(a);
        let score_b = self.minimality_score(b);
        let clauses_a = count_clauses(a);
        let clauses_b = count_clauses(b);

        if clauses_a == clauses_b && score_a.value == score_b.value {
            return "Specs are equivalent in strength and minimality.".to_string();
        }

        // Higher minimality + more clauses = stronger.
        let strength_a = (score_a.value as i64) + (clauses_a as i64 * 5);
        let strength_b = (score_b.value as i64) + (clauses_b as i64 * 5);

        if strength_a > strength_b {
            format!(
                "Spec A is stronger (score {strength_a} vs {strength_b}): more precise with {clauses_a} vs {clauses_b} clauses."
            )
        } else if strength_b > strength_a {
            format!(
                "Spec B is stronger (score {strength_b} vs {strength_a}): more precise with {clauses_b} vs {clauses_a} clauses."
            )
        } else {
            "Specs are equivalent in overall strength.".to_string()
        }
    }

    /// Generate improvement suggestions based on a quality report.
    #[must_use]
    pub fn suggest_improvements(&self, report: &QualityReport) -> Vec<String> {
        let mut suggestions = Vec::new();

        for score in &report.metrics.scores {
            if score.percentage() < 50 {
                match score.kind {
                    MetricKind::Completeness => {
                        suggestions.push(
                            "Add postconditions or invariants to cover more behaviors.".to_string(),
                        );
                    }
                    MetricKind::Precision => {
                        suggestions.push(
                            "Tighten preconditions with concrete bounds on parameters.".to_string(),
                        );
                    }
                    MetricKind::Minimality => {
                        suggestions.push(
                            "Remove duplicate or subsumed clauses from the specification."
                                .to_string(),
                        );
                    }
                    MetricKind::Consistency => {
                        suggestions
                            .push("Check for contradictory requires/ensures clauses.".to_string());
                    }
                    MetricKind::Coverage => {
                        suggestions
                            .push("Add specifications for uncovered execution paths.".to_string());
                    }
                }
            }
        }

        if report.metrics.overall_percentage() < self.config.min_acceptable_score {
            suggestions.push(format!(
                "Overall quality {}% is below threshold {}%. Consider a rewrite.",
                report.metrics.overall_percentage(),
                self.config.min_acceptable_score,
            ));
        }

        suggestions
    }

    // --- Private helpers ---

    fn completeness_score(&self, spec: &str, function_body: &str) -> QualityScore {
        let max_val = 100u32;
        let mut score = 0u32;

        // Reward having both requires and ensures.
        let has_requires = spec.contains("requires") || spec.contains("pre");
        let has_ensures = spec.contains("ensures") || spec.contains("post");
        if has_requires {
            score += 30;
        }
        if has_ensures {
            score += 30;
        }

        // Reward mentioning function parameters.
        let param_vars = extract_identifiers(function_body);
        let spec_lower = spec.to_lowercase();
        let mentioned =
            param_vars.iter().filter(|v| spec_lower.contains(&v.to_lowercase())).count();
        let param_coverage = if param_vars.is_empty() {
            40
        } else {
            ((mentioned as u32) * 40) / (param_vars.len() as u32).max(1)
        };
        score += param_coverage;

        let details = format!(
            "requires={has_requires}, ensures={has_ensures}, params_covered={mentioned}/{}",
            param_vars.len()
        );
        QualityScore::new(MetricKind::Completeness, score, max_val, details)
    }

    fn precision_score(&self, spec: &str, function_body: &str) -> QualityScore {
        let max_val = 100u32;
        let mut score = 0u32;

        // Reward numeric bounds.
        let has_bounds =
            spec.contains('<') || spec.contains('>') || spec.contains("<=") || spec.contains(">=");
        if has_bounds {
            score += 40;
        }

        // Reward type constraints or specific operators.
        let has_equality = spec.contains("==") || spec.contains("!=");
        if has_equality {
            score += 20;
        }

        // Reward mentioning return value.
        let mentions_result =
            spec.contains("result") || spec.contains("ret") || spec.contains("output");
        if mentions_result {
            score += 20;
        }

        // Reward referencing variables from the body.
        let body_vars = extract_identifiers(function_body);
        let spec_lower = spec.to_lowercase();
        let referenced =
            body_vars.iter().filter(|v| spec_lower.contains(&v.to_lowercase())).count();
        if referenced > 0 {
            score += 20u32.min(referenced as u32 * 5);
        }

        let details = format!(
            "bounds={has_bounds}, equality={has_equality}, result={mentions_result}, vars_ref={referenced}"
        );
        QualityScore::new(MetricKind::Precision, score, max_val, details)
    }

    fn consistency_score(&self, spec: &str) -> QualityScore {
        let max_val = 100u32;
        let mut score = max_val;

        // Penalize obvious contradictions: "x > 0" and "x < 0" in same spec.
        let clauses: Vec<&str> = spec.split("&&").map(str::trim).collect();
        for i in 0..clauses.len() {
            for j in (i + 1)..clauses.len() {
                if is_contradictory(clauses[i], clauses[j]) {
                    score = score.saturating_sub(50);
                }
            }
        }

        // Penalize "false" literal (unsatisfiable).
        if spec.contains("false") && !spec.contains("!= false") {
            score = score.saturating_sub(100);
        }

        let details = if score == max_val {
            "No contradictions detected.".to_string()
        } else {
            format!("Contradictions found, score reduced to {score}/{max_val}.")
        };

        QualityScore::new(MetricKind::Consistency, score, max_val, details)
    }

    fn coverage_score_from_body(&self, spec: &str, function_body: &str) -> QualityScore {
        let max_val = 100u32;

        // Count branch-like constructs in the body.
        let branches = function_body.matches("if ").count()
            + function_body.matches("match ").count()
            + function_body.matches("else").count();

        // Each spec clause can address one branch.
        let clauses = count_clauses(spec);

        let score = if branches == 0 {
            max_val // No branches to cover.
        } else {
            let ratio = ((clauses as u32) * 100) / (branches as u32).max(1);
            ratio.min(max_val)
        };

        let details = format!("branches={branches}, clauses={clauses}, ratio={score}%");
        QualityScore::new(MetricKind::Coverage, score, max_val, details)
    }
}

// --- Free functions ---

/// Extract identifier-like tokens from a string.
fn extract_identifiers(text: &str) -> Vec<String> {
    let mut ids = Vec::new();
    let mut current = String::new();

    for ch in text.chars() {
        if ch.is_alphanumeric() || ch == '_' {
            current.push(ch);
        } else {
            if !current.is_empty()
                && !current.chars().next().is_none_or(|c| c.is_ascii_digit())
                && !is_keyword(&current)
                && !ids.contains(&current)
            {
                ids.push(current.clone());
            }
            current.clear();
        }
    }
    // Final token.
    if !current.is_empty()
        && !current.chars().next().is_none_or(|c| c.is_ascii_digit())
        && !is_keyword(&current)
        && !ids.contains(&current)
    {
        ids.push(current);
    }

    ids
}

/// Check if a token is a Rust keyword (not a meaningful identifier).
fn is_keyword(word: &str) -> bool {
    matches!(
        word,
        "fn" | "let"
            | "mut"
            | "if"
            | "else"
            | "match"
            | "return"
            | "pub"
            | "struct"
            | "enum"
            | "impl"
            | "for"
            | "while"
            | "loop"
            | "break"
            | "continue"
            | "true"
            | "false"
            | "self"
            | "use"
            | "mod"
            | "const"
            | "static"
            | "type"
            | "where"
            | "as"
            | "in"
            | "ref"
            | "move"
            | "async"
            | "await"
            | "dyn"
            | "trait"
            | "super"
            | "crate"
            | "extern"
            | "unsafe"
    )
}

/// Normalize a clause for deduplication: lowercase, collapse whitespace.
fn normalize_clause(clause: &str) -> String {
    clause.split_whitespace().collect::<Vec<&str>>().join(" ").to_lowercase()
}

/// Count the number of clauses in a spec (split by && and commas).
fn count_clauses(spec: &str) -> usize {
    spec.split("&&").flat_map(|s| s.split(',')).map(str::trim).filter(|s| !s.is_empty()).count()
}

/// Heuristic contradiction detector for simple comparisons.
fn is_contradictory(a: &str, b: &str) -> bool {
    // Pattern: "x > N" vs "x < M" where M <= N.
    let a_trimmed = a.trim();
    let b_trimmed = b.trim();

    // Direct negation: "x > 0" vs "x <= 0".
    if let (Some(var_a), Some(op_a)) =
        (extract_comparison_var(a_trimmed), extract_comparison_op(a_trimmed))
        && let (Some(var_b), Some(op_b)) =
            (extract_comparison_var(b_trimmed), extract_comparison_op(b_trimmed))
        && var_a == var_b
        && is_negation(op_a, op_b)
    {
        return true;
    }

    false
}

fn extract_comparison_var(clause: &str) -> Option<String> {
    let ops = [">=", "<=", "!=", "==", ">", "<"];
    for op in &ops {
        if let Some(idx) = clause.find(op) {
            let var = clause[..idx].trim().to_string();
            if !var.is_empty() {
                return Some(var);
            }
        }
    }
    None
}

fn extract_comparison_op(clause: &str) -> Option<&str> {
    let ops = [">=", "<=", "!=", "==", ">", "<"];
    ops.iter().find(|&op| clause.contains(op)).map(|v| v as _)
}

fn is_negation(a: &str, b: &str) -> bool {
    matches!(
        (a, b),
        (">", "<=") | ("<=", ">") | ("<", ">=") | (">=", "<") | ("==", "!=") | ("!=", "==")
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn default_evaluator() -> QualityEvaluator {
        QualityEvaluator::new(QualityConfig::default())
    }

    // --- MetricKind tests ---

    #[test]
    fn test_metric_kind_all_returns_five_kinds() {
        assert_eq!(MetricKind::all().len(), 5);
    }

    #[test]
    fn test_metric_kind_labels_are_lowercase() {
        for kind in MetricKind::all() {
            assert_eq!(kind.label(), kind.label().to_lowercase());
        }
    }

    // --- QualityScore tests ---

    #[test]
    fn test_quality_score_percentage() {
        let score = QualityScore::new(MetricKind::Precision, 75, 100, "test");
        assert_eq!(score.percentage(), 75);
    }

    #[test]
    fn test_quality_score_clamps_to_max() {
        let score = QualityScore::new(MetricKind::Precision, 200, 100, "over max");
        assert_eq!(score.value, 100);
        assert_eq!(score.percentage(), 100);
    }

    #[test]
    fn test_quality_score_zero_max() {
        let score = QualityScore::new(MetricKind::Coverage, 0, 0, "empty");
        assert_eq!(score.percentage(), 0);
    }

    // --- QualityMetrics tests ---

    #[test]
    fn test_quality_metrics_aggregation() {
        let scores = vec![
            QualityScore::new(MetricKind::Completeness, 80, 100, ""),
            QualityScore::new(MetricKind::Precision, 60, 100, ""),
        ];
        let metrics = QualityMetrics::from_scores(scores);
        assert_eq!(metrics.overall_score, 140);
        assert_eq!(metrics.max_score, 200);
        assert_eq!(metrics.overall_percentage(), 70);
    }

    #[test]
    fn test_quality_metrics_score_for_lookup() {
        let scores = vec![
            QualityScore::new(MetricKind::Completeness, 80, 100, ""),
            QualityScore::new(MetricKind::Minimality, 90, 100, ""),
        ];
        let metrics = QualityMetrics::from_scores(scores);
        assert_eq!(metrics.score_for(MetricKind::Minimality).unwrap().value, 90);
        assert!(metrics.score_for(MetricKind::Precision).is_none());
    }

    // --- SpecCoverage tests ---

    #[test]
    fn test_spec_coverage_percentage() {
        let cov = SpecCoverage {
            total_paths: 10,
            covered_paths: 7,
            uncovered_variables: vec!["y".to_string()],
        };
        assert_eq!(cov.coverage_percentage(), 70);
    }

    #[test]
    fn test_spec_coverage_zero_paths() {
        let cov = SpecCoverage { total_paths: 0, covered_paths: 0, uncovered_variables: vec![] };
        assert_eq!(cov.coverage_percentage(), 0);
    }

    // --- QualityEvaluator tests ---

    #[test]
    fn test_evaluate_spec_with_requires_and_ensures() {
        let eval = default_evaluator();
        let spec = "requires x > 0 && ensures result >= 0";
        let body = "fn foo(x: i32) -> i32 { x + 1 }";
        let report = eval.evaluate_spec(spec, body);
        // Should have completeness, precision, minimality, consistency, coverage
        assert_eq!(report.metrics.scores.len(), 5);
        assert!(report.metrics.overall_score > 0);
    }

    #[test]
    fn test_evaluate_empty_spec() {
        let eval = default_evaluator();
        let report = eval.evaluate_spec("", "fn bar() {}");
        // Empty spec should score low.
        assert!(report.metrics.overall_percentage() < 50);
    }

    #[test]
    fn test_coverage_analysis_full_coverage() {
        let eval = default_evaluator();
        let spec = "x > 0 && y < 100";
        let paths = &["x > 0", "y < 100"];
        let cov = eval.coverage_analysis(spec, paths);
        assert_eq!(cov.total_paths, 2);
        assert_eq!(cov.covered_paths, 2);
    }

    #[test]
    fn test_coverage_analysis_partial() {
        let eval = default_evaluator();
        let spec = "x > 0";
        let paths = &["x > 0", "y < 100", "z == 0"];
        let cov = eval.coverage_analysis(spec, paths);
        assert_eq!(cov.total_paths, 3);
        assert_eq!(cov.covered_paths, 1);
        assert!(cov.uncovered_variables.contains(&"y".to_string()));
        assert!(cov.uncovered_variables.contains(&"z".to_string()));
    }

    #[test]
    fn test_redundancy_check_duplicate() {
        let eval = default_evaluator();
        let preconds = &["x > 0", "x > 0"];
        let pairs = eval.redundancy_check(preconds);
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0], (0, 1));
    }

    #[test]
    fn test_redundancy_check_substring() {
        let eval = default_evaluator();
        let preconds = &["x > 0 && y > 0", "x > 0"];
        let pairs = eval.redundancy_check(preconds);
        assert_eq!(pairs.len(), 1);
    }

    #[test]
    fn test_redundancy_check_no_redundancy() {
        let eval = default_evaluator();
        let preconds = &["x > 0", "y < 100", "z != 0"];
        let pairs = eval.redundancy_check(preconds);
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_minimality_score_concise_spec() {
        let eval = default_evaluator();
        let score = eval.minimality_score("x > 0 && y < 100");
        assert!(score.value > 50, "Concise spec should score well: {}", score.value);
    }

    #[test]
    fn test_minimality_score_empty() {
        let eval = default_evaluator();
        let score = eval.minimality_score("");
        assert_eq!(score.value, 0);
    }

    #[test]
    fn test_minimality_score_many_duplicates() {
        let eval = default_evaluator();
        let spec = "x > 0 && x > 0 && x > 0 && x > 0";
        let score = eval.minimality_score(spec);
        // Heavy dup penalty.
        assert!(score.value < 60, "Duplicate-heavy spec should score low: {}", score.value);
    }

    #[test]
    fn test_compare_specs_a_stronger() {
        let eval = default_evaluator();
        let a = "x > 0 && y < 100 && result >= 0";
        let b = "x > 0";
        let result = eval.compare_specs(a, b);
        assert!(result.contains("Spec A is stronger"), "Got: {result}");
    }

    #[test]
    fn test_compare_specs_equivalent() {
        let eval = default_evaluator();
        let a = "x > 0";
        let b = "x > 0";
        let result = eval.compare_specs(a, b);
        assert!(result.contains("equivalent"), "Got: {result}");
    }

    #[test]
    fn test_suggest_improvements_low_completeness() {
        let scores = vec![
            QualityScore::new(MetricKind::Completeness, 20, 100, "low"),
            QualityScore::new(MetricKind::Precision, 80, 100, "ok"),
        ];
        let metrics = QualityMetrics::from_scores(scores);
        let report = QualityReport {
            function_name: "test_fn".to_string(),
            metrics,
            suggestions: vec![],
            passes_threshold: false,
        };
        let eval = default_evaluator();
        let suggestions = eval.suggest_improvements(&report);
        assert!(
            suggestions.iter().any(|s| s.contains("postconditions")),
            "Should suggest adding postconditions: {:?}",
            suggestions
        );
    }

    #[test]
    fn test_consistency_detects_contradiction() {
        let eval = default_evaluator();
        let spec = "x > 0 && x <= 0";
        let body = "fn f(x: i32) {}";
        let report = eval.evaluate_spec(spec, body);
        let consistency = report
            .metrics
            .score_for(MetricKind::Consistency)
            .expect("should have consistency score");
        assert!(
            consistency.value < 100,
            "Contradictory spec should lose consistency points: {}",
            consistency.value
        );
    }

    #[test]
    fn test_passes_threshold_true() {
        let eval = QualityEvaluator::new(QualityConfig {
            min_acceptable_score: 10,
            ..QualityConfig::default()
        });
        let spec = "requires x > 0 && ensures result >= x";
        let body = "fn inc(x: u32) -> u32 { x + 1 }";
        let report = eval.evaluate_spec(spec, body);
        assert!(report.passes_threshold, "Should pass low threshold");
    }

    #[test]
    fn test_passes_threshold_false() {
        let eval = QualityEvaluator::new(QualityConfig {
            min_acceptable_score: 99,
            ..QualityConfig::default()
        });
        let report = eval.evaluate_spec("", "fn f() {}");
        assert!(!report.passes_threshold, "Empty spec should fail high threshold");
    }

    // --- Helper function tests ---

    #[test]
    fn test_extract_identifiers() {
        let ids = extract_identifiers("fn foo(x: i32, y_val: u64) -> bool");
        assert!(ids.contains(&"foo".to_string()));
        assert!(ids.contains(&"x".to_string()));
        assert!(ids.contains(&"y_val".to_string()));
        // Keywords should be excluded.
        assert!(!ids.contains(&"fn".to_string()));
    }

    #[test]
    fn test_normalize_clause() {
        assert_eq!(normalize_clause("  x  >  0  "), "x > 0");
        assert_eq!(normalize_clause("X > 0"), normalize_clause("x > 0"));
    }

    #[test]
    fn test_is_contradictory() {
        assert!(is_contradictory("x > 0", "x <= 0"));
        assert!(is_contradictory("y == 5", "y != 5"));
        assert!(!is_contradictory("x > 0", "y < 0"));
    }
}
