//! Counterexample-guided specification refinement.
//!
//! When a verification attempt fails with a counterexample, this module analyzes the
//! counterexample to automatically suggest stronger/weaker specifications. Integrates
//! with the prove-strengthen-backprop loop to iteratively refine specs until they are
//! both sufficient for proof and semantically meaningful.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

/// A counterexample produced by a failed verification attempt.
///
/// Contains variable assignments that witness the failure, the execution path
/// taken, and which property was violated.
#[derive(Debug, Clone, PartialEq)]
pub struct Counterexample {
    /// Variable name to concrete value mappings (e.g., `("x", "42")`).
    pub variable_assignments: Vec<(String, String)>,
    /// Sequence of basic blocks or source locations traversed.
    pub path_trace: Vec<String>,
    /// The specification clause that was violated.
    pub failing_property: String,
}

/// A suggested refinement to a specification.
#[derive(Debug, Clone, PartialEq)]
pub struct RefinementSuggestion {
    /// The original specification text.
    pub original_spec: String,
    /// The suggested replacement specification.
    pub suggested_spec: String,
    /// Confidence in this suggestion (0.0 to 1.0).
    pub confidence: f64,
    /// Human-readable explanation of why this refinement was suggested.
    pub rationale: String,
    /// Which refinement strategy produced this suggestion.
    pub strategy: RefinementStrategy,
}

/// Strategy used to produce a refinement suggestion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RefinementStrategy {
    /// Add constraints to the precondition to exclude the counterexample.
    StrengthenPrecondition,
    /// Relax the postcondition so the counterexample is no longer a violation.
    WeakenPostcondition,
    /// Add a guard clause (e.g., `if x > 0 then ...`).
    AddGuard,
    /// Split the spec into separate cases for different input domains.
    SplitCases,
}

/// Analyzes counterexamples and produces specification refinement suggestions.
#[derive(Debug, Clone)]
pub struct CexAnalyzer {
    /// Weight given to precondition strengthening vs postcondition weakening.
    precondition_bias: f64,
}

impl CexAnalyzer {
    /// Create a new analyzer with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self { precondition_bias: 0.6 }
    }

    /// Analyze a single counterexample against a spec and produce refinement suggestions.
    #[must_use]
    pub fn analyze_counterexample(
        &self,
        cex: &Counterexample,
        spec: &str,
    ) -> Vec<RefinementSuggestion> {
        let mut suggestions = Vec::new();

        if let Some(s) = self.suggest_precondition_strengthening(cex) {
            suggestions.push(s);
        }

        if let Some(s) = self.suggest_postcondition_weakening(cex, spec) {
            suggestions.push(s);
        }

        // Try guard and split strategies based on path diversity
        if !cex.path_trace.is_empty() {
            suggestions.push(RefinementSuggestion {
                original_spec: spec.to_owned(),
                suggested_spec: format!(
                    "if {} then {{ {} }}",
                    self.negate_cex_condition(cex),
                    spec,
                ),
                confidence: 0.4,
                rationale: format!(
                    "Add guard to exclude path: {}",
                    cex.path_trace.last().unwrap_or(&String::new()),
                ),
                strategy: RefinementStrategy::AddGuard,
            });
        }

        rank_suggestions(&mut suggestions);
        suggestions
    }

    /// Extract the constraints that the counterexample violates.
    #[must_use]
    pub fn extract_violated_constraints(&self, cex: &Counterexample) -> Vec<String> {
        let mut constraints = Vec::new();

        // The failing property itself is the primary violated constraint
        if !cex.failing_property.is_empty() {
            constraints.push(cex.failing_property.clone());
        }

        // Derive implicit constraints from variable assignments
        for (var, val) in &cex.variable_assignments {
            if let Ok(n) = val.parse::<i64>() {
                if n < 0 {
                    constraints.push(format!("{var} >= 0"));
                }
                if n == 0 {
                    constraints.push(format!("{var} != 0"));
                }
                if n == i64::MAX || n == i64::MIN {
                    constraints.push(format!("{var} within safe range"));
                }
            }
        }

        constraints
    }

    /// Suggest strengthening the precondition to exclude the counterexample.
    #[must_use]
    pub fn suggest_precondition_strengthening(
        &self,
        cex: &Counterexample,
    ) -> Option<RefinementSuggestion> {
        if cex.variable_assignments.is_empty() {
            return None;
        }

        let constraints: Vec<String> = cex
            .variable_assignments
            .iter()
            .filter_map(|(var, val)| {
                if let Ok(n) = val.parse::<i64>() {
                    if n < 0 {
                        Some(format!("{var} >= 0"))
                    } else if n == 0 {
                        Some(format!("{var} != 0"))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        let mut constraints = constraints;
        constraints.sort();

        if constraints.is_empty() {
            // Fall back: exclude the exact counterexample point
            let mut exclusions = cex
                .variable_assignments
                .iter()
                .map(|(var, val)| format!("{var} != {val}"))
                .collect::<Vec<_>>();
            exclusions.sort();
            let exclusion = exclusions.join(" && ");

            return Some(RefinementSuggestion {
                original_spec: String::new(),
                suggested_spec: format!("requires {exclusion}"),
                confidence: 0.3 * self.precondition_bias,
                rationale: "Exclude exact counterexample point (weak generalization)".to_owned(),
                strategy: RefinementStrategy::StrengthenPrecondition,
            });
        }

        let precondition = constraints.join(" && ");
        Some(RefinementSuggestion {
            original_spec: String::new(),
            suggested_spec: format!("requires {precondition}"),
            confidence: 0.7 * self.precondition_bias,
            rationale: format!(
                "Counterexample has variables violating: {}; strengthen precondition to exclude",
                precondition,
            ),
            strategy: RefinementStrategy::StrengthenPrecondition,
        })
    }

    /// Suggest weakening the postcondition to accommodate the counterexample.
    #[must_use]
    pub fn suggest_postcondition_weakening(
        &self,
        cex: &Counterexample,
        spec: &str,
    ) -> Option<RefinementSuggestion> {
        if cex.failing_property.is_empty() || spec.is_empty() {
            return None;
        }

        // If the spec contains the failing property, suggest weakening it
        if spec.contains(&cex.failing_property) {
            let weakened = spec.replace(
                &cex.failing_property,
                &format!("({} || <relaxed_condition>)", cex.failing_property),
            );
            return Some(RefinementSuggestion {
                original_spec: spec.to_owned(),
                suggested_spec: weakened,
                confidence: 0.5 * (1.0 - self.precondition_bias),
                rationale: format!(
                    "Postcondition '{}' violated by counterexample; weaken with disjunction",
                    cex.failing_property,
                ),
                strategy: RefinementStrategy::WeakenPostcondition,
            });
        }

        // Generic weakening: wrap in conditional
        Some(RefinementSuggestion {
            original_spec: spec.to_owned(),
            suggested_spec: "// No typed guard inferred; revise the native ensures clause manually"
                .to_owned(),
            confidence: 0.3 * (1.0 - self.precondition_bias),
            rationale: format!(
                "Failing property '{}' not found in spec text; suggest conditional postcondition",
                cex.failing_property,
            ),
            strategy: RefinementStrategy::WeakenPostcondition,
        })
    }

    /// Generalize from multiple counterexamples to find common patterns.
    #[must_use]
    pub fn generalize_from_counterexamples(
        &self,
        cexs: &[Counterexample],
    ) -> Vec<RefinementSuggestion> {
        if cexs.is_empty() {
            return Vec::new();
        }

        if cexs.len() == 1 {
            return self.analyze_counterexample(&cexs[0], "");
        }

        let mut suggestions = Vec::new();

        // Find variables that appear in all counterexamples
        let common_vars = self.find_common_variables(cexs);

        // For each common variable, look for patterns across counterexamples
        for var in &common_vars {
            let values: Vec<i64> = cexs
                .iter()
                .filter_map(|cex| {
                    cex.variable_assignments
                        .iter()
                        .find(|(v, _)| v == var)
                        .and_then(|(_, val)| val.parse::<i64>().ok())
                })
                .collect();

            if values.is_empty() {
                continue;
            }

            // Check if all values are negative
            if values.iter().all(|v| *v < 0) {
                suggestions.push(RefinementSuggestion {
                    original_spec: String::new(),
                    suggested_spec: format!("requires {var} >= 0"),
                    confidence: 0.8,
                    rationale: format!(
                        "All {} counterexamples have {var} < 0; likely missing non-negativity precondition",
                        cexs.len(),
                    ),
                    strategy: RefinementStrategy::StrengthenPrecondition,
                });
            }

            // Check if all values are zero
            if values.iter().all(|v| *v == 0) {
                suggestions.push(RefinementSuggestion {
                    original_spec: String::new(),
                    suggested_spec: format!("requires {var} != 0"),
                    confidence: 0.85,
                    rationale: format!(
                        "All {} counterexamples have {var} == 0; likely missing non-zero precondition",
                        cexs.len(),
                    ),
                    strategy: RefinementStrategy::StrengthenPrecondition,
                });
            }

            // Check if values suggest an upper bound
            if let (Some(&min), Some(&max)) = (values.iter().min(), values.iter().max())
                && min == max
                && values.len() > 1
            {
                suggestions.push(RefinementSuggestion {
                    original_spec: String::new(),
                    suggested_spec: format!("requires {var} != {min}"),
                    confidence: 0.75,
                    rationale: format!(
                        "All {} counterexamples have {var} == {min}; suggest excluding this value",
                        cexs.len(),
                    ),
                    strategy: RefinementStrategy::StrengthenPrecondition,
                });
            }
        }

        // Check if counterexamples share path prefixes -- suggests case split
        let common_path_prefix = self.find_common_path_prefix(cexs);
        if !common_path_prefix.is_empty() {
            suggestions.push(RefinementSuggestion {
                original_spec: String::new(),
                suggested_spec: format!(
                    "// Split spec at branch after: {}",
                    common_path_prefix.join(" -> "),
                ),
                confidence: 0.5,
                rationale: format!(
                    "Counterexamples share path prefix of length {}; consider splitting spec at divergence point",
                    common_path_prefix.len(),
                ),
                strategy: RefinementStrategy::SplitCases,
            });
        }

        rank_suggestions(&mut suggestions);
        suggestions
    }

    /// Build a negated condition from counterexample variable assignments.
    fn negate_cex_condition(&self, cex: &Counterexample) -> String {
        if cex.variable_assignments.is_empty() {
            return "true".to_owned();
        }

        let mut assignments = cex.variable_assignments.iter().collect::<Vec<_>>();
        assignments.sort_by(|(var_a, val_a), (var_b, val_b)| {
            var_a.cmp(var_b).then_with(|| val_a.cmp(val_b))
        });

        assignments
            .into_iter()
            .map(|(var, val)| format!("{var} != {val}"))
            .collect::<Vec<_>>()
            .join(" || ")
    }

    /// Find variable names that appear in every counterexample.
    fn find_common_variables(&self, cexs: &[Counterexample]) -> Vec<String> {
        if cexs.is_empty() {
            return Vec::new();
        }

        let mut var_counts: BTreeMap<String, usize> = BTreeMap::new();
        for cex in cexs {
            // Deduplicate within a single cex
            let mut vars: Vec<&str> =
                cex.variable_assignments.iter().map(|(v, _)| v.as_str()).collect();
            vars.sort();
            vars.dedup();
            for var in vars {
                *var_counts.entry(var.to_owned()).or_default() += 1;
            }
        }

        let mut common_vars: Vec<String> = var_counts
            .into_iter()
            .filter(|(_, count)| *count == cexs.len())
            .map(|(var, _)| var)
            .collect();
        common_vars.sort();
        common_vars
    }

    /// Find the longest common prefix of path traces across counterexamples.
    fn find_common_path_prefix(&self, cexs: &[Counterexample]) -> Vec<String> {
        let traces: Vec<&[String]> = cexs.iter().map(|c| c.path_trace.as_slice()).collect();

        if traces.is_empty() || traces.iter().any(|t| t.is_empty()) {
            return Vec::new();
        }

        let min_len = traces.iter().map(|t| t.len()).min().unwrap_or(0);
        let mut prefix = Vec::new();

        for i in 0..min_len {
            let first = &traces[0][i];
            if traces.iter().all(|t| &t[i] == first) {
                prefix.push(first.clone());
            } else {
                break;
            }
        }

        prefix
    }
}

impl Default for CexAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

/// Rank suggestions by confidence (descending).
pub fn rank_suggestions(suggestions: &mut [RefinementSuggestion]) {
    suggestions.sort_by(compare_refinement_suggestions);
}

fn compare_refinement_suggestions(
    a: &RefinementSuggestion,
    b: &RefinementSuggestion,
) -> std::cmp::Ordering {
    b.confidence
        .partial_cmp(&a.confidence)
        .unwrap_or(std::cmp::Ordering::Equal)
        .then_with(|| {
            refinement_strategy_sort_key(a.strategy).cmp(&refinement_strategy_sort_key(b.strategy))
        })
        .then_with(|| a.suggested_spec.cmp(&b.suggested_spec))
        .then_with(|| a.original_spec.cmp(&b.original_spec))
        .then_with(|| a.rationale.cmp(&b.rationale))
}

fn refinement_strategy_sort_key(strategy: RefinementStrategy) -> u8 {
    match strategy {
        RefinementStrategy::StrengthenPrecondition => 0,
        RefinementStrategy::WeakenPostcondition => 1,
        RefinementStrategy::AddGuard => 2,
        RefinementStrategy::SplitCases => 3,
    }
}

/// Apply a refinement suggestion to a specification string.
///
/// If the original spec matches, replaces it with the suggested spec.
/// Otherwise, appends the suggestion.
#[must_use]
pub fn apply_refinement(spec: &str, suggestion: &RefinementSuggestion) -> String {
    if !suggestion.original_spec.is_empty() && spec.contains(&suggestion.original_spec) {
        spec.replace(&suggestion.original_spec, &suggestion.suggested_spec)
    } else if spec.is_empty() {
        suggestion.suggested_spec.clone()
    } else {
        format!("{}\n{}", spec, suggestion.suggested_spec)
    }
}

/// Check whether a counterexample is likely spurious (artifact of abstraction).
///
/// A counterexample is considered spurious if:
/// - It has no variable assignments (empty witness)
/// - All variable values are at extreme boundary values (likely solver artifacts)
/// - The path trace is empty (no concrete execution path)
#[must_use]
pub fn is_spurious(cex: &Counterexample) -> bool {
    // Empty witness is spurious
    if cex.variable_assignments.is_empty() && cex.path_trace.is_empty() {
        return true;
    }

    // All values at extremes suggests abstraction artifact
    if !cex.variable_assignments.is_empty() {
        let all_extreme = cex.variable_assignments.iter().all(|(_, val)| {
            if let Ok(n) = val.parse::<i64>() {
                n == i64::MAX || n == i64::MIN
            } else if let Ok(n) = val.parse::<u64>() {
                n == u64::MAX || n == 0
            } else {
                false
            }
        });
        if all_extreme {
            return true;
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_cex(vars: &[(&str, &str)], path: &[&str], property: &str) -> Counterexample {
        Counterexample {
            variable_assignments: vars
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect(),
            path_trace: path.iter().map(|s| s.to_string()).collect(),
            failing_property: property.to_string(),
        }
    }

    #[test]
    fn test_cex_analyzer_new_returns_default() {
        let analyzer = CexAnalyzer::new();
        assert!((analyzer.precondition_bias - 0.6).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analyze_counterexample_negative_var_suggests_precondition() {
        let analyzer = CexAnalyzer::new();
        let cex = make_cex(&[("x", "-5")], &["bb0", "bb1"], "x + y < 100");
        let suggestions = analyzer.analyze_counterexample(&cex, "ensures(x + y < 100)");
        assert!(!suggestions.is_empty());
        let precond =
            suggestions.iter().find(|s| s.strategy == RefinementStrategy::StrengthenPrecondition);
        assert!(precond.is_some());
        assert!(precond.unwrap().suggested_spec.contains("x >= 0"));
    }

    #[test]
    fn test_analyze_counterexample_zero_var_suggests_nonzero() {
        let analyzer = CexAnalyzer::new();
        let cex = make_cex(&[("divisor", "0")], &["bb0"], "result == x / divisor");
        let suggestions = analyzer.analyze_counterexample(&cex, "ensures(result == x / divisor)");
        let precond =
            suggestions.iter().find(|s| s.strategy == RefinementStrategy::StrengthenPrecondition);
        assert!(precond.is_some());
        assert!(precond.unwrap().suggested_spec.contains("divisor != 0"));
    }

    #[test]
    fn test_analyze_counterexample_includes_guard_when_path_exists() {
        let analyzer = CexAnalyzer::new();
        let cex = make_cex(&[("x", "42")], &["bb0", "bb1"], "prop");
        let suggestions = analyzer.analyze_counterexample(&cex, "ensures(prop)");
        let guard = suggestions.iter().find(|s| s.strategy == RefinementStrategy::AddGuard);
        assert!(guard.is_some());
    }

    #[test]
    fn test_extract_violated_constraints_negative() {
        let analyzer = CexAnalyzer::new();
        let cex = make_cex(&[("x", "-1"), ("y", "0")], &[], "x > 0");
        let constraints = analyzer.extract_violated_constraints(&cex);
        assert!(constraints.contains(&"x > 0".to_string()));
        assert!(constraints.contains(&"x >= 0".to_string()));
        assert!(constraints.contains(&"y != 0".to_string()));
    }

    #[test]
    fn test_extract_violated_constraints_extreme_values() {
        let analyzer = CexAnalyzer::new();
        let cex = make_cex(&[("n", "9223372036854775807")], &[], "no overflow");
        let constraints = analyzer.extract_violated_constraints(&cex);
        assert!(constraints.iter().any(|c| c.contains("within safe range")));
    }

    #[test]
    fn test_suggest_precondition_strengthening_empty_returns_none() {
        let analyzer = CexAnalyzer::new();
        let cex = make_cex(&[], &[], "prop");
        assert!(analyzer.suggest_precondition_strengthening(&cex).is_none());
    }

    #[test]
    fn test_suggest_precondition_strengthening_positive_values_fallback() {
        let analyzer = CexAnalyzer::new();
        let cex = make_cex(&[("x", "42"), ("y", "7")], &[], "prop");
        let suggestion = analyzer.suggest_precondition_strengthening(&cex);
        assert!(suggestion.is_some());
        let s = suggestion.unwrap();
        // Fallback: exclude exact point
        assert!(s.suggested_spec.contains("x != 42"));
        assert!(s.suggested_spec.contains("y != 7"));
        assert!(s.confidence < 0.3); // Low confidence for exact exclusion
    }

    #[test]
    fn test_suggest_postcondition_weakening_matching_property() {
        let analyzer = CexAnalyzer::new();
        let cex = make_cex(&[("x", "5")], &[], "result > 0");
        let suggestion = analyzer.suggest_postcondition_weakening(&cex, "ensures(result > 0)");
        assert!(suggestion.is_some());
        let s = suggestion.unwrap();
        assert!(s.suggested_spec.contains("relaxed_condition"));
        assert_eq!(s.strategy, RefinementStrategy::WeakenPostcondition);
    }

    #[test]
    fn test_suggest_postcondition_weakening_empty_spec_returns_none() {
        let analyzer = CexAnalyzer::new();
        let cex = make_cex(&[("x", "5")], &[], "result > 0");
        assert!(analyzer.suggest_postcondition_weakening(&cex, "").is_none());
    }

    #[test]
    fn test_generalize_single_counterexample() {
        let analyzer = CexAnalyzer::new();
        let cex = make_cex(&[("x", "-1")], &["bb0"], "x >= 0");
        let suggestions = analyzer.generalize_from_counterexamples(&[cex]);
        assert!(!suggestions.is_empty());
    }

    #[test]
    fn test_generalize_multiple_counterexamples_all_negative() {
        let analyzer = CexAnalyzer::new();
        let cexs = vec![
            make_cex(&[("x", "-1")], &["bb0"], "x >= 0"),
            make_cex(&[("x", "-5")], &["bb0"], "x >= 0"),
            make_cex(&[("x", "-100")], &["bb0"], "x >= 0"),
        ];
        let suggestions = analyzer.generalize_from_counterexamples(&cexs);
        let strong = suggestions.iter().find(|s| s.suggested_spec.contains("x >= 0"));
        assert!(strong.is_some());
        assert!(strong.unwrap().confidence >= 0.8);
    }

    #[test]
    fn test_generalize_multiple_counterexamples_all_zero() {
        let analyzer = CexAnalyzer::new();
        let cexs = vec![
            make_cex(&[("d", "0")], &["bb0"], "d != 0"),
            make_cex(&[("d", "0")], &["bb0", "bb1"], "d != 0"),
        ];
        let suggestions = analyzer.generalize_from_counterexamples(&cexs);
        let nonzero = suggestions.iter().find(|s| s.suggested_spec.contains("d != 0"));
        assert!(nonzero.is_some());
        assert!(nonzero.unwrap().confidence >= 0.85);
    }

    #[test]
    fn test_generalize_empty_input() {
        let analyzer = CexAnalyzer::new();
        let suggestions = analyzer.generalize_from_counterexamples(&[]);
        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_rank_suggestions_descending_confidence() {
        let mut suggestions = vec![
            RefinementSuggestion {
                original_spec: String::new(),
                suggested_spec: "low".to_owned(),
                confidence: 0.2,
                rationale: String::new(),
                strategy: RefinementStrategy::AddGuard,
            },
            RefinementSuggestion {
                original_spec: String::new(),
                suggested_spec: "high".to_owned(),
                confidence: 0.9,
                rationale: String::new(),
                strategy: RefinementStrategy::StrengthenPrecondition,
            },
            RefinementSuggestion {
                original_spec: String::new(),
                suggested_spec: "mid".to_owned(),
                confidence: 0.5,
                rationale: String::new(),
                strategy: RefinementStrategy::WeakenPostcondition,
            },
        ];
        rank_suggestions(&mut suggestions);
        assert_eq!(suggestions[0].suggested_spec, "high");
        assert_eq!(suggestions[1].suggested_spec, "mid");
        assert_eq!(suggestions[2].suggested_spec, "low");
    }

    #[test]
    fn test_apply_refinement_replaces_matching_spec() {
        let suggestion = RefinementSuggestion {
            original_spec: "ensures x > 0".to_owned(),
            suggested_spec: "ensures x >= 0".to_owned(),
            confidence: 0.8,
            rationale: String::new(),
            strategy: RefinementStrategy::WeakenPostcondition,
        };
        let result = apply_refinement("ensures x > 0", &suggestion);
        assert_eq!(result, "ensures x >= 0");
    }

    #[test]
    fn test_apply_refinement_appends_when_no_match() {
        let suggestion = RefinementSuggestion {
            original_spec: "other_spec".to_owned(),
            suggested_spec: "requires x > 0".to_owned(),
            confidence: 0.7,
            rationale: String::new(),
            strategy: RefinementStrategy::StrengthenPrecondition,
        };
        let result = apply_refinement("ensures result > 0", &suggestion);
        assert!(result.contains("ensures result > 0"));
        assert!(result.contains("requires x > 0"));
    }

    #[test]
    fn test_apply_refinement_empty_spec() {
        let suggestion = RefinementSuggestion {
            original_spec: String::new(),
            suggested_spec: "requires x > 0".to_owned(),
            confidence: 0.7,
            rationale: String::new(),
            strategy: RefinementStrategy::StrengthenPrecondition,
        };
        let result = apply_refinement("", &suggestion);
        assert_eq!(result, "requires x > 0");
    }

    #[test]
    fn test_is_spurious_empty_witness() {
        let cex = make_cex(&[], &[], "prop");
        assert!(is_spurious(&cex));
    }

    #[test]
    fn test_is_spurious_extreme_values() {
        let cex = make_cex(
            &[("x", "9223372036854775807"), ("y", "-9223372036854775808")],
            &["bb0"],
            "no overflow",
        );
        assert!(is_spurious(&cex));
    }

    #[test]
    fn test_is_not_spurious_normal_values() {
        let cex = make_cex(&[("x", "42"), ("y", "-3")], &["bb0"], "x + y > 0");
        assert!(!is_spurious(&cex));
    }

    #[test]
    fn test_generalize_common_path_prefix_split_cases() {
        let analyzer = CexAnalyzer::new();
        let cexs = vec![
            make_cex(&[("x", "-1")], &["entry", "check", "branch_a"], "prop"),
            make_cex(&[("x", "-2")], &["entry", "check", "branch_b"], "prop"),
        ];
        let suggestions = analyzer.generalize_from_counterexamples(&cexs);
        let split = suggestions.iter().find(|s| s.strategy == RefinementStrategy::SplitCases);
        assert!(split.is_some());
        assert!(split.unwrap().suggested_spec.contains("entry -> check"));
    }
}
