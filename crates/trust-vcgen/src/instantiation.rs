// Trust: Smart quantifier instantiation for verification conditions.
//
// E-matching: pattern-based instantiation triggered by ground terms.
// Trigger inference: automatically select instantiation triggers.
// Relevancy filtering: only instantiate quantifiers relevant to the proof goal.
// Instance caching: avoid redundant instantiations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{Formula, Sort};

use crate::quantifier_tiers::substitute;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the instantiation engine.
#[derive(Debug, Clone)]
pub struct InstantiationConfig {
    /// Maximum instantiation depth (number of rounds of E-matching).
    pub max_depth: usize,
    /// Maximum total number of instances generated per quantifier.
    pub max_instances_per_quantifier: usize,
    /// Whether to enable relevancy filtering.
    pub relevancy_filter: bool,
}

impl Default for InstantiationConfig {
    fn default() -> Self {
        Self { max_depth: 3, max_instances_per_quantifier: 100, relevancy_filter: true }
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors that can occur during instantiation.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum InstantiationError {
    #[error("instantiation depth limit exceeded: {depth} > {max}")]
    DepthLimitExceeded { depth: usize, max: usize },

    #[error("instance limit exceeded for quantifier: {count} > {max}")]
    InstanceLimitExceeded { count: usize, max: usize },
}

// ---------------------------------------------------------------------------
// Trigger patterns
// ---------------------------------------------------------------------------

/// A trigger pattern for E-matching.
///
/// A trigger is a term pattern containing one or more quantified variables.
/// When a ground term matching this pattern appears in the current context,
/// the quantifier is instantiated with the matching substitution.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Trigger {
    /// The pattern formula (contains quantified variable references).
    pub pattern: TriggerPattern,
    /// Variables that this trigger binds.
    pub bound_vars: Vec<String>,
}

/// The structure of a trigger pattern.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TriggerPattern {
    /// Match a function application: `f(args...)`.
    Apply { func: String, args: Vec<TriggerPattern> },
    /// Match an array select: `Select(arr, idx)`.
    Select { array: Box<TriggerPattern>, index: Box<TriggerPattern> },
    /// Match an arithmetic operation.
    Arith { op: ArithOp, left: Box<TriggerPattern>, right: Box<TriggerPattern> },
    /// Match a specific variable (wildcard within the trigger).
    BoundVar(String),
    /// Match any ground term (wildcard).
    Wildcard,
}

/// Arithmetic operations that can appear in triggers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
}

// ---------------------------------------------------------------------------
// E-matching engine
// ---------------------------------------------------------------------------

/// An instantiation produced by E-matching.
#[derive(Debug, Clone)]
struct Instantiation {
    /// The substitution: variable name -> ground term.
    _substitution: FxHashMap<String, Formula>,
    /// The resulting formula after substitution.
    result: Formula,
    /// Which trigger fired.
    _trigger_index: usize,
}

/// The quantifier instantiation engine.
#[derive(Debug, Clone)]
pub struct InstantiationEngine {
    config: InstantiationConfig,
    /// Cache of already-generated instances by their complete, sorted
    /// substitution. A fixed-width hash alone is not equality: a collision
    /// must never suppress a distinct quantifier instance.
    cache: FxHashSet<Vec<(String, Formula)>>,
    /// Statistics.
    pub(crate) stats: InstantiationStats,
}

/// Statistics about instantiation.
#[derive(Debug, Clone, Default)]
pub struct InstantiationStats {
    pub triggers_inferred: usize,
    pub instances_generated: usize,
    pub cache_hits: usize,
    pub filtered_by_relevancy: usize,
}

impl InstantiationEngine {
    /// Create a new engine with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self {
            config: InstantiationConfig::default(),
            cache: FxHashSet::default(),
            stats: InstantiationStats::default(),
        }
    }

    /// Create a new engine with custom configuration.
    #[must_use]
    pub fn with_config(config: InstantiationConfig) -> Self {
        Self { config, cache: FxHashSet::default(), stats: InstantiationStats::default() }
    }

    /// Get statistics.
    #[must_use]
    pub fn stats(&self) -> &InstantiationStats {
        &self.stats
    }

    /// Clear the instance cache.
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }

    /// Infer triggers for a quantified formula.
    ///
    /// Selects sub-terms of the body that contain all bound variables and are
    /// likely to appear as ground terms during solving.
    #[must_use]
    pub fn infer_triggers(
        &mut self,
        bindings: &[(trust_types::Symbol, Sort)],
        body: &Formula,
    ) -> Vec<Trigger> {
        let bound_names: FxHashSet<&str> = bindings.iter().map(|(n, _)| n.as_str()).collect();
        let mut triggers = Vec::new();

        // Strategy 1: look for Select(arr, var) patterns.
        collect_select_triggers(body, &bound_names, &mut triggers);

        // Strategy 2: look for arithmetic patterns containing bound vars.
        collect_arith_triggers(body, &bound_names, &mut triggers);

        // Strategy 3: look for equality patterns `var == expr` or `expr == var`.
        collect_equality_triggers(body, &bound_names, &mut triggers);

        // Deduplicate.
        let mut seen = FxHashSet::default();
        triggers.retain(|t| seen.insert(t.clone()));

        self.stats.triggers_inferred += triggers.len();
        triggers
    }

    /// Instantiate quantifiers in a formula using E-matching against ground terms.
    ///
    /// The `ground_terms` are formulas from the current proof context that
    /// serve as matching targets for trigger patterns.
    #[must_use]
    pub fn instantiate(&mut self, formula: &Formula, ground_terms: &[Formula]) -> Formula {
        self.instantiate_depth(formula, ground_terms, 0)
    }

    fn instantiate_depth(
        &mut self,
        formula: &Formula,
        ground_terms: &[Formula],
        depth: usize,
    ) -> Formula {
        if depth >= self.config.max_depth {
            return formula.clone();
        }

        match formula {
            Formula::Forall(bindings, body) => {
                let triggers = self.infer_triggers(bindings, body);
                let mut instances = Vec::new();
                let mut instance_count = 0;

                for (trigger_idx, trigger) in triggers.iter().enumerate() {
                    for ground in ground_terms {
                        if let Some(subst) = try_match(&trigger.pattern, ground) {
                            // Check all bound vars are assigned.
                            let all_bound =
                                bindings.iter().all(|(name, _)| subst.contains_key(name.as_str()));
                            if !all_bound {
                                continue;
                            }

                            // Check relevancy.
                            if self.config.relevancy_filter
                                && !is_relevant_instance(&subst, ground_terms)
                            {
                                self.stats.filtered_by_relevancy += 1;
                                continue;
                            }

                            // Check cache.
                            let cache_key = canonical_substitution(&subst);
                            if self.cache.contains(&cache_key) {
                                self.stats.cache_hits += 1;
                                continue;
                            }

                            // Generate instance.
                            let mut inst_body = *body.clone();
                            for (var_name, val) in &subst {
                                inst_body = substitute(&inst_body, var_name, val);
                            }

                            // Recurse into the instantiated body.
                            let inst_body =
                                self.instantiate_depth(&inst_body, ground_terms, depth + 1);

                            self.cache.insert(cache_key);
                            instances.push(Instantiation {
                                _substitution: subst,
                                result: inst_body,
                                _trigger_index: trigger_idx,
                            });

                            instance_count += 1;
                            self.stats.instances_generated += 1;

                            if instance_count >= self.config.max_instances_per_quantifier {
                                break;
                            }
                        }
                    }
                    if instance_count >= self.config.max_instances_per_quantifier {
                        break;
                    }
                }

                if instances.is_empty() {
                    // No instances found — keep the quantifier.
                    formula.clone()
                } else {
                    // Return conjunction of all instances AND the original quantifier.
                    // This is sound: the instances are consequences of the quantifier.
                    let mut conjuncts: Vec<Formula> =
                        instances.into_iter().map(|i| i.result).collect();
                    conjuncts.push(formula.clone());
                    Formula::And(conjuncts)
                }
            }
            // Recurse into sub-formulas.
            Formula::And(cs) => Formula::And(
                cs.iter().map(|c| self.instantiate_depth(c, ground_terms, depth)).collect(),
            ),
            Formula::Or(cs) => Formula::Or(
                cs.iter().map(|c| self.instantiate_depth(c, ground_terms, depth)).collect(),
            ),
            Formula::Implies(a, b) => Formula::Implies(
                Box::new(self.instantiate_depth(a, ground_terms, depth)),
                Box::new(self.instantiate_depth(b, ground_terms, depth)),
            ),
            Formula::Not(inner) => {
                Formula::Not(Box::new(self.instantiate_depth(inner, ground_terms, depth)))
            }
            other => other.clone(),
        }
    }
}

impl Default for InstantiationEngine {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Trigger inference helpers
// ---------------------------------------------------------------------------

/// Collect Select(arr, var) trigger patterns from a formula.
fn collect_select_triggers(
    formula: &Formula,
    bound_vars: &FxHashSet<&str>,
    out: &mut Vec<Trigger>,
) {
    match formula {
        Formula::Select(arr, idx) => {
            // Check if index contains a bound variable.
            let idx_vars = collect_vars(idx);
            let matches_bound: Vec<String> =
                idx_vars.iter().filter(|v| bound_vars.contains(v.as_str())).cloned().collect();

            if !matches_bound.is_empty() {
                out.push(Trigger {
                    pattern: TriggerPattern::Select {
                        array: Box::new(formula_to_trigger_pattern(arr, bound_vars)),
                        index: Box::new(formula_to_trigger_pattern(idx, bound_vars)),
                    },
                    bound_vars: matches_bound,
                });
            }

            // Recurse.
            collect_select_triggers(arr, bound_vars, out);
            collect_select_triggers(idx, bound_vars, out);
        }
        Formula::Not(inner) | Formula::Neg(inner) => {
            collect_select_triggers(inner, bound_vars, out);
        }
        Formula::And(cs) | Formula::Or(cs) => {
            for c in cs {
                collect_select_triggers(c, bound_vars, out);
            }
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => {
            collect_select_triggers(a, bound_vars, out);
            collect_select_triggers(b, bound_vars, out);
        }
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            collect_select_triggers(c, bound_vars, out);
            collect_select_triggers(t, bound_vars, out);
            collect_select_triggers(e, bound_vars, out);
        }
        Formula::Forall(_, body) | Formula::Exists(_, body) => {
            collect_select_triggers(body, bound_vars, out);
        }
        _ => {}
    }
}

/// Collect arithmetic trigger patterns.
fn collect_arith_triggers(formula: &Formula, bound_vars: &FxHashSet<&str>, out: &mut Vec<Trigger>) {
    match formula {
        Formula::Add(a, b) | Formula::Sub(a, b) | Formula::Mul(a, b) => {
            let all_vars = collect_vars(formula);
            let matches_bound: Vec<String> =
                all_vars.iter().filter(|v| bound_vars.contains(v.as_str())).cloned().collect();

            if !matches_bound.is_empty() {
                let op = match formula {
                    Formula::Add(..) => ArithOp::Add,
                    Formula::Sub(..) => ArithOp::Sub,
                    Formula::Mul(..) => ArithOp::Mul,
                    _ => ArithOp::Add, // unreachable but satisfies the compiler
                };
                out.push(Trigger {
                    pattern: TriggerPattern::Arith {
                        op,
                        left: Box::new(formula_to_trigger_pattern(a, bound_vars)),
                        right: Box::new(formula_to_trigger_pattern(b, bound_vars)),
                    },
                    bound_vars: matches_bound,
                });
            }

            collect_arith_triggers(a, bound_vars, out);
            collect_arith_triggers(b, bound_vars, out);
        }
        Formula::Not(inner) | Formula::Neg(inner) => {
            collect_arith_triggers(inner, bound_vars, out);
        }
        Formula::And(cs) | Formula::Or(cs) => {
            for c in cs {
                collect_arith_triggers(c, bound_vars, out);
            }
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => {
            collect_arith_triggers(a, bound_vars, out);
            collect_arith_triggers(b, bound_vars, out);
        }
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            collect_arith_triggers(c, bound_vars, out);
            collect_arith_triggers(t, bound_vars, out);
            collect_arith_triggers(e, bound_vars, out);
        }
        Formula::Select(a, i) => {
            collect_arith_triggers(a, bound_vars, out);
            collect_arith_triggers(i, bound_vars, out);
        }
        Formula::Forall(_, body) | Formula::Exists(_, body) => {
            collect_arith_triggers(body, bound_vars, out);
        }
        _ => {}
    }
}

/// Collect equality-based triggers: `var == expr` or `expr == var`.
fn collect_equality_triggers(
    formula: &Formula,
    bound_vars: &FxHashSet<&str>,
    out: &mut Vec<Trigger>,
) {
    match formula {
        Formula::Eq(a, b) => {
            // Check if one side is a bound variable.
            if let Formula::Var(name, _) = a.as_ref()
                && bound_vars.contains(name.as_str())
            {
                out.push(Trigger {
                    pattern: formula_to_trigger_pattern(b, bound_vars),
                    bound_vars: vec![name.clone()],
                });
            }
            if let Formula::Var(name, _) = b.as_ref()
                && bound_vars.contains(name.as_str())
            {
                out.push(Trigger {
                    pattern: formula_to_trigger_pattern(a, bound_vars),
                    bound_vars: vec![name.clone()],
                });
            }
        }
        Formula::And(cs) | Formula::Or(cs) => {
            for c in cs {
                collect_equality_triggers(c, bound_vars, out);
            }
        }
        Formula::Implies(a, b) => {
            collect_equality_triggers(a, bound_vars, out);
            collect_equality_triggers(b, bound_vars, out);
        }
        Formula::Not(inner) => collect_equality_triggers(inner, bound_vars, out),
        Formula::Forall(_, body) | Formula::Exists(_, body) => {
            collect_equality_triggers(body, bound_vars, out);
        }
        _ => {}
    }
}

/// Convert a formula to a trigger pattern.
fn formula_to_trigger_pattern(f: &Formula, bound_vars: &FxHashSet<&str>) -> TriggerPattern {
    match f {
        Formula::Var(name, _) if bound_vars.contains(name.as_str()) => {
            TriggerPattern::BoundVar(name.clone())
        }
        Formula::Select(arr, idx) => TriggerPattern::Select {
            array: Box::new(formula_to_trigger_pattern(arr, bound_vars)),
            index: Box::new(formula_to_trigger_pattern(idx, bound_vars)),
        },
        Formula::Add(a, b) => TriggerPattern::Arith {
            op: ArithOp::Add,
            left: Box::new(formula_to_trigger_pattern(a, bound_vars)),
            right: Box::new(formula_to_trigger_pattern(b, bound_vars)),
        },
        Formula::Sub(a, b) => TriggerPattern::Arith {
            op: ArithOp::Sub,
            left: Box::new(formula_to_trigger_pattern(a, bound_vars)),
            right: Box::new(formula_to_trigger_pattern(b, bound_vars)),
        },
        Formula::Mul(a, b) => TriggerPattern::Arith {
            op: ArithOp::Mul,
            left: Box::new(formula_to_trigger_pattern(a, bound_vars)),
            right: Box::new(formula_to_trigger_pattern(b, bound_vars)),
        },
        _ => TriggerPattern::Wildcard,
    }
}

/// Collect all variable names in a formula.
fn collect_vars(f: &Formula) -> FxHashSet<String> {
    let mut result = FxHashSet::default();
    collect_vars_rec(f, &mut result);
    result
}

fn collect_vars_rec(f: &Formula, out: &mut FxHashSet<String>) {
    match f {
        Formula::Var(name, _) => {
            out.insert(name.clone());
        }
        Formula::Not(inner) | Formula::Neg(inner) => collect_vars_rec(inner, out),
        Formula::And(cs) | Formula::Or(cs) => {
            for c in cs {
                collect_vars_rec(c, out);
            }
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => {
            collect_vars_rec(a, out);
            collect_vars_rec(b, out);
        }
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            collect_vars_rec(c, out);
            collect_vars_rec(t, out);
            collect_vars_rec(e, out);
        }
        Formula::Select(a, i) => {
            collect_vars_rec(a, out);
            collect_vars_rec(i, out);
        }
        Formula::Forall(_, body) | Formula::Exists(_, body) => collect_vars_rec(body, out),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// E-matching
// ---------------------------------------------------------------------------

/// Try to match a trigger pattern against a ground formula.
///
/// Returns a substitution mapping bound variables to ground terms, or None
/// if the match fails.
fn try_match(pattern: &TriggerPattern, ground: &Formula) -> Option<FxHashMap<String, Formula>> {
    let mut subst = FxHashMap::default();
    if match_rec(pattern, ground, &mut subst) { Some(subst) } else { None }
}

fn match_rec(
    pattern: &TriggerPattern,
    ground: &Formula,
    subst: &mut FxHashMap<String, Formula>,
) -> bool {
    match pattern {
        TriggerPattern::Wildcard => true,
        TriggerPattern::BoundVar(name) => {
            if let Some(existing) = subst.get(name) {
                // Must match the same term.
                existing == ground
            } else {
                subst.insert(name.clone(), ground.clone());
                true
            }
        }
        TriggerPattern::Select { array, index } => {
            if let Formula::Select(g_arr, g_idx) = ground {
                match_rec(array, g_arr, subst) && match_rec(index, g_idx, subst)
            } else {
                false
            }
        }
        TriggerPattern::Arith { op, left, right } => {
            let matches = match (op, ground) {
                (ArithOp::Add, Formula::Add(a, b)) => Some((a.as_ref(), b.as_ref())),
                (ArithOp::Sub, Formula::Sub(a, b)) => Some((a.as_ref(), b.as_ref())),
                (ArithOp::Mul, Formula::Mul(a, b)) => Some((a.as_ref(), b.as_ref())),
                _ => None,
            };
            if let Some((ga, gb)) = matches {
                match_rec(left, ga, subst) && match_rec(right, gb, subst)
            } else {
                false
            }
        }
        TriggerPattern::Apply { .. } => {
            // Function application matching — not yet used since our Formula
            // doesn't have explicit function application nodes.
            false
        }
    }
}

// ---------------------------------------------------------------------------
// Relevancy filtering
// ---------------------------------------------------------------------------

/// Check if an instance is relevant to the current proof context.
///
/// An instance is relevant if at least one of its substitution values
/// appears (or has subterms that appear) in the ground terms.
fn is_relevant_instance(subst: &FxHashMap<String, Formula>, ground_terms: &[Formula]) -> bool {
    for val in subst.values() {
        // Check if the substitution value or any of its subterms appear
        // in the ground terms.
        for ground in ground_terms {
            if formula_contains(ground, val) {
                return true;
            }
        }
    }
    // If no ground terms provided, everything is relevant.
    ground_terms.is_empty()
}

/// Check if `haystack` contains `needle` as a subterm.
fn formula_contains(haystack: &Formula, needle: &Formula) -> bool {
    if haystack == needle {
        return true;
    }
    match haystack {
        Formula::Not(inner) | Formula::Neg(inner) => formula_contains(inner, needle),
        Formula::And(cs) | Formula::Or(cs) => cs.iter().any(|c| formula_contains(c, needle)),
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => formula_contains(a, needle) || formula_contains(b, needle),
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            formula_contains(c, needle)
                || formula_contains(t, needle)
                || formula_contains(e, needle)
        }
        Formula::Select(a, i) => formula_contains(a, needle) || formula_contains(i, needle),
        Formula::Forall(_, body) | Formula::Exists(_, body) => formula_contains(body, needle),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Instance caching
// ---------------------------------------------------------------------------

/// Canonical exact substitution identity for instance caching.
fn canonical_substitution(subst: &FxHashMap<String, Formula>) -> Vec<(String, Formula)> {
    let mut entries: Vec<_> =
        subst.iter().map(|(name, value)| (name.clone(), value.clone())).collect();
    entries.sort_by(|(left, _), (right, _)| left.cmp(right));
    entries
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // === Trigger inference tests ===

    #[test]
    fn test_infer_triggers_select() {
        let mut engine = InstantiationEngine::new();
        let bindings = vec![("i".into(), Sort::Int)];
        // forall i. Select(arr, i) > 0
        let body = Formula::Gt(
            Box::new(Formula::Select(
                Box::new(Formula::Var(
                    "arr".to_string(),
                    Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                )),
                Box::new(Formula::Var("i".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );

        let triggers = engine.infer_triggers(&bindings, &body);
        assert!(!triggers.is_empty(), "should infer Select trigger");
        assert!(
            triggers.iter().any(|t| matches!(&t.pattern, TriggerPattern::Select { .. })),
            "should have a Select pattern trigger"
        );
    }

    #[test]
    fn test_infer_triggers_arith() {
        let mut engine = InstantiationEngine::new();
        let bindings = vec![("i".into(), Sort::Int)];
        // forall i. i + 1 > 0
        let body = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Var("i".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(0)),
        );

        let triggers = engine.infer_triggers(&bindings, &body);
        assert!(!triggers.is_empty(), "should infer Add trigger");
    }

    #[test]
    fn test_infer_triggers_equality() {
        let mut engine = InstantiationEngine::new();
        let bindings = vec![("x".into(), Sort::Int)];
        // forall x. x == 5 => P(x)
        let body = Formula::Implies(
            Box::new(Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(5)),
            )),
            Box::new(Formula::Bool(true)),
        );

        let triggers = engine.infer_triggers(&bindings, &body);
        assert!(!triggers.is_empty(), "should infer equality trigger");
    }

    #[test]
    fn test_infer_triggers_no_bound_vars() {
        let mut engine = InstantiationEngine::new();
        let bindings = vec![("x".into(), Sort::Int)];
        // forall x. true (no terms containing x)
        let body = Formula::Bool(true);
        let triggers = engine.infer_triggers(&bindings, &body);
        assert!(triggers.is_empty(), "no triggers for formula without bound vars");
    }

    // === E-matching tests ===

    #[test]
    fn test_match_wildcard() {
        let result = try_match(&TriggerPattern::Wildcard, &Formula::Int(42));
        assert!(result.is_some());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn test_match_bound_var() {
        let result = try_match(&TriggerPattern::BoundVar("x".to_string()), &Formula::Int(42));
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.len(), 1);
        assert!(matches!(subst.get("x"), Some(Formula::Int(42))));
    }

    #[test]
    fn test_match_bound_var_consistency() {
        // Pattern: Add(x, x) should require both sides to be the same.
        let pattern = TriggerPattern::Arith {
            op: ArithOp::Add,
            left: Box::new(TriggerPattern::BoundVar("x".to_string())),
            right: Box::new(TriggerPattern::BoundVar("x".to_string())),
        };
        // Add(5, 5) should match.
        let ground_same = Formula::Add(Box::new(Formula::Int(5)), Box::new(Formula::Int(5)));
        assert!(try_match(&pattern, &ground_same).is_some());

        // Add(5, 6) should NOT match.
        let ground_diff = Formula::Add(Box::new(Formula::Int(5)), Box::new(Formula::Int(6)));
        assert!(try_match(&pattern, &ground_diff).is_none());
    }

    #[test]
    fn test_match_select() {
        let pattern = TriggerPattern::Select {
            array: Box::new(TriggerPattern::Wildcard),
            index: Box::new(TriggerPattern::BoundVar("i".to_string())),
        };
        let ground = Formula::Select(
            Box::new(Formula::Var(
                "arr".to_string(),
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
            )),
            Box::new(Formula::Int(3)),
        );
        let result = try_match(&pattern, &ground);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert!(matches!(subst.get("i"), Some(Formula::Int(3))));
    }

    #[test]
    fn test_match_arith_add() {
        let pattern = TriggerPattern::Arith {
            op: ArithOp::Add,
            left: Box::new(TriggerPattern::BoundVar("x".to_string())),
            right: Box::new(TriggerPattern::Wildcard),
        };
        let ground = Formula::Add(Box::new(Formula::Int(7)), Box::new(Formula::Int(3)));
        let result = try_match(&pattern, &ground);
        assert!(result.is_some());
        assert!(matches!(result.unwrap().get("x"), Some(Formula::Int(7))));
    }

    #[test]
    fn test_match_wrong_op() {
        let pattern = TriggerPattern::Arith {
            op: ArithOp::Add,
            left: Box::new(TriggerPattern::Wildcard),
            right: Box::new(TriggerPattern::Wildcard),
        };
        let ground = Formula::Sub(Box::new(Formula::Int(7)), Box::new(Formula::Int(3)));
        assert!(try_match(&pattern, &ground).is_none());
    }

    #[test]
    fn test_match_apply_not_supported() {
        let pattern =
            TriggerPattern::Apply { func: "f".to_string(), args: vec![TriggerPattern::Wildcard] };
        assert!(try_match(&pattern, &Formula::Int(42)).is_none());
    }

    // === Instantiation engine tests ===

    #[test]
    fn test_instantiate_forall_with_ground_terms() {
        let mut engine = InstantiationEngine::new();

        // forall i. Select(arr, i) > 0
        let arr =
            Formula::Var("arr".to_string(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let body = Formula::Gt(
            Box::new(Formula::Select(
                Box::new(arr.clone()),
                Box::new(Formula::Var("i".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let formula = Formula::Forall(vec![("i".into(), Sort::Int)], Box::new(body));

        // Ground terms: Select(arr, 0), Select(arr, 1)
        let ground_terms = vec![
            Formula::Select(Box::new(arr.clone()), Box::new(Formula::Int(0))),
            Formula::Select(Box::new(arr), Box::new(Formula::Int(1))),
        ];

        let result = engine.instantiate(&formula, &ground_terms);
        // Should produce instances.
        assert!(!matches!(result, Formula::Forall(..)), "should have generated instances");
        assert!(engine.stats().instances_generated > 0);
    }

    #[test]
    fn test_instantiate_no_matching_terms() {
        let mut engine = InstantiationEngine::new();

        // forall x. x > 0 (only arith trigger: x itself won't match int constants as Add/Sub/Mul)
        let formula = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );

        // Ground terms that don't match any trigger.
        let ground_terms = vec![Formula::Bool(true)];
        let result = engine.instantiate(&formula, &ground_terms);
        // Should remain quantified.
        assert!(matches!(result, Formula::Forall(..)));
    }

    #[test]
    fn test_instantiate_non_quantified_passthrough() {
        let mut engine = InstantiationEngine::new();
        let f =
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let result = engine.instantiate(&f, &[]);
        assert!(matches!(result, Formula::Gt(..)));
    }

    // === Cache tests ===

    #[test]
    fn test_cache_prevents_duplicate_instances() {
        let mut engine = InstantiationEngine::new();

        let arr =
            Formula::Var("arr".to_string(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let body = Formula::Gt(
            Box::new(Formula::Select(
                Box::new(arr.clone()),
                Box::new(Formula::Var("i".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let formula = Formula::Forall(vec![("i".into(), Sort::Int)], Box::new(body));

        let ground = vec![Formula::Select(Box::new(arr.clone()), Box::new(Formula::Int(0)))];

        // First instantiation.
        let _ = engine.instantiate(&formula, &ground);
        let first_count = engine.stats().instances_generated;

        // Second instantiation with same ground terms — should hit cache.
        let _ = engine.instantiate(&formula, &ground);
        // Cache hits should increase, but instances_generated should not
        // (new instances from the second call are blocked by cache).
        assert!(
            engine.stats().cache_hits > 0 || engine.stats().instances_generated == first_count,
            "cache should prevent duplicate generation"
        );
    }

    #[test]
    fn test_clear_cache() {
        let mut engine = InstantiationEngine::new();
        let subst: FxHashMap<String, Formula> =
            [("x".to_string(), Formula::Int(1))].into_iter().collect();
        let key = canonical_substitution(&subst);
        engine.cache.insert(key);
        assert!(!engine.cache.is_empty());
        engine.clear_cache();
        assert!(engine.cache.is_empty());
    }

    // === Relevancy filtering tests ===

    #[test]
    fn test_relevancy_filter_passes() {
        let subst: FxHashMap<String, Formula> =
            [("x".to_string(), Formula::Int(5))].into_iter().collect();
        let ground_terms = vec![Formula::Int(5)];
        assert!(is_relevant_instance(&subst, &ground_terms));
    }

    #[test]
    fn test_relevancy_filter_rejects() {
        let subst: FxHashMap<String, Formula> =
            [("x".to_string(), Formula::Int(999))].into_iter().collect();
        let ground_terms = vec![Formula::Int(5)];
        assert!(!is_relevant_instance(&subst, &ground_terms));
    }

    #[test]
    fn test_relevancy_empty_ground_terms() {
        let subst: FxHashMap<String, Formula> =
            [("x".to_string(), Formula::Int(5))].into_iter().collect();
        assert!(is_relevant_instance(&subst, &[]));
    }

    // === Configuration tests ===

    #[test]
    fn test_default_config() {
        let config = InstantiationConfig::default();
        assert_eq!(config.max_depth, 3);
        assert_eq!(config.max_instances_per_quantifier, 100);
        assert!(config.relevancy_filter);
    }

    #[test]
    fn test_engine_default() {
        let engine = InstantiationEngine::default();
        assert_eq!(engine.stats().instances_generated, 0);
        assert_eq!(engine.stats().cache_hits, 0);
    }

    #[test]
    fn test_custom_config() {
        let config = InstantiationConfig {
            max_depth: 1,
            max_instances_per_quantifier: 5,
            relevancy_filter: false,
        };
        let engine = InstantiationEngine::with_config(config.clone());
        assert_eq!(engine.config.max_depth, 1);
        assert_eq!(engine.config.max_instances_per_quantifier, 5);
        assert!(!engine.config.relevancy_filter);
    }

    // === formula_contains tests ===

    #[test]
    fn test_formula_contains_self() {
        let f = Formula::Int(42);
        assert!(formula_contains(&f, &f));
    }

    #[test]
    fn test_formula_contains_nested() {
        let inner = Formula::Int(42);
        let outer = Formula::Add(Box::new(inner.clone()), Box::new(Formula::Int(1)));
        assert!(formula_contains(&outer, &inner));
    }

    #[test]
    fn test_formula_not_contains() {
        let f = Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(2)));
        assert!(!formula_contains(&f, &Formula::Int(42)));
    }

    // === Hash substitution tests ===

    #[test]
    fn test_canonical_substitution_is_insertion_order_independent() {
        let subst1: FxHashMap<String, Formula> =
            [("x".to_string(), Formula::Int(1)), ("y".to_string(), Formula::Int(2))]
                .into_iter()
                .collect();
        let subst2: FxHashMap<String, Formula> =
            [("y".to_string(), Formula::Int(2)), ("x".to_string(), Formula::Int(1))]
                .into_iter()
                .collect();
        assert_eq!(canonical_substitution(&subst1), canonical_substitution(&subst2));
    }

    #[test]
    fn test_canonical_substitution_distinguishes_values() {
        let subst1: FxHashMap<String, Formula> =
            [("x".to_string(), Formula::Int(1))].into_iter().collect();
        let subst2: FxHashMap<String, Formula> =
            [("x".to_string(), Formula::Int(2))].into_iter().collect();
        assert_ne!(canonical_substitution(&subst1), canonical_substitution(&subst2));
    }

    // === collect_vars tests ===

    #[test]
    fn test_collect_vars_basic() {
        let f = Formula::Add(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        );
        let vars = collect_vars(&f);
        assert!(vars.contains("x"));
        assert!(vars.contains("y"));
        assert_eq!(vars.len(), 2);
    }

    #[test]
    fn test_collect_vars_nested() {
        let f = Formula::And(vec![
            Formula::Var("a".into(), Sort::Bool),
            Formula::Or(vec![
                Formula::Var("b".into(), Sort::Int),
                Formula::Var("c".into(), Sort::Int),
            ]),
        ]);
        let vars = collect_vars(&f);
        assert_eq!(vars.len(), 3);
    }
}
