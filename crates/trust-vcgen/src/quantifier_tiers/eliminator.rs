// trust_vcgen/quantifier_tiers/eliminator.rs: QuantifierEliminator and convenience API
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};

use super::finite_domain::{detect_finite_domain, unroll_exists, unroll_forall};
use super::presburger::{cooper_eliminate_exists, cooper_eliminate_forall, is_presburger};
use super::types::{
    EliminationStats, QuantifierConfig, QuantifierTier, SolverStrategy, TierClassification,
};

// ---------------------------------------------------------------------------
// Top-level eliminator
// ---------------------------------------------------------------------------

/// Processes formulas and eliminates quantifiers where possible.
#[derive(Debug, Clone)]
pub struct QuantifierEliminator {
    config: QuantifierConfig,
    /// Statistics about eliminations performed.
    pub(crate) stats: EliminationStats,
}

impl QuantifierEliminator {
    /// Create a new eliminator with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self { config: QuantifierConfig::default(), stats: EliminationStats::default() }
    }

    /// Create a new eliminator with custom configuration.
    #[must_use]
    pub fn with_config(config: QuantifierConfig) -> Self {
        Self { config, stats: EliminationStats::default() }
    }

    /// Return a reference to the accumulated statistics.
    #[must_use]
    pub fn stats(&self) -> &EliminationStats {
        &self.stats
    }

    /// Classify a quantified formula into a tier.
    #[must_use]
    pub fn classify(
        &self,
        bindings: &[(trust_types::Symbol, Sort)],
        body: &Formula,
    ) -> TierClassification {
        // Try Tier 1: finite domain detection.
        if let Some(domain) = detect_finite_domain(bindings, body, self.config.max_unroll) {
            return TierClassification {
                tier: QuantifierTier::FiniteUnrolling,
                domain: Some(domain),
            };
        }

        // Try Tier 2: Presburger arithmetic detection.
        if self.config.enable_tier2 && is_presburger(bindings, body) {
            return TierClassification { tier: QuantifierTier::DecidableArithmetic, domain: None };
        }

        TierClassification { tier: QuantifierTier::Full, domain: None }
    }

    /// Eliminate quantifiers in a formula, recursively processing sub-formulas.
    #[must_use]
    pub fn eliminate(&mut self, formula: &Formula) -> Formula {
        match formula {
            Formula::Forall(bindings, body) => {
                // First, recursively eliminate in the body.
                let body = self.eliminate(body);
                let class = self.classify(bindings, &body);
                match class.tier {
                    QuantifierTier::QuantifierFree | QuantifierTier::Full => {
                        self.stats.left_intact += 1;
                        Formula::Forall(bindings.clone(), Box::new(body))
                    }
                    QuantifierTier::FiniteUnrolling => {
                        if let Some(domain) = class.domain {
                            self.stats.tier1_eliminated += 1;
                            unroll_forall(bindings, &body, &domain)
                        } else {
                            self.stats.left_intact += 1;
                            Formula::Forall(bindings.clone(), Box::new(body))
                        }
                    }
                    QuantifierTier::DecidableArithmetic => {
                        match cooper_eliminate_forall(bindings, &body) {
                            Ok(result) => {
                                self.stats.tier2_eliminated += 1;
                                result
                            }
                            Err(_) => {
                                self.stats.left_intact += 1;
                                Formula::Forall(bindings.clone(), Box::new(body))
                            }
                        }
                    }
                }
            }
            Formula::Exists(bindings, body) => {
                let body = self.eliminate(body);
                let class = self.classify(bindings, &body);
                match class.tier {
                    QuantifierTier::QuantifierFree | QuantifierTier::Full => {
                        self.stats.left_intact += 1;
                        Formula::Exists(bindings.clone(), Box::new(body))
                    }
                    QuantifierTier::FiniteUnrolling => {
                        if let Some(domain) = class.domain {
                            self.stats.tier1_eliminated += 1;
                            unroll_exists(bindings, &body, &domain)
                        } else {
                            self.stats.left_intact += 1;
                            Formula::Exists(bindings.clone(), Box::new(body))
                        }
                    }
                    QuantifierTier::DecidableArithmetic => {
                        match cooper_eliminate_exists(bindings, &body) {
                            Ok(result) => {
                                self.stats.tier2_eliminated += 1;
                                result
                            }
                            Err(_) => {
                                self.stats.left_intact += 1;
                                Formula::Exists(bindings.clone(), Box::new(body))
                            }
                        }
                    }
                }
            }
            // Recurse into sub-formulas.
            Formula::Not(inner) => Formula::Not(Box::new(self.eliminate(inner))),
            Formula::And(cs) => Formula::And(cs.iter().map(|c| self.eliminate(c)).collect()),
            Formula::Or(cs) => Formula::Or(cs.iter().map(|c| self.eliminate(c)).collect()),
            Formula::Implies(a, b) => {
                Formula::Implies(Box::new(self.eliminate(a)), Box::new(self.eliminate(b)))
            }
            Formula::Ite(c, t, e) => Formula::Ite(
                Box::new(self.eliminate(c)),
                Box::new(self.eliminate(t)),
                Box::new(self.eliminate(e)),
            ),
            // Leaf / non-quantifier nodes pass through unchanged.
            other => other.clone(),
        }
    }
}

impl Default for QuantifierEliminator {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Public convenience API
// ---------------------------------------------------------------------------

/// Check whether a formula is in a decidable arithmetic fragment.
#[must_use]
pub fn is_decidable_arithmetic(formula: &Formula) -> bool {
    let frag = super::presburger::classify_fragment(formula);
    !matches!(frag, super::presburger::ArithmeticFragment::Other)
}

/// Determine the recommended solver strategy for a formula based on its
/// quantifier tier classification.
#[must_use]
pub fn apply_tier_strategy(formula: &Formula, config: &QuantifierConfig) -> SolverStrategy {
    // If no quantifiers at all, use QF solver.
    if !has_quantifiers(formula) {
        return SolverStrategy::QuantifierFree;
    }

    // Build an eliminator and classify the outermost quantifier.
    let elim = QuantifierEliminator::with_config(config.clone());
    match formula {
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let class = elim.classify(bindings, body);
            match class.tier {
                QuantifierTier::QuantifierFree => SolverStrategy::QuantifierFree,
                QuantifierTier::FiniteUnrolling => SolverStrategy::Unroll,
                QuantifierTier::DecidableArithmetic => SolverStrategy::DecidableTheory,
                QuantifierTier::Full => SolverStrategy::FullQuantifier,
            }
        }
        // Formula has quantifiers but they are nested inside connectives.
        _ => worst_tier_strategy(formula, &elim),
    }
}

/// Check whether a formula contains any quantifiers.
#[must_use]
pub fn has_quantifiers(formula: &Formula) -> bool {
    match formula {
        Formula::Forall(..) | Formula::Exists(..) => true,
        Formula::Not(inner) | Formula::Neg(inner) => has_quantifiers(inner),
        Formula::And(cs) | Formula::Or(cs) => cs.iter().any(has_quantifiers),
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
        | Formula::Rem(a, b) => has_quantifiers(a) || has_quantifiers(b),
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            has_quantifiers(c) || has_quantifiers(t) || has_quantifiers(e)
        }
        Formula::Select(a, i) => has_quantifiers(a) || has_quantifiers(i),
        _ => false,
    }
}

/// Find the most demanding tier strategy across all quantifiers in a formula.
fn worst_tier_strategy(formula: &Formula, elim: &QuantifierEliminator) -> SolverStrategy {
    match formula {
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let class = elim.classify(bindings, body);
            let this = match class.tier {
                QuantifierTier::QuantifierFree => SolverStrategy::QuantifierFree,
                QuantifierTier::FiniteUnrolling => SolverStrategy::Unroll,
                QuantifierTier::DecidableArithmetic => SolverStrategy::DecidableTheory,
                QuantifierTier::Full => SolverStrategy::FullQuantifier,
            };
            let inner = worst_tier_strategy(body, elim);
            worse_strategy(this, inner)
        }
        Formula::Not(inner) | Formula::Neg(inner) => worst_tier_strategy(inner, elim),
        Formula::And(cs) | Formula::Or(cs) => {
            cs.iter().fold(SolverStrategy::QuantifierFree, |acc, c| {
                worse_strategy(acc, worst_tier_strategy(c, elim))
            })
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
            worse_strategy(worst_tier_strategy(a, elim), worst_tier_strategy(b, elim))
        }
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            let ct = worse_strategy(worst_tier_strategy(c, elim), worst_tier_strategy(t, elim));
            worse_strategy(ct, worst_tier_strategy(e, elim))
        }
        Formula::Select(a, i) => {
            worse_strategy(worst_tier_strategy(a, elim), worst_tier_strategy(i, elim))
        }
        _ => SolverStrategy::QuantifierFree,
    }
}

/// Return the more demanding of two strategies (higher = harder).
pub(super) fn worse_strategy(a: SolverStrategy, b: SolverStrategy) -> SolverStrategy {
    let rank = |s: SolverStrategy| match s {
        SolverStrategy::QuantifierFree => 0,
        SolverStrategy::Unroll => 1,
        SolverStrategy::DecidableTheory => 2,
        SolverStrategy::FullQuantifier => 3,
    };
    if rank(a) >= rank(b) { a } else { b }
}
