// trust_vcgen/quantifier_tiers/analysis.rs: Pre-processing pass
//
// Classification, skolemization, instantiation, simplification,
// and quantifier analysis.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashSet;

use trust_types::{Formula, Sort, Symbol};

use super::eliminator::{apply_tier_strategy, has_quantifiers};
use super::finite_domain::{instantiate_binding_prefix, substitute};
use super::presburger::free_vars;
use super::types::{
    QuantifierConfig, QuantifierError, QuantifierStats, QuantifierTier, SolverStrategy,
};

/// Analyze the quantifier structure of a formula.
///
/// Counts forall/exists quantifiers, computes maximum nesting depth,
/// and detects quantifier alternation (a forall nested under an exists
/// or vice versa).
#[must_use]
pub fn analyze_quantifiers(formula: &Formula) -> QuantifierStats {
    let mut stats = QuantifierStats::default();
    analyze_quantifiers_rec(formula, 0, None, &mut stats);
    stats
}

/// Quantifier polarity for alternation detection.
#[derive(Clone, Copy, PartialEq, Eq)]
enum QPolarity {
    Forall,
    Exists,
}

fn analyze_quantifiers_rec(
    formula: &Formula,
    depth: usize,
    parent_polarity: Option<QPolarity>,
    stats: &mut QuantifierStats,
) {
    match formula {
        Formula::Forall(_, body) => {
            stats.num_forall += 1;
            let new_depth = depth + 1;
            if new_depth > stats.max_nesting_depth {
                stats.max_nesting_depth = new_depth;
            }
            if parent_polarity == Some(QPolarity::Exists) {
                stats.has_alternation = true;
            }
            analyze_quantifiers_rec(body, new_depth, Some(QPolarity::Forall), stats);
        }
        Formula::Exists(_, body) => {
            stats.num_exists += 1;
            let new_depth = depth + 1;
            if new_depth > stats.max_nesting_depth {
                stats.max_nesting_depth = new_depth;
            }
            if parent_polarity == Some(QPolarity::Forall) {
                stats.has_alternation = true;
            }
            analyze_quantifiers_rec(body, new_depth, Some(QPolarity::Exists), stats);
        }
        _ => {
            for child in formula.children() {
                analyze_quantifiers_rec(child, depth, parent_polarity, stats);
            }
        }
    }
}

/// Classify the quantifier structure of a formula into a tier.
///
/// This is a standalone top-level function (unlike `QuantifierEliminator::classify`
/// which requires bindings). Walks the formula to determine the overall tier:
/// - `QuantifierFree`: no quantifiers present
/// - `FiniteUnrolling`: all quantifiers range over finite, statically-known domains
/// - `DecidableArithmetic`: all quantifiers are in Presburger arithmetic (LIA)
/// - `Full`: at least one quantifier is in a non-decidable fragment
#[must_use]
pub fn classify_quantifiers(formula: &Formula) -> QuantifierTier {
    if !has_quantifiers(formula) {
        return QuantifierTier::QuantifierFree;
    }
    let config = QuantifierConfig::default();
    let strategy = apply_tier_strategy(formula, &config);
    match strategy {
        SolverStrategy::QuantifierFree => QuantifierTier::QuantifierFree,
        SolverStrategy::Unroll => QuantifierTier::FiniteUnrolling,
        SolverStrategy::DecidableTheory => QuantifierTier::DecidableArithmetic,
        SolverStrategy::FullQuantifier => QuantifierTier::Full,
    }
}

/// Skolemize a formula: eliminate existential quantifiers by replacing
/// bound variables with Skolem function applications.
///
/// For an existential `exists x. P(x)` appearing under universal quantifiers
/// `forall y1, ..., yn`, the bound variable `x` is replaced with a fresh
/// [`Formula::FnApp`] whose arguments are those universal variables. If there
/// are no enclosing universals, a nullary function application represents the
/// Skolem constant.
///
/// This is sound for satisfiability: `exists x. P(x)` is satisfiable iff
/// `P(skolem_x)` is satisfiable (for the appropriate Skolem function). The
/// input may place quantifiers only in positive Boolean positions. Negative or
/// non-monotone quantified positions are rejected instead of applying an
/// equisatisfiability transformation outside its valid fragment.
pub fn try_skolemize(formula: &Formula) -> Result<Formula, QuantifierError> {
    let mut allocator = SkolemSymbolAllocator::new(formula);
    skolemize_rec(formula, &[], true, &mut allocator)
}

/// Legacy infallible compatibility entry point.
///
/// This fails stop on a shape for which equisatisfiable Skolemization is not
/// justified. New code should use [`try_skolemize`] and propagate the error.
#[deprecated(note = "use try_skolemize and handle unsupported quantifier polarity/shapes")]
#[must_use]
pub fn skolemize(formula: &Formula) -> Formula {
    try_skolemize(formula).expect(
        "skolemize cannot transform this formula soundly; use try_skolemize to handle the error",
    )
}

fn skolemize_rec(
    formula: &Formula,
    enclosing_universals: &[(Symbol, Sort)],
    positive: bool,
    allocator: &mut SkolemSymbolAllocator,
) -> Result<Formula, QuantifierError> {
    match formula {
        Formula::Forall(bindings, body) => {
            require_positive_unique_bindings("forall", bindings, positive)?;
            // A nested binder shadows an outer spelling. Remove the shadowed
            // dependency while this lexical scope is active, then add the
            // inner binding as the visible universal.
            let binding_names: HashSet<&str> =
                bindings.iter().map(|(name, _)| name.as_str()).collect();
            let mut extended: Vec<_> = enclosing_universals
                .iter()
                .filter(|(name, _)| !binding_names.contains(name.as_str()))
                .cloned()
                .collect();
            extended.extend(bindings.iter().cloned());
            let new_body = skolemize_rec(body, &extended, positive, allocator)?;
            Ok(Formula::Forall(bindings.clone(), Box::new(new_body)))
        }
        Formula::Exists(bindings, body) => {
            require_positive_unique_bindings("exists", bindings, positive)?;
            let binding_names: HashSet<&str> =
                bindings.iter().map(|(name, _)| name.as_str()).collect();
            let visible_universals: Vec<_> = enclosing_universals
                .iter()
                .filter(|(name, _)| !binding_names.contains(name.as_str()))
                .cloned()
                .collect();
            // Replace each existentially bound variable with a Skolem term.
            let mut current_body = *body.clone();
            for (var_name, var_sort) in bindings {
                let skolem_term = Formula::FnApp {
                    func: allocator.fresh(),
                    args: visible_universals
                        .iter()
                        .map(|(name, sort)| Formula::SymVar(name.clone(), sort.clone()))
                        .collect(),
                    sort: var_sort.clone(),
                };
                current_body = substitute(&current_body, var_name.as_str(), &skolem_term);
            }
            // Continue skolemizing in the (now existential-free) body.
            skolemize_rec(&current_body, &visible_universals, positive, allocator)
        }
        Formula::Not(inner) => Ok(Formula::Not(Box::new(skolemize_rec(
            inner,
            enclosing_universals,
            !positive,
            allocator,
        )?))),
        Formula::And(children) => Ok(Formula::And(
            children
                .iter()
                .map(|child| skolemize_rec(child, enclosing_universals, positive, allocator))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Formula::Or(children) => Ok(Formula::Or(
            children
                .iter()
                .map(|child| skolemize_rec(child, enclosing_universals, positive, allocator))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Formula::Implies(lhs, rhs) => Ok(Formula::Implies(
            Box::new(skolemize_rec(lhs, enclosing_universals, !positive, allocator)?),
            Box::new(skolemize_rec(rhs, enclosing_universals, positive, allocator)?),
        )),
        // Equality, ITE, arithmetic, arrays, BV/FP, predicates, datatypes, and
        // function applications are non-monotone or term positions. Quantified
        // children there are ill-sorted or require a prior NNF/polarity-aware
        // elaboration, so reject rather than guessing. With no quantifier below,
        // cloning is exact and avoids a hand-maintained Formula variant list.
        other if has_quantifiers(other) => Err(QuantifierError::UnsupportedSkolemization {
            reason: "quantifier occurs below a non-monotone or term-forming Formula node".into(),
        }),
        other => Ok(other.clone()),
    }
}

fn require_positive_unique_bindings(
    quantifier: &str,
    bindings: &[(Symbol, Sort)],
    positive: bool,
) -> Result<(), QuantifierError> {
    if !positive {
        return Err(QuantifierError::UnsupportedSkolemization {
            reason: format!("{quantifier} occurs in a negative Boolean position"),
        });
    }
    let mut names = HashSet::new();
    for (name, _) in bindings {
        if name.as_str().is_empty() || !names.insert(name.as_str()) {
            return Err(QuantifierError::UnsupportedSkolemization {
                reason: format!("{quantifier} has an empty or duplicate binder `{name}`"),
            });
        }
    }
    Ok(())
}

struct SkolemSymbolAllocator {
    occupied: HashSet<String>,
    next: usize,
}

impl SkolemSymbolAllocator {
    fn new(formula: &Formula) -> Self {
        let mut occupied = HashSet::new();
        formula.visit(&mut |node| match node {
            Formula::Var(name, _) => {
                occupied.insert(name.clone());
            }
            Formula::SymVar(name, _) => {
                occupied.insert(name.as_str().to_string());
            }
            Formula::Forall(bindings, _) | Formula::Exists(bindings, _) => {
                occupied.extend(bindings.iter().map(|(name, _)| name.as_str().to_string()));
            }
            Formula::Pred(name, _) => {
                occupied.insert(name.as_str().to_string());
            }
            Formula::FnApp { func, .. } => {
                occupied.insert(func.clone());
            }
            Formula::Ctor { ctor, .. } => {
                occupied.insert(ctor.clone());
            }
            Formula::Sel { datatype, field, .. } => {
                occupied.insert(datatype.clone());
                occupied.insert(field.clone());
            }
            Formula::IsCtor { datatype, ctor, .. } => {
                occupied.insert(datatype.clone());
                occupied.insert(ctor.clone());
            }
            _ => {}
        });
        Self { occupied, next: 0 }
    }

    fn fresh(&mut self) -> String {
        loop {
            self.next = self.next.saturating_add(1);
            let candidate = crate::generated_formula_symbol("skolem", &self.next.to_string());
            if self.occupied.insert(candidate.clone()) {
                return candidate;
            }
        }
    }
}

/// Instantiate a universally quantified formula with concrete terms.
///
/// For `Forall([(x1, s1), (x2, s2), ...], body)`, substitutes each
/// bound variable `xi` with the corresponding term from `terms`.
/// If `terms` is shorter than the binding list, remaining variables
/// stay bound. If `terms` is longer, extra terms are ignored.
///
/// For non-`Forall` formulas, returns the formula unchanged. Malformed
/// manually constructed quantifiers with empty or duplicate binders are
/// rejected instead of assigning one occurrence to an arbitrary term.
pub fn try_instantiate_universal(
    formula: &Formula,
    terms: &[Formula],
) -> Result<Formula, QuantifierError> {
    match formula {
        Formula::Forall(bindings, body) => {
            let mut seen = HashSet::new();
            for (name, _) in bindings {
                if name.as_str().is_empty() || !seen.insert(name.as_str()) {
                    return Err(QuantifierError::UnsupportedInstantiation {
                        reason: format!("empty or duplicate universal binder `{name}`"),
                    });
                }
            }
            Ok(instantiate_binding_prefix(bindings, body, terms))
        }
        other => Ok(other.clone()),
    }
}

/// Legacy infallible compatibility entry point.
///
/// This fails stop for malformed quantifiers rather than guessing how a term
/// maps to an empty or duplicate binder. New code should use
/// [`try_instantiate_universal`].
#[deprecated(note = "use try_instantiate_universal and handle malformed quantifiers")]
#[must_use]
pub fn instantiate_universal(formula: &Formula, terms: &[Formula]) -> Formula {
    try_instantiate_universal(formula, terms).expect(
        "instantiate_universal rejected malformed binders; use \
         try_instantiate_universal to handle the error",
    )
}

/// Simplify quantified formulas by removing vacuous quantifiers and
/// merging nested same-kind quantifiers.
///
/// Transformations applied (recursively, bottom-up):
/// 1. **Vacuous quantifier removal**: `forall x. P` where `x` is not free in `P`
///    becomes just `P`. Same for `exists x. P`.
/// 2. **Nested merge**: `forall x. forall y. P` becomes `forall x, y. P`.
///    Same for `exists x. exists y. P`.
/// 3. **Empty binding removal**: `forall(). P` becomes `P`.
#[must_use]
pub fn simplify_quantified(formula: &Formula) -> Formula {
    // Bottom-up: simplify children first, then simplify self.
    let simplified_children = match formula {
        Formula::Not(inner) => Formula::Not(Box::new(simplify_quantified(inner))),
        Formula::And(cs) => Formula::And(cs.iter().map(simplify_quantified).collect()),
        Formula::Or(cs) => Formula::Or(cs.iter().map(simplify_quantified).collect()),
        Formula::Implies(a, b) => {
            Formula::Implies(Box::new(simplify_quantified(a)), Box::new(simplify_quantified(b)))
        }
        Formula::Ite(c, t, e) => Formula::Ite(
            Box::new(simplify_quantified(c)),
            Box::new(simplify_quantified(t)),
            Box::new(simplify_quantified(e)),
        ),
        Formula::Eq(a, b) => {
            Formula::Eq(Box::new(simplify_quantified(a)), Box::new(simplify_quantified(b)))
        }
        Formula::Forall(bindings, body) => {
            Formula::Forall(bindings.clone(), Box::new(simplify_quantified(body)))
        }
        Formula::Exists(bindings, body) => {
            Formula::Exists(bindings.clone(), Box::new(simplify_quantified(body)))
        }
        other => other.clone(),
    };

    // Now apply quantifier-specific simplifications at this level.
    match &simplified_children {
        Formula::Forall(bindings, body) => simplify_forall(bindings, body),
        Formula::Exists(bindings, body) => simplify_exists(bindings, body),
        other => other.clone(),
    }
}

/// Simplify a `Forall` node after children are already simplified.
fn simplify_forall(bindings: &[(trust_types::Symbol, Sort)], body: &Formula) -> Formula {
    if bindings.is_empty() {
        return body.clone();
    }

    let body_free = free_vars(body);
    let non_vacuous: Vec<(trust_types::Symbol, Sort)> =
        bindings.iter().filter(|(name, _)| body_free.contains(name.as_str())).cloned().collect();

    if non_vacuous.is_empty() {
        return body.clone();
    }

    // Merge nested same-kind: forall x. forall y. P => forall x, y. P
    if let Formula::Forall(inner_bindings, inner_body) = body {
        let mut merged = non_vacuous;
        merged.extend(inner_bindings.iter().cloned());
        return Formula::Forall(merged, inner_body.clone());
    }

    if non_vacuous.len() == bindings.len() {
        Formula::Forall(bindings.to_vec(), Box::new(body.clone()))
    } else {
        Formula::Forall(non_vacuous, Box::new(body.clone()))
    }
}

/// Simplify an `Exists` node after children are already simplified.
fn simplify_exists(bindings: &[(trust_types::Symbol, Sort)], body: &Formula) -> Formula {
    if bindings.is_empty() {
        return body.clone();
    }

    let body_free = free_vars(body);
    let non_vacuous: Vec<(trust_types::Symbol, Sort)> =
        bindings.iter().filter(|(name, _)| body_free.contains(name.as_str())).cloned().collect();

    if non_vacuous.is_empty() {
        return body.clone();
    }

    // Merge nested same-kind: exists x. exists y. P => exists x, y. P
    if let Formula::Exists(inner_bindings, inner_body) = body {
        let mut merged = non_vacuous;
        merged.extend(inner_bindings.iter().cloned());
        return Formula::Exists(merged, inner_body.clone());
    }

    if non_vacuous.len() == bindings.len() {
        Formula::Exists(bindings.to_vec(), Box::new(body.clone()))
    } else {
        Formula::Exists(non_vacuous, Box::new(body.clone()))
    }
}
