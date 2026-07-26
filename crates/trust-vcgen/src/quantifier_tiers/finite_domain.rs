// trust_vcgen/quantifier_tiers/finite_domain.rs: Tier 1 finite-domain detection and unrolling
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashSet;

use trust_types::{Formula, Sort, Symbol};

// ---------------------------------------------------------------------------
// Tier 1: Finite-domain detection and unrolling
// ---------------------------------------------------------------------------

/// Try to extract a finite domain for the first binding from the formula body.
///
/// Recognises patterns like:
///   `Implies(And([Le(lo, var), Lt(var, hi)]), body)` -- from forall(i, lo..hi, ...)
///   `And([Le(lo, var), Lt(var, hi), body])` -- from exists(i, lo..hi, ...)
///
/// Returns `Some(vec![lo..hi])` if the range is statically known and within `max`.
pub(super) fn detect_finite_domain(
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
    max: usize,
) -> Option<Vec<i128>> {
    if bindings.is_empty() {
        return None;
    }
    let var_name = &bindings[0].0;

    // Pattern 1: Forall desugaring -- Implies(range_guard, inner_body)
    if let Formula::Implies(guard, _) = body
        && let Some(range) = extract_range_from_guard(guard, var_name.as_str())
    {
        return range_to_domain(range.0, range.1, max);
    }

    // Pattern 2: Exists desugaring -- And([range_guard_parts..., body])
    if let Formula::And(clauses) = body
        && let Some(range) = extract_range_from_and_clauses(clauses, var_name.as_str())
    {
        return range_to_domain(range.0, range.1, max);
    }

    None
}

/// Extract (lo, hi) from a guard formula that constrains `var_name`.
fn extract_range_from_guard(guard: &Formula, var_name: &str) -> Option<(i128, i128)> {
    if let Formula::And(parts) = guard {
        return extract_range_parts(parts, var_name);
    }
    None
}

/// Extract (lo, hi) from the clauses of an And list, flattening nested Ands.
fn extract_range_from_and_clauses(clauses: &[Formula], var_name: &str) -> Option<(i128, i128)> {
    let mut flat: Vec<&Formula> = Vec::new();
    for clause in clauses {
        flatten_and_refs(clause, &mut flat);
    }
    extract_range_parts_refs(&flat, var_name)
}

/// Flatten And formulas into a flat list of references.
fn flatten_and_refs<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
    match f {
        Formula::And(cs) => {
            for c in cs {
                flatten_and_refs(c, out);
            }
        }
        other => out.push(other),
    }
}

/// Extract (lo, hi) from a flat list of bound constraint references.
fn extract_range_parts_refs(parts: &[&Formula], var_name: &str) -> Option<(i128, i128)> {
    let mut lo = None;
    let mut hi = None;

    for part in parts {
        extract_bound_from_atom(part, var_name, &mut lo, &mut hi);
    }

    match (lo, hi) {
        (Some(l), Some(h)) if l < h => Some((l, h)),
        _ => None,
    }
}

/// Extract (lo, hi) from a pair of bound constraints on `var_name`.
fn extract_range_parts(parts: &[Formula], var_name: &str) -> Option<(i128, i128)> {
    let refs: Vec<&Formula> = parts.iter().collect();
    extract_range_parts_refs(&refs, var_name)
}

/// Extract a bound from a single atomic formula.
fn extract_bound_from_atom(
    part: &Formula,
    var_name: &str,
    lo: &mut Option<i128>,
    hi: &mut Option<i128>,
) {
    match part {
        // Le(lo_val, var) -- lo_val <= var
        Formula::Le(a, b) => {
            if is_var(b, var_name)
                && let Some(val) = as_const(a)
            {
                *lo = Some(val);
            }
            // Le(var, hi_val) -- var <= hi_val (inclusive upper bound)
            if is_var(a, var_name)
                && let Some(val) = as_const(b)
            {
                *hi = Some(val + 1); // convert inclusive to exclusive
            }
        }
        // Lt(var, hi_val) -- var < hi_val
        Formula::Lt(a, b) => {
            if is_var(a, var_name)
                && let Some(val) = as_const(b)
            {
                *hi = Some(val);
            }
            // Lt(lo_val, var) -- lo_val < var
            if is_var(b, var_name)
                && let Some(val) = as_const(a)
            {
                *lo = Some(val + 1);
            }
        }
        // Ge(var, lo_val) -- var >= lo_val
        Formula::Ge(a, b) => {
            if is_var(a, var_name)
                && let Some(val) = as_const(b)
            {
                *lo = Some(val);
            }
            if is_var(b, var_name)
                && let Some(val) = as_const(a)
            {
                *hi = Some(val + 1);
            }
        }
        // Gt(var, lo_val) -- var > lo_val
        Formula::Gt(a, b) => {
            if is_var(a, var_name)
                && let Some(val) = as_const(b)
            {
                *lo = Some(val + 1);
            }
            if is_var(b, var_name)
                && let Some(val) = as_const(a)
            {
                *hi = Some(val);
            }
        }
        _ => {}
    }
}

/// Check whether a formula is `Var(name, _)`.
pub(super) fn is_var(f: &Formula, name: &str) -> bool {
    matches!(f, Formula::Var(n, _) if n == name)
}

/// If a formula is a constant integer, return its value.
pub(super) fn as_const(f: &Formula) -> Option<i128> {
    match f {
        Formula::Int(n) => Some(*n),
        _ => None,
    }
}

/// Convert a `[lo, hi)` range to a domain vector if within `max`.
fn range_to_domain(lo: i128, hi: i128, max: usize) -> Option<Vec<i128>> {
    let count = hi.saturating_sub(lo);
    if count <= 0 || count as usize > max {
        return None;
    }
    Some((lo..hi).collect())
}

/// Capture-avoiding substitution of a free Formula variable.
///
/// Both heap-backed [`Formula::Var`] and interned [`Formula::SymVar`] leaves
/// participate. Every current Formula child family is traversed through the
/// vocabulary's exhaustive `map_children` implementation. Quantifiers which
/// rebind `var_name` stop substitution, while binders that occur free in the
/// replacement are alpha-renamed before descending so the replacement cannot
/// be captured.
#[must_use]
pub(crate) fn substitute(formula: &Formula, var_name: &str, replacement: &Formula) -> Formula {
    let replacement_free: HashSet<String> = replacement.free_variables().into_iter().collect();
    let mut occupied = formula_symbol_names(formula);
    occupied.extend(formula_symbol_names(replacement));
    occupied.insert(var_name.to_string());
    let mut fresh_counter = 0usize;
    substitute_rec(
        formula,
        var_name,
        replacement,
        &replacement_free,
        &mut occupied,
        &mut fresh_counter,
    )
}

fn substitute_rec(
    formula: &Formula,
    var_name: &str,
    replacement: &Formula,
    replacement_free: &HashSet<String>,
    occupied: &mut HashSet<String>,
    fresh_counter: &mut usize,
) -> Formula {
    match formula {
        Formula::Var(name, _) if name == var_name => replacement.clone(),
        Formula::SymVar(name, _) if name.as_str() == var_name => replacement.clone(),
        Formula::Forall(bindings, body) => substitute_quantifier(
            true,
            bindings,
            body,
            var_name,
            replacement,
            replacement_free,
            occupied,
            fresh_counter,
        ),
        Formula::Exists(bindings, body) => substitute_quantifier(
            false,
            bindings,
            body,
            var_name,
            replacement,
            replacement_free,
            occupied,
            fresh_counter,
        ),
        _ => formula.clone().map_children(&mut |child| {
            substitute_rec(&child, var_name, replacement, replacement_free, occupied, fresh_counter)
        }),
    }
}

#[allow(clippy::too_many_arguments)]
fn substitute_quantifier(
    is_forall: bool,
    bindings: &[(Symbol, Sort)],
    body: &Formula,
    var_name: &str,
    replacement: &Formula,
    replacement_free: &HashSet<String>,
    occupied: &mut HashSet<String>,
    fresh_counter: &mut usize,
) -> Formula {
    if bindings.iter().any(|(name, _)| name.as_str() == var_name) {
        return if is_forall {
            Formula::Forall(bindings.to_vec(), Box::new(body.clone()))
        } else {
            Formula::Exists(bindings.to_vec(), Box::new(body.clone()))
        };
    }

    let mut renamed_bindings = bindings.to_vec();
    let mut renamed_body = body.clone();
    let mut renamed_names = HashSet::new();
    for (name, _) in bindings {
        let name = name.as_str();
        if replacement_free.contains(name) && renamed_names.insert(name.to_string()) {
            let fresh = fresh_substitution_binder(occupied, fresh_counter);
            for (binding, _) in &mut renamed_bindings {
                if binding.as_str() == name {
                    *binding = Symbol::intern(&fresh);
                }
            }
            renamed_body = alpha_rename_bound_occurrences(&renamed_body, name, &fresh);
        }
    }

    let substituted = substitute_rec(
        &renamed_body,
        var_name,
        replacement,
        replacement_free,
        occupied,
        fresh_counter,
    );
    if is_forall {
        Formula::Forall(renamed_bindings, Box::new(substituted))
    } else {
        Formula::Exists(renamed_bindings, Box::new(substituted))
    }
}

fn alpha_rename_bound_occurrences(formula: &Formula, from: &str, to: &str) -> Formula {
    match formula {
        Formula::Var(name, sort) if name == from => Formula::Var(to.to_string(), sort.clone()),
        Formula::SymVar(name, sort) if name.as_str() == from => {
            Formula::SymVar(Symbol::intern(to), sort.clone())
        }
        Formula::Forall(bindings, _) | Formula::Exists(bindings, _)
            if bindings.iter().any(|(name, _)| name.as_str() == from) =>
        {
            formula.clone()
        }
        _ => formula
            .clone()
            .map_children(&mut |child| alpha_rename_bound_occurrences(&child, from, to)),
    }
}

fn fresh_substitution_binder(occupied: &mut HashSet<String>, fresh_counter: &mut usize) -> String {
    loop {
        *fresh_counter = (*fresh_counter).saturating_add(1);
        let candidate = crate::generated_formula_symbol("subst", &fresh_counter.to_string());
        if occupied.insert(candidate.clone()) {
            return candidate;
        }
    }
}

fn formula_symbol_names(formula: &Formula) -> HashSet<String> {
    let mut names = HashSet::new();
    formula.visit(&mut |node| match node {
        Formula::Var(name, _) => {
            names.insert(name.clone());
        }
        Formula::SymVar(name, _) => {
            names.insert(name.as_str().to_string());
        }
        Formula::Forall(bindings, _) | Formula::Exists(bindings, _) => {
            names.extend(bindings.iter().map(|(name, _)| name.as_str().to_string()));
        }
        Formula::Pred(name, _) => {
            names.insert(name.as_str().to_string());
        }
        Formula::FnApp { func, .. } => {
            names.insert(func.clone());
        }
        Formula::Ctor { ctor, .. } => {
            names.insert(ctor.clone());
        }
        Formula::Sel { datatype, field, .. } => {
            names.insert(datatype.clone());
            names.insert(field.clone());
        }
        Formula::IsCtor { datatype, ctor, .. } => {
            names.insert(datatype.clone());
            names.insert(ctor.clone());
        }
        _ => {}
    });
    names
}

/// Instantiate a prefix of one quantifier's bindings simultaneously.
///
/// The bound occurrences are first renamed to fresh placeholders, then the
/// uninstantiated suffix is restored around the body before capture-avoiding
/// substitution. Placeholders keep one instantiation term from being rewritten
/// by a later term (`x := y, y := 1`), while restoring the suffix first keeps a
/// free variable in a term from being captured by a remaining binder.
pub(super) fn instantiate_binding_prefix(
    bindings: &[(Symbol, Sort)],
    body: &Formula,
    terms: &[Formula],
) -> Formula {
    if bindings.is_empty() {
        return body.clone();
    }
    let count = bindings.len().min(terms.len());
    if count == 0 {
        return Formula::Forall(bindings.to_vec(), Box::new(body.clone()));
    }

    let mut occupied = formula_symbol_names(body);
    for term in &terms[..count] {
        occupied.extend(formula_symbol_names(term));
    }
    occupied.extend(bindings.iter().map(|(name, _)| name.as_str().to_string()));
    let mut counter = 0usize;
    let mut renamed_body = body.clone();
    let mut placeholders = Vec::with_capacity(count);
    for (name, _) in &bindings[..count] {
        let placeholder = fresh_instantiation_placeholder(&mut occupied, &mut counter);
        renamed_body = alpha_rename_bound_occurrences(&renamed_body, name.as_str(), &placeholder);
        placeholders.push(placeholder);
    }

    let mut result = if count < bindings.len() {
        Formula::Forall(bindings[count..].to_vec(), Box::new(renamed_body))
    } else {
        renamed_body
    };
    for (placeholder, term) in placeholders.into_iter().zip(&terms[..count]) {
        result = substitute(&result, &placeholder, term);
    }
    result
}

fn fresh_instantiation_placeholder(occupied: &mut HashSet<String>, counter: &mut usize) -> String {
    loop {
        *counter = (*counter).saturating_add(1);
        let candidate = crate::generated_formula_symbol("instantiate", &counter.to_string());
        if occupied.insert(candidate.clone()) {
            return candidate;
        }
    }
}

/// Unroll `forall([binding], body)` over a finite domain.
pub(super) fn unroll_forall(
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
    domain: &[i128],
) -> Formula {
    if bindings.is_empty() || domain.is_empty() {
        return Formula::Bool(true);
    }

    let var_name = &bindings[0].0;
    let remaining_bindings = &bindings[1..];

    let conjuncts: Vec<Formula> = domain
        .iter()
        .map(|&val| {
            let replaced = substitute(body, var_name.as_str(), &Formula::Int(val));
            if remaining_bindings.is_empty() {
                replaced
            } else {
                Formula::Forall(remaining_bindings.to_vec(), Box::new(replaced))
            }
        })
        .collect();

    if conjuncts.len() == 1 {
        conjuncts.into_iter().next().unwrap_or(Formula::Bool(true))
    } else {
        Formula::And(conjuncts)
    }
}

/// Unroll `exists([binding], body)` over a finite domain.
pub(super) fn unroll_exists(
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
    domain: &[i128],
) -> Formula {
    if bindings.is_empty() || domain.is_empty() {
        return Formula::Bool(false);
    }

    let var_name = &bindings[0].0;
    let remaining_bindings = &bindings[1..];

    let disjuncts: Vec<Formula> = domain
        .iter()
        .map(|&val| {
            let replaced = substitute(body, var_name.as_str(), &Formula::Int(val));
            if remaining_bindings.is_empty() {
                replaced
            } else {
                Formula::Exists(remaining_bindings.to_vec(), Box::new(replaced))
            }
        })
        .collect();

    if disjuncts.len() == 1 {
        disjuncts.into_iter().next().unwrap_or(Formula::Bool(false))
    } else {
        Formula::Or(disjuncts)
    }
}
