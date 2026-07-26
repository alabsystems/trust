// If-then-else elimination over `Formula`. Solvers reason far better about a
// guarded conjunction than about a term-level `Ite`, so relations containing
// `Ite` terms are lifted into case splits, bounded by `ITE_ELIM_CASE_CAP` to
// keep a deeply nested term from exploding the VC.

use super::*;

/// Encode `var == value` WITHOUT a term-level `Ite`, by LIFTING any `Ite` in
/// `value` to a formula-level guard: `var == Ite(c, t, e)` becomes
/// `(c → var == t) ∧ (¬c → var == e)`, recursing into `t`/`e` (so a nested clamp
/// `Ite` fully flattens to guarded equalities).
///
/// Why: a term-level `Ite` in a POSTCONDITION obligation is not dischargeable by
/// the current backends — trust-mc's PDR prunes it (reports a "violation-pruned"
/// UNKNOWN) and the trust-wp native lane does not route the Ite-carrying bundle
/// to its pure-expr replay. The lifted form uses only `And`/`Implies`/`Not`/`Eq`
/// + comparisons, which BOTH backends lower and prove natively. Logically
/// equivalent to the equality (`Ite` IS the guarded case-split), so verdict-
/// preserving and sound. Depth-bounded by the caller's shallow clamp Ites.
pub(super) fn ite_free_equality(var: &Formula, value: &Formula) -> Formula {
    if let Formula::Ite(cond, then_v, else_v) = value {
        Formula::And(vec![
            Formula::Implies(cond.clone(), Box::new(ite_free_equality(var, then_v))),
            Formula::Implies(
                Box::new(Formula::Not(cond.clone())),
                Box::new(ite_free_equality(var, else_v)),
            ),
        ])
    } else {
        Formula::Eq(Box::new(var.clone()), Box::new(value.clone()))
    }
}

/// Conjoin two guards, dropping a trivially-true operand.
pub(super) fn and_guard(a: Formula, b: Formula) -> Formula {
    match (a, b) {
        (Formula::Bool(true), x) | (x, Formula::Bool(true)) => x,
        (a, b) => Formula::And(vec![a, b]),
    }
}

/// `guard → conclusion`, dropping a trivially-true guard.
pub(super) fn guarded(guard: Formula, conclusion: Formula) -> Formula {
    match guard {
        Formula::Bool(true) => conclusion,
        g => Formula::Implies(Box::new(g), Box::new(conclusion)),
    }
}

/// Case-split an integer-valued TERM on its `Ite` conditions. Returns
/// `(guard, ite_free_term)` pairs whose guards are mutually-exclusive, jointly
/// exhaustive, and themselves `Ite`-free (conditions are recursively lifted).
/// `None` if the case count would exceed `cap` — the caller then leaves the term
/// unchanged (fail-open). A leaf / opaque term (Var, Int, a BV/Fp node, …) is a
/// single guardless case.
pub(super) fn term_ite_cases(term: &Formula, cap: usize) -> Option<Vec<(Formula, Formula)>> {
    match term {
        Formula::Ite(cond, then_v, else_v) => {
            let cond_free = eliminate_term_ites(cond, cap);
            let not_cond = Formula::Not(Box::new(cond_free.clone()));
            let then_cases = term_ite_cases(then_v, cap)?;
            let else_cases = term_ite_cases(else_v, cap)?;
            if then_cases.len().checked_add(else_cases.len())? > cap {
                return None;
            }
            let mut out = Vec::with_capacity(then_cases.len() + else_cases.len());
            for (g, v) in then_cases {
                out.push((and_guard(cond_free.clone(), g), v));
            }
            for (g, v) in else_cases {
                out.push((and_guard(not_cond.clone(), g), v));
            }
            Some(out)
        }
        Formula::Neg(a) => Some(
            term_ite_cases(a, cap)?
                .into_iter()
                .map(|(g, v)| (g, Formula::Neg(Box::new(v))))
                .collect(),
        ),
        Formula::Add(a, b) => {
            bin_term_ite_cases(a, b, cap, |x, y| Formula::Add(Box::new(x), Box::new(y)))
        }
        Formula::Sub(a, b) => {
            bin_term_ite_cases(a, b, cap, |x, y| Formula::Sub(Box::new(x), Box::new(y)))
        }
        Formula::Mul(a, b) => {
            bin_term_ite_cases(a, b, cap, |x, y| Formula::Mul(Box::new(x), Box::new(y)))
        }
        Formula::Div(a, b) => {
            bin_term_ite_cases(a, b, cap, |x, y| Formula::Div(Box::new(x), Box::new(y)))
        }
        Formula::Rem(a, b) => {
            bin_term_ite_cases(a, b, cap, |x, y| Formula::Rem(Box::new(x), Box::new(y)))
        }
        // Leaf or opaque (Var/Int/UInt/SymVar/BV/Fp/Select/…): one guardless case.
        _ => Some(vec![(Formula::Bool(true), term.clone())]),
    }
}

pub(super) fn bin_term_ite_cases(
    a: &Formula,
    b: &Formula,
    cap: usize,
    mk: impl Fn(Formula, Formula) -> Formula,
) -> Option<Vec<(Formula, Formula)>> {
    let a_cases = term_ite_cases(a, cap)?;
    let b_cases = term_ite_cases(b, cap)?;
    if a_cases.len().checked_mul(b_cases.len())? > cap {
        return None;
    }
    let mut out = Vec::with_capacity(a_cases.len() * b_cases.len());
    for (ga, va) in &a_cases {
        for (gb, vb) in &b_cases {
            out.push((and_guard(ga.clone(), gb.clone()), mk(va.clone(), vb.clone())));
        }
    }
    Some(out)
}

/// Lift term-level `Ite`s out of a relation `R(a, b)`: if either side case-splits
/// on `Ite` conditions, emit `⋀ (guard_ij → R(a_i, b_j))` over the cross product.
pub(super) fn lift_relation_ites(
    a: &Formula,
    b: &Formula,
    cap: usize,
    mk: impl Fn(Formula, Formula) -> Formula,
) -> Formula {
    let (Some(a_cases), Some(b_cases)) = (term_ite_cases(a, cap), term_ite_cases(b, cap)) else {
        // Too many cases — leave the relation (with its Ite) unchanged (fail-open).
        return mk(a.clone(), b.clone());
    };
    if a_cases.len() == 1 && b_cases.len() == 1 {
        return mk(a.clone(), b.clone());
    }
    let mut conj = Vec::with_capacity(a_cases.len() * b_cases.len());
    for (ga, va) in &a_cases {
        for (gb, vb) in &b_cases {
            let guard = and_guard(ga.clone(), gb.clone());
            conj.push(guarded(guard, mk(va.clone(), vb.clone())));
        }
    }
    Formula::And(conj)
}

/// Cheap check: does `formula` contain an `Ite` anywhere (any position)? Used to
/// skip `eliminate_term_ites` (which rebuilds the tree) for the common `Ite`-free
/// VC. Robust across every variant via `Formula::children`.
pub(super) fn formula_contains_ite(formula: &Formula) -> bool {
    matches!(formula, Formula::Ite(..))
        || formula.children().iter().any(|c| formula_contains_ite(c))
}

/// GENERAL term-`Ite` elimination: rewrite a formula so no `Ite` appears in TERM
/// position, by lifting each `Ite` to a formula-level guard. This is the
/// backend-agnostic completion of `ite_free_equality`: it handles a term-`Ite`
/// anywhere in a postcondition — a residual `__ret == Ite` model fact, a nested
/// arithmetic `Lt(Ite(..)+k, n)`, or any FUTURE modeled-call value — not just the
/// `_0 == Ite` return pin. A term-`Ite` in a postcondition obligation is
/// otherwise undischargeable (trust-mc's PDR prunes it; trust-wp does not route
/// it), so eliminating it lets the obligation prove. Logically EQUIVALENT (an
/// `Ite` is its guarded case-split), so verdict-preserving and sound; fail-open
/// past `ITE_ELIM_CASE_CAP` (leaves the `Ite`, exactly today's behavior).
pub(super) fn eliminate_term_ites(formula: &Formula, cap: usize) -> Formula {
    match formula {
        Formula::Not(a) => Formula::Not(Box::new(eliminate_term_ites(a, cap))),
        Formula::And(xs) => Formula::And(xs.iter().map(|x| eliminate_term_ites(x, cap)).collect()),
        Formula::Or(xs) => Formula::Or(xs.iter().map(|x| eliminate_term_ites(x, cap)).collect()),
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(eliminate_term_ites(a, cap)),
            Box::new(eliminate_term_ites(b, cap)),
        ),
        Formula::Forall(vars, body) => {
            Formula::Forall(vars.clone(), Box::new(eliminate_term_ites(body, cap)))
        }
        Formula::Exists(vars, body) => {
            Formula::Exists(vars.clone(), Box::new(eliminate_term_ites(body, cap)))
        }
        // A boolean-valued `Ite` at formula position: `(c → t) ∧ (¬c → e)`.
        Formula::Ite(cond, then_f, else_f) => {
            let cond_free = eliminate_term_ites(cond, cap);
            Formula::And(vec![
                guarded(cond_free.clone(), eliminate_term_ites(then_f, cap)),
                guarded(Formula::Not(Box::new(cond_free)), eliminate_term_ites(else_f, cap)),
            ])
        }
        Formula::Eq(a, b) => {
            lift_relation_ites(a, b, cap, |x, y| Formula::Eq(Box::new(x), Box::new(y)))
        }
        Formula::Lt(a, b) => {
            lift_relation_ites(a, b, cap, |x, y| Formula::Lt(Box::new(x), Box::new(y)))
        }
        Formula::Le(a, b) => {
            lift_relation_ites(a, b, cap, |x, y| Formula::Le(Box::new(x), Box::new(y)))
        }
        Formula::Gt(a, b) => {
            lift_relation_ites(a, b, cap, |x, y| Formula::Gt(Box::new(x), Box::new(y)))
        }
        Formula::Ge(a, b) => {
            lift_relation_ites(a, b, cap, |x, y| Formula::Ge(Box::new(x), Box::new(y)))
        }
        // Leaves + theories we do not lift through (BV/Fp/Select/Store/Pred):
        // returned unchanged (fail-open — never introduces a term-Ite, never
        // changes meaning).
        _ => formula.clone(),
    }
}
