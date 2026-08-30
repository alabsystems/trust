//! Certified branch-clamp postcondition lane.
//!
//! This module is deliberately separate from the generic disjunctive
//! certifier.  The canonical R171 parser and proof constructor run first and
//! remain byte-for-byte unchanged.  Only a canonical miss may enter this
//! bounded lane, which distributes one decidable negated conjunction per arm,
//! derives syntactically entailed Boolean facts, and closes a strict order
//! cycle with a real Clean term.

use super::*;

const MAX_ARMS: usize = 16;
const MAX_MEMBERS: usize = 256;
const MAX_REIFICATIONS: usize = 64;
const MAX_DERIVED_FACTS: usize = 128;
const MAX_ORDER_ATOMS: usize = 48;
const MAX_CYCLE_EDGES: usize = 24;
const MAX_EDGE_SET: usize = 48;
const MAX_DFS_INSPECTIONS: usize = 4096;

pub(super) fn formula_is_well_sorted_bool(formula: &Formula) -> bool {
    trust_types::smt_logic::check_formula_sort(formula) == Ok(Sort::Bool)
}

/// Retry a canonical disjunction only after an exact, bounded transformation.
pub(super) fn try_build_disjunctive_certificate(
    disjuncts: &[Formula],
    context_edges: &[OrderEdge],
    hyps: &mut Vec<Hyp>,
    var_names: &mut BTreeSet<String>,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let expanded = distribute_negated_conjunctions(disjuncts)?;
    super::build_disjunctive_certificate_with_parser(
        &expanded,
        context_edges,
        hyps,
        var_names,
        identity,
        parse_disjunct,
    )
}

fn parse_disjunct(di: &Formula) -> Option<Disjunct<'_>> {
    super::parse_disjunct_with_and(di, parse_and_disjunct_entailed_order_atoms)
}

/// Project the right-nested conjunction carried by a derived branch and close
/// its order graph.  Every projected proposition is paired with the exact atom
/// whose edge receives its proof; Clean checks every `And.left`/`And.right` and
/// order lemma application.
pub(super) fn refute_derived_chain_atoms(
    atoms: &[(Formula, Formula, bool)],
    props: &[Expr],
    context: &[OrderEdge],
    h: Expr,
) -> Option<Expr> {
    if atoms.len() != props.len() || atoms.is_empty() {
        return None;
    }

    let mut edges = context.to_vec();
    let mut rest_proof = h;
    for (index, (a, b, strict)) in atoms.iter().enumerate() {
        let proof = if index + 1 == atoms.len() {
            rest_proof.clone()
        } else {
            let tail = build_and_prop(&props[index + 1..])?;
            let left =
                const_app("And.left", [props[index].clone(), tail.clone(), rest_proof.clone()]);
            rest_proof = const_app("And.right", [props[index].clone(), tail, rest_proof]);
            left
        };
        edges.extend(build_order_edges(a, b, *strict, proof));
    }

    refute_via_chain_edges(&edges).or_else(|| refute_via_var_cycle_k(&edges))
}

/// Close an order cycle containing at least one strict edge.
///
/// Starting from `a < b`, a bounded DFS finds `b <=* a`; strict path edges are
/// weakened with `Int.le_of_lt`, and `Int.lt_of_lt_of_le` folds the path into
/// `a < a`, closed by `Int.lt_irrefl`.  All-nonstrict cycles are intentionally
/// ignored because equality is a satisfying model for them.
fn refute_via_var_cycle_k(edges: &[OrderEdge]) -> Option<Expr> {
    refute_via_var_cycle_k_with_budget(edges, MAX_DFS_INSPECTIONS)
}

fn refute_via_var_cycle_k_with_budget(
    edges: &[OrderEdge],
    inspection_budget: usize,
) -> Option<Expr> {
    if edges.is_empty() || edges.len() > MAX_EDGE_SET || inspection_budget == 0 {
        return None;
    }

    fn find_return_path(
        edges: &[OrderEdge],
        at: &ChainNode,
        goal: &ChainNode,
        remaining: usize,
        inspections: &mut usize,
        visited: &mut Vec<ChainNode>,
        path: &mut Vec<usize>,
    ) -> bool {
        if remaining == 0 {
            return false;
        }
        for (index, edge) in edges.iter().enumerate() {
            if *inspections == 0 {
                return false;
            }
            *inspections -= 1;
            if edge.from != *at {
                continue;
            }
            if edge.to == *goal {
                path.push(index);
                return true;
            }
            if visited.contains(&edge.to) {
                continue;
            }
            visited.push(edge.to.clone());
            path.push(index);
            if find_return_path(edges, &edge.to, goal, remaining - 1, inspections, visited, path) {
                return true;
            }
            path.pop();
            visited.pop();
        }
        false
    }

    let mut inspections = inspection_budget;
    for start in edges.iter().filter(|edge| edge.strict) {
        if start.from == start.to {
            return Some(Expr::app(
                const_app("Int.lt_irrefl", [start.from_expr.clone()]),
                start.hyp.clone(),
            ));
        }

        let mut path = Vec::new();
        let mut visited = vec![start.from.clone(), start.to.clone()];
        if !find_return_path(
            edges,
            &start.to,
            &start.from,
            MAX_CYCLE_EDGES - 1,
            &mut inspections,
            &mut visited,
            &mut path,
        ) {
            if inspections == 0 {
                return None;
            }
            continue;
        }

        let origin = start.from_expr.clone();
        let mut tip = start.to_expr.clone();
        let mut cur = start.hyp.clone();
        for index in path {
            let edge = &edges[index];
            let le_step = if edge.strict {
                const_app(
                    "Int.le_of_lt",
                    [edge.from_expr.clone(), edge.to_expr.clone(), edge.hyp.clone()],
                )
            } else {
                edge.hyp.clone()
            };
            cur = const_app(
                "Int.lt_of_lt_of_le",
                [origin.clone(), tip, edge.to_expr.clone(), cur, le_step],
            );
            tip = edge.to_expr.clone();
        }
        return Some(Expr::app(const_app("Int.lt_irrefl", [origin]), cur));
    }
    None
}

/// Derive the small Boolean/reification consequence closure needed by one arm.
/// Every admitted rule is an entailment from facts already carried by that arm.
fn derive_disjunct_entailed_atoms(pool: &[&Formula]) -> Option<Vec<Formula>> {
    fn fact_entails_condition(fact: &Formula, condition: &Formula) -> bool {
        if fact == condition {
            return true;
        }
        if let Formula::Not(outer) = condition
            && let Formula::Not(inner) = outer.as_ref()
        {
            return fact_entails_condition(fact, inner);
        }
        false
    }

    fn is_bool_leaf(f: &Formula) -> bool {
        matches!(f, Formula::Var(_, Sort::Bool) | Formula::SymVar(_, Sort::Bool))
    }

    /// Add a fresh consequence without ever materializing more than the cap.
    /// The limit is a peak-work bound, not merely a post-hoc output check.
    fn push_unique(
        pool: &[&Formula],
        derived: &[Formula],
        fresh: &mut Vec<Formula>,
        fact: Formula,
    ) -> Option<()> {
        if pool.iter().any(|present| **present == fact)
            || derived.iter().any(|present| *present == fact)
            || fresh.iter().any(|present| *present == fact)
        {
            return Some(());
        }
        if derived.len().checked_add(fresh.len())? >= MAX_DERIVED_FACTS {
            return None;
        }
        fresh.push(fact);
        Some(())
    }

    if pool.is_empty() || pool.len() > MAX_MEMBERS {
        return None;
    }
    for &fact in pool {
        if !formula_is_well_sorted_bool(fact) {
            return None;
        }
    }

    let mut defs: Vec<(Formula, &Formula)> = Vec::new();
    for &fact in pool {
        let Formula::Eq(left, right) = fact else { continue };
        let pair = if is_bool_leaf(left) {
            Some((left.as_ref().clone(), right.as_ref()))
        } else if is_bool_leaf(right) {
            Some((right.as_ref().clone(), left.as_ref()))
        } else {
            None
        };
        let Some((leaf, body)) = pair else { continue };
        if !formula_is_well_sorted_bool(body) {
            return None;
        }
        if defs.len() == MAX_REIFICATIONS {
            return None;
        }
        defs.push((leaf, body));
    }

    let mut derived = Vec::new();
    for _ in 0..4 {
        let mut fresh = Vec::new();
        for asserted in pool.iter().copied().chain(derived.iter()) {
            for (leaf, body) in &defs {
                if asserted == leaf {
                    push_unique(pool, &derived, &mut fresh, (*body).clone())?;
                } else if asserted == *body {
                    push_unique(pool, &derived, &mut fresh, leaf.clone())?;
                }
                if let Formula::Not(inner) = asserted {
                    if inner.as_ref() == leaf {
                        push_unique(
                            pool,
                            &derived,
                            &mut fresh,
                            Formula::Not(Box::new((*body).clone())),
                        )?;
                    } else if inner.as_ref() == *body {
                        push_unique(
                            pool,
                            &derived,
                            &mut fresh,
                            Formula::Not(Box::new(leaf.clone())),
                        )?;
                    }
                }
            }
        }

        for candidate in pool.iter().copied().chain(derived.iter()) {
            let Formula::Implies(condition, consequence) = candidate else { continue };
            let present = pool
                .iter()
                .copied()
                .chain(derived.iter())
                .chain(fresh.iter())
                .any(|fact| fact_entails_condition(fact, condition));
            if present {
                push_unique(pool, &derived, &mut fresh, consequence.as_ref().clone())?;
            }
        }

        if fresh.is_empty() {
            break;
        }
        derived.extend(fresh);
    }
    Some(derived)
}

/// Distribute the first `not (A and B ...)` found in each conjunction arm.
/// The pieces are restricted to supported integer-order propositions, whose
/// decidability makes this exact split valid in the constructive carrier too.
fn distribute_negated_conjunctions(arms: &[Formula]) -> Option<Vec<Formula>> {
    if arms.is_empty() || arms.len() > MAX_ARMS {
        return None;
    }
    let mut out = Vec::new();
    let mut changed = false;
    for arm in arms {
        if !matches!(arm, Formula::And(_)) {
            out.push(arm.clone());
            continue;
        }
        let mut members = Vec::new();
        collect_conjuncts(arm, &mut members);
        if members.is_empty() || members.len() > MAX_MEMBERS {
            return None;
        }
        let target = members.iter().position(
            |member| matches!(member, Formula::Not(inner) if matches!(inner.as_ref(), Formula::And(_))),
        );
        let Some(target) = target else {
            out.push(arm.clone());
            if out.len() > MAX_ARMS {
                return None;
            }
            continue;
        };
        let Formula::Not(inner) = members[target] else { unreachable!() };
        let Formula::And(pieces) = inner.as_ref() else { unreachable!() };
        if pieces.is_empty() || out.len().checked_add(pieces.len())? > MAX_ARMS {
            return None;
        }
        if pieces
            .iter()
            .any(|piece| normalize_atom(&Formula::Not(Box::new(piece.clone()))).is_none())
        {
            return None;
        }
        for piece in pieces {
            let mut expanded: Vec<Formula> = members.iter().map(|item| (*item).clone()).collect();
            expanded[target] = Formula::Not(Box::new(piece.clone()));
            out.push(Formula::And(expanded));
        }
        changed = true;
    }
    changed.then_some(out)
}

/// Parse a distributed arm as order facts entailed by the authored arm.
fn parse_and_disjunct_entailed_order_atoms(di: &Formula) -> Option<Disjunct<'_>> {
    let mut flat = Vec::new();
    collect_conjuncts(di, &mut flat);
    if flat.is_empty() || flat.len() > MAX_MEMBERS {
        return None;
    }
    let derived = derive_disjunct_entailed_atoms(&flat)?;

    let mut atoms: Vec<(Formula, Formula, bool)> = Vec::new();
    let mut props = Vec::new();
    let mut smts = Vec::new();
    for fact in flat.iter().copied().chain(derived.iter()) {
        let Some(normalized) = normalize_atom(fact) else { continue };
        for atom in normalized {
            let (Some(prop), Some(smt)) = (linear_atom_prop(&atom), linear_atom_smt(&atom)) else {
                continue;
            };
            let owned = match atom {
                Atom::Lt(a, b) => (a.clone(), b.clone(), true),
                Atom::Le(a, b) => (a.clone(), b.clone(), false),
            };
            if atoms.iter().any(|present| present == &owned) {
                continue;
            }
            if atoms.len() == MAX_ORDER_ATOMS {
                return None;
            }
            atoms.push(owned);
            props.push(prop);
            smts.push(smt);
        }
    }
    if atoms.len() < 2 {
        return None;
    }
    Some(Disjunct {
        prop: build_and_prop(&props)?,
        smt: build_and_smt(&smts)?,
        refutation: DisjunctRefutation::DerivedChainAtoms { atoms, props },
    })
}

#[cfg(test)]
#[path = "branch_clamp/tests.rs"]
mod tests;
