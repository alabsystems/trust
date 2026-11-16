//! Refute an equality chain without interpreting bitvector arithmetic.
//!
//! Each distinct, well-sorted bitvector TERM receives its own fresh Int skolem.
//! Only top-level equalities and disequalities enter the context. Any model of
//! the original formula induces a model of this weaker context: map the finitely
//! many term values (separately for each width) to integer representatives. Equal
//! terms get equal representatives; distinct values get distinct representatives.
//! No arithmetic, range, overflow, or source-clause fact is assumed by this map.
//!
//! Rust selects a path through actual equality hypotheses; the emitted term
//! uses only Eq.refl/symm/trans and the actual disequality hypothesis. The usual
//! AY cross-check, local Clean kernel, full-VC lineage, and payload round-trip
//! checks remain mandatory. The existing fenced reference mint independently
//! decides Certified authority; the raw payload alone cannot grant it.
//! Presented replay reconstructs the exact same context from the original goal,
//! never from certificate-supplied data, and requires the current reference check.

use std::collections::VecDeque;

use super::*;

const MAX_LEAVES: usize = 128;
const MAX_TERMS: usize = 128;
const MAX_NODES: usize = 4096;

struct Equality {
    from: usize,
    to: usize,
    hypothesis: FVarId,
}

struct Context {
    hypotheses: Vec<Hyp>,
    variables: BTreeSet<String>,
    equalities: Vec<Equality>,
    disequalities: Vec<Equality>,
    names: Vec<String>,
}

fn term_expr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn prepare<'a>(violation: &'a Formula) -> Option<Context> {
    // Before the recursive sort checker: pending width and leaf counts alone
    // do not bound a chain of single-child conjunctions or a deep term.
    if !within_node_bound(violation) || !branch_clamp::formula_is_well_sorted_bool(violation) {
        return None;
    }
    let mut pending = vec![violation];
    let mut leaves = 0;
    let mut term_ids: trust_types::fx::FxHashMap<&Formula, usize> =
        trust_types::fx::FxHashMap::default();
    let mut context = Context {
        hypotheses: vec![],
        variables: BTreeSet::new(),
        equalities: vec![],
        disequalities: vec![],
        names: vec![],
    };
    while let Some(formula) = pending.pop() {
        if let Formula::And(parts) = formula {
            // Bound both the pending work and the eventual leaf inventory.
            if pending.len().checked_add(parts.len())? > MAX_LEAVES {
                return None;
            }
            pending.extend(parts.iter().rev());
            continue;
        }
        leaves += 1;
        if leaves > MAX_LEAVES {
            return None;
        }
        let (negative, inner) = match formula {
            Formula::Not(inner) => (true, inner.as_ref()),
            other => (false, other),
        };
        let Formula::Eq(left, right) = inner else { continue };
        let Sort::BitVec(width) = trust_types::smt_logic::check_formula_sort(left).ok()? else {
            continue;
        };
        if !(1..=128).contains(&width)
            || trust_types::smt_logic::check_formula_sort(right).ok()? != Sort::BitVec(width)
        {
            return None;
        }
        let mut intern = |term: &'a Formula| {
            if let Some(&index) = term_ids.get(term) {
                return Some(index);
            }
            if context.names.len() >= MAX_TERMS {
                return None;
            }
            let index = context.names.len();
            term_ids.insert(term, index);
            let name = format!("trust_bv_equality_{index}");
            context.variables.insert(name.clone());
            context.names.push(name);
            Some(index)
        };
        let from = intern(left.as_ref())?;
        let to = intern(right.as_ref())?;
        let lhs = &context.names[from];
        let rhs = &context.names[to];
        let proposition = eq_int(term_expr(lhs), term_expr(rhs));
        let smt = format!("(= {lhs} {rhs})");
        let hypothesis = push_hyp(
            &mut context.hypotheses,
            if negative { format!("(not {smt})") } else { smt },
            if negative { not_prop(proposition) } else { proposition },
        );
        let equality = Equality { from, to, hypothesis };
        if negative {
            context.disequalities.push(equality);
        } else {
            context.equalities.push(equality);
        }
    }
    (!context.disequalities.is_empty()).then_some(context)
}

fn within_node_bound(formula: &Formula) -> bool {
    let mut pending = vec![formula];
    let mut visited = 0;
    while let Some(formula) = pending.pop() {
        visited += 1;
        let children = formula.children();
        if visited + pending.len() + children.len() > MAX_NODES {
            return false;
        }
        pending.extend(children);
    }
    true
}

fn equality_proof(context: &Context, start: usize, goal: usize) -> Option<Expr> {
    let mut predecessors = vec![None; context.names.len()];
    let mut seen = vec![false; context.names.len()];
    let mut pending = VecDeque::from([start]);
    seen[start] = true;
    while let Some(at) = pending.pop_front() {
        if at == goal {
            break;
        }
        for (index, equality) in context.equalities.iter().enumerate() {
            let (next, reversed) = if equality.from == at {
                (equality.to, false)
            } else if equality.to == at {
                (equality.from, true)
            } else {
                continue;
            };
            if !seen[next] {
                seen[next] = true;
                predecessors[next] = Some((at, index, reversed));
                pending.push_back(next);
            }
        }
    }
    if !seen[goal] {
        return None;
    }
    let mut path = Vec::new();
    let mut at = goal;
    while at != start {
        let (previous, index, reversed) = predecessors[at]?;
        path.push((previous, at, index, reversed));
        at = previous;
    }
    let root = term_expr(&context.names[start]);
    let mut proof = eq_refl_int(root.clone());
    for (from, to, index, reversed) in path.into_iter().rev() {
        let equality = &context.equalities[index];
        let mut step = Expr::fvar(equality.hypothesis);
        if reversed {
            step = eq_symm_int(
                term_expr(&context.names[equality.from]),
                term_expr(&context.names[equality.to]),
                step,
            );
        }
        proof = eq_trans_int(
            root.clone(),
            term_expr(&context.names[from]),
            term_expr(&context.names[to]),
            proof,
            step,
        );
    }
    Some(proof)
}

pub(super) fn certify(
    violation: &Formula,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let context = prepare(violation)?;
    let proof = context.disequalities.iter().find_map(|negative| {
        let equality = equality_proof(&context, negative.from, negative.to)?;
        Some(Expr::app(Expr::fvar(negative.hypothesis), equality))
    })?;
    finish_certificate(&context.hypotheses, &proof, &context.variables, identity)
}

pub(super) fn presented_context_variables(
    violation: &Formula,
    presented: &[u8],
) -> Option<BTreeSet<String>> {
    let context = prepare(violation)?;
    let expected = serialize_context(&reduced_context(&build_ctx(&context.hypotheses))).ok()?;
    (expected == presented).then_some(context.variables)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bv_equality_bounds_single_child_chains_before_recursive_sorting() {
        let mut formula = Formula::Bool(true);
        for _ in 0..MAX_NODES {
            formula = Formula::And(vec![formula]);
        }
        assert!(!within_node_bound(&formula));
        assert!(prepare(&formula).is_none());
        // Iterative destruction of this deliberately deep, known test shape.
        while let Formula::And(mut parts) = formula {
            assert_eq!(parts.len(), 1);
            formula = parts.pop().unwrap();
        }
    }

    #[test]
    fn bv_equality_does_not_interpret_arithmetic_even_when_terms_are_equal() {
        let x = Formula::Var("x".into(), Sort::BitVec(32));
        let one = Formula::BitVec { value: 1, width: 32 };
        let left = Formula::BvAdd(Box::new(x.clone()), Box::new(one.clone()), 32);
        let right = Formula::BvAdd(Box::new(one), Box::new(x), 32);
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(left), Box::new(right))));
        let identity = ObligationIdentity::from_violation(&formula).unwrap();
        assert!(certify(&formula, &identity).is_none(), "no commutativity axiom is imported");
    }

    #[test]
    fn bv_equality_rejects_a_validly_encoded_wrong_term_after_public_lineage_is_recomputed() {
        let a = Formula::Var("a".into(), Sort::BitVec(8));
        let b = Formula::Var("b".into(), Sort::BitVec(8));
        let equality = Formula::Eq(Box::new(a), Box::new(b));
        let vc = VerificationCondition {
            kind: trust_types::VcKind::Postcondition,
            function: "bv_equality_wrong_term".into(),
            location: Default::default(),
            formula: Formula::And(vec![equality.clone(), Formula::Not(Box::new(equality))]),
            contract_metadata: None,
            obligation: None,
        };
        let mut evidence = crate::certify_vc(&vc).expect("actual equality contradiction");
        assert!(crate::replay_presented_vc_evidence(&vc, &evidence));
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = &mut evidence else {
            panic!("actual Clean proof carrier")
        };
        // Well-formed CIC, but Eq.refl is not a proof of False. Recompute the
        // public integrity hash so this control reaches current-kernel checking.
        *term = serialize_term(&eq_refl_int(term_expr("trust_bv_equality_0"))).unwrap();
        let identity = ObligationIdentity::from_vc(&vc).unwrap();
        *lineage = lineage_digest(term, context, &identity);
        assert!(!crate::replay_presented_vc_evidence(&vc, &evidence));
    }
}
