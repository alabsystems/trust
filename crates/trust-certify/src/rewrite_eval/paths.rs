// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.
//! Reuse the existing rewrite evaluator inside each ORIGINAL disjunct.
//! Every branch must produce a proof; Or.rec joins those proofs in the kernel.
//! No solver answer, sibling-path assumption, or derived normalization fact is
//! admitted as a hypothesis. Earlier lanes retain their certificate bytes.

use clean_kernel::expr::ExprFolderOpt;

use super::*;

pub(super) fn certify(
    violation: &Formula,
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    with_prepared_context(violation, |paths, hypotheses, names, carrier, global| {
        let mut fresh = Fresh {
            next_id: 0,
            int_evaluation: IntEvaluation::Literals,
            proof_sharing: true,
            proof_bindings: Vec::new(),
        };
        let term = refute_paths(paths, carrier, global, &mut fresh)?;
        let term = share_closed_propositions(violation, term, &mut fresh)?;
        finish_certificate(hypotheses, &term, names, identity)
    })
}

/// Reconstruct the exact original context without entering the rewrite search.
pub(super) fn presented_context_variables(
    violation: &Formula,
    context: &[u8],
) -> Option<BTreeSet<String>> {
    with_prepared_context(violation, |_, hypotheses, names, _, _| {
        let expected = super::super::serialize_context(&super::super::reduced_context(
            &super::super::build_ctx(hypotheses),
        ))
        .ok()?;
        (expected == context).then(|| names.clone())
    })
}

fn with_prepared_context<T>(
    violation: &Formula,
    mut accept: impl FnMut(&[Formula], &[Hyp], &BTreeSet<String>, Expr, &[Fact]) -> Option<T>,
) -> Option<T> {
    // The existing aggregate rewritten-fact budget also bounds this entire
    // input, before encoding or cloning any path. Each branch retains the
    // existing flat evaluator's pool/node/rewrite/split limits.
    if node_count(violation) > MAX_TOTAL_FACT_NODES {
        return None;
    }
    let mut flat = Vec::new();
    flatten_and(violation, &mut flat);
    let mut seen = FxHashSet::default();
    flat.retain(|formula| seen.insert(*formula));
    if flat.is_empty()
        || flat.len() > MAX_POOL
        || flat.iter().any(|formula| matches!(formula, Formula::Bool(false)))
    {
        return None;
    }
    for candidate in &flat {
        let Formula::Or(paths) = candidate else { continue };
        if paths.len() < 2
            || paths.len() > super::super::PATH_MEMBERSHIP_MAX_PATHS
            || !paths.iter().all(|path| matches!(path, Formula::And(_)))
        {
            continue;
        }
        let kept: Vec<_> = flat
            .iter()
            .filter_map(|formula| {
                Some((*formula, enc_prop(formula, Hole::None)?, smt_prop(formula)?))
            })
            .collect();
        // The chosen disjunction itself must be translated in full. Other
        // unencodable conjuncts may be dropped, as in the existing flat lane.
        let Some(selected) = kept.iter().position(|(formula, ..)| *formula == *candidate) else {
            continue;
        };
        let formulas: Vec<_> = kept.iter().map(|(formula, ..)| *formula).collect();
        let Some(names) = injective_skolems(&formulas) else { continue };
        let mut hypotheses = Vec::new();
        let mut global = Vec::new();
        let mut carrier = None;
        for (index, (formula, proposition, smt)) in kept.into_iter().enumerate() {
            let proof = Expr::fvar(push_hyp(&mut hypotheses, smt, proposition));
            if index == selected {
                carrier = Some(proof);
            } else {
                global.push(Fact { formula: formula.clone(), proof });
            }
        }
        if let Some(result) = accept(paths, &hypotheses, &names, carrier?, &global) {
            return Some(result);
        }
    }
    None
}

struct PropositionFolder<'a> {
    aliases: &'a FxHashMap<Expr, FVarId>,
    memo: FxHashMap<Expr, Option<Expr>>,
}

impl ExprFolderOpt for PropositionFolder<'_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        if let Some(id) = self.aliases.get(expression) {
            return Some(Expr::fvar(*id));
        }
        if let Some(result) = self.memo.get(expression) {
            return result.clone();
        }
        #[cfg(kani)]
        let result = self.fold_expr_opt_inner_core(expression);
        #[cfg(not(kani))]
        let result = self.fold_expr_opt_inner_full(expression);
        self.memo.insert(expression.clone(), result.clone());
        result
    }
}

/// Share repeated closed proposition types as checked definitions of `Prop`.
/// Their exact existing encodings are the values; replacing a closed expression
/// under a binder cannot capture its bound variables. The wire format and its
/// original structural limits stay unchanged.
fn share_closed_propositions(violation: &Formula, proof: Expr, fresh: &mut Fresh) -> Option<Expr> {
    let mut pending = vec![(violation, false)];
    let mut seen = FxHashSet::default();
    let mut aliases = FxHashMap::default();
    let mut bindings = Vec::new();
    while let Some((formula, children_done)) = pending.pop() {
        if !children_done {
            if !seen.insert(formula) {
                continue;
            }
            pending.push((formula, true));
            let base = pending.len();
            trust_types::for_each_formula_child(formula, |child| pending.push((child, false)));
            pending[base..].reverse();
            continue;
        }
        if bindings.len() == MAX_POOL || node_count(formula) < 3 {
            continue;
        }
        let Some(proposition) = enc_prop(formula, Hole::None) else { continue };
        if proposition.has_fvar_quick()
            || proposition.has_loose_bvars_quick()
            || aliases.contains_key(&proposition)
        {
            continue;
        }
        let value = proposition
            .fold_opt_or_clone(&mut PropositionFolder { aliases: &aliases, memo: FxHashMap::default() });
        let id = fresh.next();
        aliases.insert(proposition, id);
        bindings.push((id, Expr::prop(), value));
    }
    let proof =
        proof.fold_opt_or_clone(&mut PropositionFolder { aliases: &aliases, memo: FxHashMap::default() });
    close_proof_bindings(proof, bindings)
}

fn path_facts(formula: &Formula, proof: Expr, out: &mut Vec<Fact>) -> Option<()> {
    match formula {
        Formula::Bool(false) => return None, // Same placeholder refusal as the flat lane.
        Formula::Bool(true) => {}
        Formula::And(parts) => {
            let propositions =
                parts.iter().map(|part| enc_prop(part, Hole::None)).collect::<Option<Vec<_>>>()?;
            for (part, proof) in parts.iter().zip(and_components(&propositions, proof)) {
                path_facts(part, proof, out)?;
            }
        }
        _ => out.push(Fact { formula: formula.clone(), proof }),
    }
    Some(())
}

fn refute_path(path: &Formula, carrier: Expr, global: &[Fact], fresh: &mut Fresh) -> Option<Expr> {
    let mut facts = global.to_vec();
    path_facts(path, carrier, &mut facts)?;
    let mut seen = FxHashSet::default();
    facts.retain(|fact| seen.insert(fact.formula.clone()));
    if facts.len() > MAX_POOL
        || facts.iter().map(|fact| node_count(&fact.formula)).sum::<usize>() > MAX_VIOLATION_NODES
    {
        return None;
    }
    // A path fact is a projection out of the ORIGINAL conjunction. Rewriting
    // may use that proof many times; copying the entire projection into every
    // use makes the serialized proof grow even though the expression DAG is
    // small. Bind each already-proved fact once in this branch's kernel term.
    // Its declared type is the same encoder the original hypothesis used.
    let mut bindings = Vec::with_capacity(facts.len());
    for fact in &mut facts {
        let id = fresh.next();
        let proposition = enc_prop(&fact.formula, Hole::None)?;
        bindings.push((id, proposition, fact.proof.clone()));
        fact.proof = Expr::fvar(id);
    }
    close_proof_bindings(refute(facts, fresh, MAX_SPLITS)?, bindings)
}

fn refute_paths(
    paths: &[Formula],
    carrier: Expr,
    global: &[Fact],
    fresh: &mut Fresh,
) -> Option<Expr> {
    match paths {
        [] => None,
        [only] => refute_path(only, carrier, global, fresh),
        [first, rest @ ..] => {
            let first_type = enc_prop(first, Hole::None)?;
            let rest_props =
                rest.iter().map(|path| enc_prop(path, Hole::None)).collect::<Option<Vec<_>>>()?;
            let rest_type = nest("Or", false_expr(), &rest_props);
            // Recursor arguments, motive and branch types all use these same
            // propositions. Preserve their definitions once instead of copying
            // the large remainder of the original disjunction at every use.
            let first_type_id = fresh.next();
            let rest_type_id = fresh.next();
            let first_prop = Expr::fvar(first_type_id);
            let rest_prop = Expr::fvar(rest_type_id);
            let left_id = fresh.next();
            let left = refute_path(first, Expr::fvar(left_id), global, fresh)?;
            let left =
                Expr::lam(BinderInfo::Default, first_prop.clone(), left.abstract_fvar(left_id));
            let right_id = fresh.next();
            let right = refute_paths(rest, Expr::fvar(right_id), global, fresh)?;
            let right =
                Expr::lam(BinderInfo::Default, rest_prop.clone(), right.abstract_fvar(right_id));
            let or_type = const_app("Or", [first_prop.clone(), rest_prop.clone()]);
            let motive = Expr::lam(BinderInfo::Default, or_type, false_expr());
            let proof = const_app("Or.rec", [first_prop, rest_prop, motive, left, right, carrier]);
            let proof = Expr::let_named(
                Name::anon(),
                Expr::prop(),
                rest_type,
                proof.abstract_fvar(rest_type_id),
                false,
            );
            Some(Expr::let_named(
                Name::anon(),
                Expr::prop(),
                first_type,
                proof.abstract_fvar(first_type_id),
                false,
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(reachable_first: bool) -> Formula {
        let x = || Formula::Var("x".into(), Sort::Int);
        let alias = || Formula::Var("alias".into(), Sort::Int);
        let bit = || Formula::Var("bit".into(), Sort::Bool);
        let eq = |left, right| Formula::Eq(Box::new(left), Box::new(right));
        let lt = |right| Formula::Lt(Box::new(alias()), Box::new(Formula::Int(right)));
        Formula::And(vec![
            eq(x(), Formula::Int(1)),
            Formula::Or(vec![
                Formula::And(vec![
                    eq(alias(), x()),
                    eq(bit(), lt(2)),
                    eq(bit(), Formula::Bool(reachable_first)),
                ]),
                Formula::And(vec![
                    eq(alias(), x()),
                    eq(bit(), lt(0)),
                    eq(bit(), Formula::Bool(true)),
                ]),
            ]),
        ])
    }

    fn on_stack<T: Send + 'static>(run: impl FnOnce() -> T + Send + 'static) -> T {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(run)
            .unwrap()
            .join()
            .unwrap()
    }

    #[test]
    fn captured_enum_return_paths_require_original_kernel_proofs() {
        on_stack(|| {
            let vc: trust_types::VerificationCondition =
                serde_json::from_str(include_str!(concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/tests/fixtures/d5b_repeated_enum_return_row.json"
                )))
                .unwrap();
            let identity = ObligationIdentity::from_vc(&vc).unwrap();
            let certified = certify(&vc.formula, &identity);
            let evidence = certified.expect("the captured original row must certify");
            assert!(crate::reference_certificate_for(&evidence).is_some());
            let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
                panic!("expected a real kernel certificate");
            };
            crate::reset_certify_memo();
            assert!(crate::recheck_vc_cleancic(&term, &context, &lineage, &vc));
        });
    }

    #[test]
    fn every_original_disjunct_needs_its_own_rewrite_proof() {
        on_stack(|| {
            let closed = fixture(false);
            let identity = ObligationIdentity::from_violation(&closed).unwrap();
            assert!(certify(&closed, &identity).is_some());
            let reachable = fixture(true); // x=alias=1, bit=true satisfies its first path.
            let identity = ObligationIdentity::from_violation(&reachable).unwrap();
            assert!(certify(&reachable, &identity).is_none());
            assert!(crate::certify_violation(&reachable).is_none());
        });
    }

    #[test]
    fn original_path_certificate_replays_and_rejects_a_different_formula() {
        on_stack(|| {
            let closed = fixture(false);
            let evidence = crate::certify_violation(&closed).unwrap();
            let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
                panic!("expected a real kernel certificate");
            };
            crate::reset_certify_memo();
            assert!(crate::recheck_cleancic(&term, &context, &lineage, &closed));
            assert!(!crate::recheck_cleancic(&term, &context, &lineage, &fixture(true)));
        });
    }

    #[test]
    fn path_placeholders_sort_collisions_and_resource_excess_still_refuse() {
        on_stack(|| {
            let mut placeholder = fixture(false);
            let Formula::And(parts) = &mut placeholder else { unreachable!() };
            let Formula::Or(paths) = &mut parts[1] else { unreachable!() };
            paths[0] = Formula::And(vec![Formula::Bool(false)]);
            let identity = ObligationIdentity::from_violation(&placeholder).unwrap();
            assert!(certify(&placeholder, &identity).is_none());

            let mut collision = fixture(false);
            let Formula::And(parts) = &mut collision else { unreachable!() };
            parts.push(Formula::Var("x".into(), Sort::Bool));
            let identity = ObligationIdentity::from_violation(&collision).unwrap();
            assert!(certify(&collision, &identity).is_none());

            let excessive = Formula::And(vec![fixture(false); MAX_TOTAL_FACT_NODES]);
            let identity = ObligationIdentity::from_violation(&excessive).unwrap();
            assert!(certify(&excessive, &identity).is_none());
        });
    }
}
