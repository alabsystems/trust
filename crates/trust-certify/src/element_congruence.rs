// trust-certify/src/element_congruence.rs: the element-read congruence lane.
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

//! The ELEMENT-READ CONGRUENCE lane (Trust, VGAPS-G1C of the verifier-gaps design,
//! trust-ir `reports/2026-10-08-session-4b77663c/designs/trust-verifier-gaps-final.md`
//! §2.4, 2026-10-20).
//!
//! # The rows this exists for
//!
//! trust-vcgen's element-read congruence (`value_facts::build_element_read_congruence_facts`)
//! conjoins, for two reads of one element through two index temps, the fact
//!
//! ```text
//! Or([Not(Eq(_8, _12)), Eq(digits*[_8], digits*[_12])])
//! ```
//!
//! and a guarded re-read (`if a[i] > 0 { a[i] - 1 }`) is PROVED through it. No lane
//! above certified such a row: the disjunctive lane's parser takes an `Eq` disjunct
//! (two order atoms, not one) and a `Not(Eq)` disjunct (no order atom) for neither of
//! its shapes, and the disequality split splits only a TOP-LEVEL `Not(Eq)`.
//!
//! # The certificate
//!
//! `Or.rec` over the congruence, against the conjunctive context (the same context
//! the disjunctive lane builds, [`super::build_disjunctive_context`]):
//!
//! * the `Not(Eq(a, b))` branch, hypothesis `h : Not (Eq a b)`, is closed by
//!   `h (Int.le_antisymm a b h_ab h_ba)`, where `h_ab : a ≤ b` and `h_ba : b ≤ a` are
//!   folded from a path of CONTEXT edges (`_8 = i` and `_12 = i` give `_8 ≤ i ≤ _12`
//!   and back) with `Int.le_trans` and `Int.le_of_lt`. `Int.le_antisymm` is a
//!   constructive theorem of the kernel environment (`clean-kernel`
//!   `algebra_int_le_antisymm_proof.rs`, empty axiom closure). The branch's
//!   proposition is the disjunct itself: nothing is derived in Rust;
//! * the value tie `Eq(x, y)` is the two-atom `And(x ≤ y, y ≤ x)` the disjunctive lane
//!   already uses for an equality ([`super::normalize_atom`]'s split, the same one every
//!   context `Eq` goes through), refuted with the context by the chain engine;
//! * any other disjunct takes the primary parser's shapes, unchanged.
//!
//! The HARDENED TWIN of such a row carries a second disjunction, its own overflow core
//! `Or([d - 1 < 0, d - 1 > MAX])`, so neither `Or` closes against the conjunctive
//! context alone. One recursion step closes it ([`certify_congruence_then`]): `Or.rec`
//! over the congruence, its disequality branch as above, and its tie branch
//! `Or.rec` over the core with the tie's two edges added to the context
//! ([`refute_tie_then`]; the tie's projections are built over a placeholder free
//! variable that the kernel's own `abstract_fvar`/`instantiate` bind under the inner
//! binders, so no de Bruijn index is counted by hand).
//!
//! The design's rejected alternative (F7): a `NORMALIZATION_STEPS` derivation of
//! `Eq(x, y)` from the `Or` and the index equalities would put a Rust-justified
//! hypothesis into the `KernelCertified` context. Here the index equality is derived
//! by the kernel, from hypotheses that are the violation's own conjuncts.
//!
//! # Byte stability
//!
//! The lane runs after every other lane in `certify_lanes`, and only on a candidate
//! `Or` with a variable `Not(Eq)` disjunct, so no certificate this producer already
//! mints changes shape or bytes, and `recheck_cleancic` regenerates through the same
//! lane order. (The design's F8 flag on the shared parser is not needed: this lane
//! has its own parser and never runs inside the primary, distributed or branch-clamp
//! attempts.)
//!
//! # Soundness
//!
//! The context is a subset of the violation's conjuncts, the candidate is the
//! violation's own `Or` (its `Eq` disjunct spelled as the two inequalities it is
//! equivalent to over ℤ), every step is a kernel constant re-checked by the clean
//! kernel in [`super::finish_certificate`], and ay's required UNSAT cross-check runs on
//! the same hypotheses. A satisfiable violation has no refutation: a `Not(Eq)` branch
//! whose indices the context does not force equal has no `a ≤ b ∧ b ≤ a` path, and
//! the lane declines.

use super::*;

/// `Not(Eq(a, b))` over two PLAIN chain endpoints (a variable or a literal, not two
/// literals, not one node twice): the index disequality of a congruence.
fn index_disequality(f: &Formula) -> Option<(&Formula, &Formula)> {
    let Formula::Not(inner) = f else { return None };
    let Formula::Eq(a, b) = inner.as_ref() else { return None };
    let (na, nb) = (chain_node(a)?, chain_node(b)?);
    let plain = |n: &ChainNode| matches!(n, ChainNode::Var(_) | ChainNode::Lit(_));
    if !plain(&na) || !plain(&nb) || na == nb {
        return None;
    }
    if matches!((&na, &nb), (ChainNode::Lit(_), ChainNode::Lit(_))) {
        return None;
    }
    Some((a, b))
}

/// The congruence lane's disjunct parser: the index disequality, the value tie as two
/// order atoms, and otherwise the primary parser's shapes.
fn parse_congruence_disjunct(di: &Formula) -> Option<Disjunct<'_>> {
    if let Some((a, b)) = index_disequality(di) {
        let (ak, bk) = (linear_term_to_kernel(a)?, linear_term_to_kernel(b)?);
        let smt = format!("(not (= {} {}))", linear_term_to_smt(a)?, linear_term_to_smt(b)?);
        return Some(Disjunct {
            prop: not_prop(eq_int(ak, bk)),
            smt,
            refutation: DisjunctRefutation::Disequality { a, b },
        });
    }
    if let Some((prop, smt, atoms, props)) = value_tie(di) {
        return Some(Disjunct {
            prop,
            smt,
            refutation: DisjunctRefutation::ChainAtoms { atoms, props },
        });
    }
    parse_disjunct_with_and(di, parse_and_disjunct_present_order_atoms)
}

/// The tie parts of a congruence's value disjunct: a non-closed `Eq(x, y)` as
/// [`super::normalize_atom`]'s two order atoms `x ≤ y`, `y ≤ x` — their right-nested
/// `And` proposition and SMT, and the atoms with their per-atom propositions.
#[allow(clippy::type_complexity)]
fn value_tie(di: &Formula) -> Option<(Expr, String, Vec<(Formula, Formula, bool)>, Vec<Expr>)> {
    let Formula::Eq(..) = di else { return None };
    if matches!(closed_int_eq_operands(di), (Some(_), Some(_))) {
        return None;
    }
    let atoms = normalize_atom(di)?;
    let mut chain = Vec::new();
    let mut props = Vec::new();
    let mut smts = Vec::new();
    for atom in &atoms {
        let Atom::Le(x, y) = atom else { return None };
        props.push(linear_atom_prop(atom)?);
        smts.push(linear_atom_smt(atom)?);
        chain.push(((*x).clone(), (*y).clone(), false));
    }
    Some((build_and_prop(&props)?, build_and_smt(&smts)?, chain, props))
}

/// The nested lane's parser for the congruence `C` when ANOTHER disjunction `V` of the
/// violation is what its value branch contradicts: the tie becomes
/// [`DisjunctRefutation::ChainAtomsThen`] over `then` (V's parsed disjuncts, bound to
/// `then_hyp`); the disequality and every other disjunct parse as in
/// [`parse_congruence_disjunct`].
fn parse_congruence_disjunct_then<'a>(
    di: &'a Formula,
    then: &[Disjunct<'a>],
    then_hyp: &Expr,
) -> Option<Disjunct<'a>> {
    if let Some((prop, smt, atoms, props)) = value_tie(di) {
        let then = then.iter().map(clone_disjunct).collect::<Option<Vec<_>>>()?;
        return Some(Disjunct {
            prop,
            smt,
            refutation: DisjunctRefutation::ChainAtomsThen {
                atoms,
                props,
                then,
                then_hyp: then_hyp.clone(),
            },
        });
    }
    parse_congruence_disjunct(di)
}

/// A copy of a parsed disjunct, for the shapes the nested lane's `then` carries (a
/// disjunct of `V` is parsed by [`parse_congruence_disjunct`]); `None` for a shape it
/// does not copy, which declines the nested attempt.
fn clone_disjunct<'a>(d: &Disjunct<'a>) -> Option<Disjunct<'a>> {
    let refutation = match &d.refutation {
        DisjunctRefutation::ClosedAtom(atom) => DisjunctRefutation::ClosedAtom(ClosedOrderAtom {
            a: atom.a,
            b: atom.b,
            is_lt: atom.is_lt,
        }),
        DisjunctRefutation::ClosedEq { a, b } => DisjunctRefutation::ClosedEq { a: *a, b: *b },
        DisjunctRefutation::ChainAtom { a, b, strict } => {
            DisjunctRefutation::ChainAtom { a, b, strict: *strict }
        }
        DisjunctRefutation::ChainAtoms { atoms, props } => {
            DisjunctRefutation::ChainAtoms { atoms: atoms.clone(), props: props.clone() }
        }
        DisjunctRefutation::Disequality { a, b } => DisjunctRefutation::Disequality { a, b },
        _ => return None,
    };
    Some(Disjunct { prop: d.prop.clone(), smt: d.smt.clone(), refutation })
}

/// Every Int variable a parsed disjunct's refutation names (recursively through a
/// nested `then`), so the certificate declares it.
fn collect_disjunct_vars(d: &Disjunct<'_>, out: &mut BTreeSet<String>) {
    match &d.refutation {
        DisjunctRefutation::ChainAtom { a, b, .. } | DisjunctRefutation::Disequality { a, b } => {
            collect_formula_int_vars(a, out);
            collect_formula_int_vars(b, out);
        }
        DisjunctRefutation::InternalAndPair { var, .. } => {
            out.insert(var.clone());
        }
        DisjunctRefutation::ChainAtoms { atoms, .. }
        | DisjunctRefutation::DerivedChainAtoms { atoms, .. } => {
            for (a, b, _) in atoms {
                collect_formula_int_vars(a, out);
                collect_formula_int_vars(b, out);
            }
        }
        DisjunctRefutation::ChainAtomsThen { atoms, then, .. } => {
            for (a, b, _) in atoms {
                collect_formula_int_vars(a, out);
                collect_formula_int_vars(b, out);
            }
            for t in then {
                collect_disjunct_vars(t, out);
            }
        }
        DisjunctRefutation::ClosedAtom(_) | DisjunctRefutation::ClosedEq { .. } => {}
    }
}

/// A placeholder hypothesis id for the tie's branch hypothesis while the nested `V`
/// refutation is built under its own binders; abstracted away before the term is
/// returned, so it never reaches a certificate. Clear of every context id
/// (`HYP_FVAR_BASE + i` for the violation's few hypotheses).
const TIE_PLACEHOLDER_FVAR: u64 = HYP_FVAR_BASE + 1_000_000;

/// The tie branch of a congruence (`h : x ≤ y ∧ y ≤ x`) refuted through ANOTHER
/// disjunction of the violation, `then_hyp : V`: `Or.rec` over `V`, each of whose
/// disjuncts is refuted against the context extended by the tie's two projected
/// edges. The `V` term opens binders of its own, so the tie's projections are built
/// over a placeholder free variable and that variable is then abstracted and
/// instantiated with `h` (lifted under each binder by the kernel's own
/// `instantiate`), never spelled as a hand-counted de Bruijn index.
pub(super) fn refute_tie_then(
    atoms: &[(Formula, Formula, bool)],
    props: &[Expr],
    then: &[Disjunct<'_>],
    then_hyp: &Expr,
    context: &[OrderEdge],
    h: Expr,
) -> Option<Expr> {
    let placeholder = FVarId::new(TIE_PLACEHOLDER_FVAR);
    let mut edges = context.to_vec();
    let mut rest_proof = Expr::fvar(placeholder);
    for i in 0..atoms.len() {
        let (a, b, strict) = (&atoms[i].0, &atoms[i].1, atoms[i].2);
        let proof = if i + 1 == atoms.len() {
            rest_proof.clone()
        } else {
            let tail = build_and_prop(&props[i + 1..])?;
            let left = const_app("And.left", [props[i].clone(), tail.clone(), rest_proof.clone()]);
            rest_proof = const_app("And.right", [props[i].clone(), tail, rest_proof]);
            left
        };
        edges.extend(build_order_edges(a, b, strict, proof));
    }
    let body = build_disjunctive_false(then, &edges, then_hyp.clone())?;
    Some(body.abstract_fvar(placeholder).instantiate(&h))
}

/// `h : Not (Eq a b)` refuted against `context`: `h (Int.le_antisymm a b h_ab h_ba)`.
pub(super) fn refute_disequality(
    a: &Formula,
    b: &Formula,
    context: &[OrderEdge],
    h: Expr,
) -> Option<Expr> {
    let (na, nb) = (chain_node(a)?, chain_node(b)?);
    let h_ab = le_along_edges(context, &na, &nb)?;
    let h_ba = le_along_edges(context, &nb, &na)?;
    let eq = const_app(
        "Int.le_antisymm",
        [linear_term_to_kernel(a)?, linear_term_to_kernel(b)?, h_ab, h_ba],
    );
    Some(Expr::app(h, eq))
}

/// A proof of `from ≤ to` folded along a path of `edges` (depth-first in edge order,
/// so `recheck_cleancic` regenerates the identical term; each node at most once,
/// at most [`MAX_PATH`] edges): a strict edge is weakened by `Int.le_of_lt`, and
/// consecutive edges compose by `Int.le_trans`.
fn le_along_edges(edges: &[OrderEdge], from: &ChainNode, to: &ChainNode) -> Option<Expr> {
    const MAX_PATH: usize = 24;
    fn dfs<'e>(
        edges: &'e [OrderEdge],
        at: &ChainNode,
        goal: &ChainNode,
        path: &mut Vec<&'e OrderEdge>,
        visited: &mut Vec<ChainNode>,
    ) -> bool {
        if path.len() >= MAX_PATH {
            return false;
        }
        for e in edges {
            if e.from != *at {
                continue;
            }
            if e.to == *goal {
                path.push(e);
                return true;
            }
            if visited.contains(&e.to) {
                continue;
            }
            visited.push(e.to.clone());
            path.push(e);
            if dfs(edges, &e.to, goal, path, visited) {
                return true;
            }
            path.pop();
        }
        false
    }
    let mut path = Vec::new();
    let mut visited = vec![from.clone()];
    if !dfs(edges, from, to, &mut path, &mut visited) {
        return None;
    }
    let le = |e: &OrderEdge| {
        if e.strict {
            const_app("Int.le_of_lt", [e.from_expr.clone(), e.to_expr.clone(), e.hyp.clone()])
        } else {
            e.hyp.clone()
        }
    };
    let (first, rest) = path.split_first()?;
    let start = first.from_expr.clone();
    let mut tip = first.to_expr.clone();
    let mut proof = le(first);
    for e in rest {
        proof = const_app(
            "Int.le_trans",
            [start.clone(), tip.clone(), e.to_expr.clone(), proof, le(e)],
        );
        tip = e.to_expr.clone();
    }
    Some(proof)
}

/// LAST-RESORT lane: refute `context ∧ C` for a candidate congruence `C` (an `Or`
/// conjunct with an index-disequality disjunct), against the full context, then the
/// relevance-pruned ones the disjunctive lane's Attempt 2 uses (the variable-connected
/// component, then the one-hop set), each tried only when it differs from the full
/// context. See the module doc for the certificate and why no other lane's bytes move.
pub(super) fn certify_element_congruence_disjunction(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let mut candidates: Vec<&Vec<Formula>> = Vec::new();
    let mut context: Vec<&Formula> = Vec::new();
    for &c in conjuncts {
        match c {
            Formula::Or(ds) => {
                if ds.iter().any(|d| index_disequality(d).is_some()) {
                    candidates.push(ds);
                }
            }
            other => context.push(other),
        }
    }
    if candidates.is_empty() {
        return None;
    }
    for pruning in [None, Some(true), Some(false)] {
        for disjuncts in &candidates {
            let pruned;
            let ctx: &[&Formula] = match pruning {
                None => &context,
                Some(transitive) => {
                    pruned = relevant_context_conjuncts(disjuncts, &context, transitive);
                    if pruned.len() == context.len() {
                        continue;
                    }
                    &pruned
                }
            };
            let Some((mut hyps, edges, mut names)) = build_disjunctive_context(ctx) else {
                continue;
            };
            if let Some(evidence) = build_disjunctive_certificate_with_parser(
                disjuncts,
                &edges,
                &mut hyps,
                &mut names,
                identity,
                parse_congruence_disjunct,
            ) {
                return Some(evidence);
            }
        }
    }
    certify_congruence_then(conjuncts, &candidates, &context, identity)
}

/// The hardened twin: the congruence `C` and the twin's own overflow core `V`
/// (`Or([d - 1 < 0, d - 1 > MAX])`) are both disjunctions, so neither closes against
/// the conjunctive context alone. `Or.rec` over `C`: its disequality branch closes by
/// antisymmetry as in the single lane, and its tie branch by `Or.rec` over `V` with
/// the tie's edges in the context ([`refute_tie_then`]). `V` is any OTHER `Or`
/// conjunct, tried in conjunct order against the full context, then against the
/// context within one hop of `C`'s and `V`'s variables ([`one_hop_context`]); its
/// hypothesis is bound before `C`'s. A real twin's full context carries the range of
/// every local of the body: on the twins of trust-vcgen's
/// `element_read_congruence_realmir` fixtures the full context declined for seven of
/// nine rows, and the one-hop context closed all nine.
fn certify_congruence_then(
    conjuncts: &[&Formula],
    candidates: &[&Vec<Formula>],
    context: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    for congruence in candidates {
        for &other in conjuncts {
            let Formula::Or(v_disjuncts) = other else { continue };
            if std::ptr::eq(v_disjuncts, *congruence) {
                continue;
            }
            let mut seeds = BTreeSet::new();
            for d in congruence.iter().chain(v_disjuncts).filter_map(parse_congruence_disjunct) {
                collect_disjunct_vars(&d, &mut seeds);
            }
            let pruned = one_hop_context(&seeds, context);
            let tries = if pruned.len() == context.len() { 1 } else { 2 };
            for ctx in [context, &pruned[..]].into_iter().take(tries) {
                if let Some(evidence) =
                    certify_congruence_then_in(congruence, v_disjuncts, ctx, identity)
                {
                    return Some(evidence);
                }
            }
        }
    }
    None
}

/// [`certify_congruence_then`] for one congruence `C`, one other disjunction `V` and
/// one context.
fn certify_congruence_then_in(
    congruence: &[Formula],
    v_disjuncts: &[Formula],
    context: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let (mut hyps, edges, mut names) = build_disjunctive_context(context)?;
    let v_parsed = v_disjuncts.iter().map(parse_congruence_disjunct).collect::<Option<Vec<_>>>()?;
    let v_prop = build_or_prop(&v_parsed.iter().map(|d| d.prop.clone()).collect::<Vec<_>>())?;
    let v_fvar = FVarId::new(HYP_FVAR_BASE + hyps.len() as u64);
    let v_smt =
        format!("(or {})", v_parsed.iter().map(|d| d.smt.as_str()).collect::<Vec<_>>().join(" "));
    hyps.push(Hyp { smt: v_smt, prop: v_prop, fvar: v_fvar, name: format!("h_{}", hyps.len()) });
    let v_hyp = Expr::fvar(v_fvar);
    let c_parsed = congruence
        .iter()
        .map(|di| parse_congruence_disjunct_then(di, &v_parsed, &v_hyp))
        .collect::<Option<Vec<_>>>()?;
    for d in c_parsed.iter().chain(&v_parsed) {
        collect_disjunct_vars(d, &mut names);
    }
    let c_prop = build_or_prop(&c_parsed.iter().map(|d| d.prop.clone()).collect::<Vec<_>>())?;
    let c_fvar = FVarId::new(HYP_FVAR_BASE + hyps.len() as u64);
    let term = build_disjunctive_false(&c_parsed, &edges, Expr::fvar(c_fvar))?;
    let c_smt =
        format!("(or {})", c_parsed.iter().map(|d| d.smt.as_str()).collect::<Vec<_>>().join(" "));
    hyps.push(Hyp { smt: c_smt, prop: c_prop, fvar: c_fvar, name: format!("h_{}", hyps.len()) });
    finish_certificate(&hyps, &term, &names, identity)
}

/// The context conjuncts within ONE HOP of `seeds`: the seeds widened by the variables
/// of every order-atom conjunct that names one of them, then every conjunct, each once,
/// whose variables all lie within that set. `_9 = i`, `_13 = i` and `_8 = a*[_9]` are
/// one hop out of the congruence over `a*[_9]`, `a*[_13]`; the body's lengths, switch
/// values and other locals' ranges are not. Dropping a context conjunct only weakens the
/// refuted system.
fn one_hop_context<'f>(seeds: &BTreeSet<String>, context: &[&'f Formula]) -> Vec<&'f Formula> {
    let vars_of = |f: &Formula| {
        let mut vars = BTreeSet::new();
        collect_int_vars_deep(f, &mut vars);
        vars
    };
    let mut reach = seeds.clone();
    for &c in context {
        let vars = vars_of(c);
        if normalize_atom(c).is_some() && !vars.is_disjoint(seeds) {
            reach.extend(vars);
        }
    }
    let mut kept: Vec<&Formula> = Vec::new();
    for &c in context {
        let vars = vars_of(c);
        if !vars.is_empty() && vars.is_subset(&reach) && !kept.contains(&c) {
            kept.push(c);
        }
    }
    kept
}

#[cfg(test)]
#[path = "element_congruence/tests.rs"]
mod tests;
