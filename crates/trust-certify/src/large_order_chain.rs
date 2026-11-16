// trust-certify/src/large_order_chain.rs: the large-pool order-chain lane.
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

//! The LARGE-POOL ORDER CHAIN lane (Trust, TRUST-KI-1014-1, 2026-10-14).
//!
//! # The row this exists for
//!
//! aterm-codec `crates/aterm-codec/src/tty.rs:141`, `joint[..held]` in
//! `SafeStream::push` (`joint: [u8; 6]`, `held = self.held.min(3)`). The violation
//! is the `[slice]` bound `held > 6`; the path carries `held ≤ _10`,
//! `_10 = _11.len()` and `_11.len() = 3`, so the obligation is the three-edge
//! chain `7 ≤ held ≤ _10 ≤ 3`. The store seal `321aaeda7` minted a `CleanCic`
//! certificate for it (ay's UNSAT proof, reconstructed zero-trust over a pool of
//! about 50 hypotheses). From `6606d3bd` on the same row reaches the certifier with
//! MORE true context: the merged-interval range of `_6` (`self.held`), the
//! entry-read equalities `self*.1#e = self*.1`, the derived equality-class bounds.
//! Measured on the channel seal `trust-b58a105d` (pool captured with
//! `RUSTC_LOG=trust_certify::violation=debug`, replayed at crate level):
//!
//! * 66 atoms, 27 variables; the lifted edge set has 69 edges, so the exhaustive
//!   chain DFS ([`super::refute_via_chain_edges`]) refuses it (cap
//!   [`super::CHAIN_DFS_MAX_EDGES`] = 48);
//! * ay answers UNSAT, and clean-auto builds NO closed empty-clause term from its
//!   proof even at `TrustBudget::Unlimited` (drop the one atom `0 ≤ _6` and the
//!   zero-trust reconstruction succeeds: the gap is shape-sensitivity in the ay
//!   proof / clean-auto reconstruction, a first-party concern);
//! * every later lane declines too, so `certify_vc` returns `None`, the compiler's
//!   ay `Proved` carries no attachable evidence, and targo's publication boundary
//!   withholds it ("compiler transport claimed a favorable outcome without
//!   attachable native or clean-kernel proof evidence; downgraded before
//!   publication") — correctly: an uncertified ay claim is not publishable proof.
//!
//! The fix is a new route that PRODUCES the missing certificate, not a relaxation
//! of the boundary or of either cap.
//!
//! # The lane
//!
//! Over the SAME atoms, hypotheses and lifted edges the chain DFS uses
//! ([`super::atom_order_edges`], [`super::lifted_chain_edges`]), and only when that
//! DFS refused the set for size: a breadth-first search over the states
//! `(node, strict-so-far)` from each literal-headed edge finds the shortest WALK
//! `l R e₁ R … R u` whose closing atom `l ≤ u` (or `l < u` when any step is strict)
//! is FALSE ([`super::ClosedOrderAtom::is_false`]). The walk is folded with exactly
//! the lemmas the DFS uses ([`super::chain_step`]: `Int.le_trans`,
//! `Int.lt_of_lt_of_le`, `Int.lt_of_le_of_lt`, `Int.lt_trans`) and closed by
//! [`super::refute_false_atom`].
//!
//! Cost: per start edge `O(V + E)` over `2V` states; at most [`MAX_EDGES`] edges and
//! [`MAX_ATTEMPTS`] candidate walks are tried. No exponential search.
//!
//! # Why it is sound
//!
//! Nothing here is trusted. The term is a chain of transitivity steps over
//! hypotheses that are the obligation's own conjuncts (the pool
//! [`super::collect_supported_atoms`] keeps), and it reaches publication only
//! through [`super::finish_certificate`]: ay must independently answer UNSAT on the
//! full hypothesis set (a SAT answer declines in every mode), the clean CIC kernel
//! must check the term against `False` in the context of those hypotheses, and the
//! serialized payload must re-check after a round-trip. A satisfiable violation has
//! no false closing atom, so the search finds nothing and the lane declines; the
//! unit tests below pin that on satisfiable pools of the same size class.
//!
//! The consumer ([`super::recheck_cleancic`]) regenerates evidence through the
//! producer, so this lane's output is replayed byte-for-byte; the search is
//! deterministic (edges in pool order, interned nodes in a `BTreeMap`, FIFO queue).

use std::collections::{BTreeMap, VecDeque};

use trust_types::Formula;

use super::{
    CHAIN_DFS_MAX_EDGES, ChainNode, ClosedOrderAtom, Expr, ObligationIdentity, OrderEdge,
    atom_order_edges, chain_step, collect_supported_atoms, finish_certificate, lifted_chain_edges,
    refute_false_atom, supported_hyps_from_atoms,
};

/// The largest lifted edge set this lane searches. Above it the lane declines
/// (fail-closed), so a pathological machine-generated pool stays bounded at
/// `MAX_EDGES · (2V + E)` steps.
const MAX_EDGES: usize = 1024;

/// Candidate walks tried (each one a kernel check and an ay cross-check) before
/// the lane declines.
const MAX_ATTEMPTS: usize = 4;

/// Certify a pool whose contradiction is a transitive order chain the exhaustive
/// DFS refused to search for size. `None` unless the lifted edge set is above
/// [`CHAIN_DFS_MAX_EDGES`] (and at most [`MAX_EDGES`]) and a conflicting walk
/// certifies through [`finish_certificate`].
pub(super) fn certify_large_order_chain_contradiction(
    conjuncts: &[&Formula],
    identity: &ObligationIdentity,
) -> Option<trust_ir::ProofEvidence> {
    let (atoms, var_names) = collect_supported_atoms(conjuncts);
    if atoms.is_empty() {
        return None;
    }
    let hyps = supported_hyps_from_atoms(&atoms)?;
    let base_edges = atom_order_edges(&atoms, &hyps);
    let edges = lifted_chain_edges(&base_edges);
    // At or below the cap the exhaustive DFS already searched this exact set
    // (`transitive_chain_refutation`); this lane adds nothing there.
    if edges.len() <= CHAIN_DFS_MAX_EDGES || edges.len() > MAX_EDGES {
        return None;
    }
    let graph = EdgeGraph::new(&edges);
    let mut attempts = 0;
    for (start, edge) in edges.iter().enumerate() {
        let ChainNode::Lit(l) = edge.from else { continue };
        let Some(walk) = graph.shortest_conflicting_walk(start, l) else { continue };
        attempts += 1;
        if let Some(term) = fold_walk(&edges, &walk, l)
            && let Some(evidence) = finish_certificate(&hyps, &term, &var_names, identity)
        {
            return Some(evidence);
        }
        if attempts >= MAX_ATTEMPTS {
            return None;
        }
    }
    None
}

/// The edge set as a graph over interned [`ChainNode`]s.
struct EdgeGraph<'a> {
    edges: &'a [OrderEdge],
    nodes: Vec<&'a ChainNode>,
    /// `to` node id of each edge, parallel to `edges`.
    to: Vec<usize>,
    /// Outgoing edge indices per node id, in edge order.
    out: Vec<Vec<usize>>,
}

impl<'a> EdgeGraph<'a> {
    fn new(edges: &'a [OrderEdge]) -> Self {
        let mut ids: BTreeMap<&'a ChainNode, usize> = BTreeMap::new();
        let mut nodes: Vec<&'a ChainNode> = Vec::new();
        let mut intern = |node: &'a ChainNode| {
            *ids.entry(node).or_insert_with(|| {
                nodes.push(node);
                nodes.len() - 1
            })
        };
        let mut from = Vec::with_capacity(edges.len());
        let mut to = Vec::with_capacity(edges.len());
        for edge in edges {
            from.push(intern(&edge.from));
            to.push(intern(&edge.to));
        }
        let mut out = vec![Vec::new(); nodes.len()];
        for (index, &node) in from.iter().enumerate() {
            out[node].push(index);
        }
        Self { edges, nodes, to, out }
    }

    /// The shortest walk (as edge indices, starting with `start`) from the
    /// literal `l` that heads `edges[start]` to a literal `u` whose closing atom
    /// `l ≤ u` / `l < u` is false. Breadth-first over `(node, strict)` states, so
    /// a strict step is never lost to a shorter non-strict route.
    fn shortest_conflicting_walk(&self, start: usize, l: i128) -> Option<Vec<usize>> {
        let first = (self.to[start], usize::from(self.edges[start].strict));
        // `parent[node][strict]` = the state and edge it was reached by.
        let mut parent: Vec<[Option<(usize, usize, usize)>; 2]> = vec![[None; 2]; self.nodes.len()];
        let mut seen: Vec<[bool; 2]> = vec![[false; 2]; self.nodes.len()];
        seen[first.0][first.1] = true;
        let mut queue = VecDeque::from([first]);
        while let Some((node, strict)) = queue.pop_front() {
            if let ChainNode::Lit(u) = self.nodes[node]
                && (ClosedOrderAtom { a: l, b: *u, is_lt: strict == 1 }).is_false()
            {
                let mut walk = Vec::new();
                let mut state = (node, strict);
                while let Some((prev_node, prev_strict, edge)) = parent[state.0][state.1] {
                    walk.push(edge);
                    state = (prev_node, prev_strict);
                }
                walk.push(start);
                walk.reverse();
                return Some(walk);
            }
            for &edge in &self.out[node] {
                let next = (self.to[edge], strict | usize::from(self.edges[edge].strict));
                if !seen[next.0][next.1] {
                    seen[next.0][next.1] = true;
                    parent[next.0][next.1] = Some((node, strict, edge));
                    queue.push_back(next);
                }
            }
        }
        None
    }
}

/// Fold a conflicting walk into a kernel refutation, step for step as the DFS's
/// `extend_from` does: `acc : l R cur` and `edge : cur R next` compose by
/// [`chain_step`]; the closing literal is refuted by [`refute_false_atom`].
fn fold_walk(edges: &[OrderEdge], walk: &[usize], l: i128) -> Option<Expr> {
    let (&head, rest) = walk.split_first()?;
    let first = &edges[head];
    let l_expr = &first.from_expr;
    let mut acc = first.hyp.clone();
    let mut strict = first.strict;
    let mut cur_expr = first.to_expr.clone();
    let mut cur = &first.to;
    for &index in rest {
        let edge = &edges[index];
        if &edge.from != cur {
            return None;
        }
        acc = chain_step(strict, edge.strict, l_expr, &cur_expr, &edge.to_expr, &acc, &edge.hyp);
        strict |= edge.strict;
        cur_expr = edge.to_expr.clone();
        cur = &edge.to;
    }
    let ChainNode::Lit(u) = cur else { return None };
    refute_false_atom(&ClosedOrderAtom { a: l, b: *u, is_lt: strict }, acc)
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, Sort};

    use super::*;

    fn v(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }
    fn n(value: i128) -> Formula {
        Formula::Int(value)
    }
    fn le(a: Formula, b: Formula) -> Formula {
        Formula::Le(Box::new(a), Box::new(b))
    }
    fn lt(a: Formula, b: Formula) -> Formula {
        Formula::Lt(Box::new(a), Box::new(b))
    }
    fn eq(a: Formula, b: Formula) -> Formula {
        Formula::Eq(Box::new(a), Box::new(b))
    }

    /// True context that only enlarges the edge set: a chain of `count` padding
    /// variables, each in `[0, 100]`, `p_i ≤ p_{i+1}`. Satisfiable on its own
    /// (all zero) and disconnected from every variable the tests constrain.
    fn padding(count: usize) -> Vec<Formula> {
        let mut out = Vec::new();
        for i in 0..count {
            let p = v(&format!("pad_{i}"));
            out.push(le(n(0), p.clone()));
            out.push(le(p.clone(), n(100)));
            if i + 1 < count {
                out.push(le(p, v(&format!("pad_{}", i + 1))));
            }
        }
        out
    }

    /// The lane alone on `conjuncts` (the lane sees exactly what `certify_lanes`
    /// hands it: the normalized conjunct pool; these tests pass atoms that are
    /// already normal).
    fn lane(conjuncts: &[Formula]) -> bool {
        let violation = Formula::And(conjuncts.to_vec());
        let identity = ObligationIdentity::from_violation(&violation).expect("identity");
        let refs: Vec<&Formula> = conjuncts.iter().collect();
        matches!(
            super::super::on_certify_stack(|| certify_large_order_chain_contradiction(
                &refs, &identity
            )),
            Some(trust_ir::ProofEvidence::CleanCic { .. })
        )
    }

    fn with_padding(core: Vec<Formula>) -> Vec<Formula> {
        let mut pool = padding(20);
        pool.extend(core);
        pool
    }

    /// The tty.rs:141 shape: `held ≤ a`, `a = 3`, violation `held > 6` (as
    /// `7 ≤ held`), inside an edge set past the DFS cap. Certifies.
    #[test]
    fn guarded_slice_bound_chain_past_the_dfs_cap_certifies() {
        let pool = with_padding(vec![le(v("held"), v("a")), eq(v("a"), n(3)), le(n(7), v("held"))]);
        assert!(lane(&pool), "the three-edge chain 7 ≤ held ≤ a ≤ 3 must certify");
    }

    /// The same shape with a REAL violation: `a = 9`, so `held ∈ [7, 9]` is a model
    /// (`joint[..held]` over a 6-byte array with `held` up to 9 does go out of
    /// bounds). No conflicting chain exists; the lane must decline.
    #[test]
    fn satisfiable_slice_bound_is_declined() {
        let pool = with_padding(vec![le(v("held"), v("a")), eq(v("a"), n(9)), le(n(7), v("held"))]);
        assert!(!lane(&pool), "held = 7 satisfies the violation; nothing may certify it");
    }

    /// Strictness is tracked: `3 ≤ x < y ≤ 3` is UNSAT only through the strict
    /// step, and certifies.
    #[test]
    fn strict_step_closes_an_equal_bound_chain() {
        let pool = with_padding(vec![le(n(3), v("x")), lt(v("x"), v("y")), le(v("y"), n(3))]);
        assert!(lane(&pool), "3 ≤ x < y ≤ 3 is a contradiction via the strict step");
    }

    /// ... and NOT invented: `3 ≤ x ≤ y ≤ 3` has the model `x = y = 3`.
    #[test]
    fn non_strict_equal_bound_chain_is_declined() {
        let pool = with_padding(vec![le(n(3), v("x")), le(v("x"), v("y")), le(v("y"), n(3))]);
        assert!(!lane(&pool), "x = y = 3 is a model; the lane must decline");
    }

    /// A cycle in the order graph does not let the search manufacture a
    /// conflict: `0 ≤ x ≤ y ≤ x ≤ 5` is satisfiable.
    #[test]
    fn non_strict_cycle_is_declined() {
        let pool = with_padding(vec![
            le(n(0), v("x")),
            le(v("x"), v("y")),
            le(v("y"), v("x")),
            le(v("x"), n(5)),
        ]);
        assert!(!lane(&pool));
    }

    /// At or below the DFS cap the lane is inert: the exhaustive chain lane owns
    /// that set, so no certificate it mints can change bytes.
    #[test]
    fn inert_at_or_below_the_dfs_cap() {
        let pool = vec![le(v("held"), v("a")), eq(v("a"), n(3)), le(n(7), v("held"))];
        assert!(!lane(&pool), "a small pool is the exhaustive DFS's, not this lane's");
    }

    /// Above [`MAX_EDGES`] the lane declines (fail-closed resource bound), even on
    /// a contradiction.
    #[test]
    fn declines_above_its_edge_bound() {
        let mut pool = padding(400);
        pool.extend([le(v("held"), v("a")), eq(v("a"), n(3)), le(n(7), v("held"))]);
        assert!(!lane(&pool));
    }
}
