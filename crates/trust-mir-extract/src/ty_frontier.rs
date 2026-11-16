// trust-mir-extract/ty_frontier.rs: the DAG-aware frontier walk behind
// `ty_convert::nominal_frontier`.
//
// Kept free of rustc types on purpose, so the walk and its regression tests
// compile without a compiler session (the `bounded_adt_arg_depth` pattern in
// `ty_convert.rs`, split into its own file so the tests can also be built
// standalone against this one source file).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

/// What [`frontier_walk`] found at one node of the type DAG.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FrontierStep {
    /// A nominal ADT: the frontier records it and stops.
    Nominal,
    /// A constructor the lowering peels. Its children were handed to `visit`, in
    /// order; a node with no nominal content peels to no children at all.
    Peeled,
}

/// The walk behind `ty_convert::nominal_frontier`, generic over the node.
///
/// MEASURED DEFECT (2026-09-26): this walk used to be a plain recursion over the
/// TREE unfolding of `Ty<'tcx>`, bounded only by `MAX_TYPE_LOWERING_DEPTH`. Types
/// are interned, so a type is a DAG, and a DAG whose non-nominal nodes repeat a
/// child (`(T, T)`, a closure capturing one type twice) unfolds to a tree
/// exponential in its depth. The bound capped that at 2^64 visits, i.e. not at
/// all. The shape that reaches it is ordinary: a NESTED datatype such as
///
/// ```text
/// pub struct Perfect<T> { v: T, next: Option<Box<Perfect<(T, T)>>> }
/// ```
///
/// Its node set is infinite, so `canonical_cut_set`'s discovery walks it until
/// `MAX_CANONICAL_CUT_NODES`, and the node `Perfect<T_k>` asks for the frontier
/// of its field `v: T_k`, a tuple tree of 2^k leaves. `trustc -Ztrust-verify=on`
/// on a crate holding that struct and `fn pv(p: &Perfect<u32>) -> u32 { p.v }`
/// did not terminate (killed at 240 s on stage2 `29b6f15c7`; every sampled frame
/// of the working thread was this walk, under `canonical_cut_set`); the same file
/// with verification off compiles in 2.1 s. It is `adt_arg_depth`'s defect (see
/// there) in the one walk that did not get its fix. A cyclic type is not the
/// problem — `canonical_cut_set` already bounds the node set, and the other walks
/// memoize on the interned `Ty`; this one expanded a shared child once per PATH
/// to it.
///
/// THE FIX keeps the output EXACT. A node is expanded again only when it is
/// reached at a strictly SHALLOWER depth than every earlier expansion — the only
/// case in which the depth bound could let the new visit see more — so each node
/// is expanded at most `max_depth` times and the walk is polynomial.
///
/// Two exactness claims, and the premise that separates them:
///
/// * The SET of nominal nodes in `out` is the pre-fix walk's on ANY graph. By
///   induction on depth, every node the tree walk visits at depth `d` is expanded
///   here at some depth `<= d`; and this walk only prunes the tree walk.
/// * The ORDER of first occurrences is the pre-fix walk's on an ACYCLIC graph.
///   There, the expansion that makes a visit skippable is never an ancestor of
///   it, so it has COMPLETED, and every nominal node the skipped subtree would
///   push was already pushed. On a cycle the covering expansion can still be in
///   progress and the order can differ — measured: the first version of
///   `frontier_walk_matches_the_tree_walk_up_to_duplicates` drew cyclic graphs
///   and failed on a self-loop, `[5, 8]` against `[8, 5]`.
///
/// The production input is acyclic: every edge `nominal_frontier_step` peels
/// (`Ref`, `RawPtr`, `Slice`, `Array`, `Tuple`, `Pat`, closure and coroutine
/// upvars) goes to a strict subterm of a finite interned `Ty`, and an ADT — the
/// only way a type reaches itself — stops the walk. Both consumers read `out`
/// only up to duplicates (`intern_node` keeps the first index, the successor
/// loop tests `succ.contains`), so the discovered graph — and so the cut set —
/// is unchanged on every input the old walk finished. Pinned against the pre-fix
/// walk by `frontier_walk_matches_the_tree_walk_up_to_duplicates` (order, DAGs)
/// and `frontier_walk_finds_the_tree_walks_set_on_cyclic_graphs` (set, cycles).
///
/// `shallowest` may be shared by several walks whose outputs are concatenated
/// into one `out` (the fields of one ADT); the same argument covers the
/// concatenation. It must NOT be shared across two different `out` lists: a
/// subtree skipped for one list would be missing from the other.
pub(crate) fn frontier_walk<N, S>(
    node: N,
    depth: usize,
    max_depth: usize,
    step: &S,
    shallowest: &mut FxHashMap<N, usize>,
    out: &mut Vec<N>,
) where
    N: Copy + Eq + std::hash::Hash,
    S: Fn(N, &mut dyn FnMut(N)) -> FrontierStep,
{
    if depth >= max_depth {
        return;
    }
    if shallowest.get(&node).is_some_and(|seen| *seen <= depth) {
        return;
    }
    shallowest.insert(node, depth);
    let found = step(node, &mut |child| {
        frontier_walk(child, depth + 1, max_depth, step, shallowest, out);
    });
    if found == FrontierStep::Nominal {
        out.push(node);
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;

    /// `ty_convert::MAX_TYPE_LOWERING_DEPTH`, the bound the production walk runs
    /// under. Restated rather than imported so this file stays rustc-free.
    const PRODUCTION_MAX_DEPTH: usize = 64;

    #[derive(Clone, Debug)]
    struct Node {
        nominal: bool,
        children: Vec<usize>,
    }

    /// Run the production walk over `roots` (one shared memo, one `out`, as
    /// `adt_field_successors` does) and count its steps. Panics once the step
    /// count passes `guard`: that is what turns a non-terminating walk into a
    /// fast, bounded test failure instead of a hung test.
    fn walk(
        graph: &[Node],
        roots: &[usize],
        max_depth: usize,
        guard: usize,
    ) -> (Vec<usize>, usize) {
        let steps = Cell::new(0usize);
        let step = |node: usize, visit: &mut dyn FnMut(usize)| {
            steps.set(steps.get() + 1);
            assert!(
                steps.get() <= guard,
                "frontier walk exceeded {guard} steps: it is expanding the DAG as a tree"
            );
            if graph[node].nominal {
                return FrontierStep::Nominal;
            }
            for child in &graph[node].children {
                visit(*child);
            }
            FrontierStep::Peeled
        };
        let mut shallowest = FxHashMap::default();
        let mut out = Vec::new();
        for root in roots {
            frontier_walk(*root, 0, max_depth, &step, &mut shallowest, &mut out);
        }
        (out, steps.get())
    }

    /// The walk exactly as it stood before 2026-09-26: plain recursion over the
    /// TREE unfolding. Only an oracle for the fixed walk; exponential on a DAG.
    fn tree_walk(
        graph: &[Node],
        node: usize,
        depth: usize,
        max_depth: usize,
        out: &mut Vec<usize>,
    ) {
        if depth >= max_depth {
            return;
        }
        if graph[node].nominal {
            out.push(node);
            return;
        }
        for child in &graph[node].children {
            tree_walk(graph, *child, depth + 1, max_depth, out);
        }
    }

    fn first_occurrences(seq: &[usize]) -> Vec<usize> {
        let mut seen = std::collections::HashSet::new();
        seq.iter().copied().filter(|node| seen.insert(*node)).collect()
    }

    /// The regression, at the size the production bound allows. Node `i` is the
    /// tuple `(node i-1, node i-1)` and node 0 is nominal, i.e. the field `v: T_k`
    /// of `Perfect<T_k>`. Walked from depth 63 the tree has 2^63 leaves; before
    /// the fix this test failed at its step guard (and without the guard, never
    /// returned). The guard is the fixed walk's own worst case, `max_depth`
    /// expansions per node.
    #[test]
    fn frontier_walk_collapses_a_shared_tuple_dag() {
        let mut graph = vec![Node { nominal: true, children: Vec::new() }];
        for previous in 0..1_000 {
            graph.push(Node { nominal: false, children: vec![previous, previous] });
        }
        let root = PRODUCTION_MAX_DEPTH - 1;
        let guard = graph.len() * PRODUCTION_MAX_DEPTH;
        let (out, steps) = walk(&graph, &[root], PRODUCTION_MAX_DEPTH, guard);
        assert_eq!(first_occurrences(&out), vec![0]);
        // One expansion per distinct node on the way down: linear, not 2^63.
        assert_eq!(steps, root + 1);
    }

    /// The depth bound is why a revisit cannot simply be skipped: a node first
    /// reached deep may reach, from a shallower second visit, a nominal child the
    /// first visit was cut off from. The pre-fix walk finds it; so must this one,
    /// in either child order.
    #[test]
    fn frontier_walk_reexpands_a_node_reached_shallower_below_the_depth_bound() {
        for root_children in [vec![1, 3], vec![3, 1]] {
            let graph = vec![
                Node { nominal: false, children: root_children },
                Node { nominal: false, children: vec![2] },
                Node { nominal: false, children: vec![3] },
                Node { nominal: false, children: vec![4] },
                Node { nominal: true, children: Vec::new() },
            ];
            let mut oracle = Vec::new();
            tree_walk(&graph, 0, 0, 4, &mut oracle);
            assert_eq!(
                oracle,
                vec![4],
                "the oracle itself must see node 4 only via the short path"
            );
            let (out, _) = walk(&graph, &[0], 4, usize::MAX);
            assert_eq!(first_occurrences(&out), vec![4]);
        }
    }

    /// A deterministic LCG, so every drawn graph reproduces.
    struct Lcg(u64);

    impl Lcg {
        fn below(&mut self, bound: u64) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (self.0 >> 33) % bound
        }
    }

    /// A random graph on `len` nodes. `acyclic` draws each node's children from
    /// the nodes AFTER it only (the shape of a finite term); otherwise children
    /// are unrestricted, so cycles, self-loops and repeats all occur.
    fn draw_graph(rng: &mut Lcg, len: usize, acyclic: bool) -> Vec<Node> {
        (0..len)
            .map(|index| {
                let nominal = rng.below(10) < 3;
                let lo = if acyclic { index + 1 } else { 0 };
                let children = if lo >= len {
                    Vec::new()
                } else {
                    (0..rng.below(4)).map(|_| lo + rng.below((len - lo) as u64) as usize).collect()
                };
                Node { nominal, children }
            })
            .collect()
    }

    /// Compare the fixed walk with the pre-fix tree walk on `graphs` random
    /// graphs, every depth bound in `0..=7`, and 1-3 roots sharing one memo.
    /// `compare` receives (fixed walk output, tree walk output).
    fn against_the_tree_walk(
        seed: u64,
        acyclic: bool,
        compare: impl Fn(&[usize], &[usize], &str),
    ) -> usize {
        let mut rng = Lcg(seed);
        let mut compared = 0usize;
        for _ in 0..600 {
            let len = 1 + rng.below(12) as usize;
            let graph = draw_graph(&mut rng, len, acyclic);
            let roots: Vec<usize> =
                (0..1 + rng.below(3)).map(|_| rng.below(len as u64) as usize).collect();
            for max_depth in 0..=7 {
                let mut oracle = Vec::new();
                for root in &roots {
                    tree_walk(&graph, *root, 0, max_depth, &mut oracle);
                }
                let (out, steps) = walk(&graph, &roots, max_depth, len * max_depth.max(1));
                let context = format!("graph {graph:?} roots {roots:?} max_depth {max_depth}");
                compare(&out, &oracle, &context);
                assert!(
                    steps <= len * max_depth,
                    "{steps} steps for {len} nodes at depth {max_depth}"
                );
                compared += 1;
            }
        }
        compared
    }

    /// EXACTNESS against the pre-fix walk on ACYCLIC graphs — the production
    /// domain: the fixed walk's first occurrences, in order, equal the tree
    /// walk's, for one root and for several roots sharing one memo (the
    /// `adt_field_successors` sharing).
    #[test]
    fn frontier_walk_matches_the_tree_walk_up_to_duplicates() {
        let compared = against_the_tree_walk(0x2026_0926, true, |out, oracle, context| {
            assert_eq!(first_occurrences(out), first_occurrences(oracle), "{context}");
        });
        assert_eq!(compared, 600 * 8);
    }

    /// On graphs WITH cycles the walk still terminates within its bound and finds
    /// exactly the tree walk's SET of nominal nodes; only first-occurrence order
    /// may differ (see `frontier_walk`), which is why the production claim rests
    /// on acyclicity and this test asserts no more than the set.
    #[test]
    fn frontier_walk_finds_the_tree_walks_set_on_cyclic_graphs() {
        let sorted = |seq: &[usize]| {
            let mut set = first_occurrences(seq);
            set.sort_unstable();
            set
        };
        let compared = against_the_tree_walk(0x5E7_C7C1E, false, |out, oracle, context| {
            assert_eq!(sorted(out), sorted(oracle), "{context}");
        });
        assert_eq!(compared, 600 * 8);
    }
}
