//! Parity pins for `cfg_index`: the Lengauer–Tarjan dominator tree, its preorder
//! intervals and the skew-binary jump-pointer queries, against the textbook
//! definitions computed naively on small random graphs (reducible and irreducible,
//! with self-loops, parallel edges and unreachable components).

use super::cfg_index::{Csr, DomTree, NONE};

/// A tiny deterministic generator (xorshift), so the corpus is reproducible.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn graph(n: usize, edges: &[(u32, u32)]) -> (Csr, Csr) {
    let rev: Vec<(u32, u32)> = edges.iter().map(|&(a, b)| (b, a)).collect();
    (Csr::from_edges(n, edges), Csr::from_edges(n, &rev))
}

/// Reachability from `root`, and the naive dominator relation: `a` dominates `b` iff
/// `b` is unreachable from `root` once `a` is removed (for reachable `a != b`).
fn naive_dominates(n: usize, succ: &Csr, root: u32) -> (Vec<bool>, Vec<Vec<bool>>) {
    let reach = |removed: Option<u32>| {
        let mut seen = vec![false; n];
        if removed == Some(root) {
            return seen;
        }
        let mut stack = vec![root];
        seen[root as usize] = true;
        while let Some(v) = stack.pop() {
            for &w in succ.adj(v) {
                if Some(w) != removed && !seen[w as usize] {
                    seen[w as usize] = true;
                    stack.push(w);
                }
            }
        }
        seen
    };
    let reachable = reach(None);
    let mut dom = vec![vec![false; n]; n];
    for a in 0..n {
        if !reachable[a] {
            continue;
        }
        let without = reach(Some(a as u32));
        for b in 0..n {
            dom[a][b] = reachable[b] && (a == b || !without[b]);
        }
    }
    (reachable, dom)
}

fn random_graph(rng: &mut Rng, n: usize) -> Vec<(u32, u32)> {
    let mut edges = Vec::new();
    // A forward backbone keeps most nodes reachable; extra edges add joins, back
    // edges, self-loops and parallel edges; some nodes are left unreachable.
    for v in 1..n {
        if rng.below(5) != 0 {
            edges.push((rng.below(v as u64) as u32, v as u32));
        }
    }
    let extra = rng.below(2 * n as u64 + 1);
    for _ in 0..extra {
        edges.push((rng.below(n as u64) as u32, rng.below(n as u64) as u32));
    }
    edges
}

#[test]
fn dominators_match_the_definition_on_random_graphs() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let mut checked = 0usize;
    let mut unreachable = 0usize;
    for round in 0..400 {
        let n = 1 + rng.below(18) as usize;
        let edges = random_graph(&mut rng, n);
        let (succ, preds) = graph(n, &edges);
        let tree = DomTree::build(0, &succ, &preds);
        let (reachable, dom) = naive_dominates(n, &succ, 0);
        for b in 0..n {
            assert_eq!(
                tree.reachable(b as u32),
                reachable[b],
                "round {round}: reachability of {b}"
            );
            if !reachable[b] {
                unreachable += 1;
                assert_eq!(tree.idom(b as u32), NONE);
                continue;
            }
            for a in 0..n {
                assert_eq!(
                    tree.dominates(a as u32, b as u32),
                    dom[a][b],
                    "round {round}: does {a} dominate {b}? edges {edges:?}"
                );
                checked += 1;
            }
            // The immediate dominator is the deepest strict dominator.
            if b != 0 {
                let idom = tree.idom(b as u32) as usize;
                assert!(dom[idom][b] && idom != b, "round {round}: idom({b}) = {idom}");
                for a in 0..n {
                    if a != b && dom[a][b] {
                        assert!(
                            dom[a][idom],
                            "round {round}: {a} dominates {b} but not idom {idom}"
                        );
                    }
                }
            }
        }
    }
    assert!(checked > 10_000 && unreachable > 0, "the corpus is too thin: {checked}/{unreachable}");
}

#[test]
fn lca_and_level_ancestor_match_the_tree_walk() {
    let mut rng = Rng(0x1234_5678_9abc_def1);
    for round in 0..200 {
        let n = 2 + rng.below(40) as usize;
        let edges = random_graph(&mut rng, n);
        let (succ, preds) = graph(n, &edges);
        let tree = DomTree::build(0, &succ, &preds);
        let path = |mut v: u32| {
            let mut p = vec![v];
            while v != 0 {
                v = tree.idom(v);
                p.push(v);
            }
            p.reverse();
            p
        };
        for a in 0..n as u32 {
            if !tree.reachable(a) {
                continue;
            }
            let pa = path(a);
            assert_eq!(pa.len() as u32 - 1, tree.depth(a), "round {round}: depth of {a}");
            for d in 0..=tree.depth(a) {
                assert_eq!(tree.level_ancestor(a, d), pa[d as usize], "round {round}: la({a},{d})");
            }
            for b in 0..n as u32 {
                if !tree.reachable(b) {
                    continue;
                }
                let pb = path(b);
                let common = pa.iter().zip(&pb).take_while(|(x, y)| x == y).count();
                assert_eq!(tree.lca(a, b), pa[common - 1], "round {round}: lca({a},{b})");
            }
        }
    }
}

/// A long chain with a diamond every other node — the deep, narrow shape of the
/// `ever-init` cleanup ladders — exercises the jump pointers far from the root.
#[test]
fn deep_chains_answer_queries_without_walking_the_path() {
    let n = 4000u32;
    let mut edges = Vec::new();
    for v in 1..n {
        edges.push((v - 1, v));
        if v % 2 == 0 && v >= 2 {
            edges.push((v - 2, v));
        }
    }
    let (succ, preds) = graph(n as usize, &edges);
    crate::fn_memo::reset_analysis_memo_stats();
    let tree = DomTree::build(0, &succ, &preds);
    let built = crate::fn_memo::analysis_memo_stats().cfg_work;
    assert!(built < 20 * n as u64, "building the tree did super-linear work: {built}");
    crate::fn_memo::reset_analysis_memo_stats();
    for v in (0..n).step_by(97) {
        let _ = tree.level_ancestor(n - 1, tree.depth(v));
        let _ = tree.lca(n - 1, v);
    }
    let queries = crate::fn_memo::analysis_memo_stats().cfg_work;
    assert!(queries < 42 * 4 * 64, "jump-pointer queries walked the path: {queries}");
}

/// A random `Goto` / `SwitchInt` body over `n` blocks (loops, nested loops, irreducible
/// regions, self-loops and dead blocks all occur).
fn random_body(rng: &mut Rng, n: usize) -> trust_types::VerifiableFunction {
    use serde_json::json;
    let span = json!({"file": "cfg.rs", "line_start": 1, "col_start": 0, "line_end": 1,
        "col_end": 1});
    let mut blocks = Vec::new();
    for b in 0..n {
        let term = match rng.below(4) {
            0 => json!("Return"),
            1 => json!({"Goto": rng.below(n as u64)}),
            _ => {
                let arms: Vec<serde_json::Value> =
                    (0..1 + rng.below(2)).map(|v| json!([v, rng.below(n as u64)])).collect();
                json!({"SwitchInt": {"discr": {"Copy": {"local": 1, "projections": []}},
                    "targets": arms, "otherwise": rng.below(n as u64),
                    "exhaustive_enum_unreachable": false, "span": span}})
            }
        };
        blocks.push(json!({"id": b, "stmts": [], "terminator": term}));
    }
    let u32_ty = json!({"Int": {"width": 32, "signed": false}});
    serde_json::from_value(json!({
        "name": "cfg", "def_path": "cfg::f", "span": span,
        "body": {"locals": [{"index": 0, "ty": u32_ty, "name": null},
                            {"index": 1, "ty": u32_ty, "name": "c"}],
                 "blocks": blocks, "arg_count": 1, "return_ty": u32_ty},
        "contracts": [], "preconditions": [], "postconditions": [],
        "spec": {"requires": [], "ensures": [], "invariants": []},
    }))
    .expect("a random body deserializes")
}

/// The version oracle's loop machinery against the definitions, on random bodies: the
/// LOOP-NESTING FOREST (`innermost_loop` / `loop_parent`) names, for every node, exactly
/// the headers whose natural loop contains it (a header is the target of a dominator
/// back edge `u -> h`; its natural loop is `h` plus every node that reaches a latch
/// without passing `h`), and the FORWARD ranks (`topo_f`) never decrease along an edge
/// that is not a dominator back edge.
#[test]
fn loop_forest_and_forward_ranks_match_the_definitions() {
    use super::cfg_index::CfgIndex;
    let mut rng = Rng(0x0dd_ba11_cafe_f00d);
    let (mut headers_seen, mut nested, mut members) = (0usize, 0usize, 0usize);
    for round in 0..400 {
        let n = 1 + rng.below(16) as usize;
        let func = random_body(&mut rng, n);
        let cfg = CfgIndex::build(&func);
        let dom = cfg.dom();
        // The augmented edges, as `CfgIndex::build` makes them.
        let (e, r) = (n as u32, n as u32 + 1);
        let mut edges: Vec<(u32, u32)> = Vec::new();
        for (i, b) in func.body.blocks.iter().enumerate() {
            for t in super::full_graph_terminator_targets(&b.terminator, b.id) {
                if t.0 < n {
                    edges.push((i as u32, t.0 as u32));
                }
            }
        }
        let mut live = vec![false; n];
        let mut stack = vec![0u32];
        live[0] = true;
        while let Some(v) = stack.pop() {
            for &(a, b) in &edges {
                if a == v && !live[b as usize] {
                    live[b as usize] = true;
                    stack.push(b);
                }
            }
        }
        edges.push((r, e));
        edges.push((e, 0));
        for (d, &l) in live.iter().enumerate() {
            if !l {
                edges.push((r, d as u32));
            }
        }
        let total = n + 2;
        // Headers and their natural loops, by definition.
        let mut loops: Vec<(u32, Vec<bool>)> = Vec::new();
        for h in 0..total as u32 {
            let latches: Vec<u32> = edges
                .iter()
                .filter(|&&(u, v)| v == h && dom.dominates(h, u))
                .map(|&(u, _)| u)
                .collect();
            if latches.is_empty() {
                continue;
            }
            let mut body = vec![false; total];
            body[h as usize] = true;
            let mut stack: Vec<u32> = latches.into_iter().filter(|&u| u != h).collect();
            while let Some(x) = stack.pop() {
                if body[x as usize] {
                    continue;
                }
                body[x as usize] = true;
                for &(a, b) in &edges {
                    if b == x && !body[a as usize] {
                        stack.push(a);
                    }
                }
            }
            loops.push((h, body));
        }
        headers_seen += loops.len();
        for v in 0..total as u32 {
            let mut want: Vec<u32> =
                loops.iter().filter(|(_, body)| body[v as usize]).map(|(h, _)| *h).collect();
            want.sort_unstable();
            let mut got: Vec<u32> = Vec::new();
            let mut h = cfg.innermost_loop(v);
            while h != NONE {
                got.push(h);
                h = cfg.loop_parent(h);
            }
            nested += usize::from(got.len() > 1);
            members += got.len();
            got.sort_unstable();
            assert_eq!(got, want, "round {round}: loops containing {v}; edges {edges:?}");
            assert_eq!(cfg.is_loop_header(v), loops.iter().any(|(h, _)| *h == v));
        }
        for &(u, v) in &edges {
            if !dom.dominates(v, u) {
                assert!(
                    cfg.topo_f(u) <= cfg.topo_f(v),
                    "round {round}: forward edge {u} -> {v} decreases the rank"
                );
            }
        }
    }
    assert!(headers_seen > 200 && nested > 50 && members > 500, "thin: {headers_seen}/{nested}");
}
