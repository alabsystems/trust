// trust-vcgen/src/generate/cfg_index.rs: per-function CFG index — dominator tree
// (Lengauer–Tarjan), O(1) dominance by preorder intervals, O(log) level-ancestor and
// LCA by skew-binary jump pointers, and the augmented fact-transport graph the
// statement-version oracle (`version_ssa`) resolves over.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// WHY THIS EXISTS. Every analysis that needs "which blocks dominate this one" used to
// build it its own way, and each way was super-linear: dense `Vec<FxHashSet<usize>>`
// dominator sets refined to a fixpoint (`termination::compute_dominators`, Θ(n²)
// memory), and a whole-CFG reaching-version fixpoint materialising one
// `name -> {token}` map per block (`path_defs::entry_versions_fixpoint`, Θ(blocks ×
// names)). The index below is built once per body in O((B + E) · α) time and O(B + E)
// memory, and answers every dominance question those analyses asked.
//
// The dominator algorithm is the classic Lengauer–Tarjan "simple" variant (path
// compression, no balancing): O(E log B) worst case, exact, iterative (no recursion,
// so a 100k-block body cannot overflow the stack). The jump pointers are Myers'
// skew-binary scheme: ONE extra pointer per node gives O(log depth) level-ancestor,
// LCA and "lowest ancestor satisfying a monotone predicate" queries — linear memory,
// unlike binary lifting's B log B table.

use trust_types::VerifiableFunction;

/// Sentinel for "no node" in the `u32` arrays below.
pub(crate) const NONE: u32 = u32::MAX;

/// Deterministic work counter for [`DomTree::build`] and the query helpers: one unit
/// per edge scanned, per node numbered, per compression step and per jump taken.
/// Pure instrumentation (see `fn_memo::count_cfg_work`).
fn charge(units: usize) {
    crate::fn_memo::count_cfg_work(units as u64);
}

/// A graph in compressed-sparse-row form over nodes `0..n`.
#[derive(Clone, Debug, Default)]
pub(crate) struct Csr {
    start: Vec<u32>,
    list: Vec<u32>,
}

impl Csr {
    /// Build from an edge list (`from -> to`); `adj(v)` lists `v`'s targets in edge
    /// insertion order.
    pub(crate) fn from_edges(n: usize, edges: &[(u32, u32)]) -> Csr {
        let mut count = vec![0u32; n + 1];
        for &(from, _) in edges {
            count[from as usize + 1] += 1;
        }
        for i in 0..n {
            count[i + 1] += count[i];
        }
        let mut fill = count.clone();
        let mut list = vec![0u32; edges.len()];
        for &(from, to) in edges {
            let slot = &mut fill[from as usize];
            list[*slot as usize] = to;
            *slot += 1;
        }
        Csr { start: count, list }
    }

    pub(crate) fn adj(&self, v: u32) -> &[u32] {
        let v = v as usize;
        &self.list[self.start[v] as usize..self.start[v + 1] as usize]
    }

    pub(crate) fn len(&self) -> usize {
        self.start.len().saturating_sub(1)
    }
}

/// The dominator tree of a rooted graph, with preorder intervals, depths and
/// skew-binary jump pointers. Nodes not reachable from the root have `idom == NONE`
/// and no interval; every query below treats them as "outside the tree".
#[derive(Clone, Debug)]
pub(crate) struct DomTree {
    /// Immediate dominator; `root`'s is `root`; `NONE` for nodes unreachable from root.
    idom: Vec<u32>,
    /// Dominator-tree preorder number; `NONE` when unreachable.
    pre: Vec<u32>,
    /// Largest preorder number in the node's dominator subtree (inclusive).
    last: Vec<u32>,
    depth: Vec<u32>,
    /// Myers skew-binary jump pointer (an ancestor; `root` for the root).
    jump: Vec<u32>,
    /// Nodes by dominator-tree preorder number.
    by_pre: Vec<u32>,
}

impl DomTree {
    /// Dominators of `succ` rooted at `root`. `preds` must be the transpose of `succ`
    /// (passed in because every caller already has both).
    pub(crate) fn build(root: u32, succ: &Csr, preds: &Csr) -> DomTree {
        let n = succ.len();
        // ---- DFS preorder from the root (iterative).
        let mut num = vec![NONE; n];
        let mut vertex: Vec<u32> = Vec::with_capacity(n);
        let mut dfs_parent: Vec<u32> = Vec::with_capacity(n);
        if (root as usize) < n {
            let mut stack: Vec<(u32, u32, usize)> = vec![(root, NONE, 0)];
            num[root as usize] = 0;
            vertex.push(root);
            dfs_parent.push(NONE);
            while let Some(top) = stack.last_mut() {
                let (v, _, next) = *top;
                let adj = succ.adj(v);
                if next < adj.len() {
                    top.2 += 1;
                    charge(1);
                    let w = adj[next];
                    if num[w as usize] == NONE {
                        num[w as usize] = vertex.len() as u32;
                        dfs_parent.push(num[v as usize]);
                        vertex.push(w);
                        stack.push((w, v, 0));
                    }
                } else {
                    stack.pop();
                }
            }
        }
        let reach = vertex.len();

        // ---- Lengauer–Tarjan (simple linking, path compression), in DFS-number space.
        let mut semi: Vec<u32> = (0..reach as u32).collect();
        let mut label: Vec<u32> = (0..reach as u32).collect();
        let mut ancestor: Vec<u32> = vec![NONE; reach];
        let mut idom_num: Vec<u32> = vec![0; reach];
        // Buckets as intrusive singly linked lists: O(n) memory, no Vec<Vec<_>>.
        let mut bucket_head: Vec<u32> = vec![NONE; reach];
        let mut bucket_next: Vec<u32> = vec![NONE; reach];
        let mut path: Vec<u32> = Vec::new();

        // `eval` with iterative path compression. Returns the node on the forest path
        // from `v` (exclusive of the forest root) with minimal `semi`, or `v` itself
        // when `v` is a forest root.
        let eval = |v: u32,
                    ancestor: &mut Vec<u32>,
                    label: &mut Vec<u32>,
                    semi: &Vec<u32>,
                    path: &mut Vec<u32>|
         -> u32 {
            if ancestor[v as usize] == NONE {
                return v;
            }
            path.clear();
            let mut x = v;
            while ancestor[ancestor[x as usize] as usize] != NONE {
                path.push(x);
                x = ancestor[x as usize];
            }
            charge(path.len() + 1);
            while let Some(y) = path.pop() {
                let a = ancestor[y as usize];
                if semi[label[a as usize] as usize] < semi[label[y as usize] as usize] {
                    label[y as usize] = label[a as usize];
                }
                ancestor[y as usize] = ancestor[a as usize];
            }
            label[v as usize]
        };

        for w in (1..reach as u32).rev() {
            let node = vertex[w as usize];
            for &p in preds.adj(node) {
                charge(1);
                let v = num[p as usize];
                if v == NONE {
                    continue;
                }
                let u = eval(v, &mut ancestor, &mut label, &semi, &mut path);
                if semi[u as usize] < semi[w as usize] {
                    semi[w as usize] = semi[u as usize];
                }
            }
            let s = semi[w as usize] as usize;
            bucket_next[w as usize] = bucket_head[s];
            bucket_head[s] = w;
            let pw = dfs_parent[w as usize];
            ancestor[w as usize] = pw;
            let mut v = bucket_head[pw as usize];
            bucket_head[pw as usize] = NONE;
            while v != NONE {
                charge(1);
                let next = bucket_next[v as usize];
                let u = eval(v, &mut ancestor, &mut label, &semi, &mut path);
                idom_num[v as usize] = if semi[u as usize] < semi[v as usize] { u } else { pw };
                v = next;
            }
        }
        for w in 1..reach {
            if idom_num[w] != semi[w] {
                idom_num[w] = idom_num[idom_num[w] as usize];
            }
        }

        let mut idom = vec![NONE; n];
        for w in 0..reach {
            idom[vertex[w] as usize] =
                if w == 0 { vertex[0] } else { vertex[idom_num[w] as usize] };
        }

        // ---- Dominator tree: children (CSR), preorder intervals, depth, jump pointers.
        let mut child_edges: Vec<(u32, u32)> = Vec::with_capacity(reach.saturating_sub(1));
        // Children in DFS-number order keeps the tree preorder deterministic.
        for w in 1..reach {
            child_edges.push((idom[vertex[w] as usize], vertex[w]));
        }
        let children = Csr::from_edges(n, &child_edges);
        let mut pre = vec![NONE; n];
        let mut last = vec![NONE; n];
        let mut depth = vec![0u32; n];
        let mut jump = vec![NONE; n];
        let mut by_pre: Vec<u32> = Vec::with_capacity(reach);
        if reach > 0 {
            let mut stack: Vec<(u32, usize)> = vec![(root, 0)];
            pre[root as usize] = 0;
            by_pre.push(root);
            jump[root as usize] = root;
            while let Some(top) = stack.last_mut() {
                let (v, next) = *top;
                let kids = children.adj(v);
                if next < kids.len() {
                    top.1 += 1;
                    charge(1);
                    let c = kids[next];
                    pre[c as usize] = by_pre.len() as u32;
                    by_pre.push(c);
                    depth[c as usize] = depth[v as usize] + 1;
                    // Myers: jump(c) = jump(jump(p)) when the two jumps above `p` have
                    // equal length, else `p`.
                    let j = jump[v as usize];
                    let jj = jump[j as usize];
                    jump[c as usize] = if depth[v as usize] - depth[j as usize]
                        == depth[j as usize] - depth[jj as usize]
                    {
                        jj
                    } else {
                        v
                    };
                    stack.push((c, 0));
                } else {
                    last[v as usize] = by_pre.len() as u32 - 1;
                    stack.pop();
                }
            }
        }
        DomTree { idom, pre, last, depth, jump, by_pre }
    }

    pub(crate) fn reachable(&self, v: u32) -> bool {
        self.pre[v as usize] != NONE
    }

    pub(crate) fn idom(&self, v: u32) -> u32 {
        self.idom[v as usize]
    }

    pub(crate) fn pre(&self, v: u32) -> u32 {
        self.pre[v as usize]
    }

    pub(crate) fn last(&self, v: u32) -> u32 {
        self.last[v as usize]
    }

    pub(crate) fn depth(&self, v: u32) -> u32 {
        self.depth[v as usize]
    }

    pub(crate) fn node_at_pre(&self, p: u32) -> u32 {
        self.by_pre[p as usize]
    }

    /// `a` dominates `b` (reflexive). False when either is unreachable from the root.
    pub(crate) fn dominates(&self, a: u32, b: u32) -> bool {
        let (pa, pb) = (self.pre[a as usize], self.pre[b as usize]);
        pa != NONE && pb != NONE && pa <= pb && pb <= self.last[a as usize]
    }

    /// Whether the preorder number `p` lies in `a`'s dominator subtree.
    pub(crate) fn subtree_contains_pre(&self, a: u32, p: u32) -> bool {
        let pa = self.pre[a as usize];
        pa != NONE && pa <= p && p <= self.last[a as usize]
    }

    /// The ancestor of `v` at depth `d` (`d <= depth(v)`).
    pub(crate) fn level_ancestor(&self, mut v: u32, d: u32) -> u32 {
        while self.depth[v as usize] > d {
            crate::fn_memo::count_query_steps(1);
            let j = self.jump[v as usize];
            v = if self.depth[j as usize] >= d { j } else { self.idom[v as usize] };
        }
        v
    }

    /// The deepest common dominator of `a` and `b` (both reachable).
    pub(crate) fn lca(&self, a: u32, b: u32) -> u32 {
        let pb = self.pre[b as usize];
        self.lowest_ancestor_where(a, |x| self.subtree_contains_pre(x, pb))
    }

    /// The deepest ancestor-or-self of `v` satisfying `p`, which must be MONOTONE along
    /// the root path (false below some point, true from it up to the root). The root is
    /// assumed to satisfy it.
    pub(crate) fn lowest_ancestor_where(&self, mut v: u32, p: impl Fn(u32) -> bool) -> u32 {
        while !p(v) {
            crate::fn_memo::count_query_steps(1);
            let j = self.jump[v as usize];
            v = if !p(j) { j } else { self.idom[v as usize] };
        }
        v
    }
}

/// The per-function index the statement-version oracle resolves over: the
/// fact-transport CFG (`path_defs::full_graph_terminator_targets`, unwind-inclusive —
/// the predecessor relation of the retired reaching-version fixpoint), AUGMENTED with
/// two virtual nodes so that every block has a dominator and every seed has a site:
///
///  * `E` (`n`): the function-ENTRY definition. Edge `E -> bb0`. It "defines" every
///    name with the entry token `e`, reproducing the retired fixpoint's seed
///    `in[bb0] ∋ (name, e)`.
///  * `R` (`n + 1`): the root. Edges `R -> E` and `R -> d` for every block `d`
///    unreachable from `bb0`. `R` defines nothing, so the `R -> d` edges carry the
///    empty set — exactly what a dead block's in-set starts from in the retired
///    fixpoint — while giving `d` a dominator.
///
/// Neither virtual node is a program point; their edges add no behaviour.
pub(crate) struct CfgIndex {
    n_blocks: usize,
    preds: Csr,
    dom: DomTree,
    /// Nearest ancestor-or-self (in the dominator tree) with two or more augmented
    /// predecessors; `NONE` when there is none.
    njoin: Vec<u32>,
    /// Topological rank of each node's strongly connected component in the
    /// condensation of the FORWARD graph — the augmented graph minus its dominator
    /// BACK edges (`u -> h` with `h` dominating `u`, self-loops included): a forward
    /// edge never decreases it, so a node can reach another along forward edges only
    /// if its rank is not larger. (Irreducible cycles have no back edge and stay
    /// cycles here; their nodes share a rank.)
    topo_f: Vec<u32>,
    /// The LOOP-NESTING FOREST of the dominator back edges: `innermost[v]` is the
    /// innermost loop header whose natural loop contains `v` (`v` itself for a
    /// header), `NONE` outside every loop; `loop_parent[h]` the innermost header whose
    /// loop strictly contains header `h`'s. Natural loops of dominator back edges are
    /// nested or disjoint (a header strictly dominating another whose loop meets its
    /// own reaches that header's latches without passing itself), so this is a forest.
    innermost: Vec<u32>,
    loop_parent: Vec<u32>,
}

impl CfgIndex {
    pub(crate) fn build(func: &VerifiableFunction) -> CfgIndex {
        let n = func.body.blocks.len();
        let e = n as u32;
        let r = n as u32 + 1;
        let mut edges: Vec<(u32, u32)> = Vec::with_capacity(n * 2 + 2);
        let mut targets: Vec<trust_types::BlockId> = Vec::with_capacity(8);
        for (i, b) in func.body.blocks.iter().enumerate() {
            targets.clear();
            super::path_defs::for_each_full_graph_terminator_target(&b.terminator, |t| {
                targets.push(t);
            });
            targets.sort_unstable_by_key(|t| t.0);
            targets.dedup();
            for &t in &targets {
                if t.0 < n {
                    edges.push((i as u32, t.0 as u32));
                }
            }
        }
        charge(edges.len());
        // Blocks reachable from bb0 over the block edges alone.
        let block_succ = Csr::from_edges(n, &edges);
        let mut live = vec![false; n];
        if n > 0 {
            let mut stack = vec![0u32];
            live[0] = true;
            while let Some(v) = stack.pop() {
                for &w in block_succ.adj(v) {
                    charge(1);
                    if !live[w as usize] {
                        live[w as usize] = true;
                        stack.push(w);
                    }
                }
            }
        }
        edges.push((r, e));
        if n > 0 {
            edges.push((e, 0));
        }
        for (d, &is_live) in live.iter().enumerate() {
            if !is_live {
                edges.push((r, d as u32));
            }
        }
        let succ = Csr::from_edges(n + 2, &edges);
        let rev: Vec<(u32, u32)> = edges.iter().map(|&(a, b)| (b, a)).collect();
        let preds = Csr::from_edges(n + 2, &rev);
        let dom = DomTree::build(r, &succ, &preds);
        let mut njoin = vec![NONE; n + 2];
        for p in 0..(n as u32 + 2) {
            let v = dom.node_at_pre(p);
            njoin[v as usize] = if preds.adj(v).len() >= 2 {
                v
            } else if v == r {
                NONE
            } else {
                njoin[dom.idom(v) as usize]
            };
        }
        // Dominator back edges (`u -> h`, `h` dominates `u`) define the loops; the rest
        // is the forward graph.
        let n_aug = n + 2;
        let mut is_header = vec![false; n_aug];
        let mut fwd: Vec<(u32, u32)> = Vec::with_capacity(edges.len());
        for &(u, v) in &edges {
            charge(1);
            if dom.dominates(v, u) {
                is_header[v as usize] = true;
            } else {
                fwd.push((u, v));
            }
        }
        let topo_f = scc_topo_ranks(&Csr::from_edges(n_aug, &fwd));
        let (innermost, loop_parent) = loop_forest(&dom, &preds, &is_header);
        CfgIndex { n_blocks: n, preds, dom, njoin, topo_f, innermost, loop_parent }
    }

    pub(crate) fn n_blocks(&self) -> usize {
        self.n_blocks
    }

    /// The virtual entry-definition node `E`.
    pub(crate) fn entry_def(&self) -> u32 {
        self.n_blocks as u32
    }

    /// The virtual root `R`.
    pub(crate) fn root(&self) -> u32 {
        self.n_blocks as u32 + 1
    }

    pub(crate) fn dom(&self) -> &DomTree {
        &self.dom
    }

    /// Augmented predecessors of `v` (blocks, plus `E` for `bb0` and `R` for a dead block).
    pub(crate) fn preds(&self, v: u32) -> &[u32] {
        self.preds.adj(v)
    }

    pub(crate) fn nearest_join(&self, v: u32) -> u32 {
        self.njoin[v as usize]
    }

    /// The topological rank of `v`'s strongly connected component in the FORWARD
    /// graph (see `topo_f`).
    pub(crate) fn topo_f(&self, v: u32) -> u32 {
        self.topo_f[v as usize]
    }

    /// Whether `v` is the target of a dominator back edge.
    pub(crate) fn is_loop_header(&self, v: u32) -> bool {
        self.innermost[v as usize] == v
    }

    /// The innermost loop header whose loop contains `v`, or `NONE`.
    pub(crate) fn innermost_loop(&self, v: u32) -> u32 {
        self.innermost[v as usize]
    }

    /// The header of the loop that strictly encloses header `h`'s, or `NONE`.
    pub(crate) fn loop_parent(&self, h: u32) -> u32 {
        self.loop_parent[h as usize]
    }
}

/// The loop-nesting forest of the dominator back edges (see `CfgIndex::innermost`):
/// headers are processed innermost first (decreasing dominator preorder — an enclosing
/// header dominates the headers it encloses), each by a backward walk from its latches
/// that stops at the header. A node already claimed by an inner loop is skipped to its
/// loop's current outermost header (union-find with path halving), which becomes a
/// child of this one — so every node and edge is walked O(1) times per loop level it
/// is first claimed at, near-linear overall.
fn loop_forest(dom: &DomTree, preds: &Csr, is_header: &[bool]) -> (Vec<u32>, Vec<u32>) {
    let n = is_header.len();
    let mut innermost = vec![NONE; n];
    let mut loop_parent = vec![NONE; n];
    let mut uf: Vec<u32> = (0..n as u32).collect();
    let find = |uf: &mut Vec<u32>, mut x: u32| -> u32 {
        while uf[x as usize] != x {
            let p = uf[x as usize];
            uf[x as usize] = uf[p as usize];
            x = p;
        }
        x
    };
    let mut headers: Vec<u32> = (0..n as u32).filter(|&v| is_header[v as usize]).collect();
    headers.sort_unstable_by_key(|&h| std::cmp::Reverse(dom.pre(h)));
    let mut stack: Vec<u32> = Vec::new();
    for &h in &headers {
        innermost[h as usize] = h;
        for &u in preds.adj(h) {
            charge(1);
            if u != h && dom.dominates(h, u) {
                stack.push(u);
            }
        }
        while let Some(x) = stack.pop() {
            charge(1);
            let y = find(&mut uf, x);
            if y == h {
                continue;
            }
            if innermost[y as usize] == NONE {
                innermost[y as usize] = h;
            } else {
                // `y` heads a completed inner loop not yet given a parent.
                loop_parent[y as usize] = h;
            }
            uf[y as usize] = h;
            stack.extend_from_slice(preds.adj(y));
        }
    }
    (innermost, loop_parent)
}

/// Tarjan's strongly connected components (iterative), returned as a topological
/// rank per node: the condensation DAG's edges go from smaller to larger ranks, and
/// the nodes of one component share a rank.
fn scc_topo_ranks(succ: &Csr) -> Vec<u32> {
    let n = succ.len();
    let mut index = vec![NONE; n];
    let mut low = vec![0u32; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<u32> = Vec::new();
    let mut comp = vec![NONE; n];
    let mut n_comps = 0u32;
    let mut next = 0u32;
    let mut frames: Vec<(u32, usize)> = Vec::new();
    for root in 0..n as u32 {
        if index[root as usize] != NONE {
            continue;
        }
        frames.push((root, 0));
        index[root as usize] = next;
        low[root as usize] = next;
        next += 1;
        stack.push(root);
        on_stack[root as usize] = true;
        while let Some(&mut (v, ref mut i)) = frames.last_mut() {
            let adj = succ.adj(v);
            if *i < adj.len() {
                let w = adj[*i];
                *i += 1;
                charge(1);
                if index[w as usize] == NONE {
                    index[w as usize] = next;
                    low[w as usize] = next;
                    next += 1;
                    stack.push(w);
                    on_stack[w as usize] = true;
                    frames.push((w, 0));
                } else if on_stack[w as usize] {
                    low[v as usize] = low[v as usize].min(index[w as usize]);
                }
                continue;
            }
            frames.pop();
            if low[v as usize] == index[v as usize] {
                // `v` roots its SCC: the members are it and everything above it on the
                // stack (pushed when indexed, it is popped only with its own SCC) — the
                // pop `call_graph::detect_cycles` uses.
                while let Some(w) = stack.pop() {
                    on_stack[w as usize] = false;
                    comp[w as usize] = n_comps;
                    if w == v {
                        break;
                    }
                }
                n_comps += 1;
            }
            if let Some(&(parent, _)) = frames.last() {
                low[parent as usize] = low[parent as usize].min(low[v as usize]);
            }
        }
    }
    // Tarjan emits components in REVERSE topological order.
    for c in &mut comp {
        *c = n_comps - 1 - *c;
    }
    comp
}
