//! Propagate a per-function structural facet fact across the call graph.
//!
//! The `structural_*` modules decide a facet INTRINSICALLY for one function (its
//! own control flow / statements). A whole-function facet also requires every
//! CALLEE to have the facet. This module closes that gap with a pure graph
//! fixpoint over the [`CallGraph`] — no `rustc` dependency — and it distinguishes
//! the two propagation semantics the facets need:
//!
//!   * [`greatest_facet_closure`] — the LARGEST set of intrinsically-satisfying
//!     functions closed under "every callee also satisfies". RECURSION is
//!     preserved: a mutually-recursive group in which every member satisfies
//!     intrinsically stays in the facet. Use for `NoPanic` and `Pure` (a
//!     recursive function that never panics / has no effect is still `NoPanic` /
//!     `Pure`).
//!   * [`least_facet_closure`] — the SMALLEST set built up from callees to
//!     callers, so a function joins only once ALL its callees already have the
//!     facet. RECURSION is EXCLUDED: a function on a call cycle never joins. Use
//!     for `Total` — a mutually-recursive pair of loop-free functions may still
//!     diverge, so it is not structurally total (its termination would need a
//!     decreasing-measure argument, the E5 lane).
//!
//! A callee that does not resolve to a node in the graph is EXTERNAL (`std`,
//! foreign). It only counts as satisfying the facet when its spelling is in
//! `trusted_external`; otherwise the caller fails closed. So both closures are
//! sound: an unknown external callee never silently confers a facet.

use std::collections::HashSet;

use crate::call_graph::CallGraph;
use crate::fx::{FxHashMap, FxHashSet};

/// A resolved callee: an in-graph function (by def-path) or an external name.
enum Callee<'a> {
    Internal(&'a str),
    External(&'a str),
}

/// For each node def-path, its callees (resolved to in-graph def-paths or kept
/// as external names). Edges whose caller is not a node are ignored.
fn callees_by_caller(cg: &CallGraph) -> FxHashMap<&str, Vec<Callee<'_>>> {
    let resolver = cg.callee_resolver();
    let mut map: FxHashMap<&str, Vec<Callee<'_>>> =
        FxHashMap::with_capacity_and_hasher(cg.nodes.len(), Default::default());
    for n in &cg.nodes {
        map.entry(n.def_path.as_str()).or_default();
    }
    for e in &cg.edges {
        let Some(callees) = map.get_mut(e.caller.as_str()) else {
            continue;
        };
        let callee = match resolver.resolve(&e.callee) {
            Some(def_path) => Callee::Internal(def_path),
            None => Callee::External(e.callee.as_str()),
        };
        callees.push(callee);
    }
    map
}

/// Whether every callee of `caller` currently satisfies the facet: an internal
/// callee must be in `have`, an external callee must be in `trusted_external`.
fn all_callees_satisfy(
    callees: &[Callee<'_>],
    have: &FxHashSet<&str>,
    trusted_external: &HashSet<String>,
) -> bool {
    callees.iter().all(|c| match c {
        Callee::Internal(dp) => have.contains(*dp),
        Callee::External(name) => trusted_external.contains(*name),
    })
}

/// GREATEST fixpoint (recursion-preserving) — see the module docs. `base` is the
/// set of node def-paths that satisfy the facet INTRINSICALLY; the result is the
/// subset that also has all callees satisfying (transitively). Suitable for
/// `NoPanic` / `Pure`.
#[must_use]
pub fn greatest_facet_closure(
    cg: &CallGraph,
    base: &HashSet<String>,
    trusted_external: &HashSet<String>,
) -> HashSet<String> {
    let callees = callees_by_caller(cg);
    let cap = cg.nodes.len().min(base.len());
    // Start from every intrinsically-satisfying node and shrink.
    let mut have: FxHashSet<&str> = FxHashSet::with_capacity_and_hasher(cap, Default::default());
    let mut active: Vec<(&str, &[Callee<'_>])> = Vec::with_capacity(cap);
    for n in &cg.nodes {
        if base.contains(&n.def_path) {
            let f = n.def_path.as_str();
            if have.insert(f) {
                let cs = callees.get(f).map(Vec::as_slice).unwrap_or(&[]);
                active.push((f, cs));
            }
        }
    }
    let mut doomed: Vec<&str> = Vec::new();
    loop {
        active.retain(|&(f, cs)| {
            if all_callees_satisfy(cs, &have, trusted_external) {
                true
            } else {
                doomed.push(f);
                false
            }
        });
        if doomed.is_empty() {
            return have.into_iter().map(str::to_owned).collect();
        }
        for f in doomed.drain(..) {
            have.remove(f);
        }
    }
}

/// LEAST fixpoint (recursion-excluding) — see the module docs. A function joins
/// only when it is in `base` AND all its callees already have the facet, so a
/// function on a call cycle never joins. Suitable for `Total`.
#[must_use]
pub fn least_facet_closure(
    cg: &CallGraph,
    base: &HashSet<String>,
    trusted_external: &HashSet<String>,
) -> HashSet<String> {
    let callees = callees_by_caller(cg);
    let cap = cg.nodes.len().min(base.len());
    let mut have: FxHashSet<&str> = FxHashSet::with_capacity_and_hasher(cap, Default::default());
    let mut pending: Vec<(&str, &[Callee<'_>])> = Vec::with_capacity(cap);
    for n in &cg.nodes {
        if base.contains(&n.def_path) {
            let f = n.def_path.as_str();
            let cs = callees.get(f).map(Vec::as_slice).unwrap_or(&[]);
            pending.push((f, cs));
        }
    }
    loop {
        let mut added = false;
        pending.retain(|&(f, cs)| {
            if have.contains(f) {
                return false;
            }
            if all_callees_satisfy(cs, &have, trusted_external) {
                have.insert(f);
                added = true;
                false
            } else {
                true
            }
        });
        if !added {
            return have.into_iter().map(str::to_owned).collect();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::call_graph::{CallGraph, CallGraphEdge, CallGraphNode};
    use crate::model::SourceSpan;

    fn node(def_path: &str) -> CallGraphNode {
        CallGraphNode {
            def_path: def_path.to_string(),
            name: def_path.rsplit("::").next().unwrap_or(def_path).to_string(),
            is_public: false,
            is_entry_point: false,
            span: SourceSpan::default(),
        }
    }
    fn edge(caller: &str, callee: &str) -> CallGraphEdge {
        CallGraphEdge {
            caller: caller.to_string(),
            callee: callee.to_string(),
            call_site: SourceSpan::default(),
        }
    }
    fn set(items: &[&str]) -> HashSet<String> {
        items.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn chain_propagates_when_the_leaf_satisfies() {
        // a → b → c; all intrinsically satisfy → all keep the facet.
        let cg = CallGraph {
            nodes: vec![node("a"), node("b"), node("c")],
            edges: vec![edge("a", "b"), edge("b", "c")],
        };
        let base = set(&["a", "b", "c"]);
        let got = greatest_facet_closure(&cg, &base, &HashSet::new());
        assert_eq!(got, set(&["a", "b", "c"]));
        // The least closure agrees on an acyclic graph.
        assert_eq!(least_facet_closure(&cg, &base, &HashSet::new()), set(&["a", "b", "c"]));
    }

    #[test]
    fn a_non_satisfying_callee_denies_its_callers() {
        // a → b → c, but c does NOT intrinsically satisfy → a and b lose it too.
        let cg = CallGraph {
            nodes: vec![node("a"), node("b"), node("c")],
            edges: vec![edge("a", "b"), edge("b", "c")],
        };
        let base = set(&["a", "b"]); // c absent
        assert_eq!(greatest_facet_closure(&cg, &base, &HashSet::new()), HashSet::new());
        assert_eq!(least_facet_closure(&cg, &base, &HashSet::new()), HashSet::new());
    }

    #[test]
    fn recursion_is_preserved_by_greatest_but_excluded_by_least() {
        // a ↔ b, both intrinsically satisfy.
        let cg = CallGraph {
            nodes: vec![node("a"), node("b")],
            edges: vec![edge("a", "b"), edge("b", "a")],
        };
        let base = set(&["a", "b"]);
        // NoPanic / Pure: a recursive pair that never panics / has no effect keeps it.
        assert_eq!(greatest_facet_closure(&cg, &base, &HashSet::new()), set(&["a", "b"]));
        // Total: a recursive pair is NOT structurally total.
        assert_eq!(least_facet_closure(&cg, &base, &HashSet::new()), HashSet::new());
    }

    #[test]
    fn external_callee_needs_to_be_trusted() {
        // a calls an external std function.
        let cg = CallGraph { nodes: vec![node("a")], edges: vec![edge("a", "std::mem::swap")] };
        let base = set(&["a"]);
        // Untrusted external → a fails closed under both closures.
        assert_eq!(greatest_facet_closure(&cg, &base, &HashSet::new()), HashSet::new());
        assert_eq!(least_facet_closure(&cg, &base, &HashSet::new()), HashSet::new());
        // Trusted external → a keeps the facet.
        let trusted = set(&["std::mem::swap"]);
        assert_eq!(greatest_facet_closure(&cg, &base, &trusted), set(&["a"]));
        assert_eq!(least_facet_closure(&cg, &base, &trusted), set(&["a"]));
    }
}
