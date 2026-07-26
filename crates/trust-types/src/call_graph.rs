// trust-types/call_graph.rs: Call graph types for reachability analysis
//
// Pure data types for call graph representation.
// Analysis logic (BFS reachability) moved to trust_vcgen/reachability.rs per #162.
//
// Part of #52
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::fx::{FxHashMap, FxHashSet};
use crate::model::SourceSpan;

#[derive(Debug, Clone, Copy)]
enum Resolution<'a> {
    Unique(&'a str),
    Ambiguous,
}

/// The byte index of the FIRST occurrence of `sep` in `s` at angle-bracket depth
/// 0 (OUTSIDE any `<...>`). `None` if `sep` never appears at top level. Used by
/// [`canonical_trait_method`] to split a trait-impl `inner` on the TOP-LEVEL
/// ` as ` / ` for ` without being fooled by a `<...>`-nested occurrence.
#[must_use]
fn top_level_sep(s: &str, sep: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    let sep_bytes = sep.as_bytes();
    let mut depth: i32 = 0;
    let mut i = 0usize;
    while i + sep_bytes.len() <= bytes.len() {
        match bytes[i] {
            b'<' => depth += 1,
            b'>' => depth -= 1,
            _ => {}
        }
        if depth == 0 && &bytes[i..i + sep_bytes.len()] == sep_bytes {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Trust: TRAIT-IMPL SPELLING CANONICALIZATION — parse a trait-method def-path
/// into the normalized tuple `(trait_path, trait_generic_args, self_ty, method)`,
/// canonicalizing the TWO spellings rustc emits for the SAME associated function:
///
///   * QUALIFIED (call site):   `<SELF as TRAIT<ARGS>>::METHOD`
///   * IMPL-BLOCK (dump path):  `MOD::<impl TRAIT<ARGS> for SELF>::METHOD`
///
/// (a `From` forwarder's call is spelled `<u32 as std::convert::From<u8>>::from`
/// while its callee's def_path is `std::convert::num::<impl std::convert::From<u8>
/// for u32>::from` — the same function, unbridgeable by exact/suffix match.)
///
/// Returns `None` for anything that is NOT one of these two shapes (an inherent
/// method, a free function, a generic method segment, a malformed path). Matching
/// on the tuple is EXACT, NEVER substring/fuzzy: a false match would conflate two
/// distinct functions, so `From<u8>` vs `From<u16>` (different ARGS) never
/// cross-match, nor do `for u32` vs `for u64` (different SELF). The containing
/// module path (before the impl-block `<`) is intentionally dropped — trait
/// coherence makes `(trait, args, self, method)` a unique identity.
#[must_use]
pub fn canonical_trait_method(def_path: &str) -> Option<(String, String, String, String)> {
    let open = def_path.find('<')?;
    let bytes = def_path.as_bytes();
    let mut depth = 0usize;
    let mut close = None;
    for (i, &b) in bytes.iter().enumerate().skip(open) {
        match b {
            b'<' => depth += 1,
            b'>' => {
                depth -= 1;
                if depth == 0 {
                    close = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let close = close?;
    let method = def_path.get(close + 1..)?.strip_prefix("::")?;
    if method.is_empty() || method.contains(':') || method.contains('<') {
        return None;
    }
    let inner = def_path.get(open + 1..close)?;
    let (trait_with_args, self_ty) = if let Some(rest) = inner.strip_prefix("impl ") {
        let for_idx = top_level_sep(rest, " for ")?;
        (rest[..for_idx].trim(), rest[for_idx + " for ".len()..].trim())
    } else {
        let as_idx = top_level_sep(inner, " as ")?;
        (inner[as_idx + " as ".len()..].trim(), inner[..as_idx].trim())
    };
    let (trait_path, trait_args) = match trait_with_args.find('<') {
        Some(ti) => {
            if !trait_with_args.ends_with('>') {
                return None;
            }
            (trait_with_args[..ti].trim(), trait_with_args[ti + 1..trait_with_args.len() - 1].trim())
        }
        None => (trait_with_args, ""),
    };
    if trait_path.is_empty() || self_ty.is_empty() {
        return None;
    }
    Some((trait_path.to_string(), trait_args.to_string(), self_ty.to_string(), method.to_string()))
}

/// Reusable exact/name/suffix index for deterministic callee resolution.
///
/// Building the index is linear in the total number of def-path segments;
/// every subsequent lookup is O(1). Keep one resolver for a whole call-graph
/// pass instead of rescanning all nodes for each edge.
#[derive(Debug, Clone)]
pub struct CalleeResolver<'a> {
    exact: FxHashSet<&'a str>,
    shorthand: FxHashMap<&'a str, Resolution<'a>>,
    // Trust: TRAIT-IMPL SPELLING CANONICALIZATION — the `(trait, args, self,
    // method)` canonical tuple of every candidate def-path that IS a trait method,
    // so a call spelled `<SELF as TRAIT>::M` resolves to the `<impl TRAIT for
    // SELF>::M` dump def_path (and vice-versa) without an exact/suffix bridge.
    // Ambiguity (two def_paths canonicalizing to the same tuple) fails closed.
    canonical: FxHashMap<(String, String, String, String), Resolution<'a>>,
}

impl<'a> CalleeResolver<'a> {
    /// Build a resolver from `(def_path, function_name)` candidates.
    #[must_use]
    pub fn new(candidates: impl IntoIterator<Item = (&'a str, &'a str)>) -> Self {
        let mut resolver = Self {
            exact: FxHashSet::default(),
            shorthand: FxHashMap::default(),
            canonical: FxHashMap::default(),
        };

        for (def_path, name) in candidates {
            resolver.exact.insert(def_path);
            resolver.record_shorthand(name, def_path);

            // Pre-index every `::`-delimited suffix. This preserves qualified
            // suffix support without an O(V) fallback scan per call edge.
            for (separator, _) in def_path.match_indices("::") {
                resolver.record_shorthand(&def_path[separator + 2..], def_path);
            }

            // Trust: index the trait-impl canonical tuple (if `def_path` is a
            // trait method), so the qualified/impl-block spelling gap is bridged.
            if let Some(key) = canonical_trait_method(def_path) {
                resolver.record_canonical(key, def_path);
            }
        }

        resolver
    }

    /// Resolve an exact def-path or globally unique shorthand/suffix, else —
    /// Trust — a globally unique trait-impl canonical-tuple match.
    #[must_use]
    pub fn resolve(&self, callee: &str) -> Option<&'a str> {
        if let Some(exact) = self.exact.get(callee) {
            return Some(*exact);
        }

        match self.shorthand.get(callee) {
            Some(Resolution::Unique(def_path)) => return Some(*def_path),
            Some(Resolution::Ambiguous) => return None,
            None => {}
        }

        // Trust: TRAIT-IMPL CANONICAL-TUPLE match (only when `callee` parses as a
        // trait method). EXACT tuple equality; ambiguity fails closed.
        let key = canonical_trait_method(callee)?;
        match self.canonical.get(&key) {
            Some(Resolution::Unique(def_path)) => Some(*def_path),
            Some(Resolution::Ambiguous) | None => None,
        }
    }

    fn record_shorthand(&mut self, shorthand: &'a str, def_path: &'a str) {
        match self.shorthand.get_mut(shorthand) {
            None => {
                self.shorthand.insert(shorthand, Resolution::Unique(def_path));
            }
            Some(existing) => {
                if matches!(*existing, Resolution::Unique(previous) if previous != def_path) {
                    *existing = Resolution::Ambiguous;
                }
            }
        }
    }

    fn record_canonical(
        &mut self,
        key: (String, String, String, String),
        def_path: &'a str,
    ) {
        match self.canonical.get_mut(&key) {
            None => {
                self.canonical.insert(key, Resolution::Unique(def_path));
            }
            Some(existing) => {
                if matches!(*existing, Resolution::Unique(previous) if previous != def_path) {
                    *existing = Resolution::Ambiguous;
                }
            }
        }
    }
}

/// A node in the call graph representing a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallGraphNode {
    /// Fully qualified def_path (e.g., "crate::module::function").
    pub def_path: String,
    /// Human-readable name.
    pub name: String,
    /// Whether this function is a public API entry point.
    pub is_public: bool,
    /// Whether this function is an entry point (`main`, `#[test]`, `#[tokio::main]`, etc.).
    pub is_entry_point: bool,
    /// Source location.
    pub span: SourceSpan,
}

/// A directed edge in the call graph: caller -> callee.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallGraphEdge {
    /// Def path of the calling function.
    pub caller: String,
    /// Def path or name of the called function.
    pub callee: String,
    /// Source location of the call site.
    pub call_site: SourceSpan,
}

/// A complete call graph for a crate.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CallGraph {
    /// All functions in the crate.
    pub nodes: Vec<CallGraphNode>,
    /// All call edges (caller -> callee).
    pub edges: Vec<CallGraphEdge>,
}

impl CallGraph {
    /// Create a new empty call graph.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a function node to the graph.
    pub fn add_node(&mut self, node: CallGraphNode) {
        self.nodes.push(node);
    }

    /// Add a call edge to the graph.
    pub fn add_edge(&mut self, edge: CallGraphEdge) {
        self.edges.push(edge);
    }

    /// Return all entry point def_paths.
    #[must_use]
    pub fn entry_points(&self) -> Vec<&str> {
        self.nodes.iter().filter(|n| n.is_entry_point).map(|n| n.def_path.as_str()).collect()
    }

    /// Return all public function def_paths.
    #[must_use]
    pub fn public_functions(&self) -> Vec<&str> {
        self.nodes.iter().filter(|n| n.is_public).map(|n| n.def_path.as_str()).collect()
    }

    /// Resolve a call target to the unique matching node def-path.
    ///
    /// Fully-qualified def-paths take precedence. A short name or qualified
    /// suffix is accepted only when it identifies exactly one distinct node.
    /// Ambiguous and external targets both return `None`; consumers of proof
    /// facts must not guess which function an ambiguous spelling denotes.
    #[must_use]
    pub fn resolve_unique_callee(&self, callee: &str) -> Option<&str> {
        self.callee_resolver().resolve(callee)
    }

    /// Build a reusable resolver over all nodes in this graph.
    #[must_use]
    pub fn callee_resolver(&self) -> CalleeResolver<'_> {
        CalleeResolver::new(
            self.nodes.iter().map(|node| (node.def_path.as_str(), node.name.as_str())),
        )
    }

    /// Whether the call graph is ACYCLIC — no function (directly or transitively)
    /// calls itself. An acyclic call graph has no recursion, so combined with
    /// every function being intra-procedurally loop-free (see
    /// [`crate::structural_termination`]) the whole set terminates STRUCTURALLY:
    /// no loops and no recursion bounds every execution. This is one sound input
    /// to the E6 `Total` facet, not the whole of it (a recursive function may
    /// still terminate by a decreasing measure — the E5 lane).
    ///
    /// Edges to callees NOT present as nodes here (external / `std` / unresolved)
    /// are leaves: they cannot close a recursion cycle among this graph's own
    /// functions. A callee spelling is matched by def-path first, then by name.
    #[must_use]
    pub fn is_acyclic(&self) -> bool {
        // Index each node by def-path and (as a fallback) by name; def-path wins.
        let mut idx_of: FxHashMap<&str, usize> = FxHashMap::default();
        for (i, n) in self.nodes.iter().enumerate() {
            idx_of.entry(n.def_path.as_str()).or_insert(i);
        }
        for (i, n) in self.nodes.iter().enumerate() {
            idx_of.entry(n.name.as_str()).or_insert(i);
        }
        // Adjacency by node index, keeping only edges to resolvable nodes.
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); self.nodes.len()];
        for e in &self.edges {
            if let (Some(&ci), Some(&ti)) =
                (idx_of.get(e.caller.as_str()), idx_of.get(e.callee.as_str()))
            {
                adj[ci].push(ti);
            }
        }
        // Iterative three-colour DFS from every node; a grey→grey edge is a cycle.
        let mut colour = vec![0u8; self.nodes.len()]; // 0 white, 1 grey, 2 black
        for start in 0..self.nodes.len() {
            if colour[start] != 0 {
                continue;
            }
            colour[start] = 1;
            let mut stack = vec![(start, 0usize)];
            while let Some(&(node, k)) = stack.last() {
                if k < adj[node].len() {
                    stack.last_mut().unwrap().1 += 1;
                    let next = adj[node][k];
                    match colour[next] {
                        1 => return false,
                        0 => {
                            colour[next] = 1;
                            stack.push((next, 0));
                        }
                        _ => {}
                    }
                } else {
                    colour[node] = 2;
                    stack.pop();
                }
            }
        }
        true
    }
}

/// Resolve a callee spelling against an arbitrary function universe.
///
/// Resolution is deterministic and fail-closed:
///
/// 1. An exact def-path match always wins.
/// 2. Otherwise, a function-name or `::`-delimited def-path suffix match is
///    accepted only when all matches denote the same def-path.
/// 3. No match or multiple distinct matches returns `None`.
///
/// The complete candidate universe must be supplied. Resolving against a
/// partially populated summary cache could make a globally ambiguous name
/// appear temporarily unique.
#[must_use]
pub fn resolve_unique_def_path<'a>(
    callee: &str,
    candidates: impl IntoIterator<Item = (&'a str, &'a str)>,
) -> Option<&'a str> {
    CalleeResolver::new(candidates).resolve(callee)
}

/// Result of reachability analysis on a call graph.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReachabilityResult {
    /// Entry points used as BFS roots.
    pub entry_points: Vec<String>,
    /// Public functions reachable from entry points.
    pub reachable: Vec<ReachableFunction>,
    /// Public functions NOT reachable from any entry point.
    pub unreachable: Vec<UnreachableFunction>,
    /// Total number of functions in the graph.
    pub total_functions: usize,
    /// Total number of call edges.
    pub total_edges: usize,
}

impl ReachabilityResult {
    /// Returns true if all public functions are reachable.
    #[must_use]
    pub fn is_fully_connected(&self) -> bool {
        self.unreachable.is_empty()
    }

    /// Number of unreachable public functions.
    #[must_use]
    pub fn unreachable_count(&self) -> usize {
        self.unreachable.len()
    }
}

/// A public function that is reachable from entry points.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReachableFunction {
    pub def_path: String,
    pub name: String,
    pub span: SourceSpan,
}

/// A public function that is NOT reachable from any entry point.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnreachableFunction {
    pub def_path: String,
    pub name: String,
    pub span: SourceSpan,
    /// Why the function is considered unreachable.
    pub reason: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(def_path: &str, name: &str) -> CallGraphNode {
        CallGraphNode {
            def_path: def_path.to_string(),
            name: name.to_string(),
            is_public: false,
            is_entry_point: false,
            span: SourceSpan::default(),
        }
    }

    #[test]
    fn unique_callee_resolution_is_exact_first_and_fail_closed() {
        let graph = CallGraph {
            nodes: vec![
                node("crate::left::helper", "helper"),
                node("crate::right::helper", "helper"),
                node("crate::right::unique", "unique"),
            ],
            edges: vec![],
        };

        assert_eq!(
            graph.resolve_unique_callee("crate::left::helper"),
            Some("crate::left::helper"),
            "an exact def-path must win even when its short name is ambiguous"
        );
        assert_eq!(graph.resolve_unique_callee("unique"), Some("crate::right::unique"));
        assert_eq!(graph.resolve_unique_callee("right::unique"), Some("crate::right::unique"));
        assert_eq!(graph.resolve_unique_callee("helper"), None);
        assert_eq!(graph.resolve_unique_callee("missing"), None);
    }

    #[test]
    fn unique_callee_resolution_does_not_depend_on_candidate_order() {
        let forward = [("crate::left::helper", "helper"), ("crate::right::helper", "helper")];
        let reverse = [forward[1], forward[0]];

        assert_eq!(resolve_unique_def_path("helper", forward), None);
        assert_eq!(resolve_unique_def_path("helper", reverse), None);
    }

    fn edge(caller: &str, callee: &str) -> CallGraphEdge {
        CallGraphEdge {
            caller: caller.to_string(),
            callee: callee.to_string(),
            call_site: SourceSpan::default(),
        }
    }

    #[test]
    fn empty_and_chain_call_graphs_are_acyclic() {
        assert!(CallGraph::new().is_acyclic(), "an empty graph is acyclic");
        // a → b → c, no back edge.
        let g = CallGraph {
            nodes: vec![node("a", "a"), node("b", "b"), node("c", "c")],
            edges: vec![edge("a", "b"), edge("b", "c")],
        };
        assert!(g.is_acyclic());
    }

    #[test]
    fn direct_and_mutual_recursion_are_cyclic() {
        // direct self-recursion a → a.
        let g = CallGraph { nodes: vec![node("a", "a")], edges: vec![edge("a", "a")] };
        assert!(!g.is_acyclic(), "direct recursion is a cycle");
        // mutual recursion a → b → a.
        let g = CallGraph {
            nodes: vec![node("a", "a"), node("b", "b")],
            edges: vec![edge("a", "b"), edge("b", "a")],
        };
        assert!(!g.is_acyclic(), "mutual recursion is a cycle");
    }

    #[test]
    fn edges_to_external_callees_are_leaves() {
        // `a` calls an external `std::…` not present as a node — cannot form a
        // recursion cycle among this graph's functions.
        let g = CallGraph {
            nodes: vec![node("a", "a")],
            edges: vec![edge("a", "std::vec::Vec::push")],
        };
        assert!(g.is_acyclic());
    }

    #[test]
    fn callee_matched_by_name_still_detects_the_cycle() {
        // The edge names the callee by bare name; it must still resolve to the
        // node and close the a ↔ b cycle.
        let g = CallGraph {
            nodes: vec![node("crate::a", "a"), node("crate::b", "b")],
            edges: vec![edge("crate::a", "b"), edge("crate::b", "a")],
        };
        assert!(!g.is_acyclic());
    }

    #[test]
    fn resolver_bridges_trait_impl_qualified_and_impl_block_spellings() {
        // Trust: Item 2 (wave-a) — a `From` forwarder's call spelling
        // `<u32 as From<u8>>::from` resolves to the leaf's impl-block def_path
        // `...<impl From<u8> for u32>::from` via the canonical (trait, args, self,
        // method) tuple, so `build_call_graph` creates the edge and orders the leaf
        // FIRST. A DIFFERENT impl never cross-matches.
        let candidates = [
            ("std::convert::num::<impl std::convert::From<u8> for u32>::from", "from"),
            ("std::convert::num::<impl std::convert::From<u16> for u64>::from", "from"),
        ];
        let r = CalleeResolver::new(candidates);
        assert_eq!(
            r.resolve("<u32 as std::convert::From<u8>>::from"),
            Some("std::convert::num::<impl std::convert::From<u8> for u32>::from"),
        );
        assert_eq!(r.resolve("<u64 as std::convert::From<u8>>::from"), None);
        assert_eq!(r.resolve("<u32 as std::convert::From<u16>>::from"), None);
    }

    #[test]
    fn resolver_canonical_ambiguity_fails_closed() {
        // Two def_paths canonicalizing to the SAME tuple ⇒ ambiguous ⇒ decline.
        let candidates = [
            ("a::<impl std::convert::From<u8> for u32>::from", "from"),
            ("b::<impl std::convert::From<u8> for u32>::from", "from"),
        ];
        let r = CalleeResolver::new(candidates);
        assert_eq!(r.resolve("<u32 as std::convert::From<u8>>::from"), None);
    }

    #[test]
    fn canonical_trait_method_parses_both_spellings_equal_and_rejects_offshape() {
        let q = canonical_trait_method("<u32 as std::convert::From<u8>>::from").unwrap();
        let d = canonical_trait_method(
            "std::convert::num::<impl std::convert::From<u8> for u32>::from",
        )
        .unwrap();
        assert_eq!(q, d);
        assert_eq!(
            q,
            (
                "std::convert::From".to_string(),
                "u8".to_string(),
                "u32".to_string(),
                "from".to_string()
            )
        );
        assert_ne!(q, canonical_trait_method("<u32 as std::convert::From<u16>>::from").unwrap());
        // Inherent methods / free fns decline (keep exact/suffix matching).
        assert!(canonical_trait_method("std::num::NonZero::<u32>::get").is_none());
        assert!(canonical_trait_method("plain_fn").is_none());
    }
}
