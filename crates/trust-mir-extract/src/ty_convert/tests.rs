use super::*;

#[derive(Clone, Debug)]
struct DepthGraphNode {
    adt: bool,
    children: Vec<usize>,
}

fn graph_adt_depth(
    graph: &[DepthGraphNode],
    root: usize,
    cutoff: usize,
    node_budget: usize,
) -> usize {
    bounded_adt_arg_depth(
        root,
        cutoff,
        node_budget,
        |node| graph[node].adt,
        |node, push| graph[node].children.iter().copied().all(push),
    )
}

#[test]
fn bounded_adt_depth_collapses_a_shared_tuple_dag() {
    let mut graph = vec![DepthGraphNode { adt: true, children: Vec::new() }];
    for previous in 0..1_000 {
        graph.push(DepthGraphNode { adt: false, children: vec![previous, previous] });
    }
    assert_eq!(graph_adt_depth(&graph, 1_000, 5, 4_096), 1);
}

#[test]
fn bounded_adt_depth_clamps_exactly_after_four_adts() {
    let chain = |count: usize| {
        (0..count)
            .map(|index| DepthGraphNode {
                adt: true,
                children: (index + 1 < count).then_some(index + 1).into_iter().collect(),
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(graph_adt_depth(&chain(4), 0, 5, 32), 4);
    assert_eq!(graph_adt_depth(&chain(5), 0, 5, 32), 5);
}

#[test]
fn bounded_adt_depth_handles_deep_wrappers_without_recursion() {
    let graph = (0..3_000)
        .map(|index| DepthGraphNode {
            adt: false,
            children: (index + 1 < 3_000).then_some(index + 1).into_iter().collect(),
        })
        .collect::<Vec<_>>();
    assert_eq!(graph_adt_depth(&graph, 0, 5, 4_096), 0);
}

#[test]
fn bounded_adt_depth_wide_or_over_budget_graph_fails_closed() {
    let mut graph = vec![DepthGraphNode { adt: false, children: (1..=4_096).collect() }];
    graph.extend((0..4_096).map(|_| DepthGraphNode { adt: false, children: Vec::new() }));
    assert_eq!(graph_adt_depth(&graph, 0, 5, 4_096), 5);

    let exact = vec![
        DepthGraphNode { adt: false, children: vec![1] },
        DepthGraphNode { adt: false, children: vec![2] },
        DepthGraphNode { adt: false, children: Vec::new() },
    ];
    assert_eq!(graph_adt_depth(&exact, 0, 5, 3), 0);
    assert_eq!(graph_adt_depth(&exact, 0, 5, 2), 5);
}

#[test]
fn bounded_adt_depth_revisits_shared_nodes_at_greater_depth_in_either_order() {
    for root_children in [vec![0, 1], vec![1, 0]] {
        let graph = vec![
            DepthGraphNode { adt: false, children: vec![3] },
            DepthGraphNode { adt: true, children: vec![0] },
            DepthGraphNode { adt: false, children: root_children },
            DepthGraphNode { adt: true, children: Vec::new() },
        ];
        assert_eq!(graph_adt_depth(&graph, 2, 5, 32), 2);
    }
}

#[test]
fn trust_tuple_or_unit_maps_empty_tuple_to_unit() {
    assert_eq!(trust_tuple_or_unit(vec![]), TrustTy::Unit);
}

#[test]
fn trust_tuple_or_unit_preserves_non_empty_tuple() {
    assert_eq!(
        trust_tuple_or_unit(vec![TrustTy::Bool, TrustTy::Int { width: 32, signed: true }]),
        TrustTy::Tuple(vec![TrustTy::Bool, TrustTy::Int { width: 32, signed: true }]),
    );
}

#[test]
fn unsupported_ty_preserves_reason() {
    assert_eq!(
        unsupported_ty("TyKind::Alias", "not normalized"),
        TrustTy::Unsupported {
            kind: "TyKind::Alias".to_string(),
            detail: "not normalized".to_string(),
        },
    );
}

#[test]
fn ty_lowering_context_starts_with_guard_budget() {
    let ctx = TyLoweringCtx::default();

    assert_eq!(ctx.depth, 0);
    assert_eq!(ctx.remaining_nodes, MAX_TYPE_LOWERING_NODES);
    assert_eq!(ctx.produced_nodes, 0);
    assert_eq!(ctx.produced_budget, MAX_TYPE_LOWERING_PRODUCED_NODES);
    assert!(ctx.adt_stack.is_empty());
}

/// The ANCESTOR RE-CHARGE regression, pinned at the charge site.
///
/// Until 2026-08-28 `convert_ty_inner` charged `produced_node_count(&lowered, ..)`
/// — the size of the WHOLE produced subtree — at every level of its own recursion.
/// Each node was therefore billed once for itself and once more for each of its
/// ancestors, so the meter measured `sum over nodes of subtree_size(node)` =
/// O(nodes x depth) instead of the node count the constant, the field's doc
/// comment and the DROP-ONLY soundness argument all claim it measures. The guard
/// then degraded types that were comfortably inside its own advertised budget.
///
/// MEASURED on `crates/trust-semantics` the day it was fixed, over 20319 traced
/// walks: the ONLY type the guard degraded in the whole crate was
/// `Result<(), clean_kernel::EnvError>` — charged 8005 against the 8000 budget for
/// a walk that materializes 5633 nodes and RETAINS 6. Correcting this one charge
/// took the crate's degraded walks 83 -> 0 and its rows 101 -> 104 with ZERO rows
/// lost, and made three of the four blocked bodies lower.
///
/// This is the same correction `a0f2d05e35` already made to trust-vcgen's sibling
/// meter: "T2 — meter PEAK type materialization, not cumulative re-query churn".
#[test]
fn a_fresh_node_costs_one_regardless_of_its_subtree_size() {
    let leaf = TrustTy::Bool;
    // A deliberately fat subtree: what the old charge would have billed here.
    let mut fat = TrustTy::Bool;
    for _ in 0..200 {
        fat = TrustTy::Ref { mutable: false, inner: Box::new(fat) };
    }
    assert!(
        produced_node_count(&fat, usize::MAX) > 100,
        "fixture must be fat or the assertion below cannot discriminate"
    );
    assert_eq!(fresh_node_charge(&leaf), 1);
    assert_eq!(
        fresh_node_charge(&fat),
        1,
        "a freshly materialized node must cost ONE, independently of the subtree \
         hanging off it. Charging its subtree size here re-bills every descendant \
         once per ancestor, making the meter O(nodes x depth) and the effective \
         allowance budget/average-depth instead of budget."
    );
}

/// `produced_node_count` counts EVERY structural node — including each variant
/// field — short-circuiting at `cap`. This is the produced-tree size the
/// extraction-time budget charges (the real clone/retain memory cost).
#[test]
fn produced_node_count_counts_all_nodes_and_caps() {
    // A leaf is 1 node.
    assert_eq!(produced_node_count(&TrustTy::Bool, 1000), 1);
    // An enum: 1 (Adt) + its flattened `fields` + each variant's fields.
    let enum_ty = TrustTy::adt_enum(
        "E",
        vec![
            trust_types::VariantDef {
                name: "A".into(),
                discriminant: 0,
                fields: vec![("0".into(), TrustTy::Bool), ("1".into(), TrustTy::Bool)],
            },
            trust_types::VariantDef {
                name: "B".into(),
                discriminant: 1,
                fields: vec![("0".into(), TrustTy::Bool)],
            },
        ],
    );
    // adt_enum dedups fields into the union view; count is bounded and > 1.
    let n = produced_node_count(&enum_ty, 10_000);
    assert!(n > 1, "an enum with fields must count more than one node, got {n}");
    // The cap short-circuits: a huge tree costs O(cap).
    let mut fields = Vec::new();
    for i in 0..5_000 {
        fields.push((format!("f{i}"), TrustTy::Bool));
    }
    let fat = TrustTy::adt("Fat", fields);
    assert_eq!(
        produced_node_count(&fat, 100),
        100,
        "counting must short-circuit at the cap (O(cap), not O(size))"
    );
}

/// Lever A step 2 — the datatype gate un-degrades EXACTLY `Level` (in the
/// `clean_kernel` crate, both def-path renderings) and nothing else, so no
/// other recursive ADT's lowering shifts this step.
#[test]
fn is_level_path_matches_only_kernel_level_both_renderings() {
    // Upstream-dependency rendering (crate-name prefixed) and local-crate
    // rendering (no prefix) both match.
    assert!(is_level_path("clean_kernel", "clean_kernel::level::Level"));
    assert!(is_level_path("clean_kernel", "level::Level"));
    // Not Name/Expr, not a same-named type in another crate, not a suffix hit.
    assert!(!is_level_path("clean_kernel", "clean_kernel::name::Name"));
    assert!(!is_level_path("clean_kernel", "clean_kernel::expr::Expr"));
    assert!(!is_level_path("clean_kernel", "clean_kernel::level::LevelArc"));
    assert!(!is_level_path("clean_kernel", "sublevel::Level"));
    assert!(!is_level_path("clean_kernel", "Level"));
    // Right path, WRONG crate — rejected by the crate-name guard.
    assert!(!is_level_path("other_crate", "level::Level"));
    assert!(!is_level_path("other_crate", "clean_kernel::level::Level"));
}

/// Lever A step 5 — the `Expr`/`ExprKind` datatype gates un-degrade EXACTLY the
/// kernel `Expr` struct and `ExprKind` enum (both def-path renderings), and
/// nothing else — no cross-firing between the two, and no `Level`/`Name`.
#[test]
fn is_expr_and_exprkind_paths_match_only_their_target_both_renderings() {
    // Expr struct: both renderings match.
    assert!(is_expr_path("clean_kernel", "clean_kernel::expr::Expr"));
    assert!(is_expr_path("clean_kernel", "expr::Expr"));
    // ExprKind enum: both renderings match.
    assert!(is_exprkind_path("clean_kernel", "clean_kernel::expr::kind::ExprKind"));
    assert!(is_exprkind_path("clean_kernel", "expr::kind::ExprKind"));
    // No cross-firing: the Expr gate must NOT match ExprKind and vice versa.
    assert!(!is_expr_path("clean_kernel", "expr::kind::ExprKind"));
    assert!(!is_expr_path("clean_kernel", "clean_kernel::expr::kind::ExprKind"));
    assert!(!is_exprkind_path("clean_kernel", "expr::Expr"));
    assert!(!is_exprkind_path("clean_kernel", "clean_kernel::expr::Expr"));
    // Neither matches Level/Name, a suffix hit, or a bare name.
    assert!(!is_expr_path("clean_kernel", "clean_kernel::level::Level"));
    assert!(!is_exprkind_path("clean_kernel", "clean_kernel::name::Name"));
    assert!(!is_expr_path("clean_kernel", "other::expr::Expr"));
    assert!(!is_expr_path("clean_kernel", "Expr"));
    assert!(!is_exprkind_path("clean_kernel", "ExprKind"));
    // Right path, WRONG crate — rejected by the crate-name guard.
    assert!(!is_expr_path("other_crate", "expr::Expr"));
    assert!(!is_exprkind_path("other_crate", "expr::kind::ExprKind"));
}

/// Lever A step 2 — the transparent-pointer wrapper recognition used to peel a
/// recursive `Succ(Arc<Level>)` field to a `Level` self-reference. The real
/// kernel stores children behind `Arc<Level>`; this covers the `Arc`/`Box`/`Rc`
/// def-path recognition (the fixture exercises the `Ref`/`RawPtr` peel branch).
#[test]
fn transparent_pointer_wrappers_recognized_by_def_path() {
    for wrapper in [
        "alloc::sync::Arc",
        "std::sync::Arc",
        "alloc::rc::Rc",
        "std::rc::Rc",
        "alloc::boxed::Box",
        "std::boxed::Box",
    ] {
        assert!(is_transparent_pointer_wrapper(wrapper), "{wrapper} must peel");
    }
    // A non-wrapper nominal ADT (e.g. the kernel `Name`) must NOT peel — its
    // `Param` field stays a by-name datatype reference, not its pointee.
    assert!(!is_transparent_pointer_wrapper("clean_kernel::name::Name"));
    assert!(!is_transparent_pointer_wrapper("clean_kernel::level::Level"));
    assert!(!is_transparent_pointer_wrapper("core::cell::UnsafeCell"));
}

/// A by-name recursive datatype reference is a `Ty::Datatype` with the referent
/// name and an EMPTY variant list — the sort marker a `Level` self-reference /
/// opaque `Name` field lowers to. SOUNDNESS: it asserts nothing.
#[test]
fn recursive_datatype_ref_is_empty_named_datatype() {
    match recursive_datatype_ref("clean_kernel::level::Level") {
        TrustTy::Datatype { name, variants } => {
            assert_eq!(name, "clean_kernel::level::Level");
            assert!(variants.is_empty(), "a by-name reference carries no variants");
        }
        other => panic!("expected an empty-variant Ty::Datatype, got {other:?}"),
    }
}

/// The fail-closed degraded leaf is the recursive-ADT `Unsupported` marker
/// (load-bearing `detail.starts_with("recursive")`) — byte-compatible with the
/// existing recursive-ADT skip in the consumer. SOUNDNESS: never a provable type.
#[test]
fn produced_budget_degraded_leaf_is_recursive_adt_marker() {
    match produced_budget_degraded_leaf() {
        TrustTy::Unsupported { kind, detail } => {
            assert_eq!(kind, "TyKind::Adt");
            assert!(
                detail.starts_with("recursive"),
                "leaf must be the fail-closed recursive-ADT marker: {detail}"
            );
        }
        other => panic!("degraded leaf must be the recursive-ADT marker, got {other:?}"),
    }
}

// ─── RC-1: canonical recursive-type lowering ────────────────────────────
//
// These exercise the two properties the change stands or falls on, WITHOUT a
// compiler session: (1) the cut set is a function of the type alone, i.e. the
// greedy FVS restricted to what a root can reach equals the global FVS
// restricted the same way, for every root and independent of discovery order;
// (2) a cut point's by-name marker still tells two instantiations of one
// generic ADT apart.

/// Successor-closure of `roots` in `edges` — exactly the node set
/// `canonical_cut_set`'s discovery walk would find from those seeds.
fn reachable_from(edges: &[Vec<usize>], roots: &[usize]) -> Vec<usize> {
    let mut seen = vec![false; edges.len()];
    let mut work: Vec<usize> = roots.to_vec();
    while let Some(node) = work.pop() {
        if seen[node] {
            continue;
        }
        seen[node] = true;
        work.extend(edges[node].iter().copied());
    }
    (0..edges.len()).filter(|n| seen[*n]).collect()
}

/// Induce `edges` on `nodes`, laid out in the given (arbitrary) index order —
/// the stand-in for a different root's discovery order.
fn induced_subgraph(edges: &[Vec<usize>], nodes: &[usize]) -> Vec<Vec<usize>> {
    let mut position = vec![usize::MAX; edges.len()];
    for (slot, node) in nodes.iter().enumerate() {
        position[*node] = slot;
    }
    nodes
        .iter()
        .map(|node| {
            let mut succ: Vec<usize> = Vec::new();
            for child in edges[*node].iter().copied() {
                let slot = position[child];
                if slot != usize::MAX && !succ.contains(&slot) {
                    succ.push(slot);
                }
            }
            succ
        })
        .collect()
}

/// A `CanonicalCutKey` standing for one type, from its rendered name and the
/// rendered names of the component it is being ranked in. The wrapper bit is
/// what `wraps_component_member` computes on interned types: does this
/// name's `<…>` argument list mention ANOTHER member of the component?
fn test_key(name: &str, component: &[&str]) -> CanonicalCutKey {
    let args = name.find('<').map_or("", |open| &name[open..]);
    let wraps = component.iter().any(|member| *member != name && args.contains(*member));
    (wraps, test_static_key(name))
}

/// The pre-2026-09-13 key: (segment count, path) with NO wrapper bit. The
/// segment count is taken on the ERASED head, before any `<…>` — exactly as
/// `canonical_cut_static_key` counts `sysroot_authenticated_def_path_str`
/// (no args) and then orders by the instantiated path.
fn test_static_key(name: &str) -> CanonicalCutStaticKey {
    let head = name.split('<').next().unwrap_or(name);
    (head.matches("::").count(), name.to_string(), 0, 0)
}

fn cut_labels(edges: &[Vec<usize>], names: &[&str], nodes: &[usize]) -> Vec<String> {
    let mut picked: Vec<String> = greedy_feedback_vertex_set(edges, &mut |node, component| {
        let members: Vec<&str> = component.iter().map(|member| names[nodes[*member]]).collect();
        test_key(names[nodes[node]], &members)
    })
    .into_iter()
    .map(|slot| names[nodes[slot]].to_string())
    .collect();
    picked.sort();
    picked
}

/// The discovery-seeding defect measured on `trust-spec-elab`: a repeated
/// seed must keep its FIRST index. With `HashMap::insert`'s overwrite, the
/// second `"a"` re-pointed `"a"` at index 1 — which the next seed `"b"` then
/// also received — so every edge into `"a"` was routed to `"b"`.
#[test]
fn intern_node_keeps_the_first_index() {
    let mut index: FxHashMap<&str, usize> = FxHashMap::default();
    let mut order: Vec<&str> = Vec::new();
    assert_eq!(intern_node(&mut index, &mut order, "a"), 0);
    assert_eq!(intern_node(&mut index, &mut order, "a"), 0);
    assert_eq!(intern_node(&mut index, &mut order, "b"), 1);
    assert_eq!(intern_node(&mut index, &mut order, "a"), 0);
    assert_eq!(order, vec!["a", "b"]);
    assert_eq!(index["a"], 0);
    assert_eq!(index["b"], 1);
}

#[test]
fn strongly_connected_components_separates_cycle_from_tail() {
    // 0 → 1 → 2 → 0, and 2 → 3 (a tail that never returns).
    let edges = vec![vec![1], vec![2], vec![0, 3], vec![]];
    let alive = vec![true; 4];
    let mut components: Vec<Vec<usize>> = strongly_connected_components(&edges, &alive)
        .into_iter()
        .map(|mut c| {
            c.sort();
            c
        })
        .collect();
    components.sort();
    assert_eq!(components, vec![vec![0, 1, 2], vec![3]]);
}

#[test]
fn strongly_connected_components_skips_dead_nodes() {
    // Same graph with node 1 deleted: the cycle is broken, so every surviving
    // component is a singleton. This is the step the greedy FVS iterates on.
    let edges = vec![vec![1], vec![2], vec![0, 3], vec![]];
    let alive = vec![true, false, true, true];
    let mut components: Vec<Vec<usize>> = strongly_connected_components(&edges, &alive)
        .into_iter()
        .map(|mut c| {
            c.sort();
            c
        })
        .collect();
    components.sort();
    assert_eq!(components, vec![vec![0], vec![2], vec![3]]);
}

#[test]
fn greedy_fvs_leaves_an_acyclic_graph_uncut_and_asks_for_no_keys() {
    // The overwhelmingly common case. It must cost NOTHING beyond one SCC
    // pass — no def-path rendering at all, which is why `canonical_cut_set`
    // computes keys lazily.
    let edges = vec![vec![1, 2], vec![2], vec![3], vec![]];
    let mut key_requests = 0usize;
    let cut = greedy_feedback_vertex_set(&edges, &mut |node, _component| {
        key_requests += 1;
        test_key(&format!("n{node}"), &[])
    });
    assert!(cut.is_empty(), "acyclic graph must have an empty cut set: {cut:?}");
    assert_eq!(key_requests, 0, "an acyclic graph must not render a single def path");
}

#[test]
fn greedy_fvs_cuts_a_self_loop() {
    // `struct S { next: Box<S> }` reduces to a single node with a self edge.
    let edges = vec![vec![0]];
    let cut = greedy_feedback_vertex_set(&edges, &mut |_, _| test_key("krate::S", &[]));
    assert_eq!(cut, vec![0]);
}

#[test]
fn greedy_fvs_cuts_the_shallowest_def_path_in_the_cycle() {
    // The measured `xor_all` cycle: Tree ↔ Arc<Tree> ↔ NonNull<ArcInner<Tree>>
    // ↔ ArcInner<Tree>. The cut must land on `Tree` — the type the cycle is
    // ABOUT — not on an std container internal, so the marker names something
    // the consumer can recognize. Here `Tree` wins on BOTH components of the
    // key: it wraps nothing, and it is the shallowest path.
    let names = [
        "xor_all::Tree",
        "std::sync::Arc<xor_all::Tree>",
        "std::ptr::NonNull<alloc::sync::ArcInner<xor_all::Tree>>",
        "alloc::sync::ArcInner<xor_all::Tree>",
    ];
    let edges = vec![vec![1], vec![2], vec![3], vec![0]];
    let nodes: Vec<usize> = (0..4).collect();
    assert_eq!(cut_labels(&edges, &names, &nodes), vec!["xor_all::Tree".to_string()]);
}

/// THE MEASURED DEFECT (2026-09-13). A type in a MODULE ties a std wrapper on
/// segment count, and `"alloc" < "syn"` then cuts the wrapper. With the
/// wrapper bit the cut lands on the wrapped enum; with the old static key
/// alone it demonstrably does not.
#[test]
fn greedy_fvs_cuts_the_wrapped_type_not_its_std_wrapper() {
    let names = [
        "syn::expr::Expr",
        "alloc::boxed::Box<syn::expr::Expr>",
        "core::ptr::unique::Unique<syn::expr::Expr>",
        "core::ptr::non_null::NonNull<syn::expr::Expr>",
    ];
    let edges = vec![vec![1], vec![2], vec![3], vec![0]];
    let nodes: Vec<usize> = (0..4).collect();
    assert_eq!(cut_labels(&edges, &names, &nodes), vec!["syn::expr::Expr".to_string()]);

    // The control: the pre-fix key really does pick `Box<Expr>`.
    let old =
        greedy_feedback_vertex_set(&edges, &mut |node, _| (false, test_static_key(names[node])));
    assert_eq!(old, vec![1], "the (segments, path) key alone must still cut the wrapper");
}

/// The same defect through a USER wrapper: the crate is not what makes a
/// wrapper the wrong cut, its argument is.
#[test]
fn greedy_fvs_cuts_the_wrapped_type_not_a_user_wrapper() {
    let names = ["k::expr::Expr", "k::MyBox<k::expr::Expr>"];
    let edges = vec![vec![1], vec![0]];
    let nodes: Vec<usize> = (0..2).collect();
    assert_eq!(cut_labels(&edges, &names, &nodes), vec!["k::expr::Expr".to_string()]);
}

/// An instantiation whose arguments are OFF the cycle is not a wrapper of
/// anything on it, so `Foo<u8>` still outranks `Box<Foo<u8>>`.
#[test]
fn greedy_fvs_keeps_an_off_cycle_instantiation_ahead_of_its_wrapper() {
    let names = ["k::Foo<u8>", "alloc::boxed::Box<k::Foo<u8>>"];
    let edges = vec![vec![1], vec![0]];
    let nodes: Vec<usize> = (0..2).collect();
    assert_eq!(cut_labels(&edges, &names, &nodes), vec!["k::Foo<u8>".to_string()]);
}

/// The wrapper bit is a function of the CURRENT component, and the greedy
/// loop must ask again after every cut. `A -> Z<A> -> B<Z<A>> -> A`, plus
/// `B <-> Z`: round one cuts `A` (the only non-wrapper). In round two `Z<A>`
/// no longer wraps a member (`A` is gone) while `B<Z<A>>` still does, so `Z`
/// must be cut — a STALE bit from round one would rank both as wrappers and
/// fall through to the path order, which picks `B`.
#[test]
fn greedy_fvs_recomputes_the_wrapper_bit_after_each_cut() {
    let names = ["k::A", "k::Z<k::A>", "k::B<k::Z<k::A>>"];
    let edges = vec![vec![1], vec![2], vec![0, 1]];
    let nodes: Vec<usize> = (0..3).collect();
    assert_eq!(
        cut_labels(&edges, &names, &nodes),
        vec!["k::A".to_string(), "k::Z<k::A>".to_string()],
    );
}

/// THE root-independence property. Every root's discovery finds a
/// successor-closed subset of the global graph, in its own index order; the
/// cut it computes must be the global cut restricted to that subset. If this
/// fails, one rustc type still reaches the dump as two different unrollings —
/// the defect RC-1 exists to remove.
#[test]
fn greedy_fvs_is_root_independent() {
    // Two independent cycles plus an entry node that reaches both, plus a
    // second entry that reaches only one of them, plus a nested cycle so the
    // greedy loop has to iterate.
    //   0 entry_both → 1, 5
    //   1 a::Alpha ↔ 2 zzz::AlphaBox        (cycle A)
    //   3 entry_alpha → 1
    //   5 b::Beta → 6 zzz::BetaMid → 7 zzz::BetaTail → 5, and 6 → 6 (nested)
    // Two of the cycle members are WRAPPERS of another member, so the
    // component-dependent bit of the key is exercised by this fixture too.
    let names = [
        "e::EntryBoth",
        "a::Alpha",
        "zzz::AlphaBox<a::Alpha>",
        "e::EntryAlpha",
        "e::EntryBeta",
        "b::Beta",
        "zzz::BetaMid<b::Beta>",
        "zzz::BetaTail",
    ];
    let edges: Vec<Vec<usize>> = vec![
        vec![1, 5], // 0
        vec![2],    // 1
        vec![1],    // 2
        vec![1],    // 3
        vec![5],    // 4
        vec![6],    // 5
        vec![7, 6], // 6
        vec![5],    // 7
    ];

    let all: Vec<usize> = (0..edges.len()).collect();
    let global = cut_labels(&edges, &names, &all);
    assert!(!global.is_empty(), "the fixture must actually contain cycles");

    for root in 0..edges.len() {
        let nodes = reachable_from(&edges, &[root]);
        let reachable_names: Vec<String> = nodes.iter().map(|n| names[*n].to_string()).collect();
        let expected: Vec<String> =
            global.iter().filter(|name| reachable_names.contains(name)).cloned().collect();

        // Discovery order is whatever order the walk happened to meet the
        // nodes in. Try several, including the reverse, to prove the pick is
        // decided by the key and never by an index.
        let mut orders = vec![nodes.clone()];
        let mut reversed = nodes.clone();
        reversed.reverse();
        orders.push(reversed);
        let mut rotated = nodes.clone();
        rotated.rotate_left(nodes.len() / 2);
        orders.push(rotated);

        for order in orders {
            let sub = induced_subgraph(&edges, &order);
            let actual = cut_labels(&sub, &names, &order);
            assert_eq!(
                actual, expected,
                "root {} ({}) with discovery order {:?} computed a different cut set",
                root, names[root], order
            );
        }
    }
}

/// The merge hazard the identity-bearing marker exists to close. A cut point
/// is emitted with NO structure, so its name is the only thing that separates
/// two instantiations of one generic ADT. With the generics-erased def path
/// (the first draft of RC-1) `Foo<u8>` and `Foo<i32>` collapse to one marker
/// and the consumer's structural comparator reports two genuinely different
/// types as EQUAL — strictly worse than the non-canonicity it was fixing,
/// because that direction fails OPEN.
#[test]
fn canonical_cut_marker_must_carry_the_instantiation() {
    let erased_u8 = recursive_datatype_ref("krate::Foo");
    let erased_i32 = recursive_datatype_ref("krate::Foo");
    assert!(
        erased_u8.eq_ignoring_disc_index_safe(&erased_i32),
        "the erased-name draft really does merge the two instantiations"
    );

    let instantiated_u8 = recursive_datatype_ref("krate::Foo<u8>");
    let instantiated_i32 = recursive_datatype_ref("krate::Foo<i32>");
    assert!(
        !instantiated_u8.eq_ignoring_disc_index_safe(&instantiated_i32),
        "distinct instantiations of one recursive ADT must not compare equal"
    );

    // …and a cut point with no generic arguments keeps the EXACT legacy
    // marker, so the Lever A `Level`/`Expr`/`ExprKind` cluster and `Tree` are
    // byte-identical to pre-RC-1.
    assert!(
        recursive_datatype_ref("clean_kernel::level::Level")
            .eq_ignoring_disc_index_safe(&recursive_datatype_ref("clean_kernel::level::Level"))
    );
}

/// An ordinary (acyclic) lowering must keep using the memo, so
/// `TyLoweringCtx` starts with an empty cut set — and with NO cut-point
/// expansion pending, since `expand_cut_point` is set only by
/// `cut_point_definition` and a walk that started with one set would emit a
/// definition where a marker belongs.
#[test]
fn ty_lowering_context_starts_with_an_empty_canonical_cut() {
    let ctx = TyLoweringCtx::default();
    assert!(ctx.canonical_cut.is_empty());
    assert!(ctx.expand_cut_point.is_none());
    // …and NOT in by-name-children mode, which only a definition sub-context
    // enters: an ordinary walk over an acyclic type must expand every
    // nominal field exactly as before that mode existed.
    assert!(!ctx.by_name_nominal_children);
}

/// SAME-NAME CROSS-CRATE PIN. Two crates that share a name render one path
/// for two types; a by-name marker is nothing but its name; so without the
/// stamp the two markers merge (fail-OPEN under `ty_eq`) and their two
/// definitions collide in the table. The stamp separates them, and only
/// them: an unambiguous name keeps the bare path byte-for-byte.
#[test]
fn by_name_marker_name_separates_same_named_crates() {
    let path = || "syn::expr::Expr".to_string();
    // Two external crates both named `syn`, distinct StableCrateIds.
    let a = by_name_marker_name(path(), 0x1111, false, false, false, true);
    let b = by_name_marker_name(path(), 0x2222, false, false, false, true);
    assert_ne!(a, b, "two same-named crates must not mint one marker name");
    assert!(
        recursive_datatype_ref(&a).eq_ignoring_disc_index_safe(&recursive_datatype_ref(&a))
            && !recursive_datatype_ref(&a).eq_ignoring_disc_index_safe(&recursive_datatype_ref(&b)),
        "the markers themselves must compare unequal",
    );
    // Each stamped name still names its own crate, so the definition filed
    // under it (`rename_definition`) is found by exactly that marker.
    let mut defs = trust_types::DatatypeDefs::new();
    let def = |name: &str| {
        rename_definition(
            TrustTy::Datatype {
                name: "syn::expr::Expr".into(),
                variants: vec![("Lit".to_string(), vec![])],
            },
            name,
        )
    };
    assert!(trust_types::insert_datatype_def(&mut defs, def(&a)));
    assert!(trust_types::insert_datatype_def(&mut defs, def(&b)));
    assert!(trust_types::datatype_marker_definition(&defs, &recursive_datatype_ref(&a)).is_some());
    assert!(trust_types::datatype_marker_definition(&defs, &recursive_datatype_ref(&b)).is_some());
    assert!(
        trust_types::datatype_marker_definition(&defs, &recursive_datatype_ref(&path())).is_none(),
        "the bare, unstamped name must resolve to NEITHER crate's definition",
    );

    // An UNAMBIGUOUS external crate: the bare path, byte-identical to the
    // legacy marker, so every ordinary compilation is untouched.
    assert_eq!(by_name_marker_name(path(), 0x1111, false, false, false, false), path());
    // The local crate is never ambiguous, whoever else wears its name.
    assert_eq!(by_name_marker_name(path(), 0x1111, true, false, false, true), path());
    // The impersonation half of the rule still applies, and composes
    // idempotently with a path the renderer already stamped.
    let impersonator =
        by_name_marker_name("std::sync::Arc".into(), 0x3333, false, true, false, false);
    assert!(impersonator.starts_with(trust_types::TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX));
    assert_eq!(
        by_name_marker_name(impersonator.clone(), 0x3333, false, true, false, true),
        impersonator,
    );
}

/// R0: the definition table's KEY/VALUE agreement, at the producer end.
///
/// `canonical_cut_ref` keys a generic cut point by its INSTANTIATED def path
/// while `lower_enum_adt` / `lower_adt_as_datatype` name the definition they
/// build with the ERASED one. `rename_definition` is what reconciles them;
/// without it `trust_types::insert_datatype_def` would file `Foo<u8>`'s
/// definition under `k::Foo` — colliding with `Foo<i32>`'s — and
/// `trust_types::datatype_definition` would refuse to serve it under the key
/// the marker actually carries.
#[test]
fn a_recorded_definition_is_renamed_to_the_key_its_marker_carries() {
    let variants =
        vec![("Mk".to_string(), vec![("0".to_string(), TrustTy::Int { width: 8, signed: false })])];
    let erased = TrustTy::Datatype { name: "k::Foo".into(), variants: variants.clone() };

    // A generic cut point: the definition is restated under the instantiated
    // key, so it agrees with the marker `canonical_cut_ref` emits.
    let renamed = rename_definition(erased.clone(), "k::Foo<u8>");
    assert_eq!(trust_types::definitional_datatype_name(&renamed), Some("k::Foo<u8>"),);
    let mut defs = trust_types::DatatypeDefs::new();
    assert!(trust_types::insert_datatype_def(&mut defs, renamed));
    assert!(
        trust_types::datatype_marker_definition(&defs, &recursive_datatype_ref("k::Foo<u8>"))
            .is_some(),
        "the marker's own name must find its definition",
    );
    // …and the OTHER instantiation, which is a different cut point, does not
    // pick it up — nor does the generics-erased name `compact_oversized_field`
    // would spell.
    for other in ["k::Foo<i32>", "k::Foo"] {
        assert!(
            trust_types::datatype_marker_definition(&defs, &recursive_datatype_ref(other))
                .is_none(),
            "`{other}` must not resolve through `k::Foo<u8>`'s entry",
        );
    }

    // A NON-generic cut point keeps the exact erased name: the rename is the
    // identity, so nothing in the Lever A `Level`/`Expr`/`ExprKind` cluster
    // moves.
    assert_eq!(rename_definition(erased.clone(), "k::Foo"), erased);
}

/// R0: `compact_oversized_field` must stay UNRESOLVABLE, and the mechanism is
/// WRITE AUTHORITY, not the shape of the marker.
///
/// For a non-generic type the three producers of `Ty::Datatype { name,
/// variants: [] }` emit byte-identical markers, so no consumer can tell them
/// apart by inspection. What separates them is that only
/// `record_cut_definition` ever writes an entry: a compacted field's marker,
/// and the `__trust_compacted_aggregate` fallback, therefore resolve to
/// nothing and every consumer declines on them exactly as before the table
/// existed.
#[test]
fn a_compacted_field_marker_is_never_resolvable_as_a_cut_point() {
    // A big nested aggregate compacts to a marker naming the ADT it replaced…
    let big = TrustTy::Adt {
        name: "k::Big".into(),
        fields: vec![("0".into(), TrustTy::Int { width: 8, signed: false })].into(),
        variants: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        // Not a bignum/std-map: the unauthenticated (fail-closed) default.
        arbitrary_precision: None,
        validity_wrapper: None,
        layout: None,
        enum_layout: None,
        adt_kind: None,
    };
    let compacted = compact_oversized_field(&big);
    assert_eq!(compacted, recursive_datatype_ref("k::Big"));
    // …and to the fallback name when the field is not a named aggregate.
    assert_eq!(
        compact_oversized_field(&TrustTy::Tuple(vec![TrustTy::Bool])),
        recursive_datatype_ref("__trust_compacted_aggregate"),
    );

    // A table carrying a DIFFERENT cut point resolves neither of them. This is
    // the fail-open the withdrawn by-name body search opened: a compacted
    // `Big<u8>` field binding to a declared `Big<i32>`.
    let mut defs = trust_types::DatatypeDefs::new();
    assert!(trust_types::insert_datatype_def(
        &mut defs,
        rename_definition(
            TrustTy::Datatype {
                name: "k::Big".into(),
                variants: vec![(
                    "Mk".to_string(),
                    vec![("0".to_string(), TrustTy::Int { width: 32, signed: true })],
                )],
            },
            "k::Big<i32>",
        ),
    ));
    for marker in [&compacted, &recursive_datatype_ref("__trust_compacted_aggregate")] {
        assert!(
            trust_types::datatype_marker_definition(&defs, marker).is_none(),
            "a compacted marker must resolve to nothing: it is a SIZE BOUND, \
             not a back-edge, and binding it would be the withdrawn fail-open",
        );
    }
}
