// trust-mir-extract/ty_convert.rs: Convert rustc Ty to trust-types Ty
//
// Maps rustc's rich type system to our simplified verification types.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: enum-disc-full-native — `TagEncoding`/`Variants` classify an enum's
// discriminant layout. Same import path the compiler uses in
// `rustc_mir_transform/src/check_enums.rs:1` and `rustc_codegen_ssa`.
use rustc_abi::{TagEncoding, Variants};
use rustc_middle::ty::{self, TyCtxt, TyKind, TypeVisitableExt};
use trust_types::fx::FxHashMap;
use trust_types::{FnSig, Ty as TrustTy};

// verifier-perf: original budget restored. An earlier patch bumped
// nodes 4096 → 65536, but that interacted badly with the alias-normalize
// path — more types reached normalization, each invoking the trait
// solver, which then exceeded rustc's default 128 recursion limit while
// compiling crates like `typenum` that have deeply nested `UInt<…>`
// bounds. Revisit with a separate "skip normalize when bound likely to
// recurse" heuristic before raising again.
const MAX_TYPE_LOWERING_DEPTH: usize = 64;
const MAX_TYPE_LOWERING_NODES: usize = 4096;

// ── verifier-perf: PRODUCED-tree-size budget for type lowering ──────────────
//
// `remaining_nodes` (above) bounds the COUNT of distinct `convert_ty_inner`
// CALLS, but the memoization cache returns a `cached.clone()` WITHOUT charging,
// and `lower_enum_adt` DUPLICATES every variant field into the flattened
// `fields` view (`field_ty.clone()`) on top of the per-variant lists. So the
// SIZE of the PRODUCED `TrustTy` tree is not bounded by `remaining_nodes`: the
// kernel's mutually-recursive `Expr`/`ExprKind`/`Name` enums (each lowered once,
// then cloned into many parents) assemble a ~464 MB `Ty::Adt` tree, driving RSS
// to tens of GB and OOM-killing the verifier DURING EXTRACTION — upstream of all
// VC-gen / bundle bounds. This is the actual `build_ind_app`/`ProofCert::clone`
// stall: it is in `trust_mir_extract::ty_convert`, not in trust-vcgen.
//
// FIX: meter the cumulative node count of every PRODUCED subtree (charged for
// freshly-lowered trees AND for cache-hit clones, since the clone materializes
// the same memory). Once the cumulative produced size for ONE function's type
// lowering crosses the budget, every subsequent lowering returns the cheap
// fail-closed recursive-ADT `Unsupported` marker instead of assembling more fat
// tree. The marker is the SAME `Ty::Unsupported { kind: "TyKind::Adt", detail:
// "recursive…" }` shape this module already produces for recursive ADTs, so a
// degraded function is byte-identical to the pre-existing recursive-ADT path.
//
// SOUNDNESS (paramount): DROP-ONLY. A function whose types fit the budget is
// lowered byte-identically to baseline. A function over the budget has its fat
// types replaced by the fail-closed `Unsupported` marker, which carries NO
// modeled SMT sort — so every panic-able USE of such a value still fails closed
// at its use site (`place_sort` stays `None`), and no arithmetic/bounds/divzero
// VC is emitted for it. It can only LOSE proofs for that one function, never
// manufacture a false PROVE and never a guaranteed-violation. Overridable via
// The bound is a deterministic production constant so extraction cannot vary
// with process-global environment state.
//
// DEFAULT sizing: empirically, clean-kernel's recursive `Expr`/`ExprKind`/`Name`
// cluster drives peak verifier RSS ROUGHLY linearly in this budget — measured ~7.8
// GB at 5_000 (COMPLETES) vs ~32 GB (OOM) at 200_000. 8_000 keeps the peak in a
// ~10-13 GB band that completes with comfortable margin on a 48 GB host while
// retaining more datatype-field precision than 5_000. An ordinary function's whole
// declared-type set is well under this (a few hundred nodes), so ONLY the
// pathological recursive-enum cluster is ever degraded.
const MAX_TYPE_LOWERING_PRODUCED_NODES: usize = 8_000;

/// Total structural-node count of a produced `TrustTy`, short-circuited at `cap`
/// so a huge tree costs O(cap), not O(size). This is the real memory cost the
/// caller pays to retain/clone the lowered type.
fn produced_node_count(ty: &TrustTy, cap: usize) -> usize {
    fn go(ty: &TrustTy, cap: usize, acc: &mut usize) {
        if *acc >= cap {
            return;
        }
        *acc += 1;
        match ty {
            TrustTy::Ref { inner, .. } => go(inner, cap, acc),
            TrustTy::RawPtr { pointee, .. } => go(pointee, cap, acc),
            TrustTy::Slice { elem }
            | TrustTy::Array { elem, .. }
            | TrustTy::SymArray { elem, .. } => go(elem, cap, acc),
            TrustTy::Tuple(tys) => tys.iter().for_each(|t| go(t, cap, acc)),
            TrustTy::Adt { fields, variants, .. } => {
                for (_, t) in fields {
                    go(t, cap, acc);
                }
                for v in variants {
                    for (_, t) in &v.fields {
                        go(t, cap, acc);
                    }
                }
            }
            // Lever A: charge a datatype's variant-field nodes so the budget
            // still bounds a `Ty::Datatype` tree (a by-name ref is empty and
            // costs just the `+1` leaf above).
            TrustTy::Datatype { variants, .. } => {
                for (_, fs) in variants {
                    for (_, t) in fs {
                        go(t, cap, acc);
                    }
                }
            }
            TrustTy::Closure { upvars, .. } | TrustTy::Coroutine { upvars, .. } => {
                upvars.iter().for_each(|t| go(t, cap, acc));
            }
            _ => {}
        }
    }
    let mut acc = 0;
    go(ty, cap, &mut acc);
    acc
}

/// Deterministic produced-tree-size budget. Proof extraction must not depend on
/// ambient process environment: crossing the bound changes a type to an
/// explicit fail-closed marker and therefore changes the obligation inventory.
fn produced_node_budget() -> usize {
    MAX_TYPE_LOWERING_PRODUCED_NODES
}

/// The cheap fail-closed leaf returned once the produced-node budget is spent —
/// the SAME recursive-ADT `Unsupported` marker this module already produces for
/// genuinely recursive ADTs (load-bearing `detail.starts_with("recursive")`).
fn produced_budget_degraded_leaf() -> TrustTy {
    TrustTy::Unsupported {
        kind: "TyKind::Adt".to_string(),
        detail: "recursive ADT (degraded: type lowering exceeded produced-node budget)".to_string(),
    }
}

/// A BY-NAME recursive-datatype reference (Lever A): an empty-`variants`
/// `Ty::Datatype` whose only content is the referent's name. Emitted at a
/// recursive field position so the back-edge has a MODELED SMT sort
/// (`Sort::Datatype { name, constructors: [] }` resolves to the definitional
/// occurrence's declared datatype at declare time) — instead of the opaque
/// `Unsupported` that forced every projection/match through a recursive ADT to
/// Unknown. The defining occurrence (the outer, fully-lowered type) carries the
/// full structure. SOUNDNESS: a datatype reference introduces NO facts; it is a
/// sort marker only (see `Ty::Datatype`'s doc).
fn recursive_datatype_ref(name: &str) -> TrustTy {
    TrustTy::Datatype { name: name.to_string(), variants: Vec::new() }
}

// ─── RC-1: CANONICAL recursive-type lowering ────────────────────────────────
//
// THE DEFECT. Every `convert_ty` call starts with an EMPTY `adt_stack`, and the
// back-edge guards (`lower_adt_as_datatype`, `lower_enum_adt`, the struct arm)
// cut at the first re-entry of a type ALREADY ON THAT PATH. The cut point is
// therefore a property of the ROOT the type was reached from, not of the type.
// One rustc type reaches the dump as two different finite unrollings. Measured
// in `trust-clean/fixtures/structural-fold-corpus/xor_all.json`:
//
//     _1 : &Tree        →  Tree(full) → Arc(full) → …ArcInner.data = BY-NAME Tree
//     _6 : &Arc<Tree>   →  Arc(full)  → …ArcInner.data = Tree(full) → BY-NAME Arc
//
// so `(*_1 as Two).0`'s field type and `_6`'s declared type are the SAME rustc
// type at two different cut depths. `trust_clean::assignment_types::ty_eq` is
// strict structural equality, so `all_assignments_match` rejects the body and
// every lane gated on it (`prove::diagnose_fully_faithful_gate`, the fold
// recognizers) declines before it runs. The defect is in this producer; the
// consumer is right to be strict.
//
// THE CANONICAL RULE. Cut at a deterministic FEEDBACK VERTEX SET of the type's
// own reachability graph, exempting only the root of the current `convert_ty`
// call:
//
//   1. Discover the ADT reachability graph from the root: nodes are interned
//      `ty::Ty<'tcx>` (so `Vec<u8>` and `Vec<i32>` are DISTINCT nodes — the cut
//      set is never keyed on a generics-erased name), edges are field types
//      peeled through `&`/`*`/`[T]`/`[T; N]`/tuple/closure-upvar.
//   2. Compute its SCCs and the deterministic greedy feedback vertex set: while
//      a non-trivial SCC remains, delete its `canonical_cut_key`-least node.
//   3. Lower normally, but emit the by-name reference at every occurrence of a
//      cut-set member that is not this call's root.
//
// WHY THE RESULT IS UNIQUE (a function of the type alone). Two types in one SCC
// reach exactly the same node set (each reaches the other), so they discover the
// SAME graph and hence the same FVS. A type OUTSIDE that SCC discovers a subgraph
// that contains each SCC either wholly or not at all — and the greedy FVS is
// decided independently inside each SCC — so the FVS it computes is exactly the
// global FVS restricted to what it can reach. Therefore, for any type `C` reached
// below any root, the subtree emitted for `C` is byte-identical to the tree
// emitted for `C` as a root, UNLESS `C` is itself in the cut set. The residual is
// irreducible: a finite representation of a cyclic type must cut each cycle at
// least once. What changes is that the cut is now at a FIXED, canonically chosen
// type instead of wherever the root happened to enter the cycle.
//
// WHY IT CANNOT MERGE TWO GENUINELY DIFFERENT TYPES. The only lossy element is
// the by-name marker. The first draft of this change named the marker with the
// GENERICS-ERASED def path (`recursive_datatype_ref(&safe_def_path_str(..))`,
// the same string the legacy back-edge guards use) and argued that this could
// not merge anything the status quo did not already merge. THAT ARGUMENT WAS
// WRONG, and the counterexample is exactly the one to worry about:
//
//     enum Foo<T> { Nil, Cons(T, Box<Foo<T>>) }
//     struct Pair { a: Foo<u8>, b: Foo<i32> }
//
// `Foo<u8>` and `Foo<i32>` are two DISTINCT interned types, each on its own
// cycle, so BOTH are cut points. Lowering `Pair`, each field is a non-root
// occurrence of a cut point, so with an erased marker BOTH fields emit
// `Datatype { name: "…::Foo", variants: [] }` and `Pair`'s two genuinely
// different fields compare EQUAL under `assignment_types::ty_eq`. The status quo
// does NOT do this: it expands each field one level (`__v1_0: u8` vs
// `__v1_1: i32`) before taking its back-edge, so the two stay distinguishable.
// That is a fail-OPEN regression — the original defect only made `ty_eq` decline
// (fail-closed), which is strictly the safer direction. An over-merging
// canonicalization is worse than the bug it fixes.
//
// So the marker emitted at a cut point is IDENTITY-BEARING: `canonical_cut_ref`
// names it with the CONCRETE instantiated path (`…::Foo<u8>` vs `…::Foo<i32>`)
// whenever the type has non-lifetime generic arguments, and with the plain
// erased path when it has none. A non-generic cut point (`Tree`, `Level`,
// `Expr`, `ExprKind` — every type the Lever A datatype lowering names) therefore
// keeps BYTE-IDENTICAL markers, so nothing that resolves a by-name datatype
// reference against a defining occurrence (`Sort::from_ty`'s
// `datatype_sort_from_ty`) changes at all; and a generic cut point gets one
// distinct sort name per instantiation, which is strictly MORE discriminating
// than both the status quo and the erased-marker draft.
//
// This is also why option (a) — "by-name for EVERY occurrence of a recursive
// ADT" — was rejected: even with instantiated names it would drop the structure
// of every nominal position, and the whole point of the root exemption is that
// the defining occurrence still carries the real variant list.
//
// FAIL-SAFE. Discovery is bounded by `MAX_CANONICAL_CUT_NODES`. If the bound is
// hit — the EXPANDING-generic recursion (`List<Box<List<T>>>`), whose node set is
// genuinely infinite and which `is_expanding_recursive_adt` deliberately leaves
// `Unsupported` — the cut set is EMPTY and lowering is byte-identical to today's.
// An empty cut set is also what a non-recursive type gets, so the overwhelming
// majority of types are untouched.
//
// KNOWN RESIDUALS (recorded, not hidden — none of them can merge two types, they
// can only cost canonicity, whose failure mode is a fail-closed `ty_eq` decline):
//
//   R1. The budget fallback is root-relative: a root whose graph exceeds
//       `MAX_CANONICAL_CUT_NODES` gets an EMPTY cut set and therefore the legacy
//       root-relative lowering, while a smaller root reaching the same cycle
//       still cuts canonically.
//   R2. `nominal_frontier` does not peel `TyKind::Alias`, but `convert_ty_in_env`
//       DOES normalize opaque aliases before descending. A cycle that closes only
//       through an alias is invisible to discovery, so it is cut by the legacy
//       `adt_stack` guard instead.
//   R3. The `cap_fields` compaction gates in the struct arm and `lower_enum_adt`
//       are still keyed on `!adt_stack.is_empty()`, i.e. still root-relative.
//       RC-1 shrinks the subtrees they see (a cut point is one node) but does not
//       remove that root dependence.
//   R4. `canonical_cut_key` is total only up to the injectivity of
//       `(def-path depth, instantiated path, CrateNum, DefIndex)`. Two distinct
//       interned `Ty` sharing all four would tie, and the tie is then broken by
//       discovery order, which is root-relative. MIR types reach this code with
//       erased regions, so lifetimes cannot produce such a pair; it would take a
//       printer collision between two different concrete argument lists on one
//       `DefId`.

/// Node bound for the canonical-cut discovery walk. Reaching it yields an EMPTY
/// cut set (i.e. exactly today's root-relative lowering) — never a partial cut
/// set, which would not be canonical.
const MAX_CANONICAL_CUT_NODES: usize = MAX_TYPE_LOWERING_NODES;

/// The ordering key the greedy feedback vertex set picks its cut points with.
/// EVERY component must be a function of the TYPE ALONE — anything derived from
/// the walk (discovery index, insertion order, the root) would make the cut set
/// root-relative again, which is the very defect RC-1 exists to remove.
type CanonicalCutKey = (usize, String, u32, u32);

/// The deterministic total order the greedy feedback vertex set picks its cut
/// points with: the SHALLOWEST def path in the cycle first (so a cycle through
/// `Tree`/`std::sync::Arc`/`std::ptr::NonNull`/`alloc::sync::ArcInner` is cut at
/// `Tree`, the type the cycle is ABOUT, not at an `std` container internal),
/// then the fully-instantiated path, then the type's `DefId` (`CrateNum`,
/// `DefIndex`) so two distinct types that happen to PRINT the same still order
/// deterministically rather than falling back on discovery order. See residual
/// R4 on the block comment above for what is left.
fn canonical_cut_key<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> CanonicalCutKey {
    let TyKind::Adt(def, args) = ty.kind() else {
        return (usize::MAX, String::new(), u32::MAX, u32::MAX);
    };
    let did = def.did();
    let erased = crate::safe_def_path_str(tcx, did);
    let segments = erased.matches("::").count();
    (
        segments,
        crate::safe_def_path_str_with_args(tcx, did, *args),
        did.krate.as_u32(),
        did.index.as_u32(),
    )
}

/// The by-name reference a CUT POINT lowers to.
///
/// IDENTITY-BEARING, and that is the whole point (see "WHY IT CANNOT MERGE TWO
/// GENUINELY DIFFERENT TYPES" above): a cut point is emitted with no structure at
/// all, so its name is the ONLY thing distinguishing it from another instantiation
/// of the same generic ADT. `Foo<u8>` and `Foo<i32>` are two distinct cut points
/// and must not collapse to one marker.
///
/// A type with no non-lifetime generic arguments keeps the EXACT erased def path
/// the legacy back-edge guards emit (`recursive_datatype_ref(&safe_def_path_str)`),
/// so every marker in the Lever A `Level`/`Expr`/`ExprKind` cluster — and `Tree`
/// in the structural-fold corpus — is byte-identical to today's. Only a generic
/// cut point gains the `<args>` suffix, and there the alternative is a merge.
fn canonical_cut_ref<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> TrustTy {
    let TyKind::Adt(def, args) = ty.kind() else {
        // Unreachable: `nominal_frontier` only ever admits `TyKind::Adt` nodes,
        // so only an ADT can be in the cut set. Fail closed rather than invent a
        // name if that ever stops holding.
        return unsupported_ty("TyKind", "canonical cut point was not a nominal ADT");
    };
    let did = def.did();
    let erased = crate::safe_def_path_str(tcx, did);
    let has_non_lifetime_args = args.types().next().is_some() || args.consts().next().is_some();
    if has_non_lifetime_args {
        recursive_datatype_ref(&crate::safe_def_path_str_with_args(tcx, did, *args))
    } else {
        recursive_datatype_ref(&erased)
    }
}

/// Collect the FIRST nominal ADT on every path below `ty`, peeling exactly the
/// type constructors the lowering itself descends through. This is the edge
/// relation of the reachability graph; it is a SUPERSET of the relation the
/// datatype lowering uses (`datatype_child_field_ty` cuts at every nominal child
/// unconditionally), so a feedback vertex set computed here breaks every cycle
/// the lowering can actually walk.
fn nominal_frontier<'tcx>(
    ty: ty::Ty<'tcx>,
    depth: usize,
    out: &mut Vec<ty::Ty<'tcx>>,
) {
    if depth >= MAX_TYPE_LOWERING_DEPTH {
        return;
    }
    match ty.kind() {
        TyKind::Adt(..) => out.push(ty),
        TyKind::Ref(_, inner, _) => nominal_frontier(*inner, depth + 1, out),
        TyKind::RawPtr(pointee, _) => nominal_frontier(*pointee, depth + 1, out),
        TyKind::Slice(elem) => nominal_frontier(*elem, depth + 1, out),
        TyKind::Array(elem, _) => nominal_frontier(*elem, depth + 1, out),
        TyKind::Tuple(fields) => {
            for field in fields.iter() {
                nominal_frontier(field, depth + 1, out);
            }
        }
        TyKind::Closure(_, args) => {
            for upvar in args.as_closure().upvar_tys().iter() {
                nominal_frontier(upvar, depth + 1, out);
            }
        }
        TyKind::Coroutine(_, args) => {
            for upvar in args.as_coroutine().upvar_tys().iter() {
                nominal_frontier(upvar, depth + 1, out);
            }
        }
        _ => {}
    }
}

/// The nominal ADTs directly reachable from `ty`'s own fields (every variant of
/// an enum, `all_fields` of a struct/union).
fn adt_field_successors<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Vec<ty::Ty<'tcx>> {
    let TyKind::Adt(adt_def, args) = ty.kind() else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for variant in adt_def.variants().iter() {
        for field in variant.fields.iter() {
            nominal_frontier(field.ty(tcx, *args).skip_normalization(), 0, &mut out);
        }
    }
    out
}

/// The canonical feedback vertex set of the ADT reachability graph rooted at
/// `root`. Empty when the graph is acyclic or when discovery hit its bound.
fn canonical_cut_set<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: ty::Ty<'tcx>,
) -> trust_types::fx::FxHashSet<ty::Ty<'tcx>> {
    // ── discovery (bounded) ────────────────────────────────────────────────
    let mut order: Vec<ty::Ty<'tcx>> = Vec::new();
    let mut index: FxHashMap<ty::Ty<'tcx>, usize> = FxHashMap::default();
    let mut seeds = Vec::new();
    nominal_frontier(root, 0, &mut seeds);
    for seed in seeds {
        if index.insert(seed, order.len()).is_none() {
            order.push(seed);
        }
    }
    let mut edges: Vec<Vec<usize>> = Vec::new();
    let mut head = 0usize;
    while head < order.len() {
        if order.len() > MAX_CANONICAL_CUT_NODES {
            return trust_types::fx::FxHashSet::default();
        }
        let node = order[head];
        let mut succ = Vec::new();
        for child in adt_field_successors(tcx, node) {
            let id = match index.get(&child) {
                Some(id) => *id,
                None => {
                    if order.len() > MAX_CANONICAL_CUT_NODES {
                        return trust_types::fx::FxHashSet::default();
                    }
                    let id = order.len();
                    index.insert(child, id);
                    order.push(child);
                    id
                }
            };
            if !succ.contains(&id) {
                succ.push(id);
            }
        }
        edges.push(succ);
        head += 1;
    }
    debug_assert_eq!(edges.len(), order.len());

    // ── deterministic greedy feedback vertex set ───────────────────────────
    // Keys are computed LAZILY. `canonical_cut_key` renders two rustc def paths
    // per node, and `canonical_cut_set` runs once per `convert_ty` call — i.e.
    // once per local, per place, per body. The overwhelmingly common graph is
    // ACYCLIC, and an acyclic graph needs no key at all: the first SCC pass finds
    // no non-trivial component and the loop exits before any key is rendered.
    let mut keys: Vec<Option<CanonicalCutKey>> = vec![None; order.len()];
    let mut cut: trust_types::fx::FxHashSet<ty::Ty<'tcx>> = trust_types::fx::FxHashSet::default();
    for pick in greedy_feedback_vertex_set(&edges, &mut |node| {
        keys[node].get_or_insert_with(|| canonical_cut_key(tcx, order[node])).clone()
    }) {
        cut.insert(order[pick]);
    }
    cut
}

/// The deterministic greedy feedback vertex set of `edges`: while a non-trivial
/// strongly connected component remains, delete its `key_of`-least node.
///
/// Split out from `canonical_cut_set` — and taking no `TyCtxt` — because THIS is
/// the function root-independence rests on, and it is the part that can be tested
/// without a compiler session. The property it must have (see
/// `greedy_fvs_is_root_independent`) is:
///
///   for every successor-closed subset `S` of the nodes, and every re-indexing of
///   `S`, the cut computed on the induced subgraph equals the global cut ∩ `S`.
///
/// It holds because (i) a successor-closed subset contains each SCC wholly or not
/// at all, (ii) a path leaving an SCC never returns, so an SCC's internal SCC
/// structure after deletions depends only on its own induced subgraph, and (iii)
/// the pick is by `key_of` alone, never by node index or iteration order. Point
/// (iii) is why `key_of` must be a function of the underlying type only.
fn greedy_feedback_vertex_set(
    edges: &[Vec<usize>],
    key_of: &mut dyn FnMut(usize) -> CanonicalCutKey,
) -> Vec<usize> {
    let mut alive: Vec<bool> = vec![true; edges.len()];
    let mut cut: Vec<usize> = Vec::new();
    loop {
        let components = strongly_connected_components(edges, &alive);
        let mut progressed = false;
        for component in components {
            let self_loop = component.len() == 1 && edges[component[0]].contains(&component[0]);
            if component.len() < 2 && !self_loop {
                continue;
            }
            let mut best: Option<(usize, CanonicalCutKey)> = None;
            for node in component.iter().copied() {
                let key = key_of(node);
                let better = match &best {
                    None => true,
                    Some((_, best_key)) => key < *best_key,
                };
                if better {
                    best = Some((node, key));
                }
            }
            let Some((pick, _)) = best else { continue };
            alive[pick] = false;
            cut.push(pick);
            progressed = true;
        }
        if !progressed {
            break;
        }
    }
    cut
}

/// Tarjan SCCs of the subgraph induced on the `alive` nodes. Iterative, so a
/// deep type graph cannot overflow the extraction stack.
fn strongly_connected_components(edges: &[Vec<usize>], alive: &[bool]) -> Vec<Vec<usize>> {
    let n = edges.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut out: Vec<Vec<usize>> = Vec::new();
    let mut counter = 0usize;
    for start in 0..n {
        if !alive[start] || index[start] != usize::MAX {
            continue;
        }
        let mut work: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some((node, next)) = work.pop() {
            if next == 0 {
                index[node] = counter;
                low[node] = counter;
                counter += 1;
                stack.push(node);
                on_stack[node] = true;
            }
            let mut descended = false;
            let successors = &edges[node];
            for cursor in next..successors.len() {
                let child = successors[cursor];
                if !alive[child] {
                    continue;
                }
                if index[child] == usize::MAX {
                    work.push((node, cursor + 1));
                    work.push((child, 0));
                    descended = true;
                    break;
                } else if on_stack[child] {
                    low[node] = low[node].min(index[child]);
                }
            }
            if descended {
                continue;
            }
            if low[node] == index[node] {
                let mut component = Vec::new();
                while let Some(top) = stack.pop() {
                    on_stack[top] = false;
                    component.push(top);
                    if top == node {
                        break;
                    }
                }
                out.push(component);
            }
            if let Some((parent, _)) = work.last().copied() {
                low[parent] = low[parent].min(low[node]);
            }
        }
    }
    out
}

/// Maximum node count for a SINGLE flattened variant/struct-field subtree before
/// it is compacted (verifier-perf, Lever A). Small recursive enums and ordinary
/// scalar/pointer payloads stay well under it; the Arc/Atomic/UnsafeCell-laden
/// kernel `Expr`/`Level` pointer fields (the source of the thousands-of-nodes
/// blow-up that OOM-killed extraction / stalled `place_ty`) exceed it and
/// collapse to a by-name datatype reference, which keeps the enclosing type
/// MODELED (not bailed to `Unsupported`) so the Lever-A win lands.
const MAX_DATATYPE_FIELD_NODES: usize = 64;

/// Compact an oversized recursive-enum/struct field subtree to a small, modeled
/// placeholder. If the subtree is an aggregate carrying a name (an `Adt` or a
/// `Datatype`), preserve that name as a by-name `Ty::Datatype` reference (so the
/// sort stays a stable per-type datatype sort). A pointer/ref keeps its pointer
/// shape (its SMT sort is an integer address) and compacts the pointee. Otherwise
/// fall back to a generic opaque datatype reference. SOUNDNESS: the result is
/// always a MODELED, fact-free sort — never `Unsupported` (which would fail
/// closed) and never a fabricated constraint. An over-large field is a
/// pointer-wrapped aggregate whose SMT value is an opaque address/datatype const
/// anyway, so collapsing it loses no SOUND obligation (the scalar leaves that
/// matter — the `__tag` discriminant and small payloads — are under the cap and
/// keep full detail).
fn compact_oversized_field(ty: &TrustTy) -> TrustTy {
    match ty {
        TrustTy::Adt { name, .. } | TrustTy::Datatype { name, .. } => recursive_datatype_ref(name),
        TrustTy::Ref { mutable, inner } => {
            TrustTy::Ref { mutable: *mutable, inner: Box::new(compact_oversized_field(inner)) }
        }
        TrustTy::RawPtr { mutable, pointee } => TrustTy::RawPtr {
            mutable: *mutable,
            pointee: Box::new(compact_oversized_field(pointee)),
        },
        _ => recursive_datatype_ref("__trust_compacted_aggregate"),
    }
}

/// Count nodes in a lowered `Ty`, short-circuiting once `cap` is reached (so a
/// huge tree costs O(cap), not O(size)). Used only to decide the size-collapse in
/// `lower_enum_adt` / the recursive struct lowering.
fn ty_node_count(ty: &TrustTy, cap: usize) -> usize {
    fn go(ty: &TrustTy, cap: usize, acc: &mut usize) {
        if *acc >= cap {
            return;
        }
        *acc += 1;
        match ty {
            TrustTy::Ref { inner, .. } => go(inner, cap, acc),
            TrustTy::RawPtr { pointee, .. } => go(pointee, cap, acc),
            TrustTy::Slice { elem }
            | TrustTy::Array { elem, .. }
            | TrustTy::SymArray { elem, .. } => go(elem, cap, acc),
            TrustTy::Tuple(tys) => {
                for t in tys {
                    go(t, cap, acc);
                }
            }
            // A platform-internal std type can have a very large implementation tree.
            // Count it as ONE node (the `*acc += 1` at the top of `go`) and do NOT
            // descend, so a lock-bearing user aggregate (`Mutex<T>` inside a struct such
            // as `sink::Shared`) stays UNDER the field-compaction cap and remains fully
            // EXPANDED for the drop-glue walk — otherwise the aggregate collapses to an
            // opaque `Ty::Datatype` the classifier must decline. This is precision only:
            // the bridge now grants Drop authority to two exact pthread leaf paths and
            // fails closed on every other `std::sys` type. Undercounting only REDUCES
            // compaction (strictly more precision, never a fabricated fact); scoped to
            // `std::sys::` so the kernel `Expr`/`Level` pointer towers that motivated the
            // cap are untouched.
            TrustTy::Adt { name, .. } if name.starts_with("std::sys::") => {}
            TrustTy::Adt { fields, variants, .. } => {
                for (_, t) in fields {
                    go(t, cap, acc);
                }
                for v in variants {
                    for (_, t) in &v.fields {
                        go(t, cap, acc);
                    }
                }
            }
            TrustTy::Datatype { variants, .. } => {
                for (_, fs) in variants {
                    for (_, t) in fs {
                        go(t, cap, acc);
                    }
                }
            }
            TrustTy::Closure { upvars, .. } | TrustTy::Coroutine { upvars, .. } => {
                for t in upvars {
                    go(t, cap, acc);
                }
            }
            _ => {}
        }
    }
    let mut acc = 0;
    go(ty, cap, &mut acc);
    acc
}

struct TyLoweringCtx<'tcx> {
    depth: usize,
    remaining_nodes: usize,
    /// verifier-perf: cumulative count of PRODUCED `TrustTy` nodes materialized
    /// across THIS function's type lowering (fresh trees + cache-hit clones).
    /// Once it crosses `produced_budget`, lowering degrades to the fail-closed
    /// recursive-ADT marker. See `MAX_TYPE_LOWERING_PRODUCED_NODES`.
    produced_nodes: usize,
    /// Per-walk cached produced-node budget (read once at construction, so an env
    /// override is honored without re-parsing per node). `usize::MAX` disables.
    produced_budget: usize,
    adt_stack: Vec<ty::Ty<'tcx>>,
    /// RC-1 (canonical recursive-type lowering): the deterministic feedback
    /// vertex set of THIS walk's type-reachability graph. Every occurrence of a
    /// member that is not this walk's ROOT (`adt_stack.is_empty()`) lowers to
    /// the by-name reference, so one rustc type has exactly one representation
    /// regardless of which root it was reached from. Empty for an acyclic type
    /// and whenever discovery hit its bound — in both cases lowering is
    /// byte-identical to the pre-RC-1 behavior. See the block comment on
    /// `canonical_cut_set`.
    canonical_cut: trust_types::fx::FxHashSet<ty::Ty<'tcx>>,
    /// verifier-coverage: the `TypingEnv` in which alias
    /// normalization is attempted. `None` means "do not normalize
    /// aliases" — every non-`Free` alias stays `Unsupported` (the legacy
    /// behavior, preserved for the many `convert_ty` call sites that do
    /// not have a body's env in scope). `Some(env)` additionally enables
    /// the *narrow*, build-safe `AliasTyKind::Opaque` reveal documented on
    /// the `TyKind::Alias` arm. (`Free` aliases are expanded structurally
    /// regardless — they do not drive the trait solver.)
    typing_env: Option<ty::TypingEnv<'tcx>>,
    /// verifier-perf: memoization cache for already-lowered
    /// types in this walk. Stage2-rustc internals like `GlobalCtxt`
    /// reach the same nested `Arena<…>` / `Vec<…>` subtypes many times
    /// across the per-function MIR walk; without a cache, each visit
    /// repeats the entire subtree walk and decrements the node budget
    /// for each repeat — which is what caused the previous "node budget
    /// exceeded 4096" reports in otherwise-lowerable functions. The
    /// cache is per-`convert_ty` call (resets between functions), so it
    /// doesn't leak across compilations or carry state between MIR
    /// bodies. Keyed by the raw `Ty` pointer (rustc interns types, so
    /// equality is pointer-identity).
    cache: FxHashMap<ty::Ty<'tcx>, TrustTy>,
}

impl<'tcx> Default for TyLoweringCtx<'tcx> {
    fn default() -> Self {
        Self {
            depth: 0,
            remaining_nodes: MAX_TYPE_LOWERING_NODES,
            produced_nodes: 0,
            produced_budget: produced_node_budget(),
            adt_stack: Vec::new(),
            canonical_cut: trust_types::fx::FxHashSet::default(),
            typing_env: None,
            cache: FxHashMap::default(),
        }
    }
}

impl<'tcx> TyLoweringCtx<'tcx> {
    fn with_typing_env(typing_env: ty::TypingEnv<'tcx>) -> Self {
        Self { typing_env: Some(typing_env), ..Self::default() }
    }
}

/// verifier-coverage: ADT-argument nesting depth above which a
/// speculative alias normalization is likely to overflow rustc's trait
/// solver. Kept deliberately conservative (well below rustc's 128 limit)
/// — see the four documented `E0275` regressions on the `TyKind::Alias`
/// arm of `convert_ty_inner`.
pub(crate) const SAFE_NORMALIZE_ADT_DEPTH: usize = 4;

fn bounded_adt_arg_depth<Node, IsAdt, VisitChildren>(
    root: Node,
    cutoff: usize,
    node_budget: usize,
    mut is_adt: IsAdt,
    mut visit_children: VisitChildren,
) -> usize
where
    Node: Copy + Eq + std::hash::Hash,
    IsAdt: FnMut(Node) -> bool,
    VisitChildren: FnMut(Node, &mut dyn FnMut(Node) -> bool) -> bool,
{
    let mut remaining_nodes = node_budget;
    let mut maximum = 0;
    let mut greatest_depth_seen: FxHashMap<Node, usize> = FxHashMap::default();
    let mut worklist = vec![(root, 0usize)];

    while let Some((current, inherited_depth)) = worklist.pop() {
        if remaining_nodes == 0 {
            return cutoff;
        }
        remaining_nodes -= 1;

        let current_depth = inherited_depth + usize::from(is_adt(current));
        if current_depth >= cutoff {
            return cutoff;
        }
        if greatest_depth_seen.get(&current).is_some_and(|seen| *seen >= current_depth) {
            continue;
        }
        greatest_depth_seen.insert(current, current_depth);
        maximum = maximum.max(current_depth);

        let mut push = |child| {
            // Refuse before an attacker-shaped wide tuple/alias can grow the
            // pending set beyond the deterministic remaining work bound.
            if worklist.len() >= remaining_nodes {
                return false;
            }
            worklist.push((child, current_depth));
            true
        };
        if !visit_children(current, &mut push) {
            return cutoff;
        }
    }

    maximum
}

/// Compute the maximum ADT-argument nesting depth reachable from `ty`
/// without invoking the trait solver.
///
/// This is a pure structural walk over the already-interned `Ty<'tcx>`
/// graph: each `Adt` adds one to the depth, and we recurse into the
/// type-valued generic arguments. Other kinds (references, raw pointers,
/// slices, arrays, tuples, aliases) pass through to their contents
/// without contributing to the depth, because rustc's trait-solver
/// recursion is driven by ADT-argument nesting (e.g. `UInt<UInt<…>>`),
/// not by projection or borrow depth.
///
/// Used as a guard before calling `try_normalize_erasing_regions` on an
/// alias: aliases whose argument types nest ADTs more than
/// `SAFE_NORMALIZE_ADT_DEPTH` levels deep almost always overflow the
/// trait solver, so we leave them `Unsupported` rather than break the
/// build. See `docs/verifier-coverage-roadmap.md` §1.
pub(crate) fn adt_arg_depth<'tcx>(ty: ty::Ty<'tcx>) -> usize {
    // `Ty<'tcx>` is interned: a monomorphic type is a shared-subtree DAG (e.g.
    // `Result<T, T>`, nested `(Tn-1, Tn-1)` tuples, iterator adapter chains from
    // std). A naive structural walk re-descends every shared child once per path
    // that reaches it — O(paths) = exponential in the DAG's node count, even
    // though the distinct-node count is small. This ran during MIR extraction,
    // BEFORE the per-function verification deadline is even armed, so it hung
    // `trustc` for hours at 100% CPU on `memchr(feature="std")` with no solver
    // involved. Memoizing on the interned `Ty` pointer collapses the exponential
    // to linear in distinct subterms.
    //
    // The sole consumer (`normalize_alias`) only tests
    // `depth > SAFE_NORMALIZE_ADT_DEPTH`, so nothing past that threshold is
    // observable. Walk iteratively (no call-stack dependence) and revisit a DAG
    // node only when reached under a strictly larger ADT depth. This is a fresh
    // per-call cap equal to the type lowerer's deterministic 4096-node cap; it
    // does not borrow TyLoweringCtx's mutable counter.
    bounded_adt_arg_depth(
        ty,
        SAFE_NORMALIZE_ADT_DEPTH + 1,
        MAX_TYPE_LOWERING_NODES,
        |current| matches!(current.kind(), TyKind::Adt(..)),
        |current, push| match current.kind() {
            TyKind::Adt(_, args) => args.iter().filter_map(|arg| arg.as_type()).all(push),
            TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => push(*inner),
            TyKind::Slice(inner) | TyKind::Array(inner, _) => push(*inner),
            TyKind::Tuple(fields) => fields.iter().all(push),
            TyKind::Alias(_, alias_ty) => {
                alias_ty.args.iter().filter_map(|arg| arg.as_type()).all(push)
            }
            _ => true,
        },
    )
}

fn trust_tuple_or_unit(fields: Vec<TrustTy>) -> TrustTy {
    if fields.is_empty() { TrustTy::Unit } else { TrustTy::Tuple(fields) }
}

fn trust_fn_sig_from_rustc<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig: ty::Binder<'tcx, ty::FnSig<'tcx>>,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> FnSig {
    let sig = tcx.instantiate_bound_regions_with_erased(sig);
    FnSig {
        params: sig.inputs().iter().map(|param_ty| convert_ty_inner(tcx, *param_ty, ctx)).collect(),
        ret: Box::new(convert_ty_inner(tcx, sig.output(), ctx)),
    }
}

fn unsupported_ty(kind: impl Into<String>, detail: impl Into<String>) -> TrustTy {
    TrustTy::Unsupported { kind: kind.into(), detail: detail.into() }
}

fn ty_contains_ty<'tcx>(haystack: ty::Ty<'tcx>, needle: ty::Ty<'tcx>) -> bool {
    haystack == needle || haystack.walk().filter_map(|arg| arg.as_type()).any(|ty| ty == needle)
}

fn is_expanding_recursive_adt<'tcx>(
    stack_ty: ty::Ty<'tcx>,
    current_def_id: rustc_hir::def_id::DefId,
    current_args: ty::GenericArgsRef<'tcx>,
) -> bool {
    let TyKind::Adt(stack_adt, stack_args) = stack_ty.kind() else { return false };
    if stack_adt.did() != current_def_id {
        return false;
    }

    current_args.iter().filter_map(|arg| arg.as_type()).any(|current_arg_ty| {
        stack_args.iter().filter_map(|arg| arg.as_type()).any(|stack_arg_ty| {
            current_arg_ty != stack_arg_ty && ty_contains_ty(current_arg_ty, stack_arg_ty)
        })
    })
}

/// Convert a rustc Ty to our simplified Ty.
///
/// This entry point does **not** attempt opaque-alias normalization: an
/// `impl Trait` (`AliasTyKind::Opaque`) type lowers to `Unsupported`. Use
/// it from call sites that do not have a MIR body's `TypingEnv` in scope.
/// To reveal opaque alias types where it is sound and build-safe to do so,
/// use [`convert_ty_in_env`] instead. (`Free` aliases are still expanded.)
// Trust (v25 B1): FAITHFUL-SCALAR extraction mode. When set, isize/usize
// convert to `TrustTy::PtrSizedInt` and char to `TrustTy::Char` instead of
// the legacy width collapse — preserving the identity the trust-ir bridge
// needs for the differential's signature comparison. Thread-local + RAII so
// the flag scopes EXACTLY to one `extract_function_faithful` call even under
// parallel `mir_built` (each rustc worker thread owns its own flag), and the
// legacy verifier path (plain `extract_function`) is byte-identical
// unchanged — its ~700 direct `Ty::Int{..}` matches never see the new
// spellings until their own migration wave.
thread_local! {
    static FAITHFUL_SCALARS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(crate) struct FaithfulScalarsGuard(bool);

impl FaithfulScalarsGuard {
    pub(crate) fn enable() -> Self {
        let prev = FAITHFUL_SCALARS.with(|f| f.replace(true));
        FaithfulScalarsGuard(prev)
    }
}

impl Drop for FaithfulScalarsGuard {
    fn drop(&mut self) {
        let prev = self.0;
        FAITHFUL_SCALARS.with(|f| f.set(prev));
    }
}

fn faithful_scalars() -> bool {
    FAITHFUL_SCALARS.with(|f| f.get())
}

pub(crate) fn convert_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> TrustTy {
    let mut ctx = TyLoweringCtx::default();
    ctx.canonical_cut = canonical_cut_set(tcx, ty);
    convert_ty_inner(tcx, ty, &mut ctx)
}

/// Convert a rustc Ty to our simplified Ty, normalizing **opaque** alias
/// types (`impl Trait`) against `typing_env` where it is sound and
/// build-safe.
///
/// `typing_env` must be the env of the MIR body the type comes from — for
/// verifier purposes that is `body.typing_env(tcx)`, which is
/// `TypingEnv::post_analysis(..)` on the optimized (Runtime-phase) MIR the
/// verifier runs on. Post-analysis is exactly the mode in which rustc
/// reveals an opaque's concrete underlying type within its defining scope,
/// so the reveal is rustc's own canonical normalization rather than a
/// hand-rolled guess.
///
/// Only `AliasTyKind::Opaque` is revealed here. Projection / inherent
/// aliases keep lowering to `Unsupported` — resolving those drives the
/// trait solver, which can fatally overflow rustc's recursion limit (the
/// typenum `UInt<UInt<…>>: Unsigned` regression that defeated four prior
/// normalization attempts). See the alias arm of `convert_ty_inner`.
pub(crate) fn convert_ty_in_env<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: ty::Ty<'tcx>,
) -> TrustTy {
    let mut ctx = TyLoweringCtx::with_typing_env(typing_env);
    ctx.canonical_cut = canonical_cut_set(tcx, ty);
    convert_ty_inner(tcx, ty, &mut ctx)
}

fn convert_ty_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    // verifier-perf (produced-node budget): once this function's cumulative
    // produced-tree size has crossed the budget, stop assembling fat tree — return
    // the cheap fail-closed recursive-ADT marker. SOUNDNESS: DROP-ONLY (the marker
    // carries no modeled sort; uses still fail closed). See
    // `MAX_TYPE_LOWERING_PRODUCED_NODES`.
    if ctx.produced_nodes > ctx.produced_budget {
        return produced_budget_degraded_leaf();
    }

    // RC-1: the memo below is keyed on `ty` ALONE, but a cut point's lowering is
    // NOT a function of `ty` alone — it is the full definition at the walk's root
    // (`adt_stack` empty) and the by-name marker everywhere else. Caching either
    // one would serve it in the other position: a root `(Tree, Arc<Tree>)` lowers
    // `Tree` fully at empty stack, caches it, and then `Arc<Tree>`'s
    // `ArcInner.data` — which MUST be the cut marker — gets a cache hit and comes
    // back fully expanded, which is exactly the two-representations defect RC-1
    // exists to remove. Cut points therefore bypass the memo in both directions.
    // The cost is bounded: a cut point is either a one-node marker (free) or a
    // definitional occurrence, which only the tuple/array/ref arms can reach more
    // than once per walk.
    let is_canonical_cut_point = ctx.canonical_cut.contains(&ty);

    // verifier-perf: memoization. If we've already lowered
    // this exact `Ty` in this walk, reuse the result instead of
    // re-walking the subtree and burning the node budget again.
    // rustc interns `Ty<'tcx>` so pointer-equality is the right key.
    // The cache itself is per-`convert_ty` (no global state).
    if let Some(cached) = ctx.cache.get(&ty).filter(|_| !is_canonical_cut_point) {
        // verifier-perf: a cache hit still MATERIALIZES the cached subtree (the
        // `clone` copies the whole tree into the parent), so charge its produced
        // size against the budget — otherwise the cache lets an unbounded number of
        // fat-subtree clones bypass the budget (the actual OOM mechanism).
        let cached = cached.clone();
        ctx.produced_nodes = ctx.produced_nodes.saturating_add(produced_node_count(
            &cached,
            ctx.produced_budget.saturating_sub(ctx.produced_nodes).saturating_add(1),
        ));
        return cached;
    }

    if ctx.depth >= MAX_TYPE_LOWERING_DEPTH {
        return unsupported_ty(
            "TyKind",
            format!("type lowering exceeded depth limit {MAX_TYPE_LOWERING_DEPTH}"),
        );
    }
    if ctx.remaining_nodes == 0 {
        return unsupported_ty(
            "TyKind",
            format!("type lowering exceeded node budget {MAX_TYPE_LOWERING_NODES}"),
        );
    }
    // Ambient per-function deadline (amortized on the node counter): type
    // lowering is the extraction choke point, so polling here bounds every
    // lowering loop by the per-function budget. Bailing to `Unsupported` lets
    // extraction finish fast; the compiler's post-extraction checkpoint then
    // reports the overrun as a hard error. Fail-closed: never a proof.
    if ctx.remaining_nodes % 256 == 0 && trust_types::verify_budget::budget_exhausted() {
        return unsupported_ty(
            "TyKind",
            "type lowering exceeded the per-function verification budget",
        );
    }

    ctx.remaining_nodes -= 1;
    ctx.depth += 1;
    let lowered = match ty.kind() {
        TyKind::Bool => TrustTy::Bool,

        TyKind::Int(int_ty) => {
            // v25 B1 faithful mode: isize keeps its identity for the
            // trust-ir differential lane (legacy path collapses to width).
            if faithful_scalars() && matches!(int_ty, rustc_ast_ir::IntTy::Isize) {
                TrustTy::PtrSizedInt { signed: true }
            } else {
                let width = int_width_from_int_ty(int_ty, tcx);
                TrustTy::Int { width, signed: true }
            }
        }

        TyKind::Uint(uint_ty) => {
            if faithful_scalars() && matches!(uint_ty, rustc_ast_ir::UintTy::Usize) {
                TrustTy::PtrSizedInt { signed: false }
            } else {
                let width = uint_width_from_uint_ty(uint_ty, tcx);
                TrustTy::Int { width, signed: false }
            }
        }

        TyKind::Float(float_ty) => {
            let width = match float_ty {
                rustc_ast_ir::FloatTy::F16 => 16,
                rustc_ast_ir::FloatTy::F32 => 32,
                rustc_ast_ir::FloatTy::F64 => 64,
                rustc_ast_ir::FloatTy::F128 => 128,
            };
            TrustTy::Float { width }
        }

        TyKind::Ref(_, inner_ty, mutability) => TrustTy::Ref {
            mutable: mutability.is_mut(),
            inner: Box::new(convert_ty_inner(tcx, *inner_ty, ctx)),
        },

        TyKind::Slice(elem_ty) => {
            TrustTy::Slice { elem: Box::new(convert_ty_inner(tcx, *elem_ty, ctx)) }
        }

        TyKind::Array(elem_ty, len_const) => {
            let elem = convert_ty_inner(tcx, *elem_ty, ctx);
            // Accept an already-concrete length; otherwise EVALUATE the const so a
            // NAMED length (`[u8; INLINE_SIZE]`), an associated const, etc. lowers.
            // These are idiomatic and monomorphic at verify time, so leaving them
            // "unsupported" wrongly fails panic-freedom on ordinary fixed arrays.
            // Use the body's `TypingEnv` when present, else the fully-monomorphized
            // env (sound here: the array type is part of a concrete, monomorphic body).
            let len = len_const.try_to_target_usize(tcx).or_else(|| {
                let typing_env = ctx.typing_env.unwrap_or_else(ty::TypingEnv::fully_monomorphized);
                tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(*len_const))
                    .ok()
                    .and_then(|c| c.try_to_target_usize(tcx))
            });
            match len {
                Some(len) => TrustTy::Array { elem: Box::new(elem), len },
                // Trust: piece #7a — an un-monomorphized `[T; N]` whose length is a
                // const-generic PARAM gets a MODELED symbolic length keyed on the
                // param identity, instead of falling closed to `unsupported_ty`.
                // The length symbol `__trust_constparam_{index}_{name}` is minted
                // BYTE-IDENTICALLY (via `const_param_symbol`) with the value `N`'s
                // operand symbol, so a guard `if i < N` discharges the bounds VC.
                // SOUNDNESS: keying on `(index, name)` — NOT `(width, signed)` —
                // gives two distinct usize params `M`, `N` DISTINCT symbols, so the
                // guard on `N` cannot discharge an index on `[T; M]` (M != N). Any
                // NON-param unresolved length still fails closed below.
                None => match len_const.kind() {
                    ty::ConstKind::Param(p) => TrustTy::SymArray {
                        elem: Box::new(elem),
                        len_sym: trust_types::ConstLen { index: p.index, name: p.name.to_string() },
                    },
                    _ => unsupported_ty(
                        "TyKind::Array",
                        format!("array length {len_const:?} is not a concrete target usize"),
                    ),
                },
            }
        }

        TyKind::Tuple(fields) => {
            let field_tys: Vec<TrustTy> =
                fields.iter().map(|f| convert_ty_inner(tcx, f, ctx)).collect();
            trust_tuple_or_unit(field_tys)
        }

        TyKind::Adt(adt_def, args) => {
            let name = crate::safe_def_path_str(tcx, adt_def.did());
            // RC-1 (canonical recursive-type lowering) — THE CUT. This type lies
            // on a cycle and is the cycle's canonically chosen cut point, and it
            // is not the ROOT of this walk (`adt_stack` non-empty), so it lowers
            // to the by-name reference NO MATTER which root reached it. That is
            // what makes the representation a function of the type alone; see the
            // block comment on `canonical_cut_set` for why it is unique and why it
            // narrows, rather than widens, the generics-erased-name surface. An
            // empty cut set (acyclic type, or discovery over budget) skips this
            // arm entirely and the lowering is byte-identical to pre-RC-1.
            //
            // The marker is IDENTITY-BEARING (`canonical_cut_ref`, not
            // `recursive_datatype_ref(&name)`): `name` here is the GENERICS-ERASED
            // def path, and a cut point carries no structure, so an erased marker
            // would make `Foo<u8>` and `Foo<i32>` — two distinct cut points —
            // compare EQUAL wherever both appear below a common root. See the
            // block comment's merge analysis.
            if !ctx.adt_stack.is_empty() && ctx.canonical_cut.contains(&ty) {
                canonical_cut_ref(tcx, ty)
            }
            // Lever A step 2: the kernel universe-`Level` enum lowers to a native
            // recursive `Ty::Datatype` (its `Arc<Level>` children become by-name
            // self-references) instead of degrading to the recursive-ADT
            // `Unsupported` marker. Def-path gated to EXACTLY `Level` (the `Expr`/
            // `ExprKind` datatypes have their own step-5 gates below); `Name` still
            // keeps its existing lowering.
            else if is_level_datatype_target(tcx, adt_def.did()) {
                lower_level_datatype(tcx, ty, *adt_def, args, &name, ctx)
            }
            // Lever A step 5: the kernel `ExprKind` ENUM — the structural
            // expression variants the real `infer_type` matches on (BVar/Sort/
            // Const/App/Lam/Pi/Let/Lit/Proj/MData/…) — lowers to a native recursive
            // `Ty::Datatype`. Its recursive `Arc<Expr>` children, and its `Level`/
            // `Name`/`Literal` payloads, become BY-NAME datatype references (see
            // `datatype_child_field_ty`), so the produced tree stays O(variants):
            // the mutually-recursive Expr/ExprKind cluster no longer expands into
            // the ~464 MB `Ty::Adt` tree that OOM-killed extraction. Def-path gated
            // to EXACTLY `ExprKind`, checked BEFORE the enum path below.
            else if is_exprkind_datatype_target(tcx, adt_def.did()) {
                lower_exprkind_datatype(tcx, ty, *adt_def, args, &name, ctx)
            }
            // Lever A step 5: the kernel `Expr` STRUCT (an `ExprKind` plus cached
            // metadata) lowers to a single-constructor `Ty::Datatype` whose `kind`
            // field is a by-name `ExprKind` reference and whose `meta` field is an
            // opaque datatype reference. Checked BEFORE the struct/union path so
            // `Expr` takes the datatype model (and its recursive `kind` child a
            // by-name ref) instead of the recursive-struct field compaction.
            // Def-path gated to EXACTLY `Expr`.
            else if is_expr_datatype_target(tcx, adt_def.did()) {
                lower_expr_datatype(tcx, ty, *adt_def, args, &name, ctx)
            }
            // A UNION lowers like a struct (its real-named overlapping fields via
            // `all_fields()`), NOT like an enum: it has no discriminant, so the
            // enum path's synthetic `__tag` / `__v{v}_` shape is wrong and leaves
            // a union field projection (e.g. `MaybeUninit`'s `value` = Field(1),
            // the `vec!`/`write_box_via_move` write destination) without a sort
            // (`TrustSymbolicAggregateFieldSortMissing`). Modeling the overlapping
            // fields as independent slots is sound for verification here: a
            // single-field-used union (MaybeUninit: write `value`, read `value`)
            // is exact, and a genuine type-punning read (write one field, read
            // another) is still caught by the read-only union-field obligation,
            // which fails closed. So treat structs and unions identically below.
            else if !adt_def.is_struct() && !adt_def.is_union() {
                lower_enum_adt(tcx, ty, *adt_def, args, &name, ctx)
            } else if ctx.adt_stack.contains(&ty) {
                // Lever A (recursive-struct back-edge): re-entering the SAME ADT
                // with identical arguments is the recursive field position (e.g.
                // `Box<Self>`'s pointee resolving back to the struct). Instead of
                // poisoning the whole enclosing type to `Unsupported` — which gave
                // it no modeled SMT sort and forced every projection/match through
                // it to Unknown — emit a BY-NAME datatype reference. SMT-LIB
                // datatypes are natively recursive, so the reference resolves to the
                // definitional occurrence (the outer, fully-lowered type) at declare
                // time. SOUNDNESS: a datatype reference introduces no facts; it is a
                // sort marker only.
                recursive_datatype_ref(&name)
            } else if ctx
                .adt_stack
                .iter()
                .any(|stack_ty| is_expanding_recursive_adt(*stack_ty, adt_def.did(), args))
            {
                // An EXPANDING generic recursion (`List<Box<List<T>>>`-style, the
                // arguments grow on each re-entry) does NOT have a finite, single
                // SMT datatype sort — the by-name reference would be unsound (the
                // referent's field sorts differ per instantiation). Stay fail-closed:
                // leave it Unsupported (Unknown), never risk a wrong sort. This is
                // the deliberately-left-Unknown case.
                unsupported_ty(
                    "TyKind::Adt",
                    format!(
                        "recursive ADT {name} with expanding generic arguments encountered while lowering fields"
                    ),
                )
            } else {
                // Lever A: inside a recursive lowering (this struct is a field of an
                // ADT already on the stack — the Arc/ArcInner/Atomic/UnsafeCell
                // wrappers around a recursive `Expr`/`Level`), compact each oversized
                // field subtree so the enclosing tree cannot blow up to the
                // thousands-of-nodes size that OOM-kills extraction / stalls
                // `place_ty`'s per-place clone. At the TOP level (empty stack) keep
                // the exact legacy expansion so ordinary standalone structs are
                // byte-for-byte unchanged. SOUNDNESS: a compacted field is a modeled,
                // fact-free datatype sort — never `Unsupported`, never a fabricated
                // fact.
                let cap_fields = !ctx.adt_stack.is_empty();
                ctx.adt_stack.push(ty);
                let fields: Vec<(String, TrustTy)> = adt_def
                    .all_fields()
                    .map(|f| {
                        let field_name = f.name.to_string();
                        let mut field_ty =
                            convert_ty_inner(tcx, f.ty(tcx, args).skip_normalization(), ctx);
                        if cap_fields
                            && ty_node_count(&field_ty, MAX_DATATYPE_FIELD_NODES + 1)
                                > MAX_DATATYPE_FIELD_NODES
                        {
                            field_ty = compact_oversized_field(&field_ty);
                        }
                        (field_name, field_ty)
                    })
                    .collect();
                ctx.adt_stack.pop();
                // Trust: PHASE 4 — a struct/union has NO variants; the `fields`
                // are its single anonymous constructor's fields.
                // Trust: enum-disc-full-native — a struct is never disc-index-safe.
                // Trust (B3-4 T3): concrete struct layout, FAITHFUL LANE ONLY —
                // a Some(layout) is semantic-hash-visible, so filling it on a
                // verifier lane would shift shipped proof-cert/content pins
                // (the faithful_enum_repr shield discipline, B3-1). The gates
                // mirror the THIR producer's T2 fill exactly: fully-concrete
                // type, layout_of Ok, offsets in source-declaration order.
                let layout = if faithful_scalars()
                    && !ty.has_non_region_param()
                    && !ty.has_non_region_infer()
                    && !ty.has_opaque_types()
                {
                    ctx.typing_env.and_then(|te| {
                        tcx.layout_of(te.as_query_input(ty)).ok().map(|l| {
                            let r = adt_def.repr();
                            let repr = if r.transparent() {
                                "transparent".to_string()
                            } else if let Some(pack) = r.pack {
                                format!("packed:{}", pack.bytes())
                            } else if r.c() {
                                "c".to_string()
                            } else {
                                "rust".to_string()
                            };
                            Box::new(trust_types::AdtLayoutInfo {
                                size: l.size.bytes(),
                                align: l.align.abi.bytes(),
                                // `FieldsShape::offset` PANICS out of range and a
                                // struct's layout may carry fewer field entries
                                // than the variant has (scalable-vector structs):
                                // bounds-check, never abort the extraction.
                                field_offsets: (0..adt_def.non_enum_variant().fields.len())
                                    .filter(|i| *i < l.layout.fields().count())
                                    .map(|i| l.layout.fields().offset(i).bytes())
                                    .collect(),
                                repr,
                            })
                        })
                    })
                } else {
                    None
                };
                TrustTy::Adt {
                    name,
                    fields,
                    variants: Vec::new(),
                    disc_index_safe: false,
                    faithful_enum_repr: None,
                    layout,
                    enum_layout: None,
                    // Trust: W19 — the struct/union kind, read from rustc's AdtDef.
                    // This is the SOLE faithfulness bearer that lets the field-setter
                    // recognizer's G-STRUCT-KIND gate distinguish a struct (sound
                    // per-field frame) from a UNION (fields overlap at offset 0, the
                    // frame is operationally false). Both structs and unions reach
                    // this arm (the `!is_struct() && !is_union()` enum guard above
                    // routed enums to `lower_enum_adt`), so stamp the real kind.
                    adt_kind: Some(if adt_def.is_union() {
                        trust_types::AdtKind::Union
                    } else {
                        trust_types::AdtKind::Struct
                    }),
                }
            }
        }

        TyKind::Never => TrustTy::Never,

        _ if ty.is_unit() => TrustTy::Unit,

        // Char: legacy verification path maps to u32; the v25 faithful lane
        // preserves char identity for the trust-ir differential.
        TyKind::Char => {
            if faithful_scalars() {
                TrustTy::Char
            } else {
                TrustTy::Int { width: 32, signed: false }
            }
        }

        TyKind::RawPtr(pointee_ty, mutability) => TrustTy::RawPtr {
            mutable: mutability.is_mut(),
            pointee: Box::new(convert_ty_inner(tcx, *pointee_ty, ctx)),
        },

        // Trust: `str` is morally `[u8]` — a fat pointer carrying a byte length.
        // Modeling it as Slice<u8> reuses the existing slice encoding (same
        // Sort::Int fallback, same fat-pointer classification) so the type walk
        // stops emitting a spurious UnsupportedMir obligation for trivially-safe
        // string code. Real per-statement safety VCs are unaffected.
        TyKind::Str => {
            // Trust (B2-2): the FAITHFUL lane keeps `str` DISTINCT from `[u8]` so the
            // trust-ir bridge can spell `&str` as the format's first-class
            // FatPtr(FatPtrKind::Str), structurally equal to the producer's. The
            // legacy verifier lane keeps the historical Slice{u8} conflation
            // byte-identically (same guard discipline as the B1 scalar spellings).
            if faithful_scalars() {
                TrustTy::Str
            } else {
                TrustTy::Slice { elem: Box::new(TrustTy::Int { width: 8, signed: false }) }
            }
        }
        TyKind::Foreign(def_id) => unsupported_ty(
            "TyKind::Foreign",
            format!(
                "extern type {} is opaque to Rust layout",
                crate::safe_def_path_str(tcx, *def_id)
            ),
        ),
        TyKind::FnDef(def_id, args) => {
            let sig = tcx.fn_sig(*def_id).instantiate(tcx, args).skip_normalization();
            TrustTy::FnDef {
                name: crate::safe_def_path_str(tcx, *def_id),
                sig: Box::new(trust_fn_sig_from_rustc(tcx, sig, ctx)),
            }
        }
        TyKind::FnPtr(..) => {
            TrustTy::FnPtr { sig: Box::new(trust_fn_sig_from_rustc(tcx, ty.fn_sig(tcx), ctx)) }
        }
        TyKind::Dynamic(predicates, _) => TrustTy::Dynamic {
            trait_name: predicates
                .principal_def_id()
                .map(|def_id| crate::safe_def_path_str(tcx, def_id))
                .unwrap_or_else(|| "dyn".to_string()),
        },
        TyKind::Closure(def_id, args) => {
            let clo = args.as_closure();
            // Trust (B6, RFC TRUST_IR_V2): record the closure's CALL signature +
            // inferred kind so the trust-ir bridge can spell a by-value FnOnce env
            // as the format's first-class Ty::Closure, structurally equal to the
            // producer's. `params` are the UNTUPLED call arguments; a unit return
            // is `None` (the producer's empty-returns convention). An unresolved
            // kind (`kind_ty` still an inference placeholder — impossible for the
            // monomorphic bodies this crate extracts, but never assumed) or a
            // non-tuple input leaves `call: None` — the respell then fails closed
            // to the closure_env struct spelling.
            let call = clo.kind_ty().to_opt_closure_kind().and_then(|k| {
                let sig = tcx.instantiate_bound_regions_with_erased(clo.sig());
                let rustc_middle::ty::TyKind::Tuple(arg_tys) = sig.inputs().first()?.kind() else {
                    return None;
                };
                Some(Box::new(trust_types::ClosureCallSig {
                    kind: match k {
                        rustc_middle::ty::ClosureKind::Fn => trust_types::ClosureCallKind::Fn,
                        rustc_middle::ty::ClosureKind::FnMut => trust_types::ClosureCallKind::FnMut,
                        rustc_middle::ty::ClosureKind::FnOnce => {
                            trust_types::ClosureCallKind::FnOnce
                        }
                    },
                    params: arg_tys.iter().map(|a| convert_ty_inner(tcx, a, ctx)).collect(),
                    ret: (!sig.output().is_unit())
                        .then(|| convert_ty_inner(tcx, sig.output(), ctx)),
                }))
            });
            TrustTy::Closure {
                name: crate::safe_def_path_str(tcx, *def_id),
                upvars: clo
                    .upvar_tys()
                    .iter()
                    .map(|upvar_ty| convert_ty_inner(tcx, upvar_ty, ctx))
                    .collect(),
                call,
            }
        }
        TyKind::CoroutineClosure(def_id, _) => unsupported_ty(
            "TyKind::CoroutineClosure",
            format!(
                "coroutine closure {} needs state-machine modeling",
                crate::safe_def_path_str(tcx, *def_id)
            ),
        ),
        // Trust: piece #13 (safe-async data-safety) — model a coroutine frame
        // as an OPAQUE type (`Ty::Coroutine`), like a closure, rather than
        // `Ty::Unsupported`. This is what lets a coroutine RESUME body (post-
        // `StateTransform`) verify its ordinary arithmetic/bounds segments: the
        // resume body's `self` frame is `TyKind::Coroutine`, and the state
        // selector / across-await frame fields read out of it resolve OPAQUELY.
        //
        // Trust: piece #13 step-2 — carry the coroutine's UPVAR types (the
        // captured args, which occupy the frame's PREFIX field slots and are what
        // a zero-await resume body reads back, e.g. `((*self).0: u8)` = the saved
        // arg `x`). This is the SAME `upvar_tys()` a closure carries. SOUNDNESS is
        // preserved on BOTH lanes:
        //   * vcgen/default lane: its `project_ty`/`project_ty_ref` `Field` arms
        //     have NO `Ty::Coroutine` case (only `Ty::Closure`), so a coroutine
        //     frame-field projection STILL returns `None` there → still havoc'd,
        //     unchanged from the empty-upvars behavior (the across-await staleness
        //     trap is unaffected).
        //   * native trust-ir-bridge lane: it now resolves the field TYPE from
        //     these upvars, but the frame VALUE is built as an opaque `Inst::Undef`
        //     (piece #13 step-2 aggregate lowering), so an `ExtractField` off it
        //     yields a FRESH UNCONSTRAINED value — the field TYPE is precise but
        //     the field VALUE is havoc'd, exactly the sound over-approximation for
        //     "anything the executor left across a suspend". A value held across
        //     `.await` therefore never carries a stale pre-suspend fact.
        // Only the captured-arg prefix fields are typed here; a HIGHER field
        // (an across-await saved local, only reached in a body with an `.await`)
        // has no upvar entry and the native lane fails that projection closed
        // (Unknown, never a false proof) — the single/multi-await frontier is a
        // sound later increment.
        TyKind::Coroutine(def_id, args) => TrustTy::Coroutine {
            name: crate::safe_def_path_str(tcx, *def_id),
            upvars: args
                .as_coroutine()
                .upvar_tys()
                .iter()
                .map(|upvar_ty| convert_ty_inner(tcx, upvar_ty, ctx))
                .collect(),
        },
        TyKind::CoroutineWitness(def_id, _) => {
            TrustTy::Coroutine { name: crate::safe_def_path_str(tcx, *def_id), upvars: Vec::new() }
        }
        TyKind::Pat(inner_ty, _pat) => {
            // verifier-perf: pattern types (`u32 is 1..`, NonZeroUsize,
            // etc.) are *restricted-value subsets* of an underlying integer
            // type. Lowering as the inner type is sound for safety
            // obligations: any overflow/bounds/cast check that holds on the
            // wider integer also holds on the restricted subset. The
            // restriction itself is preserved by rustc's MIR-level
            // construction (a `Pat` literal can only be produced through
            // checked entry points), so the verifier still has correct
            // semantics — it just doesn't *additionally* exploit the
            // refinement yet. Following work: emit a `TrustRefinement::Range`
            // precondition so the SMT backend can use the tighter bound.
            convert_ty_inner(tcx, *inner_ty, ctx)
        }
        TyKind::Alias(_, alias) => {
            // Trust: rust 1.99 moved the `AliasTyKind` off `TyKind::Alias`'s first
            // payload (now `IsRigid`) onto the `AliasTy`'s `kind` field; the alias
            // `def_id` likewise lives inside that per-variant `kind`.
            let kind = alias.kind;
            // verifier-perf: keep solver-dependent alias
            // normalization fail-closed.
            //
            // FOUR attempts to call `tcx.try_normalize_erasing_regions`
            // here ALL caused typenum's `UInt<UInt<…>>: Unsigned` trait
            // resolution to exhaust rustc's 128-deep recursion limit and
            // fail with `E0275`:
            //   1. Unconditional normalize          → E0275
            //   2. Guard on "no nested Alias args"  → E0275 (typenum
            //      nesting is in ADT args, not Alias args)
            //   3. Guard on adt_arg_depth ≤ 16      → E0275 in libstd
            //      test compile (zlib-rs deps)
            //   4. Guard on adt_arg_depth ≤ 4       → E0275 in libstd
            //      test compile *during* the stage2 build itself
            //
            // The trait solver's recursion budget is exhausted by
            // something we trigger via the normalize call — not the
            // alias arg depth alone. Diagnosis is open; the path
            // forward is documented in
            // `docs/verifier-coverage-roadmap.md` §1.
            //
            // Definitionally transparent free type aliases are different:
            // rustc exposes a structural expander that substitutes the
            // alias RHS without solving projection/inherent associated-type
            // obligations. That is safe to use here because unsupported
            // constructs in the expanded RHS still flow through the normal
            // fail-closed lowering path.
            match kind {
                ty::AliasTyKind::Free { def_id } => {
                    let expanded = tcx.expand_free_alias_tys(
                        tcx.type_of(def_id).instantiate(tcx, alias.args).skip_normalization(),
                    );
                    convert_ty_inner(tcx, expanded, ctx)
                }
                // verifier-coverage: reveal `impl Trait` (opaque)
                // aliases to their concrete underlying type, but only when
                // we have the body's `TypingEnv` (i.e. we came in through
                // `convert_ty_in_env`). The reveal goes through a
                // `tcx.type_of` def lookup folded by
                // `try_normalize_erasing_regions`, NOT the trait selector,
                // so it does not re-trigger the typenum `E0275` overflow
                // that Projection/Inherent resolution does. Without an env,
                // stay fail-closed (legacy behavior).
                ty::AliasTyKind::Opaque { .. } => match ctx.typing_env {
                    Some(typing_env) => normalize_alias(tcx, typing_env, ty, ctx),
                    None => unsupported_ty(
                        "TyKind::Alias",
                        "opaque alias has no typing env to reveal against".to_string(),
                    ),
                },
                // Trust verifier-coverage: resolve monomorphic Projection/Inherent
                // associated types (e.g. a `File` fd modeled as `<_ as _>::Assoc`)
                // to their concrete underlying type through the SAME guarded
                // normalizer the Opaque arm uses. `normalize_alias`'s
                // `has_non_region_param` + `adt_arg_depth` guards reject exactly the
                // pre-monomorphization and deep-typenum (`UInt<UInt<…>>: Unsigned`)
                // cases that overflowed the trait solver (E0275) in the four prior
                // projection-normalization attempts (see the FOUR-attempts note at
                // the top of this match). Without an env, stay fail-closed.
                ty::AliasTyKind::Projection { .. } | ty::AliasTyKind::Inherent { .. } => {
                    match ctx.typing_env {
                        Some(typing_env) => normalize_alias(tcx, typing_env, ty, ctx),
                        None => unsupported_ty(
                            "TyKind::Alias",
                            format!("alias type {kind:?} has no typing env to normalize against"),
                        ),
                    }
                }
            }
        }
        TyKind::Param(param) => unsupported_ty(
            "TyKind::Param",
            format!("generic parameter {param:?} needs monomorphization"),
        ),
        TyKind::Bound(_, bound) => {
            unsupported_ty("TyKind::Bound", format!("bound type {bound:?} needs binder semantics"))
        }
        TyKind::Placeholder(placeholder) => unsupported_ty(
            "TyKind::Placeholder",
            format!("placeholder type {placeholder:?} needs canonical-query semantics"),
        ),
        TyKind::Infer(infer) => unsupported_ty(
            "TyKind::Infer",
            format!("inference variable {infer:?} was not resolved"),
        ),
        TyKind::UnsafeBinder(_) => unsupported_ty(
            "TyKind::UnsafeBinder",
            "unsafe binder type needs erased-lifetime semantics",
        ),
        TyKind::Error(_) => {
            unsupported_ty("TyKind::Error", "rustc reported an erroneous type during extraction")
        }
    };
    ctx.depth -= 1;
    // verifier-perf (produced-node budget): charge the produced size of this
    // freshly-lowered subtree (short-circuited just past the remaining headroom so
    // a huge tree costs O(headroom)). When the cumulative produced size crosses the
    // budget, the early-return at the top of `convert_ty_inner` degrades every
    // subsequent lowering to the fail-closed marker (DROP-ONLY).
    let headroom = ctx.produced_budget.saturating_sub(ctx.produced_nodes).saturating_add(1);
    ctx.produced_nodes = ctx.produced_nodes.saturating_add(produced_node_count(&lowered, headroom));
    if ctx.produced_nodes > ctx.produced_budget && std::env::var("TRUST_VCGEN_TRACE_BUDGET").is_ok()
    {
        eprintln!(
            "[TYPE_LOWERING_BUDGET] produced-node budget {} crossed (produced={}) — degrading remaining types to fail-closed Unsupported",
            ctx.produced_budget, ctx.produced_nodes,
        );
    }
    // verifier-perf: cache the result so subsequent walks
    // through the same Ty hit the early-return at the top.
    // RC-1: never memoize a cut point — its lowering depends on whether this
    // occurrence is the walk's root, which the `ty` key cannot express. See the
    // matching comment at the memo lookup.
    if !is_canonical_cut_point {
        ctx.cache.insert(ty, lowered.clone());
    }
    lowered
}

/// Normalize a monomorphic **opaque** (`impl Trait`), **projection**
/// (`<T as Trait>::Assoc`), or **inherent** alias to its concrete underlying
/// type and lower that, or return `Unsupported` if it cannot be resolved to a
/// supported sort.
///
/// Invoked only when a `typing_env` is present (i.e. we came in through
/// [`convert_ty_in_env`]). The resolution goes through rustc's own
/// `try_normalize_erasing_regions`, so:
///
/// * In PostAnalysis mode (Runtime-phase MIR — what the verifier runs on)
///   the alias resolves to its real concrete type within its defining
///   scope. We then lower *that* type. This is semantics-preserving: the
///   value at this local genuinely has the resolved type at runtime.
/// * If the env is not one that resolves this alias (e.g. an opaque outside
///   its defining scope, so normalization leaves it as an alias), or
///   normalization returns an error type, or the resolved type is itself
///   another alias, or it lowers to `Unsupported`, we fail safe and return
///   `Unsupported`. A false-`Unsupported` only costs proof coverage; mapping
///   an alias to a wrong sort would be unsound.
///
/// Build-safety guards (the two the four prior projection-normalization
/// attempts lacked — see the FOUR-attempts note on the `TyKind::Alias` arm):
///
/// * `has_non_region_param()`: only fully-monomorphic aliases are normalized.
///   A param-bearing projection is pre-monomorphization — its associated type
///   is not knowable here, and feeding it to the normalizer is exactly the
///   `UInt<UInt<…>>: Unsigned` shape that overflowed the trait solver (E0275).
/// * `adt_arg_depth(ty) <= SAFE_NORMALIZE_ADT_DEPTH`: a deeply-nested ADT
///   argument (typenum-like) can re-enter the fatal trait-solver recursion
///   when projection resolution folds the alias's generic arguments. The
///   shallow-depth guard keeps such an alias `Unsupported` rather than risking
///   the overflow.
///
/// Together these bound the projection path to monomorphic, shallow aliases
/// that resolve in O(1) without deep selector recursion — never a guess, only
/// rustc's definitional-equal concrete type or a fail-safe `Unsupported`.
fn normalize_alias<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    alias_ty: ty::Ty<'tcx>,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    // Only normalize fully-monomorphic aliases. If the alias (or its args)
    // still carries a non-region generic parameter, the body is generic /
    // pre-monomorphization: the underlying type is not knowable here, and
    // feeding a param-bearing type to `normalize_erasing_regions` is the case
    // the rest of this crate guards against (cf. `const_operand_value`). Stay
    // Unsupported — fail safe.
    if alias_ty.has_non_region_param() {
        // Trust (R3, generics): this marker is the PRODUCER of the shared
        // `trust_types::PRE_MONO_ALIAS_{KIND,DETAIL}` pair — the vcgen
        // declaration relaxation and the bridge's opaque zero-field-struct
        // lowering key on EXACTLY this (kind, detail). Keep them in lockstep.
        return unsupported_ty(
            trust_types::PRE_MONO_ALIAS_KIND,
            trust_types::PRE_MONO_ALIAS_DETAIL,
        );
    }

    let depth = adt_arg_depth(alias_ty);
    if depth > SAFE_NORMALIZE_ADT_DEPTH {
        return unsupported_ty(
            "TyKind::Alias",
            format!("alias args nest ADTs too deep ({depth}) to normalize safely"),
        );
    }

    // rustc's canonical normalization. `try_*` (not the panicking variant) so a
    // normalization failure is a graceful `Err`, never a panic. The
    // monomorphism + depth guards above keep this off the typenum E0275 path.
    let revealed =
        match tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(alias_ty)) {
            Ok(revealed) => revealed,
            Err(_) => {
                return unsupported_ty(
                    "TyKind::Alias",
                    "alias could not be normalized in this typing env".to_string(),
                );
            }
        };

    // If normalization made no progress (still the same alias, or resolved
    // to *another* alias — e.g. an opaque not in its defining scope), do not
    // loop or guess: stay Unsupported.
    if revealed == alias_ty || matches!(revealed.kind(), TyKind::Alias(..)) {
        return unsupported_ty(
            "TyKind::Alias",
            "alias did not resolve to a concrete underlying type here".to_string(),
        );
    }

    // Lower the concrete revealed type. Any downstream `Unsupported`
    // (including a `TyKind::Error` from a non-fatal overflow `delay_as_bug`)
    // propagates as-is, so we never upgrade an unprovable type to a
    // provable-looking sort.
    convert_ty_inner(tcx, revealed, ctx)
}

/// Lever A step 2 — pure predicate: is `(crate_name, def_path)` the kernel
/// universe-`Level` enum? Gated on the crate NAME being `clean_kernel` AND the
/// def path being exactly `level::Level`, handling BOTH `def_path_str` renderings:
///   * upstream dependency  → `clean_kernel::level::Level` (crate-name prefixed)
///   * crate under compile  → `level::Level` (LOCAL defs render without the crate
///     name — the real path observed extracting `Level` from the kernel crate
///     itself; verified in-test via the `probe`).
/// The crate-name guard makes the bare `level::Level` form precise (a same-named
/// `level::Level` in another crate is rejected), and exact-match (not suffix)
/// rejects `…sublevel::Level`. EXACTLY `Level` un-degrades to a `Ty::Datatype`
/// this step; every other recursive ADT (`Name`, `Expr`, …) keeps its existing
/// lowering. Pure INFRASTRUCTURE — proves no VC, drains no axiom.
fn is_level_path(crate_name: &str, def_path: &str) -> bool {
    crate_name == "clean_kernel"
        && (def_path == "clean_kernel::level::Level" || def_path == "level::Level")
}

/// `tcx`-driven form of [`is_level_path`]: reads the ADT's owning crate name and
/// its def path. Scoping to a single crate+path keeps the change faithful and
/// auditable — no other type's lowering shifts.
fn is_level_datatype_target(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> bool {
    is_level_path(tcx.crate_name(def_id.krate).as_str(), &crate::safe_def_path_str(tcx, def_id))
}

/// Lever A step 5 — is `(crate_name, def_path)` the kernel `Expr` STRUCT (the
/// `ExprKind` + cached-metadata wrapper that the whole kernel passes around)?
/// Same crate-name guard + both `def_path_str` renderings as [`is_level_path`].
/// `Expr` is defined in module `expr` (`expr/mod.rs`), so its def path is
///   * upstream dependency  → `clean_kernel::expr::Expr`
///   * crate under compile  → `expr::Expr`
/// Exact match (not suffix) rejects `…exprkind::Expr` or a same-named `Expr` in
/// another module/crate. Pure INFRASTRUCTURE — proves no VC, drains no axiom.
fn is_expr_path(crate_name: &str, def_path: &str) -> bool {
    crate_name == "clean_kernel"
        && (def_path == "clean_kernel::expr::Expr" || def_path == "expr::Expr")
}

/// Lever A step 5 — is `(crate_name, def_path)` the kernel `ExprKind` ENUM (the
/// structural expression variants the real `infer_type` matches on)? `ExprKind`
/// is defined in module `expr::kind` (`expr/kind.rs`), so its def path is
///   * upstream dependency  → `clean_kernel::expr::kind::ExprKind`
///   * crate under compile  → `expr::kind::ExprKind`
/// Same crate-name guard + exact-match discipline as [`is_expr_path`].
fn is_exprkind_path(crate_name: &str, def_path: &str) -> bool {
    crate_name == "clean_kernel"
        && (def_path == "clean_kernel::expr::kind::ExprKind" || def_path == "expr::kind::ExprKind")
}

/// `tcx`-driven form of [`is_expr_path`].
fn is_expr_datatype_target(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> bool {
    is_expr_path(tcx.crate_name(def_id.krate).as_str(), &crate::safe_def_path_str(tcx, def_id))
}

/// `tcx`-driven form of [`is_exprkind_path`].
fn is_exprkind_datatype_target(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> bool {
    is_exprkind_path(tcx.crate_name(def_id.krate).as_str(), &crate::safe_def_path_str(tcx, def_id))
}

/// The nominal-ADT paths that are TRANSPARENT heap/pointer indirections for the
/// purpose of the datatype model: a recursive child stored behind one of these
/// (`Succ(Arc<Level>)`) is semantically just the pointee datatype. Peeled by
/// [`peel_transparent_pointers`] so a recursive field models as a direct datatype
/// self-reference rather than a fat `Arc`/`Box`/`Rc` wrapper subtree.
fn is_transparent_pointer_wrapper(name: &str) -> bool {
    matches!(
        name,
        "alloc::sync::Arc"
            | "std::sync::Arc"
            | "alloc::rc::Rc"
            | "std::rc::Rc"
            | "alloc::boxed::Box"
            | "std::boxed::Box"
    )
}

/// Peel transparent references/raw pointers and `Arc`/`Rc`/`Box` wrappers off a
/// field type to reach the nominal pointee type. `Succ(Arc<Level>)`'s field peels
/// to `Level`; `Param(Name)`'s field is already nominal and peels to itself.
/// Bounded by `MAX_TYPE_LOWERING_DEPTH` so a pathological chain cannot loop.
fn peel_transparent_pointers<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
    let mut cur = ty;
    for _ in 0..MAX_TYPE_LOWERING_DEPTH {
        match cur.kind() {
            TyKind::Ref(_, inner, _) => cur = *inner,
            TyKind::RawPtr(inner, _) => cur = *inner,
            TyKind::Adt(def, args)
                if is_transparent_pointer_wrapper(&crate::safe_def_path_str(tcx, def.did())) =>
            {
                match args.types().next() {
                    Some(inner) => cur = inner,
                    None => return cur,
                }
            }
            _ => return cur,
        }
    }
    cur
}

/// Model one datatype variant/constructor field (Lever A, shared by `Level`
/// step 2 and `Expr`/`ExprKind` step 5). A field whose peeled core is a nominal
/// ADT — a recursive self-reference reached through `Arc`/`Box`/`Rc`/`&`/`*`
/// (`App(Arc<Expr>, Arc<Expr>)`, `Succ(Arc<Level>)`), or a sibling nominal payload
/// (`Sort`'s `Level`, `Const`/`Proj`/`Param`'s `Name`, `Lit`'s `Literal`,
/// `Lam`'s `BinderData`, `Expr`'s `ExprMeta`) — becomes a BY-NAME `Ty::Datatype`
/// reference: for the type itself this is the recursive back-edge; for a sibling
/// datatype (`Level`) it is the cross-reference resolved at declare time; for a
/// type NOT modeled as a datatype this step (`Name`, `Literal`, `BinderData`,
/// `ExprMeta`) it is the deliberately OPAQUE, fact-free datatype sort. A non-ADT
/// core (`BVar`'s `u32`, `Let`'s `bool`) lowers normally through
/// `convert_ty_inner`. THIS is the mechanism that dodges the 464 MB blow-up: a
/// recursive/nominal child is an O(1) by-name ref, never a full re-expansion.
/// SOUNDNESS: a by-name datatype reference asserts nothing — it is a sort marker
/// only (see `Ty::Datatype`'s doc).
fn datatype_child_field_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    field_ty: ty::Ty<'tcx>,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    let core = peel_transparent_pointers(tcx, field_ty);
    match core.kind() {
        TyKind::Adt(core_def, _) => {
            recursive_datatype_ref(&crate::safe_def_path_str(tcx, core_def.did()))
        }
        _ => convert_ty_inner(tcx, field_ty, ctx),
    }
}

/// Lever A step 2 — lower the kernel universe-`Level` enum to a native SMT-LIB
/// `Ty::Datatype` with its real five constructors: `Zero` (no fields), `Succ`
/// (one `Level`), `Max`/`IMax` (two `Level`), `Param` (one opaque `Name`). The
/// recursive `Level` children (stored behind `Arc<Level>` = `LevelArc`) model as
/// by-name datatype self-references (see `level_field_ty`), so the datatype is
/// finitely declarable in the standard datatype theory. This REPLACES the
/// recursive-ADT `Unsupported` degrade for `Level` ONLY (def-path gated).
///
/// SOUNDNESS: a datatype declaration introduces only the standard, sound
/// constructor/selector/tester/injectivity/acyclicity axioms; a fresh
/// `Level`-sorted constant is unconstrained, so it can never vacuously discharge
/// an obligation (false-prove). Faithful lowering — real variant structure, not a
/// stub.
fn lower_level_datatype<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    name: &str,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    lower_adt_as_datatype(tcx, ty, adt_def, args, name, ctx)
}

/// Lever A step 5 — lower the kernel `ExprKind` enum to a native recursive
/// `Ty::Datatype` with one constructor per variant (BVar/Sort/Const/App/Lam/Pi/
/// Let/Lit/Proj/MData/SProp/Squash/Cubical*/ZFC*). Recursive `Arc<Expr>` children
/// and `Level`/`Name`/`Literal`/`BinderData` payloads model as BY-NAME datatype
/// references (see `datatype_child_field_ty`), so the produced tree is O(variants)
/// with NO expansion of the Expr/ExprKind cluster. This REPLACES the recursive-ADT
/// `Unsupported`/produced-node-budget degrade for `ExprKind` ONLY (def-path gated).
/// SOUNDNESS: a datatype declaration introduces only the standard sound
/// constructor/selector/tester/injectivity/acyclicity axioms; a fresh
/// `ExprKind`-sorted constant is unconstrained, so it can never vacuously discharge
/// an obligation. Faithful lowering — the real variant structure, not a stub.
fn lower_exprkind_datatype<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    name: &str,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    lower_adt_as_datatype(tcx, ty, adt_def, args, name, ctx)
}

/// Lever A step 5 — lower the kernel `Expr` struct to a single-constructor
/// `Ty::Datatype` (a struct is a one-variant ADT in rustc's model) whose `kind`
/// field is a by-name `ExprKind` reference and whose `meta` field is an opaque
/// `ExprMeta` datatype reference. The by-name `kind` ref is the OTHER half of the
/// Expr/ExprKind mutual recursion — with both refs by-name, neither type expands
/// the other, so the cluster stays finitely declarable. Def-path gated to `Expr`.
/// SOUNDNESS: identical to `lower_exprkind_datatype` — a sound datatype
/// declaration, faithful single-constructor structure.
fn lower_expr_datatype<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    name: &str,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    lower_adt_as_datatype(tcx, ty, adt_def, args, name, ctx)
}

/// Lever A — the shared core that lowers ANY nominal ADT (enum OR struct) to a
/// native SMT-LIB `Ty::Datatype`: one constructor per `adt_def.variants()` entry
/// (a struct yields exactly one, named after the struct), each constructor's
/// fields modeled by `datatype_child_field_ty` (recursive/nominal children →
/// by-name refs, scalars → their concrete sort). Backs `lower_level_datatype`
/// (step 2) and `lower_expr_datatype`/`lower_exprkind_datatype` (step 5).
///
/// The by-name child refs keep the produced tree O(variants), so the
/// mutually-recursive Expr/ExprKind/Level cluster is finitely declarable and
/// never blows up (the 464 MB `Ty::Adt` expansion is dodged). SOUNDNESS: a
/// datatype declaration introduces only the standard sound datatype-theory
/// axioms; a fresh datatype-sorted constant is unconstrained.
fn lower_adt_as_datatype<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    name: &str,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    // Back-edge guard (defensive): if this type is already being lowered on this
    // walk, emit the by-name self-reference rather than re-expanding. In practice
    // `datatype_child_field_ty` peels recursive children to refs WITHOUT
    // re-entering, so the type is never pushed twice — this only backstops an
    // unexpected reach.
    if ctx.adt_stack.contains(&ty) {
        return recursive_datatype_ref(name);
    }
    ctx.adt_stack.push(ty);
    let mut variants: Vec<(String, Vec<(String, TrustTy)>)> = Vec::new();
    for variant in adt_def.variants().iter() {
        let mut variant_fields: Vec<(String, TrustTy)> = Vec::new();
        for field in variant.fields.iter() {
            let modeled =
                datatype_child_field_ty(tcx, field.ty(tcx, args).skip_normalization(), ctx);
            variant_fields.push((field.name.to_string(), modeled));
        }
        variants.push((variant.name.to_string(), variant_fields));
    }
    ctx.adt_stack.pop();
    TrustTy::Datatype { name: name.to_string(), variants }
}

fn lower_enum_adt<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    name: &str,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    if ctx.adt_stack.contains(&ty) {
        // Lever A (recursive-enum back-edge): the enum re-enters itself at a
        // variant field (e.g. `Expr` reached through a variant's `Box<Expr>`).
        // Emit a BY-NAME datatype reference rather than poisoning the enclosing
        // type to `Unsupported`. The OUTER (first) occurrence — already on the
        // stack — carries the full flat `Ty::Adt` (`__tag` + `__v{v}_…`) shape the
        // existing enum/discriminant machinery understands; this back-edge only
        // needs a modeled SMT sort so the field's place resolves a sort and no
        // longer goes Unknown. SOUNDNESS: a datatype reference asserts nothing.
        return recursive_datatype_ref(name);
    }
    // Lever A (field compaction gate) — mirror the struct path (`cap_fields =
    // !ctx.adt_stack.is_empty()` above): compact oversized variant fields ONLY
    // inside a recursive/nested lowering. At the TOP level (empty stack — the
    // local's own declared enum type, e.g. `Result<T, CheckError>`), keep the
    // exact flat expansion so a small non-recursive payload enum stays a real
    // `Ty::Adt` the native bridge can construct/project/match — an
    // unconditional cap here compacted such payloads to by-name `Ty::Datatype`
    // references, regressing whole functions to Unknown in the native lane.
    // The produced-node budget below still backstops any genuine blow-up, and
    // the recursive/nested cases (the OOM source) still compact.
    let cap_fields = !ctx.adt_stack.is_empty();
    ctx.adt_stack.push(ty);

    let mut fields = Vec::new();
    // 1. Add discriminant
    fields.push(("__tag".to_string(), TrustTy::Int { width: pointer_width(tcx), signed: true }));

    // Trust: PHASE 4 — build the per-variant constructor view ALONGSIDE the
    // existing flattened union `fields`. Each `VariantDef` carries the variant's
    // real discriminant tag (the value a `SwitchInt` compares against) plus its
    // OWN field list (each variant's fields named by their source name, or the
    // positional index for tuple variants), so `trust-clean` can reflect a real
    // multi-constructor inductive. The flattened `fields` view below is RETAINED
    // verbatim so no pre-P4 consumer (sort lookup, field projection) changes.
    let mut variants: Vec<trust_types::VariantDef> = Vec::new();
    // Trust (B3-1): a compacted (by-name-ref) variant field disqualifies the
    // faithful first-class spelling — the def would not be structurally equal
    // to the producer's.
    let mut compacted = false;

    // 2. Flatten all variants (existing union view) + populate per-variant defs.
    for (v_idx, variant) in adt_def.variants().iter_enumerated() {
        // verifier-perf (produced-node budget): bail the WHOLE enum to the
        // fail-closed recursive-ADT marker once the per-function produced-tree size
        // crosses the budget. This is the load-bearing cap for the
        // `Ty::clone`-in-the-flattened-fields-loop explosion (each `field_ty.clone()`
        // below deep-copies a recursive `Ty::Adt`, and a mutually-recursive enum
        // cluster multiplies these into a ~464 MB tree that OOM-kills extraction). By
        // bailing BEFORE accumulating more variants, the enum's retained size is
        // bounded. SOUNDNESS: DROP-ONLY — the marker carries no modeled SMT sort, so a
        // value USE still fails closed; never a false PROVE. See
        // `MAX_TYPE_LOWERING_PRODUCED_NODES`.
        if ctx.produced_nodes > ctx.produced_budget {
            ctx.adt_stack.pop();
            return produced_budget_degraded_leaf();
        }
        let mut variant_fields: Vec<(String, TrustTy)> = Vec::new();
        for field in &variant.fields {
            let mut field_ty = convert_ty_inner(tcx, field.ty(tcx, args).skip_normalization(), ctx);
            // Lever A (field compaction): a recursive enum reached through `Arc`/
            // `Box` (clean-kernel's `Expr`/`ExprKind`/`Level`) has variant fields
            // that flatten — via Arc/ArcInner/Atomic/UnsafeCell wrappers — into `Ty`
            // subtrees of HUNDREDS-to-THOUSANDS of nodes. COMPACT any oversized
            // field subtree to its by-name datatype reference so the ENCLOSING enum
            // stays MODELED (a real `Ty::Adt` whose fat field is now a small
            // datatype-sort marker) instead of bailing the whole enum to the
            // fail-closed `produced_budget_degraded_leaf` — which is exactly what
            // unlocks the Lever-A datatype-sort coverage win. SOUNDNESS: a compacted
            // field is a modeled, fact-free datatype sort (see
            // `compact_oversized_field`); only precision vs. tractability trades off,
            // never soundness, and the small scalar payloads keep full detail.
            if cap_fields
                && ty_node_count(&field_ty, MAX_DATATYPE_FIELD_NODES + 1) > MAX_DATATYPE_FIELD_NODES
            {
                field_ty = compact_oversized_field(&field_ty);
                compacted = true;
            }
            // verifier-perf (produced-node budget): charge the flattened-view clone we
            // are about to make (the `field_ty.clone()` deep-copies the produced
            // subtree — the actual OOM allocation). Once the budget is crossed, stop
            // duplicating fat subtrees and bail the enum to the fail-closed marker.
            // (A compacted field is now tiny, so this rarely trips for the recursive
            // cluster; it remains a backstop for a genuinely unbounded expansion.)
            let headroom = ctx.produced_budget.saturating_sub(ctx.produced_nodes).saturating_add(1);
            ctx.produced_nodes =
                ctx.produced_nodes.saturating_add(produced_node_count(&field_ty, headroom));
            if ctx.produced_nodes > ctx.produced_budget {
                ctx.adt_stack.pop();
                return produced_budget_degraded_leaf();
            }
            // Flattened union view (unchanged, pre-P4 shape).
            fields.push((format!("__v{}_{}", v_idx.as_usize(), field.name), field_ty.clone()));
            // Trust (B3-2c E6): under the FAITHFUL lane, a drop-free-ZST field
            // collapses to the canonical TrustTy::Unit in the PER-VARIANT view —
            // the lockstep mirror of the producer wall's forced Ty::Unit respell,
            // tested on the GROUND-TRUTH rustc type. The flattened `fields` view
            // above keeps the real spelling (the flat lane + every verifier lane
            // are byte-identical; eligible enums never consume the flat view).
            let variant_field_ty = if faithful_scalars()
                && extractor_drop_free_zst(tcx, field.ty(tcx, args).skip_normalization(), ctx)
            {
                TrustTy::Unit
            } else {
                field_ty
            };
            // Per-variant constructor field, named by the field's own name.
            variant_fields.push((field.name.to_string(), variant_field_ty));
        }
        // The variant's discriminant: the concrete tag rustc assigns (honours
        // explicit `= N` discriminants and `#[repr(iN)]`). `val` is a `u128`
        // bit pattern; widen into the `i128` the `VariantDef` stores.
        let discriminant = adt_def.discriminant_for_variant(tcx, v_idx).val as i128;
        variants.push(trust_types::VariantDef {
            name: variant.name.to_string(),
            discriminant,
            fields: variant_fields,
        });
    }

    ctx.adt_stack.pop();

    // Trust: enum-disc-full-native — classify whether a `Discriminant` read on
    // this enum yields a DENSE tag in `[min_disc, max_disc]` (Direct tag
    // encoding), which is the ONLY case where the native -full bridge may
    // soundly `Assume(min_disc <= disc <= max_disc)` over the extracted tag (so
    // `arr[e as usize]` proves). FAIL-CLOSED (`false`) for EVERY other layout:
    //   - `Variants::Multiple { Niche }` — niche-encoded enums (`Option<&T>`,
    //     `Result<bool, ()>`, `Option<NonZeroU8>`): the discriminant read does
    //     NOT recover a clean `0..n` tag, so the `[min,max]` interval over the
    //     declared discriminants is NOT a sound bound on the read value.
    //   - `Variants::Single` / `Variants::Empty` — a single- or zero-variant
    //     enum has no real tag to bound (and a fieldless 1-variant enum's
    //     "discriminant" read is a constant; bounding it buys nothing).
    //   - layout query Err, or `typing_env == None` — we cannot consult the
    //     layout, so we MUST NOT synthesize the fact.
    // NOTE: this flag is ONLY consulted by the native bridge's `Discriminant`
    // read arm; the flattened `fields` (with `__tag`) and `variants` above are
    // UNCHANGED, so `SetDiscriminant` (the WRITE path) still finds `__tag`.
    let disc_index_safe = enum_discriminant_index_safe(tcx, ty, ctx);

    // Construct directly (not via `adt_enum_with_disc_safety`, which re-derives a
    // dedup'd `fields` union): `lower_enum_adt` builds the RICHER flattened view
    // (`__tag` + per-variant `__v{idx}_{name}` fields) the discriminant/
    // projection machinery and `SetDiscriminant` depend on. Keep `fields`
    // verbatim; thread in ONLY the new `disc_index_safe` classification.
    // Trust (B3-1, RFC TRUST_IR_V2): the FAITHFUL-lane first-class-enum marker.
    // `Some` ONLY on the differential's faithful extraction AND for enums
    // ELIGIBLE for the format's EnumDef spelling — mirroring the THIR
    // producer's `register_enum` gates so both sides register structurally
    // EQUAL defs: every variant field a seedable scalar (ints incl.
    // pointer-width / bool / float — the producer's seed_constant set), no
    // compacted field, a DIRECT tag encoding (`disc_index_safe` — the G1/G2
    // fail-close: niche `Option<&T>`, untagged and layout-exotic enums keep
    // the flat spelling), and a mappable repr hint (`repr(i128)` declines,
    // exactly like the producer's `enum_repr_hint`). The hint itself is
    // CARRIED (as `Some(inner)`) because the producer pins it on its EnumDef —
    // omitting it would make structurally-equal enums disagree on
    // `canonical_tag_repr` (a false NotRun). The legacy lane and every
    // ineligible enum get `None` — byte-identical historical behavior.
    let eligible = faithful_scalars()
        && !compacted
        && disc_index_safe
        && !variants.is_empty()
        && variants.iter().all(|v| {
            v.fields.iter().all(|(_, t)| {
                matches!(
                    t,
                    TrustTy::Int { .. }
                        | TrustTy::Bool
                        | TrustTy::Float { .. }
                        | TrustTy::PtrSizedInt { .. }
                        // Trust (B3-2c E6): the canonical drop-free-ZST collapse —
                        // only ever minted by the faithful-lane respell above.
                        | TrustTy::Unit
                )
            })
        });
    let faithful_enum_repr = if eligible { extractor_enum_repr_hint(adt_def) } else { None };
    // Trust (B3-3): the concrete enum layout twin — filled ONLY alongside the
    // faithful first-class spelling (an ineligible enum keeps the flat view,
    // where no trust-ir EnumDef exists to carry a descriptor) and only when
    // the T3 layout gates hold. Decline rules are the LOCKSTEP MIRROR of the
    // THIR producer's `enum_layout_descriptor` fill (trust-thir-lower
    // lib.rs::register_enum): a drifted rule shows up as a descriptor
    // presence/content asymmetry in `tys_agree` (coverage-only Err, never a
    // manufactured divergence), which is the drift tripwire.
    let enum_layout = if eligible
        && !ty.has_non_region_param()
        && !ty.has_non_region_infer()
        && !ty.has_opaque_types()
    {
        ctx.typing_env
            .and_then(|te| tcx.layout_of(te.as_query_input(ty)).ok())
            .and_then(|l| extractor_enum_layout_info(adt_def, &l))
            .map(Box::new)
    } else {
        None
    };
    // Trust: W19 — this arm is reached ONLY for a genuine enum (`lower_enum_adt` is
    // called after the `!is_struct() && !is_union()` guard), so stamp `Enum`. The
    // setter recognizer declines it (an enum is outside the single-anonymous-
    // constructor setter fragment).
    TrustTy::Adt {
        name: name.to_string(),
        fields,
        variants,
        disc_index_safe,
        faithful_enum_repr,
        layout: None,
        enum_layout,
        adt_kind: Some(trust_types::AdtKind::Enum),
    }
}

/// Trust (B3-3): map a rustc enum layout onto the trust-ir-free
/// [`trust_types::EnumLayoutInfo`] twin, or decline (`None`) when the layout
/// is not expressible in the v31 descriptor grammar. Declines (lockstep with
/// the producer fill): `Variants::Single`/`Empty` (no tag lane to describe)
/// and a tag/niche scalar that is not a mappable integer (float or i128;
/// `Pointer` pins to U64 on the 64-bit reference target).
fn extractor_enum_layout_info<'tcx>(
    adt_def: ty::AdtDef<'tcx>,
    l: &rustc_middle::ty::layout::TyAndLayout<'tcx>,
) -> Option<trust_types::EnumLayoutInfo> {
    use rustc_abi::{TagEncoding, Variants};
    let Variants::Multiple { tag, tag_encoding, tag_field, variants: vlayouts } =
        l.layout.variants()
    else {
        return None;
    };
    // Bounds-check BEFORE `FieldsShape::offset`, which PANICS rather than
    // returning an Option — an out-of-range tag_field must decline the
    // descriptor, never abort the compile (lockstep with the producer's
    // `producer_enum_layout_descriptor`).
    if tag_field.as_usize() >= l.layout.fields().count() {
        return None;
    }
    let lane_offset = l.layout.fields().offset(tag_field.as_usize()).bytes();
    let lane_ty = scalar_repr_hint(*tag)?;
    let encoding = match tag_encoding {
        TagEncoding::Direct => trust_types::EnumTagEncodingInfo::Direct {
            tag_offset: lane_offset,
            // Check carrier: the bridge declines the copy-through when this
            // disagrees with the canonical tag repr it computes on the final
            // EnumDef (the descriptor's Direct tag lane is normatively sized
            // at canonical width — a rustc-widened tag must not mint a
            // descriptor whose normative claim is wrong).
            tag_ty: lane_ty,
        },
        TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
            trust_types::EnumTagEncodingInfo::Niche {
                untagged_variant: untagged_variant.as_u32(),
                niche_variants_start: niche_variants.start.as_u32(),
                niche_variants_end: niche_variants.last.as_u32(),
                niche_start: *niche_start,
                niche_offset: lane_offset,
                niche_ty: lane_ty,
            }
        }
    };
    let mut variant_field_offsets = Vec::with_capacity(adt_def.variants().len());
    for (vidx, variant) in adt_def.variants().iter_enumerated() {
        let vl = vlayouts.get(vidx)?;
        // `field_offsets` is DECLARATION-indexed (the memory permutation is a
        // separate private field) — read straight through.
        // `.get()`, not `[]`: a variant layout can carry FEWER offsets than
        // the variant has fields (uninhabited / degenerate variants); an
        // IndexVec index would panic. Decline the whole descriptor.
        let offs: Option<Vec<u64>> = (0..variant.fields.len())
            .map(|i| vl.field_offsets.get(rustc_abi::FieldIdx::from_usize(i)).map(|o| o.bytes()))
            .collect();
        variant_field_offsets.push(offs?);
    }
    Some(trust_types::EnumLayoutInfo {
        encoding,
        size: l.size.bytes(),
        align: l.align.abi.bytes(),
        variant_field_offsets,
    })
}

/// The width/signedness hint for a rustc tag/niche scalar: integers map
/// directly, `Pointer` pins to the 64-bit target (U64 — same rule as
/// `IntegerType::Pointer` in `extractor_enum_repr_hint`), floats and i128
/// decline.
fn scalar_repr_hint(s: rustc_abi::Scalar) -> Option<trust_types::EnumReprHint> {
    use rustc_abi::{Integer, Primitive};
    use trust_types::EnumReprHint as R;
    Some(match s.primitive() {
        Primitive::Int(i, signed) => match (i, signed) {
            (Integer::I8, true) => R::I8,
            (Integer::I8, false) => R::U8,
            (Integer::I16, true) => R::I16,
            (Integer::I16, false) => R::U16,
            (Integer::I32, true) => R::I32,
            (Integer::I32, false) => R::U32,
            (Integer::I64, true) => R::I64,
            (Integer::I64, false) => R::U64,
            (Integer::I128, _) => return None,
        },
        Primitive::Pointer(_) => R::U64,
        Primitive::Float(_) => return None,
    })
}

/// Trust (B3-1): the `#[repr]` tag hint for the faithful first-class enum
/// spelling — mirrors the THIR producer's `enum_repr_hint` EXACTLY (pointer-
/// width reprs pin to the 64-bit target; `repr(i128)`/`repr(u128)` decline the
/// whole enum). Outer `None` = ineligible; `Some(inner)` = eligible with the
/// hint's presence/absence carried verbatim.
fn extractor_enum_repr_hint(adt: ty::AdtDef<'_>) -> Option<Option<trust_types::EnumReprHint>> {
    use rustc_abi::{Integer, IntegerType};
    use trust_types::EnumReprHint as R;
    Some(match adt.repr().int {
        None => None,
        Some(IntegerType::Pointer(signed)) => Some(if signed { R::I64 } else { R::U64 }),
        Some(IntegerType::Fixed(i, signed)) => Some(match (i, signed) {
            (Integer::I8, true) => R::I8,
            (Integer::I8, false) => R::U8,
            (Integer::I16, true) => R::I16,
            (Integer::I16, false) => R::U16,
            (Integer::I32, true) => R::I32,
            (Integer::I32, false) => R::U32,
            (Integer::I64, true) => R::I64,
            (Integer::I64, false) => R::U64,
            (Integer::I128, _) => return None,
        }),
    })
}

/// Trust: enum-disc-full-native — `true` iff `ty` is an enum whose layout uses
/// a DIRECT tag encoding over `≥ 2` variants, so its `Discriminant` read yields
/// a dense discriminant the native bridge may bound. FAIL-CLOSED for niche
/// encodings, single/empty layouts, a missing `typing_env`, or a layout error.
/// Trust (B3-2c E6): is this rustc type a DROP-FREE ZST — the extractor mirror of
/// the THIR producer's `is_drop_free_zst` admission predicate. Ground-truth
/// layout test (never the mapped spelling); no typing env / generic / layout
/// Err / drop-bearing all fail closed. Used ONLY under `faithful_scalars()` to
/// collapse a ZST enum-variant field (`()` or a unit struct like `fmt::Error`)
/// to the canonical `TrustTy::Unit` — the same forced respell the producer's
/// `register_enum` wall mints, so both sides' EnumDefs stay structurally equal.
fn extractor_drop_free_zst<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    ctx: &TyLoweringCtx<'tcx>,
) -> bool {
    let Some(typing_env) = ctx.typing_env else {
        return false;
    };
    if ty.has_non_region_param() {
        return false;
    }
    let Ok(layout) = tcx.layout_of(typing_env.as_query_input(ty)) else {
        return false;
    };
    layout.is_zst() && !ty.needs_drop(tcx, typing_env)
}

fn enum_discriminant_index_safe<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    ctx: &TyLoweringCtx<'tcx>,
) -> bool {
    // GATE: must have the body's typing env to query layout. No env ⇒ fail-closed.
    let Some(typing_env) = ctx.typing_env else {
        return false;
    };
    // GATE: a still-generic enum type has no concrete layout. Fail-closed.
    if ty.has_non_region_param() {
        return false;
    }
    // GATE: layout query must succeed. Any Err ⇒ fail-closed.
    let Ok(layout) = tcx.layout_of(typing_env.as_query_input(ty)) else {
        return false;
    };
    // GATE-NICHE: Direct tag encoding only. `Niche` (Option<&T>, Result<bool,()>,
    // Option<NonZeroU8>), `Single`, and `Empty` are all fail-closed. Match on a
    // REFERENCE — `LayoutData::variants` is an owned `Variants` reached through a
    // `Deref`, so a by-value `matches!` would try to move out of the layout.
    matches!(&layout.variants, Variants::Multiple { tag_encoding: TagEncoding::Direct, .. })
}

/// Get bit width of an IntTy.
pub(crate) fn int_width_from_int_ty(int_ty: &rustc_ast_ir::IntTy, tcx: TyCtxt<'_>) -> u32 {
    match int_ty {
        rustc_ast_ir::IntTy::Isize => pointer_width(tcx),
        rustc_ast_ir::IntTy::I8 => 8,
        rustc_ast_ir::IntTy::I16 => 16,
        rustc_ast_ir::IntTy::I32 => 32,
        rustc_ast_ir::IntTy::I64 => 64,
        rustc_ast_ir::IntTy::I128 => 128,
    }
}

/// Get bit width of a UintTy.
pub(crate) fn uint_width_from_uint_ty(uint_ty: &rustc_ast_ir::UintTy, tcx: TyCtxt<'_>) -> u32 {
    match uint_ty {
        rustc_ast_ir::UintTy::Usize => pointer_width(tcx),
        rustc_ast_ir::UintTy::U8 => 8,
        rustc_ast_ir::UintTy::U16 => 16,
        rustc_ast_ir::UintTy::U32 => 32,
        rustc_ast_ir::UintTy::U64 => 64,
        rustc_ast_ir::UintTy::U128 => 128,
    }
}

/// Get the pointer width in bits for the target.
fn pointer_width(tcx: TyCtxt<'_>) -> u32 {
    tcx.data_layout.pointer_size().bits() as u32
}

#[cfg(test)]
mod tests {
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

    /// A `CanonicalCutKey` standing for one type. Only the ordering matters, so
    /// the rendered path carries the whole discriminating weight here.
    fn test_key(name: &str) -> CanonicalCutKey {
        (name.matches("::").count(), name.to_string(), 0, 0)
    }

    fn cut_labels(edges: &[Vec<usize>], names: &[&str], nodes: &[usize]) -> Vec<String> {
        let mut picked: Vec<String> = greedy_feedback_vertex_set(edges, &mut |node| {
            test_key(names[nodes[node]])
        })
        .into_iter()
        .map(|slot| names[nodes[slot]].to_string())
        .collect();
        picked.sort();
        picked
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
        let cut = greedy_feedback_vertex_set(&edges, &mut |node| {
            key_requests += 1;
            test_key(&format!("n{node}"))
        });
        assert!(cut.is_empty(), "acyclic graph must have an empty cut set: {cut:?}");
        assert_eq!(key_requests, 0, "an acyclic graph must not render a single def path");
    }

    #[test]
    fn greedy_fvs_cuts_a_self_loop() {
        // `struct S { next: Box<S> }` reduces to a single node with a self edge.
        let edges = vec![vec![0]];
        let cut = greedy_feedback_vertex_set(&edges, &mut |_| test_key("krate::S"));
        assert_eq!(cut, vec![0]);
    }

    #[test]
    fn greedy_fvs_cuts_the_shallowest_def_path_in_the_cycle() {
        // The measured `xor_all` cycle: Tree ↔ Arc ↔ NonNull ↔ ArcInner. The cut
        // must land on `Tree` — the type the cycle is ABOUT — not on an std
        // container internal, so the marker names something the consumer can
        // recognize.
        let names = ["xor_all::Tree", "std::sync::Arc", "std::ptr::NonNull", "alloc::sync::ArcInner"];
        let edges = vec![vec![1], vec![2], vec![3], vec![0]];
        let nodes: Vec<usize> = (0..4).collect();
        assert_eq!(cut_labels(&edges, &names, &nodes), vec!["xor_all::Tree".to_string()]);
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
        let names = [
            "e::EntryBoth",
            "a::Alpha",
            "zzz::AlphaBox",
            "e::EntryAlpha",
            "e::EntryBeta",
            "b::Beta",
            "zzz::BetaMid",
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
            let reachable_names: Vec<String> =
                nodes.iter().map(|n| names[*n].to_string()).collect();
            let expected: Vec<String> = global
                .iter()
                .filter(|name| reachable_names.contains(name))
                .cloned()
                .collect();

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

    /// A cut point may never be memoized: its lowering is the full definition at
    /// the walk's root and the by-name marker everywhere else, and the memo is
    /// keyed on the type alone. `TyLoweringCtx` must therefore start with an empty
    /// cut set, so an ordinary (acyclic) lowering keeps using the cache.
    #[test]
    fn ty_lowering_context_starts_with_an_empty_canonical_cut() {
        let ctx = TyLoweringCtx::default();
        assert!(ctx.canonical_cut.is_empty());
    }
}
