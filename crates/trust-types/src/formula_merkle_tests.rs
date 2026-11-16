// Tests for crate::formula_merkle.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use proptest::prelude::*;

use super::*;
use crate::Symbol;
use crate::determinism::query_size;

fn var(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

fn symvar(name: &str) -> Formula {
    Formula::SymVar(Symbol::intern(name), Sort::Int)
}

fn int(n: i128) -> Formula {
    Formula::Int(n)
}

fn add(a: Formula, b: Formula) -> Formula {
    Formula::Add(Box::new(a), Box::new(b))
}

fn gt(a: Formula, b: Formula) -> Formula {
    Formula::Gt(Box::new(a), Box::new(b))
}

fn forall(names: &[&str], body: Formula) -> Formula {
    let bindings: Vec<(&str, Sort)> = names.iter().map(|name| (*name, Sort::Int)).collect();
    Formula::forall(&bindings, body)
}

fn exists(names: &[&str], body: Formula) -> Formula {
    let bindings: Vec<(&str, Sort)> = names.iter().map(|name| (*name, Sort::Int)).collect();
    Formula::exists(&bindings, body)
}

fn digest(f: &Formula) -> FormulaDigest {
    formula_digest(f).expect("a test formula has a Merkle digest")
}

fn alpha(f: &Formula) -> FormulaDigest {
    formula_bound_alpha_digest(f).expect("a test formula has a bound-alpha digest")
}

/// `n_{i+1} = n_i + n_i`, built bottom-up in `dag`: a DAG of `depth + 1` nodes
/// whose tree has `2^(depth + 1) - 1`.
fn diamond_chain(dag: &mut FormulaDag, depth: usize) -> NodeId {
    let template = add(int(0), int(0));
    let mut node = dag.intern(&var("x"));
    for _ in 0..depth {
        node = dag.mk_like(&template, &[node, node]).expect("two children for Add");
    }
    node
}

#[test]
fn the_domain_and_one_digest_are_pinned() {
    assert_eq!(FORMULA_MERKLE_DOMAIN, b"trust-formula-merkle/v1\0");
    // The module docs' preimage, computed by hand: `x` is
    // SHA-256(DOMAIN ‖ 0x00 ‖ lp(`{"Var":["x","Int"]}`) ‖ u64le(0)), `1` likewise over
    // `{"Int":1}`, and the root over `{"Add":[{"Bool":true},{"Bool":true}]}`, arity 2
    // and the two child digests. Moving it means the encoding moved: bump the domain.
    assert_eq!(
        digest(&add(var("x"), int(1))).to_hex(),
        "ecaa7712acd6805a54a2e0bbc93dcaa27c7e02768ebf2ddd82ee59c7a9bd0bbd"
    );
}

#[test]
fn a_digest_is_a_function_of_the_tree_alone() {
    // I5: no node id, brand, insertion order or degree of sharing reaches it.
    let shared = add(var("x"), symvar("y"));
    let f = Formula::And(vec![gt(shared.clone(), int(0)), gt(shared.clone(), int(1)), shared]);
    let fresh = digest(&f);

    let mut busy = FormulaDag::new();
    for junk in [gt(int(7), var("z")), var("y"), int(1), add(var("x"), int(9))] {
        busy.intern(&junk);
    }
    let busy_root = busy.intern(&f);
    assert_eq!(MerkleCache::new().digest(&busy, busy_root).expect("digest"), fresh);

    let mut owned = FormulaDag::new();
    let owned_root = owned.intern_owned(f.clone());
    assert_eq!(MerkleCache::new().digest(&owned, owned_root).expect("digest"), fresh);

    let copy = busy.clone();
    let copy_root = copy.id_at(busy_root.index()).expect("a clone keeps every index");
    assert_eq!(MerkleCache::new().digest(&copy, copy_root).expect("digest"), fresh);
}

#[test]
fn equal_digests_exactly_for_equal_trees() {
    let corpus = vec![
        var("x"),
        symvar("x"),
        Formula::Var("x".into(), Sort::Bool),
        Formula::Var("y".into(), Sort::Int),
        int(1),
        Formula::UInt(1),
        Formula::BitVec { value: 1, width: 8 },
        Formula::BitVec { value: 1, width: 16 },
        int(i128::MAX),
        int(i128::MIN),
        Formula::BvAdd(Box::new(var("x")), Box::new(var("x")), 8),
        Formula::BvAdd(Box::new(var("x")), Box::new(var("x")), 16),
        Formula::And(vec![]),
        Formula::Or(vec![]),
        Formula::And(vec![var("x")]),
        Formula::And(vec![var("x"), var("y")]),
        Formula::And(vec![var("y"), var("x")]),
        Formula::And(vec![var("x"), var("y"), var("y")]),
        Formula::And(vec![Formula::And(vec![var("x"), var("y")])]),
        Formula::And(vec![Formula::And(vec![var("x")]), var("y")]),
        add(var("x"), var("y")),
        add(var("y"), var("x")),
        Formula::Sub(Box::new(var("x")), Box::new(var("y"))),
        forall(&["x"], gt(var("x"), int(0))),
        exists(&["x"], gt(var("x"), int(0))),
        forall(&["z"], gt(var("z"), int(0))),
        forall(&["x", "y"], gt(var("x"), var("y"))),
        forall(&["y", "x"], gt(var("x"), var("y"))),
        Formula::Pred(Symbol::intern("merkle_test_p"), vec![var("x")]),
        Formula::Pred(Symbol::intern("merkle_test_q"), vec![var("x")]),
        Formula::FnApp { func: "f".into(), args: vec![var("x")], sort: Sort::Int },
        Formula::FnApp { func: "f".into(), args: vec![var("x")], sort: Sort::Bool },
    ];
    for (i, f) in corpus.iter().enumerate() {
        assert_eq!(digest(f), digest(&f.clone()), "{f:?}");
        for g in &corpus[i + 1..] {
            assert_ne!(digest(f), digest(g), "{f:?} and {g:?} are different trees");
        }
    }
}

#[test]
fn the_memo_serializes_each_reachable_node_once() {
    // A tree of 2^65 - 1 nodes, a DAG of 65.
    let mut dag = FormulaDag::new();
    let root = diamond_chain(&mut dag, 64);
    let mut cache = MerkleCache::new();
    let first = cache.digest(&dag, root).expect("digest");
    assert_eq!(cache.stats().payloads_serialized, 65);
    assert_eq!(cache.stats().merkle_nodes, 65);
    assert_eq!(cache.digest(&dag, root).expect("digest"), first);
    assert_eq!(cache.bound_alpha_digest(&dag, root).expect("alpha"), first, "quantifier-free");
    assert_eq!(cache.stats().payloads_serialized, 65, "nothing is serialized twice");

    // The tree it denotes, where a tree can be built: the same digest.
    let mut small = FormulaDag::new();
    let small_root = diamond_chain(&mut small, 10);
    let tree = small.expand(small_root);
    assert_eq!(MerkleCache::new().digest(&small, small_root).expect("digest"), digest(&tree));
}

#[test]
fn a_cache_serves_one_dag() {
    let mut a = FormulaDag::new();
    let a_root = a.intern(&add(var("x"), int(1)));
    let mut b = FormulaDag::new();
    let b_root = b.intern(&add(var("x"), int(1)));
    let mut cache = MerkleCache::new();
    cache.digest(&a, a_root).expect("the first DAG binds the cache");
    assert_eq!(cache.digest(&b, b_root), Err(MerkleError::OtherDag { node: b_root }));
    assert!(matches!(cache.digest(&a, b_root), Err(MerkleError::UnknownNode { .. })));
    let copy = a.clone();
    let copy_root = copy.id_at(a_root.index()).expect("same index");
    assert_eq!(cache.digest(&copy, copy_root), Err(MerkleError::OtherDag { node: copy_root }));
    // A grown DAG is the same DAG.
    let later = a.intern(&gt(var("x"), int(2)));
    assert_eq!(cache.digest(&a, later).expect("digest"), digest(&gt(var("x"), int(2))));
}

#[test]
fn deep_formulas_hash_without_recursion() {
    let depth = 200_000;
    let mut chain = gt(var("x"), var("free"));
    for _ in 0..depth {
        chain = Formula::Not(Box::new(chain));
    }
    let f = forall(&["x"], chain);
    let mut renamed_chain = gt(var("y"), var("free"));
    for _ in 0..depth {
        renamed_chain = Formula::Not(Box::new(renamed_chain));
    }
    let g = forall(&["y"], renamed_chain);
    let mut dag = FormulaDag::new();
    let (f_root, g_root) = (dag.intern(&f), dag.intern(&g));
    let mut cache = MerkleCache::new();
    assert_ne!(
        cache.digest(&dag, f_root).expect("digest"),
        cache.digest(&dag, g_root).expect("digest")
    );
    assert_eq!(
        cache.bound_alpha_digest(&dag, f_root).expect("alpha"),
        cache.bound_alpha_digest(&dag, g_root).expect("alpha"),
    );
    f.drop_iterative();
    g.drop_iterative();
}

#[test]
fn the_bound_alpha_digest_reads_through_bound_names_only() {
    let y = || var("y");
    // Renaming a bound variable: equal; the Merkle digests see the names.
    assert_eq!(
        alpha(&forall(&["x"], gt(var("x"), y()))),
        alpha(&forall(&["z"], gt(var("z"), y())))
    );
    assert_ne!(
        digest(&forall(&["x"], gt(var("x"), y()))),
        digest(&forall(&["z"], gt(var("z"), y())))
    );
    // Renaming a free variable, or capturing it: different.
    assert_ne!(
        alpha(&forall(&["x"], gt(var("x"), y()))),
        alpha(&forall(&["x"], gt(var("x"), var("w"))))
    );
    assert_ne!(alpha(&forall(&["x"], gt(var("x"), y()))), alpha(&forall(&["y"], gt(y(), y()))));
    // Shadowing: an occurrence denotes its innermost binder.
    let inner = forall(&["x"], forall(&["x"], gt(var("x"), int(0))));
    assert_eq!(alpha(&inner), alpha(&forall(&["a"], forall(&["b"], gt(var("b"), int(0))))));
    assert_ne!(alpha(&inner), alpha(&forall(&["a"], forall(&["b"], gt(var("a"), int(0))))));
    // One name bound in one place and free in another.
    let mixed = |bound: &str, outside: &str| {
        Formula::And(vec![forall(&[bound], gt(var(bound), int(0))), gt(var(outside), int(1))])
    };
    assert_eq!(alpha(&mixed("x", "x")), alpha(&mixed("z", "x")));
    assert_ne!(alpha(&mixed("x", "x")), alpha(&mixed("z", "z")));
    // The quantifier and the bound sorts are read; binding order is positional.
    assert_ne!(
        alpha(&forall(&["x"], gt(var("x"), y()))),
        alpha(&exists(&["x"], gt(var("x"), y())))
    );
    let as_bool = Formula::forall(&[("x", Sort::Bool)], gt(var("x"), y()));
    assert_ne!(alpha(&forall(&["x"], gt(var("x"), y()))), alpha(&as_bool));
    let xy = forall(&["x", "y"], gt(var("x"), y()));
    assert_eq!(alpha(&xy), alpha(&forall(&["a", "b"], gt(var("a"), var("b")))));
    assert_ne!(alpha(&xy), alpha(&forall(&["y", "x"], gt(var("x"), y()))));
    // A Var and a SymVar occurrence of one bound name stay apart (a missed merge).
    assert_ne!(
        alpha(&forall(&["x"], gt(var("x"), int(0)))),
        alpha(&forall(&["x"], gt(symvar("x"), int(0))))
    );
    // Quantifier-free: the bound-alpha digest is the Merkle digest.
    let plain = add(var("x"), y());
    assert_eq!(alpha(&plain), digest(&plain));
    assert_ne!(alpha(&forall(&["x"], plain.clone())), digest(&forall(&["x"], plain)));
}

#[test]
fn a_shared_subterm_is_read_in_each_binder_it_sits_under() {
    // One DAG node `x + y`, with `x` bound in the first body and `y` in the second.
    let t = add(var("x"), var("y"));
    let f =
        Formula::And(vec![forall(&["x"], gt(t.clone(), int(0))), forall(&["y"], gt(t, int(0)))]);
    let renamed = Formula::And(vec![
        forall(&["a"], gt(add(var("a"), var("y")), int(0))),
        forall(&["b"], gt(add(var("x"), var("b")), int(0))),
    ]);
    let other = Formula::And(vec![
        forall(&["a"], gt(add(var("a"), var("y")), int(0))),
        forall(&["b"], gt(add(var("b"), var("y")), int(0))),
    ]);
    assert_eq!(alpha(&f), alpha(&renamed));
    assert_ne!(alpha(&f), alpha(&other));
}

#[test]
fn a_repeated_binding_has_no_bound_alpha_digest() {
    let twice = Formula::Forall(
        vec![(Symbol::intern("x"), Sort::Int), (Symbol::intern("x"), Sort::Int)],
        Box::new(gt(var("x"), int(0))),
    );
    assert!(matches!(
        formula_bound_alpha_digest(&twice),
        Err(MerkleError::DuplicateBinding { ref name, .. }) if name == "x"
    ));
    assert!(formula_digest(&twice).is_ok(), "its Merkle digest is still the tree's");
}

#[test]
fn the_row_node_count_is_query_size_in_a_shared_context() {
    let shared = add(var("x"), var("y"));
    let rows: Vec<Vec<Formula>> = vec![
        vec![gt(shared.clone(), int(0))],
        vec![gt(shared.clone(), int(0)), gt(shared.clone(), int(1))],
        vec![forall(&["x"], gt(shared.clone(), var("x"))), shared.clone()],
        vec![Formula::And(vec![symvar("x"), var("x"), symvar("x")])],
        vec![int(1), int(1)],
    ];
    let mut context = FormulaDag::new();
    let mut tall = FormulaDag::new();
    let chain = diamond_chain(&mut tall, 12);
    context.intern(&tall.expand(chain));
    let roots: Vec<Vec<NodeId>> =
        rows.iter().map(|row| row.iter().map(|f| context.intern(f)).collect()).collect();
    for (row, roots) in rows.iter().zip(&roots) {
        let refs: Vec<&Formula> = row.iter().collect();
        assert_eq!(row_node_count(&context, roots).expect("count"), query_size(&refs), "{row:?}");
    }
    let chain_root = context.intern(&tall.expand(chain));
    assert_eq!(row_node_count(&context, &[chain_root]).expect("count"), 13);
    assert_eq!(row_node_count(&context, &[chain_root, chain_root]).expect("count"), 13);
    assert_eq!(row_node_count(&context, &[]).expect("count"), 0);
    let mut other = FormulaDag::new();
    let foreign = other.intern(&int(1));
    assert!(matches!(row_node_count(&context, &[foreign]), Err(DagError::UnknownNode { .. })));
}

// ── Properties ──────────────────────────────────────────────────────────────

const NAMES: [&str; 3] = ["a", "b", "c"];

fn leaf() -> impl Strategy<Value = Formula> {
    prop_oneof![
        prop::sample::select(NAMES.to_vec()).prop_map(var),
        prop::sample::select(NAMES.to_vec()).prop_map(symvar),
        (0i128..3).prop_map(Formula::Int),
    ]
}

fn bindings() -> impl Strategy<Value = Vec<(Symbol, Sort)>> {
    let sort = prop::sample::select(vec![Sort::Int, Sort::Bool]);
    prop_oneof![
        (prop::sample::select(NAMES.to_vec()), sort.clone())
            .prop_map(|(name, sort)| vec![(Symbol::intern(name), sort)]),
        (prop::sample::subsequence(NAMES.to_vec(), 2).prop_shuffle(), sort).prop_map(
            |(names, sort)| names
                .into_iter()
                .map(|name| (Symbol::intern(name), sort.clone()))
                .collect()
        ),
    ]
}

fn formula() -> impl Strategy<Value = Formula> {
    leaf().prop_recursive(5, 32, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| add(a, b)),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| gt(a, b)),
            inner.clone().prop_map(|a| Formula::Neg(Box::new(a))),
            prop::collection::vec(inner.clone(), 0..3).prop_map(Formula::And),
            (bindings(), inner.clone()).prop_map(|(b, body)| Formula::Forall(b, Box::new(body))),
            (bindings(), inner).prop_map(|(b, body)| Formula::Exists(b, Box::new(body))),
        ]
    })
}

/// A variable leaf with its name replaced.
fn rename_leaf(f: &Formula, to: &str) -> Formula {
    match f {
        Formula::Var(_, sort) => Formula::Var(to.into(), sort.clone()),
        Formula::SymVar(_, sort) => Formula::SymVar(Symbol::intern(to), sort.clone()),
        other => other.clone(),
    }
}

/// The reference reading of bound-variable alpha-equivalence: every bound name
/// replaced by its binder's de Bruijn LEVEL, spelled so it cannot be a free name.
fn level_normal(f: &Formula, env: &mut Vec<String>) -> Formula {
    match f {
        Formula::Var(..) | Formula::SymVar(..) => {
            let name = f.var_name().unwrap_or_default();
            match env.iter().rposition(|bound| bound == name) {
                Some(level) => rename_leaf(f, &format!("\u{1}{level}")),
                None => f.clone(),
            }
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let base = env.len();
            let renamed: Vec<(Symbol, Sort)> = bindings
                .iter()
                .enumerate()
                .map(|(i, (_, sort))| (Symbol::intern(&format!("\u{1}{}", base + i)), sort.clone()))
                .collect();
            env.extend(bindings.iter().map(|(sym, _)| sym.as_str().to_string()));
            let body = level_normal(body, env);
            env.truncate(base);
            if matches!(f, Formula::Forall(..)) {
                Formula::Forall(renamed, Box::new(body))
            } else {
                Formula::Exists(renamed, Box::new(body))
            }
        }
        other => other.clone().map_children(&mut |child| level_normal(&child, env)),
    }
}

/// `f` with every bound variable renamed to a fresh name, consistently.
fn rename_bound(f: &Formula, env: &mut Vec<(String, String)>, next: &mut usize) -> Formula {
    match f {
        Formula::Var(..) | Formula::SymVar(..) => {
            let name = f.var_name().unwrap_or_default().to_string();
            match env.iter().rev().find(|(from, _)| *from == name) {
                Some((_, to)) => rename_leaf(f, to),
                None => f.clone(),
            }
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let base = env.len();
            let renamed: Vec<(Symbol, Sort)> = bindings
                .iter()
                .map(|(sym, sort)| {
                    *next += 1;
                    let to = format!("fresh{next}");
                    env.push((sym.as_str().to_string(), to.clone()));
                    (Symbol::intern(&to), sort.clone())
                })
                .collect();
            let body = rename_bound(body, env, next);
            env.truncate(base);
            if matches!(f, Formula::Forall(..)) {
                Formula::Forall(renamed, Box::new(body))
            } else {
                Formula::Exists(renamed, Box::new(body))
            }
        }
        other => other.clone().map_children(&mut |child| rename_bound(&child, env, next)),
    }
}

/// `f` with the FREE occurrences of `from` renamed to `to`.
fn rename_free(f: &Formula, from: &str, to: &str, bound: &mut Vec<String>) -> Formula {
    match f {
        Formula::Var(..) | Formula::SymVar(..) => {
            if f.var_name() == Some(from) && !bound.iter().any(|name| name == from) {
                rename_leaf(f, to)
            } else {
                f.clone()
            }
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let base = bound.len();
            bound.extend(bindings.iter().map(|(sym, _)| sym.as_str().to_string()));
            let body = rename_free(body, from, to, bound);
            bound.truncate(base);
            if matches!(f, Formula::Forall(..)) {
                Formula::Forall(bindings.clone(), Box::new(body))
            } else {
                Formula::Exists(bindings.clone(), Box::new(body))
            }
        }
        other => other.clone().map_children(&mut |child| rename_free(&child, from, to, bound)),
    }
}

proptest! {
    #[test]
    fn merkle_digests_are_equal_exactly_for_equal_trees(f in formula(), g in formula()) {
        prop_assert_eq!(digest(&f) == digest(&g), f == g);
        // In one shared DAG, with the other formula interned first.
        let mut dag = FormulaDag::new();
        let g_root = dag.intern(&g);
        let f_root = dag.intern(&f);
        let mut cache = MerkleCache::new();
        prop_assert_eq!(cache.digest(&dag, f_root).expect("digest"), digest(&f));
        prop_assert_eq!(cache.digest(&dag, g_root).expect("digest"), digest(&g));
    }

    #[test]
    fn the_bound_alpha_digest_is_bound_variable_alpha_equivalence(f in formula(), g in formula()) {
        let mut next = 0;
        let renamed = rename_bound(&f, &mut Vec::new(), &mut next);
        prop_assert_eq!(alpha(&renamed), alpha(&f));
        prop_assert_eq!(
            alpha(&f) == alpha(&g),
            level_normal(&f, &mut Vec::new()) == level_normal(&g, &mut Vec::new())
        );
        for name in f.free_variables() {
            let moved = rename_free(&f, &name, "elsewhere", &mut Vec::new());
            prop_assert_ne!(alpha(&moved), alpha(&f), "free `{}` renamed", name);
        }
        // In one shared DAG, through one cache.
        let mut dag = FormulaDag::new();
        let roots = [dag.intern(&g), dag.intern(&renamed), dag.intern(&f)];
        let mut cache = MerkleCache::new();
        let got: Vec<FormulaDigest> =
            roots.iter().map(|&root| cache.bound_alpha_digest(&dag, root).expect("alpha")).collect();
        prop_assert_eq!(got, vec![alpha(&g), alpha(&f), alpha(&f)]);
    }

    #[test]
    fn the_row_node_count_matches_query_size(
        rows in prop::collection::vec(prop::collection::vec(formula(), 1..4), 1..5)
    ) {
        let mut context = FormulaDag::new();
        let roots: Vec<Vec<NodeId>> =
            rows.iter().map(|row| row.iter().map(|f| context.intern(f)).collect()).collect();
        for (row, roots) in rows.iter().zip(&roots) {
            let refs: Vec<&Formula> = row.iter().collect();
            prop_assert_eq!(row_node_count(&context, roots).expect("count"), query_size(&refs));
        }
    }
}

/// T3 L4 (C06): a transient root's digest, from its children's, is the digest of the tree
/// it stands for, and the DAG holds no node for it afterwards.
#[test]
fn digest_shell_is_the_digest_of_the_transient_root() {
    let children = vec![gt(var("x"), int(0)), add(var("y"), symvar("s")), var("x")];
    let mut dag = FormulaDag::new();
    let nodes: Vec<NodeId> = children.iter().map(|child| dag.intern(child)).collect();
    let mut cache = MerkleCache::new();
    let digests: Vec<FormulaDigest> =
        nodes.iter().map(|node| cache.digest(&dag, *node).expect("digest")).collect();
    let before = dag.len();
    let shell = Shell::of(&Formula::And(children.clone()));
    let transient = MerkleCache::digest_shell(&shell, &digests).expect("digest");
    assert_eq!(dag.len(), before, "nothing interned");
    assert_eq!(Some(transient), formula_digest(&Formula::And(children)).ok());
    assert_eq!(
        MerkleCache::digest_shell(&shell, &digests[..2]),
        Err(MerkleError::ShellArity { expected: 3, found: 2 })
    );
}

/// T3 L4 (C09w): a digester's digest of a formula is that formula's digest alone (I5),
/// whatever it digested first, including formulas sharing its subtrees; a shared subtree
/// is serialized once.
#[test]
fn a_digester_digest_is_the_formula_digest_whatever_came_first() {
    let shared = add(var("x"), int(7));
    let first = gt(shared.clone(), int(0));
    let second = gt(int(1), shared.clone());
    let mut digester = FormulaDigester::new();
    assert_eq!(digester.digest(&first).ok(), Some(digest(&first)));
    assert_eq!(digester.digest(&second).ok(), Some(digest(&second)));
    assert_eq!(digester.digest(&shared).ok(), Some(digest(&shared)));
    assert_eq!(digester.digest(&first).ok(), Some(digest(&first)), "asked again");
    // first: gt, add, x, 7, 0 (5 nodes); second adds gt and 1; shared adds none.
    assert_eq!(digester.cache.stats().payloads_serialized, 7);
}

#[test]
fn wave500_static_json_bytes_match_serde_json_exactly() {
    let sorts = [
        Sort::Bool,
        Sort::Int,
        Sort::Real,
        Sort::RoundingMode,
        Sort::BitVec(1),
        Sort::BitVec(8),
        Sort::BitVec(16),
        Sort::BitVec(32),
        Sort::BitVec(64),
        Sort::BitVec(128),
        Sort::Float { eb: 8, sb: 24 },
        Sort::Float { eb: 11, sb: 53 },
    ];
    for sort in &sorts {
        let expected = serde_json::to_vec(sort).expect("sort json");
        assert_eq!(
            static_sort_json_bytes(sort),
            Some(expected.as_slice()),
            "sort mismatch for {sort:?}"
        );
    }

    let hole = || Box::new(Formula::Bool(true));
    let payloads = [
        Formula::Bool(true),
        Formula::Bool(false),
        Formula::Not(hole()),
        Formula::Neg(hole()),
        Formula::And(Vec::new()),
        Formula::Or(Vec::new()),
        Formula::Implies(hole(), hole()),
        Formula::Eq(hole(), hole()),
        Formula::Lt(hole(), hole()),
        Formula::Le(hole(), hole()),
        Formula::Gt(hole(), hole()),
        Formula::Ge(hole(), hole()),
        Formula::Add(hole(), hole()),
        Formula::Sub(hole(), hole()),
        Formula::Mul(hole(), hole()),
        Formula::Div(hole(), hole()),
        Formula::Rem(hole(), hole()),
        Formula::Ite(hole(), hole(), hole()),
        Formula::Select(hole(), hole()),
        Formula::Store(hole(), hole(), hole()),
    ];
    for payload in &payloads {
        let expected = serde_json::to_vec(payload).expect("payload json");
        assert_eq!(
            static_shell_payload_json_bytes(payload),
            Some(expected.as_slice()),
            "payload mismatch for {payload:?}"
        );
    }
}
