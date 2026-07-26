// Per-algorithm unit tests: one focused test per §16.2 mechanism, each pinning
// the exact observable order / state against a hand-derived spec expectation.
// No Node needed — these fix the algorithms; the ordering-oracle differential
// (module_order.rs) closes the loop against a real engine.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod common;
use common::*;
use trust_js_modules::{
    BindingName, GraphError, ModuleGraph, ResolveExportResult, Status,
};

fn ord(v: &[&str]) -> Vec<String> {
    v.iter().map(|x| x.to_string()).collect()
}

// ---------------------------------------------------------------------------
// linear + diamond evaluation order
// ---------------------------------------------------------------------------

#[test]
fn linear_dependency_order() {
    // c → b → a. Dependencies evaluate before dependants.
    let mut host = TestHost::new();
    host.insert("a", logger("a", &[]));
    host.insert("b", logger("b", &["a"]));
    host.insert("c", logger("c", &["b"]));
    let (graph, cap) = run(&mut host, "c");
    assert_eq!(host.log, ord(&["a", "b", "c"]));
    assert_eq!(*cap.borrow(), TlaState::Resolved);
    // link visits post-order too (InitializeEnvironment after deps).
    assert_eq!(host.link_order, ord(&["a", "b", "c"]));
    for m in ["a", "b", "c"] {
        let id = graph.module_id(&m.to_string()).unwrap();
        assert_eq!(graph.status(id), Status::Evaluated);
    }
}

#[test]
fn diamond_shared_dep_evaluated_once() {
    // d → {b, c} → a. `a` runs once, before b, then c, then d.
    let mut host = TestHost::new();
    host.insert("a", logger("a", &[]));
    host.insert("b", logger("b", &["a"]));
    host.insert("c", logger("c", &["a"]));
    host.insert("d", logger("d", &["b", "c"]));
    let (_g, cap) = run(&mut host, "d");
    assert_eq!(host.log, ord(&["a", "b", "c", "d"]));
    // `a` appears exactly once in the run order.
    assert_eq!(host.run_order.iter().filter(|m| *m == "a").count(), 1);
    assert_eq!(*cap.borrow(), TlaState::Resolved);
}

// ---------------------------------------------------------------------------
// cyclic imports
// ---------------------------------------------------------------------------

#[test]
fn clean_cycle_evaluation_order_and_cycle_root() {
    // a ↔ b (a is entry). The deeper module `b` runs first; the SCC root is `a`.
    let mut host = TestHost::new();
    host.insert("a", logger("a", &["b"]));
    host.insert("b", logger("b", &["a"]));
    let (graph, cap) = run(&mut host, "a");
    assert_eq!(host.log, ord(&["b", "a"]));
    assert_eq!(*cap.borrow(), TlaState::Resolved);
    let a = graph.module_id(&"a".to_string()).unwrap();
    let b = graph.module_id(&"b".to_string()).unwrap();
    // Both are in one SCC whose root is the entry `a`.
    assert_eq!(graph.cycle_root(a), Some(a));
    assert_eq!(graph.cycle_root(b), Some(a));
    assert_eq!(graph.dfs_ancestor_index(b), graph.dfs_ancestor_index(a));
}

#[test]
fn cycle_tdz_on_unlinked_binding_access() {
    // a ↔ b; b reads a's live binding before a's body runs → TDZ ReferenceError,
    // propagated as an evaluation error that rejects the top-level promise.
    let mut host = TestHost::new();
    host.insert("a", logger("a", &["b"]));
    let mut b = logger("b", &["a"]);
    b.access = vec!["a".to_string()]; // b uses a's binding at eval time
    host.insert("b", b);
    let (graph, cap) = run(&mut host, "a");
    // b threw before logging; a never ran.
    assert_eq!(host.log, Vec::<String>::new());
    assert!(matches!(&*cap.borrow(), TlaState::Rejected(_)));
    let a = graph.module_id(&"a".to_string()).unwrap();
    let b = graph.module_id(&"b".to_string()).unwrap();
    assert!(graph.evaluation_error(a).is_some());
    assert!(graph.evaluation_error(b).is_some());
    assert_eq!(graph.status(a), Status::Evaluated);
    assert_eq!(graph.status(b), Status::Evaluated);
}

// ---------------------------------------------------------------------------
// ResolveExport: star ambiguity, cycle handling, default
// ---------------------------------------------------------------------------

#[test]
fn resolve_export_star_ambiguous() {
    // m re-exports * from a and * from b, both providing `x` from distinct
    // bindings → ambiguous. `y` (only in a) resolves; `default` never via star.
    let mut host = TestHost::new();
    let mut a = ModuleSource::new();
    a.local_exports = vec![export_local("x", "x"), export_local("y", "y")];
    let mut b = ModuleSource::new();
    b.local_exports = vec![export_local("x", "x")];
    let mut m = ModuleSource::new();
    m.requested = ord(&["a", "b"]);
    m.star_exports = vec![reexport_star("a"), reexport_star("b")];
    host.insert("a", a);
    host.insert("b", b);
    host.insert("m", m);

    let mut graph = ModuleGraph::new();
    let mid = graph.load(&mut host, &"m".to_string()).unwrap();
    graph.link(&mut host, mid).unwrap();

    assert!(matches!(graph.resolve_export(mid, "x"), ResolveExportResult::Ambiguous));
    assert!(matches!(graph.resolve_export(mid, "y"), ResolveExportResult::Resolved { .. }));
    assert!(matches!(graph.resolve_export(mid, "default"), ResolveExportResult::NotFound));
}

#[test]
fn resolve_export_star_same_binding_not_ambiguous() {
    // m re-exports * from a and * from b; b re-exports x FROM a. Both stars reach
    // the SAME binding (a.x), so it is unambiguous, not a collision.
    let mut host = TestHost::new();
    let mut a = ModuleSource::new();
    a.local_exports = vec![export_local("x", "x")];
    let mut b = ModuleSource::new();
    b.requested = ord(&["a"]);
    b.star_exports = vec![reexport_star("a")];
    let mut m = ModuleSource::new();
    m.requested = ord(&["a", "b"]);
    m.star_exports = vec![reexport_star("a"), reexport_star("b")];
    host.insert("a", a);
    host.insert("b", b);
    host.insert("m", m);

    let mut graph = ModuleGraph::new();
    let mid = graph.load(&mut host, &"m".to_string()).unwrap();
    graph.link(&mut host, mid).unwrap();
    let a_id = graph.module_id(&"a".to_string()).unwrap();
    match graph.resolve_export(mid, "x") {
        ResolveExportResult::Resolved { module, binding } => {
            assert_eq!(module, *graph.module_key(a_id));
            assert_eq!(binding, BindingName::Local("x".to_string()));
        }
        other => panic!("expected resolved, got {other:?}"),
    }
}

#[test]
fn ambiguous_import_fails_link() {
    // Importing the ambiguous name is the SyntaxError at InitializeEnvironment.
    let mut host = TestHost::new();
    let mut a = ModuleSource::new();
    a.local_exports = vec![export_local("x", "x")];
    let mut b = ModuleSource::new();
    b.local_exports = vec![export_local("x", "x")];
    let mut m = ModuleSource::new();
    m.requested = ord(&["a", "b"]);
    m.star_exports = vec![reexport_star("a"), reexport_star("b")];
    let mut main = ModuleSource::new();
    main.requested = ord(&["m"]);
    main.imports = vec![import_named("m", "x", "x")];
    host.insert("a", a);
    host.insert("b", b);
    host.insert("m", m);
    host.insert("main", main);

    let mut graph = ModuleGraph::new();
    let id = graph.load(&mut host, &"main".to_string()).unwrap();
    let err = graph.link(&mut host, id).unwrap_err();
    assert!(matches!(err, GraphError::AmbiguousExport { .. }), "got {err:?}");
    // Fail-closed + re-linkable: the entry (still on the link stack when its
    // InitializeEnvironment threw) is unwound to Unlinked. Per §16.2.1.5.1 step 4
    // only stack modules are reset; deps that already finished linking stay Linked.
    let main_id = graph.module_id(&"main".to_string()).unwrap();
    assert_eq!(graph.status(main_id), Status::Unlinked);
}

#[test]
fn unresolved_import_fails_link() {
    // Importing a name the target never exports → the unresolved SyntaxError.
    let mut host = TestHost::new();
    let mut lib = ModuleSource::new();
    lib.local_exports = vec![export_local("foo", "foo")];
    let mut main = ModuleSource::new();
    main.requested = ord(&["lib"]);
    main.imports = vec![import_named("lib", "bar", "bar")]; // bar not exported
    host.insert("lib", lib);
    host.insert("main", main);

    let mut graph = ModuleGraph::new();
    let id = graph.load(&mut host, &"main".to_string()).unwrap();
    let err = graph.link(&mut host, id).unwrap_err();
    assert!(matches!(err, GraphError::UnresolvedImport { .. }), "got {err:?}");
}

// ---------------------------------------------------------------------------
// namespace export names + sorting + re-export
// ---------------------------------------------------------------------------

#[test]
fn namespace_export_names_sorted() {
    // Exports declared out of order + a default → namespace names are code-unit
    // sorted, and include "default".
    let mut host = TestHost::new();
    let mut m = ModuleSource::new();
    m.local_exports = vec![
        export_local("c", "c"),
        export_local("a", "a"),
        export_local("default", "*default*"),
        export_local("b", "b"),
    ];
    host.insert("m", m);

    let mut graph = ModuleGraph::new();
    let id = graph.load(&mut host, &"m".to_string()).unwrap();
    graph.link(&mut host, id).unwrap();
    let ns = graph.get_module_namespace(id);
    assert_eq!(ns.names, ord(&["a", "b", "c", "default"]));
}

#[test]
fn star_reexport_names_exclude_default_and_dedup() {
    // m = export * from a + local `own`. a exports {x, default}. The namespace of
    // m has {own, x} — `default` is never re-exported by `export *`.
    let mut host = TestHost::new();
    let mut a = ModuleSource::new();
    a.local_exports = vec![export_local("x", "x"), export_local("default", "*default*")];
    let mut m = ModuleSource::new();
    m.requested = ord(&["a"]);
    m.local_exports = vec![export_local("own", "own")];
    m.star_exports = vec![reexport_star("a")];
    host.insert("a", a);
    host.insert("m", m);

    let mut graph = ModuleGraph::new();
    let id = graph.load(&mut host, &"m".to_string()).unwrap();
    graph.link(&mut host, id).unwrap();
    let ns = graph.get_module_namespace(id);
    assert_eq!(ns.names, ord(&["own", "x"]));
}

#[test]
fn export_star_as_namespace_binding() {
    // ns_provider: `export * as inner from "lib"` → resolves to lib's namespace.
    let mut host = TestHost::new();
    let mut lib = ModuleSource::new();
    lib.local_exports = vec![export_local("foo", "foo")];
    let mut provider = ModuleSource::new();
    provider.requested = ord(&["lib"]);
    provider.indirect_exports = vec![reexport_ns("lib", "inner")];
    host.insert("lib", lib);
    host.insert("provider", provider);

    let mut graph = ModuleGraph::new();
    let id = graph.load(&mut host, &"provider".to_string()).unwrap();
    graph.link(&mut host, id).unwrap();
    let lib_id = graph.module_id(&"lib".to_string()).unwrap();
    match graph.resolve_export(id, "inner") {
        ResolveExportResult::Resolved { module, binding } => {
            assert_eq!(module, *graph.module_key(lib_id));
            assert_eq!(binding, BindingName::Namespace);
        }
        other => panic!("expected namespace binding, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// loading refusals
// ---------------------------------------------------------------------------

#[test]
fn unresolvable_specifier_errors() {
    let mut host = TestHost::new();
    host.insert("main", logger("main", &["missing"])); // no `missing` source
    let mut graph = ModuleGraph::new();
    let err = graph.load(&mut host, &"main".to_string()).unwrap_err();
    assert!(matches!(err, GraphError::Resolve(_)), "got {err:?}");
}

// ---------------------------------------------------------------------------
// top-level await ordering
// ---------------------------------------------------------------------------

#[test]
fn tla_chain_delays_dependents() {
    // c → b → a, a has top-level await. a runs, awaits, resumes; only then b, c.
    let mut host = TestHost::new();
    host.insert("a", async_logger("a", &[]));
    host.insert("b", logger("b", &["a"]));
    host.insert("c", logger("c", &["b"]));
    let (graph, cap) = run(&mut host, "c");
    assert_eq!(host.log, ord(&["a", "a$", "b", "c"]));
    assert_eq!(*cap.borrow(), TlaState::Resolved);
    // c is the async root; its promise resolved after the drain.
    let c = graph.module_id(&"c".to_string()).unwrap();
    assert_eq!(graph.status(c), Status::Evaluated);
}

#[test]
fn tla_dependency_delays_two_dependents() {
    // d → {b, c} → a(async). After a resumes, b then c (async-eval order), then d.
    let mut host = TestHost::new();
    host.insert("a", async_logger("a", &[]));
    host.insert("b", logger("b", &["a"]));
    host.insert("c", logger("c", &["a"]));
    host.insert("d", logger("d", &["b", "c"]));
    let (_g, cap) = run(&mut host, "d");
    assert_eq!(host.log, ord(&["a", "a$", "b", "c", "d"]));
    assert_eq!(*cap.borrow(), TlaState::Resolved);
}

#[test]
fn tla_two_independent_async_deps() {
    // e → {a(async), b(async)}. Pre-await a,b; resumes a$,b$ (FIFO); then e.
    let mut host = TestHost::new();
    host.insert("a", async_logger("a", &[]));
    host.insert("b", async_logger("b", &[]));
    host.insert("e", logger("e", &["a", "b"]));
    let (_g, cap) = run(&mut host, "e");
    assert_eq!(host.log, ord(&["a", "b", "a$", "b$", "e"]));
    assert_eq!(*cap.borrow(), TlaState::Resolved);
}

#[test]
fn tla_state_machine_pending_then_resolved() {
    // Before draining the reactor, the async root is evaluating-async / pending;
    // after, evaluated / resolved.
    let mut host = TestHost::new();
    host.insert("a", async_logger("a", &[]));
    host.insert("b", logger("b", &["a"]));

    let mut graph = ModuleGraph::new();
    let id = graph.load(&mut host, &"b".to_string()).unwrap();
    graph.link(&mut host, id).unwrap();
    let cap = graph.evaluate(&mut host, id);
    // Not yet drained: b awaits a's async completion.
    assert_eq!(graph.status(id), Status::EvaluatingAsync);
    assert_eq!(*cap.borrow(), TlaState::Pending);
    assert!(host.has_pending_async());
    // Drain the reactor.
    drive_async(&mut graph, &mut host);
    assert_eq!(graph.status(id), Status::Evaluated);
    assert_eq!(*cap.borrow(), TlaState::Resolved);
    assert_eq!(host.log, ord(&["a", "a$", "b"]));
}

#[test]
fn tla_rejection_propagates_to_dependents() {
    // a(async) rejects; its dependent b never runs; b's root promise rejects.
    let mut host = TestHost::new();
    let mut a = async_logger("a", &[]);
    a.async_rejects = Some("boom".to_string());
    host.insert("a", a);
    host.insert("b", logger("b", &["a"]));
    let (graph, cap) = run(&mut host, "b");
    // a logged its pre-await marker, but b never ran.
    assert_eq!(host.log, ord(&["a"]));
    assert!(matches!(&*cap.borrow(), TlaState::Rejected(_)));
    let b = graph.module_id(&"b".to_string()).unwrap();
    assert!(graph.evaluation_error(b).is_some());
}

// ---------------------------------------------------------------------------
// state-machine transitions (link vs eval status progression)
// ---------------------------------------------------------------------------

#[test]
fn status_transitions_new_unlinked_linked_evaluated() {
    let mut host = TestHost::new();
    host.insert("a", logger("a", &[]));
    host.insert("b", logger("b", &["a"]));

    let mut graph = ModuleGraph::new();
    let id = graph.load(&mut host, &"b".to_string()).unwrap();
    // After load: unlinked.
    assert_eq!(graph.status(id), Status::Unlinked);
    let a = graph.module_id(&"a".to_string()).unwrap();
    assert_eq!(graph.status(a), Status::Unlinked);
    // After link: linked.
    graph.link(&mut host, id).unwrap();
    assert_eq!(graph.status(id), Status::Linked);
    assert_eq!(graph.status(a), Status::Linked);
    // DFS indices are pre-order: the entry `b` is entered first (0), then its
    // dependency `a` (1).
    assert_eq!(graph.dfs_index(id), 0);
    assert_eq!(graph.dfs_index(a), 1);
    // After evaluate: evaluated.
    let cap = graph.evaluate(&mut host, id);
    assert_eq!(graph.status(id), Status::Evaluated);
    assert_eq!(graph.status(a), Status::Evaluated);
    assert_eq!(*cap.borrow(), TlaState::Resolved);
}

#[test]
fn re_evaluate_returns_same_promise() {
    // A second Evaluate() on an evaluated graph hands back the same capability.
    let mut host = TestHost::new();
    host.insert("a", logger("a", &[]));
    let mut graph = ModuleGraph::new();
    let id = graph.load(&mut host, &"a".to_string()).unwrap();
    graph.link(&mut host, id).unwrap();
    let cap1 = graph.evaluate(&mut host, id);
    let cap2 = graph.evaluate(&mut host, id);
    assert!(std::rc::Rc::ptr_eq(&cap1, &cap2));
    // The body ran exactly once.
    assert_eq!(host.log, ord(&["a"]));
}

// ---------------------------------------------------------------------------
// mixed default / named / namespace imports link cleanly
// ---------------------------------------------------------------------------

#[test]
fn mixed_imports_link_and_evaluate() {
    let mut host = TestHost::new();
    let mut lib = logger("lib", &[]);
    lib.local_exports = vec![
        export_local("default", "*default*"),
        export_local("foo", "foo"),
    ];
    host.insert("lib", lib);
    let mut main = logger("main", &["lib"]);
    main.imports = vec![
        import_named("lib", "default", "d"),
        import_named("lib", "foo", "f"),
        import_ns("lib", "L"),
    ];
    host.insert("main", main);

    let (graph, cap) = run(&mut host, "main");
    assert_eq!(host.log, ord(&["lib", "main"]));
    assert_eq!(*cap.borrow(), TlaState::Resolved);
    let lib_id = graph.module_id(&"lib".to_string()).unwrap();
    assert!(matches!(
        graph.resolve_export(lib_id, "default"),
        ResolveExportResult::Resolved { .. }
    ));
}
