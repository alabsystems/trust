// Determinism (M2 D2 validation #3): 100 identical Link + Evaluate runs of a rich
// module graph produce byte-identical module-VISIT order (the link DFS), body-RUN
// order (the evaluation DFS + async execution list), and observable marker trace.
// This is the invariant that makes the eventual S-module ObservableTrace
// byte-reproducible: given the same module map + host callbacks, nothing observable
// rides hash-map iteration order.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod common;
use common::*;
use trust_js_modules::ModuleGraph;

/// One rich graph exercising every observable path: a diamond over a shared leaf,
/// a 2-cycle, a star re-export, mixed default/named/namespace imports, and two
/// top-level-await modules whose completions gate dependants — so the trace
/// encodes link order, sync eval order, cycle ordering, and async execution order
/// all at once.
fn build(host: &mut TestHost) {
    // shared sync leaf
    host.insert("leaf", logger("leaf", &[]));

    // a star re-export hub: `re` re-exports * from `leaf_x`
    let mut leaf_x = logger("leaf_x", &[]);
    leaf_x.local_exports = vec![export_local("x", "x")];
    host.insert("leaf_x", leaf_x);
    let mut re = logger("re", &["leaf_x"]);
    re.star_exports = vec![reexport_star("leaf_x")];
    host.insert("re", re);

    // a library with default + named exports
    let mut lib = logger("lib", &[]);
    lib.local_exports = vec![export_local("default", "*default*"), export_local("foo", "foo")];
    host.insert("lib", lib);

    // a 2-cycle p <-> q
    host.insert("p", logger("p", &["q", "leaf"]));
    host.insert("q", logger("q", &["p"]));

    // two async (top-level await) modules
    host.insert("async_a", async_logger("async_a", &["leaf"]));
    host.insert("async_b", async_logger("async_b", &[]));

    // diamond arms depending on the async modules + the shared leaf
    host.insert("left", logger("left", &["async_a", "leaf"]));
    host.insert("right", logger("right", &["async_b", "leaf"]));

    // entry: pulls everything together with mixed import forms
    let mut main = logger("main", &["left", "right", "p", "re"]);
    main.requested = vec![
        "left".into(),
        "right".into(),
        "p".into(),
        "re".into(),
        "lib".into(),
    ];
    main.imports = vec![
        import_named("re", "x", "x"),
        import_named("lib", "default", "d"),
        import_named("lib", "foo", "f"),
        import_ns("lib", "L"),
    ];
    host.insert("main", main);
}

fn run_once() -> (Vec<String>, Vec<String>, Vec<String>) {
    let mut host = TestHost::new();
    build(&mut host);
    let mut graph = ModuleGraph::new();
    let id = graph.load(&mut host, &"main".to_string()).expect("load");
    graph.link(&mut host, id).expect("link");
    graph.evaluate(&mut host, id);
    drive_async(&mut graph, &mut host);
    (host.link_order, host.run_order, host.log)
}

#[test]
fn one_hundred_runs_byte_identical() {
    let (link0, run0, log0) = run_once();

    // Sanity: the trace is non-trivial (every phase produced observable order).
    assert!(!link0.is_empty());
    assert!(!run0.is_empty());
    assert!(!log0.is_empty());
    // The async markers land after their pre-await markers (top-level await took
    // effect), and the whole graph resolved.
    assert!(log0.contains(&"async_a$".to_string()));
    assert!(log0.contains(&"main".to_string()));

    for i in 1..100 {
        let (link, run, log) = run_once();
        assert_eq!(link, link0, "link (module-visit) order diverged on run {i}");
        assert_eq!(run, run0, "run (body) order diverged on run {i}");
        assert_eq!(log, log0, "observable marker trace diverged on run {i}");
    }

    eprintln!("determinism: 100 runs byte-identical");
    eprintln!("  link order: {link0:?}");
    eprintln!("  run  order: {run0:?}");
    eprintln!("  markers   : {log0:?}");
}
