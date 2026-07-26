// The ORDERING-ORACLE differential (M2 D2 validation #2).
//
// A battery of >=40 small multi-module programs, each expressed ONCE as a `Mod`
// list and rendered BOTH as:
//   (a) real ES modules (`gen_js`), written to a tempdir and run through Node —
//       each module `console.log`s a marker on evaluation, so Node's stdout is
//       its true evaluation order; and
//   (b) the same graph as module records (`build_source`) driven through this
//       crate's Link + Evaluate with the mock host, whose `RunModuleBody` logs the
//       same markers.
// The oracle asserts (b) == (a) for every program. Disagreements must be 0.
//
// `engine_determinism` ALWAYS runs (no Node needed): every program is driven
// twice and must produce byte-identical order — the cheap guard that ships in CI.
// `ordering_oracle_differential` is env-gated on TRUST_JS_NODE and closes the loop
// against a real engine.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod common;
use common::{drive_async, ModuleSource, TestHost};

use std::fmt::Write as _;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::Command;
use trust_js_modules::{
    ImportEntry, ImportName, IndirectExport, LocalExport, ModuleGraph, ReExportName, StarExport,
};

// ---------------------------------------------------------------------------
// One graph, one source of truth.
// ---------------------------------------------------------------------------

/// An import form.
#[derive(Clone)]
enum Imp {
    /// `import "./from.mjs"` — a dependency edge, no binding.
    Side(&'static str),
    /// `import D from "./from.mjs"`.
    Default(&'static str, &'static str),
    /// `import { name as local } from "./from.mjs"`.
    Named(&'static str, &'static str, &'static str),
    /// `import * as local from "./from.mjs"`.
    Ns(&'static str, &'static str),
}

/// An export form.
#[derive(Clone)]
enum Exp {
    /// `export const NAME = "NAME"`.
    Const(&'static str),
    /// `export default 0`.
    Default,
    /// `export { name as as_name } from "./from.mjs"`.
    ReNamed(&'static str, &'static str, &'static str),
    /// `export * from "./from.mjs"`.
    ReStar(&'static str),
    /// `export * as as_name from "./from.mjs"`.
    ReNsAs(&'static str, &'static str),
}

#[derive(Clone)]
struct Mod {
    name: &'static str,
    imports: Vec<Imp>,
    exports: Vec<Exp>,
    log: bool,
    tla: bool,
}

/// A named battery entry: the entry module is `mods[0]`.
struct Battery {
    name: &'static str,
    mods: Vec<Mod>,
}

fn spec(name: &str) -> String {
    format!("./{name}.mjs")
}

fn imp_from(i: &Imp) -> &'static str {
    match i {
        Imp::Side(f) | Imp::Default(f, _) | Imp::Named(f, _, _) | Imp::Ns(f, _) => f,
    }
}

fn exp_from(e: &Exp) -> Option<&'static str> {
    match e {
        Exp::ReNamed(f, _, _) | Exp::ReStar(f) | Exp::ReNsAs(f, _) => Some(f),
        _ => None,
    }
}

/// Requested specifiers in source order (imports, then re-export-from exports),
/// deduplicated by first occurrence — exactly the order the source presents them.
fn requested(m: &Mod) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut push = |name: &str| {
        let s = name.to_string();
        if !out.contains(&s) {
            out.push(s);
        }
    };
    for i in &m.imports {
        push(imp_from(i));
    }
    for e in &m.exports {
        if let Some(f) = exp_from(e) {
            push(f);
        }
    }
    out
}

/// Render a module as real ES-module source. Emission order (imports, re-export
/// froms, body log/await, value exports) matches `requested` / `build_source`.
fn gen_js(m: &Mod) -> String {
    let mut s = String::new();
    for i in &m.imports {
        match i {
            Imp::Side(f) => writeln!(s, "import {:?};", spec(f)).unwrap(),
            Imp::Default(f, l) => writeln!(s, "import {l} from {:?};", spec(f)).unwrap(),
            Imp::Named(f, n, l) => writeln!(s, "import {{ {n} as {l} }} from {:?};", spec(f)).unwrap(),
            Imp::Ns(f, l) => writeln!(s, "import * as {l} from {:?};", spec(f)).unwrap(),
        }
    }
    for e in &m.exports {
        match e {
            Exp::ReNamed(f, n, a) => writeln!(s, "export {{ {n} as {a} }} from {:?};", spec(f)).unwrap(),
            Exp::ReStar(f) => writeln!(s, "export * from {:?};", spec(f)).unwrap(),
            Exp::ReNsAs(f, a) => writeln!(s, "export * as {a} from {:?};", spec(f)).unwrap(),
            _ => {}
        }
    }
    if m.tla {
        writeln!(s, "console.log({:?});", m.name).unwrap();
        writeln!(s, "await Promise.resolve();").unwrap();
        writeln!(s, "console.log({:?});", format!("{}$", m.name)).unwrap();
    } else if m.log {
        writeln!(s, "console.log({:?});", m.name).unwrap();
    }
    for e in &m.exports {
        match e {
            Exp::Const(n) => writeln!(s, "export const {n} = {:?};", *n).unwrap(),
            Exp::Default => writeln!(s, "export default 0;").unwrap(),
            _ => {}
        }
    }
    s
}

/// Render a module as the record model the engine drives.
fn build_source(m: &Mod) -> ModuleSource {
    let mut src = ModuleSource::new();
    src.requested = requested(m);
    src.has_tla = m.tla;
    if m.tla {
        src.markers = vec![m.name.to_string()];
        src.post_markers = vec![format!("{}$", m.name)];
    } else if m.log {
        src.markers = vec![m.name.to_string()];
    }
    for i in &m.imports {
        match i {
            Imp::Side(_) => {}
            Imp::Default(f, l) => src.imports.push(ImportEntry {
                module_request: f.to_string(),
                import_name: ImportName::Named("default".to_string()),
                local_name: l.to_string(),
            }),
            Imp::Named(f, n, l) => src.imports.push(ImportEntry {
                module_request: f.to_string(),
                import_name: ImportName::Named(n.to_string()),
                local_name: l.to_string(),
            }),
            Imp::Ns(f, l) => src.imports.push(ImportEntry {
                module_request: f.to_string(),
                import_name: ImportName::Namespace,
                local_name: l.to_string(),
            }),
        }
    }
    for e in &m.exports {
        match e {
            Exp::Const(n) => src.local_exports.push(LocalExport {
                export_name: n.to_string(),
                local_name: n.to_string(),
            }),
            Exp::Default => src.local_exports.push(LocalExport {
                export_name: "default".to_string(),
                local_name: "*default*".to_string(),
            }),
            Exp::ReNamed(f, n, a) => src.indirect_exports.push(IndirectExport {
                export_name: a.to_string(),
                module_request: f.to_string(),
                import_name: ReExportName::Named(n.to_string()),
            }),
            Exp::ReStar(f) => src.star_exports.push(StarExport { module_request: f.to_string() }),
            Exp::ReNsAs(f, a) => src.indirect_exports.push(IndirectExport {
                export_name: a.to_string(),
                module_request: f.to_string(),
                import_name: ReExportName::All,
            }),
        }
    }
    src
}

// ---------------------------------------------------------------------------
// Concise Mod constructors.
// ---------------------------------------------------------------------------

/// A synchronous logging module whose only imports are dependency edges.
fn dep(name: &'static str, deps: &[&'static str]) -> Mod {
    Mod { name, imports: deps.iter().map(|d| Imp::Side(d)).collect(), exports: vec![], log: true, tla: false }
}
/// A top-level-await logging module with dependency-edge imports.
fn tla(name: &'static str, deps: &[&'static str]) -> Mod {
    Mod { name, imports: deps.iter().map(|d| Imp::Side(d)).collect(), exports: vec![], log: true, tla: true }
}
/// A module with explicit import/export forms.
fn m(name: &'static str, imports: Vec<Imp>, exports: Vec<Exp>, log: bool) -> Mod {
    Mod { name, imports, exports, log, tla: false }
}

// ---------------------------------------------------------------------------
// The battery.
// ---------------------------------------------------------------------------

fn graphs() -> Vec<Battery> {
    let b = |name: &'static str, mods: Vec<Mod>| Battery { name, mods };
    vec![
        // --- linear chains ---
        b("linear_2", vec![dep("main", &["a"]), dep("a", &[])]),
        b("linear_3", vec![dep("main", &["a"]), dep("a", &["b"]), dep("b", &[])]),
        b("linear_4", vec![dep("main", &["a"]), dep("a", &["b"]), dep("b", &["c"]), dep("c", &[])]),
        b("linear_5", vec![dep("main", &["a"]), dep("a", &["b"]), dep("b", &["c"]), dep("c", &["d"]), dep("d", &[])]),
        b("linear_6", vec![dep("main", &["a"]), dep("a", &["b"]), dep("b", &["c"]), dep("c", &["d"]), dep("d", &["e"]), dep("e", &[])]),
        // --- diamonds / fan-out / trees ---
        b("diamond", vec![dep("main", &["a", "b"]), dep("a", &["c"]), dep("b", &["c"]), dep("c", &[])]),
        b("diamond_wide", vec![dep("main", &["a", "b", "c"]), dep("a", &["d"]), dep("b", &["d"]), dep("c", &["d"]), dep("d", &[])]),
        b("diamond_asym", vec![dep("main", &["a", "b"]), dep("a", &["b"]), dep("b", &[])]),
        b("diamond_deep", vec![dep("main", &["a", "b"]), dep("a", &["c"]), dep("b", &["d"]), dep("c", &["e"]), dep("d", &["e"]), dep("e", &[])]),
        b("fanout_5", vec![dep("main", &["a", "b", "c", "d", "e"]), dep("a", &[]), dep("b", &[]), dep("c", &[]), dep("d", &[]), dep("e", &[])]),
        b("tree", vec![dep("main", &["a", "b"]), dep("a", &["c", "d"]), dep("b", &["e", "f"]), dep("c", &[]), dep("d", &[]), dep("e", &[]), dep("f", &[])]),
        b("shared_leaf", vec![dep("main", &["a", "b", "c"]), dep("a", &["z"]), dep("b", &["z"]), dep("c", &["z"]), dep("z", &[])]),
        b("wide_then_deep", vec![dep("main", &["a", "b"]), dep("a", &["x", "y"]), dep("b", &["y", "x"]), dep("x", &[]), dep("y", &[])]),
        // --- cycles ---
        b("cycle_2", vec![dep("main", &["a"]), dep("a", &["main"])]),
        b("cycle_3", vec![dep("main", &["a"]), dep("a", &["b"]), dep("b", &["main"])]),
        b("cycle_tail", vec![dep("main", &["a"]), dep("a", &["b"]), dep("b", &["a"])]),
        b("cycle_4", vec![dep("main", &["a"]), dep("a", &["b"]), dep("b", &["c"]), dep("c", &["main"])]),
        b("cycle_plus_leaf", vec![dep("main", &["a", "leaf"]), dep("a", &["main"]), dep("leaf", &[])]),
        b("two_cycles", vec![dep("main", &["p", "q"]), dep("p", &["p2"]), dep("p2", &["p"]), dep("q", &["q2"]), dep("q2", &["q"])]),
        b("cycle_shared_dep", vec![dep("main", &["a"]), dep("a", &["b", "z"]), dep("b", &["a", "z"]), dep("z", &[])]),
        // --- star re-export ---
        b("star_reexport", vec![
            m("main", vec![Imp::Named("hub", "x", "x")], vec![], true),
            m("hub", vec![], vec![Exp::ReStar("a")], true),
            m("a", vec![], vec![Exp::Const("x")], true),
        ]),
        b("star_chain", vec![
            m("main", vec![Imp::Named("hub2", "x", "x")], vec![], true),
            m("hub2", vec![], vec![Exp::ReStar("hub1")], true),
            m("hub1", vec![], vec![Exp::ReStar("a")], true),
            m("a", vec![], vec![Exp::Const("x")], true),
        ]),
        b("star_two_sources", vec![
            m("main", vec![Imp::Named("hub", "x", "x"), Imp::Named("hub", "y", "y")], vec![], true),
            m("hub", vec![], vec![Exp::ReStar("a"), Exp::ReStar("b")], true),
            m("a", vec![], vec![Exp::Const("x")], true),
            m("b", vec![], vec![Exp::Const("y")], true),
        ]),
        b("reexport_named", vec![
            m("main", vec![Imp::Named("lib", "y", "y")], vec![], true),
            m("lib", vec![], vec![Exp::ReNamed("a", "x", "y")], true),
            m("a", vec![], vec![Exp::Const("x")], true),
        ]),
        b("reexport_ns_as", vec![
            m("main", vec![Imp::Named("provider", "inner", "inner")], vec![], true),
            m("provider", vec![], vec![Exp::ReNsAs("lib", "inner")], true),
            m("lib", vec![], vec![Exp::Const("foo")], true),
        ]),
        // --- mixed default / named / namespace imports ---
        b("default_import", vec![
            m("main", vec![Imp::Default("lib", "D")], vec![], true),
            m("lib", vec![], vec![Exp::Default], true),
        ]),
        b("named_import", vec![
            m("main", vec![Imp::Named("lib", "foo", "foo")], vec![], true),
            m("lib", vec![], vec![Exp::Const("foo")], true),
        ]),
        b("ns_import", vec![
            m("main", vec![Imp::Ns("lib", "L")], vec![], true),
            m("lib", vec![], vec![Exp::Const("foo")], true),
        ]),
        b("mixed_all_forms", vec![
            m("main", vec![Imp::Default("lib", "D"), Imp::Named("lib", "foo", "f"), Imp::Ns("lib", "L")], vec![], true),
            m("lib", vec![], vec![Exp::Default, Exp::Const("foo")], true),
        ]),
        b("two_libs", vec![
            m("main", vec![Imp::Named("a", "x", "x"), Imp::Named("b", "y", "y")], vec![], true),
            m("a", vec![], vec![Exp::Const("x")], true),
            m("b", vec![], vec![Exp::Const("y")], true),
        ]),
        b("diamond_named", vec![
            m("main", vec![Imp::Named("a", "x", "ax"), Imp::Named("b", "x", "bx")], vec![], true),
            m("a", vec![Imp::Named("c", "x", "cx")], vec![Exp::Const("x")], true),
            m("b", vec![Imp::Named("c", "x", "cx")], vec![Exp::Const("x")], true),
            m("c", vec![], vec![Exp::Const("x")], true),
        ]),
        // --- top-level await ordering ---
        b("tla_leaf", vec![dep("main", &["a"]), tla("a", &[])]),
        b("tla_chain", vec![dep("main", &["a"]), dep("a", &["b"]), tla("b", &[])]),
        b("tla_two_dependents", vec![dep("main", &["a", "b"]), dep("a", &["c"]), dep("b", &["c"]), tla("c", &[])]),
        b("tla_two_async", vec![dep("main", &["a", "b"]), tla("a", &[]), tla("b", &[])]),
        b("tla_entry_async", vec![tla("main", &["a"]), dep("a", &[])]),
        b("tla_mixed_deps", vec![dep("main", &["a", "b"]), tla("a", &[]), dep("b", &[])]),
        b("tla_nested", vec![dep("main", &["a"]), tla("a", &["b"]), tla("b", &[])]),
        b("tla_chain_deep", vec![dep("main", &["a"]), dep("a", &["b"]), dep("b", &["c"]), tla("c", &[])]),
        b("tla_diamond_shared_async", vec![dep("main", &["a", "b"]), dep("a", &["c"]), dep("b", &["c"]), tla("c", &[])]),
        b("tla_diamond_two_async", vec![dep("main", &["a", "b"]), tla("a", &["c"]), tla("b", &["c"]), dep("c", &[])]),
        b("tla_three_async", vec![dep("main", &["a", "b", "c"]), tla("a", &[]), tla("b", &[]), tla("c", &[])]),
        b("tla_async_with_sync_sibling", vec![dep("main", &["x", "a", "y"]), dep("x", &[]), tla("a", &[]), dep("y", &[])]),
    ]
}

// ---------------------------------------------------------------------------
// engine driver
// ---------------------------------------------------------------------------

fn engine_order(battery: &Battery) -> Vec<String> {
    let mut host = TestHost::new();
    for md in &battery.mods {
        host.insert(md.name, build_source(md));
    }
    let entry = battery.mods[0].name.to_string();
    let mut graph = ModuleGraph::new();
    let id = graph.load(&mut host, &entry).expect("load");
    graph.link(&mut host, id).expect("link");
    graph.evaluate(&mut host, id);
    drive_async(&mut graph, &mut host);
    host.log
}

// ---------------------------------------------------------------------------
// Node oracle (env-gated on TRUST_JS_NODE)
// ---------------------------------------------------------------------------

struct NodeEnv {
    node: String,
    tmp: tempfile::TempDir,
}

fn node_env_or_skip() -> Option<NodeEnv> {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP ordering_oracle_differential: set TRUST_JS_NODE to a node binary to run the differential");
        return None;
    };
    Some(NodeEnv { node, tmp: tempfile::tempdir().expect("tempdir") })
}

fn node_order(env: &NodeEnv, battery: &Battery) -> Result<Vec<String>, String> {
    let dir = env.tmp.path().join(battery.name);
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    for md in &battery.mods {
        let path = dir.join(format!("{}.mjs", md.name));
        let mut f = std::fs::File::create(&path).map_err(|e| e.to_string())?;
        f.write_all(gen_js(md).as_bytes()).map_err(|e| e.to_string())?;
    }
    let entry: PathBuf = dir.join(format!("{}.mjs", battery.mods[0].name));
    let out = Command::new(&env.node)
        .arg(&entry)
        .env("TZ", "UTC")
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .output()
        .map_err(|e| format!("spawn node: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "node exited {:?}; stderr:\n{}",
            out.status.code(),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect())
}

// ---------------------------------------------------------------------------
// tests
// ---------------------------------------------------------------------------

/// Always-run: >=40 graphs, and each drives to a deterministic order twice over.
#[test]
fn engine_determinism_over_battery() {
    let progs = graphs();
    assert!(progs.len() >= 40, "battery has only {} graphs", progs.len());
    for prog in &progs {
        let a = engine_order(prog);
        let bb = engine_order(prog);
        assert_eq!(a, bb, "engine non-determinism on {}", prog.name);
    }
    eprintln!("engine-determinism: {} graphs, all stable", progs.len());
}

/// The oracle: engine evaluation order == Node's, for every graph. Gated on
/// TRUST_JS_NODE. Disagreements must be 0.
#[test]
fn ordering_oracle_differential() {
    let Some(env) = node_env_or_skip() else { return };
    let progs = graphs();
    let mut agree = 0usize;
    let mut disagree = Vec::new();
    for prog in &progs {
        let engine = engine_order(prog);
        match node_order(&env, prog) {
            Ok(node) if node == engine => agree += 1,
            Ok(node) => disagree.push(format!("  {}: engine={engine:?} node={node:?}", prog.name)),
            Err(e) => disagree.push(format!("  {}: node error: {e}", prog.name)),
        }
    }
    eprintln!(
        "ordering-oracle: {} graphs / {agree} agree / {} disagree",
        progs.len(),
        disagree.len()
    );
    assert!(disagree.is_empty(), "ordering disagreements:\n{}", disagree.join("\n"));
}
