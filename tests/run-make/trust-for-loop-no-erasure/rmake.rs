//! A `for` loop is lowered FAITHFULLY or DECLINED by the direct producer — never erased.
//!
//! Until 2026-10-01 the producer tried a "read-only-escape for-loop summary" (wave-ER,
//! f7b7cc0bd6) BEFORE the faithful `for` lowering. When a structural scan found no write to a
//! non-local PLACE, the whole loop became an `undef` rebind of the locals it mutated — no loop,
//! no calls. Its soundness argument ("callees reach non-local state only through the gated
//! borrow channels") is false for a foreign call, an unsafe fn, a static or I/O, and the result
//! was reported lowered with no tag, spliced into the crate module, licensed for codegen and
//! skipped by every differential. Measured on main f5dd1d805a (stage1, this file):
//!
//!   close_range      `for fd in lo..hi { close(fd) }`          -> `ret`
//!   cloexec_range    the same with variadic `fcntl`             -> `ret`
//!   InheritStrip::apply (aterm, reduced)                         -> `call mark_listed; ret`
//!   sum_range / sum_and_print                                    -> `%s = undef; ret %s`
//!   poke_range       a loop calling a local `unsafe fn`          -> `ret`
//!   count_slice      `for x in v { s += *x }`                    -> `ret undef`
//!
//! (`sum_and_tick` declined on main — `PendingStatic`, the atomic static kept the summary
//! out — and `sum_and_store_static` lowered faithfully: the `static` write was the one effect
//! the summary's scan saw. Both stay in the invariant below as controls.)
//!
//! The summary is gone. Every `for` now takes the faithful lanes (wave-FR for integer ranges,
//! wave-DR's back-edge CFG for opaque iterators) or declines with a tag. This test pins the
//! invariant over the whole fixture — a function whose source has a loop and whose spliced
//! trust-ir has no back-edge fails it — and pins, by name, the bodies that now lower with
//! their calls inside the loop.
//@ ignore-cross-compile

use std::collections::BTreeMap;

use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};

/// One function of the dumped module: its body lines, in order.
struct IrFn {
    lines: Vec<String>,
}

/// Parse the text module into `name -> body` plus the FuncId-ordered name list (a
/// `call @func.N` names the N-th function header).
fn parse_module(text: &str) -> (BTreeMap<String, IrFn>, Vec<String>) {
    let mut fns = BTreeMap::new();
    let mut order = Vec::new();
    let mut cur: Option<(String, Vec<String>)> = None;
    for line in text.lines() {
        if let Some(at) = line.find("fn @") {
            if line.ends_with('{') || line.contains("(functy.") {
                let rest = &line[at + 4..];
                let name = if let Some(q) = rest.strip_prefix('"') {
                    q[..q.find('"').expect("quoted name closes")].to_string()
                } else {
                    rest[..rest.find('(').expect("fn header has a type")].to_string()
                };
                order.push(name.clone());
                if line.trim_end().ends_with('{') {
                    cur = Some((name, Vec::new()));
                }
                continue;
            }
        }
        if line.starts_with('}') {
            if let Some((name, lines)) = cur.take() {
                fns.insert(name, IrFn { lines });
            }
            continue;
        }
        if let Some((_, lines)) = cur.as_mut() {
            lines.push(line.to_string());
        }
    }
    (fns, order)
}

/// `true` iff the function's CFG has a cycle: blocks and their branch targets are read off
/// the text (`bbN(..):` headers; `br`/`condbr`/`switch` operands), then a depth-first walk
/// looks for an edge back onto its own stack. Block NUMBERS are not an order — a join or loop
/// exit is routinely created before the arm that branches to it — so no numeric shortcut.
fn has_cycle(f: &IrFn) -> bool {
    let mut edges: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    let mut current: Option<u32> = None;
    for line in &f.lines {
        let code = line.split(';').next().unwrap_or("");
        if let Some(rest) = code.strip_prefix("bb") {
            let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
            if let Ok(n) = digits.parse() {
                current = Some(n);
                edges.entry(n).or_default();
                continue;
            }
        }
        let t = code.trim_start();
        if !(t.starts_with("br ") || t.starts_with("condbr ") || t.starts_with("switch ")) {
            continue;
        }
        let Some(cur) = current else { continue };
        for (i, _) in t.match_indices("bb") {
            let digits: String = t[i + 2..].chars().take_while(|c| c.is_ascii_digit()).collect();
            if let Ok(target) = digits.parse::<u32>() {
                edges.entry(cur).or_default().push(target);
            }
        }
    }
    // 1 = on the stack, 2 = finished.
    let mut state: BTreeMap<u32, u8> = BTreeMap::new();
    for &root in edges.keys() {
        if state.contains_key(&root) {
            continue;
        }
        let mut stack = vec![(root, 0usize)];
        state.insert(root, 1);
        while let Some(&(node, next)) = stack.last() {
            match edges.get(&node).and_then(|s| s.get(next)).copied() {
                Some(succ) => {
                    if let Some(top) = stack.last_mut() {
                        top.1 += 1;
                    }
                    match state.get(&succ) {
                        Some(1) => return true,
                        Some(_) => {}
                        None => {
                            state.insert(succ, 1);
                            stack.push((succ, 0));
                        }
                    }
                }
                None => {
                    state.insert(node, 2);
                    stack.pop();
                }
            }
        }
    }
    false
}

/// The callee names this function calls.
fn callees(f: &IrFn, order: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    for line in &f.lines {
        let code = line.split(';').next().unwrap_or("");
        for (i, _) in code.match_indices("call @func.") {
            let digits: String =
                code[i + 11..].chars().take_while(|c| c.is_ascii_digit()).collect();
            if let Ok(n) = digits.parse::<usize>() {
                out.push(order.get(n).cloned().unwrap_or_else(|| format!("func.{n}")));
            }
        }
    }
    out
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return; // Stock rustc has no Trust-IR artifact interface.
    }
    cmd(rustc_path())
        .args([
            "loops.rs",
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name=loops",
            "-Copt-level=0",
            "-Ccodegen-units=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-dump=ir:loops-ir",
            "--out-dir",
            "out",
        ])
        .run();

    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("loops-ir/loops.coverage.json"))
            .expect("published coverage must be valid JSON");
    let rows = report["bodies"].as_array().expect("complete body inventory");
    let row = |path: &str| {
        let matching: Vec<_> = rows.iter().filter(|r| r["def_path"] == path).collect();
        assert_eq!(matching.len(), 1, "missing/duplicate row {path}");
        matching[0]
    };
    // Headers by def path (WS5.2 names them by link symbol; `trust_ir::by_display_path`).
    let text = trust_ir::by_display_path(&rfs::read_to_string("loops-ir/loops.trust-ir.txt"));
    let (fns, order) = parse_module(&text);

    // Every fixture function has a source loop. THE INVARIANT: lowered and spliced means its
    // trust-ir loops too; otherwise it is declined with a named tag or names its splice
    // refusal. "Spliced with no back-edge" is the erasure this test exists to catch.
    let loop_fns = [
        "close_range",
        "cloexec_range",
        "InheritStrip::apply",
        "sum_range",
        "sum_and_print",
        "sum_and_tick",
        "sum_and_store_static",
        "poke_range",
        "count_slice",
        "Grid::erase_scrollback",
        "closure_close::{closure#0}",
    ];
    for name in loop_fns {
        let r = row(name);
        if r["spliced"] == true {
            let f = fns.get(name).unwrap_or_else(|| panic!("spliced `{name}` has no body:\n{text}"));
            assert!(
                has_cycle(f),
                "`{name}` is spliced with NO loop — the loop was erased:\n{}",
                f.lines.join("\n")
            );
        } else if r["lowered"] == true {
            assert!(r["splice_refusal"].is_string(), "a dropped body names why: {r}");
        } else {
            assert!(
                r["unsupported"].as_array().is_some_and(|t| !t.is_empty()),
                "a declined body carries its tag: {r}"
            );
        }
    }

    // PINNED BY NAME: four of the measured erasures now lower FAITHFULLY — spliced, a real
    // loop, and the effect the summary dropped is a call in the body again.
    for (name, effect) in [
        ("close_range", Some("close")),
        ("sum_range", None),
        ("sum_and_print", Some("std::io::_print")),
        ("poke_range", Some("poke")),
    ] {
        let r = row(name);
        assert_eq!(r["spliced"], true, "`{name}` must lower faithfully and splice: {r}");
        let f = &fns[name];
        assert!(has_cycle(f), "`{name}` must keep its loop:\n{}", f.lines.join("\n"));
        assert!(
            !f.lines.iter().any(|l| l.split(';').next().unwrap_or("").contains("undef")),
            "`{name}` computes every value it returns — no `undef` stands in for the loop:\n{}",
            f.lines.join("\n")
        );
        if let Some(effect) = effect {
            assert!(
                callees(f, &order).iter().any(|c| c == effect),
                "`{name}` must still call `{effect}`:\n{}",
                f.lines.join("\n")
            );
        }
    }

    // The variadic `fcntl` loops (`cloexec_range`, aterm's `InheritStrip::apply`) are a real
    // loop now. They used to be REFUSED at assembly, by name: a local `extern "C"` declaration
    // was read as Rust ABI, and a variadic Rust-ABI declaration is unsignable. The producer now
    // declares it C, the ABI of its `extern` block (`tests/run-make/trust-local-extern-c-abi`),
    // so the edge needs no Rust-ABI signature and the body may splice — then it must carry the
    // call. Refused stays honest only if it names the `fcntl` edge; spliced without the loop is
    // what the invariant above forbids.
    for name in ["cloexec_range", "InheritStrip::apply"] {
        let r = row(name);
        if r["spliced"] == true {
            assert!(callees(&fns[name], &order).iter().any(|c| c == "fcntl"), "{name}");
        } else {
            let tags = r["unsupported"].to_string();
            assert!(tags.contains("fcntl"), "`{name}` names the `fcntl` edge it was refused on: {r}");
        }
    }

    // `count_slice` used to pass as `ret undef`; the faithful lanes have no model for a slice
    // iterator's `next` yet, so it DECLINES with the `for`-desugar tag.
    let r = row("count_slice");
    if r["spliced"] != true {
        let tags = r["unsupported"].to_string();
        assert!(tags.contains("ForDesugar("), "the decline names the loop: {r}");
    }

    // The erase ring-rebuild shape keeps the lowering it already had on main: the summary had
    // refused it since ce36363804 (a `Vec` carrier), so it declines at `new_rows.push(row)`.
    let r = row("Grid::erase_scrollback");
    if r["spliced"] != true {
        let tags = r["unsupported"].to_string();
        assert!(tags.contains("Borrow(&mut slot missing)"), "unchanged decline: {r}");
    }
}
