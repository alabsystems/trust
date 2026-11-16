//! A field store's right-hand side is evaluated — its EFFECTS reach the trust-ir — even when
//! the lane models only part of the stored VALUE.
//!
//! Until 2026-10-01 three direct-producer lanes skipped the right-hand side of a field store
//! wholesale (since c78b82bb50, 2026-07-18):
//!
//!   * the opaque `Ty::Unit` lane (a `Vec`/`String`/data-enum field of a `&mut self` struct):
//!     `self.argv = { for fd in lo..hi { close(fd) } Vec::new() }` became `load; extractfield;
//!     insertfield; store; ret` — the loop and every `close` gone;
//!   * the Option-discriminant (`TRUST_OPTION_FLAG_LANES`, on by default) field lane:
//!     `self.boxed = Some(Box::new(close_ret(fd)))` became `const bool true; store`, and
//!     `self.boxed = close_then_some(fd)` became `undef bool; store`;
//!   * the same lane in value position (`lower_enum_construct_general`): `Some(effect)` became
//!     `const bool true` with the payload's call dropped.
//!
//! Each such body was reported lowered with no tag, spliced into the crate module, passed
//! `-Ztrust-ir-lower=strict`, and counted `route=thir result=ok` in probe channel C. Measured
//! on main f5dd1d805a with `stores.rs`: every function marked `main: erased` there.
//!
//! The rule now: a right-hand side the lane does not model is lowered for its effects unless
//! a THIR allow-list proves it has none (`effect_free_discard`); if it cannot be lowered, the
//! body declines with a tag. And a plain-data whole-value store (`self.pair = (a, b)`) stores
//! the value it computed instead of `undef`.
//!
//! The second half pins probe channel C on the same fixture: `ok` is not printed for a body
//! the probe can see is abstracted (an elided drop, an `undef`, a layout-less opaque struct
//! lane), and a loop erased beside a faithful one reads `erased(loop)`, not `ok`. Since step 2
//! increment 3 (owner ruling D17) the instance lane's own frozen gate refuses an elided drop, an
//! opaque collapse and an `undef` before assembly is asked, so those bodies read `refused(..)`
//! naming the gate; the probe's own abstraction classes are pinned by `instance_probe.rs`'s
//! `visible_abstractions_are_not_ok`.
//@ ignore-cross-compile

use std::collections::BTreeMap;

use run_make_support::{cmd, rfs, rustc, rustc_path, serde_json, trust_ir};

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

/// The instruction text of each line (the `; #loc` trailer dropped).
fn code(f: &IrFn) -> impl Iterator<Item = &str> {
    f.lines.iter().map(|l| l.split(';').next().unwrap_or(""))
}

/// `true` iff the function's CFG has a cycle (blocks and branch targets read off the text).
fn has_cycle(f: &IrFn) -> bool {
    let mut edges: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    let mut current: Option<u32> = None;
    for line in code(f) {
        if let Some(rest) = line.strip_prefix("bb") {
            let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
            if let Ok(n) = digits.parse() {
                current = Some(n);
                edges.entry(n).or_default();
                continue;
            }
        }
        let t = line.trim_start();
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
    for line in code(f) {
        for (i, _) in line.match_indices("call @func.") {
            let digits: String =
                line[i + 11..].chars().take_while(|c| c.is_ascii_digit()).collect();
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
            "stores.rs",
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name=stores",
            "-Copt-level=0",
            "-Ccodegen-units=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-dump=ir:stores-ir",
            "--out-dir",
            "out",
        ])
        .run();

    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("stores-ir/stores.coverage.json"))
            .expect("published coverage must be valid JSON");
    let rows = report["bodies"].as_array().expect("complete body inventory");
    let row = |path: &str| {
        let matching: Vec<_> = rows.iter().filter(|r| r["def_path"] == path).collect();
        assert_eq!(matching.len(), 1, "missing/duplicate row {path}");
        matching[0]
    };
    // Headers by def path (WS5.2 names them by link symbol; `trust_ir::by_display_path`).
    let text = trust_ir::by_display_path(&rfs::read_to_string("stores-ir/stores.trust-ir.txt"));
    let (fns, order) = parse_module(&text);
    let body = |name: &str| {
        fns.get(name)
            .map(|f| f.lines.join("\n"))
            .unwrap_or_else(|| format!("<`{name}` has no body in the module>"))
    };

    // THE INVARIANT: a body whose field store has an effectful right-hand side is either
    // spliced WITH that effect (the call is in the body; a source loop is a loop), or it is
    // declined with a tag / names its splice refusal. "Spliced without the call" is the
    // erasure this test exists to catch.
    let effects: [(&str, &str, bool); 10] = [
        ("S::set_rows_call", "rows_after_close", false),
        ("S::set_boxed_call", "close_then_some", false),
        ("S::set_boxed_some", "close_ret", false),
        ("S::set_mode_if", "close_ret", false),
        ("S::set_name", "close_ret", false),
        ("S::set_n", "close_ret", false),
        ("Spawn::reset_and_close", "close", true),
        ("Spawn::reset_and_close_counted", "close", true),
        ("Holder::set_pair", "bump", false),
        ("some_tuple_is_some", "close_ret", false),
    ];
    for (name, effect, looped) in effects {
        let r = row(name);
        if r["spliced"] == true {
            let f = &fns[name];
            assert!(
                callees(f, &order).iter().any(|c| c == effect),
                "`{name}` is spliced WITHOUT its `{effect}` call — the right-hand side was \
                 erased:\n{}",
                body(name)
            );
            if looped {
                assert!(has_cycle(f), "`{name}` is spliced with its loop erased:\n{}", body(name));
            }
        } else if r["lowered"] == true {
            assert!(r["splice_refusal"].is_string(), "a dropped body names why: {r}");
        } else {
            assert!(
                r["unsupported"].as_array().is_some_and(|t| !t.is_empty()),
                "a declined body carries its tag: {r}"
            );
        }
    }

    // PINNED BY NAME: the measured erasures that now lower FAITHFULLY — spliced, with the
    // effect the lane used to drop called in the body.
    for name in [
        "S::set_rows_call",
        "S::set_boxed_call",
        "Spawn::reset_and_close",
        "Spawn::reset_and_close_counted",
    ] {
        assert_eq!(row(name)["spliced"], true, "`{name}` must lower with its effect and splice");
    }

    // The effect-free control keeps the lane: `self.boxed = None` needs no lowering.
    assert_eq!(row("S::clear_boxed")["spliced"], true, "{}", body("S::clear_boxed"));

    // Plain data stores the value it computed: no `undef` stands in for it.
    for name in ["Outer::set_pair", "Outer::set_inner", "Outer::set_arr", "Outer::set_opt"] {
        assert_eq!(row(name)["spliced"], true, "`{name}` must splice: {}", row(name));
        assert!(
            !code(&fns[name]).any(|l| l.contains("undef")),
            "`{name}` stores `undef` in place of the value it computed:\n{}",
            body(name)
        );
    }

    // ── Probe channel C on the same fixture ────────────────────────────────
    let probe = rustc()
        .input("stores.rs")
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Ccodegen-units=1")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-instance-flip-probe=*")
        .arg("-Zno-steal-thir")
        .run()
        .stderr_utf8();
    let c_row = |def: &str| {
        let found: Vec<&str> = probe
            .lines()
            .filter(|l| l.starts_with("TRUST-WALLA-PROBE C sym="))
            .filter(|l| l.contains(&format!(" def={def} ")))
            .collect();
        assert_eq!(found.len(), 1, "one channel-C row for `{def}`:\n{probe}");
        found[0].to_string()
    };
    let summary = probe
        .lines()
        .find(|l| l.starts_with("TRUST-WALLA-PROBE C summary"))
        .unwrap_or_else(|| panic!("channel C printed no summary:\n{probe}"));
    for field in ["erased=0", "panics=0", "abstracted="] {
        assert!(summary.contains(field), "summary must say `{field}`: {summary}");
    }
    // Plain data, layout-carrying struct, no drop: coverage.
    for def in ["Outer::set_pair", "Outer::set_opt"] {
        let r = c_row(def);
        assert!(r.contains("route=thir result=ok("), "{r}");
    }
    // `S` is registered without a layout (its `Vec`/`String`/enum fields are `()` lanes), and
    // each of these setters drops the old field value, which the producer does not model;
    // `Holder::p` and `some_tuple_is_some`'s `Option` are modelled as their discriminant `bool`
    // (`opaque_collapse`): spliced, but not coverage. The instance lane refuses each of them
    // itself now (`refused(..)`), which is not coverage either.
    for def in [
        "S::set_rows_call",
        "S::set_boxed_call",
        "Spawn::reset_and_close_counted",
        "Holder::set_pair",
        "some_tuple_is_some",
    ] {
        let r = c_row(def);
        assert!(!r.contains("result=ok("), "an abstracted body is not coverage: {r}");
        assert!(
            r.contains("result=abstracted(")
                || r.contains("result=assembly-refused(")
                || r.contains("result=refused("),
            "{r}"
        );
    }
    // Each abstraction is named — since step 2 increment 3 by the instance lane's frozen gate,
    // which refuses it before assembly is asked (D17: no seam differential judges an instance
    // body). `S::set_n` stores a scalar faithfully but through the layout-less `S`, whose `()`
    // lanes are an opaque collapse; `S::set_boxed_call` also havocs the discriminant and drops the
    // old `Box`, and the gate names the collapse first; `some_tuple_is_some`'s `Option` is its
    // discriminant; `Holder::set_pair` still holds a pending-const sentinel, refused before the
    // lanes; `guard_scope` and `Guard::drop` hold a needs-drop value (the drop gate reads every
    // place type, so `self.0` through `&mut Guard` counts; increment 4 retires it).
    let expect = [
        ("S::set_n", "result=refused(LaneRefused(\"opaque collapse\"))"),
        ("S::set_boxed_call", "result=refused(LaneRefused(\"opaque collapse\"))"),
        ("some_tuple_is_some", "result=refused(LaneRefused(\"opaque collapse\"))"),
        ("Holder::set_pair", "result=refused(PendingConsts)"),
        ("guard_scope", "result=refused(LaneRefused(\"drop-bearing\"))"),
        ("<Guard as std::ops::Drop>::drop", "result=refused(LaneRefused(\"drop-bearing\"))"),
    ];
    for (def, want) in expect {
        let r = c_row(def);
        assert!(r.contains(want), "`{def}` must read `{want}`: {r}");
    }
}
