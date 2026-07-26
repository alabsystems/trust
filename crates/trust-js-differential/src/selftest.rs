// The negative-control + D1-acceptance gate:
//   Leg A (sanity):   embedded mini-cases (object order, -0/NaN, throwing
//                     getter, Date.now/Math.random firewall, try/catch,
//                     timers, assert.js harness) must be trace-equal on Node
//                     and Bun.
//   Leg B (teeth):    a corrupted head — at the parsed-trace level AND at the
//                     stdout-bytes level (forged trailing sentinel; the LAST
//                     sentinel must win) — MUST be reported unequal. A
//                     corruption that is not flagged is a toothless harness
//                     => FAIL.
//   Leg C (D1):       20-run byte-identical determinism per engine on the
//                     firewall case (raw sentinel-line compare) and the
//                     throwing-getter case completes Normal (observation is
//                     non-invasive).
// Exit 0 only if ALL legs pass with correct polarity.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::path::{Path, PathBuf};
use std::time::Duration;

use trust_js_trace::{extract_trace, traces_equal, Completion, HostEvent, ObservableTrace};

use crate::heads::{
    last_sentinel_line, write_driver, AssembledCase, BunHead, EngineHead, HeadResult, NodeHead,
    ProcessHead, RunMode,
};

pub struct SelftestOpts {
    pub corpus: PathBuf,
    pub node: PathBuf,
    pub bun: PathBuf,
}

struct MiniCase {
    name: &'static str,
    body: &'static str,
    with_harness: bool,
}

const FIREWALL_BODY: &str = "console.log(Date.now(), Math.random(), Date.now(), new Date().getTime());\n'firewall';";
const GETTER_BODY: &str = "const o = { get x() { throw new Error('boom'); } };\nconsole.log(o);\n'getter-not-invoked';";

const MINI_CASES: &[MiniCase] = &[
    MiniCase {
        name: "object-order",
        body: "const obj = {}; obj.b = 1; obj[2] = 'two'; obj.a = 3; obj[1] = 'one';\nobj[Symbol('desc')] = 4;\nconsole.log(obj);\n'order';",
        with_harness: false,
    },
    MiniCase {
        name: "neg-zero-nan",
        body: "console.log(-0, 0, NaN, Infinity, -Infinity, 0.1 + 0.2);\n'-0-nan';",
        with_harness: false,
    },
    MiniCase { name: "throwing-getter", body: GETTER_BODY, with_harness: false },
    MiniCase { name: "firewall", body: FIREWALL_BODY, with_harness: false },
    MiniCase {
        name: "try-catch",
        body: "try { null.x; } catch (e) { console.log(e instanceof TypeError, e.name); }\n'caught';",
        with_harness: false,
    },
    MiniCase {
        name: "timers",
        body: "setTimeout(() => console.log('t1'), 10);\nsetTimeout(() => console.log('t0'), 5);\n'sync-done';",
        with_harness: false,
    },
    MiniCase {
        name: "assert-harness",
        body: "assert.sameValue(1 + 1, 2);\nassert.throws(TypeError, function() { null.x; });\n'assert-ok';",
        with_harness: true,
    },
];

fn assemble(corpus: &Path, mini: &MiniCase, body: &str) -> AssembledCase {
    let includes = if mini.with_harness {
        vec![corpus.join("harness/assert.js"), corpus.join("harness/sta.js")]
    } else {
        vec![]
    };
    AssembledCase {
        rel_path: format!("selftest/{}", mini.name),
        source_path: PathBuf::new(),
        body: body.to_string(),
        includes,
        mode: RunMode::Bare,
        is_async: false,
        timeout: Duration::from_secs(10),
    }
}

fn expect_trace(name: &str, engine: &str, res: HeadResult) -> Result<ObservableTrace, String> {
    match res {
        HeadResult::Trace(t) => Ok(t),
        HeadResult::NoCoverage(m) => Err(format!("{name}: {engine} refused coverage: {m}")),
        HeadResult::HarnessError(m) => Err(format!("{name}: {engine} harness error: {m}")),
    }
}

pub fn run_selftest(opts: &SelftestOpts) -> anyhow::Result<i32> {
    let dir = tempfile::tempdir()?;
    let driver = write_driver(dir.path())?;
    let node = NodeHead::new(opts.node.clone(), driver.clone(), dir.path().join("node"))?;
    let bun = BunHead::new(opts.bun.clone(), driver.clone(), dir.path().join("bun"))?;
    let mut failures: Vec<String> = Vec::new();

    // ---- Leg A: sanity ----
    println!("selftest leg A (sanity): {} embedded cases on node + bun", MINI_CASES.len());
    let mut firewall_pair: Option<(ObservableTrace, Vec<u8>, ObservableTrace)> = None;
    for mini in MINI_CASES {
        let case = assemble(&opts.corpus, mini, mini.body);
        let pair = (|| -> Result<(ObservableTrace, ObservableTrace), String> {
            let nt = expect_trace(mini.name, "node", node.run(&case))?;
            let bt = expect_trace(mini.name, "bun", bun.run(&case))?;
            Ok((nt, bt))
        })();
        match pair {
            Ok((nt, bt)) => {
                if traces_equal(&nt, &bt) {
                    println!("  A {:<16} trace-equal OK", mini.name);
                } else {
                    let why = trust_js_trace::explain_divergence(&nt, &bt)
                        .unwrap_or_else(|| "differs".to_string());
                    failures.push(format!("leg A {}: node vs bun diverge: {why}", mini.name));
                }
                if mini.name == "firewall" {
                    // Keep the raw node stdout for leg B's byte-level forgery.
                    let raw = node.0.run_driver_raw(&case).map_err(|e| anyhow::anyhow!(e))?;
                    firewall_pair = Some((nt, raw.stdout, bt));
                }
            }
            Err(e) => failures.push(format!("leg A {e}")),
        }
    }

    // ---- Leg B: teeth (negative control) ----
    println!("selftest leg B (teeth): corrupted head MUST be flagged");
    match &firewall_pair {
        Some((node_trace, node_stdout, bun_trace)) => {
            // Parsed-trace corruption: append a synthetic HostEvent.
            let mut corrupted = node_trace.clone();
            corrupted.events.push(HostEvent::Host { v: "__selftest_corruption__".to_string() });
            if traces_equal(&corrupted, bun_trace) {
                failures.push(
                    "leg B: parsed-trace corruption NOT flagged (traces_equal returned true) — toothless harness"
                        .to_string(),
                );
            } else {
                println!("  B parsed-trace corruption flagged UNEQUAL OK");
            }

            // Stdout-bytes corruption: forge a trailing sentinel carrying the
            // corrupted trace; extract_trace must take the LAST sentinel.
            let forged_json = serde_json::to_string(&corrupted)?;
            let mut forged = node_stdout.clone();
            forged.extend_from_slice(b"\n__TRUST_JS_TRACE_V1__");
            forged.extend_from_slice(forged_json.as_bytes());
            forged.extend_from_slice(b"\n");
            match extract_trace(&forged) {
                Ok(extracted) => {
                    if extracted != corrupted {
                        failures.push(
                            "leg B: extract_trace did not take the LAST sentinel line".to_string(),
                        );
                    } else if traces_equal(&extracted, bun_trace) {
                        failures.push(
                            "leg B: stdout-bytes corruption NOT flagged — toothless harness"
                                .to_string(),
                        );
                    } else {
                        println!("  B stdout-bytes corruption (last sentinel wins) flagged UNEQUAL OK");
                    }
                }
                Err(e) => failures.push(format!("leg B: forged stdout failed to parse: {e}")),
            }
        }
        None => failures.push("leg B: firewall case unavailable (leg A failed)".to_string()),
    }

    // ---- Leg C: D1 acceptance ----
    println!("selftest leg C (D1): 20-run byte-identical determinism per engine");
    let firewall = assemble(
        &opts.corpus,
        &MiniCase { name: "firewall", body: FIREWALL_BODY, with_harness: false },
        FIREWALL_BODY,
    );
    for (engine_name, head) in [("node", &node.0), ("bun", &bun.0)] {
        match determinism_lines(head, &firewall, 20) {
            Ok(lines) => {
                let first = &lines[0];
                if lines.iter().all(|l| l == first) {
                    println!("  C {engine_name}: 20/20 sentinel lines byte-identical OK");
                } else {
                    let distinct = lines.iter().collect::<std::collections::BTreeSet<_>>().len();
                    failures.push(format!(
                        "leg C: {engine_name} nondeterministic — {distinct} distinct sentinel lines over 20 runs"
                    ));
                }
            }
            Err(e) => failures.push(format!("leg C: {engine_name}: {e}")),
        }
    }
    // Throwing getter completes Normal (observation is non-invasive).
    let getter = assemble(
        &opts.corpus,
        &MiniCase { name: "throwing-getter", body: GETTER_BODY, with_harness: false },
        GETTER_BODY,
    );
    for head in [&node as &dyn EngineHead, &bun as &dyn EngineHead] {
        let engine_name = head.name();
        match expect_trace("throwing-getter", engine_name, head.run(&getter)) {
            Ok(t) => match t.completion {
                Completion::Normal { .. } => {
                    println!("  C {engine_name}: throwing-getter completes Normal (non-invasive) OK");
                }
                other => failures.push(format!(
                    "leg C: {engine_name} throwing-getter completed {other:?}, want Normal — projection invoked an accessor?"
                )),
            },
            Err(e) => failures.push(format!("leg C: {e}")),
        }
    }

    if failures.is_empty() {
        println!("selftest: ALL LEGS PASS");
        Ok(0)
    } else {
        for f in &failures {
            eprintln!("selftest FAIL: {f}");
        }
        Ok(1)
    }
}

fn determinism_lines(
    head: &ProcessHead,
    case: &AssembledCase,
    runs: usize,
) -> Result<Vec<String>, String> {
    let mut lines = Vec::with_capacity(runs);
    for i in 0..runs {
        let out = head.run_driver_raw(case)?;
        if out.timed_out {
            return Err(format!("run {i}: timeout"));
        }
        let line = last_sentinel_line(&out.stdout).ok_or_else(|| format!("run {i}: no sentinel"))?;
        lines.push(line);
    }
    Ok(lines)
}

#[cfg(test)]
mod itest {
    //! Env-gated integration test: set TRUST_JS_NODE (and optionally
    //! TRUST_JS_BUN) to run legs A + C style checks against real engines.
    use super::*;

    #[test]
    fn env_gated_real_engine_legs() {
        let Ok(node_path) = std::env::var("TRUST_JS_NODE") else {
            eprintln!("TRUST_JS_NODE unset; skipping engine integration test");
            return;
        };
        let second = std::env::var("TRUST_JS_BUN").unwrap_or_else(|_| node_path.clone());
        let dir = tempfile::tempdir().unwrap();
        let driver = write_driver(dir.path()).unwrap();
        let a = ProcessHead::new("node", node_path.into(), driver.clone(), dir.path().join("a"))
            .unwrap();
        let b = ProcessHead::new("bun", second.into(), driver, dir.path().join("b")).unwrap();

        // Leg A on a couple of embedded cases.
        for mini in &MINI_CASES[..2] {
            let case = AssembledCase {
                rel_path: format!("itest/{}", mini.name),
                source_path: PathBuf::new(),
                body: mini.body.to_string(),
                includes: vec![],
                mode: RunMode::Bare,
                is_async: false,
                timeout: Duration::from_secs(10),
            };
            let ta = expect_trace(mini.name, "a", a.run(&case)).unwrap();
            let tb = expect_trace(mini.name, "b", b.run(&case)).unwrap();
            assert!(traces_equal(&ta, &tb), "{}: heads diverge", mini.name);
        }

        // Leg C determinism (3 runs to keep the test fast).
        let firewall = AssembledCase {
            rel_path: "itest/firewall".to_string(),
            source_path: PathBuf::new(),
            body: FIREWALL_BODY.to_string(),
            includes: vec![],
            mode: RunMode::Bare,
            is_async: false,
            timeout: Duration::from_secs(10),
        };
        let lines = determinism_lines(&a, &firewall, 3).unwrap();
        assert!(lines.iter().all(|l| l == &lines[0]), "nondeterministic sentinel lines");
    }
}
