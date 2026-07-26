// Faithfulness gate for the TrustTS type eraser.
//
// Node's native type-stripper is the oracle for "erasable TypeScript". For
// every erasable corpus file we assert that running `strip(source)` -> JS ->
// Node produces byte-identical stdout to running Node on the original `.ts`.
// For every `refuse_*` file we assert `strip` returns `Refused` (fail-closed).
//
// The Node-differential tests skip gracefully if no Node binary is found; the
// pure-Rust unit tests always run.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_ts_strip::{StripOutcome, strip};

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

/// Locate a runnable Node. Honors `TRUSTTS_NODE`, then the pinned campaign
/// path, then `node` on PATH. Returns None if none runs.
fn find_node() -> Option<String> {
    let mut candidates: Vec<String> = Vec::new();
    if let Ok(p) = std::env::var("TRUSTTS_NODE") {
        candidates.push(p);
    }
    if let Ok(home) = std::env::var("HOME") {
        candidates.push(format!("{home}/.local/opt/node-v24.5.0/bin/node"));
    }
    candidates.push("node".to_string());
    candidates.into_iter().find(|candidate| {
        Command::new(candidate)
            .arg("--version")
            .output()
            .is_ok_and(|output| output.status.success())
    })
}

/// Run `node <path>` and return its stdout bytes on success (exit 0).
fn node_run(node: &str, path: &Path) -> Result<Vec<u8>, String> {
    let out = Command::new(node).arg(path).output().map_err(|e| format!("spawn node: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "node exited {:?}: {}",
            out.status.code(),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(out.stdout)
}

fn corpus_files() -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(corpus_dir())
        .expect("read corpus dir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().map(|x| x == "ts").unwrap_or(false))
        .collect();
    v.sort();
    v
}

fn is_refuse(p: &Path) -> bool {
    p.file_name().and_then(|n| n.to_str()).map(|n| n.starts_with("refuse_")).unwrap_or(false)
}

/// Every `refuse_*` file must be fail-closed refused. (No Node required.)
#[test]
fn refuse_set_is_fail_closed() {
    let files = corpus_files();
    let refuse: Vec<_> = files.iter().filter(|p| is_refuse(p)).collect();
    assert!(refuse.len() >= 8, "expected >=8 refuse fixtures, found {}", refuse.len());
    for p in refuse {
        let src = std::fs::read_to_string(p).unwrap();
        match strip(&src) {
            StripOutcome::Refused(_) => {}
            StripOutcome::Js(_) => {
                panic!("{}: expected Refused (not erasable) but got Js", p.display())
            }
        }
    }
}

/// Every erasable file must strip to `Js` and, via Node, reproduce the oracle
/// output byte-for-byte.
#[test]
fn erasable_set_matches_node_oracle() {
    let Some(node) = find_node() else {
        eprintln!("SKIP: no runnable Node found; erasable differential not exercised");
        return;
    };

    let files = corpus_files();
    let erasable: Vec<_> = files.iter().filter(|p| !is_refuse(p)).collect();
    assert!(erasable.len() >= 24, "expected >=24 erasable fixtures, found {}", erasable.len());

    let tmp = std::env::temp_dir().join(format!("trust-ts-strip-{}", std::process::id()));
    std::fs::create_dir_all(&tmp).unwrap();

    let mut proven = 0usize;
    let mut failures: Vec<String> = Vec::new();

    for p in &erasable {
        let src = std::fs::read_to_string(p).unwrap();
        let stem = p.file_stem().unwrap().to_str().unwrap();

        // Oracle: Node running the original .ts (native strip).
        let oracle = match node_run(&node, p) {
            Ok(o) => o,
            Err(e) => {
                failures.push(format!("{stem}: oracle failed: {e}"));
                continue;
            }
        };

        // Candidate: strip -> JS -> Node.
        let js = match strip(&src) {
            StripOutcome::Js(js) => js,
            StripOutcome::Refused(r) => {
                failures.push(format!("{stem}: unexpectedly Refused: {r}"));
                continue;
            }
        };
        let js_path = tmp.join(format!("{stem}.js"));
        std::fs::write(&js_path, &js).unwrap();
        let got = match node_run(&node, &js_path) {
            Ok(o) => o,
            Err(e) => {
                failures.push(format!("{stem}: stripped JS failed under Node: {e}"));
                continue;
            }
        };

        if got == oracle {
            proven += 1;
        } else {
            failures.push(format!(
                "{stem}: stdout diverged\n  oracle: {:?}\n  got:    {:?}",
                String::from_utf8_lossy(&oracle),
                String::from_utf8_lossy(&got),
            ));
        }
    }

    let _ = std::fs::remove_dir_all(&tmp);

    eprintln!(
        "TrustTS faithfulness: {proven}/{} erasable files byte-identical to Node",
        erasable.len()
    );
    assert!(failures.is_empty(), "faithfulness failures:\n{}", failures.join("\n"));
    assert_eq!(proven, erasable.len(), "not all erasable files proven");
}

// ---- pure-Rust unit tests (no Node) ----

#[test]
fn strips_simple_annotation() {
    let out = strip("const x: number = 1;\nconsole.log(x);\n");
    match out {
        StripOutcome::Js(js) => {
            assert!(!js.contains(": number"), "annotation not erased: {js:?}");
            assert!(js.contains("const x"));
            assert!(js.contains("console.log(x)"));
            // width-preserving: byte length is identical.
            assert_eq!(js.len(), "const x: number = 1;\nconsole.log(x);\n".len());
        }
        StripOutcome::Refused(r) => panic!("unexpected refusal: {r}"),
    }
}

#[test]
fn refuses_enum_and_namespace() {
    assert!(matches!(strip("enum E { A }"), StripOutcome::Refused(_)));
    assert!(matches!(strip("namespace N { export const x = 1; }"), StripOutcome::Refused(_)));
    assert!(matches!(
        strip("class C { constructor(private x: number) {} }"),
        StripOutcome::Refused(_)
    ));
}

#[test]
fn never_panics_on_garbage() {
    // Totality: arbitrary inputs yield an outcome, never a panic.
    for s in ["", "<<<<", ":::", "const a: ", "function f<", "`${", "/*"] {
        let _ = strip(s);
    }
}
