// headcheck: development harness for adversarial engine-vs-head probing.
// Runs the interpreter head on a trace-driver manifest (same JSON the
// engines consume) and either prints the head verdict or compares it against
// captured engine driver stdout files.
//
//   headcheck <manifest.json> [engine-stdout-file...]
//
// Prints: `NOCOV <reason>`, or `TRACE <json>`, then per engine file
// `EQUAL <file>` / `DIVERGE <file>: <explanation>` / `ENGINE-ERR <file>`.
// Exit code 1 iff any comparison diverged.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use trust_js_interp::{evaluate_case, InterpOutcome};
use trust_js_trace::{explain_divergence, extract_trace, traces_equal};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let manifest_path = args.get(1).expect("usage: headcheck <manifest.json> [engine-out...]");
    let manifest: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(manifest_path).expect("read manifest"))
            .expect("parse manifest");
    let includes: Vec<String> = manifest["includes"]
        .as_array()
        .expect("includes")
        .iter()
        .map(|p| std::fs::read_to_string(p.as_str().expect("path")).expect("read include"))
        .collect();
    let include_refs: Vec<&str> = includes.iter().map(String::as_str).collect();
    let body = std::fs::read_to_string(manifest["source"].as_str().expect("source"))
        .expect("read body");
    let strict = manifest["mode"].as_str() == Some("strict");

    let outcome = evaluate_case(&include_refs, &body, strict);
    let mine = match outcome {
        InterpOutcome::NoCoverage { reason } => {
            println!("NOCOV {reason}");
            return;
        }
        InterpOutcome::Trace(t) => {
            println!("TRACE {}", serde_json::to_string(&t).expect("serialize"));
            t
        }
    };
    let mut bad = false;
    for f in &args[2..] {
        let stdout = std::fs::read(f).expect("read engine stdout");
        match extract_trace(&stdout) {
            Ok(engine) => {
                if traces_equal(&mine, &engine) {
                    println!("EQUAL {f}");
                } else {
                    bad = true;
                    println!(
                        "DIVERGE {f}: {}",
                        explain_divergence(&mine, &engine)
                            .unwrap_or_else(|| "unlocalized".to_string())
                    );
                }
            }
            Err(e) => {
                bad = true;
                println!("ENGINE-ERR {f}: {e:?}");
            }
        }
    }
    if bad {
        std::process::exit(1);
    }
}
