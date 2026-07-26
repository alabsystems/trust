// trust-js-autoform: the reachable front door of the M4 strict-mode arithmetic
// floor.
//
// The lowering has always been callable; nothing called it. That is worse than
// it sounds for an untrusted frontend: a lane with no entry point is a lane
// nobody can inspect, and "inspectable" is half of what the doctrine demands of
// a frontend in exchange for admitting it at all.
//
// What this prints, in order, is exactly the evidence chain a reader needs to
// decide what the Rust artifact is worth:
//
//   * the firewall standing — who proposed this, and what that provenance
//     permits (a goal, never a hypothesis or an axiom);
//   * the pinned fidelity manifest and its digest — WHICH corpus and WHICH
//     oracle judged the lowering, named before the verdict rather than after;
//   * the delta ledger — how many samples were checked bit-for-bit;
//   * the Rust artifact itself.
//
// A refusal prints the reason and exits non-zero. There is no partial output:
// a lowering that could not be checked is not an artifact, and printing one
// would invite someone to use it.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::path::Path;
use std::process::ExitCode;

use trust_js_autoform::fidelity;
use trust_types::frontend_firewall::{ProofRole, admit_role};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [path] = args.as_slice() else {
        eprintln!(
            "usage: trust-js-autoform <file.js|file.ts>\n\n\
             Lowers one strict-mode pure-arithmetic function (or module) to an\n\
             inspectable Rust artifact, and emits it ONLY if every sample in the\n\
             pinned fidelity corpus matches the interpreter oracle bit-for-bit."
        );
        return ExitCode::from(2);
    };

    let source = match std::fs::read_to_string(path) {
        Ok(source) => source,
        Err(e) => {
            eprintln!("trust-js-autoform: {path}: {e}");
            return ExitCode::from(2);
        }
    };

    let is_typescript = Path::new(path).extension().is_some_and(|e| e == "ts");
    let lowered = if is_typescript {
        trust_js_autoform::lower_ts_and_verify(&source)
    } else {
        trust_js_autoform::lower_and_verify(&source)
    };

    let lowered = match lowered {
        Ok(lowered) => lowered,
        Err(refusal) => {
            // A refusal is the sound outcome, not an error in the pejorative
            // sense — say which one it was and stop.
            eprintln!("trust-js-autoform: refused: {refusal:?}");
            return ExitCode::from(1);
        }
    };

    let pin = fidelity::pin();
    let origin = pin.origin(path.clone());
    let provenance = origin.provenance();

    println!("// provenance: {provenance}");
    println!("// elaborator: {}", origin.elaborator);
    println!(
        "// firewall: this artifact and any obligation over it may be a {}; \
         admitting it as a {} is refused ({})",
        ProofRole::Goal,
        ProofRole::Hypothesis,
        match admit_role(provenance, ProofRole::Hypothesis) {
            Ok(()) => "unexpectedly permitted".to_string(),
            Err(rejection) => rejection.to_string(),
        }
    );
    println!("// fidelity manifest: {} ({})", pin.id(), pin.digest());
    println!("// oracle: {}", fidelity::ORACLE_NAME);
    println!(
        "// delta ledger: {} samples checked bit-for-bit, all equal",
        lowered.ledger.samples_checked
    );
    println!(
        "// scope: agreement is claimed ONLY over that corpus; it is bounded \
         differential evidence, not a proof"
    );
    println!();
    println!("{}", lowered.rust_source);
    ExitCode::SUCCESS
}
