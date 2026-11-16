// clean-axioms: the `clean axioms` CLI — the success-metric instrument for the
// Clean-dependent-types program (docs/PLAN-clean-dependent-type-reflection.md).
//
// Reads a JSON proof obligation { term, context }, computes the transitive
// axiom closure of the proof term, and reports it. With `--require-axioms 3` it
// is a gate: exit non-zero unless the closure is a subset of the three
// foundational kernel axioms { propext, Quot.sound, Classical.choice } with no
// unresolved constants — i.e. "proven in Clean modulo 3 axioms".
//
// Input format (JSON):
//   {
//     "term": <ProofTerm>,
//     "context": [ { "name": "P", "entry": { "Axiom": { "ty": {"Sort":0} } } }, ... ]
//   }
// where <ProofTerm> uses serde's external tagging, e.g. {"Const":"propext"},
// {"App":[<t>,<t>]}, {"Sort":0}, {"Pi":{"binder_name":"_","domain":<t>,"codomain":<t>}}.
//
// The context may NOT declare a kernel-owned name (2026-09-28): a foundation
// (`propext`, `Quot.sound`, `Classical.choice`, the `Quot` primitives) or a
// trust marker (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`). Such a
// context is REFUSED — exit 2, no report — because no declaration in this term
// language can be the kernel's canonical one (see
// `trust_clean::reserved_declaration_refusal`). A term that names one of the
// three foundations needs no declaration: it means the kernel's own axiom.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::Read;
use std::process::ExitCode;

use trust_clean::axioms::{
    FOUNDATIONAL_AXIOMS, SuppliedObligation, axiom_closure, build_supplied_context,
};

struct Args {
    path: Option<String>,
    require_foundational: bool,
    json: bool,
}

const USAGE: &str = "\
clean-axioms — transitive axiom-closure auditor (the `clean axioms` instrument)

USAGE:
    clean-axioms [OPTIONS] [FILE]

ARGS:
    FILE                 JSON proof obligation { term, context }. '-' or omitted = stdin.

OPTIONS:
    --require-axioms <N> Gate mode: exit non-zero unless the closure is within the
                         N foundational axioms with no unresolved constants. Only
                         N=3 (the foundational set) is supported.
    --json               Emit the report as JSON instead of human-readable text.
    -h, --help           Print this help.

The foundational three: propext, Quot.sound, Classical.choice. They are the
kernel's own axioms: reference them without declaring them. A context that
declares any kernel-owned name (a foundation, a Quot primitive, or a trust
marker such as sorryAx) is REFUSED with exit status 2.";

fn parse_args() -> Result<Args, String> {
    let mut path = None;
    let mut require_foundational = false;
    let mut json = false;
    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "-h" | "--help" => {
                println!("{USAGE}");
                std::process::exit(0);
            }
            "--json" => json = true,
            "--require-axioms" => {
                let n = it.next().ok_or("--require-axioms needs a value")?;
                if n != "3" {
                    return Err(format!(
                        "only --require-axioms 3 is supported (the foundational set); got {n}"
                    ));
                }
                require_foundational = true;
            }
            other if other.starts_with("--") => return Err(format!("unknown flag: {other}")),
            other => {
                if path.is_some() {
                    return Err(format!("unexpected extra argument: {other}"));
                }
                path = Some(other.to_string());
            }
        }
    }
    Ok(Args { path, require_foundational, json })
}

fn read_input(path: &Option<String>) -> Result<String, String> {
    match path.as_deref() {
        None | Some("-") => {
            let mut buf = String::new();
            std::io::stdin().read_to_string(&mut buf).map_err(|e| format!("reading stdin: {e}"))?;
            Ok(buf)
        }
        Some(p) => std::fs::read_to_string(p).map_err(|e| format!("reading {p}: {e}")),
    }
}

fn run() -> Result<bool, String> {
    let args = parse_args()?;
    let input = read_input(&args.path)?;
    let obligation: SuppliedObligation =
        serde_json::from_str(&input).map_err(|e| format!("parsing obligation JSON: {e}"))?;
    let ctx = build_supplied_context(obligation.context)?;
    let report = axiom_closure(&obligation.term, &ctx);
    let clean = report.is_modulo_foundational();

    if args.json {
        let foundational: Vec<String> = report.foundational().into_iter().collect();
        let residual: Vec<String> = report.residual().into_iter().collect();
        let unresolved: Vec<String> = report.unresolved.iter().cloned().collect();
        // Hand-rolled to avoid leaking internal types; stable shape for tools.
        println!(
            "{{\"clean\":{clean},\"foundational\":{},\"residual\":{},\"unresolved\":{}}}",
            serde_json::to_string(&foundational).unwrap(),
            serde_json::to_string(&residual).unwrap(),
            serde_json::to_string(&unresolved).unwrap(),
        );
    } else {
        let foundational = report.foundational();
        let residual = report.residual();
        let unresolved = &report.unresolved;
        if clean {
            println!("clean axioms: CLEAN \u{2713}  (proven modulo \u{2264}3 foundational axioms)");
        } else {
            println!("clean axioms: NOT CLEAN \u{2717}");
        }
        println!(
            "  foundational used ({}): {}",
            foundational.len(),
            join_or_dash(foundational.iter())
        );
        if residual.is_empty() {
            println!("  residual (0)");
        } else {
            println!("  residual ({}):", residual.len());
            for a in &residual {
                println!("    {a}    \u{2190} trusted, must be reconstructed");
            }
        }
        if unresolved.is_empty() {
            println!("  unresolved (0)");
        } else {
            println!("  unresolved ({}):", unresolved.len());
            for c in unresolved {
                println!("    {c}    \u{2190} dangling constant, not kernel-resolved");
            }
        }
        println!("  foundational set: {}", FOUNDATIONAL_AXIOMS.join(", "));
    }

    // In gate mode, "ok" requires clean. In report mode, parsing/reporting
    // succeeded, so it is ok regardless of cleanliness.
    Ok(if args.require_foundational { clean } else { true })
}

fn main() -> ExitCode {
    match run() {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(msg) => {
            eprintln!("clean-axioms: {msg}");
            ExitCode::from(2)
        }
    }
}

fn join_or_dash<'a>(mut it: impl Iterator<Item = &'a String>) -> String {
    match it.next() {
        None => "—".to_string(),
        Some(first) => {
            let mut s = first.clone();
            for x in it {
                s.push_str(", ");
                s.push_str(x);
            }
            s
        }
    }
}
