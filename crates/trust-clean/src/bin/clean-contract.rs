// clean-contract: the `clean contract` CLI — reflect a function contract into a
// genuine Clean DEPENDENT TYPE and kernel-check it (the Curry-Howard close of
// M3; docs/PLAN-clean-dependent-type-reflection.md).
//
// Reads a JSON contract spec and builds
//   Π(p₁:Int) … Π(pₙ:Int) → Π(_ : ⟦pre⟧) → Trust.Sigma Int (λ ret. ⟦post⟧)
// then type-checks it against the carrier context. A function inhabiting this
// type IS a proof of the contract; the kernel accepting the type as a well-formed
// `Type` (Sort 1) is what "the spec is the type" means, validated.
//
// Input format (JSON):
//   { "params":   [ {"name":"x","ty":{"Int":{"width":32,"signed":true}}} ],
//     "pre":      {"Gt":[{"Var":["x","Int"]},{"Int":0}]},
//     "ret_name": "ret",
//     "ret_ty":   {"Int":{"width":32,"signed":true}},
//     "post":     {"Gt":[{"Var":["ret","Int"]},{"Var":["x","Int"]}]} }
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::Read;
use std::process::ExitCode;

use serde::Deserialize;
use trust_clean::{ProofTerm, axiom_closure, carrier_context, infer_type, reflect_contract};
use trust_types::{Formula, Ty};

#[derive(Deserialize)]
struct Param {
    name: String,
    ty: Ty,
}

#[derive(Deserialize)]
struct Contract {
    #[serde(default)]
    params: Vec<Param>,
    pre: Formula,
    ret_name: String,
    ret_ty: Ty,
    post: Formula,
}

const USAGE: &str = "\
clean-contract — reflect a function contract into a Clean dependent type

USAGE:
    clean-contract [FILE]

ARGS:
    FILE        JSON contract { params, pre, ret_name, ret_ty, post }. '-'/omitted = stdin.

Builds Π(params) → Π(_:pre) → Σ(ret) post and kernel-checks it as a Type.
Non-integer params / out-of-subset predicates fail closed (exit 1).";

fn pp(t: &ProofTerm) -> String {
    match t {
        ProofTerm::Var(i) => format!("#{i}"),
        ProofTerm::Const(s) => s.clone(),
        ProofTerm::Sort(0) => "Prop".to_string(),
        ProofTerm::Sort(u) => format!("Type{}", u - 1),
        ProofTerm::App(f, a) => format!("{} {}", pp(f), pp_atom(a)),
        ProofTerm::Lambda { binder_name, binder_type, body } => {
            format!("(λ {binder_name}:{}. {})", pp(binder_type), pp(body))
        }
        ProofTerm::Pi { binder_name, domain, codomain } => {
            format!("(Π {binder_name}:{}. {})", pp(domain), pp(codomain))
        }
        _ => format!("{t:?}"),
    }
}

fn pp_atom(t: &ProofTerm) -> String {
    match t {
        ProofTerm::App(..) | ProofTerm::Lambda { .. } | ProofTerm::Pi { .. } => {
            format!("({})", pp(t))
        }
        _ => pp(t),
    }
}

fn run() -> Result<bool, String> {
    let path = std::env::args().nth(1);
    if matches!(path.as_deref(), Some("-h") | Some("--help")) {
        println!("{USAGE}");
        return Ok(true);
    }
    let input = match path.as_deref() {
        None | Some("-") => {
            let mut s = String::new();
            std::io::stdin().read_to_string(&mut s).map_err(|e| format!("stdin: {e}"))?;
            s
        }
        Some(p) => std::fs::read_to_string(p).map_err(|e| format!("reading {p}: {e}"))?,
    };

    let contract: Contract =
        serde_json::from_str(&input).map_err(|e| format!("parsing contract JSON: {e}"))?;
    let params: Vec<(&str, &Ty)> =
        contract.params.iter().map(|p| (p.name.as_str(), &p.ty)).collect();

    match reflect_contract(&params, &contract.pre, &contract.ret_name, &contract.ret_ty, &contract.post)
    {
        Ok(term) => {
            println!("contract type: {}", pp(&term));
            let ctx = carrier_context();
            match infer_type(&term, &ctx, &[]) {
                Ok(ProofTerm::Sort(1)) => println!("kernel-check:  well-formed Type \u{2713}"),
                Ok(other) => {
                    println!("kernel-check:  unexpected kind {} \u{2717}", pp(&other));
                    return Ok(false);
                }
                Err(e) => {
                    println!("kernel-check:  REJECTED \u{2717} ({e})");
                    return Ok(false);
                }
            }
            let closure = axiom_closure(&term, &ctx);
            if !closure.unresolved.is_empty() {
                let dangling: Vec<&String> = closure.unresolved.iter().collect();
                println!("UNRESOLVED:    {dangling:?} \u{2717}");
                return Ok(false);
            }
            println!("the spec IS the type: a function of this type proves the contract.");
            Ok(true)
        }
        Err(e) => {
            eprintln!("FAIL-CLOSED:   {e}");
            Ok(false)
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(msg) => {
            eprintln!("clean-contract: {msg}");
            ExitCode::from(2)
        }
    }
}
