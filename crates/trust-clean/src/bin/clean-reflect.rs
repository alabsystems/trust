// clean-reflect: the `clean reflect` CLI — reflect a Trust type into its Clean
// dependent-type carrier term (docs/PLAN-clean-dependent-type-reflection.md, S0).
//
// Reads a JSON Trust `Ty` (default) or `Sort` (--sort) and prints the reflected
// Clean `ProofTerm`. Non-scalar types FAIL CLOSED with the offending family and
// a non-zero exit — never a silent collapse. With `--check` it also type-checks
// the reflected term against `carrier_context()` (proving the carrier is
// kernel-resolvable) and reports its axiom closure.
//
// Input format (JSON), serde external tagging:
//   Ty:   {"Int":{"width":32,"signed":true}}   {"Bool":null}->use "Bool"   {"Adt":{"name":"S","fields":[]}}
//   Sort: {"BitVec":32}   "Bool"   "Int"
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::io::Read;
use std::process::ExitCode;

use trust_clean::{
    ProofTerm, axiom_closure, carrier_context, infer_type, reflect_formula, reflect_sort,
    reflect_ty,
};
use trust_types::{Formula, Sort, Ty};

const USAGE: &str = "\
clean-reflect — reflect a Trust type into its Clean dependent-type carrier

USAGE:
    clean-reflect [OPTIONS] [FILE]

ARGS:
    FILE        JSON Trust `Ty` (or `Sort` with --sort). '-' or omitted = stdin.

OPTIONS:
    --sort      Interpret the input as a `Sort` (4-variant SMT sort) not a `Ty`.
    --formula   Interpret the input as a `Formula` predicate; reflect it into a
                Clean `Prop` term (spec-as-type proposition half, M3).
    --check     Also type-check the reflected term against the carrier context
                and print the inferred type + axiom closure.
    -h, --help  Print this help.

Non-scalar types / out-of-subset predicates fail closed (exit 1) with the
offending family — never a silent collapse.";

struct Args {
    path: Option<String>,
    as_sort: bool,
    as_formula: bool,
    check: bool,
}

fn parse_args() -> Result<Args, String> {
    let mut path = None;
    let (mut as_sort, mut as_formula, mut check) = (false, false, false);
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "-h" | "--help" => {
                println!("{USAGE}");
                std::process::exit(0);
            }
            "--sort" => as_sort = true,
            "--formula" => as_formula = true,
            "--check" => check = true,
            other if other.starts_with("--") => return Err(format!("unknown flag: {other}")),
            other if path.is_none() => path = Some(other.to_string()),
            other => return Err(format!("unexpected extra argument: {other}")),
        }
    }
    Ok(Args { path, as_sort, as_formula, check })
}

/// Collect free variables of a predicate as (name -> is_bool_sorted), so
/// `--check` can declare them in the context (bool vars `: Prop`, others `: Int`).
fn collect_formula_vars(f: &Formula, out: &mut BTreeMap<String, bool>) {
    if let Formula::Var(name, sort) = f {
        out.insert(name.clone(), matches!(sort, Sort::Bool));
    }
    for child in f.children() {
        collect_formula_vars(child, out);
    }
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

/// Pretty-print a `ProofTerm` in compact CIC notation (sufficient for the
/// scalar carrier fragment: `Const`, `App`, `Pi`, `Sort`).
fn pp(t: &ProofTerm) -> String {
    match t {
        ProofTerm::Var(i) => format!("#{i}"),
        ProofTerm::Const(s) => s.clone(),
        ProofTerm::Sort(0) => "Prop".to_string(),
        ProofTerm::Sort(u) => format!("Sort {u}"),
        ProofTerm::App(f, a) => format!("{} {}", pp(f), pp_atom(a)),
        ProofTerm::Lambda { binder_name, binder_type, body } => {
            format!("fun ({binder_name} : {}) => {}", pp(binder_type), pp(body))
        }
        ProofTerm::Pi { binder_name, domain, codomain } => {
            format!("({binder_name} : {}) -> {}", pp(domain), pp(codomain))
        }
        _ => format!("{t:?}"),
    }
}

/// Parenthesize compound terms when used as an application argument.
fn pp_atom(t: &ProofTerm) -> String {
    match t {
        ProofTerm::App(..) | ProofTerm::Lambda { .. } | ProofTerm::Pi { .. } => {
            format!("({})", pp(t))
        }
        _ => pp(t),
    }
}

fn run() -> Result<bool, String> {
    let args = parse_args()?;
    let input = read_input(&args.path)?;

    // Each branch yields the reflected term and the context to check against
    // (a predicate gets a context extended with its free variables).
    let (reflected, ctx) = if args.as_formula {
        let f: Formula =
            serde_json::from_str(&input).map_err(|e| format!("parsing Formula JSON: {e}"))?;
        println!("input (Formula): {f:?}");
        let mut ctx = carrier_context();
        let mut vars = BTreeMap::new();
        collect_formula_vars(&f, &mut vars);
        for (name, is_bool) in &vars {
            // bool var : Prop (Sort 0); integer var : Trust.Int.
            let ty =
                if *is_bool { ProofTerm::Sort(0) } else { ProofTerm::Const("Trust.Int".into()) };
            let _ = ctx.add_axiom(name, ty);
        }
        (reflect_formula(&f), ctx)
    } else if args.as_sort {
        let sort: Sort =
            serde_json::from_str(&input).map_err(|e| format!("parsing Sort JSON: {e}"))?;
        println!("input (Sort): {sort:?}");
        (reflect_sort(&sort), carrier_context())
    } else {
        let ty: Ty = serde_json::from_str(&input).map_err(|e| format!("parsing Ty JSON: {e}"))?;
        println!("input (Ty):   {ty:?}");
        (reflect_ty(&ty), carrier_context())
    };

    match reflected {
        Ok(term) => {
            println!("reflected:    {}", pp(&term));
            println!("proof-term:   {term:?}");
            if args.check {
                match infer_type(&term, &ctx, &[]) {
                    Ok(inferred) => println!("kernel-type:  {} \u{2713}", pp(&inferred)),
                    Err(e) => {
                        println!("kernel-type:  REJECTED \u{2717} ({e})");
                        return Ok(false);
                    }
                }
                let closure = axiom_closure(&term, &ctx);
                let carriers: Vec<&String> = closure.axioms.iter().collect();
                println!(
                    "carriers:     {}",
                    carriers.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")
                );
                if !closure.unresolved.is_empty() {
                    let dangling: Vec<&String> = closure.unresolved.iter().collect();
                    println!("UNRESOLVED:   {dangling:?} \u{2717}");
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Err(e) => {
            // Fail closed: name the family, exit non-zero.
            eprintln!("FAIL-CLOSED:  {e}");
            Ok(false)
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(msg) => {
            eprintln!("clean-reflect: {msg}");
            ExitCode::from(2)
        }
    }
}
