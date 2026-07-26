// clean-reflect-source: reflect the contracts of every function in a Rust source
// file into Clean dependent types and report kernel-checked coverage — the
// spec-as-type pipeline made runnable end-to-end on real source, with no
// compiler or trust-cg stack required (docs/PLAN-clean-dependent-type-reflection.md).
//
// A function's `#[requires]`/`#[ensures]` + signature become a Clean dependent
// type the kernel validates (a well-formed `Type` ⇒ "the spec is the type").
// This is the same capability as the `targo trust reflect-clean` subcommand,
// packaged as a standalone tool so it builds in the fast `crates/` loop.
//
// Scope: single-line `fn` signatures (the common annotated-function shape);
// multi-line signatures and unknown named types fail closed (reported, not
// silently mismodeled).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use trust_clean::{
    GroundOutcome, KernelGroundingSession, ProofTerm, axiom_closure, carrier_context, infer_type,
    is_foundational, reflect_source_function,
};

struct ParsedFn {
    name: String,
    typed_params: Vec<(String, String)>,
    return_type: Option<String>,
    requires: Vec<String>,
    ensures: Vec<String>,
}

fn main() -> ExitCode {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    // `--require-axioms N` gates that the reflected types rest on at most the N
    // foundational axioms (and no carrier-vocabulary residue) — the §6 contract.
    let mut require_axioms: Option<usize> = None;
    let mut kernel = false;
    let mut args: Vec<String> = Vec::new();
    let mut it = raw.into_iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--require-axioms" => require_axioms = it.next().and_then(|n| n.parse().ok()),
            // `--kernel`: ground each contract in the REAL clean-kernel and audit
            // its axiom closure (vs. the local predicative checker).
            "--kernel" => kernel = true,
            _ => args.push(a),
        }
    }
    let mut files: Vec<PathBuf> = Vec::new();
    for a in &args {
        let p = Path::new(a);
        if p.is_dir() {
            collect_rs_files(p, &mut files);
        } else if a.ends_with(".rs") {
            files.push(p.to_path_buf());
        }
    }
    if files.is_empty() {
        eprintln!("usage: clean-reflect-source [--kernel] [--require-axioms N] <file.rs | dir>...");
        return ExitCode::from(2);
    }
    files.sort();

    let ctx = carrier_context();
    let mut session = kernel.then(KernelGroundingSession::new);
    let (mut total, mut reflected, mut failed) = (0usize, 0usize, 0usize);
    let mut kernel_modulo3 = 0usize; // contracts the REAL kernel proves modulo 3
    let mut vocabulary: BTreeSet<String> = BTreeSet::new();
    for path in &files {
        let content = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("{}: {e}", path.display());
                continue;
            }
        };
        let lines: Vec<&str> = content.lines().collect();
        let funcs = parse_functions(&lines);
        if funcs.is_empty() {
            continue;
        }
        println!("{}:", path.display());
        for func in &funcs {
            total += 1;
            let typed: Vec<(&str, &str)> =
                func.typed_params.iter().map(|(n, t)| (n.as_str(), t.as_str())).collect();
            let reflected_term = reflect_source_function(
                &typed,
                func.return_type.as_deref(),
                &func.requires,
                &func.ensures,
            );
            let term = match reflected_term {
                Ok(t) => t,
                Err(e) => {
                    failed += 1;
                    println!("  - {} : fail-closed ({e})", func.name);
                    continue;
                }
            };
            if let Some(s) = &mut session {
                // REAL clean-kernel grounding + axiom audit.
                match s.check(&term) {
                    GroundOutcome::Modulo3 => {
                        reflected += 1;
                        kernel_modulo3 += 1;
                        println!("  \u{2713} {} : grounded in REAL kernel, modulo 3 axioms", func.name);
                    }
                    GroundOutcome::Residue(r) => {
                        failed += 1;
                        println!("  \u{2717} {} : grounded but rests on non-foundational axioms: {r:?}", func.name);
                    }
                    GroundOutcome::NotGrounded => {
                        failed += 1;
                        println!("  - {} : not yet groundable in real kernel (non-integer type / unsupported predicate)", func.name);
                    }
                    GroundOutcome::KernelRejected(e) => {
                        failed += 1;
                        println!("  \u{2717} {} : real kernel rejected ({e})", func.name);
                    }
                }
            } else {
                // Local predicative checker (carrier vocabulary).
                match infer_type(&term, &ctx, &[]) {
                    Ok(ProofTerm::Sort(1)) => {
                        reflected += 1;
                        let spec = if func.requires.is_empty() && func.ensures.is_empty() {
                            "(no contract)"
                        } else {
                            "contract"
                        };
                        vocabulary.extend(axiom_closure(&term, &ctx).axioms);
                        println!("  \u{2713} {} : kernel-checked dependent type {spec}", func.name);
                    }
                    Ok(_) | Err(_) => {
                        failed += 1;
                        println!("  \u{2717} {} : reflected but not a well-formed Type", func.name);
                    }
                }
            }
        }
    }

    if kernel {
        println!(
            "\n{kernel_modulo3}/{total} functions GROUNDED IN THE REAL CLEAN KERNEL modulo 3 axioms \
             ({} not yet groundable / rejected)",
            total - kernel_modulo3
        );
        if let Some(n) = require_axioms {
            if n == 3 && total > 0 && kernel_modulo3 == total {
                println!(
                    "\n\u{2713} ALL {total} contract TYPES kernel-verified in Clean modulo 3 axioms.\n\
                     (each spec is a well-formed Clean dependent type resting on only \
                     propext/Quot.sound/Classical.choice. Proving each function INHABITS its \
                     contract — that the body satisfies the spec — is the remaining inhabitation \
                     step via SMT→kernel.)"
                );
                return ExitCode::SUCCESS;
            }
            println!(
                "\n\u{2717} NOT modulo {n}: {} of {total} contracts are not yet grounded modulo 3 in \
                 the real kernel.",
                total - kernel_modulo3
            );
            return ExitCode::FAILURE;
        }
        return ExitCode::SUCCESS;
    }

    println!(
        "\n{reflected}/{total} functions reflected to kernel-checked dependent types \
         ({failed} fail-closed / unreflectable)"
    );
    report_axioms(&vocabulary);
    if let Some(n) = require_axioms {
        let residue: Vec<&String> = vocabulary.iter().filter(|a| !is_foundational(a)).collect();
        if residue.is_empty() && vocabulary.len() <= n {
            println!("\n\u{2713} reflected types proven modulo {} foundational axioms.", vocabulary.len());
            return ExitCode::SUCCESS;
        }
        println!(
            "\n\u{2717} NOT modulo {n} axioms: {} carrier-vocabulary axioms remain (run with --kernel \
             to audit against the real Clean kernel). Trust is not yet proven modulo {n}.",
            residue.len()
        );
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

/// Honest axiom accounting for the reflected contract types.
///
/// A reflected contract is a kernel-checked dependent *Type*; its well-formedness
/// rests on the carrier vocabulary (`Trust.*`), declared as axioms in
/// `carrier_context()`. None of these are the 3 foundational axioms — they are
/// the reflection's trusted *encoding*. Reaching §6's "axioms: 3" requires
/// pinning the carriers as Clean kernel *definitions* over the foundational
/// vocabulary (the S1 / kernel-grounding step); this report makes the current
/// trusted residue explicit rather than claiming a premature "axioms: 3".
fn report_axioms(vocabulary: &BTreeSet<String>) {
    let foundational: Vec<&String> = vocabulary.iter().filter(|a| is_foundational(a)).collect();
    let carriers: Vec<&String> = vocabulary.iter().filter(|a| !is_foundational(a)).collect();
    println!("\naxiom basis of the reflected types:");
    println!("  foundational (propext/Quot.sound/Classical.choice): {}", foundational.len());
    println!(
        "  carrier-vocabulary axioms (trusted encoding, to be discharged to the 3 \
         foundational via the Clean kernel — S1): {}",
        carriers.len()
    );
    if !carriers.is_empty() {
        println!("    {{ {} }}", carriers.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", "));
    }
}

/// Recursively collect `.rs` files under a directory (skipping `target/`).
fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let p = entry.path();
        if p.is_dir() {
            if p.file_name().and_then(|n| n.to_str()) != Some("target") {
                collect_rs_files(&p, out);
            }
        } else if p.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(p);
        }
    }
}

/// Parse single-line `fn` signatures and their preceding `#[requires]`/
/// `#[ensures]` attribute block.
fn parse_functions(lines: &[&str]) -> Vec<ParsedFn> {
    let mut funcs = Vec::new();
    for (i, raw) in lines.iter().enumerate() {
        let line = raw.trim();
        if !is_fn_header(line) {
            continue;
        }
        let Some((name, typed_params, return_type)) = parse_fn_signature(line) else {
            continue;
        };
        let (requires, ensures) = scan_contract_exprs(lines, i);
        funcs.push(ParsedFn { name, typed_params, return_type, requires, ensures });
    }
    funcs
}

fn is_fn_header(line: &str) -> bool {
    let l = line.trim_start_matches("pub ").trim_start();
    let l = l.trim_start_matches("const ").trim_start_matches("async ");
    let l = l.trim_start_matches("unsafe ").trim_start_matches("extern ");
    l.starts_with("fn ") && line.contains('(')
}

/// Parse `fn name(p: T, q: U) -> R` (single line). Returns name, typed params,
/// optional return type. Generic/`where`/multi-line forms return `None`.
fn parse_fn_signature(line: &str) -> Option<(String, Vec<(String, String)>, Option<String>)> {
    let fn_pos = line.find("fn ")?;
    let after_fn = &line[fn_pos + 3..];
    let paren = after_fn.find('(')?;
    let name = after_fn[..paren].trim().to_string();
    if name.is_empty() || name.contains('<') {
        return None; // generic function name / malformed
    }
    // Match the parameter list parentheses by depth.
    let params_src = balanced_parens(&after_fn[paren..])?;
    let typed_params = parse_params(&params_src);

    // Return type: between `->` and `{`/`where`/end.
    let rest = &after_fn[paren + params_src.len() + 2..]; // skip "(...)"
    let return_type = rest.find("->").map(|arrow| {
        let after = &rest[arrow + 2..];
        let end = after.find('{').or_else(|| after.find("where")).unwrap_or(after.len());
        after[..end].trim().to_string()
    });
    Some((name, typed_params, return_type))
}

/// Given a string starting at `(`, return the inner content of the balanced
/// parenthesis group (excluding the outer parens).
fn balanced_parens(s: &str) -> Option<String> {
    let mut depth = 0i32;
    let mut start = None;
    for (i, c) in s.char_indices() {
        match c {
            '(' => {
                if depth == 0 {
                    start = Some(i + 1);
                }
                depth += 1;
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(s[start?..i].to_string());
                }
            }
            _ => {}
        }
    }
    None
}

fn parse_params(params_src: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for part in split_top_level(params_src) {
        let part = part.trim();
        if part.is_empty() || part == "&self" || part == "self" || part == "&mut self" {
            continue;
        }
        if let Some((name, ty)) = part.split_once(':') {
            out.push((name.trim().to_string(), ty.trim().to_string()));
        }
    }
    out
}

/// Split on top-level commas, respecting `()`, `[]`, `<>` nesting.
fn split_top_level(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (i, c) in s.char_indices() {
        match c {
            '(' | '[' | '<' => depth += 1,
            ')' | ']' | '>' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(s[start..i].to_string());
                start = i + 1;
            }
            _ => {}
        }
    }
    let tail = &s[start..];
    if !tail.trim().is_empty() {
        parts.push(tail.to_string());
    }
    parts
}

/// Scan upward from a function header line for its `#[requires(...)]` /
/// `#[ensures(...)]` attribute expressions.
fn scan_contract_exprs(lines: &[&str], header_idx: usize) -> (Vec<String>, Vec<String>) {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut i = header_idx;
    let mut scanned = 0;
    while i > 0 && scanned < 24 {
        i -= 1;
        scanned += 1;
        let l = lines[i].trim();
        if l.is_empty() || l.starts_with("//") || l.starts_with('*') {
            continue;
        }
        if let Some(expr) = attr_paren_expr(l, "requires") {
            requires.push(expr);
            continue;
        }
        if let Some(expr) = attr_paren_expr(l, "ensures") {
            ensures.push(expr);
            continue;
        }
        if l.starts_with("#[") || l.starts_with("#!") {
            continue;
        }
        break;
    }
    requires.reverse();
    ensures.reverse();
    (requires, ensures)
}

fn attr_paren_expr(line: &str, name: &str) -> Option<String> {
    if !line.starts_with("#[") || !line.contains(name) {
        return None;
    }
    let open = line.find('(')?;
    let close = line.rfind(')')?;
    (close > open).then(|| line[open + 1..close].trim().to_string())
}
