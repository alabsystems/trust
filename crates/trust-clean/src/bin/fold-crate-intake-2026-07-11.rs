// fold-crate-intake-2026-07-11: per-function structural-fold-lane triage for
// the published-crate intake mission (the recursive-ADT crate ladder rung —
// "point the fold lane at a crate it has never seen"). For EVERY function in
// a dump directory, reports the fold recognizer's verdict BY NAME: either
// `fold_shape_ok` (the lane's recognizer accepted the body — the certificate
// then still has to clear registration + safety + kernel re-check in the
// production gate) or the exact `FoldDecline` kill-table name + detail. This
// is the rung-G work-queue generator: the named declines over a REAL
// published crate are the lane's measured gap list.
//
// SCRATCH TOOL — census-only, additive (new file, does not touch prove.rs /
// trustir_fold.rs / any pipeline source). Uses ONLY the public API:
// `trust_clean::trustir_fold::{sem_structural_fold_shape_of_with_bodies,
// DumpBodies, FoldDecline}` — the exact recognizer entry point the
// production `prove_one_function` fold lane drives, with the SAME sibling
// bodies map `prove_dump_dir_with_budget` threads (so P-STACK closure
// resolution behaves identically).
//
// Usage: fold-crate-intake-2026-07-11 <dump_dir> [--all]
//   default: prints only SELF-RECURSIVE functions (direct self-call in some
//            block) — the fold lane's candidate population — plus a summary
//            of everything else by decline name to stderr.
//   --all:   prints every function.
// Output: one TSV line per function to stdout:
//   def_path\tself_recursive\tfold_verdict\tdetail
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::BTreeMap;
use std::path::Path;

use trust_clean::trustir_fold::{DumpBodies, sem_structural_fold_shape_of_with_bodies};
use trust_types::{Terminator, VerifiableFunction};

fn read_all_functions(dir: &Path) -> std::io::Result<Vec<VerifiableFunction>> {
    let mut out = Vec::new();
    let mut entries: Vec<_> =
        std::fs::read_dir(dir)?.filter_map(Result::ok).map(|e| e.path()).collect();
    entries.sort();
    for path in entries {
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let bytes = std::fs::read(&path)?;
        if let Ok(func) =
            trust_clean::prove::decode_verifiable_function_with_authenticated_legacy_metadata(
                &bytes,
            )
        {
            out.push(func);
        }
    }
    Ok(out)
}

fn is_direct_self_recursive(f: &VerifiableFunction) -> bool {
    f.body.blocks.iter().any(
        |b| matches!(&b.terminator, Terminator::Call { func: callee, .. } if *callee == f.def_path),
    )
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: fold-crate-intake-2026-07-11 <dump_dir> [--all]");
        std::process::exit(2);
    }
    let all = args.iter().any(|a| a == "--all");

    let funcs = read_all_functions(Path::new(&args[1]))?;
    let bodies: DumpBodies = {
        let mut m = DumpBodies::new();
        for f in &funcs {
            m.entry(f.def_path.clone()).or_insert_with(|| f.clone());
        }
        m
    };

    println!("def_path\tself_recursive\tfold_verdict\tdetail");
    let mut decline_counts: BTreeMap<String, usize> = BTreeMap::new();
    let mut rec_total = 0usize;
    let mut ok_total = 0usize;
    for f in &funcs {
        let self_rec = is_direct_self_recursive(f);
        if self_rec {
            rec_total += 1;
        }
        let (verdict, detail) = match sem_structural_fold_shape_of_with_bodies(f, &bodies) {
            Ok(shape) => {
                ok_total += 1;
                ("fold_shape_ok".to_string(), format!("sort={:?}", shape.sort))
            }
            Err(d) => (d.name().to_string(), format!("{d:?}")),
        };
        *decline_counts.entry(verdict.clone()).or_default() += 1;
        if all || self_rec {
            // Tabs/newlines never appear in def paths; details are debug-fmt.
            println!("{}\t{}\t{}\t{}", f.def_path, self_rec, verdict, detail.replace('\t', " "));
        }
    }

    eprintln!(
        "== fold-crate-intake summary: {} functions, {} direct-self-recursive, {} fold_shape_ok",
        funcs.len(),
        rec_total,
        ok_total
    );
    for (name, n) in &decline_counts {
        eprintln!("   {name}: {n}");
    }
    Ok(())
}
