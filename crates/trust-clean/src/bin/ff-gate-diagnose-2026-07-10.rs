// ff-gate-diagnose-2026-07-10: per-function FULLY_FAITHFUL gate diagnosis for
// the M6 rung-6 mission (reports/m6-rung6-*.md — "the FF push"). Reports, for
// EVERY function in a dump directory, WHICH conjunct of the fully-faithful
// gate is missing: SHAPE_GAP ("no recognizer on either lane accepted the
// body's control-flow/return shape at all") vs SAFETY_GAP ("a shape WAS
// recognized, but the safety-VC / kernel-adequacy conjunct is what's open").
//
// SCRATCH TOOL — census-only, additive (new file, does not touch prove.rs /
// mirsem.rs / any pipeline source). Uses ONLY the public API:
// `trust_clean::{diagnose_fully_faithful_gate, FullyFaithfulDiagnosis}` (the
// exact same gate `prove_one_function` itself evaluates — see that
// function's doc comment and the `diagnosis_fully_faithful_matches_production_gate`
// pin in `prove.rs`'s test module) plus the SAME callees-first ordering
// `prove_dump_dir_with_budget` uses internally (`trust_vcgen::build_call_graph`
// + `compute_verification_order`), so a callee's certified `CalleeFact` is
// already registered when its callers are diagnosed — composition-aware,
// exactly like production.
//
// Usage: ff-gate-diagnose-2026-07-10 <dump_dir> [<dump_dir2> ...]
// Output: one TSV line per function to stdout:
//   def_path\tcluster_tag\tvia_ir_shape\tvia_ir_safety\tvia_mirsem_shape\t
//   via_mirsem_sl_safety_discharged\tvia_mirsem_call_requires\tvia_mirsem_loop_full\t
//   fully_faithful\titer_loop_projection
// plus a cluster summary to stderr at the end.
//
// Trust: W2 INCREMENT-2 — the ADDITIVE `iter_loop_projection` column (`recognized` |
// `declined`) reports the CLASS-NEUTRAL iterator-for-loop partial lane
// (`prove::iter_loop_projection_recognized`), computed against the SAME callees-first
// `certified` registry. It does NOT feed `cluster_tag` (sum_loop/count_pos STAY
// SHAPE_GAP); recognition is surfaced ONLY here + the `iter_loop_decline_reason`
// tier-claim breakdown printed to stderr.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::BTreeMap;
use std::path::Path;

use trust_clean::{FullyFaithfulDiagnosis, diagnose_fully_faithful_gate_with_bodies};
use trust_types::VerifiableFunction;

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

fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: ff-gate-diagnose-2026-07-10 <dump_dir> [<dump_dir2> ...]");
        std::process::exit(2);
    }

    let mut funcs: Vec<VerifiableFunction> = Vec::new();
    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for dir in &args[1..] {
        for f in read_all_functions(Path::new(dir))? {
            if seen.insert(f.def_path.clone()) {
                funcs.push(f);
            }
        }
    }

    // Callees-first order — mirrors `prove_dump_dir_with_budget` exactly (see
    // that function's own comment for why this ordering is sound / non-cyclic
    // for certification purposes).
    let order = trust_vcgen::compute_verification_order(&trust_vcgen::build_call_graph(&funcs));
    let mut by_path: BTreeMap<&str, std::collections::VecDeque<usize>> = BTreeMap::new();
    for (i, f) in funcs.iter().enumerate() {
        by_path.entry(f.def_path.as_str()).or_default().push_back(i);
    }
    let mut seq: Vec<usize> = Vec::with_capacity(funcs.len());
    for def_path in &order {
        if let Some(idxs) = by_path.get_mut(def_path.as_str()) {
            if let Some(i) = idxs.pop_front() {
                seq.push(i);
            }
        }
    }
    for i in 0..funcs.len() {
        if !seq.contains(&i) {
            seq.push(i);
        }
    }

    println!(
        "def_path\tcluster_tag\tvia_ir_shape\tvia_ir_safety\tvia_mirsem_shape\tvia_mirsem_sl_safety_discharged\tvia_mirsem_call_requires\tvia_mirsem_loop_full\tfully_faithful\titer_loop_projection\tstruct_return\titer_premise_witnessed"
    );

    let mut certified: BTreeMap<String, trust_clean::mirsem::CalleeFact> = BTreeMap::new();
    let mut cluster_counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut diagnoses: Vec<(String, FullyFaithfulDiagnosis)> = Vec::new();
    // Trust: W2 INC2 — the additive, CLASS-NEUTRAL iterator-for-loop recognition column +
    // its tier-claim breakdown (stderr). Never feeds `cluster_tag`.
    let mut iter_loop_recognized: Vec<(String, String)> = Vec::new();

    // Trust: structural-fold rung B — the SIBLING DUMP BODIES map, mirroring
    // `prove_dump_dir_with_budget` (the fold lane's stack_safe trampoline /
    // wrapper fingerprints resolve closure bodies through it).
    let bodies: trust_clean::trustir_fold::DumpBodies = {
        let mut m = trust_clean::trustir_fold::DumpBodies::new();
        for f in &funcs {
            m.entry(f.def_path.clone()).or_insert_with(|| f.clone());
        }
        m
    };

    for i in seq {
        let func = &funcs[i];
        let diag = diagnose_fully_faithful_gate_with_bodies(func, &certified, &bodies);
        if diag.fully_faithful {
            certified
                .insert(func.def_path.clone(), trust_clean::mirsem::CalleeFact::of_certified(func));
        }
        *cluster_counts.entry(diag.cluster_tag()).or_default() += 1;
        // Trust: W2 INC2 — CLASS-NEUTRAL iterator-for-loop lane, against the same
        // callees-first `certified` registry (composition-aware, exactly like production).
        let iter_recognized =
            trust_clean::prove::iter_loop_projection_recognized(func, &certified);
        if iter_recognized {
            iter_loop_recognized.push((
                func.def_path.clone(),
                trust_clean::prove::iter_loop_decline_reason(func, &certified),
            ));
        }
        // Trust: RECORD-WITNESS increment 1 (2026-07-22) — the ADDITIVE, CLASS-NEUTRAL
        // single-variant struct-constructor lane. It does NOT feed `cluster_tag`
        // (a struct-return that certifies here flips `fully_faithful` via its own
        // funnel disjunct; this column just surfaces the record lane's recognition).
        let struct_return_recognized = trust_clean::prove::struct_return_recognized(func);
        // Trust: P-ITER-COUNT WITNESS (2026-07-22) — the ADDITIVE, CLASS-NEUTRAL per-link
        // witness column. `witnessed` iff D1–D4/D6 + G8 all pass over the sibling dumps; it
        // does NOT feed `cluster_tag` (sum_loop/count_pos STAY SHAPE_GAP) and asserts NO
        // discharge of P-ITER-COUNT.
        let iter_premise_witnessed =
            trust_clean::prove::iter_count_premise_witnessed(func, &certified, &bodies);
        println!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            func.def_path,
            diag.cluster_tag(),
            diag.via_ir_shape,
            diag.via_ir_safety,
            diag.via_mirsem_shape,
            diag.via_mirsem_straight_line_safety_discharged,
            diag.via_mirsem_call_requires,
            diag.via_mirsem_loop_full,
            diag.fully_faithful,
            if iter_recognized { "recognized" } else { "declined" },
            if struct_return_recognized { "recognized" } else { "declined" },
            if iter_premise_witnessed { "witnessed" } else { "not-witnessed" },
        );
        diagnoses.push((func.def_path.clone(), diag));
    }

    eprintln!("\n=== FF-gate cluster summary ({} functions) ===", diagnoses.len());
    for (tag, count) in &cluster_counts {
        eprintln!("  {tag:<16} {count}");
    }
    eprintln!("\n=== SHAPE_GAP functions (recognizer declines on both lanes) ===");
    for (def_path, diag) in &diagnoses {
        if diag.cluster_tag() == "SHAPE_GAP" {
            eprintln!("  {def_path}  {diag:?}");
        }
    }
    eprintln!("\n=== SAFETY_GAP functions (shape recognized, safety/discharge open) ===");
    for (def_path, diag) in &diagnoses {
        if diag.cluster_tag() == "SAFETY_GAP" {
            eprintln!("  {def_path}  {diag:?}");
        }
    }
    // Trust: W2 INC2 — CLASS-NEUTRAL iterator-for-loop lane recognitions + tier claims.
    // These functions KEEP their cluster_tag (SHAPE_GAP); this is an ADDITIVE surface.
    eprintln!(
        "\n=== iter_loop_projection: recognized ({} functions, CLASS-NEUTRAL — cluster_tag \
         UNCHANGED) ===",
        iter_loop_recognized.len()
    );
    for (def_path, claim) in &iter_loop_recognized {
        eprintln!("  {def_path}\n    {claim}");
    }
    Ok(())
}
