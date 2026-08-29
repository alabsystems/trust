// r4-fallback-diagnose-2026-08-13: WHY does a row take the MirSem fallback?
//
// WHY THIS EXISTS. `corpus-census-2026-07-24` reports the R4 split
// (`fully_faithful == via_trustir + mirsem_fallback`) and the teardown's exit
// criterion is `mirsem_fallback == 0`. The 2026-08-13 baseline put that at 46
// rows over 19 directories, but a COUNT is not a work list: it says nothing about
// which trust-ir conjunct declined, so nobody can tell whether 46 rows are 46
// problems or one problem 46 times.
//
// This prints, per fallback row, the two trust-ir pillars separately —
// `via_ir_shape` (did ANY trust-ir recognizer accept the body at all?) and
// `via_ir_safety` (are its safety VCs kernel-adequate?). That is the split that
// decides the work: a shape gap is a missing recognizer, a safety gap is a
// discharge gap, and they are fixed in different places.
//
// SCRATCH/MEASUREMENT TOOL — additive, read-only with respect to the corpus, and
// built only from the public `trust_clean` API (`prove_dump_dir_with_budget`'s
// own inputs plus `diagnose_fully_faithful_gate`, which the crate documents as
// mirroring `prove_one_function`'s gate EXACTLY and pins with
// `diagnosis_fully_faithful_matches_production_gate`).
//
// HONEST SCOPE. Same corpus caveat as the census: this is the COMMITTED FIXTURE
// CORPUS, a curated regression corpus, NOT a sample of Rust. Counts here are
// about the teardown work list, nothing more. The diagnosis is run
// COMPOSITION-BLIND (empty callee registry) — see the note at the call site —
// so a row whose trust-ir lane needs a certified callee can appear as a shape
// gap here; that is called out in the output rather than hidden.
//
// Usage:
//   r4-fallback-diagnose-2026-08-13 <dump-dir> [dump-dir ...]

use std::collections::BTreeMap;
use std::path::Path;

fn main() {
    let dirs: Vec<String> = std::env::args().skip(1).collect();
    if dirs.is_empty() {
        eprintln!("usage: r4-fallback-diagnose-2026-08-13 <dump-dir> [dump-dir ...]");
        std::process::exit(2);
    }

    let mut shape_gaps = 0_usize;
    let mut safety_gaps = 0_usize;
    let mut faithful_via_ir = 0_usize;
    let mut rows = 0_usize;

    println!("lane\tvia_ir_shape\tvia_ir_safety\tdir\tfunction");
    for dir in &dirs {
        let path = Path::new(dir);
        let Ok(entries) = std::fs::read_dir(path) else {
            eprintln!("skip (unreadable): {dir}");
            continue;
        };
        for entry in entries.flatten() {
            let p = entry.path();
            if p.extension().and_then(|e| e.to_str()) != Some("json") {
                continue;
            }
            let Ok(text) = std::fs::read_to_string(&p) else { continue };
            let Ok(func) = serde_json::from_str::<trust_types::VerifiableFunction>(&text) else {
                continue;
            };
            // Composition-blind: an empty registry. A row that needs a certified
            // callee therefore reads as a shape gap here. Stated, not hidden.
            let callees: BTreeMap<String, trust_clean::mirsem::CalleeFact> = BTreeMap::new();
            let d = trust_clean::prove::diagnose_fully_faithful_gate(&func, &callees);
            if !d.fully_faithful {
                continue;
            }
            rows += 1;
            if d.via_ir {
                faithful_via_ir += 1;
                continue;
            }
            // A fallback row: trust-ir declined but MirSem accepted.
            let tag = if !d.via_ir_shape { "SHAPE_GAP" } else { "SAFETY_GAP" };
            if d.via_ir_shape {
                safety_gaps += 1;
            } else {
                shape_gaps += 1;
            }
            println!("{tag}\t{}\t{}\t{}\t{}", d.via_ir_shape, d.via_ir_safety, dir, func.name);
        }
    }

    eprintln!();
    eprintln!("=== R4 FALLBACK DIAGNOSIS (composition-blind) ===");
    eprintln!("fully_faithful rows seen   {rows}");
    eprintln!("  via_trustir              {faithful_via_ir}");
    eprintln!(
        "  fallback: SHAPE_GAP      {shape_gaps}   (no trust-ir recognizer accepted the body)"
    );
    eprintln!(
        "  fallback: SAFETY_GAP     {safety_gaps}   (recognizer accepted; safety pillar declined)"
    );
}
