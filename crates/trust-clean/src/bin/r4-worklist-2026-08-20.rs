// r4-worklist-2026-08-20: WHERE is the remaining not-fully-faithful population?
//
// WHY THIS EXISTS. `corpus-census-2026-07-24` reports how many functions certify
// and `r4-fallback-diagnose-2026-08-13` explains the MirSem-fallback rows — but
// the fallback population has been 0 since the teardown exit criterion was met,
// so that tool now prints nothing while ~1200 corpus functions still do not
// certify. A count of what certifies is not a work list for what does not.
//
// This prints the NOT-FULLY-FAITHFUL population grouped by the pillar that
// blocks it, using `diagnose_fully_faithful_gate` (which the crate documents as
// mirroring `prove_one_function`'s gate EXACTLY and pins with
// `diagnosis_fully_faithful_matches_production_gate`):
//
//   SHAPE_GAP   — no recognizer on EITHER lane accepted the body (a missing
//                 recognizer: the body's control/data shape is unmodeled).
//   SAFETY_GAP  — some lane recognized the shape; the safety conjunct
//                 (kernel-adequacy or discharge) is what is missing.
//
// and, for SAFETY_GAP rows, which side declined (trust-ir adequacy vs MirSem
// discharge), so a campaign can pick the class with a real population instead of
// a plausible-sounding one. (Measured 2026-08-20: the "signed var*var mul
// record" unit recorded as next-up would have moved ZERO rows — all 7 corpus
// sites are SHAPE_GAP, not SAFETY_GAP. This tool exists so that is a
// measurement, not a surprise.)
//
// HONEST SCOPE, twice over:
//
//  1. This is the COMMITTED FIXTURE CORPUS — a curated regression corpus, NOT a
//     sample of Rust. Counts are about this work list, nothing more.
//  2. COMPOSITION-BLIND: the diagnosis runs with an EMPTY callee registry, so a
//     row whose trust-ir lane needs a certified callee reads as a shape gap
//     here even though the real callees-first census would certify it. The
//     `--registry` flag builds a per-directory registry from that directory's
//     own certified functions first, which recovers most of the composition
//     effect; the totals differ between the two modes and BOTH are printed as
//     what they are.
//
// SCRATCH/MEASUREMENT TOOL — additive, read-only with respect to the corpus, and
// built only from the public `trust_clean` API.
//
// Usage:
//   r4-worklist-2026-08-20 [--registry] [--top N] <dump-dir> [dump-dir ...]

use std::collections::BTreeMap;
use std::path::Path;

use trust_types::VerifiableFunction;

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let use_registry = args.iter().any(|a| a == "--registry");
    args.retain(|a| a != "--registry");
    let mut top = 25usize;
    if let Some(i) = args.iter().position(|a| a == "--top") {
        if let Some(n) = args.get(i + 1).and_then(|s| s.parse().ok()) {
            top = n;
        }
        args.drain(i..=i + 1);
    }
    if args.is_empty() {
        eprintln!("usage: r4-worklist-2026-08-20 [--registry] [--top N] <dump-dir> ...");
        std::process::exit(2);
    }

    let mut total = 0usize;
    let mut ff = 0usize;
    // cluster -> count
    let mut clusters: BTreeMap<&'static str, usize> = BTreeMap::new();
    // finer blocking-pillar tag -> (count, sample def_paths)
    let mut pillars: BTreeMap<String, (usize, Vec<String>)> = BTreeMap::new();
    // expr-fold decline names, which are already stable strings
    let mut expr_declines: BTreeMap<&'static str, usize> = BTreeMap::new();

    for dir in &args {
        let Ok(entries) = std::fs::read_dir(Path::new(dir)) else { continue };
        let mut funcs: Vec<VerifiableFunction> = Vec::new();
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|x| x.to_str()) != Some("json") {
                continue;
            }
            let Ok(bytes) = std::fs::read(&path) else { continue };
            let Ok(func) = serde_json::from_slice::<VerifiableFunction>(&bytes) else { continue };
            funcs.push(func);
        }
        funcs.sort_by(|a, b| a.def_path.cmp(&b.def_path));

        // Optional registry pass: certify what we can first, so composition-bearing
        // rows are diagnosed against a populated registry (an approximation of the
        // census's Tarjan-SCC callees-first order — it is a single fixpoint sweep,
        // which is enough for the shallow chains this corpus carries).
        let mut registry: BTreeMap<String, trust_clean::mirsem::CalleeFact> = BTreeMap::new();
        if use_registry {
            for _ in 0..3 {
                let before = registry.len();
                for f in &funcs {
                    if registry.contains_key(&f.def_path) {
                        continue;
                    }
                    if trust_clean::prove::diagnose_fully_faithful_gate(f, &registry)
                        .fully_faithful
                    {
                        registry.insert(
                            f.def_path.clone(),
                            trust_clean::mirsem::CalleeFact::of_certified(f),
                        );
                    }
                }
                if registry.len() == before {
                    break;
                }
            }
        }

        for func in &funcs {
            total += 1;
            let d = trust_clean::prove::diagnose_fully_faithful_gate(func, &registry);
            if d.fully_faithful {
                ff += 1;
                continue;
            }
            *clusters.entry(d.cluster_tag()).or_insert(0) += 1;
            if let Some(name) = d.expr_fold_decline {
                *expr_declines.entry(name).or_insert(0) += 1;
            }
            // The finer tag: which pillar on which lane is the FIRST missing one.
            let tag = if !d.via_ir_shape && !d.via_mirsem_shape {
                "SHAPE: no recognizer on either lane".to_string()
            } else if d.via_ir_shape && !d.via_ir_safety && !d.via_mirsem_shape {
                "SAFETY(trust-ir): shape ok, safety-VC adequacy declined".to_string()
            } else if d.via_ir_shape && !d.via_ir_safety && d.via_mirsem_shape {
                "SAFETY(both lanes): shapes ok, both safety pillars declined".to_string()
            } else if !d.via_ir_shape && d.via_mirsem_straight_line_shape {
                if !d.via_mirsem_straight_line_safety_discharged {
                    "SHAPE(trust-ir) + DISCHARGE(mirsem): only mirsem sees it, VCs undischarged"
                        .to_string()
                } else if !d.via_mirsem_call_requires {
                    "SHAPE(trust-ir) + REQUIRES(mirsem): only mirsem sees it, requires unestablished"
                        .to_string()
                } else {
                    "SHAPE(trust-ir): only mirsem sees the shape".to_string()
                }
            } else if !d.via_ir_shape && d.via_mirsem_loop_shape && !d.via_mirsem_loop_full {
                "SHAPE(trust-ir) + LOOP-WITNESS(mirsem): loop CFG seen, kernel witness declined"
                    .to_string()
            } else {
                format!(
                    "OTHER: ir_shape={} ir_safety={} mirsem_shape={} mirsem_loop_full={}",
                    d.via_ir_shape, d.via_ir_safety, d.via_mirsem_shape, d.via_mirsem_loop_full
                )
            };
            let slot = pillars.entry(tag).or_insert((0, Vec::new()));
            slot.0 += 1;
            if slot.1.len() < top {
                slot.1.push(func.def_path.clone());
            }
        }
    }

    println!("mode: {}", if use_registry { "REGISTRY (per-dir fixpoint)" } else { "COMPOSITION-BLIND" });
    println!("functions            {total}");
    println!("fully_faithful       {ff}");
    println!("not_fully_faithful   {}", total - ff);
    println!("\n--- CLUSTER ---");
    for (k, v) in &clusters {
        println!("{v:>6}  {k}");
    }
    println!("\n--- BLOCKING PILLAR (first missing) ---");
    let mut rows: Vec<(&String, &(usize, Vec<String>))> = pillars.iter().collect();
    rows.sort_by(|a, b| b.1.0.cmp(&a.1.0));
    for (tag, (n, samples)) in rows {
        println!("{n:>6}  {tag}");
        for s in samples.iter().take(8) {
            println!("           {s}");
        }
    }
    if !expr_declines.is_empty() {
        println!("\n--- EXPR-FOLD SCC DECLINE NAMES ---");
        let mut e: Vec<(&&str, &usize)> = expr_declines.iter().collect();
        e.sort_by(|a, b| b.1.cmp(a.1));
        for (name, n) in e {
            println!("{n:>6}  {name}");
        }
    }
}
