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
    // `--shapes`: histogram the SHAPE_GAP population by a STRUCTURAL SIGNATURE
    // (block count class, terminator kinds, rvalue kinds, return-type class,
    // loopiness) so a campaign can see which MISSING RECOGNIZER would move the
    // most rows, instead of guessing from a handful of sampled def_paths.
    let shapes_mode = args.iter().any(|a| a == "--shapes");
    args.retain(|a| a != "--shapes");
    // `--tractable`: split the SHAPE_GAP population into what a recognizer could
    // PLAUSIBLY reach versus what is outside the modeled fragment entirely. The
    // raw shape-gap count is NOT a work list — measured 2026-08-20, most of it is
    // bodies that are correctly declined (raw pointers, floats, trait objects,
    // unmodeled types), and planning against the raw number overstates the
    // available work by roughly an order of magnitude.
    let tractable_mode = args.iter().any(|a| a == "--tractable");
    args.retain(|a| a != "--tractable");
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
    let mut shapes: BTreeMap<String, (usize, Vec<String>)> = BTreeMap::new();
    let mut tract: BTreeMap<&'static str, (usize, Vec<String>)> = BTreeMap::new();
    // For rows the gate ACTUALLY declines and whose only blocker is a type: which
    // type set. Measured behind the gate on purpose — a scan that classifies by
    // type/structure WITHOUT asking whether the row certifies counts rows that
    // already pass, which overstates every per-type target (measured 2026-08-22:
    // it put `Closure` at 56 when the gate-filtered figure is far smaller).
    let mut type_sets: BTreeMap<String, (usize, Vec<String>)> = BTreeMap::new();

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
                    if trust_clean::prove::diagnose_fully_faithful_gate(f, &registry).fully_faithful
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
            if tractable_mode && d.cluster_tag() == "SHAPE_GAP" {
                let cls = fragment_class(func);
                if cls.starts_with("TYPE-ONLY") {
                    let set = offending_type_kinds(func);
                    let e = type_sets.entry(set).or_insert((0, Vec::new()));
                    e.0 += 1;
                    if e.1.len() < top {
                        e.1.push(func.def_path.clone());
                    }
                }
                let t = tract.entry(cls).or_insert((0, Vec::new()));
                t.0 += 1;
                if t.1.len() < top {
                    t.1.push(func.def_path.clone());
                }
            }
            if shapes_mode && d.cluster_tag() == "SHAPE_GAP" {
                let sig = structural_signature(func);
                let s = shapes.entry(sig).or_insert((0, Vec::new()));
                s.0 += 1;
                if s.1.len() < top {
                    s.1.push(func.def_path.clone());
                }
            }
        }
    }

    println!(
        "mode: {}",
        if use_registry { "REGISTRY (per-dir fixpoint)" } else { "COMPOSITION-BLIND" }
    );
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
    if tractable_mode {
        println!("\n--- SHAPE_GAP FRAGMENT SPLIT (the raw count is NOT a work list) ---");
        let mut rows: Vec<(&&str, &(usize, Vec<String>))> = tract.iter().collect();
        rows.sort_by(|a, b| b.1.0.cmp(&a.1.0));
        for (cls, (n, samples)) in &rows {
            println!("{n:>6}  {cls}");
            for s in samples.iter().take(top) {
                println!("           {s}");
            }
        }
    }
    if tractable_mode && !type_sets.is_empty() {
        println!("\n--- TYPE-ONLY ROWS BY OFFENDING TYPE SET (gate-filtered) ---");
        let mut rows: Vec<(&String, &(usize, Vec<String>))> = type_sets.iter().collect();
        rows.sort_by(|a, b| b.1.0.cmp(&a.1.0));
        for (set, (n, samples)) in rows.iter().take(14) {
            println!("{n:>6}  {set}");
            for s in samples.iter().take(3) {
                println!("           {s}");
            }
        }
    }
    if shapes_mode {
        println!(
            "\n--- SHAPE_GAP STRUCTURAL FAMILIES (what a recognizer would have to accept) ---"
        );
        let mut rows: Vec<(&String, &(usize, Vec<String>))> = shapes.iter().collect();
        rows.sort_by(|a, b| b.1.0.cmp(&a.1.0));
        for (sig, (n, samples)) in rows.iter().take(30) {
            println!("{n:>6}  {sig}");
            for s in samples.iter().take(3) {
                println!("           {s}");
            }
        }
        let tail: usize = rows.iter().skip(30).map(|(_, (n, _))| *n).sum();
        if tail > 0 {
            println!("{tail:>6}  (+ {} further families)", rows.len().saturating_sub(30));
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

/// A coarse STRUCTURAL signature: two functions with the same signature would be
/// accepted (or declined) by the same recognizer, near enough for planning. It is
/// deliberately coarse — the point is to rank MISSING RECOGNIZERS by population,
/// not to describe any one body.
fn structural_signature(func: &VerifiableFunction) -> String {
    use std::collections::BTreeSet;

    use trust_types::{Rvalue, Statement, Terminator, Ty};
    let body = &func.body;
    let blocks = match body.blocks.len() {
        0 => "b0",
        1 => "b1",
        2 => "b2",
        3 => "b3",
        4..=6 => "b4-6",
        7..=12 => "b7-12",
        _ => "b13+",
    };
    let mut terms: BTreeSet<&str> = BTreeSet::new();
    let mut rvals: BTreeSet<&str> = BTreeSet::new();
    let ids: Vec<_> = body.blocks.iter().map(|b| b.id).collect();
    let mut back_edge = false;
    let mut seen: Vec<_> = Vec::new();
    for b in &body.blocks {
        seen.push(b.id);
        let succs: Vec<_> = match &b.terminator {
            Terminator::Goto(t) => {
                terms.insert("goto");
                vec![*t]
            }
            Terminator::SwitchInt { targets, otherwise, .. } => {
                terms.insert("switch");
                let mut v: Vec<_> = targets.iter().map(|(_, t)| *t).collect();
                v.push(*otherwise);
                v
            }
            Terminator::Call { target, .. } => {
                terms.insert("call");
                target.iter().copied().collect()
            }
            Terminator::Assert { target, .. } => {
                terms.insert("assert");
                vec![*target]
            }
            Terminator::Drop { target, .. } => {
                terms.insert("drop");
                vec![*target]
            }
            Terminator::Return => {
                terms.insert("ret");
                vec![]
            }
            Terminator::Unreachable => {
                terms.insert("unreachable");
                vec![]
            }
            _ => {
                terms.insert("other-term");
                vec![]
            }
        };
        for s in succs {
            if seen.contains(&s) && ids.contains(&s) {
                back_edge = true;
            }
        }
        for st in &b.stmts {
            match st {
                Statement::Assign { rvalue, .. } => {
                    rvals.insert(match rvalue {
                        Rvalue::Use(_) => "use",
                        Rvalue::BinaryOp(..) => "binop",
                        Rvalue::CheckedBinaryOp(..) => "checked",
                        Rvalue::UnaryOp(..) => "unop",
                        Rvalue::Cast(..) => "cast",
                        Rvalue::Ref { .. } => "ref",
                        Rvalue::AddressOf(..) => "addrof",
                        Rvalue::Aggregate { .. } => "aggregate",
                        Rvalue::Discriminant(_) => "discr",
                        Rvalue::Len(_) => "len",
                        _ => "rv-other",
                    });
                }
                Statement::SetDiscriminant { .. } => {
                    rvals.insert("setdiscr");
                }
                _ => {}
            }
        }
    }
    let ret = match &body.return_ty {
        Ty::Unit => "ret:unit",
        Ty::Bool => "ret:bool",
        Ty::Int { .. } => "ret:int",
        Ty::Adt { .. } => "ret:adt",
        Ty::Ref { .. } => "ret:ref",
        Ty::Tuple(_) => "ret:tuple",
        _ => "ret:other",
    };
    format!(
        "{blocks} {}{} term[{}] rv[{}]",
        ret,
        if back_edge { " LOOP" } else { "" },
        terms.into_iter().collect::<Vec<_>>().join(","),
        rvals.into_iter().collect::<Vec<_>>().join(","),
    )
}

/// Which side of the MODELED FRAGMENT a shape-gap body sits on.
///
/// IN-FRAGMENT is NOT a promise that a row is easy — it says only that the
/// body's types are modeled and its control flow is simple, so a recognizer
/// COULD reach it without first modeling a new type. `u128_mulhi` is
/// in-fragment and still hard. The classes exist to stop the raw count from
/// reading as available work, not to estimate effort.
///
/// The point is to stop the raw `SHAPE_GAP` count from reading as available
/// work. A body that mentions a raw pointer, a float, a trait object or any
/// type the extractor could not model is not waiting for a recognizer — it is
/// outside what this tier models at all, and writing a recognizer for it would
/// mean modeling the type first. Measured 2026-08-20, that is most of the
/// population.
fn fragment_class(func: &VerifiableFunction) -> &'static str {
    use trust_types::{Rvalue, Statement, Terminator, Ty};
    fn ty_outside(ty: &Ty, depth: usize) -> bool {
        if depth > 6 {
            return true;
        }
        match ty {
            Ty::Int { .. } | Ty::Bool | Ty::Unit => false,
            Ty::Ref { inner, .. } => ty_outside(inner, depth + 1),
            Ty::Tuple(ts) => ts.iter().any(|t| ty_outside(t, depth + 1)),
            Ty::Adt { fields, .. } => fields.iter().any(|(_, t)| ty_outside(t, depth + 1)),
            // Raw pointers, floats, and everything the extractor left unmodeled.
            _ => true,
        }
    }
    let body = &func.body;
    // STALE FIXTURE, checked FIRST because it is not recognizer work at all. A
    // body whose return local is never assigned, with a return type that is not
    // `Unit`, does not contain the code that produces its return value:
    // `std::cmp::impls::<impl PartialOrd for u8>::lt` and 11 siblings (plus 5
    // `clamp`, 1 `fmt`) dump as ZERO statements with `_0: Bool` while the real
    // function returns `a < b`.
    //
    // MEASURED 2026-08-21 against the CURRENT compiler, because "the extractor
    // drops code" would have been a soundness bug worth stopping for: it does
    // not. Re-dumping those same functions today yields 7 statements for `lt`
    // and 65 across 9 blocks for `clamp`. These entries are artifacts of their
    // harvest era.
    //
    // The disposition is NOT "regenerate them in place": `cmp-mono-select-2026-07-16`
    // is a FROZEN SNAPSHOT by contract — its PROVENANCE calls it "a historical,
    // non-authoritative W16 harvest", its `results.tsv` binds the SHA-256 of the
    // exact committed bytes, and its regenerate script requires an exact closed
    // identity set. Mutating one destroys the record it exists to keep.
    //
    // Nor is it "harvest the real bodies into a new dated directory", which was
    // BUILT AND THEN DROPPED on 2026-08-21 after measurement: 9 of the 14
    // def_paths such a harvest produces ALREADY EXIST elsewhere in the corpus, 8
    // as byte-identical committed dumps (`w16-mono-harvest-2026-07-25`,
    // `extractor-repairs-verified-2026-07-21`, …). Since the census SUMS
    // per-directory `fully_faithful` without de-duplicating def_paths, committing
    // it would have added +12 to the headline for ~4 genuinely new functions.
    //
    // So these rows are NOT WORK: the functions they name are already covered
    // elsewhere. What must never happen under any option is CERTIFYING one — a
    // recognizer that accepted a code-free body would mint a certificate for code
    // the dump does not contain.
    // `prove::tests::audit_unassigned_return_locals_never_certify` is the
    // standing guard that none of them certifies (21 such bodies today, 0
    // certifying).
    if !matches!(body.return_ty, Ty::Unit) {
        let mut writes_ret = false;
        for b in &body.blocks {
            for st in &b.stmts {
                match st {
                    Statement::Assign { place, .. }
                    | Statement::SetDiscriminant { place, .. }
                    | Statement::Deinit { place } => {
                        if place.local == 0 {
                            writes_ret = true;
                        }
                    }
                    _ => {}
                }
            }
            if let Terminator::Call { dest, .. } = &b.terminator {
                if dest.local == 0 {
                    writes_ret = true;
                }
            }
        }
        if !writes_ret {
            return "EXTRACTION-GAP: return local never assigned (the dump lacks the code)";
        }
    }
    // TYPE vs STRUCTURE, and why the ORDER of these tests matters. An earlier
    // version returned the type verdict FIRST, which made every call-bearing body
    // that merely MENTIONS an unmodeled type read as "waiting for a type model".
    // Measured 2026-08-22 that was wrong by ~4x: of the 921 corpus bodies carrying
    // an unmodeled type, 713 (77%) are ALSO call- or drop-bearing, so the type is
    // not their only blocker; only 208 are plausibly type-blocked alone. A
    // campaign aimed at the first number would model types to unlock rows that a
    // call would still stop. So the type verdict is now reported ONLY when no
    // structural blocker co-occurs, and the co-occurring case is named as such.
    let type_blocked =
        body.locals.iter().any(|l| ty_outside(&l.ty, 0)) || ty_outside(&body.return_ty, 0);
    let mut has_call = false;
    let mut has_drop = false;
    let mut has_loop = false;
    let mut seen: Vec<_> = Vec::new();
    for b in &body.blocks {
        seen.push(b.id);
        match &b.terminator {
            Terminator::Call { .. } => has_call = true,
            Terminator::Drop { .. } => has_drop = true,
            Terminator::Goto(t) if seen.contains(t) => has_loop = true,
            Terminator::SwitchInt { targets, otherwise, .. } => {
                if targets.iter().any(|(_, t)| seen.contains(t)) || seen.contains(otherwise) {
                    has_loop = true;
                }
            }
            _ => {}
        }
        for st in &b.stmts {
            if let Statement::Assign { rvalue, .. } = st {
                if matches!(rvalue, Rvalue::AddressOf(..)) {
                    return "OUT-OF-FRAGMENT: takes a raw address";
                }
            }
        }
    }
    if has_drop {
        return if type_blocked {
            "BOTH: unmodeled type AND a Drop terminator"
        } else {
            "STRUCTURE: Drop terminator (no drop-semantics model)"
        };
    }
    if has_call {
        return if type_blocked {
            "BOTH: unmodeled type AND call-bearing (a type model alone does not reach it)"
        } else {
            "COMPOSITION-GATED: call-bearing; needs its callee certified first"
        };
    }
    if type_blocked {
        return "TYPE-ONLY: unmodeled type is the sole structural blocker";
    }
    if has_loop {
        return "IN-FRAGMENT(loop): modeled types, no calls — a loop recognizer could reach it";
    }
    "IN-FRAGMENT(straight-line): modeled types, call-free, loop-free"
}

/// The set of type kinds in a body's signature/locals that `fragment_class`
/// counts as unmodeled, rendered as a stable sorted label.
fn offending_type_kinds(func: &VerifiableFunction) -> String {
    use std::collections::BTreeSet;

    use trust_types::Ty;
    fn walk(ty: &Ty, out: &mut BTreeSet<&'static str>, depth: usize) {
        if depth > 24 {
            return;
        }
        match ty {
            Ty::Int { .. } | Ty::Bool | Ty::Unit => {}
            Ty::Ref { inner, .. } => walk(inner, out, depth + 1),
            Ty::Tuple(ts) => {
                for t in ts {
                    walk(t, out, depth + 1);
                }
            }
            Ty::Adt { fields, .. } => {
                for (_, t) in fields {
                    walk(t, out, depth + 1);
                }
            }
            Ty::RawPtr { pointee, .. } => {
                out.insert("RawPtr");
                walk(pointee, out, depth + 1);
            }
            Ty::Slice { elem, .. } => {
                out.insert("Slice");
                walk(elem, out, depth + 1);
            }
            Ty::Array { elem, .. } => {
                out.insert("Array");
                walk(elem, out, depth + 1);
            }
            Ty::Float { .. } => {
                out.insert("Float");
            }
            Ty::Closure { .. } => {
                out.insert("Closure");
            }
            Ty::Dynamic { .. } => {
                out.insert("Dynamic");
            }
            Ty::FnPtr { .. } => {
                out.insert("FnPtr");
            }
            Ty::FnDef { .. } => {
                out.insert("FnDef");
            }
            Ty::Str => {
                out.insert("Str");
            }
            Ty::Char => {
                out.insert("Char");
            }
            Ty::Never => {
                out.insert("Never");
            }
            Ty::Coroutine { .. } => {
                out.insert("Coroutine");
            }
            Ty::Datatype { .. } => {
                out.insert("Datatype");
            }
            Ty::Unsupported { .. } => {
                out.insert("Unsupported");
            }
            _ => {
                out.insert("other");
            }
        }
    }
    let mut out = BTreeSet::new();
    for l in &func.body.locals {
        walk(&l.ty, &mut out, 0);
    }
    walk(&func.body.return_ty, &mut out, 0);
    out.into_iter().collect::<Vec<_>>().join(", ")
}
