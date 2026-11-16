//! tir_scoreboard: replay the WORKING-TREE `lower_module_to_lir` over
//! `-Ztrust-dump=ir:` binary Modules and classify every refusal.
//!
//! This is the measurement half of the standing goal "trust-cg fully compiles
//! all of Trust via trust-ir": the sealed toolchain's `-Ztrust-cg-frontend`
//! report scores the SEALED converter, while this example scores the working
//! tree, so a converter widening is measurable before a toolchain rebuild.
//!
//! Usage:
//!   targo --unverified run -p trust-cg-bridge --example tir_scoreboard \
//!       --features tir-scoreboard -- DUMP_DIR/*.trust-ir.bin
//!
//! Output: one `fn` line per refused function (grep-friendly), one `mod` line
//! per module, and a global refusal histogram. For an `UnsupportedInst
//! { inst: "Call" }` refusal, every call in the function body is classified by
//! callee shape — the classes map 1:1 onto candidate inliner widenings:
//!   * `nonlocal`        — callee not in this Module (upstream instance hole)
//!   * `bodyless`        — local declaration without blocks
//!   * `self-recursive`  — callee == caller
//!   * `local-nonleaf`   — local callee that itself calls (recursion widening)
//!   * `local-memops`    — local callee whose body holds non-inlinable insts
//!                         (Load/Store/Alloca/GEP/..., memory-splice widening)
//!   * `local-multiret`  — local callee with a non-single-value Return
//!   * `local-plain`     — none of the above: the inliner/fixpoint should have
//!                         taken it (a residue here is an inliner gap or bug)
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_cg_bridge::module_to_lir::lower_trust_ir_function_to_lir;
use trust_ir::inst::Inst;
use trust_ir::{Function as IrFunction, Module};

/// Mirror of the converter's `is_multiblock_inlinable_value` set, plus the
/// terminators the splice can clone. Kept local on purpose: the example
/// classifies against the CURRENT admission surface, and a drift here only
/// mislabels a histogram row, never a compile.
fn is_inlinable_body_inst(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Const { .. }
            | Inst::BinOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::Cast { .. }
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::Undef { .. }
            | Inst::InsertField { .. }
            | Inst::MakeAggregate { .. }
            | Inst::ExtractField { .. }
            | Inst::Assume { .. }
            | Inst::Assert { .. }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::Unreachable
    )
}

fn classify_callee(
    module: &Module,
    caller: &IrFunction,
    callee: trust_ir::value::FuncId,
) -> &'static str {
    let Some(f) = module.function_by_id(callee) else {
        return "nonlocal";
    };
    if f.blocks.is_empty() {
        return "bodyless";
    }
    if f.id == caller.id {
        return "self-recursive";
    }
    let has_call = f
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .any(|n| matches!(n.inst, Inst::Call { .. } | Inst::CallIndirect { .. }));
    if has_call {
        return "local-nonleaf";
    }
    let has_noninlinable =
        f.blocks.iter().flat_map(|b| b.body.iter()).any(|n| !is_inlinable_body_inst(&n.inst));
    if has_noninlinable {
        return "local-memops";
    }
    let multiret = f
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .any(|n| matches!(&n.inst, Inst::Return { values } if values.len() != 1));
    if multiret {
        return "local-multiret";
    }
    "local-plain"
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!("usage: tir_scoreboard <module.trust-ir.bin>...");
        std::process::exit(2);
    }

    let mut histogram: BTreeMap<String, usize> = BTreeMap::new();
    let mut call_classes: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut total_fns = 0usize;
    let mut total_ok = 0usize;

    for path in &args {
        let bytes = match std::fs::read(path) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("read {path}: {e}");
                continue;
            }
        };
        let module = match trust_ir::binary::deserialize_module(&bytes) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("deserialize {path}: {e}");
                continue;
            }
        };

        let mut ok = 0usize;
        let mut refused = 0usize;
        for function in &module.functions {
            // Declarations (body-less imports) are not lowering subjects.
            if function.blocks.is_empty() {
                continue;
            }
            // Static-initializer bodies are evaluated, not codegen'd: the
            // frontend lowers reachable `MonoItem::Fn` instances only, and a
            // static's bytes come from const evaluation. Scoring them would
            // overcount the goal denominator.
            if function.name.ends_with("::{const-init}") {
                continue;
            }
            total_fns += 1;
            match lower_trust_ir_function_to_lir(&module, function) {
                Ok(_) => {
                    ok += 1;
                    total_ok += 1;
                }
                Err(e) => {
                    refused += 1;
                    let msg = e.to_string();
                    // Histogram key: strip per-function noise (backtick names).
                    let key: String = {
                        let mut k = String::new();
                        let mut in_tick = false;
                        for c in msg.chars() {
                            match c {
                                '`' => in_tick = !in_tick,
                                _ if in_tick => {}
                                _ => k.push(c),
                            }
                        }
                        k
                    };
                    *histogram.entry(key).or_default() += 1;
                    let is_call_residue = msg.contains("unsupported instruction");
                    if is_call_residue && msg.contains("Call") {
                        for block in &function.blocks {
                            for node in &block.body {
                                if let Inst::Call { callee, .. } = &node.inst {
                                    let class = classify_callee(&module, function, *callee);
                                    *call_classes.entry(class).or_default() += 1;
                                    println!(
                                        "fn {} :: {} :: call-> {}",
                                        function.name,
                                        class,
                                        module
                                            .function_by_id(*callee)
                                            .map(|f| f.name.as_str())
                                            .unwrap_or("<nonlocal>")
                                    );
                                }
                            }
                        }
                    } else {
                        println!("fn {} :: refused :: {}", function.name, msg);
                    }
                }
            }
        }
        println!("mod {path}: {ok} ok / {refused} refused");
    }

    println!("\n== working-tree converter: {total_ok}/{total_fns} functions lower ==");
    println!("\n== refusal histogram ==");
    let mut rows: Vec<(usize, &String)> = histogram.iter().map(|(k, v)| (*v, k)).collect();
    rows.sort_by(|a, b| b.0.cmp(&a.0));
    for (n, k) in rows {
        println!("{n:6}  {k}");
    }
    println!("\n== Call-residue callee classes ==");
    let mut rows: Vec<(usize, &'static str)> = call_classes.iter().map(|(k, v)| (*v, *k)).collect();
    rows.sort_by(|a, b| b.0.cmp(&a.0));
    for (n, k) in rows {
        println!("{n:6}  {k}");
    }
}
