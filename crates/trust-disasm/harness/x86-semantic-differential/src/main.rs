//! THE x86-64 SEMANTIC DIFFERENTIAL — does the instruction DO what
//! `X86_64Semantics` says, judged by execution under Rosetta 2?
//!
//! The third harness, closing the gap section A0 of the AArch64 twin records:
//! until now the x86-64 model had a DECODE differential only, and of the
//! sixteen 2026-08-18 defects that comparison could catch eight — shift-count
//! masking and the shift flags needed something that EXECUTES. This is that.
//!
//! # THE CHECK
//!
//!     for candidate bytes W and starting state S:
//!         decode_x86_64(W) Ok  ∧  X86_64Semantics::effects Ok
//!         ∧  W executes from S under Rosetta
//!     ⟹ the replayed effects agree with the execution on rax..r15, rsp, the
//!        next rip, the MODELED flags (SF ZF CF OF), and every 8-byte word of
//!        the shared memory window.
//!
//! # BLIND SPOTS — the authoritative inventory
//!
//! The rule is the twin's, restated because forgetting it is how ITS x86 gap
//! went unnoticed: **if a limitation is not listed here, this harness is
//! claiming to cover it.**
//!
//! ## A0. THE ORACLE IS ROSETTA 2, NOT SILICON
//!
//! This host has no x86-64 CPU (measured: an `-arch x86_64` Mach-O would not
//! even start before `softwareupdate --install-rosetta`). The executor runs
//! under Apple's translator — an INDEPENDENT second implementation of x86-64,
//! unrelated to our decoder and to LLVM, with hardware TSO and exact
//! scalar-integer semantics as its published fidelity contract. Strictly
//! stronger than the decode differential (it executes; it judges values,
//! flags, and memory), strictly weaker than hardware: a bug Rosetta shares
//! with our model is invisible here, and Rosetta's own fidelity is an axiom
//! of this harness, not a theorem.
//!
//! ## B. PF and AF are not compared
//!
//! The model carries exactly four flags (SF ZF CF OF on the shared N Z C V
//! state). Parity and adjust exist only on the hardware side; the executor
//! reads out only the modeled four.
//!
//! ## C. A flag the model DECLINES is masked, not compared
//!
//! The shift CF/OF are deliberate per-instruction unknowns (the SDM leaves
//! them undefined off the happy path). Such bits are counted in
//! `flag_bits_declined` and excluded bit-wise; SF/ZF of the same shift remain
//! compared. A model that declined EVERY flag would show up as that counter
//! exploding, not as quiet agreement.
//!
//! ## D. The XMM/YMM/x87 files are neither loaded nor compared
//!
//! `X86_64Semantics` refuses SSE/AVX/x87, so such instructions are outside
//! the antecedent (`NoEffects`), and no vector state exists on either side.
//!
//! ## E. Coverage is GENERATED, never exhaustive
//!
//! No fixed width to enumerate. `compared` counts what the generator
//! produced; per-opcode families and per-bucket exclusions are printed so a
//! shrinking population is a visible number, never silence.
//!
//! ## F. One instruction per slot; self-referential code is out of scope
//!
//! Candidates run once from a controlled state. Anything whose behaviour
//! depends on running INSIDE a larger program (self-modifying code, RIP
//! chains) is not represented.

mod ctx;
mod generate;
mod model;
mod mutate;
mod natsem;

use std::collections::BTreeMap;
use std::io::Write;

use crate::model::Skip;
use crate::mutate::Mutation;

#[derive(Default)]
struct Counts {
    candidates: usize,
    outside_antecedent: usize,
    replayer_unsupported: usize,
    eval_error: usize,
    mem_outside_window: usize,
    mem_read_outside: usize,
    hw_timeout: usize,
    hw_killed: usize,
    diff_overflow: usize,
    escaped_into_prologue: usize,
    compared: usize,
    agreed: usize,
    mismatched: usize,
    flag_bits_declined: usize,
    families: BTreeMap<String, usize>,
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut mode = "all".to_string();
    let mut seed: u64 = 0xC0FFEE;
    let mut limit: usize = 20_000;
    let mut show = 10usize;
    let mut mutation = Mutation::None;
    let mut mutation_name = String::new();

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--mode" => {
                i += 1;
                mode = args.get(i).cloned().unwrap_or(mode);
            }
            "--seed" => {
                i += 1;
                seed = args.get(i).and_then(|s| s.parse().ok()).unwrap_or(seed);
            }
            "--limit" => {
                i += 1;
                limit = args.get(i).and_then(|s| s.parse().ok()).unwrap_or(limit);
            }
            "--show" => {
                i += 1;
                show = args.get(i).and_then(|s| s.parse().ok()).unwrap_or(show);
            }
            "--mutate" => {
                i += 1;
                mutation_name = args.get(i).cloned().unwrap_or_default();
                mutation = match Mutation::parse(&mutation_name) {
                    Some(m) => m,
                    None => {
                        eprintln!("unknown mutation `{mutation_name}`; --list-mutations");
                        std::process::exit(2);
                    }
                };
            }
            "--list-mutations" => {
                for m in mutate::BATTERY {
                    println!("{m}");
                }
                return;
            }
            other => {
                eprintln!("unknown argument {other}");
                std::process::exit(2);
            }
        }
        i += 1;
    }

    let bin = concat!(env!("CARGO_MANIFEST_DIR"), "/natsem86");
    let (word_pc, slot_base, rec_size, ctx_len) = natsem::slotpc(bin);
    assert_eq!(rec_size, natsem::REC_SIZE, "record layout drifted between C and Rust");
    assert_eq!(ctx_len, 136, "ctx layout drifted between C and Rust");

    let all = generate::candidates(&mode, seed, limit);
    let profiles = ctx::default_profiles();
    let workdir = std::env::temp_dir().join(format!("x86-sem-diff-{seed:x}"));
    let _ = std::fs::create_dir_all(&workdir);

    let mut counts = Counts::default();
    counts.candidates = all.len();
    let mut examples: Vec<String> = Vec::new();

    for profile in &profiles {
        // Build words.bin for the candidates that decode AND model.
        let mut in_scope: Vec<(Vec<u8>, usize, &'static str, model::Predicted)> = Vec::new();
        for bytes in &all {
            match model::predict(bytes, word_pc, profile, mutation) {
                Ok((len, family, predicted)) => {
                    if bytes.len() < len {
                        // Decoder consumed past the candidate: the trailing
                        // bytes would be 0xCC filler, so length and semantics
                        // would disagree with the oracle about DIFFERENT bytes.
                        counts.outside_antecedent += 1;
                        continue;
                    }
                    in_scope.push((bytes[..len].to_vec(), len, family, predicted));
                }
                Err(Skip::NotDecoded | Skip::NoEffects) => counts.outside_antecedent += 1,
                Err(Skip::UnsupportedEffect(_)) => counts.replayer_unsupported += 1,
                Err(Skip::EvalError(_)) => counts.eval_error += 1,
            }
        }

        let ctx_path = workdir.join(format!("{}.ctx", profile.name));
        let words_path = workdir.join(format!("{}.words", profile.name));
        let recs_path = workdir.join(format!("{}.recs", profile.name));
        std::fs::write(&ctx_path, profile.ctx_bytes()).expect("write ctx");
        {
            let mut f = std::fs::File::create(&words_path).expect("words");
            for (bytes, len, _, _) in &in_scope {
                let mut slot = [0u8; natsem::SLOT_BYTES];
                slot[0] = *len as u8;
                slot[1..1 + bytes.len()].copy_from_slice(bytes);
                f.write_all(&slot).expect("write slot");
            }
        }

        let records = natsem::run(
            bin,
            ctx_path.to_str().unwrap(),
            words_path.to_str().unwrap(),
            recs_path.to_str().unwrap(),
            in_scope.len(),
        );

        for ((bytes, len, family, predicted), record) in in_scope.iter().zip(&records) {
            match record.outcome {
                natsem::OUT_TIMEOUT => {
                    counts.hw_timeout += 1;
                    continue;
                }
                natsem::OUT_KILLED => {
                    counts.hw_killed += 1;
                    continue;
                }
                _ => {}
            }
            if predicted.mem_outside_window || predicted.mem_read_outside_window {
                counts.mem_outside_window += 1;
                if predicted.mem_read_outside_window {
                    counts.mem_read_outside += 1;
                }
                continue;
            }
            if record.ndiff == 0xff {
                counts.diff_overflow += 1;
                continue;
            }

            // ESCAPE that re-enters the slot prologue: control branched
            // BACKWARD into the setup code, which then re-ran, so the recorded
            // state is not this one word's post-state. The AArch64 twin
            // excludes the same class ("branched back into the slot
            // prologue"). `slot_base <= pc < word_pc` is exactly the prologue.
            // A branch whose TARGET is the slot prologue makes the hardware
            // re-run setup and fault somewhere else entirely, so the recorded
            // pc is a MULTI-instruction post-state, not this word's. Key the
            // exclusion on the MODEL's predicted target (the branch target it
            // computed) — the record's own pc is the final fault, which is why
            // keying on it missed these. `slot_base <= target < word_pc` is the
            // prologue exactly.
            // Any branch whose MODEL target is the prologue is un-bracketable,
            // whatever the hardware then did: if taken, the CPU re-runs setup
            // and the record is a multi-instruction state; if the model and
            // hardware even DISAGREE about taken-ness, the disagreement plays
            // out as re-executed setup versus a fallthrough and cannot be read
            // as this one word's effect. Excluded regardless of outcome.
            // A branch whose MODEL target lands anywhere INSIDE the slot —
            // the prologue OR the candidate's own bytes — is un-bracketable:
            // the CPU either re-runs setup or executes OVERLAPPING bytes
            // (`7d ff` = jge -1 jumps into its own second byte), so the record
            // is never this one word's clean post-state. The only in-slot
            // target that IS comparable is the epilogue byte itself (a
            // fallthrough or a branch to exactly pc+len), which is `>=
            // epilogue_pc`. Everything below it is excluded.
            let epilogue_pc = word_pc + *len as u64;
            if predicted.pc >= slot_base && predicted.pc < epilogue_pc {
                counts.escaped_into_prologue += 1;
                continue;
            }

            // The model ACCEPTED this instruction; the hardware must have
            // executed it. A fault here is the invariant class — x86 has no
            // separate exhaustive invariant harness, so it is a FAMILY here.
            if record.outcome != natsem::OUT_EXECUTED && record.outcome != natsem::OUT_ESCAPED {
                counts.compared += 1;
                counts.mismatched += 1;
                *counts.families.entry(format!("{family}:hardware_refused")).or_default() += 1;
                if examples.len() < show {
                    examples.push(format!(
                        "{bytes:02x?} [{}] {family}: model accepts, hardware outcome {}",
                        profile.name, record.outcome
                    ));
                }
                continue;
            }

            counts.compared += 1;
            counts.flag_bits_declined +=
                usize::from((!predicted.flags_mask & 0b1111).count_ones() as u16) as usize;
            let mut wrong: Vec<String> = Vec::new();

            for r in 0..16 {
                if predicted.gpr[r] != record.gpr[r] {
                    wrong.push(format!(
                        "r{r}: model={:#x} rosetta={:#x}",
                        predicted.gpr[r], record.gpr[r]
                    ));
                }
            }
            if predicted.pc != record.pc {
                // For EXECUTED the record pc is the epilogue byte (= pc+len);
                // for ESCAPED it is the branch target. Both are exactly what
                // the model's pc should equal.
                wrong.push(format!("pc: model={:#x} rosetta={:#x}", predicted.pc, record.pc));
            }
            let mask = predicted.flags_mask;
            if (predicted.flags & mask) != (record.flags & mask) {
                wrong.push(format!(
                    "flags(SZCV&{mask:04b}): model={:04b} rosetta={:04b}",
                    predicted.flags & mask,
                    record.flags & mask
                ));
            }
            let mut hw_mem: Vec<(u64, u64)> = record.mem.clone();
            hw_mem.sort_unstable();
            let mut mo_mem = predicted.mem.clone();
            mo_mem.sort_unstable();
            if hw_mem != mo_mem {
                wrong.push(format!("mem: model={mo_mem:x?} rosetta={hw_mem:x?}"));
            }

            if wrong.is_empty() {
                counts.agreed += 1;
            } else {
                counts.mismatched += 1;
                *counts.families.entry((*family).to_string()).or_default() += 1;
                if examples.len() < show {
                    examples.push(format!(
                        "{bytes:02x?} len={len} [{}] {family}: {}",
                        profile.name,
                        wrong.join("; ")
                    ));
                }
            }
        }
    }

    println!("x86-64 semantic differential (oracle: Rosetta 2)");
    println!("  mode        : {mode} (seed {seed:#x}, limit {limit})");
    if mutation != Mutation::None {
        println!("  mutation    : {mutation_name}");
    }
    println!("  candidates  : {} x {} profiles", counts.candidates, profiles.len());
    println!("  compared    : {}", counts.compared);
    println!("  agreed      : {}", counts.agreed);
    println!("  mismatched  : {}", counts.mismatched);
    println!(
        "  unchecked   : outside_antecedent={} replayer_unsupported={} eval_error={} \
         mem_window={} (reads_outside={}) diff_overflow={} escaped_prologue={} hw_timeout={} hw_killed={}",
        counts.outside_antecedent,
        counts.replayer_unsupported,
        counts.eval_error,
        counts.mem_outside_window,
        counts.mem_read_outside,
        counts.diff_overflow,
        counts.escaped_into_prologue,
        counts.hw_timeout,
        counts.hw_killed
    );
    println!("  flag bits declined by the model: {}", counts.flag_bits_declined);
    if !counts.families.is_empty() {
        println!(
            "  families    : {}",
            counts.families.iter().map(|(k, v)| format!("{k}={v}")).collect::<Vec<_>>().join(", ")
        );
    }
    for e in &examples {
        println!("    {e}");
    }

    if mutation != Mutation::None {
        if counts.mismatched == 0 {
            println!("NON-VACUITY FAILURE: the mutation was not caught.");
            std::process::exit(1);
        }
        println!("mutation caught ({} mismatches)", counts.mismatched);
        return;
    }
    if counts.compared == 0 {
        println!("VACUOUS: nothing was compared.");
        std::process::exit(1);
    }
    if counts.mismatched > 0 {
        std::process::exit(1);
    }
}
