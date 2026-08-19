//! THE x86-64 DECODE DIFFERENTIAL — does our decoder read the bytes the way an
//! independent disassembler does?
//!
//! This harness exists because of a measured gap. `native-invariant` and
//! `native-semantic` beside it are **AArch64 only** — every antecedent in them
//! names `decode_aarch64` and `Aarch64Semantics` — so until 2026-08-18 the
//! x86-64 half of `trust-disasm` was checked by unit tests alone, that is,
//! against expectations a human wrote down. Sixteen defects were found by audit
//! in one day, five of them WRONG ADDRESSES coexisting in a single file, and
//! two checked-in tests were asserting two of the bugs as CORRECT.
//!
//! # THE CHECK
//!
//!     for every candidate byte string W:
//!         trust_disasm::decode_x86_64(W) is Ok  ∧  the oracle decodes W
//!     ⟹ they agree on the instruction LENGTH, on the effective-address terms
//!       (or the resolved absolute address), and on the register operands.
//!
//! # THE ORACLE IS NOT HARDWARE, AND THAT IS THE HEADLINE LIMITATION
//!
//! The AArch64 harnesses execute candidate words on the CPU. This one cannot.
//! MEASURED on this host (Apple M5 Max, arm64 darwin): an `-arch x86_64` Mach-O
//! BUILDS but will not run — `bad CPU type in executable` — and Rosetta's
//! `oahd` is not running. There is no x86-64 CPU here to be ground truth.
//!
//! So the oracle is LLVM's disassembler (`clang` to assemble, `objdump -d` to
//! read back), and the consequent is "agrees with an INDEPENDENT
//! DISASSEMBLER", not "agrees with the hardware". Two decoders can be wrong
//! together, and a shared misreading of the SDM would be invisible here. That
//! is strictly weaker than the sibling harnesses and is why this file says
//! "differential", never "oracle" unqualified.
//!
//! # BLIND SPOTS — the authoritative inventory
//!
//! Following `native-semantic`'s rule, which is normative and is repeated here
//! because it is the reason that harness's own x86 gap went unnoticed:
//! **if a limitation is not listed here, this harness is claiming to cover it.**
//!
//! ## A. It is a DECODE differential — EFFECTS are entirely out of scope
//!
//! Nothing about what an instruction DOES is compared: not flags, not the value
//! written, not masking, not the width of a value (as opposed to the width in
//! the mnemonic). Concretely, of the sixteen defects of 2026-08-18 this check
//! would have caught the eight that are decode-level — the five address
//! defects, `mov ah` vs `spl`, `movb`'s store width, and `jp`/`jnp` — and would
//! NOT have caught shift-count masking or the shift flags. Those need a
//! semantic differential, which needs a CPU.
//!
//! ## B. Coverage is GENERATED, never exhaustive
//!
//! AArch64 words are fixed-width, so `native-invariant --full` enumerates all
//! 2^32. x86-64 instructions are 1-15 bytes: there is no space to enumerate.
//! Coverage here is whatever the generator produces, so a `compared` count is a
//! statement about the GENERATOR, not about the encoding space. The
//! addressing-mode sweep is systematic over the ModRM/SIB/REX matrix — the
//! region every address defect lived in — and everything else is a corpus or
//! random bytes.
//!
//! ## C. Only the first instruction of each slot is read
//!
//! Candidates sit at a fixed 16-byte stride (>15, the longest instruction)
//! padded with `int3`, so a length disagreement is contained to one slot rather
//! than desynchronising the stream. Bytes a shorter decode leaves over are not
//! compared; the length mismatch itself is the finding.
//!
//! ## D. Forms the projection cannot parse are COUNTED, never assumed
//!
//! An AT&T operand shape `parse_att_mem` does not handle is reported as
//! `OracleOperandUnparsed` — OUR gap, reported separately from a mismatch,
//! because folding it into agreement is how a harness quietly stops checking.
//! Likewise a candidate our decoder refuses is `OurDecodeRefused`: refusal is a
//! legitimate answer for a verifying compiler and is not a disagreement.
//!
//! ## E. Segment prefixes, 16-bit address size, VEX/EVEX, x87 and SIMD
//!
//! The generator does not emit them and the projection does not model them. Not
//! "handled" — absent. Anything the decoder does with them is unmeasured here.
//!
//! # NON-VACUITY
//!
//! `--mutate NAME` runs the differential against a deliberately wrong decode
//! (see `mutate.rs`), and the gate requires every mutation to be CAUGHT. A
//! harness that has quietly stopped comparing something fails before any
//! agreement number is believed. The battery is a floor: each mutation breaks a
//! whole class, whereas the real defects were narrow and needed a specific
//! encoding to be in the population at all.

mod compare;
mod generate;
mod mutate;
mod oracle;

use trust_disasm::arch::{Arch, Decoder};
use trust_disasm::x86_64::X86_64Decoder;

/// Decode at the address the candidate actually occupies.
///
/// This must match the oracle's view: a RIP-relative address resolves against
/// the NEXT instruction, so it is a function of WHERE the candidate sits.
/// Decoding every candidate at 0 while the oracle saw it at `16 * slot`
/// reported a mismatch on every RIP-relative form — a harness bug, found on the
/// very first run, and precisely the kind the slot layout makes visible.
fn decode(bytes: &[u8], address: u64) -> Result<trust_disasm::Instruction, ()> {
    X86_64Decoder::new().decode(bytes, address).map_err(|_| ())
}

use std::collections::BTreeMap;

use compare::{Mismatch, Unchecked};

#[derive(Default, Debug)]
struct Counts {
    compared: usize,
    agreed: usize,
    mismatched: usize,
    unchecked: BTreeMap<Unchecked, usize>,
    families: BTreeMap<String, usize>,
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut mutation: Option<String> = None;
    let mut mode = "sweep".to_string();
    let mut seed: u64 = 0xC0FFEE;
    let mut limit: usize = 20_000;
    let mut show = 8usize;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--mutate" => {
                i += 1;
                mutation = args.get(i).cloned();
            }
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

    let candidates = generate::candidates(&mode, seed, limit);
    if candidates.is_empty() {
        eprintln!("mode `{mode}` produced no candidates");
        std::process::exit(2);
    }

    let workdir = std::env::temp_dir().join(format!("x86-decode-differential-{seed:x}"));
    let _ = std::fs::create_dir_all(&workdir);

    let mut counts = Counts::default();
    let mut examples: Vec<(Vec<u8>, Mismatch)> = Vec::new();

    // Batch so one assemble+disassemble covers many candidates.
    for chunk in candidates.chunks(2000) {
        let oracle_out = match oracle::disassemble(chunk, &workdir) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("oracle failed: {e}");
                std::process::exit(3);
            }
        };
        for (slot, (bytes, theirs)) in chunk.iter().zip(oracle_out).enumerate() {
            // Address is RELATIVE TO THE CHUNK: each chunk is assembled as its
            // own object starting at 0, so the oracle sees slot `n` at `16n`
            // within that object. Treating chunks as one continuous space made
            // every RIP-relative candidate past the first chunk disagree by
            // exactly the chunk's byte length — which is how this was found.
            let address = (slot * oracle::SLOT) as u64;
            let Some(theirs) = theirs else {
                *counts.unchecked.entry(Unchecked::OracleSilent).or_default() += 1;
                continue;
            };
            if compare::has_unmodelled_prefix(bytes) {
                *counts.unchecked.entry(Unchecked::UnmodelledPrefix).or_default() += 1;
                continue;
            }
            let Ok(insn) = decode(bytes, address) else {
                *counts.unchecked.entry(Unchecked::OurDecodeRefused).or_default() += 1;
                continue;
            };
            let mut ours = match compare::project_ours(&insn) {
                Ok(p) => p,
                Err(u) => {
                    *counts.unchecked.entry(u).or_default() += 1;
                    continue;
                }
            };
            if let Some(m) = mutation.as_deref() {
                mutate::apply(&mut ours, m);
            }
            let theirs_proj = match compare::project_oracle(&theirs) {
                Ok(p) => p,
                Err(u) => {
                    *counts.unchecked.entry(u).or_default() += 1;
                    continue;
                }
            };
            counts.compared += 1;
            match compare::compare(&ours, &theirs_proj) {
                None => counts.agreed += 1,
                Some(m) => {
                    counts.mismatched += 1;
                    *counts.families.entry(m.family.to_string()).or_default() += 1;
                    if examples.len() < show {
                        examples.push((bytes.clone(), m));
                    }
                }
            }
        }
    }

    println!("x86-64 decode differential");
    println!("  mode        : {mode} (seed {seed:#x}, limit {limit})");
    if let Some(m) = &mutation {
        println!("  mutation    : {m}");
    }
    println!("  candidates  : {}", candidates.len());
    println!("  compared    : {}", counts.compared);
    println!("  agreed      : {}", counts.agreed);
    println!("  mismatched  : {}", counts.mismatched);
    println!(
        "  unchecked   : {}",
        counts
            .unchecked
            .iter()
            .map(|(k, v)| format!("{k:?}={v}"))
            .collect::<Vec<_>>()
            .join(", ")
    );
    if !counts.families.is_empty() {
        println!(
            "  families    : {}",
            counts.families.iter().map(|(k, v)| format!("{k}={v}")).collect::<Vec<_>>().join(", ")
        );
    }
    for (bytes, m) in &examples {
        println!("    {:02x?}  {}: {}", bytes, m.family, m.detail);
    }

    // A mutation run must MISMATCH; a normal run must not.
    if mutation.is_some() {
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
