//! THE INVARIANT HARNESS — checks the CLASS, not the instance.
//!
//! Four soundness families have now been found one at a time, each after the
//! previous was declared closed: dropped `Effect::PcUpdate`, the overflowing
//! bitmask decoder, unvalidated reserved fields, and CONSTRAINED UNPREDICTABLE
//! operand aliasing. Every one of them was a word the gate ACCEPTED and the CPU
//! REFUSES. A mnemonic-level differential cannot see that class: it compares
//! NAMES, and both aliasing and reserved-field words can carry correct names.
//!
//! THE INVARIANT, stated so it can be executed:
//!
//!     for every word W:
//!         trust_disasm::decode_aarch64(W) is Ok
//!       ∧ Aarch64Semantics::effects(W)    is Ok
//!     ⟹ W does not fault when executed natively.
//!
//! WHY THAT ANTECEDENT AND NOT "the gate reaches Proven". The gate cannot reach
//! Proven on an object unless every word in it decodes and the model produces
//! effects for it — the model is how the machine side is built. So
//! {gate-Proven words} ⊆ {decode ∧ model words}, and checking the WEAKER
//! antecedent finds a SUPERSET of the real violations. That is conservative in
//! the correct direction: this harness can over-report, never under-report.
//!
//! IT IS EXHAUSTIVE, NOT SAMPLED. The AArch64 encoding space is 2^32 words;
//! roughly 22% of it decodes and models. The native executor runs ~450k
//! words/sec, so the entire space is checkable in under an hour on this host.
//! `--full` checks every word there is. Sampling modes exist only for a fast
//! pre-flight; the recorded baseline is a full run.
//!
//! Ground truth is `natexec` (natexec.c, beside this file), which executes
//! each word for real and classifies BY FAULTING PC, so a taken branch landing
//! in unmapped memory is never confused with the word itself faulting.
//!
//! # BLIND SPOTS — the authoritative inventory
//!
//! Normative, in the same sense as the corresponding section of
//! `native-semantic`: **if a limitation is not listed here, this harness is
//! claiming to cover it.** The reason the fault class survived four separate
//! discoveries is that nobody could state what the checks did not reach.
//!
//! ## What this harness does NOT check — the big one
//!
//! **SEMANTICS.** This is a FAULT vs NO-FAULT oracle and nothing else. A word
//! that executes but whose real effect differs from `Aarch64Semantics::effects`
//! passes here with no complaint, and that is a false Proven exactly as much as
//! an unexecutable word. That entire class belongs to `native-semantic` beside
//! this one, and it found three live families the moment it existed. **A green
//! run here means the CPU RUNS the word; it does not mean the CPU does what was
//! certified.**
//!
//! ## Outside the antecedent — never candidates
//!
//! Words the decoder or `Aarch64Semantics` refuses are not scanned, because the
//! gate cannot reach Proven on them either. That makes the check conservative in
//! the right direction — it over-reports, never under-reports — but it is not
//! coverage of those encodings. `SVC`/`HVC`/`SMC`/`BRK`/`HLT`/`MRS`/`MSR` and
//! the other privileged forms are refused by the model and therefore untested.
//!
//! ## Feature-dependent legality, and why a violation here is host-relative
//!
//! The host is one Apple aarch64 CPU at EL0. An encoding that is UNDEFINED here
//! for want of a `FEAT_*` may be legal on another aarch64 part, and vice versa.
//! A SIGILL is therefore evidence that THIS CPU refuses a word the model
//! accepts — which is exactly the gate's exposure on this host — but the
//! converse, "no SIGILL means architecturally legal", does not follow. SVE/SME,
//! PAC and MTE are absent; nothing behind them is exercised.
//!
//! ## Outcomes that are not violations, and are not agreement either
//!
//! * `MEMFAULT` — the word was ACCEPTED by the CPU (on AArch64 an undefined
//!   encoding raises before any address is generated), and then addressed
//!   memory this harness had not mapped. It proves acceptance and says nothing
//!   about semantics.
//! * `ESCAPED` — control flow left the slot. The encoding was accepted; where
//!   it went is not this harness's question.
//! * `TIMEOUT` — the word did not return in the allotted time. Counted, never
//!   folded into either verdict.
//! * `KILLED` — some `brk` immediates are claimed by the kernel as fatal traps
//!   and deliver SIGKILL, which no handler can intercept. The driver resumes at
//!   the next index and records the casualty rather than losing it.
//!
//! ## System state
//!
//! One MMU configuration, one `SCTLR`, one translation regime, EL0 only. All
//! registers are seeded to the SAME pointer value (which is right for a fault
//! question and useless for a semantic one — see `native-semantic`'s profiles).
//! `x16` is pinned away from any syscall number so that a candidate which
//! happens to be `SVC` cannot reach a real system call.
//!
//! # NON-VACUITY
//!
//! `--force-candidates` admits the words in a `--words` file regardless of what
//! the decoder and the model say about them. `run.sh` uses it to drive three
//! encodings the CPU is KNOWN to refuse through the entire sweep — chunking,
//! executor, PC-based classification, violation counting, report and baseline
//! emission — and requires that all three be reported as violations while their
//! one-register controls are not. Without it there is no way to make this sweep
//! produce a violation at all: every word that would be one has been fixed, so
//! "0 violations" and "the pipeline is broken" print identically.
//!
//! usage:
//!   natinv --full            [--workers N] [--workdir D] [--out PREFIX]
//!   natinv --sample COUNT    [--workers N] [--workdir D] [--out PREFIX]
//!   natinv --words FILE.txt  (hex words, one per line — recheck a violation set)
//!   natinv --words F --force-candidates   (non-vacuity: bypass the antecedent)

use std::collections::HashMap;
use std::io::Write;
use std::sync::{Arc, Mutex};

mod attribute;
mod natexec;

use attribute::{decoder_fn, producible};
use natexec::{OUT_N, OUT_NAMES, OUT_SIGILL, natexec_path, run_chunk};
use trust_disasm::decode_aarch64;
use trust_machine_sem::{Aarch64Semantics, MachineState, Semantics};

/// Weyl multiplier: odd, so `i ↦ i·K mod 2^32` is a PERMUTATION of the whole
/// encoding space. Taking the first N of it is an unbiased sample that — unlike
/// a fixed stride — cannot align with the bitfield structure of the encoding.
const WEYL: u32 = 2_654_435_761;

/// `--offset N` shifts the sample's INDEX window, so `--sample C --offset C`
/// is a population DISJOINT from `--sample C`. Re-running a harness on the
/// same words it was tuned against measures reproducibility, not exposure;
/// a fresh population is what tests whether the answer was specific to the
/// sample. `--full` ignores this — it already contains every window.
const CHUNK: usize = 2_000_000;

#[derive(Default, Clone)]
struct Tally {
    counts: [u64; OUT_N],
}

struct Shared {
    by_fn: HashMap<&'static str, Tally>,
    by_fn_op: HashMap<(&'static str, String), Tally>,
    total: Tally,
    candidates: u64,
    scanned: u64,
    violations: Vec<u32>,
    done_words: u64,
    /// Words whose actual opcode is not in the attributed leaf's producible
    /// set. The dispatch mirror in `attribute.rs` can drift from the decoder it
    /// mirrors; if it has, the per-decoder-function ranking of violations is
    /// wrong, and that must be reported rather than silently believed.
    attribution_errors: u64,
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let flag = |name: &str| -> Option<String> {
        args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).cloned()
    };
    let workers: usize = flag("--workers").and_then(|s| s.parse().ok()).unwrap_or(12);
    let offset: u64 = flag("--offset").and_then(|s| s.parse().ok()).unwrap_or(0);
    let work =
        std::path::PathBuf::from(flag("--workdir").unwrap_or_else(|| "/tmp/natinv".to_string()));
    let out_prefix = flag("--out").unwrap_or_else(|| "/tmp/natinv/run".to_string());
    std::fs::create_dir_all(&work).expect("mkdir workdir");
    if let Some(p) = std::path::Path::new(&out_prefix).parent() {
        std::fs::create_dir_all(p).ok();
    }

    // --- what to scan ---
    enum Plan {
        Full,
        Sample(u64),
        Words(Vec<u32>),
    }
    let plan = if args.iter().any(|a| a == "--full") {
        Plan::Full
    } else if let Some(n) = flag("--sample") {
        Plan::Sample(n.parse().expect("--sample COUNT"))
    } else if let Some(f) = flag("--words") {
        let t = std::fs::read_to_string(&f).expect("read words file");
        Plan::Words(
            t.lines()
                .map(str::trim)
                .filter(|l| !l.is_empty() && !l.starts_with('#'))
                .filter_map(|l| u32::from_str_radix(l.split_whitespace().next().unwrap_or(l), 16).ok())
                .collect(),
        )
    } else {
        eprintln!("usage: natinv --full | --sample COUNT | --words FILE  [--workers N] [--workdir D] [--out PREFIX]");
        std::process::exit(2);
    };

    let total_words: u64 = match &plan {
        Plan::Full => 1u64 << 32,
        Plan::Sample(n) => *n,
        Plan::Words(v) => v.len() as u64,
    };
    // NON-VACUITY. Every word that would violate this invariant has been fixed,
    // so the sweep can no longer produce a violation from a real population —
    // which means "0 violations" and "the violation path is broken" print
    // exactly the same thing. This flag forces a known-bad word list through
    // the antecedent so the sweep must report it. See the NON-VACUITY section
    // of the module header, and `run.sh`, which requires it to fire.
    let force = args.iter().any(|a| a == "--force-candidates");
    if force && !matches!(&plan, Plan::Words(_)) {
        eprintln!("--force-candidates is only meaningful with --words");
        std::process::exit(2);
    }
    let plan = Arc::new(plan);

    println!("== NATIVE INVARIANT SWEEP ==");
    println!("antecedent : decode_aarch64(W).is_ok() AND Aarch64Semantics::effects(W).is_ok()");
    println!("consequent : W does not fault when executed natively");
    println!("population : {total_words} words, {workers} workers, index offset {offset}");
    println!("executor   : {}", natexec_path());
    if force {
        println!();
        println!("!! --force-candidates: the antecedent is BYPASSED. This is a non-vacuity");
        println!("!! probe, and violations here are the EXPECTED result — zero of them means");
        println!("!! the violation path is broken, not that the invariant holds.");
    }
    println!();

    let shared = Arc::new(Mutex::new(Shared {
        by_fn: HashMap::new(),
        by_fn_op: HashMap::new(),
        total: Tally::default(),
        candidates: 0,
        scanned: 0,
        violations: Vec::new(),
        done_words: 0,
        attribution_errors: 0,
    }));

    let t0 = std::time::Instant::now();
    let mut handles = Vec::new();
    for w in 0..workers {
        let shared = Arc::clone(&shared);
        let work = work.clone();
        let plan = Arc::clone(&plan);
        handles.push(std::thread::spawn(move || {
            let st = MachineState::symbolic();
            let mut buf: Vec<u32> = Vec::with_capacity(CHUNK);
            let mut chunk_id = 0usize;
            let mut local_scanned = 0u64;

            // Each worker owns a contiguous slice of the INDEX space; the Weyl
            // permutation (or identity, for --full) maps index -> word.
            let per = total_words / workers as u64;
            let lo = per * w as u64;
            let hi = if w + 1 == workers { total_words } else { per * (w as u64 + 1) };

            let flush = |buf: &mut Vec<u32>, chunk_id: &mut usize, scanned: &mut u64| {
                let outcomes = run_chunk(buf, &work, &format!("{w}_{chunk_id}"));
                *chunk_id += 1;
                let mut s = shared.lock().expect("lock");
                for (word, &oc) in buf.iter().zip(outcomes.iter()) {
                    let oc = oc as usize;
                    s.total.counts[oc] += 1;
                    let f = decoder_fn(*word);
                    s.by_fn.entry(f).or_default().counts[oc] += 1;
                    if let Ok(i) = decode_aarch64(&word.to_le_bytes(), 0x1000) {
                        if !producible(f).contains(&i.opcode) {
                            s.attribution_errors += 1;
                        }
                        let op = format!("{:?}", i.opcode);
                        s.by_fn_op.entry((f, op)).or_default().counts[oc] += 1;
                    }
                    if oc == OUT_SIGILL {
                        s.violations.push(*word);
                    }
                }
                s.candidates += buf.len() as u64;
                s.scanned += *scanned;
                s.done_words += *scanned;
                let done = s.done_words;
                let viol = s.violations.len();
                drop(s);
                *scanned = 0;
                if done % (200 * CHUNK as u64) < CHUNK as u64 {
                    eprintln!(
                        "  .. scanned {done} / {total_words}  violations so far {viol}"
                    );
                }
                buf.clear();
            };

            for idx in lo..hi {
                let word: u32 = match &*plan {
                    Plan::Full => idx as u32,
                    Plan::Sample(_) => (idx.wrapping_add(offset) as u32).wrapping_mul(WEYL),
                    Plan::Words(v) => v[idx as usize],
                };
                local_scanned += 1;
                let admitted = force
                    || decode_aarch64(&word.to_le_bytes(), 0x1000)
                        .is_ok_and(|i| Aarch64Semantics.effects(&st, &i).is_ok());
                if admitted {
                    buf.push(word);
                    if buf.len() >= CHUNK {
                        flush(&mut buf, &mut chunk_id, &mut local_scanned);
                    }
                }
            }
            flush(&mut buf, &mut chunk_id, &mut local_scanned);
        }));
    }
    for h in handles {
        h.join().expect("worker");
    }
    let elapsed = t0.elapsed();

    let mut s = shared.lock().expect("lock");
    s.violations.sort_unstable();

    // ---------- report ----------
    let mut rep = String::new();
    macro_rules! p {
        ($($a:tt)*) => {{ let l = format!($($a)*); println!("{l}"); rep.push_str(&l); rep.push('\n'); }};
    }

    p!("scanned    : {} words in {:.1}s", s.scanned, elapsed.as_secs_f64());
    p!(
        "candidates : {} decode AND model ({:.2}% of scanned)",
        s.candidates,
        100.0 * s.candidates as f64 / s.scanned.max(1) as f64
    );
    p!("attribution: {} words whose opcode is outside the attributed decoder leaf{}",
        s.attribution_errors,
        if s.attribution_errors == 0 { " (mirror agrees with the decoder)" } else { " — RANKING BELOW IS SUSPECT" });
    p!("");
    p!("-- native outcome over the candidate set --");
    for i in 0..OUT_N {
        if s.total.counts[i] > 0 {
            p!(
                "{:>10}  {:>12}  {:>7.4}%",
                OUT_NAMES[i],
                s.total.counts[i],
                100.0 * s.total.counts[i] as f64 / s.candidates.max(1) as f64
            );
        }
    }
    p!("");
    let v = s.total.counts[OUT_SIGILL];
    p!("=========================================================");
    p!("VIOLATIONS (candidate word, SIGILL at the word): {v}");
    p!("=========================================================");
    p!("");

    if v > 0 {
        p!("-- violations by decoder function --");
        let mut rows: Vec<_> =
            s.by_fn.iter().map(|(f, t)| (*f, t.counts[OUT_SIGILL], t.counts.iter().sum::<u64>())).collect();
        rows.sort_by_key(|(_, sig, _)| std::cmp::Reverse(*sig));
        for (f, sig, tot) in rows.iter().filter(|(_, s, _)| *s > 0) {
            p!("{f:<52} {sig:>12} / {tot:<12} ({:>6.2}%)", 100.0 * *sig as f64 / *tot as f64);
        }
        p!("");
        p!("-- violations by decoder function x opcode --");
        let mut rows: Vec<_> = s
            .by_fn_op
            .iter()
            .map(|((f, o), t)| (*f, o.clone(), t.counts[OUT_SIGILL], t.counts.iter().sum::<u64>()))
            .collect();
        rows.sort_by_key(|(_, _, sig, _)| std::cmp::Reverse(*sig));
        for (f, o, sig, tot) in rows.iter().filter(|(_, _, s, _)| *s > 0).take(60) {
            p!("{f:<44} {o:<12} {sig:>12} / {tot:<12} ({:>6.2}%)", 100.0 * *sig as f64 / *tot as f64);
        }
    }

    // Full violation word list, for family analysis and for re-checking.
    let vf = format!("{out_prefix}.violations.bin");
    let mut f = std::io::BufWriter::new(std::fs::File::create(&vf).expect("create violations"));
    for w in &s.violations {
        f.write_all(&w.to_le_bytes()).expect("write");
    }
    f.flush().expect("flush");
    p!("");
    p!("violation words : {vf} ({} words)", s.violations.len());

    // Machine-readable baseline.
    let bl = format!("{out_prefix}.baseline.json");
    let mut j = String::from("{\n");
    // COST, RECORDED. "0 violations over all 2^32 words" is only re-derivable
    // by someone who knows what re-deriving it costs; a result whose price is
    // unstated gets cited instead of reproduced.
    j.push_str(&format!("  \"mode\": \"{}\",\n", if force { "force-candidates" } else { "gated" }));
    j.push_str(&format!("  \"elapsed_s\": {:.1},\n", elapsed.as_secs_f64()));
    j.push_str(&format!("  \"workers\": {workers},\n"));
    j.push_str(&format!("  \"scanned\": {},\n", s.scanned));
    j.push_str(&format!("  \"candidates\": {},\n", s.candidates));
    j.push_str(&format!("  \"violations\": {},\n", s.total.counts[OUT_SIGILL]));
    j.push_str(&format!("  \"attribution_errors\": {},\n", s.attribution_errors));
    j.push_str("  \"outcomes\": {\n");
    let mut first = true;
    for i in 0..OUT_N {
        if s.total.counts[i] > 0 {
            if !first {
                j.push_str(",\n");
            }
            first = false;
            j.push_str(&format!("    \"{}\": {}", OUT_NAMES[i], s.total.counts[i]));
        }
    }
    j.push_str("\n  },\n");
    j.push_str("  \"violations_by_decoder_fn\": {\n");
    let mut rows: Vec<_> =
        s.by_fn.iter().map(|(f, t)| (*f, t.counts[OUT_SIGILL])).filter(|(_, n)| *n > 0).collect();
    rows.sort();
    for (i, (f, n)) in rows.iter().enumerate() {
        j.push_str(&format!("    \"{f}\": {n}{}\n", if i + 1 < rows.len() { "," } else { "" }));
    }
    j.push_str("  }\n}\n");
    std::fs::write(&bl, &j).expect("write baseline");
    p!("baseline        : {bl}");

    std::fs::write(format!("{out_prefix}.report.txt"), &rep).expect("write report");
}
