//! THE NATIVE SEMANTIC DIFFERENTIAL — does the word DO what the model says?
//!
//! `native-invariant` beside this one checks that a word the gate accepts is a
//! word the CPU will RUN. That is necessary and it is not sufficient. The
//! output gate does not merely require that a word executes: it re-derives the
//! object's meaning from `Aarch64Semantics::effects` and proves a theorem about
//! THAT. If the effect list is wrong — a swapped operand, a missed flag, a
//! wrong extension, a writeback that does not happen — the word runs fine and
//! the gate proves a theorem about an instruction that does not exist. That is
//! a false Proven, and no fault-based oracle can see it.
//!
//! THE CHECK:
//!
//!     for every word W and starting state S:
//!         decode(W) is Ok  ∧  effects(W) is Ok  ∧  W executes natively from S
//!     ⟹ replaying effects(W) on S agrees with the hardware on
//!         x0..x30, sp, NZCV, the next pc, and every byte of memory.
//!
//! The consequent is compared over the WHOLE architectural scalar state that
//! the model claims to describe — not a projection of it. Comparing only the
//! registers an instruction is "supposed" to write would assume the answer.
//!
//! Words the harness cannot speak about are counted and named, never folded
//! into agreement: a load that faulted, an effect list outside the concrete
//! replayer, a memory write beyond the checked window. UNCHECKED is reported as
//! its own column.
//!
//! # BLIND SPOTS — the authoritative inventory
//!
//! Four soundness families were found one at a time, each after the previous
//! was declared closed, and the reason the class survived four times is that
//! nobody could say what the checks did not cover. An undocumented blind spot
//! is indistinguishable from coverage. So this section is normative: **if a
//! limitation is not listed here, the harness is claiming to cover it.** Adding
//! an exclusion means adding it here and giving it a counter in `Counts`.
//!
//! ## A. Outside the antecedent — never candidates, by construction
//!
//! * **Privileged and system instructions.** `SVC`, `HVC`, `SMC`, `BRK`, `HLT`,
//!   `MRS`, `MSR`, `WFE`, `WFI` are refused by `Aarch64Semantics` with a
//!   proof-blocker error, so they never enter the candidate set and this
//!   harness says nothing about them. That is the correct disposition — the
//!   gate cannot reach Proven on them either — but it is a gap in COVERAGE, not
//!   a proof of correctness. The refusal is asserted over the actual population
//!   at startup (see the containment check in `main`) rather than assumed,
//!   because it is also the property that makes running arbitrary words safe.
//! * **Exception-generating and exception-returning forms** (`ERET`, `DCPS`,
//!   `SMSTART`) for the same reason.
//!
//! ## B. Inside the antecedent, outside this oracle — counted, never assumed
//!
//! Each of these is a `Counts` field printed on every run. They are excluded
//! from `compared`, so lost coverage shows up as a smaller denominator instead
//! of hiding inside an agreement count.
//!
//! * `unchecked_native` — the word faulted natively or timed out. **Memory
//!   faults are a blind spot of this harness, not of the program**: whether a
//!   load from an unmapped address traps is exactly what `native-invariant`
//!   checks; here a fault means there is no post-state to compare.
//! * `unchecked_model` — the effect list is outside the concrete replayer.
//!   Broken out by reason in the "why words could not be replayed" table. The
//!   standing resident is the exclusive-atomic pair (`LDXR`/`STXR` reserve a
//!   monitor this state does not have). **Exclusive-monitor semantics and
//!   memory ordering are therefore untested here**, and cannot be tested by a
//!   single-threaded oracle at all.
//!
//!   TWO FORMER RESIDENTS ARE GONE, and how they left is the point. FP
//!   `Formula` nodes were refused outright, so `FADD`/`FSUB`/`FMUL`/`FDIV` —
//!   3,000 words of each in the full-tier population — were `unchecked`, and
//!   `Effect::Branch`/`Call`/`Return` were refused, so `B`/`BL`/`BLR`/`BR`
//!   were too. All eight opcodes were ACCEPTED by the model throughout, which
//!   means the output gate could reach Proven on them while nothing compared
//!   them: changing `sem_bl`'s return address from `pc+4` to `pc+8` was
//!   MEASURED to pass the full standing gate. The lesson generalises and is now
//!   printed on every run — see the accepted-but-never-compared report below.
//! * `unchecked_mem` — a predicted access fell outside the shared scratch
//!   window, or more than `NDIFF_MAX` 8-byte words changed. The two sides do
//!   not share a memory image outside scratch, so comparing there would
//!   manufacture a disagreement out of the harness's own layout.
//! * `unchecked_x18` — harness bug 3 (below).
//! * `unchecked_reentry` — harness bug 4 (below).
//! * `killed` — the candidate killed the executor process. The word is
//!   attributed and never allowed to shift later records.
//!
//! ## C. Architectural state this harness does not model or compare
//!
//! Nothing here is counted, because there is no per-word event to count — these
//! are whole dimensions the comparison does not have.
//!
//! * **`FPCR` / `FPSR`.** The context block loads x0-x30, sp, NZCV and V0-V31,
//!   and nothing else. Rounding mode, flush-to-zero, and the cumulative IEEE
//!   exception bits are whatever the process inherited, identical on both
//!   sides but never compared. An instruction whose only wrong effect is a
//!   wrong FPSR bit is invisible. (Scalar FP is separately known-diverging —
//!   see `baseline.json`.)
//! * **Feature-dependent legality.** The host is one Apple aarch64 CPU. Words
//!   that are legal only under a feature it lacks (SVE/SME, and any `FEAT_*`
//!   absent here) fault; words legal only *because* of a feature it has do not
//!   fault. A verdict from this harness is a verdict about THIS microarchitecture,
//!   and a word that agrees here can still be illegal on another aarch64 part.
//! * **System state.** EL0 only, one MMU configuration, one `SCTLR`, PAC and
//!   MTE off, one page-table layout. Anything whose behaviour depends on
//!   privilege, translation regime, or a system register is out of reach.
//! * **Anything that is not architectural post-state.** Timing, caches, TLBs,
//!   the exclusive monitor, speculation. A model that is right about the state
//!   and wrong about the ordering passes here.
//! * **`x18`** in both directions — harness bug 3.
//! * **IEEE arithmetic itself.** The concrete replayer evaluates the model's
//!   `FpToIeeeBv(Fp*(RNE, FpFromBits, FpFromBits))` shape with Rust's `f32`/
//!   `f64` operators, which compile to the HOST's `fadd`/`fsub`/`fmul`/`fdiv`.
//!   So `FADD`/`FSUB`/`FMUL`/`FDIV` agreeing here is not an independent check
//!   of the arithmetic and cannot be. It IS a check of everything around it:
//!   which file each operand comes from, which lane and how wide, whether the
//!   destination's upper lanes are zeroed, whether the register written is the
//!   one named, and whether any flag or memory effect was invented or lost —
//!   the class every bug in this program has actually belonged to. A mutated
//!   `FSUB` computing an addition is caught (`Fsub=319`, fast tier).
//!
//! ## D. The four harness bugs, each now a COUNTED exclusion or a guard
//!
//! Every one of these produced a confident wrong number before it was found.
//! They are listed so that the next one is looked for in the same places.
//!
//! 1. **NZCV written at bit 0 instead of PSTATE 31:28.** `MSR NZCV, Xt` takes
//!    the flags from bits 31:28 and ignores the rest, so a 0..15 nibble set the
//!    flags to zero and every flag-reading instruction was reported as a model
//!    disagreement — the harness's own bug wearing the exact costume of the
//!    finding it exists to make. FIXED, and now guarded: `Profile::to_ctx_bytes`
//!    shifts by 28 with the reason written beside it.
//! 2. **A fault outside a candidate `siglongjmp`-ing into an uninitialized
//!    buffer.** Wedged a worker for 29 minutes producing no output and no
//!    error — the worst failure mode there is, because a harness that produces
//!    nothing is often read as a harness that found nothing. FIXED in
//!    `natsem.c`; a fault with no live candidate is now fatal and loud.
//! 3. **`x18` is the Darwin platform register** and the OS resets it on some
//!    exception returns. Measured, not inferred (see the comment in `compare`).
//!    A word that WRITES x18 can never be compared; a word that READS it is
//!    compared only when the record shows x18 survived, because excluding every
//!    reader unconditionally costs 24,066 comparisons and excluding none of
//!    them made `ands x4,x18,#0x1fc000001fc0` flake between runs. Counted as
//!    `unchecked_x18`.
//! 4. **A backward branch re-entering the slot prologue.** The prologue reloads
//!    the whole register file, so the record is the candidate's effect plus a
//!    second prologue pass. Filtering on the ESCAPED outcome is NOT enough —
//!    the re-entered prologue falls through to the epilogue and the record
//!    arrives labelled EXECUTED. Excluded STRUCTURALLY from the decoded target
//!    (`reenters_slot`), counted as `unchecked_reentry`.
//!
//! A fifth was found while extending the V file: harness bug 3's READ
//! direction, missing because only the write direction had been excluded. It is
//! folded into `unchecked_x18` above rather than given its own number, since it
//! is the same register and the same cause.
//!
//! 5. **A NONDETERMINISTIC EXCLUSION HIDING INSIDE A DETERMINISTIC-LOOKING
//!    DENOMINATOR.** `TIMEOUT` was counted in `unchecked_native` beside genuine
//!    faults. A fault is a function of the word and the starting state; a
//!    timeout is a function of what else the HOST was doing inside the alarm
//!    window. So the gate's coverage floor — advertised as exactly
//!    reproducible — silently depended on machine load, and a fast-tier run
//!    during a stage-1 rustc rebuild failed it: coverage 47300 against a floor
//!    of 47320 recorded on an idle host, with the twenty missing words all
//!    timeouts and a `Fcvtzu` mismatch count one lower to match. FIXED:
//!    `unchecked_timeout` is its own counter, its own ledger line, and part of
//!    the coverage identity, with a separate ceiling so a genuinely hanging
//!    candidate class still fails loudly. The general shape — a bucket whose
//!    size depends on the environment, summed with buckets that do not — is
//!    worth looking for wherever a count is called reproducible.
//!
//! ## A0. ARCHITECTURE — this oracle is AArch64 ONLY, and x86-64 has none
//!
//! Listed FIRST because it is the largest exclusion in this file and the one a
//! reader is least likely to infer: every antecedent above says
//! `decode_aarch64` and `Aarch64Semantics`. There is no x86-64 differential
//! oracle anywhere in `crates/trust-disasm/harness/`. `trust_disasm::
//! decode_x86_64` and `trust_machine_sem::X86_64Semantics` are checked by unit
//! tests only — that is, against expectations a human wrote down, never against
//! the hardware.
//!
//! This section exists because of the rule stated at the top of the inventory:
//! *if a limitation is not listed here, the harness is claiming to cover it.*
//! The x86-64 gap was unlisted, so this file was making exactly that claim.
//!
//! WHAT IT COST, measured 2026-08-18 (see
//! `docs/audits/2026-08-18-x86-address-decoding.md` and
//! `docs/audits/2026-08-18-binary-stack-audit.md`): sixteen defects, of which
//! FIVE were wrong ADDRESSES coexisting in one file — RIP-relative short by
//! `insn.size`, absolute `[disp32]` computed as PC-relative, a dropped
//! displacement, a dropped `R12` index, and a fabricated `RBP` base — plus
//! `mov ah` modelled as a STACK POINTER write, `movb` as an eight-byte store,
//! and `jp`/`jnp` as unconditional branches. Every one of them is a divergence
//! this oracle's consequent would have caught on the first word: they compare
//! registers, flags and memory bytes against the CPU. None of them faults, so
//! `native-invariant` beside this file could not see them either.
//!
//! WHY IT DOES NOT SIMPLY GENERALISE. The `--full` mode here is exhaustive over
//! a 2^32 space because AArch64 words are fixed-width. x86-64 instructions are
//! 1-15 bytes, so there is no space to enumerate and an x86-64 oracle needs a
//! generator or corpus instead — a different selector, though the same
//! consequent (compare the whole architectural post-state, count what you
//! cannot speak about, never fold it into agreement) transfers unchanged.
//!
//! Until that exists, no x86-64 count anywhere may be read as differential
//! evidence.
//!
//! ## E. THE SET THIS ORACLE NEVER SPOKE ABOUT — now printed, must stay empty
//!
//! `N opcodes compared` is a number about what the CONCRETE REPLAYER can
//! execute, and it is easy to read as a number about what the GATE can reach
//! Proven on. They are different sets, and the difference was eight opcodes.
//! Every run now prints the opcodes the model ACCEPTS and this oracle never
//! compared, so the gap is a line in the report rather than a subtraction
//! nobody performs.
//!
//! # NON-VACUITY
//!
//! `--mutate NAME` runs the differential against a deliberately WRONG model
//! (see `mutate.rs`). The gate runs the whole battery and requires every
//! mutation to be caught, so a harness that has quietly stopped comparing
//! something fails before any sweep number is believed.
//!
//! THE BATTERY IS A FLOOR, NOT A CEILING, and it is a lower floor than it
//! looks: every mutation rewrites a whole effect CLASS, so one word of the
//! right kind catches it, whereas all three real divergences were NARROW and
//! DATA-DEPENDENT and needed a specific word to be in the population at all.
//! Both properties have been measured, separately — see the note at the top of
//! `mutate.rs` for the three source-level defects that were injected into the
//! shipping model and each failed the fast tier.
//!
//! # STARTING STATES
//!
//! `--profile-set default` is the shipping three and is what every baseline
//! number is measured over; `compared` is (words x profiles), so adding a
//! profile to the default set would inflate every recorded count without
//! checking a single new word. `adversarial` (corner values, `sp` at the
//! scratch edge and below the 64-bit wrap), `flags16` (one profile per NZCV
//! setting — the whole domain of a condition code) and `fp` (IEEE specials in
//! the V file) are for hunting.
//!
//! usage:
//!   natsem-diff --sample N [--offset K]
//!   natsem-diff --stratify N            per-OPCODE cap; reaches rare forms
//!                                       that uniform sampling never sees
//!   natsem-diff --words FILE            recheck a specific word list
//!   natsem-diff ... --mutate NAME       run against a deliberately wrong model
//!   natsem-diff ... --out PREFIX        write PREFIX.result.json

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

mod ctx;
mod model;
mod mutate;
mod natsem;

use ctx::{
    Profile, SCRATCH_BASE, profile_corners, profile_extremes, profile_fp, profile_fp_rotated,
    profile_mixed, profile_pointers, profile_spedge, profile_spwrap, profile_values,
    profiles_flags16,
};
use model::{Skip, predict};
use mutate::Mutation;
use natsem::{
    OUT_ESCAPED, OUT_EXECUTED, OUT_KILLED, OUT_SIGILL, OUT_TIMEOUT, Record, run_chunk, slot_pc,
};
use trust_disasm::operand::Operand;
use trust_disasm::{Opcode, decode_aarch64};
use trust_machine_sem::{Aarch64Semantics, MachineState, Semantics};

/// Odd multiplier: `i ↦ i·K mod 2^32` is a permutation of the encoding space,
/// so a prefix of it is an unbiased sample that cannot align with the bitfield
/// structure the way a fixed stride would.
const WEYL: u32 = 2_654_435_761;
const CHUNK: usize = 100_000;

/// How many logical slices the POPULATION scan is cut into.
///
/// DELIBERATELY NOT `--workers`. Both selectors used to shard by thread count,
/// which made the chosen word set a function of how many cores the operator
/// gave the run: `--stratify 3000 --workers 8` and `--workers 4` produced
/// DIFFERENT populations, so a recorded baseline could not be reproduced by
/// anyone who typed a different number. A gate whose population moves with the
/// machine it runs on is not a gate. `--workers` now controls execution
/// parallelism only, and the population is a pure function of the selector
/// arguments and this constant — checkable through the digest printed below.
const SHARDS: u64 = 8;

/// FNV-1a over the population, so "the same words were checked" is verifiable
/// rather than asserted. Recorded in the baseline; a changed digest means the
/// comparison is against a different set and the counts are not comparable.
fn population_digest(words: &[u32]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for w in words {
        for b in w.to_le_bytes() {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    h
}

fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

#[derive(Default)]
struct Counts {
    compared: u64,
    agreed: u64,
    mismatched: u64,
    unchecked_native: u64,
    /// THE ONE EXCLUSION THAT IS NOT A FUNCTION OF THE WORD.
    ///
    /// Every other bucket is decided by the candidate and the starting state:
    /// a word that faults, faults again. A TIMEOUT is decided by the HOST — how
    /// many other processes wanted the core during that alarm window — so it
    /// moves between runs on a loaded machine and does not move on an idle one.
    /// Counted separately for exactly that reason: folded into
    /// `unchecked_native` it made the gate's coverage floor depend on what else
    /// was running, and a gate that fails because someone started a build is a
    /// gate people learn to re-run rather than read. MEASURED: a fast-tier run
    /// during a stage-1 rustc rebuild reported coverage 47300 against a floor of
    /// 47320 recorded on an idle host — 20 words, all of them timeouts.
    unchecked_timeout: u64,
    unchecked_model: u64,
    unchecked_mem: u64,
    unchecked_x18: u64,
    unchecked_reentry: u64,
    violations_sigill: u64,
    killed: u64,
}

#[derive(Debug, Clone)]
struct Mismatch {
    word: u32,
    profile: &'static str,
    opcode: String,
    kind: String,
    detail: String,
}

fn nzcv_str(v: u8) -> String {
    format!(
        "{}{}{}{}",
        if v & 8 != 0 { 'N' } else { 'n' },
        if v & 4 != 0 { 'Z' } else { 'z' },
        if v & 2 != 0 { 'C' } else { 'c' },
        if v & 1 != 0 { 'V' } else { 'v' }
    )
}

/// Compare one predicted post-state against one observed post-state.
///
/// Returns `Ok(())` on agreement, `Err((kind, detail))` on the FIRST
/// disagreement — first in a fixed order, so the same mismatch always reports
/// the same way and families group cleanly.
fn compare(p: &model::Predicted, r: &Record) -> Result<(), (String, String)> {
    for i in 0..31 {
        // x18 IS NOT THIS HARNESS'S TO HOLD. It is the Darwin platform
        // register, and the OS resets it on some exception returns. MEASURED,
        // with x18 seeded to 0xdeadbeefcafef00d and three candidates:
        //
        //   d503201f  nop                  EXECUTED  x18 = 0xdeadbeefcafef00d
        //   14000002  b .+8                ESCAPED   x18 = 0xdeadbeefcafef00d
        //   340327bf  cbz wzr, +0x6514     ESCAPED   x18 = 0
        //
        // Neither `b` nor `cbz` writes x18, and a neighbouring register (x17)
        // was intact in all three — so the zero is the platform's, not the
        // candidate's. Comparing it would report the OS as a model bug.
        //
        // This is a REAL blind spot, not a free pass: a word whose modelled
        // effect writes x18 is counted as `unchecked (writes x18)` and excluded
        // from `compared`, so the coverage lost is on the report rather than
        // hidden inside an agreement count.
        if i == 18 {
            continue;
        }
        if p.gpr[i] != r.gpr[i] {
            return Err((
                format!("x{i}"),
                format!("model x{i}={:#018x} native x{i}={:#018x}", p.gpr[i], r.gpr[i]),
            ));
        }
    }
    if p.sp != r.sp {
        return Err(("sp".into(), format!("model sp={:#018x} native sp={:#018x}", p.sp, r.sp)));
    }
    // THE SIMD/FP FILE. Compared over the WHOLE file, like the GPRs — comparing
    // only the register an instruction is "supposed" to write assumes the
    // answer, and the bug this file was added to catch was precisely an
    // instruction writing the wrong register.
    for i in 0..32 {
        if p.fpr[i] != r.fpr[i] {
            return Err((
                format!("v{i}"),
                format!("model v{i}={:#034x} native v{i}={:#034x}", p.fpr[i], r.fpr[i]),
            ));
        }
    }
    if p.nzcv != r.nzcv {
        return Err((
            "nzcv".into(),
            format!("model {} native {}", nzcv_str(p.nzcv), nzcv_str(r.nzcv)),
        ));
    }
    if p.pc != r.pc {
        return Err(("pc".into(), format!("model pc={:#x} native pc={:#x}", p.pc, r.pc)));
    }
    // Memory. Both sides are lists of (aligned address, whole 8-byte value)
    // that DIFFER from the shared pattern, so equality of the lists is equality
    // of the memory images over the window.
    let mut pm = p.mem.clone();
    let mut rm = r.mem.clone();
    pm.sort_unstable();
    rm.sort_unstable();
    if pm != rm {
        let fmt = |v: &Vec<(u64, u64)>| {
            if v.is_empty() {
                "(no write)".to_string()
            } else {
                v.iter().map(|(a, x)| format!("[{a:#x}]={x:#018x}")).collect::<Vec<_>>().join(" ")
            }
        };
        return Err(("mem".into(), format!("model {} native {}", fmt(&pm), fmt(&rm))));
    }
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let flag = |name: &str| -> Option<String> {
        args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).cloned()
    };
    // THE BATTERY IS DEFINED IN CODE, AND THE GATE ASKS THE CODE.
    //
    // `run.sh` iterates over THIS list, not over the keys of baseline.json. If
    // the script read the baseline instead, a mutation added to `mutate.rs`
    // without a matching baseline entry would simply never run — a check that
    // silently matches nothing, which is the same failure mode as a test filter
    // that selects zero tests, and the same failure mode this whole gate exists
    // to prevent. The script cross-checks the two and fails if they disagree.
    if args.iter().any(|a| a == "--list-mutations") {
        for m in mutate::BATTERY {
            println!("{}", m.name());
        }
        return;
    }

    let workers: usize = flag("--workers").and_then(|s| s.parse().ok()).unwrap_or(8);
    let work =
        std::path::PathBuf::from(flag("--workdir").unwrap_or_else(|| "/tmp/natsem".to_string()));
    std::fs::create_dir_all(&work).expect("mkdir workdir");
    let seed: u64 = flag("--seed").and_then(|s| s.parse().ok()).unwrap_or(0xC0FFEE);
    let out_prefix = flag("--out");
    let mutation = match flag("--mutate") {
        None => Mutation::None,
        Some(name) => match Mutation::from_name(&name) {
            Some(m) => m,
            None => {
                eprintln!(
                    "unknown mutation {name:?}; known: none, {}",
                    mutate::BATTERY.map(Mutation::name).join(", ")
                );
                std::process::exit(2);
            }
        },
    };

    let (pc, slot_lo) = slot_pc();
    // THE PROFILE SET IS A DIMENSION OF THE POPULATION, and it is versioned
    // exactly like the word list. `compared` is (words x profiles), so the
    // gate's coverage floors are counts of BOTH — adding a profile to the
    // DEFAULT set would inflate every recorded number without checking a single
    // new word, and removing one would look like a model regression. So the
    // default is frozen at the shipping three and anything else must be named.
    let profile_set = flag("--profile-set").unwrap_or_else(|| "default".to_string());
    let profiles: Vec<Profile> = match profile_set.as_str() {
        "default" => vec![profile_pointers(seed), profile_mixed(seed), profile_values(seed)],
        // Boundary inputs and the flag settings the default three never reach.
        "adversarial" => vec![
            profile_corners(seed),
            profile_extremes(seed),
            profile_spedge(seed),
            profile_spwrap(seed),
        ],
        // All sixteen NZCV settings: the whole domain of a condition code.
        "flags16" => profiles_flags16(seed),
        // IEEE special values in the SIMD/FP file.
        "fp" => vec![profile_fp(seed), profile_fp_rotated(seed), profile_pointers(seed)],
        other => {
            eprintln!("unknown --profile-set {other:?}; known: default, adversarial, flags16, fp");
            std::process::exit(2);
        }
    };

    // ---- choose the population ----
    //
    // Timed separately from the sweep, because for the smaller tiers the SCAN
    // dominates the wall clock and a cost figure that hid it would understate
    // what the gate actually charges a developer.
    let t_scan = std::time::Instant::now();
    let words: Vec<u32> = if let Some(f) = flag("--words") {
        let t = std::fs::read_to_string(&f).expect("read words file");
        t.lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .filter_map(|l| {
                u32::from_str_radix(l.split_whitespace().next().unwrap_or(l), 16).ok()
            })
            .collect()
    } else if let Some(n) = flag("--stratify") {
        let cap: usize = n.parse().expect("--stratify N");
        stratified(cap, pc)
    } else {
        let n: u64 = flag("--sample").expect("--sample N | --stratify N | --words F").parse().expect("N");
        let off: u64 = flag("--offset").and_then(|s| s.parse().ok()).unwrap_or(0);
        candidates(n, off, pc)
    };
    let scan_s = t_scan.elapsed().as_secs_f64();

    // FREEZING A POPULATION. The stratified scan costs ~10s regardless of the
    // cap — it walks 320M indices to find the rare opcodes — so a smaller cap
    // buys almost no time and a "fast tier" defined only by its cap would be a
    // weaker check for no gain. Instead the fast tier's population is dumped
    // once and COMMITTED, and replayed with `--words`. That makes it free to
    // run, byte-identical on every host, and reviewable as a diff.
    //
    // It also splits the two tiers along the right seam: the frozen population
    // detects REGRESSIONS in a fixed set of words, and the rescanning full tier
    // DISCOVERS forms that a decoder or semantics change has newly admitted.
    let dump_population = flag("--dump-population");

    // CONTAINMENT, CHECKED RATHER THAN ASSUMED.
    //
    // `native-invariant` pins x16 to a non-syscall value so that a candidate
    // which happens to be `svc` cannot reach a real system call. This harness
    // CANNOT do that: x16 carries a profile value, because a register excluded
    // from the starting state is a register the differential cannot check.
    //
    // What makes that safe is the antecedent itself — `Aarch64Semantics`
    // returns a proof-blocker error for SVC/HVC/SMC/BRK/HLT/MRS/MSR/WFE/WFI
    // (`aarch64/mod.rs`), so none of them is ever a candidate. That is a real
    // guarantee and it is also exactly the kind of guarantee that quietly stops
    // holding. So it is asserted here, over the actual population, rather than
    // believed: being protected by ordering instead of by construction is the
    // pattern this whole program exists to remove.
    for w in &words {
        if let Ok(i) = decode_aarch64(&w.to_le_bytes(), pc) {
            assert!(
                !matches!(
                    i.opcode,
                    Opcode::Svc | Opcode::Hvc | Opcode::Smc | Opcode::Brk | Opcode::Hlt
                ),
                "{w:08x} decodes as {:?} and is in the candidate set — the model no longer \
                 refuses it, so a candidate could now reach a real system call or an \
                 uncatchable trap. Fix the containment before running.",
                i.opcode
            );
        }
    }

    let digest = population_digest(&words);
    if let Some(path) = dump_population {
        let mut s = format!("# stratified population, digest {digest:#018x}, {} words\n", words.len());
        for w in &words {
            s.push_str(&format!("{w:08x}\n"));
        }
        std::fs::write(&path, s).expect("write population");
        println!("population {} words, digest {digest:#018x} -> {path}", words.len());
        return;
    }
    println!("== NATIVE SEMANTIC DIFFERENTIAL ==");
    println!("antecedent : decode ∧ effects ∧ the word executes natively");
    println!("consequent : replayed effects == hardware on x0-x30, sp, V0-V31, NZCV, pc, memory");
    println!(
        "candidates : {} words x {} profiles [{profile_set}: {}]",
        words.len(),
        profiles.len(),
        profiles.iter().map(|p| p.name).collect::<Vec<_>>().join(",")
    );
    println!("population : digest {digest:#018x}  seed {seed:#x}  (independent of --workers)");
    println!("slot pc    : {pc:#x}   (the model's PC, taken from the executor)");
    println!("executor   : {}", natsem::natsem_path());
    if mutation != Mutation::None {
        println!();
        println!("!! MUTATED MODEL: {} — {}", mutation.name(), mutation.provenance());
        println!("!! This run is a NON-VACUITY probe. Mismatches here are the EXPECTED");
        println!("!! result; zero of them means this differential has gone blind.");
    }
    println!();

    // THE POPULATION'S OPCODES, RECORDED BEFORE THE SWEEP.
    //
    // "82 opcodes compared" is a number about what this oracle COULD replay,
    // and read alone it is easily mistaken for a number about what the gate can
    // reach Proven on. Those are different sets. `Effect::Branch`, the
    // exclusive atomics and the FP `Formula` nodes are outside the CONCRETE
    // REPLAYER, not outside `Aarch64Semantics` — the output gate consumes the
    // same effect lists symbolically and can prove a theorem about every one of
    // them. So an opcode that the model ACCEPTS and this differential NEVER
    // COMPARES is a live hole with the exact shape of the bug this harness
    // exists to find, and it must be printed rather than inferred by
    // subtracting two lists in one's head.
    let mut population_ops: BTreeMap<String, u64> = BTreeMap::new();
    {
        let st = MachineState::symbolic();
        for w in &words {
            if let Ok(i) = decode_aarch64(&w.to_le_bytes(), pc) {
                if Aarch64Semantics.effects(&st, &i).is_ok() {
                    *population_ops.entry(format!("{:?}", i.opcode)).or_default() += 1;
                }
            }
        }
    }

    let counts = Arc::new(Mutex::new(Counts::default()));
    let mismatches = Arc::new(Mutex::new(Vec::<Mismatch>::new()));
    let skips = Arc::new(Mutex::new(BTreeMap::<String, u64>::new()));
    let by_opcode = Arc::new(Mutex::new(BTreeMap::<String, (u64, u64)>::new()));
    let t0 = std::time::Instant::now();

    for profile in &profiles {
        let ctx_path = work.join(format!("ctx_{}.bin", profile.name));
        std::fs::write(&ctx_path, profile.to_ctx_bytes()).expect("write ctx");

        let chunks: Vec<(usize, Vec<u32>)> =
            words.chunks(CHUNK).enumerate().map(|(i, c)| (i, c.to_vec())).collect();
        let next = Arc::new(Mutex::new(0usize));
        let mut handles = Vec::new();
        for w in 0..workers {
            let (next, chunks, counts, mismatches, skips, by_opcode) = (
                Arc::clone(&next),
                chunks.clone(),
                Arc::clone(&counts),
                Arc::clone(&mismatches),
                Arc::clone(&skips),
                Arc::clone(&by_opcode),
            );
            let work = work.clone();
            let ctx_path = ctx_path.clone();
            let profile = profile.clone();
            handles.push(std::thread::spawn(move || {
                loop {
                    let idx = {
                        let mut g = next.lock().expect("lock");
                        let i = *g;
                        if i >= chunks.len() {
                            break;
                        }
                        *g += 1;
                        i
                    };
                    let (cid, chunk) = &chunks[idx];
                    let recs = run_chunk(
                        chunk,
                        &ctx_path,
                        &work,
                        &format!("{}_{w}_{cid}", profile.name),
                        SCRATCH_BASE,
                    );
                    let mut local_mis = Vec::new();
                    let mut local_skip: BTreeMap<String, u64> = BTreeMap::new();
                    let mut local = Counts::default();
                    let mut local_op: BTreeMap<String, (u64, u64)> = BTreeMap::new();
                    for (word, rec) in chunk.iter().zip(recs.iter()) {
                        match rec.outcome {
                            OUT_SIGILL => {
                                local.violations_sigill += 1;
                                local_mis.push(Mismatch {
                                    word: *word,
                                    profile: profile.name,
                                    opcode: opcode_of(*word, pc),
                                    kind: "SIGILL".into(),
                                    detail: "the CPU refuses a word the model accepts".into(),
                                });
                                continue;
                            }
                            OUT_KILLED => {
                                local.killed += 1;
                                continue;
                            }
                            OUT_EXECUTED => {}
                            OUT_ESCAPED => {}
                            OUT_TIMEOUT => {
                                local.unchecked_timeout += 1;
                                continue;
                            }
                            _ => {
                                local.unchecked_native += 1;
                                continue;
                            }
                        }
                        // RE-ENTRY, excluded STRUCTURALLY rather than by
                        // outcome. A candidate whose PC-relative target lands
                        // inside the slot template can branch back into the
                        // prologue, which reloads x0..x30 from whatever `x30`
                        // now points at — so the record is the effect of the
                        // candidate PLUS a second pass of the prologue, and
                        // possibly of the candidate again.
                        //
                        // Filtering on the ESCAPED outcome is NOT enough, and
                        // that was measured: the re-entered prologue runs to
                        // its end and falls through to the epilogue, so the
                        // record arrives labelled EXECUTED with a completely
                        // reloaded register file. Five words survived an
                        // outcome-based filter this way (`374ffd78` targets
                        // slot_lo+8, `b62ffe99` slot_lo+44). The TARGET is
                        // known from the decode, so the exclusion does not have
                        // to depend on what happened at run time.
                        if reenters_slot(*word, pc, slot_lo) {
                            local.unchecked_reentry += 1;
                            continue;
                        }
                        let p = match predict(*word, pc, &profile, mutation) {
                            Ok(p) => p,
                            Err(skip) => {
                                local.unchecked_model += 1;
                                *local_skip.entry(skip_key(&skip)).or_default() += 1;
                                continue;
                            }
                        };
                        if p.mem_outside_window || p.mem_read_outside_window || rec.ndiff == 0xff
                        {
                            local.unchecked_mem += 1;
                            continue;
                        }
                        // x18 IS NOT THIS HARNESS'S TO HOLD (see `compare`).
                        // A word that WRITES it can never be compared on that
                        // register. A word that READS it can — but only when
                        // x18 was actually intact while the candidate ran, and
                        // the record settles that: if the observed x18 still
                        // holds the value the prologue loaded, the OS did not
                        // reset it for this candidate and the value that flowed
                        // into the result was the modeled one.
                        //
                        // MEASURED, not assumed: excluding every x18 READER
                        // unconditionally is sound but costs 24,066
                        // comparisons, and excluding none of them is what let
                        // `ands x4,x18,#0x1fc000001fc0` (f21a1a44) report
                        // `model x4=0xc80 native x4=0x0` on one sweep and agree
                        // on the next. This condition keeps the coverage and
                        // the determinism at once.
                        let x18_intact = rec.gpr[18] == profile.gpr[18];
                        if p.writes_x18 || (p.reads_x18 && !x18_intact) {
                            local.unchecked_x18 += 1;
                            continue;
                        }
                        local.compared += 1;
                        let op = opcode_of(*word, pc);
                        let e = local_op.entry(op.clone()).or_default();
                        e.0 += 1;
                        match compare(&p, rec) {
                            Ok(()) => local.agreed += 1,
                            Err((kind, detail)) => {
                                local.mismatched += 1;
                                e.1 += 1;
                                local_mis.push(Mismatch {
                                    word: *word,
                                    profile: profile.name,
                                    opcode: op,
                                    kind,
                                    detail,
                                });
                            }
                        }
                    }
                    let mut c = counts.lock().expect("lock");
                    c.compared += local.compared;
                    c.agreed += local.agreed;
                    c.mismatched += local.mismatched;
                    c.unchecked_native += local.unchecked_native;
                    c.unchecked_timeout += local.unchecked_timeout;
                    c.unchecked_model += local.unchecked_model;
                    c.unchecked_mem += local.unchecked_mem;
                    c.unchecked_x18 += local.unchecked_x18;
                    c.unchecked_reentry += local.unchecked_reentry;
                    c.violations_sigill += local.violations_sigill;
                    c.killed += local.killed;
                    drop(c);
                    let mut m = mismatches.lock().expect("lock");
                    m.extend(local_mis);
                    drop(m);
                    let mut s = skips.lock().expect("lock");
                    for (k, v) in local_skip {
                        *s.entry(k).or_default() += v;
                    }
                    drop(s);
                    let mut o = by_opcode.lock().expect("lock");
                    for (k, (t, b)) in local_op {
                        let e = o.entry(k).or_default();
                        e.0 += t;
                        e.1 += b;
                    }
                }
            }));
        }
        for h in handles {
            h.join().expect("worker");
        }
        let c = counts.lock().expect("lock");
        println!(
            "  profile {:<9} cumulative: compared {} agreed {} MISMATCH {}",
            profile.name, c.compared, c.agreed, c.mismatched
        );
    }

    // ---------- report ----------
    let c = counts.lock().expect("lock");
    let m = mismatches.lock().expect("lock");
    let s = skips.lock().expect("lock");
    let o = by_opcode.lock().expect("lock");
    let elapsed = t0.elapsed().as_secs_f64();
    let excluded = c.unchecked_native
        + c.unchecked_timeout
        + c.unchecked_model
        + c.unchecked_mem
        + c.unchecked_x18
        + c.unchecked_reentry
        + c.killed;
    println!();
    println!("elapsed          : {elapsed:.1}s sweep + {scan_s:.1}s population scan");
    println!("compared         : {}", c.compared);
    println!("agreed           : {}", c.agreed);
    println!();
    // THE BLIND-SPOT LEDGER, printed on every run rather than kept in a doc.
    // Each line is a class of word this oracle CANNOT speak about; the module
    // header says why each one exists. Coverage that is lost has to be visible
    // beside the coverage that was obtained, or "0 mismatches" is a number
    // about an unknown denominator.
    println!("-- blind-spot ledger (excluded from `compared`; see the BLIND SPOTS header) --");
    println!("   native fault                                : {}", c.unchecked_native);
    println!("   native TIMEOUT (host-dependent, see Counts) : {}", c.unchecked_timeout);
    println!("   effects outside the concrete replayer       : {}", c.unchecked_model);
    println!("   memory outside the shared window            : {}", c.unchecked_mem);
    println!("   touches the platform register x18 [bug 3]   : {}", c.unchecked_x18);
    println!("   branched back into the slot prologue [bug 4]: {}", c.unchecked_reentry);
    println!("   killed the executor                         : {}", c.killed);
    println!(
        "   TOTAL EXCLUDED {excluded} of {} trials ({:.2}% compared)",
        excluded + c.compared,
        100.0 * c.compared as f64 / (excluded + c.compared).max(1) as f64
    );
    println!();
    println!("-- why words could not be replayed --");
    for (k, v) in s.iter() {
        println!("   {v:>10}  {k}");
    }
    println!();
    println!("=========================================================");
    println!("SEMANTIC MISMATCHES : {}", c.mismatched);
    println!("SIGILL VIOLATIONS   : {}", c.violations_sigill);
    println!("=========================================================");

    if !m.is_empty() {
        let mut by_kind: BTreeMap<(String, String), Vec<&Mismatch>> = BTreeMap::new();
        for x in m.iter() {
            by_kind.entry((x.opcode.clone(), x.kind.clone())).or_default().push(x);
        }
        println!();
        println!("-- mismatch families (opcode x first disagreeing component) --");
        let mut rows: Vec<_> = by_kind.iter().collect();
        rows.sort_by_key(|(_, v)| std::cmp::Reverse(v.len()));
        for ((op, kind), v) in rows.iter().take(40) {
            let e = v[0];
            println!("{:>9}  {op:<14} {kind:<6} e.g. {:08x} [{}] {}", v.len(), e.word, e.profile, e.detail);
        }
        let mut f = String::new();
        for x in m.iter() {
            f.push_str(&format!(
                "{:08x}\t{}\t{}\t{}\t{}\n",
                x.word, x.profile, x.opcode, x.kind, x.detail
            ));
        }
        std::fs::write("/tmp/natsem/mismatches.tsv", &f).ok();
        println!();
        println!("all mismatches: /tmp/natsem/mismatches.tsv");
    }

    // Per-opcode coverage, so a claim of "no mismatch" can be read against
    // WHICH opcodes were actually exercised. An opcode with 0 compared words is
    // not evidence of anything.
    let mut cov: Vec<_> = o.iter().collect();
    cov.sort_by_key(|(_, (t, _))| std::cmp::Reverse(*t));
    println!();
    println!("-- opcodes compared (count, mismatches) --");
    let mut line = String::new();
    for (op, (t, b)) in &cov {
        line.push_str(&format!("{op}={t}{}  ", if *b > 0 { format!("/BAD{b}") } else { String::new() }));
        if line.len() > 100 {
            println!("   {line}");
            line.clear();
        }
    }
    if !line.is_empty() {
        println!("   {line}");
    }
    println!("   ({} distinct opcodes compared)", cov.len());

    // THE ACCEPTED-BUT-NEVER-COMPARED SET. See the comment where
    // `population_ops` is built: these are opcodes the MODEL accepts — so the
    // output gate can reach Proven on them — and about which this differential
    // has said nothing at all. Zero mismatches is not a statement about them.
    let never: Vec<(&String, &u64)> =
        population_ops.iter().filter(|(op, _)| !o.contains_key(*op)).collect();
    println!();
    println!("-- accepted by the model, NEVER COMPARED here (count = words in population) --");
    if never.is_empty() {
        println!("   none — every opcode the model accepts in this population was compared");
    } else {
        let mut line = String::new();
        for (op, n) in &never {
            line.push_str(&format!("{op}={n}  "));
            if line.len() > 100 {
                println!("   {line}");
                line.clear();
            }
        }
        if !line.is_empty() {
            println!("   {line}");
        }
        println!(
            "   ({} of {} accepted opcodes are UNCHECKED by this oracle — the gate is not)",
            never.len(),
            population_ops.len()
        );
    }

    // ---------- machine-readable result ----------
    //
    // The gate reads THIS, not the human report. Parsing prose out of stdout is
    // how a check ends up silently matching nothing when a line is reworded —
    // the same failure mode as a test filter that matches zero tests.
    if let Some(prefix) = &out_prefix {
        let mut fams: BTreeMap<&str, u64> = BTreeMap::new();
        for x in m.iter() {
            *fams.entry(x.opcode.as_str()).or_default() += 1;
        }
        let mut j = String::from("{\n");
        j.push_str(&format!("  \"mutation\": \"{}\",\n", mutation.name()));
        j.push_str(&format!("  \"population_words\": {},\n", words.len()));
        j.push_str(&format!("  \"population_digest\": \"{digest:#018x}\",\n"));
        j.push_str(&format!("  \"seed\": {seed},\n"));
        j.push_str(&format!("  \"profiles\": {},\n", profiles.len()));
        j.push_str(&format!("  \"profile_set\": \"{}\",\n", json_escape(&profile_set)));
        j.push_str(&format!("  \"sweep_s\": {elapsed:.2},\n"));
        j.push_str(&format!("  \"scan_s\": {scan_s:.2},\n"));
        j.push_str(&format!("  \"compared\": {},\n", c.compared));
        j.push_str(&format!("  \"agreed\": {},\n", c.agreed));
        j.push_str(&format!("  \"mismatched\": {},\n", c.mismatched));
        j.push_str(&format!("  \"sigill_violations\": {},\n", c.violations_sigill));
        j.push_str(&format!("  \"opcodes_compared\": {},\n", cov.len()));
        j.push_str(&format!("  \"opcodes_accepted\": {},\n", population_ops.len()));
        j.push_str("  \"opcodes_accepted_never_compared\": [");
        for (i, (op, _)) in never.iter().enumerate() {
            j.push_str(&format!("{}\"{}\"", if i == 0 { "" } else { ", " }, json_escape(op)));
        }
        j.push_str("],\n");
        j.push_str("  \"excluded\": {\n");
        j.push_str(&format!("    \"native_fault\": {},\n", c.unchecked_native));
        j.push_str(&format!("    \"native_timeout\": {},\n", c.unchecked_timeout));
        j.push_str(&format!("    \"effects_outside_replayer\": {},\n", c.unchecked_model));
        j.push_str(&format!("    \"memory_outside_window\": {},\n", c.unchecked_mem));
        j.push_str(&format!("    \"platform_register_x18\": {},\n", c.unchecked_x18));
        j.push_str(&format!("    \"slot_prologue_reentry\": {},\n", c.unchecked_reentry));
        j.push_str(&format!("    \"killed_executor\": {}\n", c.killed));
        j.push_str("  },\n");
        j.push_str("  \"mismatch_families\": {");
        for (i, (op, n)) in fams.iter().enumerate() {
            j.push_str(&format!(
                "{}\n    \"{}\": {n}",
                if i == 0 { "" } else { "," },
                json_escape(op)
            ));
        }
        j.push_str(if fams.is_empty() { "}\n" } else { "\n  }\n" });
        j.push_str("}\n");
        std::fs::write(format!("{prefix}.result.json"), &j).expect("write result json");
        println!();
        println!("result json      : {prefix}.result.json");
    }

    // EXIT CODE IS ABOUT THE MODEL, NOT ABOUT THE MUTATION. Under `--mutate`
    // mismatches are the point, so a nonzero count is success for that run and
    // the gate decides what to make of it; a SIGILL is a violation either way.
    let bad = if mutation == Mutation::None {
        c.mismatched > 0 || c.violations_sigill > 0
    } else {
        c.violations_sigill > 0
    };
    if bad {
        std::process::exit(1);
    }
}

/// Does this word carry a PC-relative target inside the slot template?
fn reenters_slot(word: u32, pc: u64, slot_lo: u64) -> bool {
    let Ok(insn) = decode_aarch64(&word.to_le_bytes(), pc) else { return false };
    let hit = insn.operands().any(|o| match o {
        Operand::PcRelAddr(target) => *target >= slot_lo && *target <= pc,
        _ => false,
    });
    hit
}

fn opcode_of(word: u32, pc: u64) -> String {
    decode_aarch64(&word.to_le_bytes(), pc)
        .map(|i| format!("{:?}", i.opcode))
        .unwrap_or_else(|_| "<refused>".into())
}

fn is_candidate(word: u32, pc: u64, st: &MachineState) -> bool {
    decode_aarch64(&word.to_le_bytes(), pc)
        .is_ok_and(|i| Aarch64Semantics.effects(st, &i).is_ok())
}

/// Uniform candidates: scan the Weyl permutation from `offset`, keep the words
/// the gate's antecedent admits, until `n` of them are collected.
///
/// The shard count is `SHARDS`, NOT the worker count, so the selected set is a
/// pure function of `(n, offset)`.
fn candidates(n: u64, offset: u64, pc: u64) -> Vec<u32> {
    let found = Arc::new(Mutex::new(Vec::<u32>::new()));
    let mut handles = Vec::new();
    let per = (n / SHARDS) + 1;
    for s in 0..SHARDS {
        let found = Arc::clone(&found);
        handles.push(std::thread::spawn(move || {
            let st = MachineState::symbolic();
            let mut mine = Vec::new();
            // Each shard owns its own stretch of the permutation, well clear of
            // its neighbours', so the union is still an unbiased prefix-free set.
            let mut idx = offset + s * (1 << 28);
            while (mine.len() as u64) < per {
                let word = (idx as u32).wrapping_mul(WEYL);
                if is_candidate(word, pc, &st) {
                    mine.push(word);
                }
                idx += 1;
            }
            found.lock().expect("lock").extend(mine);
        }));
    }
    for h in handles {
        h.join().expect("scan");
    }
    let mut v = Arc::try_unwrap(found).expect("sole owner").into_inner().expect("lock");
    v.sort_unstable();
    v.dedup();
    v
}

/// Stratified candidates: at most `cap` words per OPCODE.
///
/// Uniform sampling of the encoding space is dominated by a handful of huge
/// opcode buckets — a 3-million-word uniform sample can contain single-digit
/// examples of an entire instruction class. Capping per opcode spends the
/// budget where the coverage is, and is what makes "N distinct opcodes
/// compared" a number worth printing.
///
/// DETERMINISTIC IN `cap` ALONE. The shard count is `SHARDS`, not the worker
/// count — see the constant. `--stratify 3000` names one specific set of words
/// on every host, and the digest printed by `main` is what proves it.
fn stratified(cap: usize, pc: u64) -> Vec<u32> {
    let acc = Arc::new(Mutex::new(BTreeMap::<String, Vec<u32>>::new()));
    let mut handles = Vec::new();
    let per_shard = cap / SHARDS as usize + 1;
    for s in 0..SHARDS {
        let acc = Arc::clone(&acc);
        handles.push(std::thread::spawn(move || {
            let st = MachineState::symbolic();
            let mut mine: BTreeMap<String, Vec<u32>> = BTreeMap::new();
            // Shard slices are 2^28 indices apart and each scans far less
            // than that, so the union is disjoint by construction.
            let stride = 1u64 << 28;
            let mut idx = s * stride;
            // A bounded scan: enough to fill the caps for everything that is
            // not vanishingly rare, and bounded so the harness terminates.
            for _ in 0..40_000_000u64 {
                let word = (idx as u32).wrapping_mul(WEYL);
                idx += 1;
                if let Ok(i) = decode_aarch64(&word.to_le_bytes(), pc) {
                    if Aarch64Semantics.effects(&st, &i).is_ok() {
                        let k = format!("{:?}", i.opcode);
                        let e = mine.entry(k).or_default();
                        if e.len() < per_shard {
                            e.push(word);
                        }
                    }
                }
            }
            let mut g = acc.lock().expect("lock");
            for (k, v) in mine {
                g.entry(k).or_default().extend(v);
            }
        }));
    }
    for h in handles {
        h.join().expect("scan");
    }
    let g = Arc::try_unwrap(acc).expect("sole owner").into_inner().expect("lock");
    let mut out = Vec::new();
    for (_, mut v) in g {
        v.sort_unstable();
        v.dedup();
        v.truncate(cap);
        out.extend(v);
    }
    out.sort_unstable();
    out.dedup();
    out
}

fn skip_key(s: &Skip) -> String {
    match s {
        Skip::NotDecoded => "decoder refuses the word".into(),
        Skip::NoEffects => "model refuses the word".into(),
        Skip::UnsupportedEffect(w) => format!("effect outside the concrete replayer: {w}"),
        Skip::EvalError(e) => format!("formula not concretely evaluable: {e}"),
    }
}
