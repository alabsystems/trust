//! Driver for the native semantic executor (`natsem.c`, beside this file).
//!
//! Same rule as `native-invariant`'s executor glue, for the same reason: a word
//! is NEVER dropped. If a candidate kills the executor, the record at the first
//! missing index is what did it and is marked `KILLED`, not allowed to vanish
//! into a short read and shift every later record by one — which would
//! misattribute every subsequent comparison.

use std::io::Read;
use std::process::Command;

/// `sizeof(rec_t)` in `natsem.c`. The V file was APPENDED, so every offset the
/// parser below already read is unchanged; only this total moved.
pub const REC_SIZE: usize = 1048;
pub const NDIFF_MAX: usize = 16;
/// Byte offset of `rec_t::v` — immediately after the memory-diff arrays.
const REC_V_OFFSET: usize = 536;

pub const OUT_EXECUTED: u8 = 0;
pub const OUT_SIGILL: u8 = 1;
pub const OUT_ESCAPED: u8 = 4;
pub const OUT_TIMEOUT: u8 = 7;
pub const OUT_KILLED: u8 = 9;

/// One word's observed post-state, read out of the trap's `ucontext`.
#[derive(Debug, Clone)]
pub struct Record {
    pub outcome: u8,
    /// Number of 8-byte memory words that changed. `0xff` means more changed
    /// than the record holds, so the memory comparison is UNCHECKED rather than
    /// believed.
    pub ndiff: u8,
    pub gpr: [u64; 31],
    pub sp: u64,
    pub pc: u64,
    pub nzcv: u8,
    /// The SIMD/FP file V0..V31, read out of the trap's `ucontext` NEON state.
    pub fpr: [u128; 32],
    pub mem: Vec<(u64, u64)>,
}

fn rd64(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(b[off..off + 8].try_into().expect("8 bytes"))
}

#[must_use]
pub fn parse_record(b: &[u8], win_base: u64) -> Record {
    let outcome = b[0];
    let ndiff = b[1];
    let mut gpr = [0u64; 31];
    for (i, slot) in gpr.iter_mut().enumerate() {
        *slot = rd64(b, 8 + i * 8);
    }
    let sp = rd64(b, 256);
    let pc = rd64(b, 264);
    let nzcv = rd64(b, 272) as u8;
    let n = if ndiff == 0xff { NDIFF_MAX } else { ndiff as usize };
    let mut mem = Vec::with_capacity(n);
    for i in 0..n {
        mem.push((win_base + rd64(b, 280 + i * 8), rd64(b, 280 + NDIFF_MAX * 8 + i * 8)));
    }
    let fpr = core::array::from_fn(|i| {
        let lo = rd64(b, REC_V_OFFSET + i * 16);
        let hi = rd64(b, REC_V_OFFSET + i * 16 + 8);
        (u128::from(hi) << 64) | u128::from(lo)
    });
    Record { outcome, ndiff, gpr, sp, pc, nzcv, fpr, mem }
}

#[must_use]
pub fn natsem_path() -> String {
    std::env::var("NATSEM")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/natsem").to_string())
}

/// The address the candidate word executes at, asked of the executor itself
/// rather than recomputed here. The model is given this as its PC, so every
/// PC-relative form (`adr`, `adrp`, `b.cond`, literal loads) is compared
/// against the address it actually ran at.
/// Returns `(word_pc, template_base)`.
#[must_use]
pub fn slot_pc() -> (u64, u64) {
    let out = Command::new(natsem_path()).arg("--slotpc").output().expect("spawn natsem --slotpc");
    let text = String::from_utf8_lossy(&out.stdout);
    let mut it = text.split_whitespace();
    let pc = it.next().expect("slot pc").parse().expect("slot pc value");
    let lo = it.next().expect("template base").parse().expect("template base value");
    // THE BINARY LAYOUT, ASKED OF THE EXECUTOR RATHER THAN ASSUMED. A `rec_t`
    // or context block that grew on one side only would not fault: it would
    // misparse every field and produce confident nonsense. Both sides state
    // their sizes and they must agree here, before a single word runs.
    let rec_size: usize = it.next().expect("rec size").parse().expect("rec size value");
    let ctx_len: usize = it.next().expect("ctx len").parse().expect("ctx len value");
    assert_eq!(
        rec_size, REC_SIZE,
        "natsem.c sizeof(rec_t) = {rec_size} but this driver parses {REC_SIZE}-byte records"
    );
    assert_eq!(
        ctx_len,
        crate::ctx::CTX_LEN,
        "natsem.c CTX_LEN = {ctx_len} but this driver writes {}-byte context blocks",
        crate::ctx::CTX_LEN
    );
    (pc, lo)
}

fn run_once(
    ctx: &std::path::Path,
    wf: &std::path::Path,
    of: &std::path::Path,
    start: usize,
    want: usize,
) -> (Vec<u8>, bool) {
    let out_p = Command::new(natsem_path())
        .arg(ctx)
        .arg(wf)
        .arg(of)
        .arg(start.to_string())
        .output()
        .expect("spawn natsem");
    let mut out = Vec::new();
    if let Ok(mut f) = std::fs::File::open(of) {
        f.read_to_end(&mut out).expect("read records");
    }
    if out.len() < want * REC_SIZE && !out_p.status.success() && out_p.status.code().is_some() {
        let err = String::from_utf8_lossy(&out_p.stderr);
        let tail: Vec<&str> = err.lines().rev().take(3).collect();
        eprintln!("  !! natsem exited {:?}: {}", out_p.status.code(), tail.join(" | "));
    }
    out.truncate(want * REC_SIZE);
    let by_signal = out_p.status.code().is_none();
    (out, by_signal)
}

/// Run one chunk to completion. Always returns exactly `words.len()` records.
#[must_use]
pub fn run_chunk(
    words: &[u32],
    ctx: &std::path::Path,
    work: &std::path::Path,
    tag: &str,
    win_base: u64,
) -> Vec<Record> {
    if words.is_empty() {
        return Vec::new();
    }
    let wf = work.join(format!("w{tag}.bin"));
    let of = work.join(format!("o{tag}.bin"));
    let mut blob = Vec::with_capacity(words.len() * 4);
    for w in words {
        blob.extend_from_slice(&w.to_le_bytes());
    }
    std::fs::write(&wf, &blob).expect("write words");

    let mut acc: Vec<Record> = Vec::with_capacity(words.len());
    let mut stillborn = 0usize;
    while acc.len() < words.len() {
        let want = words.len() - acc.len();
        let (got, by_signal) = run_once(ctx, &wf, &of, acc.len(), want);
        let whole = got.len() / REC_SIZE;
        for i in 0..whole {
            acc.push(parse_record(&got[i * REC_SIZE..(i + 1) * REC_SIZE], win_base));
        }
        if whole == want {
            break;
        }
        if !by_signal {
            stillborn += 1;
            assert!(
                stillborn <= 3,
                "chunk {tag}: natsem exited without running at index {} — fix the executor \
                 rather than attributing its failure to a candidate",
                acc.len()
            );
            continue;
        }
        stillborn = 0;
        acc.push(Record {
            outcome: OUT_KILLED,
            ndiff: 0,
            gpr: [0; 31],
            sp: 0,
            pc: 0,
            nzcv: 0,
            fpr: [0; 32],
            mem: Vec::new(),
        });
    }
    let _ = std::fs::remove_file(&wf);
    let _ = std::fs::remove_file(&of);
    acc
}
