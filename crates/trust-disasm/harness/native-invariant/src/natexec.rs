//! Driver for the native executor (`natexec.c`, beside this file).
//!
//! The executor runs each candidate word for real and reports one outcome byte
//! per word. This module owns the one rule that matters at this boundary: a
//! word is NEVER dropped. If a candidate terminates the executor process, the
//! word at the first missing index is what did it, and it is recorded as
//! `KILLED` rather than allowed to vanish into a short read.

use std::io::Read;
use std::process::Command;

pub const OUT_N: usize = 10;
pub const OUT_NAMES: [&str; OUT_N] = [
    "EXECUTED",
    "SIGILL",
    "MEMFAULT",
    "TRAP_SELF",
    "ESCAPED",
    "SIGSYS",
    "SIGFPE",
    "TIMEOUT",
    "OTHER",
    "KILLED",
];
/// The only outcome that violates the invariant: the CPU refused the encoding.
pub const OUT_SIGILL: usize = 1;
/// A candidate that terminated the executor process.
pub const OUT_KILLED: usize = 9;

#[must_use]
pub fn natexec_path() -> String {
    std::env::var("NATEXEC")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/natexec").to_string())
}

/// Outcome bytes, plus whether the executor died by SIGNAL (a candidate did it)
/// rather than exiting with a code (the executor itself failed to start).
fn run_once(
    wf: &std::path::Path,
    of: &std::path::Path,
    start: usize,
    want: usize,
) -> (Vec<u8>, bool) {
    // NEVER silence the oracle. The first version of this discarded the
    // executor's stderr; when the executor then failed to start, the driver saw
    // only an empty result file, blamed the first candidate, and spun 32,703
    // times re-running the same chunk. A harness that hides why its ground
    // truth failed reports nonsense with total confidence.
    let out_p = Command::new(natexec_path())
        .arg(wf)
        .arg(of)
        .arg(start.to_string())
        .output()
        .expect("spawn natexec");
    let mut out = Vec::new();
    if let Ok(mut f) = std::fs::File::open(of) {
        f.read_to_end(&mut out).expect("read outcomes");
    }
    if out.len() < want && !out_p.status.success() && out_p.status.code().is_some() {
        // Exited with a code (not a signal): the executor failed to START. That
        // is a harness fault, not a candidate outcome, and must be visible.
        let err = String::from_utf8_lossy(&out_p.stderr);
        let tail: Vec<&str> = err.lines().rev().take(3).collect();
        eprintln!("  !! natexec exited {:?}: {}", out_p.status.code(), tail.join(" | "));
    }
    out.truncate(want);
    let by_signal = out_p.status.code().is_none();
    (out, by_signal)
}

/// Run one chunk to completion. The returned vector always has exactly
/// `words.len()` entries — a word is never dropped.
///
/// A candidate that the kernel answers with SIGKILL (some `brk` immediates)
/// terminates the executor. The chunk's word file is written ONCE and the
/// executor is resumed by index, so a casualty costs one process spawn rather
/// than a rewritten chunk. The first version rewrote the remainder each time
/// and, when the executor was failing to start at all, spun 32,703 rounds
/// re-writing 3 MB apiece — the harness's own failure mode masquerading as a
/// property of the input.
#[must_use]
pub fn run_chunk(words: &[u32], work: &std::path::Path, tag: &str) -> Vec<u8> {
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

    let mut acc: Vec<u8> = Vec::with_capacity(words.len());
    let mut stillborn = 0usize;
    while acc.len() < words.len() {
        let want = words.len() - acc.len();
        let (got, by_signal) = run_once(&wf, &of, acc.len(), want);
        if got.len() == want {
            acc.extend_from_slice(&got);
            break;
        }
        // Discriminate the two ways a short result can happen. Killed by a
        // SIGNAL: the candidate at the next index did it, and since outcome
        // writes are unbuffered that index is exact. Exited with a CODE: the
        // executor never ran, and blaming a candidate would be a fabrication.
        if !by_signal {
            stillborn += 1;
            assert!(
                stillborn <= 3,
                "chunk {tag}: executor exited without running at index {} — fix the executor \
                 rather than attributing its failure to a candidate",
                acc.len()
            );
            continue;
        }
        stillborn = 0;
        acc.extend_from_slice(&got);
        acc.push(OUT_KILLED as u8);
    }
    let _ = std::fs::remove_file(&wf);
    let _ = std::fs::remove_file(&of);
    acc
}
