//! Executor protocol: spawn `natsem86` (an x86_64 Mach-O; the kernel routes it
//! through Rosetta), never drop a record. A candidate that kills the executor
//! is recorded KILLED at its own index and the run RESUMES at the next index —
//! a dropped record would shift every later one and misattribute every
//! subsequent comparison.

use std::io::Read;
use std::process::Command;

pub const REC_SIZE: usize = 408;
pub const NDIFF_MAX: usize = 16;
pub const SLOT_BYTES: usize = 16;

pub const OUT_EXECUTED: u8 = 0;
pub const OUT_SIGILL: u8 = 1;
pub const OUT_MEMFAULT: u8 = 2;
pub const OUT_TRAP_SELF: u8 = 3;
pub const OUT_ESCAPED: u8 = 4;
pub const OUT_TIMEOUT: u8 = 7;
pub const OUT_KILLED: u8 = 9;

#[derive(Debug, Clone)]
pub struct Record {
    pub outcome: u8,
    pub ndiff: u8,
    pub gpr: [u64; 16],
    pub pc: u64,
    /// SF<<3 | ZF<<2 | CF<<1 | OF.
    pub flags: u8,
    pub mem: Vec<(u64, u64)>,
}

fn rd64(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(b[off..off + 8].try_into().expect("8 bytes"))
}

pub fn parse_record(b: &[u8], win_base: u64) -> Record {
    let outcome = b[0];
    let ndiff = b[1];
    let mut gpr = [0u64; 16];
    for (i, slot) in gpr.iter_mut().enumerate() {
        *slot = rd64(b, 8 + i * 8);
    }
    let pc = rd64(b, 8 + 128);
    let flags = rd64(b, 8 + 136) as u8;
    let n = if ndiff == 0xff { NDIFF_MAX } else { usize::from(ndiff).min(NDIFF_MAX) };
    let mut mem = Vec::with_capacity(n);
    for i in 0..n {
        mem.push((win_base + rd64(b, 152 + i * 8), rd64(b, 152 + NDIFF_MAX * 8 + i * 8)));
    }
    Record { outcome, ndiff, gpr, pc, flags, mem }
}

/// The `--slotpc` handshake: (candidate pc, record size, ctx len).
pub fn slotpc(bin: &str) -> (u64, u64, usize, usize) {
    let out = Command::new(bin).arg("--slotpc").output().expect("natsem86 --slotpc");
    let text = String::from_utf8_lossy(&out.stdout);
    let mut it = text.split_whitespace();
    let pc: u64 = it.next().expect("pc").parse().expect("pc");
    let base: u64 = it.next().expect("base").parse().expect("base");
    let rec: usize = it.next().expect("rec").parse().expect("rec");
    let ctx: usize = it.next().expect("ctx").parse().expect("ctx");
    (pc, base, rec, ctx)
}

/// Run the executor over `words`, resuming past kills, returning one record
/// per word.
pub fn run(
    bin: &str,
    ctx_path: &str,
    words_path: &str,
    recs_path: &str,
    count: usize,
) -> Vec<Record> {
    let _ = std::fs::remove_file(recs_path);
    let mut done = 0usize;
    while done < count {
        let status = Command::new(bin)
            .args([ctx_path, words_path, recs_path, &done.to_string()])
            .status()
            .expect("spawn natsem86");
        let have = std::fs::metadata(recs_path).map(|m| m.len() as usize / REC_SIZE).unwrap_or(0);
        if status.success() && have >= count {
            break;
        }
        if have <= done && !status.success() {
            // The executor died ON the record at index `have`: write KILLED.
            let mut killed = vec![0u8; REC_SIZE];
            killed[0] = OUT_KILLED;
            use std::io::Write;
            let mut f = std::fs::OpenOptions::new().append(true).open(recs_path).expect("recs");
            f.write_all(&killed).expect("write killed");
            done = have + 1;
        } else {
            done = have;
        }
    }
    let mut data = Vec::new();
    std::fs::File::open(recs_path).expect("recs").read_to_end(&mut data).expect("read");
    data.chunks(REC_SIZE).take(count).map(|c| parse_record(c, crate::ctx::SCRATCH_BASE)).collect()
}
