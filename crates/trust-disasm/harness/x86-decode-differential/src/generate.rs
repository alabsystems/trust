//! Candidate generation.
//!
//! Coverage here is a statement about THIS FILE, never about the encoding
//! space: x86-64 instructions are 1-15 bytes, so there is nothing to enumerate
//! (see blind spot B in `main.rs`).
//!
//! The `sweep` mode is systematic over the ModRM/SIB/REX matrix because that is
//! precisely where every address defect of 2026-08-18 lived — RIP-relative
//! resolution, absolute `[disp32]`, a dropped displacement, `R12` as an index,
//! and a fabricated base. A random-byte mode alone would hit those cells only
//! by luck.

/// Opcodes whose ModRM operand is a memory reference we can project, paired
/// with the REX prefixes worth varying. `8B` is `mov r64, r/m64`.
const MODRM_OPCODES: &[u8] = &[0x8B, 0x89, 0x03, 0x01, 0x8A, 0x88];

pub fn candidates(mode: &str, seed: u64, limit: usize) -> Vec<Vec<u8>> {
    let mut out = match mode {
        "corpus" => corpus(),
        "sweep" => sweep(),
        "random" => random(seed, limit),
        "all" => {
            let mut v = corpus();
            v.extend(sweep());
            v.extend(random(seed, limit));
            v
        }
        _ => Vec::new(),
    };
    out.truncate(limit.max(1).min(200_000));
    out
}

/// The encodings that exhibited real defects, kept so a regression in any of
/// them is caught by the smallest possible run.
fn corpus() -> Vec<Vec<u8>> {
    [
        // RIP-relative: address must resolve against the NEXT instruction.
        "488b0510000000",
        "488d0510000000",
        // ... including past a trailing immediate (11 bytes).
        "48c705000000000100000",
        // Absolute [disp32] via SIB with no base and no index.
        "488b042534120000",
        // R12 as a SIB index (REX.X), and R13 as the control.
        "4a8b0423",
        "4a8b0c2b",
        // [index*scale + disp32]: no base register, displacement kept.
        "488b0c8510000000",
        // base + index*scale + disp8.
        "488b544b20",
        // 8-bit registers: AH without REX, SPL with it.
        "b412",
        "40b412",
        // Immediate stores of each width.
        "c60701",
        "c70001000000",
        "48c70001000000",
        // Shifts (decode side only).
        "48c1e040",
        "48d3e0",
    ]
    .iter()
    .filter_map(|h| hex(h))
    .collect()
}

/// Systematic over the addressing-mode matrix: mod x rm x SIB(base,index,scale)
/// x REX.{W,R,X,B}. This is the region the address defects lived in.
fn sweep() -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for &opcode in MODRM_OPCODES {
        for rex in [0x00u8, 0x48, 0x4A, 0x49, 0x4B, 0x4C, 0x4F] {
            for md in 0u8..3 {
                for rm in 0u8..8 {
                    for reg in [0u8, 3] {
                        let modrm = (md << 6) | (reg << 3) | rm;
                        let mut bytes = Vec::new();
                        if rex != 0 {
                            bytes.push(rex);
                        }
                        bytes.push(opcode);
                        bytes.push(modrm);
                        if rm == 4 {
                            // SIB byte follows: vary scale, index and base.
                            for &sib in &[0x00u8, 0x23, 0x2B, 0x85, 0x4B, 0xE5, 0x24] {
                                let mut w = bytes.clone();
                                w.push(sib);
                                push_disp(&mut w, md, (sib & 0x07) == 5);
                                out.push(w);
                            }
                            continue;
                        }
                        push_disp(&mut bytes, md, false);
                        // mod=00, rm=101 is RIP-relative and carries a disp32.
                        if md == 0 && rm == 5 {
                            bytes.extend_from_slice(&[0x10, 0x00, 0x00, 0x00]);
                        }
                        out.push(bytes);
                    }
                }
            }
        }
    }
    out
}

fn push_disp(bytes: &mut Vec<u8>, md: u8, sib_no_base: bool) {
    match md {
        1 => bytes.push(0x20),
        2 => bytes.extend_from_slice(&[0x20, 0x00, 0x00, 0x00]),
        0 if sib_no_base => bytes.extend_from_slice(&[0x34, 0x12, 0x00, 0x00]),
        _ => {}
    }
}

/// Random bytes: finds crashes, length disagreements and forms neither the
/// corpus nor the sweep thought of. Deterministic in the seed so a failing run
/// reproduces exactly.
fn random(seed: u64, limit: usize) -> Vec<Vec<u8>> {
    let mut state = seed | 1;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    (0..limit.min(50_000))
        .map(|_| {
            let len = 1 + (next() % 8) as usize;
            (0..len).map(|_| (next() >> 24) as u8).collect()
        })
        .collect()
}

fn hex(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok()).collect()
}
