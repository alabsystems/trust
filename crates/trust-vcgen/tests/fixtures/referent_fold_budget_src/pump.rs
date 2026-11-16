// REAL class "whole function collapsed to unsupported_mir (vcgen budget exhausted)":
// shape of aterm-codec `Inflater::pump` (inflate/stream.rs:205) — `let Self { .. } = self`
// splits `&mut self` into many `&mut` field locals, a `match phase` hands out `&mut`
// payload fields, and stores go through all of them inside a loop. Every such store makes
// main's referent-fold stability walk re-resolve the stored-through pointer (nested, no
// memo), so VC generation outruns the 120 s function budget and the whole body becomes
// `unsupported_mir`. The seal proves the arithmetic rows.
pub enum Phase {
    Header,
    Stored { remaining: u32 },
    Huff { lit: u32, dist: u32, warm: u32 },
    Done,
}

pub struct St {
    input: Vec<u8>,
    cursor: usize,
    phase: Phase,
    final_block: bool,
    out: Vec<u8>,
    out_at: usize,
    produced: u64,
}

impl St {
    pub fn pump(&mut self) -> u32 {
        let Self { input, cursor, phase, final_block, out, out_at, produced } = self;
        let mut steps = 0u32;
        loop {
            if out.len().saturating_sub(*out_at) >= 4096 || steps > 64 {
                return steps;
            }
            steps += 1;
            match phase {
                Phase::Done => return steps,
                Phase::Header => {
                    let b = input.get(*cursor).copied().unwrap_or(0);
                    *cursor = cursor.saturating_add(1);
                    *final_block = b & 1 == 1;
                    *phase = match (b >> 1) & 3 {
                        0 => Phase::Stored { remaining: u32::from(b) },
                        1 => Phase::Huff { lit: 1, dist: 2, warm: 3 },
                        _ => Phase::Done,
                    };
                }
                Phase::Stored { remaining } => {
                    while *remaining > 0 {
                        let b = input.get(*cursor).copied().unwrap_or(0);
                        *cursor = cursor.saturating_add(1);
                        out.push(b);
                        *produced = produced.saturating_add(1);
                        *remaining = remaining.saturating_sub(1);
                    }
                    *phase = if *final_block { Phase::Done } else { Phase::Header };
                }
                Phase::Huff { lit, dist, warm } => {
                    let b = input.get(*cursor).copied().unwrap_or(0);
                    *cursor = cursor.saturating_add(1);
                    *lit = lit.wrapping_add(u32::from(b));
                    *dist = dist.wrapping_add(*lit);
                    out.push(b);
                    *produced = produced.saturating_add(1);
                    if *warm == 0 {
                        *phase = if *final_block { Phase::Done } else { Phase::Header };
                    } else {
                        *warm -= 1;
                    }
                    *out_at = out_at.saturating_add(0);
                }
            }
        }
    }
}
