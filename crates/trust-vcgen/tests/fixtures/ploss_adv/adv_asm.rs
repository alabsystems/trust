// adv_asm: a write the MIR carries only as an inline-asm OUTPUT (aarch64), feeding the
// class-10 range lane and a scalar index. Every `_bug` panics on the input in its comment.
#![allow(clippy::all, unused_mut, unused_assignments, dead_code)]

// AS01: range built from `len`, asm writes 3 into `len`, guard on the new value.
// m=100 panics.
pub fn as01_asm_out_range_bug(buf: &[u8; 8], m: usize) -> usize {
    let mut len = m;
    let r = ..len;
    unsafe { core::arch::asm!("mov {0}, #3", out(reg) len) };
    if len > 8 {
        return 0;
    }
    buf[r].len()
}

// AS02: `k < 4` by construction, asm adds 4 (inout), index. n=0 panics.
pub fn as02_asm_inout_index_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    unsafe { core::arch::asm!("add {0}, {0}, #4", inout(reg) k) };
    t[k]
}

// AS03: a loop-carried `len` written by asm in a branch, loop-head literal guard,
// range after the join. xs=[true], m=3 panics (asm writes 100).
pub fn as03_asm_loop_switch_bug(xs: &[bool], buf: &[u8; 8], m: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len {
            3 => {}
            _ => return acc,
        }
        if c {
            unsafe { core::arch::asm!("mov {0}, #100", out(reg) len) };
        }
        acc ^= buf[..len].len();
    }
    acc
}
