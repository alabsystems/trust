// PATH-GUARD-VALUE-1 verification probes, round 2 (verifyA): guards whose formula
// reads a value at a point OTHER than the source terminal, and the bool-def /
// copy-def sibling channels with writes the kill may not see.
#![allow(unused_assignments, unused_mut, clippy::all)]

#[inline(never)]
pub fn set(p: &mut usize, v: usize) {
    *p = v;
}

// V17: `len()` taken inside a block expression BEFORE the slice is reseated, the
// comparison after. a=[1,2,3,4,5], b=[] panics.
pub fn v17_len_block_expr_bug(a: &[u8], b: &[u8]) -> u8 {
    let mut v = a;
    if {
        let l = v.len();
        v = b;
        l
    } > 3
    {
        v[3]
    } else {
        0
    }
}

// V19: the plain-statement form of V17. a=[1,2,3,4,5], b=[] panics.
pub fn v19_len_then_reseat_bug(a: &[u8], b: &[u8]) -> u8 {
    let mut v = a;
    let l = v.len();
    v = b;
    if l > 3 { v[3] } else { 0 }
}

// V20: an `if len != 3` bool guard (copy temp + Ne) and a `&mut len` CALL write.
// xs=[true], m=3, n=100 panics.
pub fn v20_bool_guard_call_write_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        if len != 3 {
            return acc;
        }
        if c {
            set(&mut len, n);
        }
        acc ^= buf[len];
    }
    acc
}

// V21: the bool guard and a raw-pointer write. xs=[true], m=3, n=100 panics.
pub fn v21_bool_guard_raw_write_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let p: *mut usize = &raw mut len;
    let mut acc = 0u8;
    for &c in xs {
        if len != 3 {
            return acc;
        }
        if c {
            unsafe {
                *p = n;
            }
        }
        acc ^= buf[len];
    }
    acc
}

// V22: the guard is on a COPY `t` and the write is a `&mut` call (a2 + v20).
// xs=[true], m=3, n=100 panics.
pub fn v22_copy_guard_call_write_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        let t = len;
        if t != 3 {
            return acc;
        }
        if c {
            set(&mut len, n);
        }
        acc ^= buf[len];
    }
    acc
}

// V23: `len < 8` guard at the loop head; the write is `len = len + n` in a branch.
// xs=[true], m=3, n=100 panics.
pub fn v23_lt_guard_add_write_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        if len >= 8 {
            return acc;
        }
        if c {
            len = len.wrapping_add(n);
        }
        acc ^= buf[len];
    }
    acc
}

// V24: two loop-carried values; the guard tests `a`, the write swaps `a` and `b`.
// xs=[true], a0=3, b0=100 panics.
pub fn v24_swap_bug(xs: &[bool], buf: &[u8; 8], a0: usize, b0: usize) -> u8 {
    let mut a = a0;
    let mut b = b0;
    let mut acc = 0u8;
    for &c in xs {
        match a {
            3 => {}
            _ => return acc,
        }
        if c {
            core::mem::swap(&mut a, &mut b);
        }
        acc ^= buf[a];
    }
    acc
}

// V25: guard in a `loop` with an explicit `break`-guarded exit and a write on the
// latch, the read in the next iteration BEFORE the guard re-runs? The guard runs
// first in every iteration; the read is after a conditional write. xs=[true],
// m=3, n=100 panics.
pub fn v25_loop_break_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    let mut i = 0;
    loop {
        if i >= xs.len() {
            break;
        }
        if len != 3 {
            break;
        }
        if xs[i] {
            len = n;
        }
        acc ^= buf[len];
        i += 1;
    }
    acc
}

// V26: the write is in a nested `match` with three arms (a 3-way join).
// xs=[2], m=3, n=100 panics.
pub fn v26_three_way_join_bug(xs: &[u8], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        match len {
            3 => {}
            _ => return acc,
        }
        match c {
            0 => acc = acc.wrapping_add(1),
            1 => len = 3,
            _ => len = n,
        }
        acc ^= buf[len];
    }
    acc
}

// C11: V19's correct twin: the comparison reads the CURRENT length.
pub fn c11_len_after_reseat_ctl(a: &[u8], b: &[u8]) -> u8 {
    let mut v = a;
    v = b;
    let l = v.len();
    if l > 3 { v[3] } else { 0 }
}

// C12: a while loop over a local struct field (two tracked names: aggregate init
// and field write), read before the bump.
pub struct Pos {
    pub i: usize,
    pub tag: u8,
}
pub fn c12_local_struct_while_ctl(buf: &[u8; 8]) -> u32 {
    let mut p = Pos { i: 0, tag: 1 };
    let mut s = 0u32;
    while p.i < 8 {
        s += buf[p.i] as u32;
        p.i += 1;
    }
    s + p.tag as u32
}

// C13: `match self.state` style: a field of `&mut` guarded then read.
pub struct M {
    pub k: usize,
    pub v: [u8; 8],
}
pub fn c13_self_field_match_ctl(m: &mut M, xs: &[bool]) -> u8 {
    let mut acc = 0u8;
    for &c in xs {
        if m.k >= 8 {
            return acc;
        }
        acc ^= m.v[m.k];
        if c {
            m.k += 1;
        }
    }
    acc
}

// C14: a tuple local `(len, x)` guard on `.0`, read before write.
pub fn c14_tuple_field_ctl(xs: &[bool], buf: &[u8; 8], m: usize) -> u8 {
    let mut t = (m, 0u8);
    let mut acc = 0u8;
    for &c in xs {
        match t.0 {
            0..=7 => {}
            _ => return acc,
        }
        acc ^= buf[t.0];
        if c {
            t.0 = t.0 / 2;
        }
        t.1 = t.1.wrapping_add(1);
    }
    acc ^ t.1
}
