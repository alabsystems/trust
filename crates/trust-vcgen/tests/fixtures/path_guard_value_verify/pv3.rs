// PATH-GUARD-VALUE-1 verification probes, round 3 (verifyA): slice-RANGE twins of the
// new class-A shapes, for the range lane on the fix/range-bound-unknown merge.
#![allow(unused_assignments, unused_mut, clippy::all)]

pub struct Pair {
    pub a: usize,
    pub b: usize,
}

// R01 (v01): outer-head guard, inner loop writes, `..len` after. xs=[true], 3, 100 panics.
pub fn r01_nested_inner_write_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len {
            3 => {}
            _ => return acc,
        }
        let mut k = 0;
        while k < 2 {
            if c {
                len = n;
            }
            k += 1;
        }
        acc ^= buf[..len].len();
    }
    acc
}

// R10 (v10): local struct field subject. xs=[true], 3, 100 panics.
pub fn r10_local_field_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut s = Pair { a: m, b: 0 };
    let mut acc = 0;
    for &c in xs {
        match s.a {
            3 => {}
            _ => return acc,
        }
        if c {
            s.a = n;
        }
        s.b += 1;
        acc ^= buf[s.a..].len();
    }
    acc
}

// R16 (v16): Option payload. xs=[true], Some(3), Some(100) panics.
pub fn r16_option_payload_bug(xs: &[bool], buf: &[u8; 8], m: Option<usize>, n: Option<usize>) -> usize {
    let mut o = m;
    let mut acc = 0;
    for &c in xs {
        let Some(3) = o else { return acc };
        if c {
            o = n;
        }
        if let Some(j) = o {
            acc ^= buf[..j].len();
        }
    }
    acc
}

// R26 (v26): three-way join. xs=[2], 3, 100 panics.
pub fn r26_three_way_join_bug(xs: &[u8], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len {
            3 => {}
            _ => return acc,
        }
        match c {
            0 => acc += 1,
            1 => len = 3,
            _ => len = n,
        }
        acc ^= buf[..len].len();
    }
    acc
}

// R02c (c02): local field, guard then range BEFORE the write. Correct.
pub fn r02_local_field_read_first_ctl(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut s = Pair { a: m, b: 0 };
    let mut acc = 0;
    for &c in xs {
        match s.a {
            3 => {}
            _ => return acc,
        }
        acc ^= buf[..s.a].len();
        if c {
            s.a = n;
        }
        s.b += 1;
    }
    acc
}

// R05c: scalar guard then range BEFORE the write (gs_read_before_write twin). Correct.
pub fn r05_read_first_ctl(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len {
            3 => {}
            _ => return acc,
        }
        acc ^= buf[len..].len();
        if c {
            len = n;
        }
    }
    acc
}
