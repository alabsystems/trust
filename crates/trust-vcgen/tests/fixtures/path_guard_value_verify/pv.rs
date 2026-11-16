// PATH-GUARD-VALUE-1 adversarial verification probes (verifyA). Every `_bug`
// panics on the input in its comment; every `_ctl` is correct on every input.
#![allow(unused_assignments, unused_mut, clippy::all)]

pub struct St {
    pub len: usize,
}

pub struct Pair {
    pub a: usize,
    pub b: usize,
}

pub struct Cur<'a> {
    pub buf: &'a [u8],
    pub pos: usize,
}

#[inline(never)]
pub fn set(p: &mut usize, v: usize) {
    *p = v;
}

// V01: guard at the OUTER loop head, an inner loop writes `len`, the read follows
// the inner loop. xs=[true], m=3, n=100 panics.
pub fn v01_nested_inner_write_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
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
        acc ^= buf[len];
    }
    acc
}

// V02: the write is a `&mut len` passed to a call. xs=[true], m=3, n=100 panics.
pub fn v02_call_mut_write_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        match len {
            3 => {}
            _ => return acc,
        }
        if c {
            set(&mut len, n);
        }
        acc ^= buf[len];
    }
    acc
}

// V03: the write goes through a raw pointer made before the loop; guard and read
// name `len` directly. xs=[true], m=3, n=100 panics.
pub fn v03_raw_ptr_write_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let p: *mut usize = &raw mut len;
    let mut acc = 0u8;
    for &c in xs {
        match len {
            3 => {}
            _ => return acc,
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

// V04: the guard subject is `*r` for a `&mut` held across the loop.
// xs=[true], m=3, n=100 panics.
pub fn v04_mut_ref_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let r = &mut len;
    let mut acc = 0u8;
    for &c in xs {
        match *r {
            3 => {}
            _ => return acc,
        }
        if c {
            *r = n;
        }
        acc ^= buf[*r];
    }
    acc
}

// V05: the guard is the result of `v.is_empty()` taken BEFORE `v` is reseated.
// a=[1], b=[] panics (v[0] on an empty slice).
pub fn v05_is_empty_stale_bug(a: &[u8], b: &[u8]) -> u8 {
    let mut v = a;
    let e = v.is_empty();
    v = b;
    if e {
        return 0;
    }
    v[0]
}

// V06: `v.is_empty()` taken at the loop head, `v` reseated in a branch, `v[0]`
// after the join. xs=[true], a=[1], b=[] panics.
pub fn v06_is_empty_loop_bug(xs: &[bool], a: &[u8], b: &[u8]) -> u8 {
    let mut v = a;
    let mut acc = 0u8;
    for &c in xs {
        if v.is_empty() {
            return acc;
        }
        if c {
            v = b;
        }
        acc ^= v[0];
    }
    acc
}

// V07: an assert-passed bounds fact at the loop head (`buf[len]`), a write in a
// branch, a second `buf[len]` after the join. xs=[true], m=3, n=100 panics.
pub fn v07_bounds_fact_loop_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        acc ^= buf[len];
        if c {
            len = n;
        }
        acc ^= buf[len];
    }
    acc
}

// V08: a `match` on a RANGE at the loop head, a write in a branch, the read after
// the join. xs=[true], m=3, n=100 panics.
pub fn v08_range_match_loop_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        match len {
            0..=7 => {}
            _ => return acc,
        }
        if c {
            len = n;
        }
        acc ^= buf[len];
    }
    acc
}

// V09: two sequential loops: the first exits on `len == 3`, the second writes
// `len`, the read follows. m=0, xs=[true], n=100 panics.
pub fn v09_two_loops_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    while len != 3 {
        len = (len + 1) % 8;
    }
    for &c in xs {
        if c {
            len = n;
        }
    }
    buf[len]
}

// V10: a local struct field is the guard subject (two tracked names: the whole
// aggregate and the field). xs=[true], m=3, n=100 panics.
pub fn v10_local_field_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut s = Pair { a: m, b: 0 };
    let mut acc = 0u8;
    for &c in xs {
        match s.a {
            3 => {}
            _ => return acc,
        }
        if c {
            s.a = n;
        }
        s.b += 1;
        acc ^= buf[s.a];
    }
    acc
}

// V11: guard on a loop-carried `len`, write then `continue`, so the read is
// reached only on the no-write path in THIS iteration; but the guard's value
// in the NEXT iteration is the written one. xs=[true,false], m=3, n=100: the
// second iteration re-tests `len == 3` and returns. Correct? the guard re-runs,
// so this is a CONTROL (see c04). Bug twin: the read is in the write arm.
// xs=[true], m=3, n=100 panics.
pub fn v11_write_arm_read_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        match len {
            3 => {}
            _ => return acc,
        }
        if c {
            len = n;
            acc ^= buf[len];
            continue;
        }
        acc ^= buf[len];
    }
    acc
}

// V12: the guard is a `while` loop condition over a field of `&mut self`, and
// a branch writes the field before the read. c=[true], pos=0, n=100 panics.
pub fn v12_cursor_write_bug(cur: &mut Cur<'_>, c: &[bool], n: usize) -> u32 {
    let mut s = 0u32;
    let mut k = 0;
    while cur.pos < cur.buf.len() && k < c.len() {
        if c[k] {
            cur.pos = n;
        }
        s += cur.buf[cur.pos] as u32;
        cur.pos += 1;
        k += 1;
    }
    s
}

// V13: a guard inside an INNER loop on the OUTER loop's carried value; the
// outer loop writes after the inner loop; the read is in the inner loop body
// of the NEXT outer iteration, before the guard re-runs? No — the inner head
// re-tests. Bug: inner loop guard `len == 3` exit edge, write after the inner
// loop in a branch, read after the join. xs=[true], m=3, n=100 panics.
pub fn v13_inner_exit_guard_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        let mut j = 0;
        while len == 3 && j < 1 {
            j += 1;
        }
        if len != 3 {
            return acc;
        }
        if c {
            len = n;
        }
        acc ^= buf[len];
    }
    acc
}

// V14: `s.starts_with("abc")` taken BEFORE `s` is reseated.
// a="abcd", b="" panics (byte index 2 of an empty str).
pub fn v14_starts_with_stale_bug(a: &str, b: &str) -> u8 {
    let mut s = a;
    let ok = s.starts_with("abc");
    s = b;
    if !ok {
        return 0;
    }
    s.as_bytes()[2]
}

// V15: a `checked_sub`-style assert fact (`7 - len` cannot underflow => len <= 7)
// at the loop head; a PLAIN assignment write in a branch (a3 used a call write).
// xs=[true], m=3, n=100 panics.
pub fn v15_sub_fact_assign_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        let d = 7 - len;
        if c {
            len = n;
        }
        acc ^= buf[len] ^ (d as u8);
    }
    acc
}

// V16: guard via `if let Some(3) = o` on a loop-carried Option; write in a branch;
// read the payload after the join. xs=[true], m=Some(3), n=Some(100) panics.
pub fn v16_option_payload_bug(xs: &[bool], buf: &[u8; 8], m: Option<usize>, n: Option<usize>) -> u8 {
    let mut o = m;
    let mut acc = 0u8;
    for &c in xs {
        let Some(3) = o else { return acc };
        if c {
            o = n;
        }
        if let Some(j) = o {
            acc ^= buf[j];
        }
    }
    acc
}

// ---- controls (correct on every input) ----

// C01: field behind `&mut`, guard then read BEFORE the write.
pub fn c01_field_read_before_write_ctl(xs: &[bool], buf: &[u8; 8], st: &mut St, n: usize) -> u8 {
    let mut acc = 0u8;
    for &c in xs {
        match st.len {
            3 => {}
            _ => return acc,
        }
        acc ^= buf[st.len];
        if c {
            st.len = n;
        }
    }
    acc
}

// C02: local struct field, guard then read BEFORE the write.
pub fn c02_local_field_read_before_write_ctl(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut s = Pair { a: m, b: 0 };
    let mut acc = 0u8;
    for &c in xs {
        match s.a {
            3 => {}
            _ => return acc,
        }
        acc ^= buf[s.a];
        if c {
            s.a = n;
        }
        s.b += 1;
    }
    acc
}

// C03: the canonical cursor loop over `&mut self` fields.
pub fn c03_cursor_ctl(cur: &mut Cur<'_>) -> u32 {
    let mut s = 0u32;
    while cur.pos < cur.buf.len() {
        s = s.wrapping_add(cur.buf[cur.pos] as u32);
        cur.pos += 1;
    }
    s
}

// C04: write then `continue`: the read is reached only on the no-write path.
pub fn c04_continue_after_write_ctl(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        match len {
            3 => {}
            _ => return acc,
        }
        if c {
            len = n;
            continue;
        }
        acc ^= buf[len];
    }
    acc
}

// C05: guard at the outer head; an inner loop that does NOT write `len`; read after.
pub fn c05_nested_no_write_ctl(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        match len {
            3 => {}
            _ => return acc,
        }
        let mut k = 0;
        while k < 2 {
            acc = acc.wrapping_add(1);
            k += 1;
        }
        acc ^= buf[len];
        if c {
            len = n;
        }
    }
    acc
}

// C06: a plain local in a loop with an `if len < 8` guard and a later bump.
pub fn c06_lt_guard_bump_ctl(xs: &[bool], buf: &[u8; 8], m: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        if len >= 8 {
            return acc;
        }
        acc ^= buf[len];
        if c {
            len += 1;
        }
    }
    acc
}

// C07: the guard sits in the loop body after the write (f07 shape), scalar.
pub fn c07_guard_after_write_ctl(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        if c {
            len = n;
        }
        match len {
            3 => {}
            _ => return acc,
        }
        acc ^= buf[len];
    }
    acc
}

// C08: guard on `*r`, read before the write.
pub fn c08_mut_ref_read_first_ctl(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let r = &mut len;
    let mut acc = 0u8;
    for &c in xs {
        match *r {
            3 => {}
            _ => return acc,
        }
        acc ^= buf[*r];
        if c {
            *r = n;
        }
    }
    acc
}

// C09: `v.is_empty()` at the loop head, read before the reseat.
pub fn c09_is_empty_loop_ctl(xs: &[bool], a: &[u8], b: &[u8]) -> u8 {
    let mut v = a;
    let mut acc = 0u8;
    for &c in xs {
        if v.is_empty() {
            return acc;
        }
        acc ^= v[0];
        if c {
            v = b;
        }
    }
    acc
}

// C10: non-loop: a guard on a join value, the read under it (pg.rs C1 shape),
// with a match instead of `if`.
pub fn c10_join_then_guard_ctl(buf: &[u8; 8], m: usize, c: bool) -> u8 {
    let mut len = m;
    if c {
        len = m / 2;
    }
    if len < 8 { buf[len] } else { 0 }
}
