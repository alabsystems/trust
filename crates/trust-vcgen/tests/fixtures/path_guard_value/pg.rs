// PATH-GUARD-VALUE-1 probes (round 2): more shapes of the loop-head guard / later
// write defect, and controls the fix must keep PROVED.

pub struct St { pub len: usize }

// B1: the gs shape on a struct field behind `&mut` (a projected guard subject).
// xs=[true], st.len=3, n=100 panics.
pub fn field_switch_bug(xs: &[bool], buf: &[u8; 8], st: &mut St, n: usize) -> u8 {
    let mut acc = 0;
    for &c in xs {
        match st.len { 3 => {} _ => return acc }
        if c { st.len = n; }
        acc ^= buf[st.len];
    }
    acc
}

// B2: a plain `if len != 3 { return }` guard (bool switch resolved to its compare).
// xs=[true], m=3, n=100 panics.
pub fn bool_guard_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        if len != 3 { return acc; }
        if c { len = n; }
        acc ^= buf[len];
    }
    acc
}

// B3: a `while i < 8` loop condition, then a conditional write before the index.
// c=[true], n=100 panics.
pub fn while_lt_bug(buf: &[u8; 8], c: &[bool], n: usize) -> u8 {
    let mut i = 0;
    let mut acc = 0;
    let mut k = 0;
    while i < 8 && k < c.len() {
        if c[k] { i = n; }
        acc ^= buf[i];
        k += 1;
    }
    acc
}

// C1: a guard on a join value outside any loop; the read is under the guard. Correct.
pub fn nl_join_guard_ctl(buf: &[u8; 8], m: usize, c: bool) -> u8 {
    let mut len = m;
    if c { len = m / 2; }
    match len { 3 => buf[len], _ => 0 }
}

// C2: loop-head guard, a diamond that does not write `len`, then the read; `len` is
// written only after the read. Correct (len == 3 at the read).
pub fn diamond_nowrite_ctl(xs: &[bool], buf: &[u8; 8], m: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        match len { 3 => {} _ => return acc }
        if c { acc = acc.wrapping_add(1); } else { acc ^= 1; }
        acc ^= buf[len];
        len = m;
    }
    acc
}

// C3: the canonical guarded loop index. Correct.
pub fn loop_index_ctl(buf: &[u8; 8], n: usize) -> u8 {
    let mut i = 0;
    let mut acc = 0;
    while i < n {
        if i < 8 { acc ^= buf[i]; }
        i += 1;
    }
    acc
}

// C4: `while i < 8` with the index read before a conditional bump. Correct.
pub fn while_lt_read_first_ctl(buf: &[u8; 8], c: &[bool]) -> u8 {
    let mut i = 0;
    let mut acc = 0;
    let mut k = 0;
    while i < 8 && k < c.len() {
        acc ^= buf[i];
        if c[k] { i += 1; } else { i += 2; }
        k += 1;
    }
    acc
}
