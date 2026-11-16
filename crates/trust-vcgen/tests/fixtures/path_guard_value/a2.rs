// Design probes (not for landing): siblings of the path-guard set-spelling
// defect A through establish-point-stamped defs and assert-passed facts.

// A2: the guard is on a COPY `t` of the loop-carried `len` (a pure place-read
// def `t == len#{init,write}` stamped at the loop head), and the index reads
// `len` after a branch that writes it. Input xs=[true], m=3, n=100 panics.
pub fn a2_copy_def_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        let t = len;
        if t != 3 { return acc; }
        if c { len = n; }
        acc ^= buf[len];
    }
    acc
}

// A2 control: the index reads `len` BEFORE the write. Correct (len == 3).
pub fn a2_copy_def_ctl(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        let t = len;
        if t != 3 { return acc; }
        acc ^= buf[len];
        if c { len = n; }
    }
    acc
}

// A3: an assert-passed (CheckedSub) fact `len <= 7` established at the loop
// head; a CALL-dest write in a branch (adds no threaded def). xs=[true], m=3,
// n=100 panics.
pub fn a3_semfact_call_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0u8;
    for &c in xs {
        let d = 7 - len;
        if c { len = std::hint::black_box(n); }
        acc ^= buf[len] ^ (d as u8);
    }
    acc
}

// A4: the gs shape, but the write is a CALL dest instead of an assignment.
pub fn a4_switch_call_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len { 3 => {} _ => return acc }
        if c { len = std::hint::black_box(n); }
        acc ^= buf[len];
    }
    acc
}

// GS control: guard and read BEFORE the write in the same iteration. Correct.
pub fn gs_read_before_write_ctl(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len { 3 => {} _ => return acc }
        acc ^= buf[len];
        if c { len = n; }
    }
    acc
}

// GS control 2: the write in the branch stores a SAFE value; correct, but a
// join phi separates the guard's value from the read's (expected proof loss).
pub fn gs_safe_write_ctl(xs: &[bool], buf: &[u8; 8], m: usize) -> u8 {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len { 3 => {} _ => return acc }
        if c { len = 2; }
        acc ^= buf[len];
    }
    acc
}
