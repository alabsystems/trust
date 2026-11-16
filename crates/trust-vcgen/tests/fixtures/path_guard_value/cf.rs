// rangeconfirm: independent rebuild of the range lens claims (sources from the report).

// G01: single literal arm. Claimed panic at xs = [true], m = 3, n = 100.
pub fn g01_one_arm_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len { 3 => {} _ => return acc }
        if c { len = n; }
        acc ^= buf[..len].len();
    }
    acc
}

// G02: if-let literal, RangeFrom.
pub fn g02_iflet_lit_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        let 3 = len else { return acc };
        if c { len = n; }
        acc ^= buf[len..].len();
    }
    acc
}

// G03: loop/break form.
pub fn g03_loop_bug(buf: &[u8; 8], k: usize, m: usize, n: usize) -> usize {
    let mut len = m;
    let mut i = 0;
    let mut acc = 0;
    loop {
        if i > k { break; }
        match len { 3 => {} _ => return acc }
        if i == k { len = n; }
        acc ^= buf[..len].len();
        i += 1;
    }
    acc
}

// GS: scalar twin of G01 (ordinary index).
pub fn gs_one_arm_scalar_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len { 3 => {} _ => return acc }
        if c { len = n; }
        acc ^= buf[len];
    }
    acc
}

// F01: multi-arm.
pub fn f01_switch_range_to_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len { 0 | 1 | 2 | 3 => {} _ => return acc }
        if c { len = n; }
        acc += buf[..len].len();
    }
    acc
}

// F02: multi-arm scalar.
pub fn f02_switch_scalar_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len { 0 | 1 | 2 | 3 => {} _ => return acc }
        if c { len = n; }
        acc += buf[len] as usize;
    }
    acc
}

// F03: RangeFrom via let binding.
pub fn f03_switch_range_from_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len { 0 | 1 | 2 | 3 => {} _ => return acc }
        if c { len = n; }
        let r = len..;
        acc += buf[r].len();
    }
    acc
}

// F04: lo..8.
pub fn f04_switch_range_pair_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut lo = m;
    let mut acc = 0;
    for &c in xs {
        match lo { 0 | 1 | 2 | 3 => {} _ => return acc }
        if c { lo = n; }
        acc += buf[lo..8].len();
    }
    acc
}

// F05: while.
pub fn f05_switch_while_bug(buf: &[u8; 8], k: usize, m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    let mut i = 0;
    while i < k {
        match len { 0 | 1 | 2 | 3 => {} _ => return acc }
        if i == 0 { len = n; }
        acc += buf[..len].len();
        i += 1;
    }
    acc
}

// F07: control (guard after the write). Correct.
pub fn f07_switch_after_write_ctl(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        if c { len = n; }
        match len { 0 | 1 | 2 | 3 => {} _ => return acc }
        acc += buf[..len].len();
    }
    acc
}

// F08: split_at.
pub fn f08_switch_split_at_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len { 0 | 1 | 2 | 3 => {} _ => return acc }
        if c { len = n; }
        acc += buf.split_at(len).0.len();
    }
    acc
}

// R22: guard via an inlined helper. Correct.
#[inline(always)]
fn fits(len: usize) -> bool { len <= 8 }
pub fn r22_helper_guard_ctl(xs: &[usize], buf: &[u8; 8]) -> usize {
    let mut len = 0;
    let mut acc = 0;
    for &x in xs {
        if !fits(len) { return acc; }
        acc += buf[..len].len();
        len = x;
    }
    acc
}
