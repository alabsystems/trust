// Probes: the yield lane's joined-copy fallback (a copy of a joined local as a range end).

// Panics (xs = [true], m = 0, n = 100): the guard reads `k` BEFORE a conditional write,
// the copy `k2` is read after the join (same reaching-definition set as the guard).
pub fn y_guard_before_write_bug(a: &[u8; 8], xs: &[bool], m: usize, n: usize) -> u32 {
    let mut k = m;
    let mut acc = 0u32;
    for &c in xs {
        if k > 8 {
            return acc;
        }
        if c {
            k = n;
        }
        let k2 = k;
        for i in 0..k2 {
            acc += a[i] as u32;
        }
    }
    acc
}

// The same shape with a plain index (no yield fact): the general encoding's control.
pub fn plain_guard_before_write_bug(a: &[u8; 9], xs: &[bool], m: usize, n: usize) -> u32 {
    let mut k = m;
    let mut acc = 0u32;
    for &c in xs {
        if k > 8 {
            return acc;
        }
        if c {
            k = n;
        }
        let k2 = k;
        acc += a[k2] as u32;
    }
    acc
}

// Correct (sweep p50): a copy of a joined local as a range end.
pub fn y_joined_end_ctl(a: &[u8; 26], n: usize) -> u32 {
    let k = if n > 26 { 26 } else { n };
    let mut acc = 0u32;
    for i in 0..k {
        acc += a[i] as u32;
    }
    acc
}
