// Probes for the joined-copy range-bound fallback in the BTree range lane and the
// str char-boundary axiom (follow-up of dd584167118).
use std::collections::BTreeMap;

// ── BTreeMap::range ────────────────────────────────────────────────────────────

// Correct: guard after the join, range built in the call's own block.
pub fn bt_join_guard_ctl(map: &BTreeMap<usize, u8>, a: usize, m: usize, n: usize, c: bool) -> usize {
    let mut k = m;
    if c {
        k = n;
    }
    if a > k {
        return 0;
    }
    map.range(a..k).count()
}

// Panics (map non-empty, xs = [true], m < a <= n): the range is read BEFORE the
// conditional write, the guard AFTER the join reads the new value.
pub fn bt_joined_after_bug(map: &BTreeMap<usize, u8>, xs: &[bool], a: usize, m: usize, n: usize) -> usize {
    let mut k = m;
    let mut acc = 0;
    for &c in xs {
        let r = a..k;
        if c {
            k = n;
        }
        if a > k {
            return acc;
        }
        acc += map.range(r).count();
    }
    acc
}

// Panics (n < a, map non-empty): the bound is rewritten and the guard reads the new value.
pub fn bt_stale_guard_bug(map: &BTreeMap<usize, u8>, a: usize, m: usize, n: usize, c: bool) -> usize {
    let mut k = m;
    if c {
        k = n;
    }
    let r = a..k;
    k = m;
    if a > k {
        return 0;
    }
    map.range(r).count() + k
}

// Correct: the range is built in an earlier block than the call (a call in between).
pub fn bt_cross_block_ctl(map: &BTreeMap<usize, u8>, a: usize, m: usize, n: usize, c: bool) -> usize {
    let mut k = m;
    if c {
        k = n;
    }
    if a > k {
        return 0;
    }
    let r = a..k;
    let z = std::hint::black_box(0usize);
    map.range(r).count() + z
}

// Panics (a > k): no guard, range built in an earlier block.
pub fn bt_cross_block_bug(map: &BTreeMap<usize, u8>, a: usize, m: usize, n: usize, c: bool) -> usize {
    let mut k = m;
    if c {
        k = n;
    }
    let r = a..k;
    let z = std::hint::black_box(0usize);
    map.range(r).count() + z
}

// Correct: inclusive range over a joined bound, guarded.
pub fn bt_inclusive_ctl(map: &BTreeMap<usize, u8>, a: usize, m: usize, n: usize, c: bool) -> usize {
    let mut k = m;
    if c {
        k = n;
    }
    if a > k {
        return 0;
    }
    map.range(a..=k).count()
}

// Panics: inclusive range read before the conditional write, guard after the join.
pub fn bt_inclusive_joined_after_bug(
    map: &BTreeMap<usize, u8>,
    xs: &[bool],
    a: usize,
    m: usize,
    n: usize,
) -> usize {
    let mut k = m;
    let mut acc = 0;
    for &c in xs {
        let r = a..=k;
        if c {
            k = n;
        }
        if a > k {
            return acc;
        }
        acc += map.range(r).count();
    }
    acc
}

// Panics: guard on the bound BEFORE a conditional write, range built after it.
pub fn bt_guard_before_write_bug(
    map: &BTreeMap<usize, u8>,
    xs: &[bool],
    a: usize,
    m: usize,
    n: usize,
) -> usize {
    let mut k = m;
    let mut acc = 0;
    for &c in xs {
        if a > k {
            return acc;
        }
        if c {
            k = n;
        }
        acc += map.range(a..k).count();
    }
    acc
}

// ── str char boundary ──────────────────────────────────────────────────────────

// Correct: a tested, multiply-written endpoint (the copy `e` of joined `n`).
pub fn cb_join_tested_ctl(s: &str, m: usize, c: bool) -> usize {
    let mut n = m;
    if c {
        n = s.len();
    }
    let e = n;
    if s.is_char_boundary(e) { s[..e].len() } else { 0 }
}

// Correct: same, `e..`.
pub fn cb_join_tested_from_ctl(s: &str, m: usize, c: bool) -> usize {
    let mut n = m;
    if c {
        n = 0;
    }
    let e = n;
    if s.is_char_boundary(e) { s[e..].len() } else { 0 }
}

// Panics (`e` not tested on the `else` path).
pub fn cb_join_untested_bug(s: &str, m: usize, c: bool) -> usize {
    let mut n = m;
    if c {
        n = s.len();
    }
    let e = n;
    if s.is_char_boundary(e) { 0 } else { s[..e].len() }
}

// Correct: tested, in a loop over a joined bound.
pub fn cb_join_tested_loop_ctl(s: &str, xs: &[bool], m: usize) -> usize {
    let mut n = m;
    let mut acc = 0;
    for &c in xs {
        if c {
            n = s.len();
        }
        let e = n;
        if s.is_char_boundary(e) {
            acc += s[..e].len();
        }
    }
    acc
}

// ── slice range, inclusive (the `index_range_violation` fallback) ─────────────

// Correct: inclusive range over a joined, guarded bound.
pub fn sl_inclusive_ctl(b: &[u8; 8], m: usize, n: usize, c: bool) -> usize {
    let mut k = m;
    if c {
        k = n;
    }
    if k >= 8 {
        return 0;
    }
    b[..=k].len()
}

// Panics: inclusive range read before a conditional write, guard after the join.
pub fn sl_inclusive_joined_after_bug(b: &[u8; 8], xs: &[bool], m: usize, n: usize) -> usize {
    let mut k = m;
    let mut acc = 0;
    for &c in xs {
        let r = ..=k;
        if c {
            k = n;
        }
        if k >= 8 {
            return acc;
        }
        acc += b[r].len();
    }
    acc
}
