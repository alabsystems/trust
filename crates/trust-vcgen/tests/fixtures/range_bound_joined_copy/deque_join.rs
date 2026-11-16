// Probes: VecDeque::range over a multiply-written bound (the `norm_range_violation` lane).
use std::collections::VecDeque;

// Correct: guard after the join, range built in the call's own block.
pub fn vd_join_guard_ctl(q: &VecDeque<u8>, m: usize, n: usize, c: bool) -> usize {
    let mut k = m;
    if c {
        k = n;
    }
    if k > q.len() {
        return 0;
    }
    q.range(..k).count()
}

// Panics (xs = [true], q.len() < m, n <= q.len()): the range is read before the
// conditional write, the guard after the join reads the new value.
pub fn vd_joined_after_bug(q: &VecDeque<u8>, xs: &[bool], m: usize, n: usize) -> usize {
    let mut k = m;
    let mut acc = 0;
    for &c in xs {
        let r = ..k;
        if c {
            k = n;
        }
        if k > q.len() {
            return acc;
        }
        acc += q.range(r).count();
    }
    acc
}
