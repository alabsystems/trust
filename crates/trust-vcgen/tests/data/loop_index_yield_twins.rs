// TRUST-KI-1015-1, the loop-index shape: a loop payload read through `i - k` (a `for i in
// START..END` range, an `enumerate` index, an adapter closure's item), in the default lane's
// per-statement rows and in their `unix_hardened` twins. Each group is correct first (every
// index and subtraction is in range), then the same shapes made wrong, each with a reachable panic.

// ---- a range: `for i in START..END` yields `START <= i < END`; correct ----

pub fn sum_lag15(w: &[u32; 64]) -> u32 {
    let mut acc = 0u32;
    for i in 16..64 {
        acc = acc.wrapping_add(w[i - 15]);
    }
    acc
}

pub fn schedule(w: &mut [u32; 64]) {
    for i in 16..64 {
        let s0 = w[i - 15].rotate_right(7) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_right(17) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
    }
}

pub fn lag2_slice(v: &[u32]) -> u32 {
    let mut acc = 0u32;
    for i in 2..v.len() {
        acc = acc.wrapping_add(v[i - 2]);
    }
    acc
}

// ---- wrong: each has a reachable panic ----

// Off by one: at i = 15, `i - 16` underflows.
pub fn off_by_one_sub(w: &[u32; 64]) -> u32 {
    let mut acc = 0u32;
    for i in 15..64 {
        acc = acc.wrapping_add(w[i - 16]);
    }
    acc
}

// Wrong range: at i = 0, `i - 15` underflows.
pub fn range_from_zero(w: &[u32; 64]) -> u32 {
    let mut acc = 0u32;
    for i in 0..64 {
        acc = acc.wrapping_add(w[i - 15]);
    }
    acc
}

// Wrong end: at i = 65, `w[i - 1]` reads index 64.
pub fn range_past_end(w: &[u32; 64]) -> u32 {
    let mut acc = 0u32;
    for i in 16..66 {
        acc = acc.wrapping_add(w[i - 1]);
    }
    acc
}

// Wrong width: at i = 47, `w[i - 15]` reads index 32 of a 32-element array.
pub fn narrow_array(w: &[u32; 32]) -> u32 {
    let mut acc = 0u32;
    for i in 16..64 {
        acc = acc.wrapping_add(w[i - 15]);
    }
    acc
}

// Guard removed: the start is the caller's; at lo = 0, `i - 15` underflows.
pub fn caller_start(w: &[u32; 64], lo: usize) -> u32 {
    let mut acc = 0u32;
    for i in lo..64 {
        acc = acc.wrapping_add(w[i - 15]);
    }
    acc
}

// The payload is rebound: `i = n` replaces the yielded value, so the range says nothing.
pub fn rebound_payload(w: &[u32; 64], n: usize) -> u32 {
    let mut acc = 0u32;
    for mut i in 16..64 {
        i = n;
        acc = acc.wrapping_add(w[i - 15]);
    }
    acc
}

// The slice twin of the off-by-one: at i = 1, `i - 2` underflows.
pub fn lag2_slice_from_one(v: &[u32]) -> u32 {
    let mut acc = 0u32;
    for i in 1..v.len() {
        acc = acc.wrapping_add(v[i - 2]);
    }
    acc
}

// ---- enumerate: `for (i, x) in s.iter().enumerate()` yields `0 <= i < s.len()` ----
// Correct: `s[i - k]` under `i >= k` (the read is below the length the loop runs over), and
// `w[63 - i]` (`63 - i` cannot underflow, because `i < 64`).

pub fn enum_lag3(v: &[u32]) -> u32 {
    let mut acc = 0u32;
    for (i, x) in v.iter().enumerate() {
        if i >= 3 {
            acc = acc.wrapping_add(v[i - 3] ^ *x);
        }
    }
    acc
}

pub fn enum_lag15(w: &[u32; 64]) -> u32 {
    let mut acc = 0u32;
    for (i, x) in w.iter().enumerate() {
        if i >= 15 {
            acc = acc.wrapping_add(w[i - 15] ^ *x);
        }
    }
    acc
}

pub fn enum_mirror(w: &[u32; 64]) -> u32 {
    let mut acc = 0u32;
    for (i, x) in w.iter().enumerate() {
        acc = acc.wrapping_add(w[63 - i] ^ *x);
    }
    acc
}

// Wrong, each with a reachable panic.

// Guard off by one: at i = 2, `i - 3` underflows.
pub fn enum_lag3_guard_off_by_one(v: &[u32]) -> u32 {
    let mut acc = 0u32;
    for (i, x) in v.iter().enumerate() {
        if i >= 2 {
            acc = acc.wrapping_add(v[i - 3] ^ *x);
        }
    }
    acc
}

// A wider array: at i = 64, `63 - i` underflows.
pub fn enum_mirror_wide(a: &[u32; 65]) -> u32 {
    let mut acc = 0u32;
    for (i, x) in a.iter().enumerate() {
        acc = acc.wrapping_add(a[63 - i] ^ *x);
    }
    acc
}

// Off by one: at i = 0, `w[64 - i]` reads index 64.
pub fn enum_mirror_past(w: &[u32; 64]) -> u32 {
    let mut acc = 0u32;
    for (i, x) in w.iter().enumerate() {
        acc = acc.wrapping_add(w[64 - i] ^ *x);
    }
    acc
}

// The wrong slice: `i` is below `a.len()`, and `b[i - 3]` reads past a shorter `b`.
pub fn enum_other_lag(a: &[u32], b: &[u32]) -> u32 {
    let mut acc = 0u32;
    for (i, x) in a.iter().enumerate() {
        if i >= 3 {
            acc = acc.wrapping_add(b[i - 3] ^ *x);
        }
    }
    acc
}

// ---- an adapter closure: `(16..64).for_each(|i| ..)`, the ADAPTER_YIELD premise `16 <= i < 64` ----
// Correct.

pub fn for_each_lag15(w: &[u32; 64]) -> u32 {
    let mut acc = 0u32;
    (16..64).for_each(|i| {
        acc = acc.wrapping_add(w[i - 15]);
    });
    acc
}

pub fn for_each_lag16(w: &[u32; 64]) -> u32 {
    let mut acc = 0u32;
    (16..64).for_each(|i| {
        acc = acc.wrapping_add(w[i - 16]);
    });
    acc
}

// Wrong, each with a reachable panic.

// Off by one: at i = 16, `i - 17` underflows.
pub fn for_each_lag17(w: &[u32; 64]) -> u32 {
    let mut acc = 0u32;
    (16..64).for_each(|i| {
        acc = acc.wrapping_add(w[i - 17]);
    });
    acc
}

// Wrong end: at i = 65, `w[i - 1]` reads index 64.
pub fn for_each_past_end(w: &[u32; 64]) -> u32 {
    let mut acc = 0u32;
    (16..66).for_each(|i| {
        acc = acc.wrapping_add(w[i - 1]);
    });
    acc
}

// Wrong width: at i = 47, `w[i - 15]` reads index 32 of a 32-element array.
pub fn for_each_narrow(w: &[u32; 32]) -> u32 {
    let mut acc = 0u32;
    (16..64).for_each(|i| {
        acc = acc.wrapping_add(w[i - 15]);
    });
    acc
}
