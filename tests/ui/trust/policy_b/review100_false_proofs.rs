//@ needs-trust-verify
//@ edition: 2021
//@ revisions: join_call_arm signed_clamp_add signed_clamp_index stale_yield_bound len_ssa unsigned_clamp_cast for_len get_join last_join clamp_short_circuit enumerate_stale get_ok last_ok store_through_bound repeated_decrement short_circuit_decrement converging_break reverse_loop frozen_copy_converging frozen_copy_downward get_source_borrowed
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[join_call_arm] check-fail
//@[signed_clamp_add] check-fail
//@[signed_clamp_index] check-fail
//@[stale_yield_bound] check-fail
//@[len_ssa] check-pass
//@[unsigned_clamp_cast] check-pass
//@[for_len] check-pass
//@[get_join] check-fail
//@[last_join] check-fail
//@[clamp_short_circuit] check-fail
//@[enumerate_stale] check-fail
//@[get_ok] check-pass
//@[last_ok] check-pass
//@[store_through_bound] check-pass
//@[repeated_decrement] check-fail
//@[short_circuit_decrement] check-fail
//@[converging_break] check-fail
//@[reverse_loop] check-pass
//@[frozen_copy_converging] check-fail
//@[frozen_copy_downward] check-fail
//@[get_source_borrowed] check-fail
//! Review round 100 (2026-10-10): three false proofs older than the change the round
//! reviewed. Each panicking revision VERIFIED on stage-1 sa145 (the first three
//! kernel-certified under `-Ztrust-policy=certify`) and panics on the input named.
//! * `join_call_arm`: the `_len == coll_len(v)` tie was attached to the call's return
//!   target, the join the `k = n` arm also enters (`f(&vec![1, 2, 3], 10, false)`).
//! * `signed_clamp_add` / `signed_clamp_index`: a SIGNED clamp `if n > C { C } else
//!   { n }` was taken as an unsigned bound of `k as u64` / `k as usize` (`n = -1`).
//! * `stale_yield_bound`: a `next` result carried into the next iteration of an outer
//!   loop, where the range end was redefined before the payload was extracted
//!   (`f(100, 50, &[0; 26])` indexes 49).
//! Review round 101 found the same classes in sibling producers (all pre-existing):
//! * `get_join`: a `get` Some-arm seed from a call returning into a join.
//! * `last_join`: a `last()` seed keyed on an `Option` written twice.
//! * `clamp_short_circuit`: a clamp's var arm also entered around its test.
//! * `enumerate_stale`: the stale-bound class in the enumerate yield builder.
//! Review round 102 (pre-existing): `repeated_decrement` and `short_circuit_decrement`
//! (a `j > K` guard credited to a decrement it does not dominate, or to a second one),
//! `converging_break` (a two-pointer `lo < len` fact at a block the guard does not
//! dominate).
//! Review round 103 (pre-existing): `frozen_copy_converging` / `frozen_copy_downward`, a
//! guard testing a stale copy of the cursor, credited to the cursor's current value.
//! Review round 104 (pre-existing): `get_source_borrowed`, the `get` seed credited to an
//! index source rewritten through `&mut`.
//! The `check-pass` revisions are the controls that keep their proofs.

#[cfg(join_call_arm)]
pub fn f(v: &Vec<u8>, n: usize, c: bool) -> u8 {
    let k = if c { v.len() } else { n };
    if k > 0 { v[k - 1] } else { 0 }
}

#[cfg(signed_clamp_add)]
pub fn f(n: i64) -> u64 {
    let k: i64 = if n > 5 { 5 } else { n };
    (k as u64) + 10
}

#[cfg(signed_clamp_index)]
pub fn f(n: i64, a: &[u8; 26]) -> u8 {
    let k: i64 = if n > 25 { 25 } else { n };
    a[k as usize]
}

#[cfg(stale_yield_bound)]
pub fn f(n: usize, m: usize, a: &[u8; 26]) -> u8 {
    let mut r0 = 0..1usize;
    let mut o = r0.next();
    let mut s = 0u8;
    let mut c = false;
    let mut t = 0u32;
    loop {
        let k2 = if c { 26 } else { n };
        let e = k2 + 0;
        if c {
            if let Some(i) = o {
                s ^= a[i];
            }
        }
        let mut r = 0..e;
        let mut j = 0usize;
        while j < m {
            o = r.next();
            j += 1;
        }
        c = true;
        t += 1;
        if t > 1 {
            break;
        }
    }
    s
}

#[cfg(len_ssa)]
pub fn f(v: &Vec<u8>) -> u8 {
    let k = v.len();
    if k > 0 { v[k - 1] } else { 0 }
}

#[cfg(unsigned_clamp_cast)]
pub fn f(n: u32, a: &[u8; 26]) -> u8 {
    let k: u32 = if n > 25 { 25 } else { n };
    a[k as usize]
}

#[cfg(for_len)]
pub fn f(v: &Vec<u32>) -> u32 {
    let mut s = 0u32;
    for i in 0..v.len() {
        s = s.wrapping_add(v[i]);
    }
    s
}

#[cfg(get_join)]
pub fn f(s: &[u8], i: usize, c: bool) -> u8 {
    let o = if c { s.get(i) } else { Some(&0u8) };
    match o {
        Some(_) => s[i],
        None => 0,
    }
}

#[cfg(last_join)]
pub fn f(v: &Vec<u8>, r: &u8, c: bool) -> usize {
    let o = if c { v.last() } else { Some(r) };
    match o {
        Some(_) => v.len() - 1,
        None => 0,
    }
}

#[cfg(clamp_short_circuit)]
pub fn f(v: usize, w: bool, a: &[u8; 6]) -> u8 {
    let k: usize = if !w && v > 5 { 5 } else { v };
    a[k]
}

#[cfg(enumerate_stale)]
pub fn f(a: &[u8], ks: &[usize]) -> u8 {
    let z = [0u8; 0];
    let mut it0 = z.iter().enumerate();
    let mut o = it0.next();
    let mut acc = 0u8;
    for &k in ks {
        if k > a.len() {
            return 0;
        }
        let s = &a[..k];
        if let Some((i, _)) = o {
            acc = acc.wrapping_add(s[i]);
        }
        let mut it = s.iter().enumerate();
        o = it.next();
    }
    acc
}

#[cfg(get_ok)]
pub fn f(s: &[u8], i: usize) -> u8 {
    match s.get(i) {
        Some(_) => s[i],
        None => 0,
    }
}

#[cfg(last_ok)]
pub fn f(v: &Vec<u8>) -> usize {
    match v.last() {
        Some(_) => v.len() - 1,
        None => 0,
    }
}

#[cfg(store_through_bound)]
pub fn f(v: &mut [u32]) {
    for i in 0..v.len() {
        v[i] = v[i].wrapping_mul(3);
    }
}

#[cfg(repeated_decrement)]
pub fn f(a: &[u8]) -> u8 {
    let mut i = a.len();
    if i > 1 {
        i -= 1;
        i -= 1;
        i -= 1;
        return a[i];
    }
    0
}

#[cfg(short_circuit_decrement)]
pub fn f(a: &[u8], flag: bool) -> u8 {
    let mut i = a.len();
    if flag || i > 1 {
        i -= 1;
        return a[i - 1];
    }
    0
}

#[cfg(converging_break)]
pub fn f(s: &[u8], c: bool) -> u8 {
    let mut lo = 0usize;
    let mut hi = s.len();
    while lo < hi {
        hi -= 1;
        if c {
            break;
        }
        lo += 1;
    }
    s[lo]
}

#[cfg(reverse_loop)]
pub fn f(a: &[u8]) -> u32 {
    let mut i = a.len();
    let mut s = 0u32;
    while i > 1 {
        i -= 1;
        s = s.wrapping_add(a[i - 1] as u32);
    }
    s
}

#[cfg(frozen_copy_converging)]
pub fn f(s: &[u8]) -> u32 {
    let mut lo = 0usize;
    let mut hi = s.len();
    let l0 = lo;
    let mut acc = 0u32;
    while l0 < hi {
        hi -= 1;
        acc = acc.wrapping_add(s[lo] as u32);
        lo += 2;
    }
    acc
}

#[cfg(frozen_copy_downward)]
pub fn f(a: &[u8]) -> u32 {
    let mut j = a.len();
    let k = j;
    let mut s = 0u32;
    while k > 1 {
        if j == 0 {
            break;
        }
        j -= 1;
        s = s.wrapping_add(a[j - 1] as u32);
    }
    s
}

#[cfg(get_source_borrowed)]
pub fn f(s: &[u8], mut i: usize) -> u8 {
    let o = {
        let t = i;
        let p = &mut i;
        *p = 100;
        s.get(t)
    };
    match o {
        Some(_) => s[i],
        None => 0,
    }
}
