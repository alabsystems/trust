// foldfix adversarial aliasing probes (2026-10-07), for the change that answers a
// store through an ATTRIBUTED other pointer in pointer-reached memory by that
// pointer's provenance. Every `_bug` panics for every n; every `_ctl` never panics.
// Bug shape: `z` borrows `l[k]`, a store through `y` (attributed to a Deref place
// that really is `k`'s slot) moves `k`, `if k == k0 { return }` makes the VC's new
// `k` differ from the borrow-time one, then `t[*z]` reads the 9 stored through z.
#![allow(clippy::all, unused_mut)]
pub struct S {
    pub f: u8,
    pub g: u8,
}
#[repr(C)]
pub struct W {
    pub f: usize,
}

// 1. Box carries the pointer to `k`; `y` folds to `*bp`.
pub fn box_alias_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let mut l = [1usize; 4];
    let bx: Box<*mut usize> = Box::new(&raw mut k);
    let bp: *mut usize = *bx;
    let y: *mut usize = unsafe { &raw mut *bp };
    let z = &mut l[k];
    *z = 9;
    unsafe { *y = (k0 + 1) & 3 };
    if k == k0 {
        return 0;
    }
    t[*z]
}

// 2. Box-owned struct field stored through between two stores through `z`; `k`
// shared-borrowed. Safe; the fold of `z` must survive the attributed `(*bx).f`.
pub fn box_field_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut bx = Box::new(S { f: 0, g: 0 });
    std::hint::black_box(&bx);
    let k = n & 3;
    let rk = &k;
    let mut l = [0usize; 4];
    let y = &mut bx.f;
    let z = &mut l[k];
    *z = 2;
    *y = 3;
    *z = 2;
    t[l[k]] ^ (*rk as u8) ^ bx.g
}

// 3. Twin of 2: the last store through `z` writes 6, so `t[l[k]]` panics.
pub fn box_field_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut bx = Box::new(S { f: 0, g: 0 });
    std::hint::black_box(&bx);
    let k = n & 3;
    let rk = &k;
    let mut l = [0usize; 4];
    let y = &mut bx.f;
    let z = &mut l[k];
    *z = 2;
    *y = 3;
    *z = 6;
    t[l[k]] ^ (*rk as u8) ^ bx.g
}

// 4. Vec carries the pointer to `k`; `y` folds through the element read.
pub fn vec_alias_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let mut l = [1usize; 4];
    let mut v: Vec<*mut usize> = Vec::new();
    v.push(&raw mut k);
    let vp: *mut usize = v[0];
    let y: *mut usize = unsafe { &raw mut *vp };
    let z = &mut l[k];
    *z = 9;
    unsafe { *y = (k0 + 1) & 3 };
    if k == k0 {
        return 0;
    }
    t[*z]
}

// 5. A Vec element stored through via a slice reborrow; safe.
pub fn vec_slice_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut v = vec![0u8; 4];
    let k = n & 3;
    let rk = &k;
    let mut l = [0usize; 4];
    let s: &mut [u8] = &mut v[..];
    let y = &mut s[1];
    let z = &mut l[k];
    *z = 2;
    *y = 3;
    *z = 2;
    t[l[k]] ^ (*rk as u8) ^ v[1]
}

// 6. split_at_mut halves stored through between stores through `z`; safe.
pub fn split_ctl(n: usize, a: &mut [u8; 4], t: &[u8; 4]) -> u8 {
    let k = n & 3;
    let rk = &k;
    let mut l = [0usize; 4];
    let (lo, hi) = a.split_at_mut(2);
    let y = &mut lo[0];
    let w = &mut hi[1];
    let z = &mut l[k];
    *z = 2;
    *y = 3;
    *w = 4;
    *z = 2;
    t[l[k]] ^ (*rk as u8)
}

// 7. split_at_mut of a slice made from `&raw mut k`: the low half IS `k`.
pub fn split_alias_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let mut l = [1usize; 4];
    let s: &mut [usize] = unsafe { std::slice::from_raw_parts_mut(&raw mut k, 1) };
    let (lo, _hi) = s.split_at_mut(1);
    let y: *mut usize = &raw mut lo[0];
    let z = &mut l[k];
    *z = 9;
    unsafe { *y = (k0 + 1) & 3 };
    if k == k0 {
        return 0;
    }
    t[*z]
}

// 8. Reborrows in a loop through `&mut *p`; safe.
pub fn loop_reborrow_ctl(m: &mut S, n: usize, t: &[u8; 4]) -> u8 {
    let k = n & 3;
    let rk = &k;
    let mut l = [0usize; 4];
    let z = &mut l[k];
    *z = 2;
    let mut p: &mut S = m;
    let mut i = 0;
    while i < (n & 7) {
        let q = &mut *p;
        q.f = q.f.wrapping_add(1);
        p = q;
        i += 1;
    }
    *z = 2;
    t[l[k]] ^ (*rk as u8) ^ p.g
}

// 9. Reborrows in a loop of a raw pointer derived from `&raw mut k`.
pub fn loop_reborrow_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let mut l = [1usize; 4];
    let mut p: *mut usize = &raw mut k;
    let z = &mut l[k];
    *z = 9;
    let mut i = 0;
    while i < (n & 1) + 1 {
        let y: *mut usize = unsafe { &raw mut *p };
        unsafe { *y = (*y + 1) & 3 };
        p = y;
        i += 1;
    }
    if k == k0 {
        return 0;
    }
    t[*z]
}

// 10. A boxed pointer array walked in a loop; its second element is `&raw mut k`.
pub fn box_loop_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let mut l = [1usize; 4];
    let mut h = 0usize;
    let hp: *mut usize = &raw mut h;
    let kp: *mut usize = &raw mut k;
    let ptrs = Box::new([hp, kp]);
    let z = &mut l[k];
    *z = 9;
    let mut i = 0;
    while i < 2 {
        let q: *mut usize = ptrs[i];
        let y: *mut usize = unsafe { &raw mut *q };
        unsafe { *y = (*y + 1) & 3 };
        i += 1;
    }
    if k == k0 {
        return 0;
    }
    t[*z] ^ (h as u8)
}
