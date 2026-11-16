// adv_fold: the referent fold's D41a provenance arm (a store through an ATTRIBUTED other
// pointer asks that pointer's provenance) x carried facts / range rows, on the
// integrated tree. Shape (fx_adv.rs): `z` borrows `l[k]`, a store through `y` that
// really is `k`'s slot moves `k`, `if k == k0 { return }`, then a row reads through `z`.
// Every `_bug` panics for every n; every `_ctl` never panics.
#![allow(clippy::all, unused_mut, unused_assignments, dead_code)]

pub struct S {
    pub f: usize,
    pub g: u8,
}

// FD01: the pointer to `k` rides in a TUPLE field; `y = &raw mut *holder.0`.
pub fn fd01_tuple_holder_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let mut l = [1usize; 4];
    let holder: (*mut usize, u8) = (&raw mut k, 0);
    let y: *mut usize = unsafe { &raw mut *holder.0 };
    let z = &mut l[k];
    *z = 9;
    unsafe { *y = (k0 + 1) & 3 };
    if k == k0 {
        return 0;
    }
    t[*z]
}

// FD02: the pointer in an `Option`, taken out with `if let`.
pub fn fd02_option_holder_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let mut l = [1usize; 4];
    let o: Option<*mut usize> = Some(&raw mut k);
    let z = &mut l[k];
    *z = 9;
    if let Some(q) = o {
        let y: *mut usize = unsafe { &raw mut *q };
        unsafe { *y = (k0 + 1) & 3 };
    }
    if k == k0 {
        return 0;
    }
    t[*z]
}

// FD03: the pointer in a 2-element ARRAY, selected by a runtime index.
pub fn fd03_array_holder_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let mut h = 0usize;
    let mut l = [1usize; 4];
    let ptrs: [*mut usize; 2] = [&raw mut h, &raw mut k];
    let j = ((n >> 8) & 1) | 1;
    let z = &mut l[k];
    *z = 9;
    let y: *mut usize = unsafe { &raw mut *ptrs[j] };
    unsafe { *y = (k0 + 1) & 3 };
    if k == k0 {
        return 0;
    }
    t[*z] ^ (h as u8)
}

// FD04: the pointer to `k` rides in a Box'd TUPLE (unresolvable), `y = &raw mut *(*bx).1`.
pub fn fd04_box_tuple_holder_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let mut l = [1usize; 4];
    let bx: Box<(u8, *mut usize)> = Box::new((0, &raw mut k));
    let q: *mut usize = bx.1;
    let y: *mut usize = unsafe { &raw mut *q };
    let z = &mut l[k];
    *z = 9;
    unsafe { *y = (k0 + 1) & 3 };
    if k == k0 {
        return 0;
    }
    t[*z]
}

// FD05: box_field_ctl's shape with the index guard behind a `&raw const` borrow that is
// then cast to `*mut` and stored through (the guard's only borrow is the const one).
pub fn fd05_raw_const_cast_store_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut bx = Box::new(S { f: 0, g: 0 });
    std::hint::black_box(&bx);
    let mut k = n & 3;
    let k0 = k;
    let rk = &raw const k;
    let mut l = [1usize; 4];
    let y = &mut bx.f;
    let z = &mut l[k];
    *z = 9;
    *y = 3;
    let pk = rk as *mut usize;
    unsafe { *pk = (k0 + 1) & 3 };
    if k == k0 {
        return 0;
    }
    t[*z]
}

// FD06: control: FD04 with the Box holding a pointer to ANOTHER struct (correct).
pub fn fd06_box_other_struct_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut s = S { f: n & 3, g: 0 };
    let mut o = S { f: 0, g: 0 };
    let mut l = [0usize; 4];
    let bx: Box<*mut S> = Box::new(&raw mut o);
    let bp: *mut S = *bx;
    let y: *mut usize = unsafe { &raw mut (*bp).f };
    let z = &mut l[s.f];
    *z = 2;
    unsafe { *y = 7 };
    *z = 2;
    s.g = 1;
    t[l[s.f]] ^ s.g
}

// FD07: FD05 with the pointer made by `&raw mut k` and only TYPED `*const` before the
// cast back (no aliasing-model question: a `&raw mut` pointer may be written through).
pub fn fd07_raw_mut_as_const_store_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut bx = Box::new(S { f: 0, g: 0 });
    std::hint::black_box(&bx);
    let mut k = n & 3;
    let k0 = k;
    let rk: *const usize = &raw mut k;
    let mut l = [1usize; 4];
    let y = &mut bx.f;
    let z = &mut l[k];
    *z = 9;
    *y = 3;
    let pk = rk as *mut usize;
    unsafe { *pk = (k0 + 1) & 3 };
    if k == k0 {
        return 0;
    }
    t[*z]
}

// FD08: no referent fold at all: `&raw const k` cast to `*mut` and stored through, then
// `t[k]`. n=0 panics (k becomes 4).
pub fn fd08_raw_const_store_no_fold_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let rk = &raw const k;
    let pk = rk as *mut usize;
    unsafe { *pk = k0 + 4 };
    t[k]
}

// FD09: FD08 with `&raw mut k` typed `*const` (no aliasing-model question). n=0 panics.
pub fn fd09_raw_mut_typed_const_no_fold_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let rk: *const usize = &raw mut k;
    let pk = rk as *mut usize;
    unsafe { *pk = k0 + 4 };
    t[k]
}

// FD10: FD08 with a plain `&raw mut k` (the havoc'd baseline). n=0 panics.
pub fn fd10_raw_mut_store_no_fold_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let pk = &raw mut k;
    unsafe { *pk = k0 + 4 };
    t[k]
}
