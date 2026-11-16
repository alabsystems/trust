// Adversarial verification probes for fix/opaque-scalar-identity (OPAQUE-SCALAR-ID-1).
// Every `vb_*_bug` function panics on the input named in its comment; every
// `vb_c*` function is a correct program (a control).
#![allow(clippy::all)]
#![allow(unused)]
use std::mem::{size_of, transmute};

// ---------------------------------------------------------------- loops
// L1: one site executed on two iterations; the previous iteration's address is
// carried in `prev`. vb_l1_prev_addr_bug(&[1, 2]) panics (two distinct addresses).
pub fn vb_l1_prev_addr_bug(xs: &[u8]) {
    let mut prev = 0usize;
    let mut i = 0;
    while i < xs.len() {
        let a = &xs[i] as *const u8 as usize;
        if i > 0 && a != prev {
            panic!("L1 addresses differ");
        }
        prev = a;
        i += 1;
    }
}

// L2: the first iteration's address is saved and compared with a later one.
// vb_l2_first_addr_bug(&[1, 2]) panics.
pub fn vb_l2_first_addr_bug(xs: &[u8]) {
    let mut first = 0usize;
    let mut i = 0;
    while i < xs.len() {
        let a = &xs[i] as *const u8 as usize;
        if i == 0 {
            first = a;
        } else if a != first {
            panic!("L2 addresses differ");
        }
        i += 1;
    }
}

// L3: float bits of consecutive elements. vb_l3_prev_bits_bug(&[1.0, 2.0]) panics.
pub fn vb_l3_prev_bits_bug(fs: &[f32]) {
    let mut prev = 0u32;
    let mut i = 0;
    while i < fs.len() {
        let b: u32 = unsafe { transmute::<f32, u32>(fs[i]) };
        if i > 0 && b != prev {
            panic!("L3 bits differ");
        }
        prev = b;
        i += 1;
    }
}

// L4: an array filled by one transmute site in a loop.
// vb_l4_array_fill_bug(&[[1, 2, 3, 4], [0; 4]]) panics.
pub fn vb_l4_array_fill_bug(ps: &[[u8; 4]; 2]) {
    let mut buf = [0u32; 2];
    let mut i = 0;
    while i < 2 {
        buf[i] = unsafe { transmute::<[u8; 4], u32>(ps[i]) };
        i += 1;
    }
    if buf[0] != buf[1] {
        panic!("L4 packs differ");
    }
}

// L5: the loop's last address vs the address taken before the loop.
// vb_l5_last_vs_first_bug(&[1, 2]) panics.
pub fn vb_l5_last_vs_first_bug(xs: &[u8]) {
    if xs.len() < 2 {
        return;
    }
    let first = &xs[0] as *const u8 as usize;
    let mut last = first;
    let mut i = 1;
    while i < xs.len() {
        last = &xs[i] as *const u8 as usize;
        i += 1;
    }
    if last != first {
        panic!("L5 last != first");
    }
}

// L6: two-element loop that keeps BOTH iterations' bits in two locals.
// vb_l6_two_slots_bug(&[1.0, 2.0]) panics.
pub fn vb_l6_two_slots_bug(fs: &[f32; 2]) {
    let mut s0 = 0u32;
    let mut s1 = 0u32;
    let mut i = 0;
    while i < 2 {
        let b: u32 = unsafe { transmute::<f32, u32>(fs[i]) };
        if i == 0 {
            s0 = b;
        } else {
            s1 = b;
        }
        i += 1;
    }
    if s0 != s1 {
        panic!("L6 slots differ");
    }
}

// ---------------------------------------------------------------- helpers
#[inline(never)]
fn addr_of(r: &u8) -> usize {
    r as *const u8 as usize
}

// H1: one helper site, two calls. vb_h1_helper_twice_bug(&a, &b) panics.
pub fn vb_h1_helper_twice_bug(a: &u8, b: &u8) {
    let x = addr_of(a);
    let y = addr_of(b);
    if x != y {
        panic!("H1 helper addresses differ");
    }
}

// H2: one closure site, two calls. vb_h2_closure_twice_bug(&a, &b) panics.
pub fn vb_h2_closure_twice_bug(a: &u8, b: &u8) {
    let f = |r: &u8| r as *const u8 as usize;
    let x = f(a);
    let y = f(b);
    if x != y {
        panic!("H2 closure addresses differ");
    }
}

#[inline(always)]
fn sz<T>() -> usize {
    const { size_of::<T>() }
}

// H3: one generic helper's const block at two instantiations.
// vb_h3_generic_size_bug::<u8, u32>() panics.
pub fn vb_h3_generic_size_bug<T, U>() {
    let a = sz::<T>();
    let b = sz::<U>();
    if a != b {
        panic!("H3 sizes differ");
    }
}

pub trait Tr {
    const C: usize;
}
pub struct One;
pub struct Two;
impl Tr for One {
    const C: usize = 1;
}
impl Tr for Two {
    const C: usize = 2;
}

// H4: two associated consts through locals. vb_h4_assoc_bug::<One, Two>() panics.
pub fn vb_h4_assoc_bug<T: Tr, U: Tr>() {
    let a = T::C;
    let b = U::C;
    if a != b {
        panic!("H4 assoc consts differ");
    }
}

// H5: one assoc const inside a generic helper, two instantiations, -O1 inlined.
#[inline(always)]
fn assoc_of<T: Tr>() -> usize {
    T::C
}
// vb_h5_assoc_helper_bug::<One, Two>() panics.
pub fn vb_h5_assoc_helper_bug<T: Tr, U: Tr>() {
    let a = assoc_of::<T>();
    let b = assoc_of::<U>();
    if a != b {
        panic!("H5 assoc consts differ");
    }
}

// ---------------------------------------------------------------- B'' opaque references
// Q1: `usize as *const u8` (PointerWithExposedProvenance) twice. Safe code.
// vb_q1_int_to_ptr_bug(1, 2) panics.
pub fn vb_q1_int_to_ptr_bug(x: usize, y: usize) {
    let p = x as *const u8;
    let q = y as *const u8;
    if p != q {
        panic!("Q1 recovered pointers differ");
    }
}

pub static SA: u8 = 1;
pub static SB: u8 = 2;

// Q2: two statics' addresses. vb_q2_two_statics_bug() always panics.
pub fn vb_q2_two_statics_bug() {
    let p = &SA as *const u8;
    let q = &SB as *const u8;
    if p != q {
        panic!("Q2 statics differ");
    }
}

// Q3: two promoted slices of different lengths. vb_q3_promoted_bug() always panics.
pub fn vb_q3_promoted_bug() {
    let a: &[u8] = &[1, 2];
    let b: &[u8] = &[3, 4, 5];
    if a.len() != b.len() {
        panic!("Q3 lengths differ");
    }
}

// Q4: recovered pointer compared after a round trip through two different ints.
// vb_q4_recovered_vs_ref_bug(&v, 0) panics (a live reference is never null).
pub fn vb_q4_recovered_vs_ref_bug(r: &u8, k: usize) {
    let p = k as *const u8;
    let q = (r as *const u8 as usize) as *const u8;
    if p != q {
        panic!("Q4 differ");
    }
}

// Q5: two statics read through raw pointers; the values differ.
// vb_q5_static_values_bug() always panics.
pub fn vb_q5_static_values_bug() {
    let p = &SA as *const u8;
    let q = &SB as *const u8;
    let (a, b) = unsafe { (*p, *q) };
    if a == b {
        return;
    }
    panic!("Q5 static values differ");
}

// ---------------------------------------------------------------- controls (correct programs)
// C1: a copied address equals itself.
pub fn vb_c1_copy_tie(r: &u8) -> usize {
    let x = r as *const u8 as usize;
    let y = x;
    if x != y {
        panic!("C1 unreachable");
    }
    x
}

// C2: inside a loop, one iteration's address equals its own copy.
pub fn vb_c2_loop_copy_tie(xs: &[u8]) -> usize {
    let mut acc = 0usize;
    let mut i = 0;
    while i < xs.len() {
        let a = &xs[i] as *const u8 as usize;
        let b = a;
        if a != b {
            panic!("C2 unreachable");
        }
        acc = acc.wrapping_add(b);
        i += 1;
    }
    acc
}

// C3: an index reduced modulo the table length is in bounds.
pub fn vb_c3_mod_index(r: &u8, t: &[u8; 4]) -> u8 {
    let k = (r as *const u8 as usize) % 4;
    t[k]
}

// C4: float bits masked to the table length are in bounds.
pub fn vb_c4_bits_mask(f: f32, t: &[u8; 16]) -> u8 {
    let b: u32 = unsafe { transmute::<f32, u32>(f) };
    t[(b & 15) as usize]
}

// C5: one associated const read twice is one value.
pub fn vb_c5_assoc_twice<T: Tr>() {
    let a = T::C;
    let b = T::C;
    if a != b {
        panic!("C5 unreachable");
    }
}

// C6: a recovered pointer equals its own copy.
pub fn vb_c6_ptr_self(x: usize) {
    let p = x as *const u8;
    let q = p;
    if p != q {
        panic!("C6 unreachable");
    }
}

// C7: in a loop, the bits of the current element are compared with themselves
// after a round trip through a second local.
pub fn vb_c7_loop_bits_self(fs: &[f32]) -> u32 {
    let mut acc = 0u32;
    let mut i = 0;
    while i < fs.len() {
        let b: u32 = unsafe { transmute::<f32, u32>(fs[i]) };
        let c = b;
        if b != c {
            panic!("C7 unreachable");
        }
        acc ^= c;
        i += 1;
    }
    acc
}
