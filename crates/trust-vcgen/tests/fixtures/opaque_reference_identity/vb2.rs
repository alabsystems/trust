// Second batch of adversarial probes for OPAQUE-SCALAR-ID-1.
#![feature(f16)]
#![allow(clippy::all)]
#![allow(unused)]
use std::mem::transmute;

// R1: two promoted references compared as raw pointers. Always panics.
pub fn r1_promoted_ptrs() {
    let a: *const u16 = &1u16;
    let b: *const u16 = &2u16;
    if a != b {
        panic!("R1 promoted pointers differ");
    }
}

// R4: two f16 constants (Operand::Unsupported with identical kind/detail).
// r4_f16() always panics.
pub fn r4_f16() {
    let a = 1.0f16;
    let b = 2.0f16;
    if a != b {
        panic!("R4 f16 differ");
    }
}

// R5: a user local spelled like an opaque-scalar site symbol (must be demoted).
// r5_capture(&v, 0) panics.
pub fn r5_capture(r: &u8, k: usize) {
    let __trust_opaque_scalar_u64_b0_s2_o0 = k;
    let x = r as *const u8 as usize;
    if x != __trust_opaque_scalar_u64_b0_s2_o0 {
        panic!("R5 capture");
    }
}

pub const CA: &[u32] = &[1, 2];
pub const CB: &[u32] = &[3];

// R11: lengths of two different constant slices. Always panics.
pub fn r11_const_slices() {
    if CA.len() != CB.len() {
        panic!("R11 const slice lengths differ");
    }
}

// R12: pointers of two different constant slices. Always panics.
pub fn r12_const_slice_ptrs() {
    if CA.as_ptr() != CB.as_ptr() {
        panic!("R12 const slice pointers differ");
    }
}

// R13: element reads of two different constant slices. Always panics.
pub fn r13_const_slice_elems() {
    if CA[0] != CB[0] {
        panic!("R13 const slice elements differ");
    }
}

// R14: int-to-ptr in a loop, the previous iteration's pointer vs the current one.
// r14_loop_ptrs(&[1, 2]) panics.
pub fn r14_loop_ptrs(xs: &[usize]) {
    let mut prev = core::ptr::null::<u8>();
    let mut i = 0;
    while i < xs.len() {
        let p = xs[i] as *const u8;
        if i > 0 && p != prev {
            panic!("R14 differ");
        }
        prev = p;
        i += 1;
    }
}

// R15: recovered pointers through the std helper (a call at -O0, inlined at -O1).
// r15_with_exposed(1, 2) panics.
pub fn r15_with_exposed(x: usize, y: usize) {
    let p = core::ptr::with_exposed_provenance::<u8>(x);
    let q = core::ptr::with_exposed_provenance::<u8>(y);
    if p != q {
        panic!("R15 differ");
    }
}

// R16: recovered pointer offset arithmetic: `x as *const u8` vs `(x+1) as *const u8`.
// r16_offset(5) always panics.
pub fn r16_offset(x: usize) {
    let p = x as *const u8;
    let q = x.wrapping_add(1) as *const u8;
    if p != q {
        panic!("R16 differ");
    }
}

// R17: a recovered pointer vs a real reference's pointer (no address cast).
// r17_ref_vs_recovered(&v, 0) panics.
pub fn r17_ref_vs_recovered(r: &u8, k: usize) {
    let p = r as *const u8;
    let q = k as *const u8;
    if p != q {
        panic!("R17 differ");
    }
}

// R18: the bool form, through a helper-free comparison chain feeding an index.
// r18_index_chain(1, 2, &[0; 2]) panics with an out-of-bounds index.
pub fn r18_index_chain(x: usize, y: usize, t: &[u8; 2]) -> u8 {
    let same = (x as *const u8) == (y as *const u8);
    let i = same as usize * 0 + (!same) as usize * 7;
    t[i]
}
