//@ needs-trust-verify
//@ edition: 2021
//@ revisions: reloaded_pointer_index reloaded_pointer_range_end reloaded_pointer_range_div param_store_frame_local
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[reloaded_pointer_index] check-fail
//@[reloaded_pointer_range_end] check-fail
//@[reloaded_pointer_range_div] check-fail
//@[param_store_frame_local] check-pass
//! Review round 111 (2026-10-10, pre-existing): a store through a RELOADED pointer to
//! a pointer (`**pp = v`, MIR `_10 = copy (*_5); (*_10) = v`) did not rebind the
//! referent's interval, and the stale interval of a copy of it discharged the bounds
//! row. Each revision VERIFIED kernel-certified on stage-1 sa157 and panics:
//! `f(&[1; 26], 26)`, `g(&[1; 26])`, `h(&[1; 13])`. Round 112: the control
//! `param_store_frame_local` keeps its proof, since a store through a never-reseated `&mut`
//! parameter cannot reach a local of the frame.

#[cfg(reloaded_pointer_index)]
pub fn f(a: &[u8; 26], v: usize) -> u8 {
    let mut m = 25usize;
    let mut q = &mut m;
    let pp = &mut q;
    **pp = v;
    a[m / 1]
}

#[cfg(reloaded_pointer_range_end)]
pub fn g(a: &[u8; 26]) -> u8 {
    let mut m = 26usize;
    let p: &mut usize = &mut m;
    let pp = &mut &mut *p;
    **pp = 100;
    let mut t = 0u8;
    for i in 0..m {
        t ^= a[i];
    }
    t
}

#[cfg(reloaded_pointer_range_div)]
pub fn h(a: &[u8; 13]) -> u8 {
    let mut m = 26usize;
    let p: &mut usize = &mut m;
    let pp = &mut &mut *p;
    **pp = 100;
    let mut t = 0u8;
    for i in 0..(m / 2) {
        t ^= a[i];
    }
    t
}

#[cfg(param_store_frame_local)]
pub fn k(a: &[u8; 8], v: &mut usize, w: usize) -> u8 {
    let mut m = 3usize;
    let r = &mut m;
    *r = 5;
    *v = w;
    a[m / 1]
}
