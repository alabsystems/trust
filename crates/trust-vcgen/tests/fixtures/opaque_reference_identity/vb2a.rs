// Adversarial round-2 verification probes for fix/opaque-scalar-identity
// (OPAQUE-SCALAR-ID-1 + OPAQUE-REF-ID-1). Every `*_bug` function panics on the
// input named in its comment; every `*_ctl` function is a correct program.
#![allow(clippy::all)]
#![allow(unused)]
use core::mem::size_of;
use core::ptr;

// ------------------------------------------------ opaque REFERENCES in loops
// (OpaqueConst carries no UnsupportedMir row, so nothing contains a false proof.)

// N1: recovered pointers written to two array slots by ONE site in a loop.
// n1_recovered_array_slots_bug(&[1, 2]) panics.
pub fn n1_recovered_array_slots_bug(xs: &[usize; 2]) {
    let mut ps: [*const u8; 2] = [ptr::null(); 2];
    let mut i = 0;
    while i < 2 {
        ps[i] = xs[i] as *const u8;
        i += 1;
    }
    if ps[0] != ps[1] {
        panic!("N1 slots differ");
    }
}

pub struct Two {
    pub a: *const u8,
    pub b: *const u8,
}

// N2: one site's two executions kept in two struct fields.
// n2_recovered_fields_bug(&[1, 2]) panics.
pub fn n2_recovered_fields_bug(xs: &[usize; 2]) {
    let mut s = Two { a: ptr::null(), b: ptr::null() };
    let mut i = 0;
    while i < 2 {
        let p = xs[i] as *const u8;
        if i == 0 {
            s.a = p;
        } else {
            s.b = p;
        }
        i += 1;
    }
    if s.a != s.b {
        panic!("N2 fields differ");
    }
}

// N3: the first iteration's recovered pointer carried in an Option.
// n3_recovered_option_carry_bug(&[1, 2]) panics.
pub fn n3_recovered_option_carry_bug(xs: &[usize]) {
    let mut saved: Option<*const u8> = None;
    let mut i = 0;
    while i < xs.len() {
        let p = xs[i] as *const u8;
        match saved {
            Some(s) => {
                if s != p {
                    panic!("N3 carried differs");
                }
            }
            None => saved = Some(p),
        }
        i += 1;
    }
}

// N4: an index decided by a loop-carried recovered-pointer comparison.
// n4_recovered_loop_index_bug(&[1, 2], &[0; 4]) panics (index 9 out of bounds).
pub fn n4_recovered_loop_index_bug(xs: &[usize], t: &[u8; 4]) -> u8 {
    let mut acc = 0u8;
    let mut prev: *const u8 = ptr::null();
    let mut i = 0;
    while i < xs.len() {
        let cur = xs[i] as *const u8;
        if i > 0 {
            acc ^= t[if cur == prev { 0 } else { 9 }];
        }
        prev = cur;
        i += 1;
    }
    acc
}

// ------------------------------------------------ fn items: one def, two instances
#[inline(never)]
pub fn gsize<T>() -> usize {
    size_of::<T>()
}

// N5: two instances of ONE generic fn item, reified, compared with `!=`.
// n5_fn_instances_ne_bug() always panics (the two bodies return 1 and 8).
pub fn n5_fn_instances_ne_bug() {
    let f: fn() -> usize = gsize::<u8>;
    let g: fn() -> usize = gsize::<u64>;
    if f != g {
        panic!("N5 instances differ");
    }
}

// N6: the same through `ptr::fn_addr_eq`, generic caller.
// n6_fn_instances_addr_eq_bug::<u8, u64>() panics.
pub fn n6_fn_instances_addr_eq_bug<T, U>() {
    let f: fn() -> usize = gsize::<T>;
    let g: fn() -> usize = gsize::<U>;
    if !ptr::fn_addr_eq(f, g) {
        panic!("N6 instances differ");
    }
}

// N7: an index decided by fn-pointer equality of two instances.
// n7_fn_instances_index_bug(&[0; 4]) always panics (index 9).
pub fn n7_fn_instances_index_bug(t: &[u8; 4]) -> u8 {
    let f: fn() -> usize = gsize::<u8>;
    let g: fn() -> usize = gsize::<u64>;
    t[if f == g { 0 } else { 9 }]
}

// N8: a divisor decided by fn-pointer equality of two instances.
// n8_fn_instances_div_bug() always panics (division by zero).
pub fn n8_fn_instances_div_bug() -> u32 {
    let f: fn() -> usize = gsize::<u8>;
    let g: fn() -> usize = gsize::<u64>;
    100 / if f == g { 1 } else { 0 }
}

// N9: calling the two instances through their pointers.
// n9_fn_instances_call_bug() always panics (1 != 8).
pub fn n9_fn_instances_call_bug() {
    let f: fn() -> usize = gsize::<u8>;
    let g: fn() -> usize = gsize::<u64>;
    if f() != g() {
        panic!("N9 results differ");
    }
}

// ------------------------------------------------ controls (correct programs)

// C1: two expose casts of the SAME pointer at two sites. Never panics.
pub fn n_c1_two_exposes_same_ptr_ctl(r: &u8) {
    let a = r as *const u8 as usize;
    let b = r as *const u8 as usize;
    if a != b {
        panic!("C1");
    }
}

// C2: a recovered pointer copied, compared with its copy in a loop. Never panics.
pub fn n_c2_loop_copy_ctl(xs: &[usize]) {
    let mut i = 0;
    while i < xs.len() {
        let p = xs[i] as *const u8;
        let q = p;
        if p != q {
            panic!("C2");
        }
        i += 1;
    }
}

// C3: same keyed constant read twice. Never panics.
pub fn n_c3_same_key_twice_ctl<T>() {
    let a = size_of::<T>();
    let b = size_of::<T>();
    if a != b {
        panic!("C3");
    }
}

// C4: one fn instance reified twice. Never panics (one function, one address
// within one codegen unit).
pub fn n_c4_one_instance_twice_ctl() {
    let f: fn() -> usize = gsize::<u8>;
    let g: fn() -> usize = gsize::<u8>;
    if f() != g() {
        panic!("C4");
    }
}

// C5: an index computed from a keyed constant compared with itself. Never panics.
pub fn n_c5_keyed_index_ctl<T>(t: &[u8; 4]) -> u8 {
    let a = size_of::<T>();
    let b = size_of::<T>();
    t[if a == b { 0 } else { 9 }]
}
