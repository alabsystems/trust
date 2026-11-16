#![allow(dead_code, unused_assignments, unreachable_code, unconditional_panic)]

struct Holder { items: [u32; 1] }

pub fn reference_index_order() -> u32 {
    let mut a = [0u32; 1];
    let p = &mut a;
    let mut n = 0u32;
    p[{ n = n * 10 + 1; 0 }] = { n = n * 10 + 2; 7 };
    n
}

pub fn reference_index_return() -> u32 {
    let mut a = [0u32; 1];
    let p = &mut a;
    let mut n = 0u32;
    p[{ n += 1; 0 }] = { return n + 9 };
    n
}

pub fn reference_bounds_return() -> u32 {
    let mut a = [0u32; 1];
    let p = &mut a;
    p[1] = { return 9 };
    0
}

pub fn ssa_fallback_once() -> u32 {
    let mut a = [0u32; 1];
    let mut n = 0u32;
    a[{ n = n * 10 + 1; 0 }] = { n = n * 10 + 2; 7 };
    n
}

pub fn field_fallback_once() -> u32 {
    let mut h = Holder { items: [0] };
    let mut n = 0u32;
    h.items[0] = { n += 1; 7 };
    n
}

pub fn field_index_order() -> u32 {
    let mut h = Holder { items: [0] };
    let p = &mut h;
    let mut n = 0u32;
    p.items[{ n = n * 10 + 1; 0 }] = { n = n * 10 + 2; 7 };
    n
}

pub fn reference_retarget() -> u32 {
    let mut a = [0u32; 1];
    let mut b = [0u32; 1];
    let mut p = &mut a;
    p[0] = { p = &mut b; 7 };
    a[0] * 10 + b[0]
}

pub fn index_return_after_rhs() -> u32 {
    let mut a = [0u32; 1];
    let p = &mut a;
    let mut n = 0u32;
    p[{ return n + 9; 0 }] = { n += 2; 7 };
    0
}

pub fn nested_rhs_once() -> u32 {
    let mut a = [0u32; 1];
    let p = &mut a;
    let mut b = [0u32; 1];
    let mut n = 0u32;
    p[{ n = n * 10 + 3; 0 }] = {
        b[0] = { n = n * 10 + 1; 7 };
        n = n * 10 + 2;
        7
    };
    n
}

pub fn nested_index_once() -> u32 {
    let mut a = [0u32; 1];
    let p = &mut a;
    let mut b = [0u32; 1];
    let mut n = 0u32;
    p[{
        b[0] = { n = n * 10 + 2; 7 };
        n = n * 10 + 3;
        0
    }] = { n = n * 10 + 1; 7 };
    n
}
