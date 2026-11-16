// B'' reproducers: `usize as *const T` (PointerWithExposedProvenance) is lowered
// to ConstValue::OpaqueConst, which trust-vcgen renders as the ONE symbol
// `__unknown_const`. Safe code; each function panics on the input in its comment.

// q1_int_to_ptr(1, 2) panics.
pub fn q1_int_to_ptr(x: usize, y: usize) {
    let p = x as *const u8;
    let q = y as *const u8;
    if p != q {
        panic!("Q1 recovered pointers differ");
    }
}

// q4_recovered_vs_ref(&v, 0) panics (a live reference is never null).
pub fn q4_recovered_vs_ref(r: &u8, k: usize) {
    let p = k as *const u8;
    let q = (r as *const u8 as usize) as *const u8;
    if p != q {
        panic!("Q4 differ");
    }
}

// q6_assert_eq_ptr(1, 2) panics: the assert! form a user writes.
pub fn q6_assert_ptr(x: usize, y: usize) {
    assert!(x as *const u32 == y as *const u32, "Q6");
}

// q7_null_vs_recovered(5) panics: a recovered non-zero address is not null.
pub fn q7_null_vs_recovered(x: usize) {
    let p = x as *const u8;
    let n = 0usize as *const u8;
    if p != n {
        panic!("Q7 differ");
    }
}
