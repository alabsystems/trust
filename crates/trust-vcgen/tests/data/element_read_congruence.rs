// Element-read congruence (G1 of the verifier-gaps design,
// trust-ir reports/2026-10-08-session-4b77663c/designs/trust-verifier-gaps-final.md,
// Appendix A.1-A.5). Two reads of one element of one base, with fresh index temps,
// must be tied when their indices agree; every `must_refute_*` body panics natively
// (-O0 and -O3) on the input in its comment and must keep refuting.
#![allow(clippy::all, unused_mut, unused_assignments, dead_code)]

// ---- A.1: positives and parameter-index counters ---------------------------
pub fn dec_first_nonzero(digits: &mut [u8]) {
    let mut i = 0;
    while i < digits.len() {
        if digits[i] > 0 {
            digits[i] -= 1;
            break;
        }
        digits[i] = 9;
        i += 1;
    }
}
pub fn guard_then_use(a: &[u8], i: usize) -> u8 {
    if i < a.len() && a[i] > 0 { a[i] - 1 } else { 0 }
}
pub fn equal_by_guard(a: &[u8], i: usize, j: usize) -> u8 {
    if i < a.len() && i == j && a[i] > 0 { a[j] - 1 } else { 0 }
}
// (&[1, 0], 0, 1) panics.
pub fn must_refute_other_index(a: &[u8], i: usize, j: usize) -> u8 {
    if i < a.len() && j < a.len() && a[i] > 0 { a[j] - 1 } else { 0 }
}
// (&[1], &[0], 0) panics.
pub fn must_refute_other_base(a: &[u8], b: &[u8], i: usize) -> u8 {
    if i < a.len() && i < b.len() && a[i] > 0 { b[i] - 1 } else { 0 }
}
// (&mut 1, &[true]) panics.
pub fn must_refute_loop_conditional_store_ptr(p: &mut u8, c: &[bool]) -> u8 {
    let mut n = 0;
    let mut acc = 0u8;
    while n < c.len() {
        let x = *p;
        if c[n] {
            *p = 0;
        }
        if x > 0 {
            acc = *p - 1;
        }
        n += 1;
    }
    acc
}

// ---- A.2: mutable index locals (one fresh index temp per read) ---------------
pub fn mut_guard_then_use(a: &mut [u8], k: usize) -> u8 {
    let mut i = k;
    if i >= a.len() {
        i = 0;
    }
    if i < a.len() && a[i] > 0 { a[i] - 1 } else { 0 }
}
// (&mut [1, 1], 0, &[true]) panics.
pub fn must_refute_loop_collision_temps(a: &mut [u8], k: usize, c: &[bool]) -> u8 {
    let mut i = 0usize;
    let mut n = 0;
    let mut acc = 0u8;
    while n < c.len() {
        if i < a.len() && k < a.len() {
            let x = a[i];
            if c[n] {
                a[k] = 0;
            }
            if x > 0 {
                acc = a[i] - 1;
            }
        }
        n += 1;
        if n > 1000 {
            i = n;
        }
    }
    acc
}
// (&mut [1, 1], 0) panics.
pub fn must_refute_store_between_temps(a: &mut [u8], k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    if i < a.len() && k < a.len() && a[i] > 0 {
        a[k] = 0;
        a[i] - 1
    } else {
        0
    }
}
// (&mut [1, 1], 0) panics.
pub fn must_refute_call_between_temps(a: &mut [u8], k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    if i < a.len() && a[i] > 0 {
        zero_all2(a);
        a[i] - 1
    } else {
        0
    }
}
#[inline(never)]
pub fn zero_all2(a: &mut [u8]) {
    for x in a.iter_mut() {
        *x = 0;
    }
}
// (&mut [1, 0], 1) panics.
pub fn must_refute_index_moved_temps(a: &mut [u8], j: usize) -> u8 {
    let mut i = 0usize;
    if i < a.len() && j < a.len() && a[i] > 0 {
        i = j;
        a[i] - 1
    } else {
        0
    }
}
// (&mut [1, 1], 0) panics.
pub fn must_refute_prev_iteration_temps(a: &mut [u8], k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    let mut ok = false;
    let mut n = 0;
    let mut acc = 0u8;
    while n < 3 {
        if i < a.len() {
            if ok {
                acc = a[i] - 1;
            }
            ok = a[i] > 0;
            a[i] = 0;
        }
        n += 1;
    }
    acc
}
// (&mut [1, 1], 0) panics.
pub fn must_refute_raw_alias_temps(a: &mut [u8], k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    let p = a.as_mut_ptr();
    if i < a.len() && k < a.len() && a[i] > 0 {
        unsafe {
            *p.add(k) = 0;
        }
        a[i] - 1
    } else {
        0
    }
}
// (&mut [1], &mut [0]) panics.
pub fn must_refute_other_base_temps(a: &mut [u8], b: &mut [u8]) -> u8 {
    let mut i = 0usize;
    if a.len() > 1000 {
        i = 1;
    }
    if i < a.len() && i < b.len() && a[i] > 0 { b[i] - 1 } else { 0 }
}
// (&mut [1], &mut [0]) panics.
pub fn must_refute_reseat_temps<'a>(mut a: &'a mut [u8], b: &'a mut [u8]) -> u8 {
    let mut i = 0usize;
    if a.len() > 1000 {
        i = 1;
    }
    if i < a.len() && i < b.len() && a[i] > 0 {
        a = b;
        a[i] - 1
    } else {
        0
    }
}
// (&mut [[1, 1], [1, 1]], 0) panics.
pub fn must_refute_nested_temps(a: &mut [[u8; 2]], k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    if i < a.len() && k < a.len() && a[i][1] > 0 {
        a[k][1] = 0;
        a[i][1] - 1
    } else {
        0
    }
}

// ---- A.3: shared-slice twins that prove today --------------------------------
pub fn imm_guard_then_use(a: &[u8], k: usize) -> u8 {
    let mut i = k;
    if i >= a.len() {
        i = 0;
    }
    if i < a.len() && a[i] > 0 { a[i] - 1 } else { 0 }
}
pub fn imm_first_nonzero_pred(digits: &[u8]) -> u8 {
    let mut i = 0;
    while i < digits.len() {
        if digits[i] > 0 {
            return digits[i] - 1;
        }
        i += 1;
    }
    0
}

// ---- A.4: reseats and copies of the base -------------------------------------
// (&mut [1], &mut [0], 0) panics.
pub fn must_refute_two_reborrows_across_reseat<'a>(
    mut a: &'a mut [u8],
    b: &'a mut [u8],
    k: usize,
) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    let r1: &[u8] = &*a;
    let g = if i < r1.len() { r1[i] } else { 0 };
    a = b;
    let r2: &[u8] = &*a;
    if g > 0 && i < r2.len() { r2[i] - 1 } else { 0 }
}
// (&mut [0], &mut [1], 0) returns 0.
pub fn reseated_root_then_guard_then_use<'a>(
    mut a: &'a mut [u8],
    b: &'a mut [u8],
    k: usize,
) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    a = b;
    if i < a.len() && a[i] > 0 { a[i] - 1 } else { 0 }
}
// (&mut [1], 0, 0) returns 0.
pub fn mut_equal_by_guard(a: &mut [u8], i: usize, j: usize) -> u8 {
    if i < a.len() && i == j && a[i] > 0 { a[j] - 1 } else { 0 }
}
// (&[1], &[0], 0) panics.
pub fn must_refute_copy_then_reseat<'a>(mut a: &'a [u8], b: &'a [u8], k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    let r1: &[u8] = a;
    a = b;
    if i < r1.len() && i < a.len() && r1[i] > 0 { a[i] - 1 } else { 0 }
}

// ---- A.5: write channels between the two reads (each panics on its input) ----
// (&mut [1, 1], 0)
pub fn must_refute_reborrow_store_temps(a: &mut [u8], k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    if i < a.len() && k < a.len() && a[i] > 0 {
        let r: &mut [u8] = &mut *a;
        r[k] = 0;
        a[i] - 1
    } else {
        0
    }
}
// (&mut [1, 1], 0)
pub fn must_refute_elem_ref_store_temps(a: &mut [u8], k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    if i < a.len() && k < a.len() && a[i] > 0 {
        let r: &mut u8 = &mut a[k];
        *r = 0;
        a[i] - 1
    } else {
        0
    }
}
// (&mut [1, 1], 0)
pub fn must_refute_ptr_write_temps(a: &mut [u8], k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    if i < a.len() && k < a.len() && a[i] > 0 {
        unsafe { core::ptr::write(a.as_mut_ptr().add(k), 0) };
        a[i] - 1
    } else {
        0
    }
}
// (&mut [1, 1], 0, &[true])
pub fn must_refute_loop_elem_ref_collision(a: &mut [u8], k: usize, c: &[bool]) -> u8 {
    let mut i = 0usize;
    let mut n = 0;
    let mut acc = 0u8;
    while n < c.len() {
        if i < a.len() && k < a.len() {
            let x = a[i];
            if c[n] {
                let r = &mut a[k];
                *r = 0;
            }
            if x > 0 {
                acc = a[i] - 1;
            }
        }
        n += 1;
        if n > 1000 {
            i = n;
        }
    }
    acc
}
pub struct H<'a> {
    pub s: &'a mut [u8],
}
// h = H { s: &mut [1, 1] }, k = 0
pub fn must_refute_field_slice_store(h: &mut H, k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    if i < h.s.len() && k < h.s.len() && h.s[i] > 0 {
        h.s[k] = 0;
        h.s[i] - 1
    } else {
        0
    }
}
// h = H { s: &mut [1, 1] }, k = 0
pub fn must_refute_field_slice_reborrow_store(h: &mut H, k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    if i < h.s.len() && k < h.s.len() && h.s[i] > 0 {
        let r: &mut [u8] = &mut *h.s;
        r[k] = 0;
        h.s[i] - 1
    } else {
        0
    }
}

// ---- a read only a LATER conjunct names (review of 95449037cd, 2026-10-22) ----------
// `match a[i]` switches on the element itself (`switchInt(copy (*a)[_12])`), so the
// `Sub` row's path guard is the only conjunct naming the guard's read, and the safety
// and hardened lanes conjoin it after the global facts.
pub fn mut_match_then_use(a: &mut [u8], k: usize) -> u8 {
    let mut i = k;
    if i >= a.len() {
        i = 0;
    }
    if i < a.len() {
        match a[i] {
            0 => 0,
            _ => a[i] - 1,
        }
    } else {
        0
    }
}
// (&mut [1], 0) panics.
pub fn must_refute_match_store_between(a: &mut [u8], k: usize) -> u8 {
    let mut i = 0usize;
    if k > 1000 {
        i = k;
    }
    if i < a.len() && k < a.len() {
        match a[i] {
            0 => 0,
            _ => {
                a[k] = 0;
                a[i] - 1
            }
        }
    } else {
        0
    }
}
// (&mut [1, 0], 0, 1) panics.
pub fn must_refute_match_other_index(a: &mut [u8], i: usize, j: usize) -> u8 {
    if i < a.len() && j < a.len() {
        match a[i] {
            0 => 0,
            _ => a[j] - 1,
        }
    } else {
        0
    }
}
