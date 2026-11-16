// adv_ptrbound: a range bound (or a range-iterator end) read from a place BEHIND a
// pointer, resolved by the GLOBAL resolver (`resolve_range_bound_formula`'s projected
// arm: root single-valued, no projected write ROOTED AT IT) and versioned at the call by
// the `1e` arm -- while the place is rewritten through ANOTHER local (a copy of the
// pointer, an aliasing raw pointer, a referent-folded `&mut`) between the read into the
// range and the call, and a guard tests the NEW value.
// Every `_bug` panics on the input in its comment; every `_ctl` is correct on every input.
#![allow(clippy::all, unused_mut, unused_assignments)]

#[repr(C)]
pub struct St {
    pub len: usize,
}

// PB01: range from `(*p).len`; rewritten through a COPY `q` of `p`; guard on `(*p).len`.
// p -> St { len: 100 }, n=3 panics.
pub unsafe fn pb01_ptr_copy_write_range_bug(p: *mut St, buf: &[u8; 8], n: usize) -> usize {
    unsafe {
        let r = ..(*p).len;
        let q = p;
        (*q).len = n;
        if (*p).len > 8 {
            return 0;
        }
        buf[r].len()
    }
}

// PB02: as PB01 but `q` is a SECOND parameter that aliases `p`.
// p == q -> St { len: 100 }, n=3 panics.
pub unsafe fn pb02_alias_param_write_range_bug(
    p: *const St,
    q: *mut St,
    buf: &[u8; 8],
    n: usize,
) -> usize {
    unsafe {
        let r = ..(*p).len;
        (*q).len = n;
        if (*p).len > 8 {
            return 0;
        }
        buf[r].len()
    }
}

// PB03: range-ITERATOR end `(*p).len` (evaluated once); rewritten in the body through a
// copy `q`; guard on the new `(*p).len`; `buf[i]` with the old end.
// p -> St { len: 100 }, n=3 panics (i reaches 8).
pub unsafe fn pb03_yield_end_ptr_copy_bug(p: *mut St, buf: &[u8; 8], n: usize) -> u8 {
    unsafe {
        let q = p;
        let mut acc = 0;
        for i in 0..(*p).len {
            (*q).len = n;
            if (*p).len > 8 {
                return acc;
            }
            acc ^= buf[i];
        }
        acc
    }
}

// PB04: range from `*z` with `z = &mut len` (referent-folded to `len`), `len` written
// DIRECTLY after `z`'s last use, guard on the new `len`.
// m=100, n=3 panics.
pub fn pb04_folded_ref_bound_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let z = &mut len;
    let r = ..*z;
    len = n;
    if len > 8 {
        return 0;
    }
    buf[r].len()
}

// PB05: shared-reference twin of PB04 (`z = &len`).  m=100, n=3 panics.
pub fn pb05_shared_ref_bound_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let z = &len;
    let r = ..*z;
    len = n;
    if len > 8 {
        return 0;
    }
    buf[r].len()
}

// PB06: range-iterator end through a folded shared ref, `len` rewritten in the loop
// body after `z`'s last use, guard on the new value.  m=100, n=3 panics (i reaches 8).
pub fn pb06_yield_end_folded_ref_bug(buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let z = &len;
    let mut acc = 0;
    for i in 0..*z {
        len = n;
        if len > 8 {
            return acc;
        }
        acc ^= buf[i];
    }
    acc
}

// PB07: range bound from a struct FIELD of a LOCAL (not behind a pointer), the field
// rewritten after the range is built, guard on the new field value.
// m=100, n=3 panics.
pub fn pb07_local_field_bound_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut s = St { len: m };
    let r = ..s.len;
    s.len = n;
    if s.len > 8 {
        return 0;
    }
    buf[r].len()
}

// PB08: a tuple local's field as the bound, rewritten whole.  m=100, n=3 panics.
pub fn pb08_tuple_whole_write_bound_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut t = (m, 0u8);
    let r = ..t.0;
    t = (n, 1);
    if t.0 > 8 {
        return 0;
    }
    buf[r].len()
}

// PB09 control: PB01 with the guard BEFORE the range read (correct).
pub unsafe fn pb09_ptr_guard_first_ctl(p: *mut St, buf: &[u8; 8], n: usize) -> usize {
    unsafe {
        if (*p).len > 8 {
            return 0;
        }
        let r = ..(*p).len;
        let q = p;
        (*q).len = n;
        buf[r].len()
    }
}
