// adv_ptrbound2: the H1 class (a projected / referent-folded range bound resolved
// globally and renamed at the CALL) through FIELDS: of a `&mut` parameter, of a local
// struct, and an exclusive pair. Every `_bug` panics on the input in its comment.
#![allow(clippy::all, unused_mut, unused_assignments, dead_code)]

pub struct St {
    pub len: usize,
}

// PB10: field behind a `&mut` param, read through a shared reborrow `z = &s.len`, the
// field rewritten directly after `z`'s last use. s.len=100, n=3 panics.
pub fn pb10_mut_param_field_bug(s: &mut St, buf: &[u8; 8], n: usize) -> usize {
    let z = &s.len;
    let r = ..*z;
    s.len = n;
    if s.len > 8 {
        return 0;
    }
    buf[r].len()
}

// PB11: field of a LOCAL struct through `z = &st.len`. m=100, n=3 panics.
pub fn pb11_local_struct_field_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut st = St { len: m };
    let z = &st.len;
    let r = ..*z;
    st.len = n;
    if st.len > 8 {
        return 0;
    }
    buf[r].len()
}

// PB12: exclusive pair `*a..*b` with `b = &hi`, `hi` rewritten. m=100, n=3 panics.
pub fn pb12_pair_folded_end_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let lo = 0usize;
    let mut hi = m;
    let a = &lo;
    let b = &hi;
    let r = *a..*b;
    hi = n;
    if hi > 8 {
        return 0;
    }
    buf[r].len()
}

// PB13: range-iterator end `*z`, `z = &s.len` of a `&mut` param, the field rewritten in
// the loop body. s.len=100, n=3 panics (i reaches 8).
pub fn pb13_yield_end_mut_param_field_bug(s: &mut St, buf: &[u8; 8], n: usize) -> u8 {
    let z = &s.len;
    let mut acc = 0;
    for i in 0..*z {
        s.len = n;
        if s.len > 8 {
            return acc;
        }
        acc ^= buf[i];
    }
    acc
}

// PB14: RangeFrom `*z..` with the guard on the NEW value of `len`. m=100, n=3 panics.
pub fn pb14_range_from_folded_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let z = &len;
    let r = *z..;
    len = n;
    if len > 8 {
        return 0;
    }
    buf[r].len()
}

// PB15 control: the guard tests the value the range was built from (correct).
pub fn pb15_folded_guard_first_ctl(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    if len > 8 {
        return 0;
    }
    let z = &len;
    let r = ..*z;
    len = n;
    buf[r].len() ^ len
}

// PB16: inclusive `..=*z` (the `collection_range` lane). m=100, n=3 panics.
pub fn pb16_inclusive_folded_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let z = &len;
    let r = ..=*z;
    len = n;
    if len > 7 {
        return 0;
    }
    buf[r].len()
}

// PB17: `(Bound::Included(*z), Bound::Unbounded)`. m=100, n=3 panics.
pub fn pb17_bound_pair_folded_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    use std::ops::Bound;
    let mut len = m;
    let z = &len;
    let r = (Bound::Included(*z), Bound::Unbounded);
    len = n;
    if len > 8 {
        return 0;
    }
    buf[r].len()
}

// PB18: a LOCAL copy `t = len` (whole, not projected) is the bound; `len` rewritten and
// guarded; the class-10 lane names `t` (single-valued, correct) -- control of the
// mechanism: expected NOT proved (t is unguarded), never certified.
pub fn pb18_local_copy_bound_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let t = len;
    let r = ..t;
    len = n;
    if len > 8 {
        return 0;
    }
    buf[r].len()
}
