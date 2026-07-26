// Family: stdlib enum predicates breadth.
// Ordering::{is_lt,is_le,is_gt,is_ge,is_eq,is_ne}, ControlFlow::<i32,i32>::{is_break,is_continue},
// Poll::<i32>::{is_ready,is_pending}, Bound::<i32> matches! forms, Result::<i32,u8> matches!(Ok(_)),
// plus 3 distinct 2-variant user enums via matches!.

use std::cmp::Ordering;
use std::ops::{Bound, ControlFlow};
use std::task::Poll;

// --- Ordering predicates ---
#[inline(never)]
pub fn w_ord_is_lt(o: Ordering) -> bool {
    o.is_lt()
}
#[inline(never)]
pub fn w_ord_is_le(o: Ordering) -> bool {
    o.is_le()
}
#[inline(never)]
pub fn w_ord_is_gt(o: Ordering) -> bool {
    o.is_gt()
}
#[inline(never)]
pub fn w_ord_is_ge(o: Ordering) -> bool {
    o.is_ge()
}
#[inline(never)]
pub fn w_ord_is_eq(o: Ordering) -> bool {
    o.is_eq()
}
#[inline(never)]
pub fn w_ord_is_ne(o: Ordering) -> bool {
    o.is_ne()
}

// --- ControlFlow predicates ---
#[inline(never)]
pub fn w_cf_is_break(c: ControlFlow<i32, i32>) -> bool {
    c.is_break()
}
#[inline(never)]
pub fn w_cf_is_continue(c: ControlFlow<i32, i32>) -> bool {
    c.is_continue()
}

// --- Poll predicates ---
#[inline(never)]
pub fn w_poll_is_ready(p: Poll<i32>) -> bool {
    p.is_ready()
}
#[inline(never)]
pub fn w_poll_is_pending(p: Poll<i32>) -> bool {
    p.is_pending()
}

// --- Bound matches! forms ---
#[inline(never)]
pub fn w_bound_is_included(b: Bound<i32>) -> bool {
    matches!(b, Bound::Included(_))
}
#[inline(never)]
pub fn w_bound_is_excluded(b: Bound<i32>) -> bool {
    matches!(b, Bound::Excluded(_))
}
#[inline(never)]
pub fn w_bound_is_unbounded(b: Bound<i32>) -> bool {
    matches!(b, Bound::Unbounded)
}

// --- Result matches! form ---
#[inline(never)]
pub fn w_result_is_ok(r: Result<i32, u8>) -> bool {
    matches!(r, Ok(_))
}

// --- User 2-variant enums ---
pub enum E1 {
    A,
    B,
}
pub enum E2 {
    A,
    B,
}
pub enum E3 {
    A,
    B,
}

#[inline(never)]
pub fn w_e1_is_a(e: E1) -> bool {
    matches!(e, E1::A)
}
#[inline(never)]
pub fn w_e2_is_a(e: E2) -> bool {
    matches!(e, E2::A)
}
#[inline(never)]
pub fn w_e3_is_a(e: E3) -> bool {
    matches!(e, E3::A)
}

fn main() {
    let n = std::env::args().count() as i32;

    let o = if n > 1 {
        Ordering::Less
    } else if n == 1 {
        Ordering::Equal
    } else {
        Ordering::Greater
    };
    let cf: ControlFlow<i32, i32> = if n > 0 {
        ControlFlow::Break(n)
    } else {
        ControlFlow::Continue(n)
    };
    let p: Poll<i32> = if n > 0 { Poll::Ready(n) } else { Poll::Pending };
    let b: Bound<i32> = if n > 1 {
        Bound::Included(n)
    } else if n == 1 {
        Bound::Excluded(n)
    } else {
        Bound::Unbounded
    };
    let r: Result<i32, u8> = if n > 0 { Ok(n) } else { Err(n as u8) };
    let e1 = if n > 0 { E1::A } else { E1::B };
    let e2 = if n > 0 { E2::A } else { E2::B };
    let e3 = if n > 0 { E3::A } else { E3::B };

    let mut acc: u32 = 0;
    acc += w_ord_is_lt(o) as u32;
    acc += w_ord_is_le(o) as u32;
    acc += w_ord_is_gt(o) as u32;
    acc += w_ord_is_ge(o) as u32;
    acc += w_ord_is_eq(o) as u32;
    acc += w_ord_is_ne(o) as u32;
    acc += w_cf_is_break(cf) as u32;
    acc += w_cf_is_continue(cf) as u32;
    acc += w_poll_is_ready(p) as u32;
    acc += w_poll_is_pending(p) as u32;
    acc += w_bound_is_included(b) as u32;
    acc += w_bound_is_excluded(b) as u32;
    acc += w_bound_is_unbounded(b) as u32;
    acc += w_result_is_ok(r) as u32;
    acc += w_e1_is_a(e1) as u32;
    acc += w_e2_is_a(e2) as u32;
    acc += w_e3_is_a(e3) as u32;
    println!("{}", acc);
}
