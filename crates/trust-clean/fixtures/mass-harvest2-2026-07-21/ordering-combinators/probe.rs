// Ordering-combinators harvest corpus.
// Family: Ordering::reverse / then / then_with(closure), i32::cmp / u8::cmp,
// cmp().reverse() chains, and thin wrappers. All #[inline(never)], all called
// from main with inputs derived from std::env::args().count().

use std::cmp::Ordering;

// --- leaves / direct combinator wrappers -----------------------------------

#[inline(never)]
fn ord_reverse(o: Ordering) -> Ordering {
    o.reverse()
}

#[inline(never)]
fn ord_then(a: Ordering, b: Ordering) -> Ordering {
    a.then(b)
}

#[inline(never)]
fn ord_then_with_cmp(a: Ordering, x: i32, y: i32) -> Ordering {
    a.then_with(|| x.cmp(&y))
}

#[inline(never)]
fn cmp_i32(a: i32, b: i32) -> Ordering {
    a.cmp(&b)
}

#[inline(never)]
fn cmp_u8(a: u8, b: u8) -> Ordering {
    a.cmp(&b)
}

// --- chains ----------------------------------------------------------------

#[inline(never)]
fn cmp_reverse_i32(a: i32, b: i32) -> Ordering {
    a.cmp(&b).reverse()
}

#[inline(never)]
fn cmp_then_pair(a1: i32, b1: i32, a2: u8, b2: u8) -> Ordering {
    a1.cmp(&b1).then(a2.cmp(&b2))
}

#[inline(never)]
fn cmp_then_with_pair(a1: i32, b1: i32, a2: i32, b2: i32) -> Ordering {
    a1.cmp(&b1).then_with(|| a2.cmp(&b2))
}

#[inline(never)]
fn double_reverse(o: Ordering) -> Ordering {
    o.reverse().reverse()
}

#[inline(never)]
fn reverse_then(a: Ordering, b: Ordering) -> Ordering {
    a.reverse().then(b.reverse())
}

// --- wrappers over combinator results --------------------------------------

#[inline(never)]
fn ord_is_lt(o: Ordering) -> bool {
    o.is_lt()
}

#[inline(never)]
fn cmp_is_eq_i32(a: i32, b: i32) -> bool {
    a.cmp(&b).is_eq()
}

#[inline(never)]
fn ord_to_i8(o: Ordering) -> i8 {
    o as i8
}

fn main() {
    let n = std::env::args().count() as i32;
    let m = n as u8;

    let o1 = cmp_i32(n, 5);
    let o2 = cmp_u8(m, 3);
    let o3 = ord_reverse(o1);
    let o4 = ord_then(o1, o2);
    let o5 = ord_then_with_cmp(o1, n, 7);
    let o6 = cmp_reverse_i32(n, 2);
    let o7 = cmp_then_pair(n, 4, m, 9);
    let o8 = cmp_then_with_pair(n, 1, n + 2, 3);
    let o9 = double_reverse(o2);
    let o10 = reverse_then(o1, o2);
    let b1 = ord_is_lt(o3);
    let b2 = cmp_is_eq_i32(n, 6);
    let d = ord_to_i8(o4);

    let acc = (o1 as i32)
        + (o2 as i32)
        + (o3 as i32)
        + (o4 as i32)
        + (o5 as i32)
        + (o6 as i32)
        + (o7 as i32)
        + (o8 as i32)
        + (o9 as i32)
        + (o10 as i32)
        + (b1 as i32)
        + (b2 as i32)
        + (d as i32);
    std::process::exit(acc & 0x7f);
}
