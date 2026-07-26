// bool-ops family harvest: then_some / then / !,&,|,^ / cmp
use std::cmp::Ordering;

// --- ADT-return lane: Option construction from guard ---
#[inline(never)]
fn w_then_some(b: bool, x: u32) -> Option<u32> {
    b.then_some(x)
}

#[inline(never)]
fn w_then(b: bool, x: u32) -> Option<u32> {
    b.then(|| x.wrapping_add(1))
}

// --- operator forms (lower to primitive MIR UnOp/BinOp) ---
#[inline(never)]
fn w_not_op(b: bool) -> bool {
    !b
}

#[inline(never)]
fn w_and_op(b: bool, c: bool) -> bool {
    b & c
}

#[inline(never)]
fn w_or_op(b: bool, c: bool) -> bool {
    b | c
}

#[inline(never)]
fn w_xor_op(b: bool, c: bool) -> bool {
    b ^ c
}

// --- explicit trait-leaf forms (monomorphize the core::ops impls for bool) ---
#[inline(never)]
fn w_not_leaf(b: bool) -> bool {
    std::ops::Not::not(b)
}

#[inline(never)]
fn w_and_leaf(b: bool, c: bool) -> bool {
    std::ops::BitAnd::bitand(b, c)
}

#[inline(never)]
fn w_or_leaf(b: bool, c: bool) -> bool {
    std::ops::BitOr::bitor(b, c)
}

#[inline(never)]
fn w_xor_leaf(b: bool, c: bool) -> bool {
    std::ops::BitXor::bitxor(b, c)
}

// --- comparison ---
#[inline(never)]
fn w_cmp(b: bool, c: bool) -> Ordering {
    b.cmp(&c)
}

fn main() {
    let n = std::env::args().count();
    let b = n > 1;
    let c = n % 2 == 0;
    let x = n as u32;

    let mut acc = 0u32;
    if let Some(v) = w_then_some(b, x) {
        acc = acc.wrapping_add(v);
    }
    if let Some(v) = w_then(b, x) {
        acc = acc.wrapping_add(v);
    }
    acc = acc.wrapping_add(w_not_op(b) as u32);
    acc = acc.wrapping_add(w_and_op(b, c) as u32);
    acc = acc.wrapping_add(w_or_op(b, c) as u32);
    acc = acc.wrapping_add(w_xor_op(b, c) as u32);
    acc = acc.wrapping_add(w_not_leaf(b) as u32);
    acc = acc.wrapping_add(w_and_leaf(b, c) as u32);
    acc = acc.wrapping_add(w_or_leaf(b, c) as u32);
    acc = acc.wrapping_add(w_xor_leaf(b, c) as u32);
    acc = acc.wrapping_add(match w_cmp(b, c) {
        Ordering::Less => 0,
        Ordering::Equal => 1,
        Ordering::Greater => 2,
    });
    std::process::exit((acc % 7) as i32);
}
