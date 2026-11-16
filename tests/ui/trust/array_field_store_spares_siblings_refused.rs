//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `array_field_store_spares_siblings.rs`: the store reaches
//! the guarded value itself, so its fact must not survive. Each panics on the input
//! named beside it.

pub struct Bytes {
    items: [u8; 8],
    len: usize,
}

// i = 0: the store overwrites the guarded element with 250, and `250 + 10` overflows.
pub fn same_element(s: &mut Bytes, i: usize) -> u8 { //~ ERROR failed for `array_field_store_spares_siblings_refused::same_element`
    if s.items[0] < 10 && i < 8 {
        s.items[i] = 250;
        s.items[0] + 10
    } else {
        0
    }
}

// The same constant slot: the store overwrites the guarded element with 250.
pub fn same_constant_element(s: &mut Bytes) -> u8 { //~ ERROR failed for `array_field_store_spares_siblings_refused::same_constant_element`
    if s.items[3] < 10 {
        s.items[3] = 250;
        s.items[3] + 10
    } else {
        0
    }
}

pub struct Grid {
    cells: [[u8; 4]; 4],
}

// r = 0, c = 0: an element of the nested array, reached through two symbolic
// indices, is the guarded element.
pub fn nested_element(g: &mut Grid, r: usize, c: usize) -> u8 { //~ ERROR failed for `array_field_store_spares_siblings_refused::nested_element`
    if g.cells[0][0] < 10 && r < 4 && c < 4 {
        g.cells[r][c] = 250;
        g.cells[0][0] + 10
    } else {
        0
    }
}

// A store to the guarded FIELD itself.
pub fn same_field(s: &mut Bytes) -> usize { //~ ERROR failed for `array_field_store_spares_siblings_refused::same_field`
    if s.len < 8 {
        s.len = usize::MAX;
        s.len + 1
    } else {
        0
    }
}
