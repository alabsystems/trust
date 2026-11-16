#![allow(dead_code)]

// A struct field whose array element is ITSELF an array (and one beside a scalar field).
pub struct M {
    pub m: [[u32; 2]; 2],
}

pub fn get(x: M) -> M {
    x
}

pub struct Q {
    pub q: [[u8; 2]; 2],
    pub z: u8,
}

pub fn qz(x: &Q) -> u8 {
    x.z
}

// A struct field whose array element is a tuple.
pub struct P {
    pub p: [(u8, u16); 2],
}

pub fn getp(x: P) -> P {
    x
}

pub struct S {
    pub a: u8,
    pub b: u16,
}

// Promoted array globals: a tuple element and a nested-array element (both spliced when the
// array was spelled as a tuple), and a struct element (wave-NSA already spelled it an array,
// and it did not splice).
pub fn pt() -> &'static [(u8, u16); 2] {
    &[(1, 2), (3, 4)]
}

pub fn pn() -> &'static [[u8; 2]; 2] {
    &[[1, 2], [3, 4]]
}

pub fn ps() -> &'static [S; 2] {
    &[S { a: 1, b: 2 }, S { a: 3, b: 4 }]
}

// A fn pointer to a fn taking an array of tuples (table-free inline under the old spelling):
// the reify splices. One taking a nested array (already a first-class array inside the old
// spelling) did not splice, and does not.
pub fn take(a: [(u8, u8); 2]) -> u8 {
    a[0].0
}

pub fn reify() -> u8 {
    let f: fn([(u8, u8); 2]) -> u8 = take;
    f([(1, 2), (3, 4)])
}

pub fn take_n(a: [[u8; 2]; 2]) -> u8 {
    let [x, _] = a;
    x[0]
}

pub fn reify_n() -> u8 {
    let f: fn([[u8; 2]; 2]) -> u8 = take_n;
    f([[1, 2], [3, 4]])
}
