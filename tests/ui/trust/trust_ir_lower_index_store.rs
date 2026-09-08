//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-FS2: index-STORES through the chain resolver. `a[i] = v` on a
// `&mut [T; N]` param (the zero-field indexed deref) and `w.xs[i] = v`
// (index over a field chain) Store through the composed address behind the
// FI-b bounds idiom. The place-mode split keeps every BORROW caller's gates
// byte-identical to wave-FI-c — three same-wave regressions taught it:
// deferring the thin-result gate widened the borrow probe surface (a layout
// delayed-bug on trivially-false-bound unsized structs, and a registration-
// order perturbation from the mutating map_ty probe), and the sizedness scan
// must refuse only CONCRETELY-unsized fields (is_sized on ty::Param answers
// false conservatively and over-refused a generic body FI-c served).

pub fn store_ref(a: &mut [u8; 3], i: usize) {
    a[i] = 9;
}

pub fn store_const(a: &mut [u8; 3]) {
    a[0] = 7;
}

pub struct W {
    pub xs: [i64; 4],
    pub n: u32,
}

pub fn store_field(w: &mut W, i: usize) {
    w.xs[i] = 5;
}

// wave-FS3: ONE box level under the indexed lane — the data pointer loads at
// +0 (box_data_ptr_at_offset_zero-gated) with wave-BX's structured
// inheritance, and the index lands on the heap block.
pub fn store_boxed(node: &mut Box<[u8; 1]>) {
    node[0] = 9u8;
}

fn main() {
    let mut a = [1u8, 2, 3];
    store_ref(&mut a, 1);
    store_const(&mut a);
    assert_eq!(a, [7, 9, 3]);
}
