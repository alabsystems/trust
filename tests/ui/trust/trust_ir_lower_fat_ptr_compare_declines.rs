//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-FPC (INVALID root 8, full-population frontier): `ICmp` is defined
// over integer/char/bool scalars and THIN pointers. A FAT raw pointer
// (`*const str` / `*const [T]`) maps to the two-lane tuple spelling, and
// the operand values arrive under the cast lane's `fatptr` spelling — so
// emitting the primitive compare shipped `ICmpRequiresIntegerOrPtr` plus
// two `OperandTypeMismatch` rows (raw-pointer-from-str-comparison). The
// Binary compare arm now fails a non-scalar/non-thin-ptr spelling closed
// (`Binary(non-scalar compare)`); the honest wide-pointer compare is
// data-eq AND meta-eq and is not built until a population demands it.
#![allow(unused_must_use)]
#![allow(ambiguous_wide_pointer_comparisons)]

// The measured shape: must DECLINE, never emit the ill-typed ICmp —
// probe-verified 0 validation errors while this body reports the tag.
pub fn fat_ptr_compare(a: &str) -> bool {
    let x = a as *const str;
    x == x
}

// Negative control: a THIN raw-pointer compare is NOT claimed by the new
// tag — it keeps its own PRE-EXISTING refusal (`Binary(borrow ptr
// operand)`: the operands are casts of param borrows, refused before the
// compare arm is reached). The wave-FPC gate scopes to the fat spellings
// alone; if this body ever reports `Binary(non-scalar compare)` the gate
// has widened past its population.
pub fn thin_ptr_compare(a: &i32, b: &i32) -> bool {
    let x = a as *const i32;
    let y = b as *const i32;
    x == y
}

fn main() {
    fat_ptr_compare("hi");
    thin_ptr_compare(&1, &2);
}
