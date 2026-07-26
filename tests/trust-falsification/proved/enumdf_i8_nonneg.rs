#![crate_type = "lib"]
// COMPLETENESS (enum-disc-full-native 2026-06-25): a fieldless `#[repr(i8)]` enum with
// NON-NEGATIVE explicit discriminants (0, 1, 2) is Direct-tag-encoded and classified
// `disc_index_safe`. min_disc 0 >= 0 passes GATE-NONNEG, so the `-full` native bridge emits
// `Inst::Assume(0 <= tag <= 2)`. max_disc 2 < array length 3, so `arr[e as usize]` is in bounds.
#[repr(i8)]
pub enum E {
    A = 0,
    B = 1,
    C = 2,
}

pub fn f(e: E) -> u8 {
    let a = [7u8, 8, 9];
    a[e as usize]
}
