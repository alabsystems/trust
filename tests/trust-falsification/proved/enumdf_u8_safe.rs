#![crate_type = "lib"]
// COMPLETENESS (enum-disc-full-native 2026-06-25): `arr[e as usize]` for a fieldless
// `#[repr(u8)]` enum proves under `-full` via the NATIVE trust-ir bridge. The enum lowers
// to a Direct-tag-encoded layout (classified `disc_index_safe`), so the bridge's
// `Rvalue::Discriminant` read emits `Inst::Assume(0 <= tag <= 3)` over the extracted `__tag`.
// max_disc 3 < array length 4, so every `e as usize` index is in bounds.
// This already proves in DEFAULT mode (commit c7192e0a5d); this fixture pins the `-full` path.
#[repr(u8)]
pub enum E {
    A,
    B,
    C,
    D,
}

pub fn f(e: E) -> u8 {
    let a = [10u8, 20, 30, 40];
    a[e as usize]
}
