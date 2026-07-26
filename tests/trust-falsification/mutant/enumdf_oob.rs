#![crate_type = "lib"]
// MUTANT (enum-disc-full-native soundness twin): a fieldless `#[repr(u8)]` enum with FIVE
// variants (discriminants 0..=4) indexed into a length-4 array. The `-full` native bridge
// emits `Inst::Assume(0 <= tag <= 4)` — the TRUE discriminant range — which is COMPATIBLE with
// the OOB violation `tag == 4 >= 4` (E::E is reachable). The access is therefore NOT proved and
// `-full` MUST refute (exit 1). Pins that the assumed bound is the ACTUAL max discriminant
// (inclusive) and is self-limiting: a too-loose bound or an off-by-one would FALSE-PROVE this
// guaranteed OOB at `E::E as usize == 4`.
#[repr(u8)]
pub enum E {
    A,
    B,
    C,
    D,
    E,
}

pub fn f(e: E) -> u8 {
    let a = [10u8, 20, 30, 40];
    a[e as usize]
}
