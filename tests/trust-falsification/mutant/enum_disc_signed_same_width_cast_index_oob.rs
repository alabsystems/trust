#![crate_type = "lib"]
// MUTANT (CAST-ENUMDISC-SIGNED-1, 2026-10-05): the safety-row shape of
// `enum_disc_signed_same_width_cast.rs`. `F::A as i8 == -56` and `-56 as usize` is
// 18446744073709551560, so `arr[(e as i8) as usize]` on a `[u32; 2]` panics
// ("index out of bounds: the len is 2 but the index is 18446744073709551560").
// The identity `_d == e_disc` the enum-disc-index arm emitted for the same-width
// `u8 -> i8` cast made the `F::A` path contradictory, and the bounds row was
// kernel-certified (stage1-w15r, these gate flags: rc=0, "1 proved ... of which 1
// kernel-certified"). It MUST fail closed (exit 1): the bounds row refutes on the
// `F::A` witness once the arm declines.
#[repr(u8)]
pub enum F {
    A = 200,
    B = 1,
}

pub fn idx(e: F, arr: &[u32; 2]) -> u32 {
    arr[(e as i8) as usize]
}
