#![crate_type = "lib"]
// MUTANT (CAST-ENUMDISC-SIGNED-1, 2026-10-05): a cast from a `#[repr(u8)]` enum's
// discriminant to `i8`, the SAME width but SIGNED. `F::A as i8 == -56`, so the
// postcondition is false of the binary. The enum-disc-index arm of
// `guards::cast_definition_formula` emitted `_0 == _2` from the destination WIDTH
// alone; beside `_2 == 200`, the true tag image `_0 == -56 || _0 == 1` and
// `_0 <= 127` that was a contradiction on the `F::A` path, and the row was
// kernel-certified (stage1-w15r, these gate flags: rc=0, "2 proved ... of which 1
// kernel-certified"). With the arm requiring every tag to survive the cast this
// MUST fail closed (exit 1). The fitting-tag sibling (`{100, 1} as i8`) and the
// wider-destination one (`as i16`) prove: tests/ui/trust/
// enum_disc_cast_same_width_signed_is_not_identity.rs, revision `holds`.
// MEASURED 2026-10-06 on the stage 1 of `9e11546767` under these gate flags: exit 1, but with
// "0 failed, 1 unknown" (the return-slot tripwire: no lane relates a same-width
// unsigned->signed cast's result to its source), which the gate scores
// `incomplete`, an UNCAUGHT mutant, not `refuted`. KNOWN_HAZARDS CAST-ENUMDISC-SIGNED-1.
#[repr(u8)]
pub enum F {
    A = 200,
    B = 1,
}

pub fn m_f(e: F) -> i8
    ensures result >= 0
{
    e as i8
}
