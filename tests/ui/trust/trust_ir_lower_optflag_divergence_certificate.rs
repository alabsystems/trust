//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// OS1-DRC (wave-full-0901 coverage tier): the `Ty(option-flag in
// signature)` RETURN-position refusal now rides the wave-DRC
// body-divergence certificate. The tag guards an ABI lie — the signature
// signs the opaque-lane Option at its `Ty::Bool` flag spelling while a
// returning body would hand back something else — but a body that emits
// ZERO `Inst::Return` terminators (`fn next(..) -> Option<..> { loop {} }`,
// project-defer-unification's measured shape) never materializes the lie,
// so the refusal lands only when a `Return` exists in the emitted blocks.
// Param positions still refuse at signature time: the body READS a param,
// and no divergence certificate helps that. The payload is GENERIC on
// purpose — a monomorphic payload registers a real enum and the flag lane
// never engages (measured while writing this fixture).
pub trait Pix {
    type Pixel;
}

// Diverging body over an opaque-lane Option (generic payload): must
// LOWER (probe-verified 0 validation errors).
pub fn diverging_next<I: Pix>() -> Option<(u32, u32, I::Pixel)> {
    loop {}
}

// Returning body, same signature: the certificate fails and the tag
// lands verbatim — must stay refused (`Ty(option-flag in signature)`).
pub fn returning_next<I: Pix>(p: I::Pixel) -> Option<(u32, u32, I::Pixel)> {
    Some((0, 0, p))
}

fn main() {}
