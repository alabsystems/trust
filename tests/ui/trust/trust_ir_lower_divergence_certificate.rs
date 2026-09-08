//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-DRC: THE BODY-DIVERGENCE CERTIFICATE the wave-UE record prescribed.
// A fn whose declared return is an opaque-lane enum (register_enum declined
// end-to-end) used to refuse at SIGNATURE time ('Ty(opaque-lane enum
// return)'). The refusal is now DEFERRED and adjudicated by `finish_body`
// against the EMITTED blocks: ZERO `Inst::Return` terminators — every path
// provably diverges IN THE ARTIFACT — certifies that the `returns: [Unit]`
// signature has no Return to contradict, so the module stays well-formed
// VACUOUSLY. Any Return at all (including one whose value a transmute
// manufactured from an uninhabited type — wave-UE's exact counterexample,
// which took INVALID 1 -> 6 under the signature-time exemption) lands the
// original refusal verbatim. Measured on this wave: INVALID stayed at
// baseline, where UE's type test took it to 6 on the same population.

pub enum Never {}

// All paths diverge: the certificate holds; this body lowers.
pub fn boom() -> Never {
    panic!("no")
}

// THE ATTACK, pinned: a manufactured "inhabitant" of an uninhabited type
// EMITS a Return, the certificate fails, and the refusal lands. This body
// must NOT lower.
pub fn fake() -> Never {
    unsafe { std::mem::transmute(()) }
}

// The opaque-Result twin: an always-panicking fn returning a declined enum.
pub enum OpaqueRes<T> {
    Ok(T),
    Err(String),
}
pub fn always_panics<T>() -> OpaqueRes<T> {
    panic!("nope")
}
