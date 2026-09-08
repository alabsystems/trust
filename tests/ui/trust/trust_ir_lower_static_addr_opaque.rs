//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-SAO): the STATIC twin of wave-NCA. When a static's initializer
//! cannot be decoded but the reference is a THIN address to an immutable Freeze
//! pointee with a positive spelling, the ADDRESS is still exactly modellable —
//! the value-less extern-global + `GlobalAddr` vocabulary, one spelling over
//! from the const case.
//!
//! `run-pass` executes REAL MIR (the body goes symbolic and never flips), so
//! the asserted values pin that nothing pretended to know the initializer.
//!
//! The unit half of this class is a genuine STOP and is deliberately not here:
//! `Ty::Unit` is also the producer's opaque spelling, and trust-ir's unit VALUE
//! and its unpatched PLACEHOLDER are the same constant, so a `()` static cannot
//! be told from an unevaluated one.

pub static BYTES: [u8; 4] = [1, 2, 3, 4];

pub fn probe_static_byte_array_ref() -> &'static [u8; 4] {
    &BYTES
}

fn main() {
    let r = probe_static_byte_array_ref();
    assert_eq!(r[0] as u32 + r[3] as u32, 5);
}
