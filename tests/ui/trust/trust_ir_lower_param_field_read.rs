//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-PLF): reading a BARE-`ty::Param` field back out of a holder.
//!
//! `map_ty`'s `ty::Param` arm already spells a bare type param as the opaque
//! `Ty::Unit` lane, and its own comment declares what that admits: "locals,
//! params, returns and call arguments of the type". The producer already
//! BUILDS the lane (`P { a: t, b: 7 }` emits a real `InsertField` of the
//! opaque param value) and already CARRIES it. The `Field` arm was the single
//! site that refused to read it back out — the wave-AOF field-store asymmetry
//! in reverse.
//!
//! GROUND TRUTH on the expression type, never the mapped `Ty::Unit`: that
//! spelling is also the value-less `()` and the degraded/unsupported
//! placeholder, so keying on it would silence a real gap as clean.
//! `unit_field_still_declines` is the fence.

pub struct P<T> {
    pub a: T,
    pub b: u8,
}

pub fn read_param_field<T>(p: P<T>) -> T {
    p.a
}

pub fn build_then_read<T>(t: T) -> T {
    let p = P { a: t, b: 7 };
    p.a
}

pub struct U {
    pub u: (),
    pub n: u8,
}

/// The fence: a genuine `()` field is NOT a param lane and keeps its own path.
pub fn unit_field_still_declines(x: U) -> u8 {
    x.n
}

fn main() {
    assert_eq!(read_param_field(P { a: 5u32, b: 1 }), 5);
    assert_eq!(build_then_read("s"), "s");
    assert_eq!(unit_field_still_declines(U { u: (), n: 9 }), 9);
}
