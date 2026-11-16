// trust-soundness-corpus entry `tvc-mut-alias-field-method` (trust-vc &mut place escape (930d025f)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
use std::ops::AddAssign;

struct S2 {
    g: u8,
    h: u8,
}

#[trust_vc::requires(y == 1u8)]
fn never_whole_alias_field_method(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s;
    r.g.add_assign(1u8);
    trust_vc::assert!(s.g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn verified_alias_write_twin(y: u8) {
    let mut s = S2 { g: y, h: y };
    let r = &mut s.g;
    *r = 5;
    trust_vc::assert!(s.g == 5u8 && s.h == 1u8);
}
