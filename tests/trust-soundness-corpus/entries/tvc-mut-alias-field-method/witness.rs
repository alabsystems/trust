// trust-soundness-corpus entry `tvc-mut-alias-field-method` (trust-vc &mut place escape (930d025f)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
// The reproducer with its contract and assertion as plain code.
use std::ops::AddAssign;
struct S2 {
    g: u8,
    #[allow(dead_code)]
    h: u8,
}
fn never_whole_alias_field_method(y: u8) {
    assert!(y == 1u8, "requires");
    let mut s = S2 { g: y, h: y };
    let r = &mut s;
    r.g.add_assign(1u8);
    println!("s.g = {}", s.g);
    assert!(s.g == 1u8, "trust_vc::assert! violated");
}
fn main() {
    never_whole_alias_field_method(std::hint::black_box(1));
}
