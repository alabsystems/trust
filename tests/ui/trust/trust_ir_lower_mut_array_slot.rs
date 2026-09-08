//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-CTA): `&mut <array literal>` / `&mut [x; N]` rvalues join the
//! chain-temp fresh-slot allow-list at the first-class `Ty::Array` spelling —
//! an array literal is never a place, so the fresh private slot cannot alias
//! any place borrow (the four-sites hazard, satisfied affirmatively).

fn bump(buf: &mut [u8; 4]) {
    buf[0] = buf[0].wrapping_add(7);
}

pub fn array_literal_slot() -> u8 {
    let d: &mut [u8; 3] = &mut [1, 2, 3];
    d[1] = 9;
    d[0] + d[1]
}

pub fn repeat_slot() -> u8 {
    let b: &mut [u8; 4] = &mut [0u8; 4];
    bump(b);
    b[0]
}

fn main() {
    assert_eq!(array_literal_slot(), 10);
    assert_eq!(repeat_slot(), 7);
}
