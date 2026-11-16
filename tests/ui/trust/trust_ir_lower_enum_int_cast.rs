//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-EC): a FIELDLESS enum cast to an integer is its discriminant —
//! `ExtractField(0)` of the enum aggregate (the registered tag, in the
//! canonical repr) followed by the ordinary int→int cast, so a canonical `I8`
//! `-1` sign-extends to `u32` exactly as `(-1isize) as u32` does and a `U8`
//! `200` truncates to `i8` as `200isize as i8`. Every cast here carried
//! `Cast(non-int source)` before the wave; `strict` turns that into a compile
//! error, so this file is the mutation check.
#[derive(Clone, Copy)]
enum Color {
    Red = 1,
    Green = 2,
    Blue = 4,
}
#[repr(i8)]
#[derive(Clone, Copy)]
enum Signed {
    Neg = -1,
    Zero = 0,
    Pos = 1,
}
enum Big {
    Small = 3,
    Large = 200,
}
fn tag(c: Color) -> u8 {
    c as u8
}
fn wide(c: Color) -> i64 {
    c as i64
}
fn neg(s: Signed) -> i32 {
    s as i32
}
fn byte(s: &Signed) -> u8 {
    *s as u8
}
fn narrow(b: Big) -> i8 {
    b as i8
}
fn main() {
    let ok = tag(Color::Blue) == 4
        && wide(Color::Green) == 2
        && neg(Signed::Neg) == -1
        && neg(Signed::Pos) == 1
        && byte(&Signed::Zero) == 0
        && narrow(Big::Large) == -56
        && narrow(Big::Small) == 3;
    std::process::exit(!ok as i32);
}
