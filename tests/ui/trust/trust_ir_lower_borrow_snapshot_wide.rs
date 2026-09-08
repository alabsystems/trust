//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-BS): the SHARED-BORROW snapshot admits nested / float /
//! array-field / opaque-lane aggregates — `snapshotable_borrow_pointee`, a
//! predicate SEPARATE from the promotion lanes' narrow one. The measured
//! population is `assert_eq!`'s `&$left`/`&$right` on such operands (a
//! `String`, a float struct, a nested struct), which died on
//! `Borrow(non-scalar pointee)` / `Borrow(non-local place)` at the borrow
//! itself, never inside the operand. Under `strict`; the promotion lanes
//! are exercised by `p.x = 1.0` on a float-field struct, which must STAY on
//! wave-AW's value surgery (no `&mut`, no slot).

#[derive(PartialEq, Debug, Clone, Copy)]
struct Pf {
    x: f64,
    y: f64,
}

#[derive(PartialEq, Debug, Clone, Copy)]
struct Qn {
    a: u32,
    b: (u8, u8),
}

#[derive(PartialEq, Debug, Clone, Copy)]
struct Ar {
    a: [u8; 3],
}

fn float_struct(p: Pf) {
    assert_eq!(p, Pf { x: 1.0, y: 2.0 });
}

fn nested(q: Qn) {
    assert_eq!(q, Qn { a: 1, b: (2, 3) });
}

fn array_field(r: Ar) {
    assert_eq!(r, Ar { a: [1, 2, 3] });
}

fn float_tuple(t: (f64, f64)) {
    assert_eq!(t, (1.0, 2.0));
}

fn owned_string(s: String) {
    assert_eq!(s, String::new());
}

fn temp_string() {
    assert_eq!(String::from("a"), "a".to_string());
}

fn aw_stays_value_surgery(v: f64) -> f64 {
    let mut p = Pf { x: 0.0, y: 0.0 };
    p.x = v; // never borrowed: SSA + InsertField, exactly as before this wave
    p.x + p.y
}

fn main() {
    float_struct(Pf { x: 1.0, y: 2.0 });
    nested(Qn { a: 1, b: (2, 3) });
    array_field(Ar { a: [1, 2, 3] });
    float_tuple((1.0, 2.0));
    owned_string(String::new());
    temp_string();
    if aw_stays_value_surgery(1.5) != 1.5 {
        std::process::exit(1);
    }
}
