//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-BS): the SHARED-BORROW snapshot admits nested / float /
//! array-field / opaque-lane aggregates — `snapshotable_borrow_pointee`, a
//! predicate SEPARATE from the promotion lanes' narrow one. The measured
//! population is `assert_eq!`'s `&$left`/`&$right` on such operands (a
//! `String`, a float struct, a nested struct), which died on
//! `Borrow(non-scalar pointee)` / `Borrow(non-local place)` at the borrow
//! itself, never inside the operand. Under `strict`; the promotion lanes
//! are exercised by `p.x = 1.0` on a float-field struct, which must STAY on
//! wave-AW's value surgery (no `&mut`, no slot).
//!
//! EFFECT CONSERVATION (D28, 2026-10-01): `owned_string` and `temp_string` drop `String`s. Until
//! the step 2 increment 4b residuals the direct trust-ir did not carry those drops (the
//! `assert_eq!` operands are borrowed temporaries), the effect-conservation gate tagged each body
//! `Abstracted(drop, ..)` and strict refused it. The producer now places them — each temporary
//! dropped at the end of its scope, through its object's proved home or, where the `assert_eq!`
//! tuple takes the borrow's address, through the borrow's slot under 4b's root rule (a `String` is
//! `Freeze` and its glue only frees memory: every copy is the same drop) — so both bodies are
//! clean under strict; a producer tag would still be its own, unannotated, strict error, so this
//! file keeps its mutation check.

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
