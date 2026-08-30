//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-LP): a LITERAL payload subpattern — `E::A(true)`,
//! `Cons(10, _)` — lowers as the arm's refutable entry test: ExtractField
//! the committed variant's field, ICmp Eq against the def-typed constant,
//! CondBr hit -> body / miss -> the same shared fallthrough the guard-false
//! and nested-miss routes use. No address, no offset table, no new Inst.

enum BoolCarrier {
    A(bool),
    B(u32),
}

enum IntCarrier {
    Cons(u64, u32),
    Nil,
}

fn check_bool(e: &BoolCarrier) -> u32 {
    match *e {
        BoolCarrier::A(true) => 1,
        BoolCarrier::A(false) => 2,
        BoolCarrier::B(_) => 3,
    }
}

fn check_int(e: IntCarrier) -> u32 {
    match e {
        IntCarrier::Cons(10, _) => 1,
        IntCarrier::Cons(_, _) => 2,
        IntCarrier::Nil => 3,
    }
}

fn main() {
    assert_eq!(check_bool(&BoolCarrier::A(true)), 1);
    assert_eq!(check_bool(&BoolCarrier::A(false)), 2);
    assert_eq!(check_bool(&BoolCarrier::B(7)), 3);
    assert_eq!(check_int(IntCarrier::Cons(10, 0)), 1);
    assert_eq!(check_int(IntCarrier::Cons(11, 0)), 2);
    assert_eq!(check_int(IntCarrier::Nil), 3);
}
