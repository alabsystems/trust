//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-FA): `println!`/`panic!` with a NON-TRIVIAL argument — rustc
//! keeps evaluation order with `match (&e0, ..) { args => Arguments::new_v1(..)
//! }` — lowers by evaluating each scrutinee element for its effects (the
//! calls stay in program order) and dropping the read-only formatting
//! plumbing into the unit-sink / diverging callee, as wave-ER does for the
//! trivial-argument form. Under `strict`.

fn compute(x: u32) -> u32 {
    x + 41
}

fn report(x: u32) {
    println!("value = {}", compute(x));
    println!("{} and {}", compute(x), compute(x + 1));
}

fn must_be_one(x: u32) {
    if x != 1 {
        panic!("expected one, got {}", compute(x));
    }
}

fn main() {
    report(1);
    must_be_one(1);
}
