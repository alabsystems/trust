//@ compile-flags: -Z trust-verify=off
//@ check-fail
//! A syntax error in the SECOND declaration is reported by the parser at its
//! own span, first, and nothing from the island is registered or minted: the
//! first declaration is not silently callable from a half-parsed island, and
//! the `E0425` that follows is never the first symptom. (The parser records
//! no declarations for an island it could not parse, so this `E0425` carries
//! no per-declaration refusal note — the syntax error above it is the note.)

mod m {
    clean {
        def pick (a : UInt64) (b : UInt64) : UInt64 := a
        theorem pick_eq (a b : UInt64) : pick a b = a := := rfl
    }
}
//~^^^ ERROR Clean island failed to parse

fn main() {
    let lo = m::pick(7, 41);
    //~^ ERROR cannot find function `pick` in module `m`
    assert!(lo == 7);
}
