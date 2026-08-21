//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//! **I8 negative — `clean mod name { … }` is not a form.**
//! The braced body belongs either to an inline island or to the `.clean`
//! file; guessing which would silently pick a semantics. Refused at parse
//! time with the three options (ruling v7/D3): `clean mod name;` + the body
//! in `name.clean`; drop `mod name` for an inline island (declarations land
//! in the enclosing module either way); or `mod name { clean { … } }` for a
//! real Rust module scope.

clean mod oops { def x (a : UInt64) : UInt64 := a }
//~^ ERROR takes no braced body

fn main() {}
