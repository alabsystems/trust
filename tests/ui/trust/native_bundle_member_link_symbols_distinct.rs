//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! Trust (native bundle, 2026-09-27): two bundle members that share a bare item
//! name each get their own TrustIR link symbol.
//!
//! `make`'s native bundle holds `make`, `A::new` and `B::new`. The bridge named
//! every lowered function by its bare item name, so two functions were called
//! `new`; TrustIR ratifies `Function::name` as the only def identity and its
//! full-module validation refuses the module (`functions #1 and #2 share the
//! link symbol "new"; ambiguous name-keyed identity, fail-closed`). trust-mc's
//! proof-authority gate runs that validation first, so it refused the whole
//! bundle and `make`'s panic-freedom row stayed `runtime_checked` — refused
//! under certify for a naming collision that says nothing about the code.
//! MEASURED on a stage-1 build of 2db97a27bf: this file fails with exactly that
//! reason. On the 2026-09-27 refusal inventory it was the single largest reason
//! a whole-function panic-freedom row was refused (derived `eq`/`partial_cmp`,
//! `{closure#0}`, `new`, ...).
//!
//! Every in-module reference to a function is by id, so the bridge now gives a
//! later duplicate its crate-qualified def-path; the root keeps its name.

pub struct A(pub u32);
pub struct B(pub u32);

impl A {
    pub fn new(x: u32) -> A {
        A(x)
    }
}

impl B {
    pub fn new(x: u32) -> B {
        B(x)
    }
}

pub fn make(x: u32) -> u32 {
    let a = A::new(x);
    let b = B::new(x);
    if a.0 != b.0 {
        panic!()
    }
    a.0
}
