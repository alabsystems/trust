//~ NOTE "line_start":35,"col_start":4,"line_end":38,"col_end":5},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":39,"col_start":4,"line_end":42,"col_end":5},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":45,"col_start":0,"line_end":47,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":49,"col_start":0,"line_end":52,"col_end":1},"outcome":"runtime_checked","solver":"trust-full-verifier
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! DYN-WRAPPER-FORWARD-1 (2026-10-10), correction to OD-1-RG-CONCRETE: a
//! `#[trust::panic_free]` contract on the methods of an OPEN exported trait is not a
//! crate-side remedy for the wrapper-forwarding rows. The open-dispatch rows do not
//! move (`Fixed::a`, `Fixed::b` and `refusal` stay `failed`, line 1, first three
//! pins; `decline` stays `runtime_checked`, fourth pin), and the contract is itself
//! a hard error at each forwarding impl: its body calls an open trait object, so it
//! cannot discharge the contract every impl inherits.

pub trait Facts {
    #[trust::panic_free]
    fn a(&self) -> bool;
    #[trust::panic_free]
    fn b(&self) -> bool;
}

pub trait Prep: Facts {
    #[trust::panic_free]
    fn c(&self) -> bool;
}

struct Fixed<'f>(&'f dyn Prep);

impl Facts for Fixed<'_> {
    fn a(&self) -> bool {
        //~^ ERROR is not proved panic-free
        self.0.a()
    }
    fn b(&self) -> bool {
        //~^ ERROR is not proved panic-free
        self.0.b() && !self.0.c()
    }
}

fn refusal(f: &dyn Facts) -> bool {
    f.a() || f.b()
}

pub fn decline(f: &dyn Prep) -> bool {
    let w = Fixed(f);
    refusal(&w)
}
