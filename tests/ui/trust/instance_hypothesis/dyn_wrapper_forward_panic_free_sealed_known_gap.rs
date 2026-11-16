//~ NOTE "line_start":78,"col_start":0,"line_end":81,"col_end":1},"outcome":"runtime_checked","solver":"trust-full-verifier
//~| NOTE "crate_name":"dyn_wrapper_forward_panic_free_sealed_known_gap","functions_analyzed":7,"functions_verified":3,"total_proved":3,"total_failed":0,
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! DYN-WRAPPER-FORWARD-1 (2026-10-10), KNOWN PRECISION GAP (ii), a tripwire: recipe
//! (C) (each trait sealed directly) PLUS `#[trust::panic_free]` on every method. The
//! callers rely on the contract: `refusal` carries no absent-callee row and the
//! crate summary has zero failed (second pin); `decline` is `runtime_checked` (first
//! pin). But each forwarding impl in `Fixed` is still a hard error: its body's call
//! to `<dyn Prep as Facts>::a` (resp. `b`, `c`), whose callee carries the same
//! contract on a sealed trait, is left `unknown` (spawn census) and the impl does
//! not discharge its own contract by relying on the callee's. Fail-closed, not
//! unsound. If the gap is closed, the two ERROR annotations fail: make this
//! `check-pass`, drop them, and update the DYN-WRAPPER-FORWARD-1 row in
//! docs/DECISION_QUEUE.md. Until then recipe (C) is offered without the contract.

mod private {
    pub trait Sealed {}
}

pub trait Facts: private::Sealed {
    #[trust::panic_free]
    fn a(&self) -> bool;
    #[trust::panic_free]
    fn b(&self) -> bool;
}

pub trait Prep: Facts + private::Sealed {
    #[trust::panic_free]
    fn c(&self) -> bool;
}

pub struct Real {
    pub x: bool,
}

impl private::Sealed for Real {}

impl Facts for Real {
    fn a(&self) -> bool {
        self.x
    }
    fn b(&self) -> bool {
        !self.x
    }
}

impl Prep for Real {
    fn c(&self) -> bool {
        self.x
    }
}

impl private::Sealed for Fixed<'_> {}

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
