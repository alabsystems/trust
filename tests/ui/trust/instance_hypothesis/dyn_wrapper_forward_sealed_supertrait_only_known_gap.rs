//~ NOTE "line_start":64,"col_start":4,"line_end":66,"col_end":5},"outcome":"runtime_checked","solver":"trust-full-verifier
//~| NOTE "line_start":67,"col_start":4,"line_end":69,"col_end":5},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":72,"col_start":0,"line_end":74,"col_end":1},"outcome":"runtime_checked","solver":"trust-full-verifier
//~| NOTE "line_start":76,"col_start":0,"line_end":79,"col_end":1},"outcome":"runtime_checked","solver":"trust-full-verifier
//~| NOTE "crate_name":"dyn_wrapper_forward_sealed_supertrait_only_known_gap","functions_analyzed":7,"functions_verified":3,"total_proved":3,"total_failed":1,
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-pass
//! DYN-WRAPPER-FORWARD-1 (2026-10-10), KNOWN PRECISION GAP (i), a tripwire: only the
//! supertrait `Facts` is sealed; the public subtrait `Prep: Facts` is not sealed
//! directly. Every `Prep` impl must also implement `Facts`, which only this crate
//! can do, so `Prep`'s impl set is in fact closed. `dyn_trait_sealedness` does not
//! see that today and treats `Prep` as open, so `Fixed::b`'s call to `Prep::c`
//! keeps its `failed` row (line 1, second pin) while `Fixed::a`, `refusal` and
//! `decline` (whose calls go through the sealed `Facts`) are `runtime_checked`
//! (first, third and fourth pins); one failed row in the crate summary (fifth
//! pin). This is fail-closed, not unsound. If the gap is closed, the second and
//! fifth pins fail: re-pin `Fixed::b` to `runtime_checked`, zero failed, and
//! update the DYN-WRAPPER-FORWARD-1 row in docs/DECISION_QUEUE.md.

mod private {
    pub trait Sealed {}
}

pub trait Facts: private::Sealed {
    fn a(&self) -> bool;
    fn b(&self) -> bool;
}

pub trait Prep: Facts {
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
        self.0.a()
    }
    fn b(&self) -> bool {
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
