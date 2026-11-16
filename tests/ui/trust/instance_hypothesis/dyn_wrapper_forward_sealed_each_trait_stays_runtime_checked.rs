//~ NOTE "line_start":61,"col_start":4,"line_end":63,"col_end":5},"outcome":"runtime_checked","solver":"trust-full-verifier
//~| NOTE "line_start":64,"col_start":4,"line_end":66,"col_end":5},"outcome":"runtime_checked","solver":"trust-full-verifier
//~| NOTE "line_start":69,"col_start":0,"line_end":71,"col_end":1},"outcome":"runtime_checked","solver":"trust-full-verifier
//~| NOTE "line_start":73,"col_start":0,"line_end":76,"col_end":1},"outcome":"runtime_checked","solver":"trust-full-verifier
//~| NOTE "crate_name":"dyn_wrapper_forward_sealed_each_trait_stays_runtime_checked","functions_analyzed":7,"functions_verified":3,"total_proved":3,"total_failed":0,
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-pass
//! DYN-WRAPPER-FORWARD-1 (2026-10-10), recipe (C): the wrapper-forwarding shape of
//! `dyn_wrapper_forward_open_trait_is_failed.rs` with EACH public trait (`Facts` AND
//! `Prep`) carrying the never-exported supertrait `private::Sealed`. The impl set is
//! now closed (`dyn_trait_sealedness`), no adversary can supply an impl, and no row is
//! `failed`: `Fixed::a`, `Fixed::b`, `refusal` and `decline` are `runtime_checked`
//! (line 1, first four pins) and the crate summary counts zero failed (fifth pin).
//! This is the crate-side recipe the ruling offers clean-ck0 (once its
//! `ForgedFieldCount` integration-test impl of `Env` moves in-crate).

mod private {
    pub trait Sealed {}
}

pub trait Facts: private::Sealed {
    fn a(&self) -> bool;
    fn b(&self) -> bool;
}

pub trait Prep: Facts + private::Sealed {
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
