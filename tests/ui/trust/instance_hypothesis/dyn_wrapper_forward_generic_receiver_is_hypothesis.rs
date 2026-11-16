//~ NOTE [trust-instance-hypothesis] call to `<P as dyn_wrapper_forward_generic_receiver_is_hypothesis::Facts>::a`
//~| NOTE [trust-instance-hypothesis] call to `<P as dyn_wrapper_forward_generic_receiver_is_hypothesis::Prep>::c`
//~| NOTE [trust-instance-hypothesis] call to `<F as dyn_wrapper_forward_generic_receiver_is_hypothesis::Facts>::b`
//~| NOTE "crate_name":"dyn_wrapper_forward_generic_receiver_is_hypothesis","functions_analyzed":4,"functions_verified":0,"total_proved":0,"total_failed":0,
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-pass
//! DYN-WRAPPER-FORWARD-1 (2026-10-10), recipe (B), GENERIC RECEIVER: the
//! wrapper-forwarding shape of `dyn_wrapper_forward_open_trait_is_failed.rs` with
//! `P: Prep + ?Sized` in place of `dyn Prep`. No row is `failed` (line 1, last
//! pin): each trait-method call becomes an OD-1 `assumption:instance-hypothesis`
//! row (first three pins), an assumption discharged per instance where a crate
//! instantiates `decline`. This is NOT proof: it moves the obligation to the
//! instantiating crate (for ty, `tla-check`).

pub trait Facts {
    fn a(&self) -> bool;
    fn b(&self) -> bool;
}

pub trait Prep: Facts {
    fn c(&self) -> bool;
}

struct Fixed<'f, P: ?Sized>(&'f P);

impl<P: Prep + ?Sized> Facts for Fixed<'_, P> {
    fn a(&self) -> bool {
        self.0.a()
    }
    fn b(&self) -> bool {
        self.0.b() && !self.0.c()
    }
}

fn refusal<F: Facts + ?Sized>(f: &F) -> bool {
    f.a() || f.b()
}

pub fn decline<P: Prep + ?Sized>(f: &P) -> bool {
    let w = Fixed(f);
    refusal(&w)
}
