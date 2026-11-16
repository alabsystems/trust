//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//! R43-ZERO-ROW-PARITY boundary (twin of `zero_obligation_parametric_generic_callee.rs`):
//! the zero-row call gate's generic arm is the R43 parametric arm, and a generic body
//! that DROPS its `T` is not parametric. `sink::<Bomb>` runs a panicking destructor,
//! the instantiation-dependent panic R43 exists to exclude, so `c` must stay refused
//! (measured refused before and after the change, with obligations of its own).

pub struct Bomb;

impl Drop for Bomb {
    fn drop(&mut self) {
        //~^ ERROR Trust strict verification failed for
        //~| ERROR Trust Level 0 safety verification incomplete for
        panic!("boom");
    }
}

#[inline(never)]
fn sink<T>(_t: T) {}
//~^ ERROR Trust strict verification failed for
//~| ERROR Trust Level 0 safety verification incomplete for

pub fn c(b: Bomb) {
    //~^ ERROR Trust strict verification failed for
    //~| ERROR Trust Level 0 safety verification incomplete for
    sink::<Bomb>(b)
}

// The R43 TARGET premise, through the zero-row gate (review, 2026-10-13). The trait
// defaults are registered panic-free AND parametric, so only the resolve pin
// (`generic_call_runs_the_registered_body`) separates the three callers below:
// `keeps_default` runs the default itself and is accepted (no annotation: any error
// fails this test), `overridden` runs `Overrides`'s panicking `pass`, and
// `through_dyn` is a `Virtual` call whose `def_id()` IS the default's; both stay
// refused (`TRUST_PARAMETRIC_CALL_DEBUG`: `proven=true parametric=true resolves=false`).
pub trait Tr {
    #[inline(never)]
    fn pass<T>(&self, x: T) -> T
    where
        Self: Sized,
    {
        x
    }
    #[inline(never)]
    fn one(&self) -> u32 {
        1
    }
}

pub struct Keeps;
impl Tr for Keeps {}

pub struct Overrides;
impl Tr for Overrides {
    fn pass<T>(&self, _x: T) -> T
    //~^ ERROR Trust strict verification failed for
    //~| ERROR Trust Level 0 safety verification incomplete for
    where
        Self: Sized,
    {
        panic!("override")
    }
    fn one(&self) -> u32 {
        //~^ ERROR Trust strict verification failed for
        //~| ERROR Trust Level 0 safety verification incomplete for
        panic!("override")
    }
}

pub fn keeps_default(k: &Keeps) -> u8 {
    k.pass::<u8>(1)
}

pub fn overridden(o: &Overrides) -> u8 {
    //~^ ERROR Trust strict verification failed for
    //~| ERROR Trust Level 0 safety verification incomplete for
    o.pass::<u8>(1)
}

pub fn through_dyn(t: &dyn Tr) -> u32 {
    //~^ ERROR Trust strict verification failed for
    //~| ERROR Trust Level 0 safety verification incomplete for
    t.one()
}
