//@ needs-trust-verify
//@ edition: 2021
//@ revisions: default certify
//@ compile-flags: --crate-type lib -Ztrust-verify=on
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-pass
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! ARGS-FINGERPRINT-READ-1 round 5 (2026-10-08) — a call to the implemented trait item
//! whose callee self type is a PROPER SUBTERM of the impl's self type may still recurse
//! forever, and D9 charges it.
//!
//! Round 4 exempted such a call from D9 ("every chain through this impl shrinks the
//! instance type, so it ends"). That holds only for chains that stay inside this impl.
//! The callee's self type is a parameter, and the impl it selects can grow the type again
//! and call back:
//!
//! * `impl<X: ?Sized + Tr> Tr for &X` forwards to `X`; with `X = dyn Tr` the vtable
//!   dispatches straight back into `<&dyn Tr as Tr>::f`, same `n` (`static S` below
//!   is a `&dyn Tr` pointing at itself; `S.f(3)` overflows the stack).
//! * `impl<Y: Up> Up for Box<Y>` forwards to `Y`, and `impl Up for u8` calls
//!   `<Box<u8> as Up>::g`: `u8 -> Box<u8> -> u8 -> ...`, same `n`, forever.
//!
//! MEASURED (level 2, JSON; review scratch `r7/dyn_shrink.rs`, `r8/probes/regrow.rs`):
//! no termination row for either forwarding body on the preview3 stage 1 (main
//! `7be75e9a80`) or on round 4. Round 5 charges both (the annotations). The re-entering
//! `impl Up for u8` is left out of this file: its call reaches the `Box` impl's
//! open-dispatch hypothesis, which fails the default lane for a reason unrelated to D9
//! (measured on both stage 1s), and its call resolves to the `Box` impl item, another
//! `DefId`, so it is not charged. The charge on the forwarding body does not depend on
//! which impls exist: D9 reads only this body.

pub trait Tr {
    fn f(&self, n: u64) -> u64;
}

impl<X: ?Sized + Tr> Tr for &X {
    fn f(&self, n: u64) -> u64 {
        //[default]~^ WARN termination is ASSUMED, not proved — 1 self call(s) bind no `decreases` measure
        //[certify]~^^ ERROR termination is not established — 1 self call(s) bind no
        if n == 0 {
            return 0;
        }
        <X as Tr>::f(*self, n)
    }
}

pub static S: &(dyn Tr + Sync) = &S;

pub trait Up {
    fn g(n: u64) -> u64;
}

impl<Y: Up> Up for Box<Y> {
    fn g(n: u64) -> u64 {
        //[default]~^ WARN termination is ASSUMED, not proved — 1 self call(s) bind no `decreases` measure
        //[certify]~^^ ERROR termination is not established — 1 self call(s) bind no
        if n == 0 {
            return 0;
        }
        <Y as Up>::g(n)
    }
}
