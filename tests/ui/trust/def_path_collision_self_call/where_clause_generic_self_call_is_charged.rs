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
//! ARGS-FINGERPRINT-READ-1 round 4 (2026-10-08) — an unresolved call to the trait item
//! a body implements may run that body, and D9 charges it.
//!
//! `<W<G> as Tr>::f::<G>(n)` inside `impl Tr for W<u8>` does not resolve (`W<G>: Tr`
//! is a where-clause candidate), and with `G = u8` it IS this body, called with the same
//! `n`: `run` recurses forever. vcgen's rendered-path test does not see a self call
//! (`W<G>` is not `W<u8>`), so its inferred lane mints nothing, and D9's census, which
//! counted only `Item(own) | Unresolved(own)`, charged nothing either. MEASURED (level 2,
//! JSON, `where_self_generic.rs`): no termination row for `f` on the preview3 stage 1
//! (main `7be75e9a80`) or on round 3.
//!
//! Round 4 charges it. Round 4 also exempted the structural forwarding impl below (its
//! call's self type `X` is a proper subterm of `Box<X>`), arguing that such chains shrink
//! the type and end. Review refuted that: the callee's impl may grow the type again and
//! re-enter (`trait_item_call_through_another_impl_is_charged.rs`). Round 5 (2026-10-08)
//! charges the forwarding call too: the capability cost, pinned by the annotations on `g`.

pub struct W<X>(pub X);
pub trait Tr {
    fn f<G>(n: u64) -> u64
    where
        W<G>: Tr;
}

impl Tr for W<u8> {
    fn f<G>(n: u64) -> u64
    //[default]~^ WARN termination is ASSUMED, not proved — 1 self call(s) bind no `decreases` measure
    //[certify]~^^ ERROR termination is not established — 1 self call(s) bind no
    where
        W<G>: Tr,
    {
        if n == 0 {
            return 0;
        }
        <W<G> as Tr>::f::<G>(n)
    }
}

pub trait Fwd {
    fn g(n: u64) -> u64;
}

impl Fwd for u8 {
    fn g(n: u64) -> u64 {
        n
    }
}

impl<X: Fwd> Fwd for Box<X> {
    fn g(n: u64) -> u64 {
        //[default]~^ WARN termination is ASSUMED, not proved — 1 self call(s) bind no `decreases` measure
        //[certify]~^^ ERROR termination is not established — 1 self call(s) bind no
        <X as Fwd>::g(n)
    }
}
