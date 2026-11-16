//~ NOTE propagated: `propagated_open_dispatch_refutation_is_failed::helper::<T>` is a still-generic call to a local body whose own row was refuted on its open dispatch `<U as propagated_open_dispatch_refutation_is_failed::Tr>::m`
//~| NOTE "proved":0,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":1,"cached":0,"total":2}
//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 open shapes (2026-10-04; docs/DECISION_QUEUE.md "OD-1" item 14): a caller of a
//! generic helper whose own row is a class (c) open-dispatch refutation. `helper<U>`
//! dispatches `<U as Tr>::m` with a raw-pointer argument, which is never admitted, so
//! its row is `failed`. `caller<T>` calls `helper::<T>`: the adversary who picks a
//! panicking `T` breaks `caller` exactly as it breaks `helper`, so `caller`'s row for
//! the call is stamped `failed` too, naming the callee's refuted site (line 1, first pin: the
//! reason a stamped row carries). Before this change it read `runtime_checked`. Control:
//! `caller_resolved` calls `helper::<W<V>>`, where the site RESOLVES (`impl<V> Tr for
//! W<V>`), so no adversary exists at these arguments and its row stays
//! `runtime_checked` (second pin), which strict and certify refuse anyway.
pub trait Tr {
    fn m(&self, p: *const u8) -> u32;
}

pub struct W<V>(pub V);

impl<V> Tr for W<V> {
    fn m(&self, _p: *const u8) -> u32 {
        1
    }
}

pub fn helper<U: Tr>(u: &U, p: *const u8) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    u.m(p)
}

pub fn caller<T: Tr>(t: &T, p: *const u8) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    helper(t, p)
}

pub fn caller_resolved<V>(w: &W<V>, p: *const u8) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^ ERROR Trust strict verification failed
    helper(w, p)
}
