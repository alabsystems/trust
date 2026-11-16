//@ revisions: off adv strict
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Cdebuginfo=2
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict
//@[off] build-pass
//@[adv] build-pass
//@[strict] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: cycle detected
//! `tests/ui/coroutine/issue-87142.rs`, whose `start` builds MIR that mentions
//! `<() as CoroutineProviderAlt>::Coro`, an `impl Trait` associated type.
//!
//! Drop-in (release gate): stock rustc accepts this crate, and so does every
//! revision here. On `origin/main` `93f05556da` the verified lanes rejected it
//! with E0391: wfcheck computes `type_of` of the opaque `Coro`, which borrow-checks
//! its defining body `start` (and the coroutine inside it), building their MIR; inside
//! that `mir_built`, the trust-ir producer normalized `Context<()>`'s argument
//! `<() as CoroutineProviderAlt>::Coro` under the codegen typing mode
//! (`canonical_adt_args`), and the MIR oracle asked
//! `layout_of(NonNull<<() as CoroutineProviderAlt>::Coro>)` — both REVEAL the opaque,
//! demanding the `type_of` already on the stack. Which one cycled first depended on
//! query order (the upstream file, built with compiletest's flags, reached the second
//! once the first was fixed). The
//! producer now normalizes without revealing first and keys an opaque as the alias,
//! as typeck spells it; inside `mir_built` the oracle's layouts and resolutions go
//! through the producer's #48 funnel. `strict` refuses `start` and its coroutine on Trust
//! verdicts, which drop-in permits, and on nothing else.

#![feature(impl_trait_in_assoc_type, coroutine_trait, coroutines)]
#![crate_type = "lib"]

use std::ops::Coroutine;

pub trait CoroutineProviderAlt: Sized {
    type Coro: Coroutine<(), Return = (), Yield = ()>;

    fn start(ctx: Context<Self>) -> Self::Coro;
}

pub struct Context<G: 'static + CoroutineProviderAlt> {
    pub link: Box<G::Coro>,
}

impl CoroutineProviderAlt for () {
    type Coro = impl Coroutine<(), Return = (), Yield = ()>;
    fn start(ctx: Context<Self>) -> Self::Coro {
    //[strict]~^ ERROR Trust strict verification failed for `<() as opaque_projection_in_mir_built::CoroutineProviderAlt>::start`: 1 obligation(s) were not fully verified
        #[coroutine]
        move || {
        //[strict]~^ ERROR Trust strict verification failed for `<() as opaque_projection_in_mir_built::CoroutineProviderAlt>::start::{closure#0}`: coroutine executor-protocol premise is unproved
            match ctx {
                _ => (),
            }
            yield ();
        }
    }
}
