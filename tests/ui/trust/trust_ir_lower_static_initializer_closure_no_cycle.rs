//@ dont-check-compiler-stderr
//@ check-pass
//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-verify-timeout-ms=2000
//@ dont-require-annotations: NOTE
// The 2 s per-obligation budget (default 20 s) removes most of this file's
// cost, because some engine runs out the budget on an obligation it cannot
// decide. It is safe: every per-function verdict was measured identical at
// 0.5 s, 2 s and 20 s (2026-09-23, 96f2019566), and the `Trust verification:`
// NOTE pins fail if the smaller budget ever changes one.

//! Regression for the `core::task::wake` query cycles in `RawWaker::NOOP` and
//! `Waker::{from_fn_ptr}::VTABLE`. Lowering the nested closures must decline
//! producer-side evaluation of the local static and keep the MIR-oracle const
//! operand opaque: asking CTFE for either initializer while CTFE is building the
//! closure's MIR recursively requests it and reports E0391.
//!
//! `trust_ir_lower_static_ctfe_no_cycle.rs` covers the broader producer-only
//! shape with verification disabled. This sibling deliberately enters the live
//! verifier path; its expected advisory diagnostics make the gate anti-vacuous
//! and prove that cycle avoidance survives verifier-side MIR extraction too.

struct Vtable {
    clone: unsafe fn(*const ()) -> *const (),
    wake: unsafe fn(*const ()),
}

struct Raw {
    data: *const (),
    vtable: &'static Vtable,
}

impl Vtable {
    const unsafe fn new(
        clone: unsafe fn(*const ()) -> *const (),
        wake: unsafe fn(*const ()),
    ) -> Self {
        Self { clone, wake }
    }
}

impl Raw {
    // The sibling shape in `RawWaker::NOOP`: the nested VTABLE closure reads
    // its enclosing associated const rather than the VTABLE static directly.
    const NOOP: Raw = {
        const VTABLE: Vtable = unsafe {
            Vtable::new(
                |this| {
                    let _recursive_value = Raw::NOOP;
                    this
                },
                |_| {},
            )
        };
        Raw { data: core::ptr::null(), vtable: &VTABLE }
    };
}

const fn from_fn_ptr(f: fn()) -> *const Vtable {
    //~^ WARN Trust Level 0 safety verification incomplete for `trust_ir_lower_static_initializer_closure_no_cycle::from_fn_ptr`
    //~| NOTE Trust verification: 0 proved, 1 failed, 0 unknown
    static VTABLE: Vtable = unsafe {
        Vtable::new(
            |this| {
                let _recursive_address = &VTABLE;
                this
            },
            |_| {},
        )
    };
    let _ = f;
    &VTABLE
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete for `trust_ir_lower_static_initializer_closure_no_cycle::main`
    //~| NOTE Trust verification: 2 proved, 10 failed, 5 unknown
    //~| WARN termination is ASSUMED, not proved — 1 self reference(s) take this function as a value
    // Trust (GLR-1, 2026-10-26, docs/DECISION_QUEUE.md): 5 unknown, was 4. `main` calls
    // through the table's fn-pointer fields below, which the indirect-call gate refuses;
    // since GLR-1 that refusal publishes an `unknown` `native-verification-gap` row on
    // every lane, this advisory one included.
    // Trust (D9 review F5, 2026-09-27; measured on the first D9 stage 1,
    // `22dea9d082b`: the warning fires and the test passes): `main` passes
    // ITSELF as a `fn()` below, a self reference the D9 charge now records as
    // `assumption:termination-unmeasured` (a warning here, under advisory). It is
    // the disclosed cost of F5: `from_fn_ptr` only stores the pointer and never
    // calls it, which the census cannot tell apart from a call-back.
    let table = from_fn_ptr(main);
    // Keep both function-pointer fields live so the initializer is not a
    // dead-data-only approximation of core's RawWakerVTable shape.
    unsafe {
        ((*table).wake)(((*table).clone)(core::ptr::null()));
        (Raw::NOOP.vtable.wake)((Raw::NOOP.vtable.clone)(Raw::NOOP.data));
    }
}
