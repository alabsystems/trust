//@ dont-check-compiler-stderr
//@ check-pass
//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=on -Ztrust-policy=advisory

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
    let table = from_fn_ptr(main);
    // Keep both function-pointer fields live so the initializer is not a
    // dead-data-only approximation of core's RawWakerVTable shape.
    unsafe {
        ((*table).wake)(((*table).clone)(core::ptr::null()));
        (Raw::NOOP.vtable.wake)((Raw::NOOP.vtable.clone)(Raw::NOOP.data));
    }
}
