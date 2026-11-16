//@ needs-trust-verify
//@ revisions: verify strict
//@ aux-build: take_raw_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-ir-lower=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ check-fail
//! **A reference to a pointer-typed pointee is signed, and a dropped borrow still cannot
//! reach it** (`crates/trust-thir-lower/src/lib.rs`: `recover_callee_param_tys` and
//! `ref_arg_pointee_may_be_pointer`).
//!
//! `take_raw(p: &*const u8)` called as `take_raw(&q)`. `*const u8` ITSELF spells `Ty::Ptr`, so
//! `&P` and `P` share one spelling and the arity+type check a signed declaration rests on could
//! not see a DROPPED BORROW between them. Measured 2026-09-15 by adversarial review of the first
//! cut that signed this shape: the producer carried the pointer-typed local by VALUE
//! (`try_lower_receiver_place_value`), so the call was lowered as `take_raw(q)`, type-checked
//! against the signed declaration, and went from REFUSED to an UNFAITHFUL ACCEPTANCE.
//!
//! RE-PINNED 2026-09-29 (thir-generic-instance-callee). The guard that answered that by leaving
//! every such DECLARATION unsigned is retired; the defect is closed at the CALL SITE, where this
//! pin said it belonged. No value-for-pointer carrier may stand in for a reference whose pointee
//! is (or may be) a pointer, so `&q` must be a real borrow — and for a raw-pointer PARAMETER there
//! is none yet (`Borrow(non-scalar pointee)`: the named-local snapshot admits no unledgered
//! `Ty::Ptr`), so the CALLING BODY is refused at its own call site, while `take_raw`'s declaration
//! is now signed `(ptr) -> u8`. The observable result is unchanged and MUST stay red: the native
//! lane reports the call `unsupported`, the caller's one obligation stays `runtime-checked`, and
//! strict verification refuses the crate — "Trust strict verification failed for `call_raw`: 1
//! obligation(s) were not fully verified". If this file ever compiles clean, `&q` gained a real
//! borrow slot (then re-pin it `check-pass` and say so). A carrier coming back (a soundness
//! regression: the module would be a program that is not this one) does NOT make revision
//! `verify` compile clean; revision `strict` is what catches it, below.
//!
//! REVISION `strict` (added 2026-10-15, docs/DECISION_QUEUE.md REF-TO-PTR-SIGN-1) is the one
//! with teeth. MEASURED on a stage 1 with the call-site checks removed: `call_raw` lowered as
//! `call @take_raw(%0)` (the review's dropped borrow, against the signed `(ptr) -> (u8)`) and
//! spliced, and revision `verify` STILL failed with its one error, because `take_raw` is a
//! verify-off extern callee that the verifier treats as havoc whichever value reaches it. So
//! the verification error alone never detected the hazard. Under `-Ztrust-ir-lower=strict` the
//! call-site refusal IS the error (`Borrow(non-scalar pointee)`), and on that build it was
//! missing.
//!
//! Its companion `trust_ir_lower_ref_to_pointer_carrier_refused.rs` pins the receiver and place
//! shapes under strict lowering, `trust_ir_lower_ref_to_pointer_params_sign.rs` the signed
//! shapes, and `tests/run-make/trust-ir-ref-to-pointer-declarations` this exact shape against the
//! emitted module.
extern crate take_raw_dep;

pub fn call_raw(q: *const u8) -> u8 {
    //[strict]~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    take_raw_dep::take_raw(&q)
}
//[verify]~^^^^ ERROR Trust strict verification failed for `trust_ir_lower_ref_to_pointer_param_declines::call_raw`
