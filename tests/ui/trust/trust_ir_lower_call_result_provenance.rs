//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-CRP): the CALL-RESULT ESCAPE LEDGER — the third writer of the class
//! wave-FIL split, and the one wave-FIL's own doc comment named as NOT repaired.
//!
//! `interior_ptrs` is one of only three classes the two return-escape guards except,
//! and the guard's own comment says why: it means "addressing caller memory that
//! outlives the call". wave-CR pushed every thin-reference CALL RESULT into it,
//! reasoning that "the callee's frame is gone, so it can only designate caller
//! memory, a global, or the heap". That does not follow. **Caller memory includes
//! the caller's own frame.** A callee cannot return a pointer to its own frame, but
//! it can hand back a reference derived from a reference ARGUMENT, and that argument
//! may be a borrow of a local right here.
//!
//! Probed on the c9 control (2026-08-31), one function apart:
//!
//! ```ignore
//! fn id(x: &i32) -> &i32 { x }
//! fn escape_direct() -> *const i32 { let w = 5; &w as *const i32 }      // REFUSED
//! fn escape()        -> *const i32 { let w = 5; id(&w) as *const i32 }  // was CLEAN
//! ```
//!
//! A one-line identity call laundered a dead frame address past the very guard the
//! direct spelling trips. The guard was not wrong; the ledger lied to it.
//!
//! THE RULE: the result outlives this frame only if every argument that could carry
//! frame provenance already does. Fail-closed on the LEDGER rather than on a type —
//! an argument is admitted when this lowering never minted it as a borrow pointer at
//! all, or when it is one of the three classes that DO outlive the frame (a ref
//! PARAM, a `'static` global, or an interior pointer derived from one of those).
//! Anything else puts the result in `frame_interior_ptrs`, which no guard excepts.
//!
//! `borrow_ptrs` and `mut_borrow_ptrs` are deliberately UNTOUCHED: they govern the
//! `Deref` load and the `*r = v` store, which are faithful at a frame address exactly
//! as they are at a caller address. Only the ESCAPE question turns on provenance, so
//! only the escape ledger is gated — which is what keeps this repair narrow enough to
//! read, and what the A-cases below pin.
//!
//! IT IS NOT A MISCOMPILE AND NEVER WAS, for the same reason wave-FIL was not: the
//! R-cases return a raw pointer to dead memory in the SOURCE too — legal Rust, only
//! the dereference is UB — and rustc's own MIR returns the same address. What was
//! wrong is the CLAIM. A consumer reading `interior_ptrs` as its documentation
//! licenses concluded something false about a returned pointer, and the only thing
//! standing between that and an exploitable shape was which spellings borrowck
//! happens to permit.
//!
//! Under `strict`, so a refusal is a compile error AND the MIR re-derived from the
//! producer's own trust-ir must still agree with the built MIR for every body that
//! keeps lowering. The tag is deliberately not asserted, only that the body refuses.

#![allow(dead_code)]

pub struct S {
    pub a: i32,
    pub b: i32,
}

pub static G: i32 = 7;

// The laundering callee. Its own body is a ref-param passthrough and must stay clean.
pub fn id(x: &i32) -> &i32 {
    x
}

pub fn id2<'a>(x: &'a i32, _y: &'a i32) -> &'a i32 {
    x
}

pub fn fst(s: &S) -> &i32 {
    &s.a
}

// ---------------------------------------------------------------------------
// MUST REFUSE. Each was clean before wave-CRP; each returns, past the frame that
// owns it, an address obtained by handing a frame borrow to a callee. Delete the
// argument gate and these stop erroring — nothing else in the tree would say so.
// ---------------------------------------------------------------------------

// R1 — the shipped witness. The identity call is the whole laundering mechanism.
pub fn call_launders_frame_addr() -> *const i32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let w = 5i32;
    id(&w) as *const i32
}

// R2 — the gate is over EVERY argument, not the first. A safe first argument must
// not excuse a frame borrow in second position: the callee's signature does not say
// which input the result was derived from, so any frame-provenance argument poisons
// the result. An `all()` weakened to "the first" leaves this clean.
pub fn second_arg_also_poisons(p: &'static i32) -> *const i32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let w = 5i32;
    id2(p, &w) as *const i32
}

// R3 — the frame borrow reaches the callee through a STRUCT, so the argument is a
// `&local` snapshot of an aggregate rather than a scalar. Same conclusion: the
// returned interior points into this frame.
pub fn struct_arg_poisons() -> *const i32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let s = S { a: 1, b: 2 };
    fst(&s) as *const i32
}

// ---------------------------------------------------------------------------
// MUST STAY CLEAN. The repair is an argument gate, not a retreat from wave-CR: a
// call result whose provenance really does outlive the frame keeps its escape
// ticket, and a call result that never escapes keeps lowering regardless.
// ---------------------------------------------------------------------------

// A1 — a ref PARAM argument. This is wave-CR's motivating shape and the one thing
// this repair must not cost: the callee's result is derived from caller memory that
// outlives the call, so returning it onward is faithful.
pub fn ref_param_arg_still_escapes(p: &i32) -> &i32 {
    id(p)
}

// A2 — the same through a struct ref param, so the result is a genuine INTERIOR
// pointer into caller memory. Pins that the gate reads the ledger and not the arity.
pub fn ref_param_struct_still_escapes(s: &S) -> &i32 {
    fst(s)
}

// A3 — a `'static` GLOBAL argument. Not a frame address by construction.
pub fn global_arg_still_escapes() -> &'static i32 {
    id(&G)
}

// A4 — a frame borrow handed to a call whose result is IMMEDIATELY DEREFERENCED and
// never returned. `borrow_ptrs` is untouched by the repair, so the `Deref` load still
// lowers; moving the result out of `borrow_ptrs` instead of out of `interior_ptrs`
// would break exactly this body and no test above would notice.
pub fn frame_arg_deref_still_lowers() -> i32 {
    let w = 5i32;
    *id(&w)
}

// A5 — the same for a struct interior, one level deeper.
pub fn frame_struct_deref_still_lowers() -> i32 {
    let s = S { a: 1, b: 2 };
    *fst(&s)
}
