//@ needs-trust-verify
//@ build-pass
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-ir-lower-mutate-finalization
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE

//! **Regression: a producer-side invalid module must not kill the ADVISORY lane.**
//!
//! `trust_ir_crate_finalize` raised `trust-ir-lower semantic finalization failed`
//! as a `fatal` in every policy. That failure is a PRODUCER defect — the
//! crate-level Trust-IR module did not validate — and its consequence is that
//! the native lane has no bundle, i.e. a loss of COVERAGE. An invalid module
//! proves nothing, so nothing unproved can be smuggled through it.
//!
//! Advisory's contract is that the crate COMPILES while the prover is improved
//! and every obligation is reported. A crate-fatal producer defect breaks that
//! in the worst way: the user gets no census at all, for a defect in the
//! compiler rather than in their own code. MEASURED 2026-09-07 on
//! `first-party/ty`'s `tla-im`: 663 functions verified, 610 warnings emitted,
//! all of it discarded on one `CallArgTypeMismatch`.
//!
//! # The shape is INCIDENTAL, and it has been re-pointed twice in one day
//!
//! This file needs A crate whose module does not validate; it does not care
//! WHICH producer gap supplies one, and it must never be the reason a gap stays
//! open.
//!
//! 1. The original shape was `nodes::rrb::Node::<A>::size` reduced. `611f4f9086`
//!    fixed it, and this file went on passing for months afterwards because
//!    `build-pass` passes just as well on a crate with nothing wrong with it —
//!    only the strict control said anything. That asymmetry is why this half now
//!    pins the WARNING TEXT: both halves go red together.
//! 2. The second shape was a const-generic array-by-value parameter. The
//!    declaration-signing campaign closed it the same afternoon, and both halves
//!    went red together — the mechanism working, not failing.
//! 3. The third shape was `println!("{:?}", ..)` of a container, whose
//!    `std::io::_print` declaration takes `fmt::Arguments` BY VALUE. The
//!    2026-09-16 rvalue-snapshot landing LOWERED that argument (the producer
//!    now signs `_print` as `(struct.K) -> ()`), and both halves went red
//!    together — again the mechanism working.
//! 4. The fourth shape was a fn-POINTER parameter. It lasted the length of a
//!    push: origin signed fn-pointer parameters (`5e291566326`) while the
//!    re-point was in flight, and both halves went red together AGAIN.
//! 5. The pair now RIDES NO PRODUCER GAP. `-Ztrust-ir-lower-mutate-finalization`
//!    hands the finalizer the real validator's refusals of a separate
//!    one-declaration probe module (`trust_thir_lower::finalization_probe`)
//!    carrying the one encoding v41 refuses by construction. Four re-points in
//!    two days is a test measuring the calendar, which this file's own rule
//!    named as the failure to avoid — "replace both files with a routing test"
//!    — and this is that routing test. The probe fails closed: if the validator
//!    ever accepts that encoding again, the probe reports a `ProbeNotRefused`
//!    refusal instead of passing quietly.
//!
//! Shape 3 was chosen as durable by DESIGN rather than by luck; it lasted one
//! day. The paragraph below records why it was believed durable — the belief
//! rested on a drop that the lowering retired — and stays as the history. `fmt::Arguments` is deliberately outside
//! `ty_is_foundational` (it carries fn pointers to arbitrary user `Display`
//! impls by value), and signing it is explicitly forbidden by the argument-drop
//! coherence gate: `lower_call_args` DROPS the `Arguments` construction for a
//! unit-returning or diverging sink, and `param_tys_poisoned` withdraws the
//! callee's signature whenever an argument was dropped, precisely so a wider
//! type reader cannot turn that drop into a `CallArgCountMismatch`. Closing this
//! one is therefore not a signing improvement; it is a different decision.
//!
//! IF IT IS RE-POINTED A FOURTH TIME, keep the discipline: this half pins the
//! warning text and `build-pass`; the control pins that SOME refusal arrives.
//! `reports/2026-09-16-rust-abi-vararg-the-locality-guard.md` carries the
//! residue table to choose from. If no producer gap refuses any more, replace
//! both files with a routing test rather than leaving two files that pass
//! because there is nothing left to catch.

// Nothing in this crate is wrong. The invalid module comes from
// `-Ztrust-ir-lower-mutate-finalization`: the finalizer is handed the REAL
// validator's refusals of a separate one-declaration module built to carry the
// exact encoding v41 refuses (`CallingConv::Rust` + `params: [] + is_vararg:
// true`), so what is routed is the validator's own sentence — and the routing
// is the ONLY thing this pair asserts.
fn main() {}

// The crate-finalization diagnostic is SPANLESS — it is about the crate's
// module, not about any one item — so it takes compiletest's file-level
// annotation form rather than a caret pointing at an item.
//~? WARN trust-ir-lower semantic finalization failed
