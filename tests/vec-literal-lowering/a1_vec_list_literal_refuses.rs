//@ vec-lowering: refuses
//@ vec-lowering-why: [global-alloc-dealloc-panic-free]
//! THE MOST IDIOMATIC VEC CONSTRUCTION IN RUST, and it still does not verify —
//! but as of 2026-09-20 it LOWERS, and the reason it refuses has moved.
//!
//! WHAT IT USED TO RECORD: `field projection on union
//! core::mem::maybe_uninit::MaybeUninit requires a trust-ir union
//! representation`, i.e. the bundle could not be lowered at all. `MaybeUninit`
//! is `union { uninit: (), value: ManuallyDrop<T> }` — exactly ONE field with
//! any bytes — and `field_type` now answers for that shape, because the hazard
//! its refusal guards (two live fields at offset 0) cannot arise with one.
//! Multi-payload unions keep the refusal:
//! `tests/ui/trust/union_multi_payload_field_stays_closed.rs`.
//!
//! WHAT BLOCKS IT NOW — AND I HAVE MIS-NAMED THIS FOUR TIMES, SO READ THE
//! RETRACTION BEFORE THE CLAIM.
//!
//! What is actually MEASURED: the lowering completes, and the strict gate sees
//! TWO rows — `0 trusted, 1 certified, 0 failed, 0 unknown, 1 runtime-checked`.
//! The `[assert]` row is runtime-checked, and policy B's report path did not
//! apply. That is all the default output establishes.
//!
//! WHAT I CLAIMED AND RETRACT, in order: (1) the allocator contract — no, that
//! `CONTRACT [global-alloc-dealloc-panic-free]` row is by-design conditional
//! evidence that "discharges vacuously against `Global`'s std dealloc chain …
//! and verification proceeds"; (2) a policy-B ruling about retained runtime
//! checks — no, policy B is already ruled, an exclusion fired; (3) item 1 of
//! `panic_free_drop.rs`'s staged plan; (4) **drop glue**, which I grepped out of
//! the diagnostic and committed. That was a misreading: the note is DISJUNCTIVE
//! boilerplate — "an absent callee … OR for drop glue" — and matching the second
//! half of an `or` is not a finding. `a3`/`a5` verify while dropping the same
//! `Vec<u32>`, which I offered as evidence FOR the drop-glue reading when it is
//! equally consistent with every other branch.
//!
//! WHY FOUR MISREADS IN A ROW, and this is the actionable part: the exclusion
//! note lists FOUR causes — "a generic absent callee, drop glue, a
//! `write_fmt`/`fmt::write` dispatch, or any such row in a function that uses
//! `unsafe`" — and the compiler does not say WHICH ONE FIRED. `TRUST_VANILLA_DEBUG`
//! names no callee here, which rules out the first, and the remaining three are
//! indistinguishable from the default output. A refusal whose cause cannot be
//! read is a refusal nobody can act on, and it is why this header has been wrong
//! three times and committed wrong once.
//!
//! **So the named next step was the DIAGNOSTIC, not a fix** — and it landed the
//! same day (`72b6df39c4`). The exclusion now names its cause, and it
//! discriminates: this file reports **drop glue**, while `t22`
//! (`Vec::<u32>::remove`) and the `r1/generic_mono_caller_closure_*` rows report
//! "a generic absent callee".
//!
//! SO THE RETRACTED CLAIM WAS RIGHT, AND THE RETRACTION WAS STILL CORRECT. The
//! cause IS drop glue. It was retracted because the way it had been reached —
//! matching the second half of an `or` in boilerplate — is not evidence for it,
//! and a conclusion that happens to be true is not a method. The distinction is
//! the one trust-mc states about refuting an over-approximating encoding: "not
//! evidence even when its conclusion happens to be true."
//!
//! WHAT REMAINS — and the "expansion introduces it, `to_vec` does not" reading
//! that stood here is WRONG TOO. `TRUST_DROP_GATE_DEBUG` prints the gate's plan,
//! and a1 and a3 reach an IDENTICAL one:
//!
//! ```text
//! [DROP_GATE] ty=Seq { elem: Int { width: 32, .. } } RECURSIVE_VERDICT=false
//!             trivially_no_drop=false bundled={"alloc::vec::Vec", "alloc::raw_vec::RawVec"}
//! ```
//!
//! So BOTH charge a `Vec<u32>` drop-glue row. Only a1's survives to the report.
//! The difference is therefore in what DISCHARGES it downstream, not in what
//! introduces it — which is a different question from any asked here so far, and
//! is where the next person should start.
//!
//! AND ONE STEP FURTHER, from the row inventories. Both end with exactly one
//! runtime-checked row and one skipped `CONTRACT [global-alloc-dealloc-panic-free]`:
//!
//! ```text
//! a1   1 proved, 1 runtime-checked, 1 skipped   out of 3
//! a3   0 proved, 1 runtime-checked, 1 skipped   out of 2
//! ```
//!
//! So a1 does not carry an extra FAILING row — it carries an extra PROVED one.
//! What differs is WHICH row is the runtime-checked one: in a1 it is the
//! drop-glue row (an assumption-panic row, hence fatal), in a3 it is an ordinary
//! `[assert]` (hence reported under policy B). In a3 the identically-charged
//! drop glue never becomes a surviving row at all.
//!
//! **That is the question to start from: why does the charge survive as a row in
//! a1 and not in a3, given the gate plans are identical?** Not "what discharges
//! it" — nothing visible discharges it, it is never minted.
//!
//! RULED OUT, so nobody spends a cycle on it: the number of drop SITES. a1 has
//! SEVEN `DROP_GATE` lines, a3 has eight, and a5 — which verifies — has eighteen,
//! all with the same two distinct plans. The failing program has the FEWEST.
//!
//! That is the sixth reading of this one residue, each replaced by a better
//! instrument rather than a better guess: allocator contract -> policy-B ruling
//! -> `panic_free_drop` item 1 -> drop glue (right, but read off boilerplate) ->
//! "the expansion's own glue" -> "both charge it; the discharge differs". The
//! row is small and the attributions have been consistently wrong, so measure
//! before writing the seventh.
//!
//! The original record:
//!
//!   failed to lower `main` and its local callees into typed TrustIr
//!   NativeVerificationBundle input: unsupported operation: field projection on
//!   union `core::mem::maybe_uninit::MaybeUninit` requires a trust-ir union
//!   representation
//!
//! `vec![a, b, c]` builds through a boxed slice and that path projects a field
//! of `MaybeUninit`, which is a UNION. trust-ir has no union representation, so
//! the whole bundle fails to lower and the function gets no native evidence.
//!
//! This is a missing CAPABILITY with a named requirement, not a refutation and
//! not a policy choice — and it is why `tests/daily-driver-realistic/p4.rs`
//! still fails after its `dyn` dispatch is discharged: its `main` uses `vec![]`.
//!
//! DO NOT "FIX" THIS BY SPECIAL-CASING `MaybeUninit`. The refusal is deliberate
//! and central, at `crates/trust-ir-bridge/src/lower.rs:15883`, and its comment
//! states the reason: "a positively identified union has overlapping fields,
//! while the trust-ir aggregate spelling used by this bridge has independent
//! fields. Any field projection would therefore invent struct semantics. Refuse
//! centrally so reads, writes, borrows, and address walks all fail closed."
//!
//! Projecting `MaybeUninit<T>`'s payload to `T` would also be reading possibly
//! -uninitialised memory as initialised — the exact thing the union
//! representation would have to model. The requirement is a real trust-ir
//! representation, in the `first-party/trust-ir` submodule; it fails CLOSED
//! meanwhile, which is the safe direction and why this row is a capability gap
//! rather than a hazard.
fn main() { let v: Vec<u32> = vec![1, 2, 3]; let _ = v.len(); }
