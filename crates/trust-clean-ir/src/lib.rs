// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! Clean -> TrustIR.
//!
//! The two-language design makes Rust and Clean co-equal authoritative
//! languages and names TrustIR the target universal IR. Rust already reaches
//! TrustIR (the THIR frontend behind `-Ztrust-ir-lower`, plus the MIR-derived
//! compatibility spine). Clean did not: its island is parsed, kernel-checked,
//! and planned into a [`CleanOriginPlan`], and the only consumer of that plan
//! emitted rustc MIR. The two languages therefore met at MIR.
//!
//! This module is the second consumer of that same plan:
//!
//! ```text
//! clean { … } → parse → kernel check → CleanOriginPlan ─┬→ clean_origin_mir → MIR
//!                                                       └→ this crate       → TrustIR
//! ```
//!
//! # What a plan already guarantees
//!
//! A [`CleanOriginPlan`] cannot exist unless `plan_clean_origin_body` re-checked
//! the declaration's provenance against the CIC kernel and derived a **total**
//! [`CarrierSignature`] — one carrier per argument and one for the result. So
//! this crate never asks "is this Clean declaration real"; that is settled
//! before it is called. It maps a sealed plan into a second IR.
//!
//! # GATING — read this before trusting a body from here
//!
//! **This crate is not proof authority and is not a gate.** The Clean-origin
//! CALL lane is the one direction in Trust that PRODUCES A VALUE, so a
//! disagreement between the Clean `def` and the emitted body is a wrong binary,
//! not a failed proof. That is why `trust-clean-origin` gates emitted MIR with
//! `admit_lowering`: the body is reflected back into a Clean term and put to the
//! kernel at the carrier type.
//!
//! A TrustIR function returned from here has had **no such gate applied to it**
//! symbolically. At `u8` it now has an EXHAUSTIVE one: see
//! `tests/exhaustive_kernel_agreement.rs`, which sweeps the entire domain of a
//! `u8` carrier (256 unary inputs, 65 536 binary pairs per declaration) and has
//! the KERNEL decide every agreement. Two total functions on a finite domain
//! that agree everywhere are the same function, so at that carrier this is
//! extensional equality, not a sample -- 394 752 kernel-decided agreements
//! across twelve declarations. It is still not `admit_lowering`: enumeration
//! holds at `u8` only, while a reflector's symbolic result would hold at every
//! width at once.
//! It is faithful to the plan, and the plan rests on a kernel verdict. W2 now
//! adds one deliberately narrow production exception to the historical
//! body-ungated state: an independent crate reflects the *actual emitted*
//! `WrappingBinOp` Function for Add/Sub/Mul at exact UInt8/16/32/64 and the
//! kernel re-checks that reflected term at the carrier. Two consequences, both
//! binding:
//!
//! * Do not hand a function from here to codegen merely because this producer
//!   emitted it. Only a row carrying the private, final-subject-authenticated
//!   W2 `gate` permission has body authority, and even that same-crate evidence
//!   is not G5 cross-crate linking or G7 codegen authority. Every other shape
//!   remains body-ungated. The general gated value-producing lane remains
//!   `clean_origin_mir`.
//!
//!   **This crate IS on a compilation path, in one narrow role** — the older
//!   note here said nothing in `compiler/` called it, and that has been stale
//!   since the signature-agreement check landed.
//!   `rustc_mir_transform` depends on this crate (`Cargo.toml:53`) and
//!   `clean_origin_mir.rs:351` calls [`trust_ir_func_ty`] on the sealed plan,
//!   making a TrustIR signature that disagrees with the plan's arity a FATAL
//!   compilation error. That is a real wrong-binary gate: two independent
//!   readings of one carrier signature must agree. A REFUSAL remains nonfatal
//!   for non-target shapes. For W2 WrappingBinOp, signature lowering and body
//!   emission refusals are fatal self-disagreements and cannot become skip or
//!   general-lane rows.
//!
//!   The signature is gated for every planned shape. Body gating exists only
//!   for the exact W2 WrappingBinOp slice above; the broader independent
//!   reflectors below remain library-level evidence rather than shipped
//!   permissions. Both boundaries matter.
//!
//! **INDEPENDENT reflectors now exist** (`tests/independent_reflector_{a,b,c}.rs`),
//! and this supersedes the co-authorship caveat that stood here. Each was written
//! by an author under a hard prohibition on reading THIS FILE, the co-authored
//! `symbolic_reflection.rs`, or `trust-clean-origin/src/reflect.rs` — working only
//! from the TrustIR spec and Clean's own semantics, from three different angles.
//! They may CALL `emit_clean_origin_function` to obtain a body to reflect; they
//! may not read how it thinks. That removes the specific cancellation mechanism
//! the old caveat named: a reflector cannot invert a mistake it has never seen.
//!
//! 61 tests across the three, at u8/u16/u32/u64, covering projection, constants,
//! Add/Sub/Mul/And/Or, nesting, and Select over `<`, `<=` and `=`. Each carries
//! its own mutation battery against the EMITTED body (swapped select arms,
//! Add->Sub, flipped operands, shifted constant, Ult->Ule) and its own
//! non-vacuity control.
//!
//! Two mutations SURVIVE, both deliberately, and both are recorded rather than
//! hidden: a dead `Copy` before the `Return` (it denotes nothing), and reordering
//! two independent pure instructions (semantics-preserving, since definitions are
//! substituted into uses). Each is used as a POSITIVE CONTROL proving the
//! survivor assertion is not dead code — without one, "0 survivors" would be
//! indistinguishable from a battery that cannot report a survivor at all. The
//! real limit they record: the round trip cannot see instructions nobody reads.
//!
//! What remains weaker than the MIR lane: same model family authored all of them,
//! so correlated priors are not excluded — only the read-the-emitter mechanism is.
//!
//! A CO-AUTHORED symbolic reflector also exists, kept alongside the independent
//! ones as a second spelling rather than as the primary evidence:
//! `tests/symbolic_reflection.rs` rebuilds an emitted straight-line body as a
//! Clean term and asks the kernel for `is_def_eq` against the declaration --
//! one judgement covering ALL inputs at a width, which enumeration cannot reach
//! above `u8`. Measured: 28 agreements (7 shapes x u8/u16/u32/u64), covering
//! projection, constants, `Add`/`Sub`/`Mul`, nesting, AND `Select` over `<`.
//! The `Decidable` instance a select needs is CITED (`instDecidableUInt8Lt`, the
//! constant Clean itself elaborates to), never BUILT -- a comparison with no
//! canonical instance name refuses by name.
//!
//! It does NOT close this gap, and the reason is the one stated below: a
//! reflector that inverts precisely this emitter's mistake makes the round trip
//! cancel, so a symmetric error stays invisible. Its failure is a real defect;
//! its success is evidence, not proof.
//!
//! **The residual risk is now MEASURED rather than asserted.** "Co-authored" was
//! doing too much work as a blanket disclaimer, and the specific hazard it names
//! is falsifiable: if the reflector were a trivial inverse -- or effectively a
//! constant function rebuilding the declaration whatever it was handed -- it
//! would accept any emitted body and every agreement row would be vacuous. So a
//! mutation battery breaks the EMITTED body (the `Function` the emitter actually
//! produced) and requires the kernel to REJECT each one: a swapped select arm,
//! `Add` lowered as `Sub`, swapped operands on a non-commutative op, a shifted
//! constant, and `<` widened to `<=` -- the off-by-one that differs at exactly
//! one point of the domain. Ten mutations across two widths, all rejected.
//!
//! That establishes the reflector is SENSITIVE TO EMITTED STRUCTURE, so the
//! round trip does not collapse. It still does not establish independence: a
//! mutation this reflector inverts in exactly the same wrong way stays
//! invisible, and only a reflector written by someone who has not read this
//! emitter closes that. Two things bound the damage without
//! substituting for independence -- the exhaustive `u8` gate catches exactly the
//! symmetric errors it could hide (no reflector sits in that loop), and the
//! reflection targets a CANONICAL spelling (`UInt8.add a b`) where Clean
//! elaborates to typeclass-mediated `HAdd.hAdd` with instance arguments, so the
//! kernel must do real definitional work to accept. Comparison and `Select`
//! refuse by name rather than being approximated.
//! * When that reflector is written, it must be an INDEPENDENT spelling, as the
//!   MIR side's is. A reflector co-authored with this emitter would make the
//!   gate a round trip and prove nothing.
//!
//! Until then the honest description of this lane is: a faithful re-spelling of
//! a kernel-checked plan into TrustIR, suitable for analysis and for feeding the
//! TrustIR spine, and not a proof-carrying substitute for the MIR lane.
//!
//! # Wiring into the compiler — the recording path (DECIDED 2026-08-27)
//!
//! The open decision this section used to hold is CLOSED, exactly on the terms
//! it demanded: Clean-origin TrustIR got its OWN recording path, gated on its
//! own evidence — the kernel verdict — feeding the same consumer. Design of
//! record: `docs/design/2026-08-27-two-language-direct-to-trust-ir.md` §3.
//! The shipped shape:
//!
//! * `rustc_mir_transform::clean_origin_ir::collect_clean_origin_ir` runs at
//!   the `rustc_interface` finalize seam, ONLY under verification: it demands
//!   each gated body, re-derives the kernel environment, re-plans, re-extracts
//!   the cached emitted MIR, RE-RUNS `admit_lowering` fresh (the export lane's
//!   independence discipline — on a warm cache the demand is not a gate
//!   execution), and only then calls [`emit_clean_origin_function`]. A
//!   [`CleanIrRefusal`] is normally a skip-with-reason row; for the already
//!   targeted W2 WrappingBinOp population, signature/emission/carrier-gate
//!   disagreement is fatal and cannot reroute to general. An environment or
//!   MIR gate refusal on any registry def is fatal (the environment disagreeing
//!   with itself).
//! * `trust_thir_lower::clean_origin_join::append_clean_origin` appends the
//!   records to the assembled per-crate Module: dense ids minted at push,
//!   `FuncTy` interned by equality, `Producer::Clean` stamped, ZERO claim
//!   channels (the authority tripwire re-runs after the append), each function
//!   validated per-function before publication, and a `DesignOnly` disclosure
//!   SpecModule (`@trust-internal::clean-origin-disclosure-v1`) carrying each
//!   row's tier IN-BAND. Most rows remain tier `structural`/`kernel-tv` with
//!   body `ungated`; exact W2 WrappingBinOp rows are tier `gate`, with an
//!   affine token rebound after final id/type/provenance assignment and a
//!   digest of that exact published Function.
//! * Same-crate Rust→Clean call edges are re-pointed to the admitted Clean
//!   Function and certified for remap shape. Matching is on the ledger's EXACT
//!   same-crate source `DefIndex` — a same-path/different-identity candidate is
//!   fatal, so the canonical def path corroborates identity but never confers
//!   it — and on the edge's operand and result TYPES against the target
//!   signature, not merely on arity; a position the seam cannot decide is
//!   linked but disclosed in the row's `type_unchecked`. That is the landed
//!   IR-5 same-crate join witnessed by runmake; it is still not G5
//!   digest-bound cross-crate linking.
//!
//! The rejected alternative stays recorded because it stays tempting:
//! `trust-thir-lower`'s flip registry is where Rust-origin bodies reach the
//! spine, and joining it is WRONG — `flip_registry::record_green` requires a
//! `Lowered` produced by THIR lowering, a derived-MIR differential verdict, a
//! `SourceHeaderCorrespondence`, HIR-loop binding provenance, and a lineage
//! digest, every one of which exists to prove *derived* MIR agrees with
//! *built* MIR for a Rust body. A Clean-origin body cannot manufacture that
//! evidence without faking exactly the thing the gates check.
//!
//! # Coverage
//!
//! All thirteen [`CleanOriginShape`]s emit. Eleven need nothing but the plan;
//! the two recursion shapes additionally need a [`NatRuntime`], because they
//! compute at the unbounded bignum `Nat` and no machine width is a faithful
//! substitute for it.
//!
//! # The recursion shapes are NOT wired to the in-compiler seam, and why
//!
//! `rustc_mir_transform::clean_origin_ir` calls [`emit_clean_origin_function`]
//! — the no-runtime entry — so both recursion shapes skip there. Measured on
//! the 2026-08-30 Clean corpus scorecard, they skip for the CARRIER reason and
//! not for [`CleanIrRefusal::RecursionNeedsNatRuntime`]: both are `Nat -> Nat`
//! in every position by plan construction, so [`trust_ir_func_ty`] refuses the
//! SIGNATURE before the body emitter is ever reached.
//!
//! Passing a [`NatRuntime`] there would not fix it, and would be worse than the
//! skip. Three facts were named here; the v43 handle adoption settles the
//! FIRST of them and leaves the other two standing, so the conclusion is
//! unchanged:
//!
//! * ~~the four runtime callees are not in the crate `Module`, and only a
//!   producer that owns the Module can mint them~~ — SETTLED.
//!   [`declare_pinned_nat_runtime`] mints them, as the bodyless `External` C
//!   declarations trust-ir's validator pins, and
//!   [`NatRuntime::check_pinned_callees`] re-derives from a finished module
//!   that each call edge reaches its own pinned shim. A seam that owns the
//!   `Module` can now do this correctly; it still has to do it.
//! * `clean_origin_join::append_clean_origin` re-mints the appended function's
//!   [`FuncId`] and rewrites NOTHING inside its body, so a self-referential
//!   body appended there calls whichever function holds the placeholder index.
//!   STILL TRUE, and now explicitly fail-closed on the other side as well: the
//!   join's two general-lane type remaps REFUSE a `Ty::Handle` outright,
//!   because a join that re-mints ids without carrying the pinned declarations
//!   would strand the handle's only legal origin;
//! * the whole-module validator that would notice is a debug-gated tripwire
//!   that fails no build, and the per-record validation runs over a
//!   ONE-function mini-module, where a self-call to id 0 resolves to itself.
//!   STILL TRUE.
//!
//! So the emitted-but-mispointed body would typecheck, validate and publish.
//! [`callee_edges`] is the precondition a seam must check before appending such
//! a record, and [`CleanIrRefusal::CallEdgeWithoutOwningModuleIdentity`] is
//! this crate refusing to hand one to a caller that cannot.
//!
//! The capability is not lost meanwhile: the same declarations are recorded by
//! the GENERAL lane (clean-compiler's own pipeline, merged with real id
//! remapping) at tier `general` — claim-free, ungated, and by design never a
//! link target.
//!
//! **All thirteen are checked by EXECUTION against the CIC kernel**, but the
//! two groups are not checked over the same domain, and the difference matters.
//!
//! * the eleven straight-line shapes run over the WHOLE domain of their carrier
//!   at `u8` and `u16` — exhaustive, including a 65 536-pair sweep.
//! * the two recursion shapes run over a small range of inputs against a
//!   one-limb model of `Nat` supplied by the test. `trust_ir::interpret` cannot
//!   execute a call to a bodyless declaration (`MissingBlock`) and has no
//!   host-call hook, so the runtime is given TrustIR bodies in the test. That is
//!   possible without weakening the emitter because [`NatRuntime::carrier`]
//!   lets the CALLER choose: production passes [`NatCarrier::PinnedHandle`] —
//!   the nominal opaque handle `handle<"Nat", "trust_bignum::Nat">` — and the
//!   harness passes a DECLARED [`NatCarrier::ExecutableSubstitute`]. The
//!   emitter never learns a width either way.
//!
//!   That carrier was a bare `Ty::Ptr` until trust-ir v43 supplied
//!   [`trust_ir::ty::Ty::Handle`], and the difference is not cosmetic. A `Ptr`
//!   is POINTER-LIKE, so `GEP`/`Load`/`PtrToInt` and every cast are well-typed
//!   on it and nothing in the format forbids dereferencing a `Nat`; and it is
//!   the same type EVERY other opaque runtime would use, so one runtime's
//!   handle satisfied another's entry point by construction. The design of
//!   record (§6.4) requires a nominal handle plus validate-time pinning of the
//!   callee identities before any `Nat` shape reaches a codegen exit; that is
//!   what [`declare_pinned_nat_runtime`] and
//!   [`NatRuntime::check_pinned_callees`] supply.
//!
//! A single limb is faithful to `Nat` exactly while values stay below
//! `u64::MAX`; outside that range the model wraps and `Nat` does not. So the
//! recursion evidence is real but BOUNDED, and is not a proof for arbitrary
//! `Nat`.
//!
//! **That bound now FAILS CLOSED, and it is demonstrated rather than assumed.**
//! The open question a bounded model leaves is whether exceeding the range would
//! be NOTICED -- a wrapped `add` produces a perfectly well-formed number, and
//! every structural check would still be satisfied by it. `nat_recursion.rs`'s
//! `a_limb_model_that_exceeds_its_range_is_caught_by_the_kernel` answers it by
//! mutation: the same emitter and the same recursion run against a limb model
//! whose `add` truncates to 6 bits -- the identical failure a real one-limb model
//! has at `u64::MAX`, at a width reachable in a test -- and the kernel, which
//! computes over unbounded `Nat`, REJECTS the truncated answer. So the harness
//! can tell a faithful limb model from a diverged one, which is what makes the
//! bounded evidence trustworthy inside its range. It is not a formality either: it caught two emitter defects that every
//! structural check passed — a `NatConst` that dropped its literal, in two
//! places at once.
//!
//! A refusal is never a silent fallback to an approximate body, and emitting
//! the recursion shapes at a machine width so the interpreter could run them
//! would be exactly the wrap the `Nat` refusal exists to prevent.
//!
//! # RELEASE: which handles the emitted body frees, and which it LEAKS
//!
//! Until 2026-09-17 a `Nat` handle was never released. `TRUSTED_HANDLE_RUNTIMES`
//! pinned no release entry point, so `Nat`-shaped Clean code was
//! *correct-by-leak*: one allocation lost per constructed value, per frame,
//! disclosed rather than hidden. trust-ir then ratified the fifth pin row
//! ([`NAT_RELEASE_ROLE`], symbol `trust_bignum_nat_drop`, signature
//! `(H) -> ()`; `SPEC_RATIFICATIONS` §7) and `trust-bignum` shipped the shim,
//! so the emitter can release — and this section states exactly what it does
//! and does not release, because the two directions fail very differently: a
//! leak loses memory, a release the emitter cannot justify is a double free or
//! a use-after-free inside a TRUSTED runtime that nothing downstream checks.
//!
//! **Nothing downstream checks it.** `validate_module` makes NO liveness claim
//! about a handle: handle values are deliberately non-linear (the ratified
//! transport set admits `Copy` and `Select`), so two SSA values may denote one
//! allocation, and a module that double-releases or reads after release
//! VALIDATES — trust-ir pins that as a non-guarantee with two tests. trust-cg
//! admits the call as pinned-runtime transport and decides nothing about
//! lifetime either. `TRUST.md` item 9(c) is where the trusted base records it.
//! So the discipline below is the ONLY thing standing between this producer
//! and a corrupt heap, which is why it is conservative.
//!
//! ## The two measured facts it rests on
//!
//! Both are properties of the shims (`trust-bignum/src/handle_abi.rs`), each
//! pinned by a test there rather than assumed here:
//!
//! 1. **`from_u64` / `add` / `sub` ALLOCATE FRESH.** Each returns
//!    `Box::into_raw` of a new `Nat` that aliases no operand and no earlier
//!    result. Structural, not conventional: the wrapped methods are
//!    `(&self, &Self) -> Self`, so they cannot return an operand.
//! 2. **`add` / `sub` / `is_zero` only BORROW.** They take `*const Nat` and
//!    reborrow shared; none consumes, frees or mutates. So a handle survives
//!    every call that reads it, and releasing an operand AFTER the arithmetic
//!    that read it is correct.
//!
//! ## The classification
//!
//! Every handle SSA value in an emitted recursion falls in exactly one class:
//!
//! | provenance | class | released? |
//! |---|---|---|
//! | a block PARAMETER (`n`) | the CALLER's allocation | **never** |
//! | `from_u64` / `add` / `sub` result | fresh, ours | yes, unless returned or withheld |
//! | the SELF-CALL's result | fresh iff this body is return-fresh | only then |
//! | the value being RETURNED | transferred to the caller | **never** |
//!
//! The releases are emitted immediately before the `Return` of the arm that
//! allocated them — the last point at which they are all live, all in scope,
//! and past every call that read them. The entry block allocates nothing, so
//! there is no cross-block ownership to reason about.
//!
//! ## Return-freshness, and the one shape that still leaks
//!
//! A body is *return-fresh* when neither arm's root denotes a parameter (see
//! `body_returns_a_fresh_allocation`, which carries the induction). It is
//! decidable here because the self-call's callee IS the function being emitted
//! — [`NatRuntime`]'s identity check requires `self_id == id` — so no third
//! party's contract has to be assumed.
//!
//! * **return-fresh** — `countdownSum n = if n = 0 then 0 else n + countdownSum (n-1)`,
//!   and every shape whose arms root at `Add` / `Pred` / `NatConst` / `Rec`:
//!   the self-call's result is an allocation the call made, so the predecessor
//!   passed to it and the result handed back are both released. **Nothing
//!   leaks per frame.**
//! * **NOT return-fresh** — an arm rooting at `Decreasing`, as
//!   `f n = if n = 0 then n else f (n-1)` returns its own parameter: the callee
//!   may hand its argument straight back, so the self-call's result may BE the
//!   predecessor. Releasing either would dangle the other, and which of them is
//!   it is a runtime fact, not a shape. So the predecessor is WITHHELD and the
//!   self-call's result is never recorded: **a frame leaks its own
//!   predecessor — one allocation per frame — deliberately.** (Not two: the
//!   self-call's result is either that same allocation or one a deeper frame
//!   made and this one passes onward.)
//!
//! Neither shape ever releases the parameter `n` or the returned value, in
//! either case: those are the two handles this body does not own.
//!
//! ## The contract an emitted function offers ITS caller
//!
//! Stated because the self-call relies on it and any other caller must too,
//! and because it is the half no type in this crate carries:
//!
//! * **Arguments are BORROWED.** An emitted body never releases a parameter,
//!   so the caller still owns every handle it passed, and must release them
//!   itself.
//! * **The RESULT is the caller's to release** — but it is a FRESH allocation
//!   only when the body is return-fresh. A non-return-fresh body may return an
//!   alias of one of its arguments, so a caller holding both must not release
//!   both. The self-call handles this by withholding; an external caller that
//!   cannot tell the shapes apart should release the result and leak the
//!   argument, or leak both.
//!
//! A caller that wants the old behaviour passes [`NatRuntime::release`] `None`
//! and nothing is released at all. That is what the kernel-agreement harness
//! does when its executable substitute models `Nat` as a VALUE — there is no
//! allocation to release, and the shapes that leak leak identically either way.

use trust_clean_carrier::{CarrierSignature, CleanType};
use trust_clean_origin::{BoolExpr, UIntConditional, UINT_CONDITIONAL_MAX_DECISIONS};
use trust_clean_origin::emit::{
    COMPOSED_MAX_OPS, CleanOriginPlan, CleanOriginShape, RustCallArg, RustCallLiteral,
    RustCallNode, RustCalleeRef, StandaloneBitwiseExpr, StandaloneBitwiseOp,
    StandaloneCleanOriginPlan, StandaloneScalarPlan, StandaloneScalarShape,
};
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, HandleTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, CallingConv, Constant, Function, Module};
// The pinned handle runtime is READ from the validator that enforces it, never
// restated here: `TRUSTED_HANDLE_RUNTIMES` owns the `(name, runtime)` pairing,
// the link-time symbols, their def paths, the calling convention and the
// exact signatures, and `ModuleBuilder::declare_handle_runtime_roles` is the
// writer that turns the roles this producer calls into the bodyless `External`
// declarations `validate_module` admits. A second copy in this crate could satisfy itself
// while disagreeing with the gate.
use trust_ir_build::{HandleRuntimePin, ModuleBuilder, TRUSTED_HANDLE_RUNTIMES};
use trust_types::admissible_body::{
    ArithBinOp, ArithExpr, ArithOperand, BeqOperand, BoolBinOp, RawBinOpKind, RecBodyExpr,
    SelectCmp,
};

/// The pinned runtime-local type name of Clean's `Nat` carrier.
///
/// Half of the `(name, runtime)` pair that IS the handle's identity. Spelled
/// here only so this crate's diagnostics can name it; the authority is
/// [`trust_ir_build::TRUSTED_HANDLE_RUNTIMES`], read by [`pinned_nat_runtime`].
pub const NAT_HANDLE_NAME: &str = "Nat";

/// The pinned runtime path that owns Clean's `Nat` arithmetic.
pub const NAT_HANDLE_RUNTIME: &str = "trust_bignum::Nat";

/// The entry-point ROLES the emitted recursion can call, in the order this
/// producer names them. Role names are the pin's own
/// ([`trust_ir_build::HandleEntryPoint::role`]); the LINK-TIME SYMBOL each one
/// resolves to is the pin's business, never this crate's.
///
/// The first four are called by EVERY emitted recursion. [`NAT_RELEASE_ROLE`]
/// is last and is OPTIONAL to the emitter — see [`NatRuntime::release`] — but
/// it is in this list because the production emitter does call it.
///
/// This list is also EXACTLY what [`declare_pinned_nat_runtime`] declares. The
/// pin row is larger (trust-ir WS3.2 pinned the Clean kernel's native `Nat`
/// surface: `mul`, `div`, `mod`, `beq`, ... — nineteen roles), and every
/// `External` declaration is a symbol the link must resolve, so a module states
/// only the roles its body can call.
pub const NAT_RUNTIME_ROLES: [&str; 5] = ["from_u64", "add", "sub", "is_zero", "drop"];

/// The pin's role name for the RELEASE entry point.
///
/// Spelled once. The pin calls the role `"drop"` and the symbol it resolves to
/// is `trust_bignum_nat_drop` (trust-ir `SPEC_RATIFICATIONS` §7); this crate
/// calls the concept RELEASE in prose, because `drop` in Rust prose means the
/// `Drop` trait. One string, two vocabularies, no second source of truth.
pub const NAT_RELEASE_ROLE: &str = "drop";

/// The validator's own pin row for [`NAT_HANDLE_RUNTIME`].
///
/// Read rather than restated. The §6.4 requirement is "validate-time pinning of
/// `NatRuntime` callee identities against the pinned `("Nat",
/// "trust_bignum::Nat")` pairing", and a producer that kept its own copy of that
/// pairing could satisfy its own copy while disagreeing with the validator — the
/// two-spellings defect this crate refuses everywhere else. So the symbols, the
/// def paths, the calling convention and the exact signatures all come from
/// [`trust_ir_build::TRUSTED_HANDLE_RUNTIMES`], and a row that is not there is a
/// refusal ([`CleanIrRefusal::NatRuntimeIsNotPinnedByTheValidator`]) rather than
/// a fallback.
pub fn pinned_nat_runtime() -> Result<&'static HandleRuntimePin, CleanIrRefusal> {
    TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.name == NAT_HANDLE_NAME && pin.runtime == NAT_HANDLE_RUNTIME)
        .ok_or(CleanIrRefusal::NatRuntimeIsNotPinnedByTheValidator {
            name: NAT_HANDLE_NAME,
            runtime: NAT_HANDLE_RUNTIME,
        })
}

/// The pinned handle type a `Nat` value is carried at in production.
///
/// A NOMINAL opaque handle, not a pointer: `Ty::Handle` is never equal to
/// `Ty::Ptr`, no cast bridges the two, and `Handle(A) != Handle(B)` for two
/// different runtimes. That inequality is the whole point — it is what makes
/// "two opaque runtimes cannot exchange handles" a type error instead of a
/// convention.
#[must_use]
pub fn nat_handle_ty() -> Ty {
    Ty::handle(NAT_HANDLE_NAME, NAT_HANDLE_RUNTIME)
}

/// What a `Nat` VALUE is carried at, and on whose authority.
///
/// ONE field rather than a `Ty` beside a boolean, deliberately. "Is this the
/// pinned production carrier" and "which type is it" are one fact, and two
/// fields carrying one fact is the shape that lets a caller pass `Ty::U64` while
/// claiming handle authority — which is exactly the claim the §6.4 requirement
/// exists to make uninventable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatCarrier {
    /// PRODUCTION. The pinned nominal opaque handle ([`nat_handle_ty`]), whose
    /// only origins are the validator-pinned entry points of
    /// `trust_bignum::Nat` and whose only uses are exact-typed transport.
    ///
    /// This is what must reach a codegen exit. Until trust-ir v43 this slot
    /// held a bare `Ty::Ptr`, and a bare pointer is strictly weaker in two ways
    /// that matter: it is pointer-like (so `GEP`, `Load`, `PtrToInt` and every
    /// cast are well-typed on it, and nothing in the format says a `Nat` must
    /// not be dereferenced), and it is the SAME type every other opaque runtime
    /// would use (so runtime A's handle satisfies runtime B's entry point by
    /// construction).
    PinnedHandle,
    /// An EXECUTABLE SUBSTITUTE the caller supplies so the emitted recursion can
    /// be RUN rather than only inspected.
    ///
    /// `trust_ir::interpret` cannot execute a call to a bodyless declaration and
    /// has no host-call hook, so the kernel-agreement harness gives the four
    /// runtime callees TrustIR BODIES over a model carrier (a one-limb `u64`
    /// `Nat`). That is real evidence and it is deliberately kept: an emitter
    /// that recursed on `n`, swapped the arms or dropped the accumulation
    /// passes every structural check and fails there.
    ///
    /// It carries NO handle authority, and it is a DECLARED substitution rather
    /// than an inferred one: a caller cannot reach this state by passing a type
    /// that happens not to be a handle, and the emitter therefore never has to
    /// guess whether a non-handle carrier was intended.
    ExecutableSubstitute(Ty),
}

impl NatCarrier {
    /// The TrustIR type to carry a `Nat` value at.
    #[must_use]
    pub fn ty(&self) -> Ty {
        match self {
            Self::PinnedHandle => nat_handle_ty(),
            Self::ExecutableSubstitute(ty) => ty.clone(),
        }
    }

    /// True only for the pinned production carrier.
    #[must_use]
    pub fn is_pinned_handle(&self) -> bool {
        matches!(self, Self::PinnedHandle)
    }

    /// Well-formedness of the carrier itself.
    ///
    /// A substitute exists to be COMPUTED ON, and a handle is precisely the type
    /// nothing can compute on — no `Load`, no arithmetic, no constant. So a
    /// substitute that is a handle is refused rather than emitted: if it is the
    /// pinned pair it is a [`Self::PinnedHandle`] wearing the wrong constructor
    /// (and the interpreter would fail on it anyway), and if it is any other
    /// pair it is a FOREIGN runtime's handle being handed to
    /// `trust_bignum::Nat`'s entry points — the exchange the nominal identity
    /// exists to forbid.
    ///
    /// Run at the top of [`emit_clean_origin_function_with_nat`], before a
    /// single instruction is built. Public so a caller can ask the same
    /// question before it commits to a carrier.
    pub fn check(&self) -> Result<(), CleanIrRefusal> {
        let Self::ExecutableSubstitute(ty) = self else {
            return Ok(());
        };
        match ty.handle_ty() {
            None => Ok(()),
            Some(handle)
                if handle.name == NAT_HANDLE_NAME && handle.runtime == NAT_HANDLE_RUNTIME =>
            {
                Err(CleanIrRefusal::NatSubstituteCarrierIsThePinnedHandle)
            }
            Some(handle) => Err(CleanIrRefusal::NatCarrierIsAForeignHandle {
                name: handle.name.clone(),
                runtime: handle.runtime.clone(),
            }),
        }
    }
}

/// A used Rust callee resolved by the caller that owns the final module.
///
/// `plan_index` indexes [`CleanOriginPlan::callees`]. The owning append seam
/// must authenticate the source identity and ensure this exact function exists
/// with this signature and Rust calling convention. This descriptor carries no
/// proof authority; neither a display name nor a matching signature is identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustCalleeTarget {
    /// Index of the registered callee in the sealed plan's roster.
    pub plan_index: usize,
    /// The callee's actual function id in the owning module.
    pub id: FuncId,
    /// The exact function type registered for that module function.
    pub signature: FuncTy,
}

/// The TrustIR identities of the bignum `Nat` runtime the recursion shapes call.
///
/// Clean's `Nat` is UNBOUNDED. TrustIR has no `Nat` type, so a faithful emission
/// cannot pick a machine width — it carries the value as a NOMINAL OPAQUE HANDLE
/// pinned to `trust_bignum::Nat` ([`NatCarrier::PinnedHandle`]) and calls the
/// same runtime the MIR lane calls. That keeps the arithmetic exactly where
/// Clean's semantics live instead of re-implementing it at a width that would
/// wrap.
///
/// The caller supplies the ids because function identity belongs to the owning
/// [`trust_ir::Module`], not to this producer: minting them here would let two
/// independently emitted modules disagree about which `FuncId` is `Nat::add`.
/// A caller that HAS the module gets more than that — see
/// [`declare_pinned_nat_runtime`], which takes the four ids FROM the pinned
/// declarations it writes, and [`NatRuntime::check_pinned_callees`], which
/// re-derives the same fact from a finished module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NatRuntime {
    /// What a `Nat` VALUE is carried at, and on whose authority.
    ///
    /// Still a PARAMETER rather than a constant, because the substitution
    /// ability is what lets the emitted recursion be executed against the
    /// kernel. What changed in v43 is that the substitution is now DECLARED:
    /// see [`NatCarrier`].
    pub carrier: NatCarrier,
    /// `trust_bignum::Nat::from_u64` — materialize a literal.
    pub from_u64: FuncId,
    /// `trust_bignum::Nat::add`.
    pub add: FuncId,
    /// `trust_bignum::Nat::sub` — Lean's TRUNCATED subtraction, which IS the
    /// predecessor at subtrahend 1 on every input, `Nat.pred 0 = 0` included.
    pub sub: FuncId,
    /// A zero test on a `Nat` handle, returning [`Ty::Bool`].
    pub is_zero: FuncId,
    /// `trust_bignum::Nat`'s RELEASE entry point (pin role
    /// [`NAT_RELEASE_ROLE`], symbol `trust_bignum_nat_drop`), or `None` to
    /// emit no releases at all.
    ///
    /// OPTIONAL, and the two states are genuinely different requests rather
    /// than a default plus a fallback:
    ///
    /// * `Some(id)` — the emitted body releases every handle it can PROVE it
    ///   owns, at the end of the arm that allocated it. See the crate docs'
    ///   release section for the exact classification and for the shapes that
    ///   deliberately still leak.
    /// * `None` — nothing is released. Sound, and the pre-2026-09-17 behaviour:
    ///   a leak is a bounded loss of memory, while a release the emitter cannot
    ///   justify is a double free in trusted code. It is what the
    ///   kernel-agreement harness passes when its executable substitute models
    ///   `Nat` as a VALUE, where there is no allocation to release.
    ///
    /// [`PinnedNatRuntime::for_function`] always supplies it, because
    /// [`declare_pinned_nat_runtime`] declares every role in
    /// [`NAT_RUNTIME_ROLES`], the release role included: a production emission
    /// has the callee by construction and cannot forget it.
    pub release: Option<FuncId>,
    /// The function being emitted, for the self-call.
    ///
    /// It must equal the `id` passed to
    /// [`emit_clean_origin_function_with_nat`], and that is CHECKED
    /// ([`CleanIrRefusal::NatRuntimeSelfIdIsNotTheEmittedFunction`]) rather
    /// than assumed. Two ids that are supposed to name one function, supplied
    /// independently at one call, is the shape of a defect that typechecks:
    /// a body whose "self-call" is a call to a DIFFERENT function passes every
    /// structural check, and the recursion it is supposed to be is simply not
    /// there.
    pub self_id: FuncId,
}

impl NatRuntime {
    /// The identity preconditions the emitted body's call edges rest on.
    ///
    /// Checked at the top of [`emit_clean_origin_function_with_nat`], before a
    /// single instruction is built, because every one of these is a fact about
    /// WHICH FUNCTION a call edge names — and a call edge naming the wrong
    /// function is a wrong-binary outcome that no later structural check can
    /// see. `FuncId` is a positional index into the owning module: nothing
    /// about it is nominal, so "these five ids denote five distinct runtime
    /// functions plus this one" has to be stated somewhere or it is not stated
    /// at all.
    ///
    /// Deliberately NOT a check that the ids resolve to the right SYMBOLS —
    /// AT THIS ENTRY POINT. This method sees only ids, and a `FuncId` is a
    /// positional index with no nominal content, so there is nothing here to
    /// compare a symbol against.
    ///
    /// That is no longer the end of the story, and the older note here (which
    /// said naming the right symbol is simply "the caller's") overstated the
    /// limit. A caller that holds the module CAN have the symbols checked, and
    /// §6.4 requires it: [`Self::check_pinned_callees`] resolves each of the
    /// four ids in a given [`trust_ir::Module`] and requires the function it
    /// lands on to carry the pinned shim's link-time symbol, and
    /// [`declare_pinned_nat_runtime`] removes the question at the source by
    /// taking the ids FROM the declarations it writes.
    fn check_identities(&self, emitted: FuncId) -> Result<(), CleanIrRefusal> {
        if self.self_id != emitted {
            return Err(CleanIrRefusal::NatRuntimeSelfIdIsNotTheEmittedFunction {
                self_id: self.self_id.index(),
                emitted: emitted.index(),
            });
        }
        // ONE spelling of the role-to-field mapping, shared with
        // `check_pinned_callees`: two copies of "these four fields are these
        // four roles" is how a field gets checked under another's name.
        let named = self.roles();
        for (index, (name, id)) in named.iter().enumerate() {
            if *id == emitted {
                return Err(CleanIrRefusal::NatRuntimeIdAliasesTheEmittedFunction {
                    runtime: name,
                    id: id.index(),
                });
            }
            for (other_name, other_id) in &named[index + 1..] {
                if id == other_id {
                    return Err(CleanIrRefusal::NatRuntimeIdsAlias {
                        first: name,
                        second: other_name,
                        id: id.index(),
                    });
                }
            }
        }
        Ok(())
    }

    /// The SUPPLIED `(role, id)` pairs, in [`NAT_RUNTIME_ROLES`] order.
    ///
    /// The single place this crate maps a role NAME onto a `NatRuntime` field.
    /// `roles_are_exactly_the_declared_role_names` pins that it agrees with
    /// [`NAT_RUNTIME_ROLES`], which is what the diagnostics and the pin lookup
    /// read.
    ///
    /// A `Vec` rather than an array because [`Self::release`] is optional: an
    /// absent release callee is an ABSENT ROW here, not a placeholder id. Both
    /// consumers — the distinctness check and the pinned-callee check — must
    /// see exactly the ids the caller supplied, and a placeholder would make
    /// one of them compare a `FuncId` nobody named.
    fn roles(&self) -> Vec<(&'static str, FuncId)> {
        let mut roles = vec![
            ("from_u64", self.from_u64),
            ("add", self.add),
            ("sub", self.sub),
            ("is_zero", self.is_zero),
        ];
        if let Some(release) = self.release {
            roles.push((NAT_RELEASE_ROLE, release));
        }
        roles
    }

    /// THE §6.4 PRECONDITION: the carrier reaching a codegen exit must be the
    /// pinned nominal handle, never a substitute and never another runtime's.
    ///
    /// Separate from emission on purpose. Emission still admits a declared
    /// [`NatCarrier::ExecutableSubstitute`], because that is what lets the
    /// emitted recursion be RUN against the kernel — evidence this lane has and
    /// would lose by hardcoding the carrier. What must not happen is a
    /// substitute reaching a real exit, so the requirement is a check a
    /// consumer calls at the exit, and it names the carrier it refused rather
    /// than reporting a generic failure.
    pub fn require_pinned_handle_carrier(&self) -> Result<HandleTy, CleanIrRefusal> {
        match &self.carrier {
            NatCarrier::PinnedHandle => Ok(HandleTy::new(NAT_HANDLE_NAME, NAT_HANDLE_RUNTIME)),
            NatCarrier::ExecutableSubstitute(ty) => match ty.handle_ty() {
                Some(handle) => Err(CleanIrRefusal::NatCarrierIsAForeignHandle {
                    name: handle.name.clone(),
                    runtime: handle.runtime.clone(),
                }),
                None => {
                    Err(CleanIrRefusal::NatCarrierIsNotThePinnedHandle { carrier: ty.to_string() })
                }
            },
        }
    }

    /// VALIDATE-TIME PINNING of the callee identities, against a module.
    ///
    /// [`Self::check_identities`] can only say the five ids are distinct. This
    /// says WHAT THEY NAME: each role's id must resolve, in `module`, to a
    /// function whose `Function::name` is that role's pinned link-time symbol.
    /// Without it the emitted body's `Call` edges are four positional indices,
    /// and a module that resolved `add` to any other function would typecheck,
    /// validate and compute something the declaration does not say.
    ///
    /// This does NOT re-run the validator's own rules on the declarations (that
    /// every pinned symbol is a bodyless `External` C declaration at the exact
    /// pinned signature). Those belong to `validate_module`, which decides them
    /// for the whole module and refuses a handle produced by anything else; a
    /// second copy here would be a second authority that could drift. What this
    /// adds is the half the validator cannot see: which of those declarations
    /// THIS runtime's call edges point at.
    pub fn check_pinned_callees(&self, module: &Module) -> Result<(), CleanIrRefusal> {
        let pin = pinned_nat_runtime()?;
        self.require_pinned_handle_carrier()?;
        for (role, id) in self.roles() {
            let expected = pin
                .entry_points
                .iter()
                .find(|entry| entry.role == role)
                .ok_or(CleanIrRefusal::NatRuntimeRoleIsNotPinned { role })?;
            // `FuncId` is positional, but nothing guarantees a module's
            // `functions` vector is ordered by id (a codec or a join seam may
            // append out of order), so the id is looked UP rather than indexed.
            let actual =
                module.functions.iter().find(|function| function.id == id).ok_or(
                    CleanIrRefusal::NatRuntimeCalleeIsNotInTheModule { role, id: id.index() },
                )?;
            if actual.name != expected.symbol {
                return Err(CleanIrRefusal::NatRuntimeCalleeIsNotThePinnedShim {
                    role,
                    expected: expected.symbol,
                    actual: actual.name.clone(),
                    id: id.index(),
                });
            }
        }
        Ok(())
    }
}

/// Declare the five `trust_bignum::Nat` entry points this producer calls
/// ([`NAT_RUNTIME_ROLES`]) in `builder`, and return the [`NatRuntime`] whose
/// callee ids ARE those declarations.
///
/// The fifth is the RELEASE entry point ([`NAT_RELEASE_ROLE`]). Exactly the
/// roles in [`NAT_RUNTIME_ROLES`] are declared — the ones the emitted body
/// calls — and NOT the whole pin row. The row once was those five; since
/// trust-ir WS3.2 it also pins the Clean kernel's native `Nat` surface
/// (fourteen more roles: `mul`, `div`, `mod`, `beq`, `ble`, ...), and declaring
/// it whole put fourteen `External` declarations no emitted body calls into
/// every module — symbols a link must then resolve, and which
/// `trust-bignum`'s `handle_abi` does not export (it exports these five).
/// trust-ir's own contract for a producer that calls part of a row is
/// `ModuleBuilder::declare_handle_runtime_roles`, so a row edit never changes
/// what this producer declares.
///
/// This is the production path, and it is the one that makes the emitted module
/// acceptable to `validate_module`: the declarations are written by
/// [`trust_ir_build::ModuleBuilder::declare_handle_runtime_roles`] from the
/// validator's own pin row, so they are bodyless `External` C declarations at
/// exactly the pinned signatures and def paths, and the validator then refuses
/// any OTHER origin for a `Nat` handle in the same module — an unpinned bodyless
/// declaration whose signature reaches the handle, a local definition of a
/// pinned symbol, a global or a `SymbolAddr` shadowing one.
///
/// Idempotent, because `declare_handle_runtime_roles` reuses an existing
/// declaration that already matches the pin exactly and refuses one that does
/// not. So a module emitting several `Nat` declarations gets ONE declaration
/// per symbol, which is what a link expects.
///
/// ONE CONSEQUENCE THE CALLER MUST SATISFY: a pinned entry point is a bodyless
/// EXTERNAL declaration, which is an ABI boundary, so `validate_module` then
/// requires the module to carry `Module::target_info` (`TargetInfoRequired`).
/// This function deliberately does not invent one — which target a Clean island
/// is compiled for is the compilation session's fact, and a producer guessing it
/// would be a layout claim nobody made. Build the module with
/// [`trust_ir_build::ModuleBuilder::new_with_target_info`].
///
/// `self_id` is still the caller's, because the function being emitted is the
/// caller's: it is the id the caller will give the emitted `Function`, and
/// [`emit_clean_origin_function_with_nat`] re-checks that they agree.
pub fn declare_pinned_nat_runtime(
    builder: &mut ModuleBuilder,
) -> Result<PinnedNatRuntime, CleanIrRefusal> {
    let pin = pinned_nat_runtime()?;
    // A role the row does not pin is named as THAT role, before the builder is
    // asked: its `UnknownRole` would only surface as a rendered string.
    if let Some(role) = NAT_RUNTIME_ROLES
        .into_iter()
        .find(|role| !pin.entry_points.iter().any(|entry| entry.role == *role))
    {
        return Err(CleanIrRefusal::NatRuntimeRoleIsNotPinned { role });
    }
    let decls = builder.declare_handle_runtime_roles(pin, &NAT_RUNTIME_ROLES).map_err(|error| {
        CleanIrRefusal::NatRuntimeDeclarationRefused { detail: error.to_string() }
    })?;
    let role = |role: &'static str| {
        decls.entry(role).ok_or(CleanIrRefusal::NatRuntimeRoleIsNotPinned { role })
    };
    Ok(PinnedNatRuntime {
        from_u64: role("from_u64")?,
        add: role("add")?,
        sub: role("sub")?,
        is_zero: role("is_zero")?,
        release: role(NAT_RELEASE_ROLE)?,
    })
}

/// The ids [`declare_pinned_nat_runtime`] wrote, before they are bound to the
/// function being emitted.
///
/// Split from [`NatRuntime`] so the ORDER cannot go wrong. `NatRuntime` needs
/// `self_id`, and `self_id` is only knowable AFTER the runtime declarations are
/// written (they take ids of their own, so the emitted function's id is the one
/// after them — [`trust_ir_build::ModuleBuilder::peek_next_func_id`]). A single
/// call taking `self_id` up front would force the caller to predict that count,
/// and a wrong prediction is the
/// [`CleanIrRefusal::NatRuntimeSelfIdIsNotTheEmittedFunction`] class of defect
/// this crate exists to refuse rather than to invite.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PinnedNatRuntime {
    from_u64: FuncId,
    add: FuncId,
    sub: FuncId,
    is_zero: FuncId,
    /// The pinned RELEASE declaration. Not optional here, unlike
    /// [`NatRuntime::release`]: [`declare_pinned_nat_runtime`] writes EVERY role
    /// in [`NAT_RUNTIME_ROLES`], release included, so a production emission
    /// always has the callee and the type says so.
    release: FuncId,
}

impl PinnedNatRuntime {
    /// Bind the declared runtime to the function about to be emitted.
    ///
    /// The carrier is [`NatCarrier::PinnedHandle`] and not a parameter: these
    /// ids are the PINNED declarations, whose signatures are spelled in the
    /// pinned handle, so carrying the value at anything else would make every
    /// call edge ill-typed. A substitute carrier belongs to a runtime the caller
    /// built itself, which is the [`NatRuntime`] literal — still available, and
    /// still what the kernel-agreement harness uses.
    pub fn for_function(&self, self_id: FuncId) -> Result<NatRuntime, CleanIrRefusal> {
        let runtime = NatRuntime {
            carrier: NatCarrier::PinnedHandle,
            from_u64: self.from_u64,
            add: self.add,
            sub: self.sub,
            is_zero: self.is_zero,
            // ALWAYS supplied on this path. The pinned row includes the
            // release entry point, so a production emission that leaked would
            // be leaking with the callee in hand — and `None` is a request to
            // leak, never a default.
            release: Some(self.release),
            self_id,
        };
        // The declarations are distinct by construction, but `self_id` is the
        // caller's, so the same identity checks emission would run are run here
        // — where the caller can still fix the id, rather than after a body has
        // been assembled around it.
        runtime.check_identities(self_id)?;
        Ok(runtime)
    }

    /// The pinned handle type these declarations produce and consume.
    #[must_use]
    pub fn handle_ty(&self) -> Ty {
        nat_handle_ty()
    }
}

/// Why a plan could not be spelled in TrustIR.
///
/// Every variant names the construct and what to do about it. "Unsupported"
/// with no next step is a defect (v7/D3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CleanIrRefusal {
    /// A carrier in the signature has no TrustIR type ON THIS WALK.
    ///
    /// Three distinct cases, and since trust-ir v43 they are NOT the same
    /// story — which is why the message distinguishes them (WS5.14, ruling
    /// v7/D3):
    ///
    /// * `Nat` HAS a TrustIR spelling: the nominal opaque handle
    ///   [`nat_handle_ty`] (`Ty::Handle("Nat", "trust_bignum::Nat")`). It is
    ///   transport only, and it is admitted only when the caller named the
    ///   runtime that owns the arithmetic ([`trust_ir_func_ty_with_nat`] /
    ///   [`emit_clean_origin_function_with_nat`] against a [`NatRuntime`]).
    ///   A walk given no runtime refuses rather than minting a handle with no
    ///   pinned origin — `validate_module` would refuse that module anyway
    ///   (`HandleForeignDeclaration`).
    /// * `Int` has NO row at all: no pinned runtime, signed or otherwise.
    /// * `USize` is target-dependent — bounded by `System.Platform.numBits`,
    ///   which the carrier crate deliberately does not resolve.
    ///
    /// A non-machine `UInt`/`BitVec` width reaches this variant too; for it the
    /// machine-width option is the whole answer.
    CarrierHasNoTrustIrType {
        /// Where in the signature: `Some(i)` is argument `i`, `None` the result.
        position: Option<usize>,
        /// The Clean type that has no TrustIR spelling.
        clean: CleanType,
    },
    /// The shape is emittable to MIR but this producer does not spell it yet.
    /// Named individually so the message says which construct to add, rather
    /// than reporting a generic "unsupported".
    ShapeNotYetSpelled {
        /// The shape's constructor name, e.g. `"WrappingBinOp"`.
        shape: &'static str,
    },
    /// The plan selected a source parameter that its own signature does not
    /// have. This is an internal inconsistency in a sealed plan, not user
    /// error; it is reported rather than panicked so a caller can fail closed.
    ProjectionOutOfRange {
        /// The 0-based source parameter the shape asked for.
        projected: usize,
        /// The arity the signature actually has.
        arity: usize,
    },
    /// A conditional tree disagrees with the sealed planner's decision bound.
    InvalidUnsignedConditional,
    /// A recursion shape reached this producer. Both recursion shapes compute
    /// at the UNBOUNDED bignum `Nat` carrier (`RecBodyExpr`'s nodes are
    /// `trust_bignum::Nat::{from_u64, add, sub}` calls), not at a machine
    /// integer. TrustIR has no `Nat`, so there is no faithful spelling until
    /// the bignum runtime type and its callees are modelled here.
    RecursionAtUnboundedNatCarrier {
        /// The shape's constructor name.
        shape: &'static str,
    },
    /// A recursion shape was reached without [`NatRuntime`] identities. The
    /// shape IS emittable -- see [`emit_clean_origin_function_with_nat`] -- but
    /// only against a runtime the caller names, because the values are unbounded
    /// and no machine width is a faithful substitute.
    RecursionNeedsNatRuntime {
        /// The shape's constructor name.
        shape: &'static str,
    },
    /// A shape that neither TRANSPORTS its carrier nor is one of the two
    /// recursion shapes reached this producer with `CleanType::Nat` in its
    /// signature, while a [`NatRuntime`] carrier was being threaded.
    ///
    /// [`emit_clean_origin_function_with_nat`] resolves the runtime carrier
    /// ONCE and hands it to [`trust_ir_func_ty_with_nat`] for EVERY shape, so a
    /// `Nat` position becomes the runtime carrier whatever the body then does
    /// with it. For the recursion shapes that is the design; for a shape that
    /// COMPUTES on its carrier it is the wrong binary, in both carriers:
    ///
    /// * at [`NatCarrier::PinnedHandle`] the emitted body would be `BinOp` /
    ///   `ICmp` / `Cast` over an OPAQUE RUNTIME POINTER — measured in
    ///   `tests/nat_carrier_shape_scope.rs`;
    /// * at a [`NatCarrier::ExecutableSubstitute`] it would be well-typed
    ///   machine arithmetic that WRAPS an unbounded value — and nothing
    ///   downstream can see that, because the module is valid.
    ///
    /// Refused HERE because the emitter is the layer that knows the shape. The
    /// planner refuses the same pairing today for its own single-domain
    /// reasons, and `validate_module` refuses the handle half; neither is a
    /// statement about what a BODY may do with its carrier, and neither covers
    /// the substitute.
    ShapeMayNotCarryNat {
        /// The shape's constructor name, e.g. `"WrappingBinOp"`.
        shape: &'static str,
        /// Where the `Nat` is: `Some(i)` is argument `i`, `None` the result.
        position: Option<usize>,
    },
    /// The plan's self-call argument is not the predecessor. Every recursion
    /// shape in this fragment recurses on `pred(n)`; anything else is a
    /// termination argument this producer cannot reproduce.
    RecursionArgIsNotPred {
        /// The shape's constructor name.
        shape: &'static str,
    },
    /// A `/` or `%` reached this producer without evidence that its divisor is
    /// nonzero. Total-at-nonzero is a real boundary, not a formality: the one
    /// direction that produces a value must not emit a partial operation.
    PartialOpWithoutDivisorEvidence {
        /// The operator, as written in Clean.
        op: &'static str,
    },
    /// A `ConstantUint` value does not fit the result carrier's width. The
    /// sealed plan re-range-checks this, so reaching it means the plan and the
    /// signature disagree.
    ConstantOutOfRange {
        /// The numeral the plan carries.
        value: u128,
        /// The result carrier's width in bits.
        width: u32,
    },
    /// [`NatRuntime::self_id`] is not the id the emission was asked to give the
    /// function. The self-call would then name a DIFFERENT function under the
    /// spelling of recursion — a body that typechecks, validates, and computes
    /// something the declaration does not say.
    NatRuntimeSelfIdIsNotTheEmittedFunction {
        /// The id the runtime named for the self-call.
        self_id: u32,
        /// The id the emission was asked to give the function.
        emitted: u32,
    },
    /// Two [`NatRuntime`] entries name one id. `from_u64`/`add`/`sub`/`is_zero`
    /// are four distinct runtime functions; aliasing any two means every call
    /// to one of them is a call to the other.
    NatRuntimeIdsAlias {
        /// The first entry, by field name.
        first: &'static str,
        /// The second entry, by field name.
        second: &'static str,
        /// The id they share.
        id: u32,
    },
    /// A [`NatRuntime`] entry names the function being emitted. The Clean
    /// declaration is not one of its own `Nat` primitives, so this is always a
    /// miswiring — and it would emit unbounded recursion through a callee slot.
    NatRuntimeIdAliasesTheEmittedFunction {
        /// The entry, by field name.
        runtime: &'static str,
        /// The shared id.
        id: u32,
    },
    /// The validator's pinned runtime registry has no row for
    /// `("Nat", "trust_bignum::Nat")`. Every identity in this lane is read from
    /// that row, so its absence is refused rather than substituted for.
    NatRuntimeIsNotPinnedByTheValidator {
        /// The runtime-local type name looked for.
        name: &'static str,
        /// The runtime path looked for.
        runtime: &'static str,
    },
    /// The pinned row exists but does not pin a role this producer calls. The
    /// emitted recursion needs all four; a missing one has no spelling.
    NatRuntimeRoleIsNotPinned {
        /// The role, by [`NAT_RUNTIME_ROLES`] name.
        role: &'static str,
    },
    /// [`trust_ir_build::ModuleBuilder::declare_handle_runtime_roles`] declined
    /// to write the pinned declarations into the caller's module.
    NatRuntimeDeclarationRefused {
        /// The builder's own reason, rendered.
        detail: String,
    },
    /// A handle was REQUIRED and the carrier is not one. The design of record
    /// (§6.4) requires the pinned nominal handle before any `Nat` shape reaches
    /// a codegen exit, and an executable substitute — the carrier that lets the
    /// recursion be RUN — is not it.
    NatCarrierIsNotThePinnedHandle {
        /// The carrier that was supplied, rendered.
        carrier: String,
    },
    /// The carrier is a handle owned by a DIFFERENT runtime. Two opaque
    /// runtimes must not exchange handles: the emitted body calls
    /// `trust_bignum::Nat`'s pinned entry points, so a handle belonging to
    /// another runtime would be passed to a runtime that never produced it.
    NatCarrierIsAForeignHandle {
        /// The foreign handle's runtime-local type name.
        name: String,
        /// The foreign handle's runtime path.
        runtime: String,
    },
    /// A carrier was DECLARED an executable substitute but is the pinned handle
    /// itself. A substitute exists to be computed on and a handle is precisely
    /// what nothing can compute on, so this is a constructor mistake rather
    /// than a capability: use [`NatCarrier::PinnedHandle`].
    NatSubstituteCarrierIsThePinnedHandle,
    /// A [`NatRuntime`] callee id does not resolve to any function in the
    /// module it was checked against.
    NatRuntimeCalleeIsNotInTheModule {
        /// The role, by [`NAT_RUNTIME_ROLES`] name.
        role: &'static str,
        /// The id that resolved to nothing.
        id: u32,
    },
    /// A [`NatRuntime`] callee id resolves to a function that is NOT the pinned
    /// shim for its role. The call edge would reach some other function under
    /// the spelling of bignum arithmetic — well-formed, well-typed, and not the
    /// declaration.
    NatRuntimeCalleeIsNotThePinnedShim {
        /// The role, by [`NAT_RUNTIME_ROLES`] name.
        role: &'static str,
        /// The link-time symbol the pin names for that role.
        expected: &'static str,
        /// The symbol the id actually resolves to.
        actual: String,
        /// The id.
        id: u32,
    },
    /// A Rust call chain or its module-owned callee bindings disagree with
    /// the sealed plan. No partially emitted function is returned.
    RustCallEmissionRefused {
        /// The concrete missing identity, carrier, or postorder invariant.
        reason: String,
    },
    /// The call-free entry point ([`emit_clean_origin_function`]) produced a
    /// body carrying a call edge.
    ///
    /// That entry exists to be callable at a PLACEHOLDER id — the in-compiler
    /// recording seam passes `FuncId::new(0)` for both `id` and `ty` and lets
    /// the append seam mint the real ones. That is sound exactly while the
    /// emitted body embeds no function identity, and every shape it reaches
    /// today is straight-line and call-free. A call edge makes the placeholder
    /// OBSERVABLE inside the body, where no seam rewrites it, so it is refused
    /// here rather than published pointing at whichever function happens to
    /// hold the placeholder index.
    CallEdgeWithoutOwningModuleIdentity {
        /// The first callee id found in the emitted body.
        callee: u32,
    },
}

impl core::fmt::Display for CleanIrRefusal {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::CarrierHasNoTrustIrType { position, clean } => {
                let where_ = match position {
                    Some(i) => format!("argument {i}"),
                    None => "the result".to_string(),
                };
                write!(
                    f,
                    "Clean type {clean:?} at {where_} has no TrustIR type ON THIS WALK. TrustIR \
                     carries fixed-width machine integers (`UInt8`/`UInt16`/`UInt32`/`UInt64`, \
                     `BitVec w` at those widths) and `bool`. `Nat` is NOT in that list and is \
                     still carriable: trust-ir v43 carries it as the nominal opaque handle \
                     `Ty::Handle(\"Nat\", \"trust_bignum::Nat\")`, for TRANSPORT only, and only \
                     when the caller names the runtime that owns the arithmetic \
                     (`trust_ir_func_ty_with_nat` / `emit_clean_origin_function_with_nat` \
                     against a `NatRuntime`) — this walk was given none, so it refuses rather \
                     than minting a handle with no pinned origin. `Int` has NO row at all (no \
                     pinned runtime, signed or otherwise), and `USize` is target-dependent \
                     (`System.Platform.numBits`, which the carrier crate deliberately does not \
                     resolve). Options: for `Nat`, name a `NatRuntime` and emit through the \
                     `_with_nat` entry point; give the declaration a machine-width type \
                     (`UInt8`/`UInt16`/`UInt32`/`UInt64`, `BitVec w`, or `Bool`); or keep this \
                     declaration proof-only so no value is produced for it."
                )
            }
            Self::ShapeNotYetSpelled { shape } => write!(
                f,
                "the Clean body shape `{shape}` is recognised and emittable to MIR, but this \
                 TrustIR producer does not spell it yet. Options: add the `{shape}` arm to \
                 `trust-clean-ir` (the plan already carries everything the arm needs), or route \
                 this declaration through the MIR lane, which handles every recognised shape."
            ),
            Self::ProjectionOutOfRange { projected, arity } => write!(
                f,
                "the plan projects source parameter {projected} but its signature has arity \
                 {arity}. A sealed plan should not be able to say this; please report it with \
                 the declaration that produced it."
            ),
            Self::InvalidUnsignedConditional => write!(
                f,
                "the unsigned conditional tree must contain between 2 and {} decisions, \
                 matching its sealed source plan",
                UINT_CONDITIONAL_MAX_DECISIONS,
            ),
            Self::RecursionAtUnboundedNatCarrier { shape } => write!(
                f,
                "`{shape}` computes at the unbounded bignum `Nat` carrier -- its body nodes are \
                 `trust_bignum::Nat::from_u64`/`add`/`sub` calls, not machine arithmetic -- and \
                 TrustIR has no `Nat` type. Emitting it at a fixed width would WRAP where Clean \
                 does not, which is the wrong-binary outcome this lane exists to prevent. \
                 Options: route this declaration through the MIR lane, which lowers these to the \
                 bignum runtime; or model `trust_bignum::Nat` as a TrustIR type and declare its \
                 runtime callees, after which this arm can emit the same zero-test / \
                 predecessor / self-call contract."
            ),
            Self::RecursionNeedsNatRuntime { shape } => write!(
                f,
                "`{shape}` computes at the unbounded bignum `Nat` carrier, so it can only be \
                 emitted against the runtime that owns that arithmetic. Options: call \
                 `emit_clean_origin_function_with_nat` and supply the `NatRuntime` identities \
                 for `trust_bignum::Nat::{{from_u64, add, sub}}` and the zero test; or route \
                 this declaration through the MIR lane, which resolves those callees itself."
            ),
            Self::ShapeMayNotCarryNat { shape, position } => {
                let where_ = match position {
                    Some(i) => format!("argument {i}"),
                    None => "the result".to_string(),
                };
                write!(
                    f,
                    "`{shape}` carries `Nat` at {where_}, and `{shape}` is neither a projection \
                     (which only TRANSPORTS its carrier) nor one of the two recursion shapes \
                     (whose arithmetic is the named runtime's). A `Nat` position is emitted at \
                     the runtime carrier, so this body would either compute on an opaque \
                     runtime handle or WRAP an unbounded value at a machine width -- and the \
                     second is well-typed, so nothing downstream would catch it. Options: give \
                     the declaration a machine-width carrier \
                     (`UInt8`/`UInt16`/`UInt32`/`UInt64`, `BitVec w`) in every position; \
                     express it as one of the recursion shapes, whose bignum arithmetic this \
                     producer does emit; or keep this declaration proof-only so no value is \
                     produced for it."
                )
            }
            Self::RecursionArgIsNotPred { shape } => write!(
                f,
                "`{shape}`'s self-call argument is not `pred(n)`. Every recursion in this \
                 fragment decreases by exactly one, and the emitted body's termination rests on \
                 that. Options: express the declaration as a predecessor recursion; or route it \
                 through the MIR lane, whose gate re-checks the recursive-argument identity \
                 against the kernel."
            ),
            Self::PartialOpWithoutDivisorEvidence { op } => write!(
                f,
                "`{op}` is total only at a nonzero divisor, and this TrustIR producer has no \
                 divisor evidence to rely on -- the total-vs-panicking accounting lives in \
                 `RawBinOpBody` on the MIR side. Emitting it anyway would put a partial \
                 operation in the one lane that produces a value. Options: route this \
                 declaration through the MIR lane, which carries that accounting; or thread the \
                 divisor evidence into the plan so this arm can emit `UDiv`/`URem` on a proven \
                 nonzero divisor."
            ),
            Self::ConstantOutOfRange { value, width } => write!(
                f,
                "the plan's numeral {value} does not fit the result carrier's {width}-bit \
                 width. A sealed plan re-range-checks this, so the plan and its signature \
                 disagree; please report it with the declaration that produced it."
            ),
            Self::NatRuntimeSelfIdIsNotTheEmittedFunction { self_id, emitted } => write!(
                f,
                "the `NatRuntime` names function {self_id} for the self-call while the \
                 emission was asked to give this function id {emitted}. The emitted \
                 \"recursion\" would call a different function, which typechecks and \
                 validates and is not the declaration. Options: pass \
                 `NatRuntime::self_id` equal to the `id` argument (they are one \
                 function); or, if the owning module's id is not known yet, do not emit \
                 this shape -- a self-referential body has no placeholder-id spelling."
            ),
            Self::NatRuntimeIdsAlias { first, second, id } => write!(
                f,
                "the `NatRuntime` names one id ({id}) for both `{first}` and `{second}`. \
                 Those are distinct bignum runtime functions; aliasing them makes every \
                 `{first}` call a `{second}` call, at a carrier this producer cannot \
                 re-check. Options: resolve each runtime callee in the owning module \
                 separately and pass its own id."
            ),
            Self::NatRuntimeIdAliasesTheEmittedFunction { runtime, id } => write!(
                f,
                "the `NatRuntime` names the function being emitted (id {id}) as its \
                 `{runtime}`. A Clean declaration is never one of its own `Nat` \
                 primitives, so this is a miswiring, and the emitted body would recurse \
                 through a callee slot instead of computing. Options: resolve \
                 `{runtime}` in the owning module and pass ITS id."
            ),
            Self::NatRuntimeIsNotPinnedByTheValidator { name, runtime } => write!(
                f,
                "the TrustIR validator's pinned handle-runtime registry has no row for \
                 ({name:?}, {runtime:?}), so there is no trusted origin for a `Nat` handle and \
                 no pinned symbol to call. This producer reads that row instead of keeping its \
                 own copy, so it refuses rather than inventing one. Options: restore the row in \
                 `trust_ir_build::TRUSTED_HANDLE_RUNTIMES`; or emit this declaration against an \
                 executable substitute carrier, which makes no handle claim."
            ),
            Self::NatRuntimeRoleIsNotPinned { role } => write!(
                f,
                "the pinned `trust_bignum::Nat` row does not pin the `{role}` entry point, and \
                 the emitted recursion names {roles:?}. A role with no pinned symbol \
                 has no call edge this producer can vouch for. Options: add the `{role}` entry \
                 point to the pin row, with its exact link-time symbol and signature.",
                roles = NAT_RUNTIME_ROLES,
            ),
            Self::NatRuntimeDeclarationRefused { detail } => write!(
                f,
                "the pinned `trust_bignum::Nat` declarations could not be written into the \
                 module: {detail}. Options: remove or repair the conflicting function so the \
                 pinned symbol names the exact bodyless `External` C declaration the validator \
                 pins, then declare the runtime again."
            ),
            Self::NatCarrierIsNotThePinnedHandle { carrier } => write!(
                f,
                "a `Nat` carrier of `{carrier}` was supplied where the PINNED handle is \
                 required. The two-language design (§6.4) requires the nominal opaque handle \
                 `handle<{NAT_HANDLE_NAME:?}, {NAT_HANDLE_RUNTIME:?}>` before any `Nat` shape \
                 reaches a codegen exit, because a bare machine or pointer carrier can be \
                 dereferenced, cast and exchanged with any other opaque runtime. An executable \
                 substitute is for RUNNING the emitted recursion against the kernel and makes \
                 no handle claim. Options: pass `NatCarrier::PinnedHandle` for anything a \
                 backend will consume; or keep the substitute and do not route the result to a \
                 codegen exit."
            ),
            Self::NatCarrierIsAForeignHandle { name, runtime } => write!(
                f,
                "the `Nat` carrier is the handle ({name:?}, {runtime:?}), which belongs to a \
                 DIFFERENT runtime than the one this body calls \
                 ({NAT_HANDLE_NAME:?}, {NAT_HANDLE_RUNTIME:?}). Two opaque runtimes must not \
                 exchange handles: the emitted calls go to `trust_bignum::Nat`'s pinned entry \
                 points, which never produced this value and cannot be asked to consume it. \
                 Options: carry Clean's `Nat` at its own pinned handle \
                 (`NatCarrier::PinnedHandle`); or emit against the other runtime's own producer."
            ),
            Self::NatSubstituteCarrierIsThePinnedHandle => write!(
                f,
                "an executable substitute carrier was declared, but the type supplied IS the \
                 pinned handle `handle<{NAT_HANDLE_NAME:?}, {NAT_HANDLE_RUNTIME:?}>`. A \
                 substitute exists to be computed on, and a handle is exactly what nothing may \
                 load, cast or construct -- the interpreter cannot run one either. Options: pass \
                 `NatCarrier::PinnedHandle`, which is what this type means; or supply a carrier \
                 the model bodies can actually compute on, such as `Ty::U64`."
            ),
            Self::NatRuntimeCalleeIsNotInTheModule { role, id } => write!(
                f,
                "the `NatRuntime` names function {id} for `{role}`, and the module checked \
                 against has no function with that id. A call edge to an id nothing resolves is \
                 not a call this producer can publish. Options: declare the pinned runtime with \
                 `declare_pinned_nat_runtime`, which takes the ids from the declarations it \
                 writes; or check against the module the ids were resolved in."
            ),
            Self::NatRuntimeCalleeIsNotThePinnedShim { role, expected, actual, id } => write!(
                f,
                "the `NatRuntime` names function {id} for `{role}`, and in the module checked \
                 against that id is `{actual}`, not the pinned shim `{expected}`. The emitted \
                 body would call some other function under the spelling of bignum arithmetic: \
                 well-formed, well-typed, and not the declaration. Options: declare the pinned \
                 runtime with `declare_pinned_nat_runtime` so the ids come from the pinned \
                 declarations; or resolve `{expected}` in the owning module and pass ITS id."
            ),
            Self::RustCallEmissionRefused { reason } => write!(
                f,
                "Rust call chain emission refused: {reason}. Supply exact used callee bindings \
                 from the owning module and preserve the sealed plan's carriers and postorder; \
                 no placeholder identity or call-effect assumption can replace them."
            ),
            Self::CallEdgeWithoutOwningModuleIdentity { callee } => write!(
                f,
                "the call-free entry point produced a body containing a call to function \
                 {callee}. `emit_clean_origin_function` is the entry the in-compiler \
                 recording seam calls at a PLACEHOLDER id, so a callee id in the body \
                 would be published naming whichever function holds that index in the \
                 owning module -- nothing between here and publication rewrites it. \
                 Options: emit this shape through `emit_clean_origin_function_with_nat` \
                 from a caller that knows the owning module's ids; or add a callee-remap \
                 seam to the append path first, and route the shape through it."
            ),
        }
    }
}

/// The recorded reason for a planner-lane refusal, stated at the SHAPE and not
/// only at the signature position the carrier walk happened to reach first.
///
/// This is what the in-compiler planner lane writes into its coverage and
/// disclosure rows (`clean_origin.skipped[].reason`). It lives HERE, beside the
/// refusal it annotates, so the text is unit-testable against real planned
/// Clean declarations instead of only through a stage-1 compile.
///
/// # Why the two recursion shapes need their own sentence (G4, 2026-09-01)
///
/// [`trust_ir_func_ty`] is called before the body emitter, and both recursion
/// shapes are `Nat -> Nat` in EVERY position by their own plan-time signature
/// checks (`trust_clean_origin::emit`'s `check_structural_nat_signature` /
/// `check_wf_nat_signature`: "the structural lane is stated at the bignum
/// carrier only"). So the FIRST refusal they meet is always the carrier one,
/// and the carrier refusal's machine-width option is wrong here: a
/// machine-width signature is not a recursion shape at all.
///
/// Measured on the 2026-08-30 Clean corpus scorecard: 10 of the 15
/// `planner-skipped` rows are these two shapes, every one of them carrying
/// `Clean type Nat at argument 0 has no TrustIR type`. Read literally that
/// attributes two thirds of this lane's residue to the CARRIER rung, which is
/// not where the work is — this crate has spelled both shapes since the
/// [`NatRuntime`] landed, and the same corpus records every one of these ten
/// declarations at tier `general` (`general::<name>`), compiled through
/// clean-compiler's own pipeline and merged with real id remapping.
///
/// # What the note names (WS5.14, re-measured 2026-09-19)
///
/// The note used to name "four callees not present in the crate Module" and an
/// "opaque `Ty::Ptr` carrier". Both had gone stale: the carrier is
/// [`nat_handle_ty`] since trust-ir v43, the emitter calls FIVE pinned entry
/// points ([`NAT_RUNTIME_ROLES`], including the release entry
/// [`NAT_RELEASE_ROLE`]) out of a pin row that has since grown wider, and
/// [`declare_pinned_nat_runtime`] already turns exactly those five into the
/// declarations `validate_module` admits — it simply has no caller in the
/// compiler. (Batch review, 2026-09-23: since trust-ir WS3.2 the row pins
/// nineteen shims, and the minter declares only the five it calls since
/// `3f2696b73b`; so the note says "the five entry points it calls", never "the
/// row's five".) The four live blockers, each re-measured at this tree, are the
/// (1) to (4) of the text below. (Landing review, 2026-09-28: the note used to
/// name a fifth — IR-5's `repoint_edges` guarding a plain call edge on ARITY
/// ALONE. `3b30328c07` made the seam type-check an unsigned declaration's edge
/// too (`ty_link_verdict`: `Bound` / `Differs` / `Undecided`), so that claim
/// had gone stale in exactly the way this note exists to prevent, and the note
/// now says the seam's type check is NOT a blocker.) A reason that misnames
/// the blocker is a v7/D3 defect, so this states it. Nothing else changes:
/// same verdict, same row, same tier.
#[must_use]
pub fn planner_skip_reason(shape: &CleanOriginShape, refusal: &CleanIrRefusal) -> String {
    match shape {
        // Deliberately matched on the SHAPE VARIANT, not on the compiler's
        // rendered `shape_tag` string: a tag rename must not silently drop the
        // note, and the note is about what the plan IS.
        CleanOriginShape::StructuralNatRec { .. } | CleanOriginShape::WellFoundedNatRec { .. } => {
            format!(
                "{refusal}\n\nSHAPE NOTE: this refusal is the signature walk's, and it is \
                 not the blocker. Both recursion shapes are `Nat -> Nat` in every position \
                 BY PLAN CONSTRUCTION, so the carrier refusal always fires first and its \
                 machine-width option does not apply — a machine-width signature would not \
                 be this shape. `trust-clean-ir` CAN spell both, at the trust-ir v43 handle \
                 `Ty::Handle(\"Nat\", \"trust_bignum::Nat\")`, against a `NatRuntime` naming \
                 the five entry points it calls, each PINNED (`from_u64`, `add`, `sub`, \
                 `is_zero` and the RELEASE entry `drop` — `NAT_RUNTIME_ROLES`; the pin row \
                 itself is wider) plus the self-call, and `declare_pinned_nat_runtime` \
                 already writes exactly those five declarations from the validator's own \
                 pin row. What is missing is downstream of this crate \
                 and is NOT a carrier: \
                 (1) `declare_pinned_nat_runtime` has NO caller in the compiler — the \
                 crate-module producer never mints the pinned declarations, and only a \
                 producer that owns the Module can (it must also give that module a \
                 `TargetInfo`, which any bodyless `External` declaration requires); \
                 (2) `clean_origin_join` refuses `Ty::Handle` in BOTH general remap lanes \
                 (`remap_general_ty` for bodies, `remap_ty` for signatures and the interned \
                 type table), because the join re-mints every `FuncId` and carries no pinned \
                 declarations — an admitted handle would arrive with no pinned origin, which \
                 `validate_module` refuses as `HandleForeignDeclaration`; \
                 (3) `clean_origin_join::append_clean_origin` re-mints the appended \
                 function's `FuncId` and rewrites NOTHING inside its body, so a \
                 self-referential body appended there would call whichever function holds \
                 the placeholder index: the append path still has no callee-remap seam, \
                 which is why this crate refuses to publish into it at all \
                 (`CallEdgeWithoutOwningModuleIdentity`); \
                 (4) and this one is not fixed by the three above: the Rust side of the \
                 boundary carries `trust_bignum::Nat` BY VALUE as a `Struct` (its limb \
                 vector), while the pinned carrier is a BOXED HANDLE (`*mut Nat`, the \
                 `trust_bignum` handle ABI), so a Rust caller cannot be linked to a \
                 handle-carried Clean row even once (1)-(3) land. That boundary is an open \
                 decision, not a coding task. \
                 The seam's own edge type check is NOT a blocker: IR-5's `repoint_edges` \
                 checks a re-pointed call edge's result and argument TYPES against the \
                 Clean definition's signature, for an unsigned declaration as for a signed \
                 one (`ty_link_verdict`), and discloses every position it declines to decide \
                 (`type_unchecked`) — so a linked `Nat` row IS type-checked there, and \
                 against the by-value `Struct` of (4) it answers `Differs` and keeps the \
                 edge declared. \
                 The declaration is NOT unrecorded meanwhile: the general lane compiles it \
                 and it is published at tier `general` under clean-compiler's own symbol — \
                 claim-free, ungated, and by design never a link target. Options: mint the \
                 pinned declarations in the crate-module producer, carry them through the \
                 join so `Ty::Handle` can be admitted, add a callee-remap seam to the append \
                 path, and settle the by-value/handle boundary; or leave the row where it is, which costs the \
                 capability nothing and keeps it un-callable."
            )
        }
        _ => refusal.to_string(),
    }
}

/// The TrustIR type a carrier is carried at, or a refusal naming the position.
///
/// [`CleanType`] is `#[non_exhaustive]`, so the wildcard arm is required and a
/// new variant CANNOT be caught here at compile time. It therefore falls to a
/// REFUSAL, never to a guess: a Clean type this crate has never heard of has no
/// TrustIR spelling by definition, and inventing one would be the wrong-binary
/// outcome this whole lane exists to prevent.
fn trust_ir_ty(
    clean: CleanType,
    position: Option<usize>,
    nat_ty: Option<&Ty>,
) -> Result<Ty, CleanIrRefusal> {
    let refuse = || CleanIrRefusal::CarrierHasNoTrustIrType { position, clean };
    match clean {
        CleanType::Bool => Ok(Ty::Bool),
        // `UInt w` and `BitVec w` are both w-bit unsigned carriers. Widths other
        // than the machine set have no TrustIR type; the carrier crate only
        // admits a carrier at a machine width, so a non-machine width reaching
        // here is a refusal rather than a silent widening.
        // Trust: the machine set here is exactly `trust-clean-origin`'s, whose
        // `carrier_class_of` calls `UInt(8 | 16 | 32 | 64)` — and nothing wider —
        // a `MachineUInt`. This crate is a CONSUMER of that crate's plans, so it
        // must not admit a carrier the producer does not classify.
        //
        // 128 was admitted here and is not: it is unwitnessable end to end.
        // `trust_spec_elab::MachineUIntWidth` is `{U8, U16, U32, U64}`, and
        // `trust_certify::clean_island::island_return_domain` maps the carrier
        // names `UInt8`/`UInt16`/`UInt32`/`UInt64` and no other — so there is no
        // `UInt128` for the kernel to reduce an application at, and the
        // kernel-agreement gate could never cover a `Ty::U128` it emitted. The
        // refusal text above never offered 128 either. Emitting a carrier no
        // oracle can check is an unchecked claim, not a capability.
        //
        // This is a fail-closed alignment, not a fragment limit (v7/D2): the way
        // to carry 128 is to extend the CHECK — add `UInt128` to the island and
        // to `MachineUIntWidth`, teach `carrier_class_of` about it, then add the
        // arm back here with a gate row beside it.
        CleanType::UInt(w) | CleanType::BitVec(w) => match w {
            8 => Ok(Ty::U8),
            16 => Ok(Ty::U16),
            32 => Ok(Ty::U32),
            64 => Ok(Ty::U64),
            _ => Err(refuse()),
        },
        // Trust: `Nat` is unbounded, so there is no machine width for it -- but
        // there IS a faithful spelling when a runtime owns the arithmetic: a
        // NOMINAL OPAQUE HANDLE. `Ty::Handle(("Nat", "trust_bignum::Nat"))`
        // carries the value without claiming a width AND without claiming to be
        // a pointer, so nothing may dereference, offset, cast or
        // constant-construct it, and no other runtime's handle is equal to it.
        // Admitted ONLY when the caller named the runtime; otherwise this type
        // would be a value with no origin and nothing that can operate on it.
        //
        // `nat_ty` is the CARRIER THE CALLER RESOLVED
        // (`NatCarrier::ty`), not a type chosen here: production resolves the
        // pinned handle, and the kernel-agreement harness resolves a declared
        // executable substitute so the emitted recursion can be run. Either
        // way the arithmetic stays in the named runtime functions.
        CleanType::Nat if nat_ty.is_some() => Ok(nat_ty.expect("just checked").clone()),
        // Unbounded, target-dependent, and not-a-value: no carrier, so no type.
        CleanType::Nat | CleanType::Int | CleanType::USize | CleanType::Sort => Err(refuse()),
        // `#[non_exhaustive]`: a variant added upstream lands here. Refuse it.
        _ => Err(refuse()),
    }
}

/// The TrustIR function type of a plan's signature.
///
/// Separated from body emission because a caller that only needs to register
/// the type — to reserve a [`FuncTyId`] before emitting — must not have to
/// build a body to get it.
pub fn trust_ir_func_ty(signature: &CarrierSignature) -> Result<FuncTy, CleanIrRefusal> {
    trust_ir_func_ty_with_nat(signature, None)
}

/// As [`trust_ir_func_ty`], but admits the unbounded `Nat` carrier as an opaque
/// handle when a [`NatRuntime`] will own its arithmetic.
pub fn trust_ir_func_ty_with_nat(
    signature: &CarrierSignature,
    nat_ty: Option<&Ty>,
) -> Result<FuncTy, CleanIrRefusal> {
    let mut params = Vec::with_capacity(signature.arity());
    for (index, carrier) in signature.arguments().iter().enumerate() {
        params.push(trust_ir_ty(carrier.clean(), Some(index), nat_ty)?);
    }
    let returns = vec![trust_ir_ty(signature.result().clean(), None, nat_ty)?];
    Ok(FuncTy { params, returns, is_vararg: false, abi: None })
}

/// Emit the TrustIR function for a sealed Clean-origin plan.
///
/// `id` and `ty` are supplied by the caller because identity and type
/// registration belong to the owning [`trust_ir::Module`], not to this
/// producer: minting them here would let two independently emitted functions
/// claim the same id.
///
/// Read the crate-level `GATING` section before treating the result as
/// value-producing. It is faithful to the plan; it has not been reflected back
/// to the kernel.
pub fn emit_clean_origin_function(
    plan: &CleanOriginPlan,
    id: FuncId,
    ty: FuncTyId,
) -> Result<Function, CleanIrRefusal> {
    let function = emit_clean_origin_function_with_nat(plan, id, ty, None)?;
    // Trust (G4, 2026-09-01): THE PLACEHOLDER-ID INVARIANT, CHECKED.
    //
    // This is the entry the in-compiler recording seam
    // (`rustc_mir_transform::clean_origin_ir`) calls, and it calls it with
    // `FuncId::new(0)` / `FuncTyId::new(0)` — placeholders, because identity is
    // minted downstream by `clean_origin_join::append_clean_origin`, which sets
    // `function.id` and `function.ty` and REWRITES NOTHING INSIDE THE BODY.
    //
    // That division of labour is sound exactly while no emitted body names a
    // function. Every shape reachable here today is straight-line and call-free,
    // so the placeholder is never observable. But nothing said so, and nothing
    // checked it: the day a shape on this path emits a call — the give-back of
    // the two recursion shapes, or a future island-to-island `DirectCall` — the
    // published body would carry an edge to whichever function occupies the
    // placeholder index in the crate module. It would validate (the standalone
    // walk builds a one-function mini-module, where id 0 resolves to the
    // function itself), and the whole-module walk that WOULD catch it is a
    // `tracing::enabled!(DEBUG)` tripwire that fails no build.
    //
    // A wrong callee that typechecks, validates and compiles is exactly the
    // failure class this producer exists to prevent, so the invariant is a
    // check, not a comment.
    if let Some(callee) = callee_edges(&function).first() {
        return Err(CleanIrRefusal::CallEdgeWithoutOwningModuleIdentity { callee: callee.index() });
    }
    Ok(function)
}

/// Map the registered Rust callee's supported carriers to its exact IR type.
///
/// This shares the conversion used by Rust call emission with the owning
/// compiler/join seam. It does not resolve identity or grant body authority.
pub fn rust_callee_func_ty(callee: &RustCalleeRef) -> Result<FuncTy, CleanIrRefusal> {
    let carrier = |rust: &trust_types::Ty| match rust {
        trust_types::Ty::Bool => Ok(Ty::Bool),
        trust_types::Ty::Int { width, signed: false } => {
            trust_ir_ty(CleanType::UInt(*width), None, None)
        }
        other => Err(rust_call_refusal(format!(
            "callee `{}` has unsupported Rust carrier {other:?}",
            callee.clean_name
        ))),
    };
    Ok(FuncTy {
        params: callee.params.iter().map(&carrier).collect::<Result<_, _>>()?,
        returns: vec![carrier(&callee.result)?],
        is_vararg: false,
        abi: None,
    })
}

/// Emit an already sealed Rust call chain using final module-owned callee ids.
///
/// Supply exactly one binding for each used plan index, in any order. Unused
/// roster entries need no binding. The caller must authenticate each source
/// identity, the Rust calling convention, and the actual module membership and
/// registered types, including `id`/`ty` for the function being emitted.
///
/// Calls remain observable, conservatively effectful [`Inst::Call`] operations,
/// in the plan's postorder, matching the existing MIR `UnwindAction::Continue`
/// projection. This adds neither a local unwind handler nor a NoPanic claim.
/// No body gate, callee summary, or codegen permission is minted here.
pub fn emit_clean_origin_rust_call_function(
    plan: &CleanOriginPlan,
    id: FuncId,
    ty: FuncTyId,
    callees: &[RustCalleeTarget],
) -> Result<Function, CleanIrRefusal> {
    let CleanOriginShape::RustCallChain { nodes } = plan.shape() else {
        return Err(rust_call_refusal("the sealed plan is not a RustCallChain"));
    };
    emit_rust_call_chain(
        &trust_clean_origin::symbol::declaration_symbol(plan.declaration()),
        plan.signature(),
        nodes,
        plan.callees(),
        id,
        ty,
        callees,
    )
}

fn rust_call_refusal(reason: impl Into<String>) -> CleanIrRefusal {
    CleanIrRefusal::RustCallEmissionRefused { reason: reason.into() }
}

fn emit_rust_call_chain(
    name: &str,
    signature: &CarrierSignature,
    nodes: &[RustCallNode],
    roster: &[RustCalleeRef],
    id: FuncId,
    ty: FuncTyId,
    callees: &[RustCalleeTarget],
) -> Result<Function, CleanIrRefusal> {
    if nodes.is_empty() || nodes.len() > COMPOSED_MAX_OPS {
        return Err(rust_call_refusal(format!("invalid call count {}", nodes.len())));
    }
    let func_ty = trust_ir_func_ty(signature)?;
    // Bound every fresh SSA id before NextValue's u32 counter is used.
    let literals = nodes
        .iter()
        .flat_map(|node| &node.args)
        .filter(|arg| matches!(arg, RustCallArg::Literal(_)))
        .count();
    let total_values =
        signature.arity().checked_add(nodes.len()).and_then(|count| count.checked_add(literals));
    if total_values.is_none_or(|count| u32::try_from(count).is_err()) {
        return Err(rust_call_refusal("the call chain exceeds the SSA value id space"));
    }
    for (position, target) in callees.iter().enumerate() {
        let Some(callee) = roster.get(target.plan_index) else {
            return Err(rust_call_refusal(format!(
                "callee index {} is outside the plan roster",
                target.plan_index
            )));
        };
        if !nodes.iter().any(|node| node.callee == target.plan_index) {
            return Err(rust_call_refusal(format!("unused callee binding {}", target.plan_index)));
        }
        if callee.def_path.is_empty() {
            return Err(rust_call_refusal(format!(
                "callee {} has no registered source identity",
                target.plan_index
            )));
        }
        if target.id == id {
            return Err(rust_call_refusal(format!(
                "callee {} aliases the emitted function",
                target.plan_index
            )));
        }
        if callees[..position]
            .iter()
            .any(|prior| prior.plan_index == target.plan_index || prior.id == target.id)
        {
            return Err(rust_call_refusal(format!(
                "duplicate callee index or module id at binding {position}"
            )));
        }
        if target.signature != rust_callee_func_ty(callee)? {
            return Err(rust_call_refusal(format!(
                "callee {} has a mismatched module signature",
                target.plan_index
            )));
        }
    }

    let entry = BlockId::new(0);
    let mut block = Block::new(entry);
    for (index, param_ty) in func_ty.params.iter().enumerate() {
        block = block.with_param(ValueId::new(index as u32), param_ty.clone());
    }
    let mut next = NextValue::after_params(signature.arity());
    let mut results: Vec<(ValueId, Ty)> = Vec::with_capacity(nodes.len());
    let mut references = vec![0usize; nodes.len()];
    for (index, node) in nodes.iter().enumerate() {
        let Some(target) = callees.iter().find(|target| target.plan_index == node.callee) else {
            return Err(rust_call_refusal(format!(
                "node {index} has no module binding for callee {}",
                node.callee
            )));
        };
        if node.args.len() != target.signature.params.len() {
            return Err(rust_call_refusal(format!("node {index} has the wrong argument count")));
        }
        let mut args = Vec::with_capacity(node.args.len());
        for (position, (arg, expected)) in
            node.args.iter().zip(&target.signature.params).enumerate()
        {
            let (value, actual) = match arg {
                RustCallArg::Param(parameter) => {
                    let Some(actual) = func_ty.params.get(*parameter) else {
                        return Err(rust_call_refusal(format!(
                            "node {index} names missing parameter {parameter}"
                        )));
                    };
                    (ValueId::new(*parameter as u32), actual.clone())
                }
                RustCallArg::Node(prior) => {
                    let Some((value, actual)) = results.get(*prior) else {
                        return Err(rust_call_refusal(format!(
                            "node {index} reads non-earlier node {prior}"
                        )));
                    };
                    references[*prior] += 1;
                    (*value, actual.clone())
                }
                RustCallArg::Literal(literal) => {
                    let constant = match literal {
                        RustCallLiteral::UInt(value) => {
                            let width = match expected {
                                Ty::U8 => 8,
                                Ty::U16 => 16,
                                Ty::U32 => 32,
                                Ty::U64 => 64,
                                _ => {
                                    return Err(rust_call_refusal(format!(
                                        "node {index} argument {position} has a numeral at {expected:?}"
                                    )));
                                }
                            };
                            if !fits_unsigned(*value, width) {
                                return Err(CleanIrRefusal::ConstantOutOfRange {
                                    value: *value,
                                    width,
                                });
                            }
                            canonical_constant(*value)
                        }
                        RustCallLiteral::Bool(value) => {
                            if *expected != Ty::Bool {
                                return Err(rust_call_refusal(format!(
                                    "node {index} argument {position} has a Boolean at {expected:?}"
                                )));
                            }
                            Constant::Bool(*value)
                        }
                    };
                    let value = next.take();
                    block.body.push(InstrNode {
                        inst: Inst::Const { ty: expected.clone(), value: constant },
                        results: vec![value],
                        proofs: Vec::new(),
                        span: None,
                        proof_context: None,
                        scope: None,
                    });
                    (value, expected.clone())
                }
            };
            if actual != *expected {
                return Err(rust_call_refusal(format!(
                    "node {index} argument {position} carries {actual:?}, expected {expected:?}"
                )));
            }
            args.push(value);
        }
        // Emit each node exactly once; reuse its SSA result without re-emitting
        // its call. Inst::Call retains unknown effects, including failure to return.
        let result = next.take();
        block.body.push(call_node(target.id, args, result));
        results.push((result, target.signature.returns[0].clone()));
    }
    let root = nodes.len() - 1;
    for (index, count) in references.into_iter().enumerate() {
        if count != usize::from(index != root) {
            return Err(rust_call_refusal(format!(
                "node {index} is referenced {count} times instead of its sealed-tree count"
            )));
        }
    }
    if results[root].1 != func_ty.returns[0] {
        return Err(rust_call_refusal(
            "the root call result disagrees with the function result carrier",
        ));
    }
    block.body.push(ret_node(results[root].0));
    let mut function = Function::new(id, name, ty, entry);
    function.calling_conv = CallingConv::Rust;
    // Default attrs/summary/proofs preserve unknown Rust effects and confer no authority.
    function.blocks.push(block);
    Ok(function)
}

/// Every function id the emitted body names, in emission order.
///
/// The publication precondition in one call. A [`Function`] with a non-empty
/// answer here CANNOT be appended to a module by a seam that re-mints its
/// [`FuncId`] without also rewriting these edges: `FuncId` is a positional
/// index, so a re-mint moves the function and leaves every edge inside it
/// pointing where it used to be relative to — which is to say, at some other
/// function. A caller that cannot rewrite them must refuse the record.
///
/// Both spellings of a static callee are read, because both are re-pointed by
/// the join seam's own edge rewriter: `Inst::Call` and a
/// [`Constant::FnDef`]-valued `Inst::Const`.
#[must_use]
pub fn callee_edges(function: &Function) -> Vec<FuncId> {
    let mut edges = Vec::new();
    for block in &function.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Call { callee, .. } => edges.push(*callee),
                Inst::Const { value: Constant::FnDef(id), .. } => edges.push(*id),
                _ => {}
            }
        }
    }
    edges
}

/// Emit a sealed standalone plan using the same typed SSA construction as
/// the legacy producer. This does not mint a gate or a legacy MIR plan.
pub fn emit_standalone_clean_origin_function(
    plan: &StandaloneCleanOriginPlan,
    id: FuncId,
    ty: FuncTyId,
) -> Result<Function, CleanIrRefusal> {
    emit_planned_function(
        &trust_clean_origin::symbol::declaration_symbol(plan.declaration()),
        plan.signature(),
        plan.shape(),
        id,
        ty,
        None,
    )
}

/// Trust (WS5.20, F-096): emit a standalone-only SCALAR plan
/// ([`StandaloneScalarPlan`]) as one straight-line block.
///
/// * `ComparisonConnective`: two `ICmp`s over parameters, then `BinOp::And`/
///   `BinOp::Or` at `Ty::Bool` (both comparisons are pure and total, so the
///   non-short-circuit connective computes Lean's `&&`/`||`).
/// * `Bitwise`: the tree by post-order, `BinOp::And`/`BinOp::Or` at the carrier.
/// * `TotalDivision`: Lean's `UIntN.div` is total (`x / 0 = 0`) and TrustIR's
///   `UDiv` by zero is UB, so the divisor is guarded explicitly:
///   `z = 0; one = 1; isz = icmp eq y z; d = select isz one y; q = udiv x d;
///   r = select isz z q`. `UDiv` never sees a zero divisor.
///
/// The standalone gate reads this SSA back independently; nothing here is
/// trusted by it.
pub fn emit_standalone_scalar_function(
    plan: &StandaloneScalarPlan,
    id: FuncId,
    ty: FuncTyId,
) -> Result<Function, CleanIrRefusal> {
    let func_ty = trust_ir_func_ty(plan.signature())?;
    let arity = plan.signature().arity();
    let entry = BlockId::new(0);
    let mut block = Block::new(entry);
    for (index, param_ty) in func_ty.params.iter().enumerate() {
        block = block.with_param(ValueId::new(index as u32), param_ty.clone());
    }
    let result_ty = func_ty.returns[0].clone();
    let mut next = NextValue::after_params(arity);
    let push = |block: &mut Block, inst: Inst, result: ValueId| {
        block.body.push(InstrNode {
            inst,
            results: vec![result],
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
    };
    match plan.shape() {
        StandaloneScalarShape::ComparisonConnective { op, left, right } => {
            let operand_ty = func_ty
                .params
                .first()
                .cloned()
                .ok_or(CleanIrRefusal::ProjectionOutOfRange { projected: 0, arity })?;
            let compare = |comparison: &trust_clean_origin::emit::StandaloneComparison,
                           next: &mut NextValue,
                           block: &mut Block|
             -> Result<ValueId, CleanIrRefusal> {
                let lhs = param_value(comparison.left, arity)?;
                let rhs = param_value(comparison.right, arity)?;
                Ok(emit_icmp(icmp_of(comparison.cmp), &operand_ty, lhs, rhs, next, block))
            };
            let lhs = compare(left, &mut next, &mut block)?;
            let rhs = compare(right, &mut next, &mut block)?;
            let ir_op = match op {
                BoolBinOp::And => BinOp::And,
                BoolBinOp::Or => BinOp::Or,
            };
            let out = next.take();
            push(&mut block, Inst::BinOp { op: ir_op, ty: result_ty, lhs, rhs }, out);
            block.body.push(ret_node(out));
        }
        StandaloneScalarShape::Bitwise { expr } => {
            let root = emit_bitwise_expr(expr, &result_ty, &mut next, &mut block, arity)?;
            block.body.push(ret_node(root));
        }
        StandaloneScalarShape::TotalDivision { dividend, divisor } => {
            let x = param_value(*dividend, arity)?;
            let y = param_value(*divisor, arity)?;
            let zero = next.take();
            push(&mut block, Inst::Const { ty: result_ty.clone(), value: Constant::Int(0) }, zero);
            let one = next.take();
            push(&mut block, Inst::Const { ty: result_ty.clone(), value: Constant::Int(1) }, one);
            let is_zero = emit_icmp(ICmpOp::Eq, &result_ty, y, zero, &mut next, &mut block);
            let safe_divisor = next.take();
            push(
                &mut block,
                Inst::Select { ty: result_ty.clone(), cond: is_zero, then_val: one, else_val: y },
                safe_divisor,
            );
            let quotient = next.take();
            push(
                &mut block,
                Inst::BinOp { op: BinOp::UDiv, ty: result_ty.clone(), lhs: x, rhs: safe_divisor },
                quotient,
            );
            let out = next.take();
            push(
                &mut block,
                Inst::Select { ty: result_ty, cond: is_zero, then_val: zero, else_val: quotient },
                out,
            );
            block.body.push(ret_node(out));
        }
    }
    let name = trust_clean_origin::symbol::declaration_symbol(plan.declaration());
    let mut function = Function::new(id, name, ty, entry);
    // The same convention every other Clean-origin body carries (see
    // `emit_planned_function`); the standalone gate pins it as neutral metadata.
    function.calling_conv = CallingConv::Rust;
    function.blocks.push(block);
    Ok(function)
}

/// Post-order emission of a standalone `&&&`/`|||` tree.
fn emit_bitwise_expr(
    expr: &StandaloneBitwiseExpr,
    ty: &Ty,
    next: &mut NextValue,
    block: &mut Block,
    arity: usize,
) -> Result<ValueId, CleanIrRefusal> {
    match expr {
        StandaloneBitwiseExpr::Operand(operand) => operand_value(*operand, ty, next, block, arity),
        StandaloneBitwiseExpr::Bin { op, left, right } => {
            let lhs = emit_bitwise_expr(left, ty, next, block, arity)?;
            let rhs = emit_bitwise_expr(right, ty, next, block, arity)?;
            let out = next.take();
            let op = match op {
                StandaloneBitwiseOp::And => BinOp::And,
                StandaloneBitwiseOp::Or => BinOp::Or,
            };
            block.body.push(InstrNode {
                inst: Inst::BinOp { op, ty: ty.clone(), lhs, rhs },
                results: vec![out],
                proofs: Vec::new(),
                span: None,
                proof_context: None,
                scope: None,
            });
            Ok(out)
        }
    }
}

/// As [`emit_clean_origin_function`], but able to spell the two recursion
/// shapes because the caller names the bignum runtime.
///
/// Split rather than made a required parameter so the eleven shapes that need no
/// runtime keep a call that cannot pass the wrong one.
pub fn emit_clean_origin_function_with_nat(
    plan: &CleanOriginPlan,
    id: FuncId,
    ty: FuncTyId,
    nat: Option<NatRuntime>,
) -> Result<Function, CleanIrRefusal> {
    emit_planned_function(
        &trust_clean_origin::symbol::declaration_symbol(plan.declaration()),
        plan.signature(),
        plan.shape(),
        id,
        ty,
        nat,
    )
}

fn emit_planned_function(
    name: &str,
    signature: &CarrierSignature,
    shape: &CleanOriginShape,
    id: FuncId,
    ty: FuncTyId,
    nat: Option<NatRuntime>,
) -> Result<Function, CleanIrRefusal> {
    // Identity FIRST, before any instruction is built: every check in here is
    // about which function a call edge names, and a body assembled around a
    // miswired id is a body that has to be thrown away anyway.
    if let Some(nat) = nat.as_ref() {
        nat.check_identities(id)?;
        // The carrier is checked HERE, not silently accepted: a substitute that
        // is a handle (this runtime's or another's) is a claim the emitter
        // cannot honour, and saying so is the difference between a refusal and
        // a body that carries a handle nothing pinned.
        nat.carrier.check()?;
    }
    let nat_ty = nat.as_ref().map(|n| n.carrier.ty());
    // WHICH SHAPES MAY HAVE THE RUNTIME CARRIER, decided HERE because this is
    // the layer that knows the shape.
    //
    // `nat_ty` is threaded into `trust_ir_func_ty_with_nat` for EVERY shape, so
    // a `CleanType::Nat` position becomes the runtime carrier whatever the body
    // then does with it. That is the design for the two recursion shapes, whose
    // arithmetic IS the named runtime's calls, and it is right for the
    // projections, which only transport their carrier (`Return <parameter>` --
    // exactly the exact-typed transport trust-ir v43 ratified a handle FOR).
    //
    // For every other shape it would be a wrong binary, and measurably so.
    // Relaxing only the planner's two `Nat`-at-a-computing-shape refusals
    // (`recognise_wrapping_expr`'s result-carrier gate and
    // `check_arith_signature`) makes `def natAdd (a b : Nat) : Nat := a + b`
    // plan as `WrappingBinOp`, and this emitter then emits, without a word:
    //
    //     BinOp { op: Add, ty: Handle(("Nat", "trust_bignum::Nat")),
    //             lhs: v0, rhs: v1 }
    //
    // -- arithmetic on an opaque runtime pointer. `validate_module` does refuse
    // that one (`BinOpRequiresInteger` + `InvalidHandleUse`, both pinned in
    // `tests/nat_carrier_shape_scope.rs`), but the SUBSTITUTE carrier the
    // kernel-agreement harness passes emits `BinOp { ty: U64 }` instead: a
    // well-typed 64-bit WRAP of an unbounded `Nat`, which validates clean and
    // which no downstream layer can see. That is the path where validation does
    // not run, and it is why this refusal is not redundant with either the
    // planner's rules or the validator's.
    //
    // Conservative on purpose: it refuses a `Nat` in ANY position of a
    // non-transport shape, not only the position the body computes at. No
    // capability is lost -- the reflected side B of every arithmetic and select
    // shape is single-domain over ALL parameters, used or not, which is exactly
    // why `check_arith_signature` refuses those signatures too -- and a refusal
    // is never a wrong binary.
    if nat_ty.is_some()
        && let Some(position) = first_nat_position(signature)
        && let Some(refused) = shape_that_may_not_carry_nat(shape)
    {
        return Err(CleanIrRefusal::ShapeMayNotCarryNat { shape: refused, position });
    }
    let func_ty = trust_ir_func_ty_with_nat(signature, nat_ty.as_ref())?;

    // One entry block whose parameters ARE the source parameters, in source
    // order. Clean's de Bruijn inversion (source parameter `i` is `BVar(n-1-i)`
    // under `n` binders) is already resolved by the planner -- `projected` is a
    // 0-based SOURCE position -- so this crate must not invert anything. That
    // inversion is the one mistranslation this lane can make, and doing it in
    // two places is how the two spellings would disagree.
    let entry = BlockId::new(0);
    let mut block = Block::new(entry);
    // Extra blocks, for the shapes that need real control flow. Empty for every
    // straight-line shape, so those functions stay exactly one block.
    let mut blocks: Vec<Block> = Vec::new();
    for (index, param_ty) in func_ty.params.iter().enumerate() {
        block = block.with_param(ValueId::new(index as u32), param_ty.clone());
    }

    let arity = signature.arity();
    let result_ty = func_ty.returns[0].clone();

    match shape {
        // Both projection shapes return a source parameter verbatim. They are
        // deliberately the SAME body: the distinct plan variants exist so an
        // inductive verdict is not mistaken for syntactic recognition, which is
        // a fact about how the plan was justified, not about what it computes.
        CleanOriginShape::Projection { projected }
        | CleanOriginShape::InductiveProjection { projected } => {
            if *projected >= arity {
                return Err(CleanIrRefusal::ProjectionOutOfRange { projected: *projected, arity });
            }
            block.body.push(ret_node(ValueId::new(*projected as u32)));
        }

        CleanOriginShape::ConstantUint { value } => {
            let width = match signature.result().clean() {
                CleanType::Bool => 1,
                CleanType::UInt(w) | CleanType::BitVec(w) => w,
                // Unreachable: `trust_ir_func_ty` above already refused every
                // other result carrier. Reported rather than panicked so a
                // future carrier type cannot turn this into an ICE.
                other => {
                    return Err(CleanIrRefusal::CarrierHasNoTrustIrType {
                        position: None,
                        clean: other,
                    });
                }
            };
            if !fits_unsigned(*value, width) {
                return Err(CleanIrRefusal::ConstantOutOfRange { value: *value, width });
            }
            // `Constant` is canonical: `Int` carries everything representable in
            // `i128`, and `U128` ONLY the upper half of the u128 range. Picking
            // by value is what keeps one spelling per construct.
            let constant = canonical_constant(*value);
            let konst = ValueId::new(arity as u32);
            block.body.push(InstrNode {
                inst: Inst::Const { ty: result_ty, value: constant },
                results: vec![konst],
                proofs: Vec::new(),
                span: None,
                proof_context: None,
                scope: None,
            });
            block.body.push(ret_node(konst));
        }

        // A single wrapping op over two operands. TrustIR's `BinOp::Add/Sub/Mul`
        // ARE the wrapping ones -- its reference interpreter defines them as
        // `raw.wrapping_{op}` (`trust_ir::interpret`) -- which is exactly Clean
        // `UIntN` semantics, so this is a faithful mapping and not a widening.
        // Width is NOT a field on the shape: it comes from the signature, so
        // there is no second place a width can disagree.
        CleanOriginShape::WrappingBinOp { op, left, right } => {
            let mut next = NextValue::after_params(arity);
            let lhs = operand_value(*left, &result_ty, &mut next, &mut block, arity)?;
            let rhs = operand_value(*right, &result_ty, &mut next, &mut block, arity)?;
            let out = next.take();
            block.body.push(InstrNode {
                inst: Inst::BinOp { op: trust_ir_binop(*op), ty: result_ty, lhs, rhs },
                results: vec![out],
                proofs: Vec::new(),
                span: None,
                proof_context: None,
                scope: None,
            });
            block.body.push(ret_node(out));
        }

        // A nested composition of the same wrapping ops. Emitted by POST-ORDER
        // traversal through fresh values, which is the same order the MIR lane
        // emits its call chain in -- deliberately, so the two lanes agree about
        // evaluation order rather than agreeing by luck.
        CleanOriginShape::Composed { expr } => {
            let mut next = NextValue::after_params(arity);
            let root = emit_arith_expr(expr, &result_ty, &mut next, &mut block, arity)?;
            block.body.push(ret_node(root));
        }
        // The SELECT FAMILY. All five are `if <cmp> then <arm> else <arm>`, and
        // they differ only in how the comparison operands and the arms are
        // spelled. TrustIR has a branchless `Inst::Select`, so all five emit
        // ICmp-then-Select in ONE block.
        //
        // The MIR lane emits a four-block O0 diamond for these. That is not a
        // disagreement: a branchless select and a diamond compute the same
        // value, and the two IRs simply have different idioms. It does mean a
        // future TrustIR-side gate must compare SEMANTICS, not block structure
        // -- a shape-equality gate would reject this lane for being better.
        CleanOriginShape::Select { cmp, cmp_left, cmp_right, then_param, else_param } => {
            let mut next = NextValue::after_params(arity);
            let lhs = param_value(*cmp_left, arity)?;
            let rhs = param_value(*cmp_right, arity)?;
            let cond = emit_icmp(icmp_of(*cmp), &result_ty, lhs, rhs, &mut next, &mut block);
            let then_val = param_value(*then_param, arity)?;
            let else_val = param_value(*else_param, arity)?;
            emit_select_and_return(&result_ty, cond, then_val, else_val, &mut next, &mut block);
        }

        CleanOriginShape::SelectLiteral { cmp, cmp_param, literal, then_param, else_param } => {
            let mut next = NextValue::after_params(arity);
            let lhs = param_value(*cmp_param, arity)?;
            // The literal is STRICTLY the comparison's right operand; a literal
            // on the left is outside the fragment and never reaches a plan.
            let rhs = operand_value(
                ArithOperand::Const(*literal),
                &result_ty,
                &mut next,
                &mut block,
                arity,
            )?;
            let cond = emit_icmp(icmp_of(*cmp), &result_ty, lhs, rhs, &mut next, &mut block);
            let then_val = param_value(*then_param, arity)?;
            let else_val = param_value(*else_param, arity)?;
            emit_select_and_return(&result_ty, cond, then_val, else_val, &mut next, &mut block);
        }

        CleanOriginShape::SelectOperands { cmp, cmp_left, cmp_right, then_arm, else_arm } => {
            let mut next = NextValue::after_params(arity);
            let lhs = param_value(*cmp_left, arity)?;
            let rhs = operand_value(*cmp_right, &result_ty, &mut next, &mut block, arity)?;
            let cond = emit_icmp(icmp_of(*cmp), &result_ty, lhs, rhs, &mut next, &mut block);
            let then_val = operand_value(*then_arm, &result_ty, &mut next, &mut block, arity)?;
            let else_val = operand_value(*else_arm, &result_ty, &mut next, &mut block, arity)?;
            emit_select_and_return(&result_ty, cond, then_val, else_val, &mut next, &mut block);
        }

        CleanOriginShape::UnsignedConditional { expr } => {
            let mut next = NextValue::after_params(arity);
            let value = emit_unsigned_conditional(expr, &result_ty, &mut next, &mut block, arity)?;
            block.body.push(ret_node(value));
        }

        // `beq` is decidable equality: the comparison is always `==`.
        CleanOriginShape::SelectBeq { cmp_left, cmp_right, then_arm, else_arm } => {
            let mut next = NextValue::after_params(arity);
            let lhs = param_value(*cmp_left, arity)?;
            let rhs = operand_value(*cmp_right, &result_ty, &mut next, &mut block, arity)?;
            let cond = emit_icmp(ICmpOp::Eq, &result_ty, lhs, rhs, &mut next, &mut block);
            let then_val = operand_value(*then_arm, &result_ty, &mut next, &mut block, arity)?;
            let else_val = operand_value(*else_arm, &result_ty, &mut next, &mut block, arity)?;
            emit_select_and_return(&result_ty, cond, then_val, else_val, &mut next, &mut block);
        }

        // The general `beq`, whose operands may be computed and whose
        // SCRUTINEE selects which way the decision reads. `scrutinee == false`
        // is `if (a == b) == false`, i.e. `!=` -- emitted as `ICmpOp::Ne`
        // rather than by swapping the arms, because swapping arms and negating
        // a predicate are the same value only when the arms are pure, and
        // relying on that would be an argument this producer should not make.
        CleanOriginShape::SelectBeqGeneral {
            scrutinee,
            cmp_left,
            cmp_right,
            then_arm,
            else_arm,
        } => {
            let mut next = NextValue::after_params(arity);
            let lhs = beq_operand_value(cmp_left, &result_ty, &mut next, &mut block, arity)?;
            let rhs = beq_operand_value(cmp_right, &result_ty, &mut next, &mut block, arity)?;
            let op = if *scrutinee { ICmpOp::Eq } else { ICmpOp::Ne };
            let cond = emit_icmp(op, &result_ty, lhs, rhs, &mut next, &mut block);
            let then_val = operand_value(*then_arm, &result_ty, &mut next, &mut block, arity)?;
            let else_val = operand_value(*else_arm, &result_ty, &mut next, &mut block, arity)?;
            emit_select_and_return(&result_ty, cond, then_val, else_val, &mut next, &mut block);
        }

        // W6 (Rust-calls-Clean): a comparison of two parameters returned as
        // `Bool`. The comparison PRODUCES the `i1` result directly — no select,
        // no diamond — so the trust-IR body is one `ICmp` and a return. The
        // ICmp's OPERAND type is the ARGUMENT carrier (`UInt`), NOT the result
        // carrier (`Bool`/`i1`): the select arms above pass `&result_ty`
        // because their operands ARE the result carrier, which is not the case
        // here.
        CleanOriginShape::DecideComparison { cmp, cmp_left, cmp_right } => {
            let mut next = NextValue::after_params(arity);
            let lhs = param_value(*cmp_left, arity)?;
            let rhs = param_value(*cmp_right, arity)?;
            let operand_ty = func_ty
                .params
                .get(*cmp_left)
                .cloned()
                .ok_or(CleanIrRefusal::ProjectionOutOfRange { projected: *cmp_left, arity })?;
            let cond = emit_icmp(icmp_of(*cmp), &operand_ty, lhs, rhs, &mut next, &mut block);
            block.body.push(ret_node(cond));
        }

        // W6 (Rust-calls-Clean): a strict boolean CONNECTIVE over two `Bool`
        // parameters. `and`/`or` on `Bool` are total, so they emit directly at
        // the `i1` result carrier — no branch, no partiality, unlike the `/`/`%`
        // raw binops below.
        //
        // WS5.13: the spelling is the BOOLEAN connective `BinOp::BAnd` /
        // `BinOp::BOr`, never the overloaded integer `And`/`Or`. TrustIR's
        // one-spelling doctrine (the `B*` ops exist since trust-ir 4b069189)
        // makes `band`/`bor` THE Bool connectives; `and`/`or` still admit a
        // scalar `Bool` only as the second spelling that doctrine exists to
        // remove, so this producer must not depend on it.
        CleanOriginShape::BoolConnective { op, left, right } => {
            let ir_op = match op {
                BoolBinOp::And => BinOp::BAnd,
                BoolBinOp::Or => BinOp::BOr,
            };
            let mut next = NextValue::after_params(arity);
            let lhs = param_value(*left, arity)?;
            let rhs = param_value(*right, arity)?;
            let out = next.take();
            block.body.push(InstrNode {
                inst: Inst::BinOp { op: ir_op, ty: result_ty, lhs, rhs },
                results: vec![out],
                proofs: Vec::new(),
                span: None,
                proof_context: None,
                scope: None,
            });
            block.body.push(ret_node(out));
        }

        // W6 (Rust-calls-Clean): boolean NEGATION. `Bool.not` on `Bool` is
        // total and emits directly at the `i1` result carrier.
        //
        // WS5.13 (F-033): spelled `bxor %b, true` — the ONE spelling of scalar
        // Bool negation. `UnOp::Not` is NOT admitted at scalar `Bool` by the
        // trust-ir validator (its `Not` rule is integer / integer-vector /
        // bool-vector only), so the old `UnOp::Not` spelling was refused at
        // the join seam's per-function validation and the row was SKIPPED,
        // leaving `neg` a body-less declaration. `b XOR true` is `NOT b` on the
        // 0/1 carrier; the constant is `true`, and a `false` there is the
        // identity — the mutation control in `tests/bool_value_spelling.rs`.
        CleanOriginShape::BoolNot { param } => {
            let mut next = NextValue::after_params(arity);
            let operand = param_value(*param, arity)?;
            let truth = next.take();
            block.body.push(InstrNode {
                inst: Inst::Const { ty: result_ty.clone(), value: Constant::Bool(true) },
                results: vec![truth],
                proofs: Vec::new(),
                span: None,
                proof_context: None,
                scope: None,
            });
            let out = next.take();
            block.body.push(InstrNode {
                inst: Inst::BinOp { op: BinOp::BXor, ty: result_ty, lhs: operand, rhs: truth },
                results: vec![out],
                proofs: Vec::new(),
                span: None,
                proof_context: None,
                scope: None,
            });
            block.body.push(ret_node(out));
        }

        // A sealed Boolean expression is pure and total. Emit its actual tree
        // directly into TrustIR; this spelling supplies no body-gate permission.
        CleanOriginShape::BoolExpression { expr } => {
            let mut next = NextValue::after_params(arity);
            let out = emit_bool_expr(expr, &mut next, &mut block, arity)?;
            block.body.push(ret_node(out));
        }

        // Raw bitwise/division ops. `&` and `|` are TOTAL and emit directly.
        // `/` and `%` are total only at a NONZERO divisor, and this producer
        // has no divisor evidence -- the plan's total-vs-panicking accounting
        // lives in `RawBinOpBody`, on the MIR side. Emitting `UDiv` at an open
        // divisor would put a partial operation into the one lane that
        // produces a value, so they REFUSE here rather than being emitted
        // hopefully. This is a capability gap, not a soundness claim: the
        // refusal names the boundary so the arm can be added once the divisor
        // evidence is threaded through.
        CleanOriginShape::RawBinOp { op, left, right } => {
            let ir_op = match op {
                RawBinOpKind::BitAnd => BinOp::And,
                RawBinOpKind::BitOr => BinOp::Or,
                // `^` and `>>` joined the MIR lane on 2026-09-23 (clean pin
                // `bf31976f48`). They are NOT spelled here yet, deliberately:
                // this producer's independent reflectors refuse TrustIR `Xor`
                // today, and TrustIR `LShr`'s amount semantics have not been
                // measured against Lean's modulo-the-width reduction. Refusing
                // keeps this lane's reach exactly where it was measured.
                RawBinOpKind::BitXor => return Err(shape_todo("RawBinOp(BitXor)")),
                RawBinOpKind::Shr => return Err(shape_todo("RawBinOp(Shr)")),
                RawBinOpKind::Div | RawBinOpKind::Rem => {
                    return Err(CleanIrRefusal::PartialOpWithoutDivisorEvidence {
                        op: if matches!(op, RawBinOpKind::Div) { "/" } else { "%" },
                    });
                }
            };
            let mut next = NextValue::after_params(arity);
            let lhs = operand_value(*left, &result_ty, &mut next, &mut block, arity)?;
            let rhs = operand_value(*right, &result_ty, &mut next, &mut block, arity)?;
            let out = next.take();
            block.body.push(InstrNode {
                inst: Inst::BinOp { op: ir_op, ty: result_ty, lhs, rhs },
                results: vec![out],
                proofs: Vec::new(),
                span: None,
                proof_context: None,
                scope: None,
            });
            block.body.push(ret_node(out));
        }
        // The two RECURSION shapes. These are not "not written yet": they
        // compute at a carrier TrustIR does not have. `RecBodyExpr`'s nodes are
        // bignum `Nat` operations, and `trust_ir_ty` already refuses
        // `CleanType::Nat` for the same reason -- an unbounded value has no
        // fixed-width spelling, and choosing one would wrap where Clean does
        // not. Refusing here is the same decision, applied to the body instead
        // of the signature.
        // The two RECURSION shapes. Both are the same emitted contract -- the
        // zero test, the predecessor, the self-call -- which is deliberate and
        // is also what the MIR lane emits for them. The plan variants differ in
        // how the two arms were JUSTIFIED (structural `Nat.rec` iota vs a
        // `WellFounded.fix` functional), not in what they compute, and this
        // producer must not invent a distinction the kernel does not make.
        //
        // `nat` is required because these compute at the unbounded bignum
        // carrier: without the runtime identities there is no faithful
        // emission, and the refusal below says so rather than falling back to a
        // machine width that would wrap.
        CleanOriginShape::StructuralNatRec { base, step, rec_arg } => {
            let Some(nat) = nat.as_ref() else {
                return Err(CleanIrRefusal::RecursionNeedsNatRuntime { shape: "StructuralNatRec" });
            };
            check_rec_arg(rec_arg, "StructuralNatRec")?;
            emit_nat_recursion(&mut block, &mut blocks, arity, nat, base, step)?;
        }
        // This entry has no module-owned Rust callee bindings. The separate
        // emit_clean_origin_rust_call_function entry can emit the sealed chain
        // only after the owning append seam resolves its actual function ids.
        // Preserve the placeholder entry's refusal and its disclosed skip.
        CleanOriginShape::RustCallChain { .. } => {
            return Err(CleanIrRefusal::ShapeNotYetSpelled { shape: "RustCallChain" });
        }
        CleanOriginShape::WellFoundedNatRec {
            zero_value,
            nonzero_value,
            rec_args,
            measure_index,
            ..
        } => {
            let Some(nat) = nat.as_ref() else {
                return Err(CleanIrRefusal::RecursionNeedsNatRuntime {
                    shape: "WellFoundedNatRec",
                });
            };
            // Trust: the plan now carries the self-call arguments BY SOURCE
            // POSITION (`rec_args`) with `measure_index` naming the one the
            // recursion descends on, rather than a single `rec_arg`. Only the
            // measure position is `Pred`; the others are ordinary values (R3a).
            //
            // Check the MEASURE argument, which is the fact this producer relies
            // on for termination. The other positions need no check here because
            // `emit_nat_recursion` refuses any arity but 1 -- a multi-argument
            // recursion has no spelling in this producer yet and fails closed
            // rather than emitting a call that drops arguments.
            let measure = rec_args
                .get(*measure_index)
                .ok_or(CleanIrRefusal::RecursionArgIsNotPred { shape: "WellFoundedNatRec" })?;
            check_rec_arg(measure, "WellFoundedNatRec")?;
            emit_nat_recursion(&mut block, &mut blocks, arity, nat, zero_value, nonzero_value)?;
        }
    }

    // `Function::new` rather than a struct literal: `Function` carries a dozen
    // fields whose defaults are the IR's business (linkage, calling convention,
    // attrs, provenance carriers), and a literal here would silently pin them
    // the day one is added.
    let mut function = Function::new(id, name, ty, entry);
    // Clean-origin declarations are compiler-minted Rust items. The compiler
    // installs every callable signature with `mk_fn_sig_rust_abi` (the
    // resolver feed for fixed-width carriers and the deferred provider for
    // Nat), so the direct TrustIR definition must carry that same convention.
    // Leaving the `Function::new` C default here is not conservative: it
    // asserts a foreign ABI and turns every Rust -> Clean call into a
    // cross-convention edge. A fixed-width scalar happens to hide that lie; a
    // `Nat` carrier exposes it
    // because its repr(Rust) struct is then (correctly) refused at an apparent
    // FFI boundary.
    function.calling_conv = CallingConv::Rust;
    function.blocks = core::mem::take(&mut blocks);
    function.blocks.insert(0, block);
    Ok(function)
}

/// The first signature position carried at `CleanType::Nat`.
///
/// The outer `Option` is "there is one at all"; the inner is the position in
/// the spelling every refusal in this crate uses -- `Some(i)` is argument `i`,
/// `None` is the result.
fn first_nat_position(signature: &CarrierSignature) -> Option<Option<usize>> {
    if let Some(index) =
        signature.arguments().iter().position(|carrier| matches!(carrier.clean(), CleanType::Nat))
    {
        return Some(Some(index));
    }
    matches!(signature.result().clean(), CleanType::Nat).then_some(None)
}

/// Whether a shape may have the runtime `Nat` carrier in its signature, and its
/// constructor name for the refusal when it may not.
///
/// EXHAUSTIVE, with no `_` arm, and that is the point: [`CleanOriginShape`] is
/// a deliberately CLOSED enum whose own documentation says a new variant must
/// be a compile error in its consumers rather than a runtime fall-through. So a
/// new shape does not inherit a verdict about the bignum carrier here -- it
/// fails to compile until someone decides one, which is the whole reason this
/// question belongs to the emitter.
fn shape_that_may_not_carry_nat(shape: &CleanOriginShape) -> Option<&'static str> {
    match shape {
        // TRANSPORT. Both emit `Return <block parameter>` and nothing else, so
        // the carrier is carried, never computed on. This is the one
        // non-recursion lane a `Nat` reaches today (`param` is the selection
        // table's only value-carrying whole-body row stated at
        // `CarrierClass::AnyExact`), and `tests/nat_carrier_shape_scope.rs`
        // pins that the emitted module validates.
        CleanOriginShape::Projection { .. } | CleanOriginShape::InductiveProjection { .. } => None,
        // THE RUNTIME'S OWN SHAPES. Their arithmetic is `NatRuntime`'s calls,
        // which is what the carrier was introduced for.
        CleanOriginShape::StructuralNatRec { .. } | CleanOriginShape::WellFoundedNatRec { .. } => {
            None
        }
        // COMPUTING SHAPES. Each one emits a `BinOp` / `UnOp` / `ICmp` /
        // `Const` / `Select` AT the carrier, so a `Nat` position would put the
        // runtime carrier under a machine operation.
        CleanOriginShape::ConstantUint { .. } => Some("ConstantUint"),
        CleanOriginShape::WrappingBinOp { .. } => Some("WrappingBinOp"),
        CleanOriginShape::Composed { .. } => Some("Composed"),
        CleanOriginShape::Select { .. } => Some("Select"),
        CleanOriginShape::SelectLiteral { .. } => Some("SelectLiteral"),
        CleanOriginShape::SelectOperands { .. } => Some("SelectOperands"),
        CleanOriginShape::UnsignedConditional { .. } => Some("UnsignedConditional"),
        CleanOriginShape::SelectBeq { .. } => Some("SelectBeq"),
        CleanOriginShape::SelectBeqGeneral { .. } => Some("SelectBeqGeneral"),
        CleanOriginShape::RawBinOp { .. } => Some("RawBinOp"),
        CleanOriginShape::DecideComparison { .. } => Some("DecideComparison"),
        CleanOriginShape::BoolConnective { .. } => Some("BoolConnective"),
        CleanOriginShape::BoolNot { .. } => Some("BoolNot"),
        CleanOriginShape::BoolExpression { .. } => Some("BoolExpression"),
        // NOT YET SPELLED at all, and its own arm refuses below. Named here
        // rather than grouped with the transport shapes so that spelling it
        // does not silently inherit permission for the bignum carrier.
        CleanOriginShape::RustCallChain { .. } => Some("RustCallChain"),
    }
}

/// A source parameter as a value, bounds-checked against the signature.
fn param_value(index: usize, arity: usize) -> Result<ValueId, CleanIrRefusal> {
    if index >= arity {
        return Err(CleanIrRefusal::ProjectionOutOfRange { projected: index, arity });
    }
    Ok(ValueId::new(index as u32))
}

/// Emit the sealed unsigned decision tree using the existing typed comparison
/// and select operations. Both arms are total, pure parameter/literal trees;
/// evaluating them before `Select` cannot add effects or partial operations.
/// Count decisions across both arms, not independently per path.
fn emit_unsigned_conditional(
    expr: &UIntConditional,
    ty: &Ty,
    next: &mut NextValue,
    block: &mut Block,
    arity: usize,
) -> Result<ValueId, CleanIrRefusal> {
    fn emit(
        expr: &UIntConditional,
        ty: &Ty,
        next: &mut NextValue,
        block: &mut Block,
        arity: usize,
        remaining: &mut usize,
    ) -> Result<ValueId, CleanIrRefusal> {
        match expr {
            UIntConditional::Operand(operand) => operand_value(*operand, ty, next, block, arity),
            UIntConditional::If { cmp, left, right, then_branch, else_branch } => {
                *remaining = remaining
                    .checked_sub(1)
                    .ok_or(CleanIrRefusal::InvalidUnsignedConditional)?;
                let lhs = param_value(*left, arity)?;
                let rhs = operand_value(*right, ty, next, block, arity)?;
                let cond = emit_icmp(icmp_of(*cmp), ty, lhs, rhs, next, block);
                let then_val = emit(then_branch, ty, next, block, arity, remaining)?;
                let else_val = emit(else_branch, ty, next, block, arity, remaining)?;
                let value = next.take();
                block.body.push(InstrNode {
                    inst: Inst::Select { ty: ty.clone(), cond, then_val, else_val },
                    results: vec![value],
                    proofs: Vec::new(),
                    span: None,
                    proof_context: None,
                    scope: None,
                });
                Ok(value)
            }
        }
    }
    let mut remaining = UINT_CONDITIONAL_MAX_DECISIONS;
    let value = emit(expr, ty, next, block, arity, &mut remaining)?;
    if UINT_CONDITIONAL_MAX_DECISIONS - remaining < 2 {
        return Err(CleanIrRefusal::InvalidUnsignedConditional);
    }
    Ok(value)
}

/// Emit a sealed Boolean tree in source order, with every temporary defined
/// before its use. Parameter indices already name source positions.
fn emit_bool_expr(
    expr: &BoolExpr,
    next: &mut NextValue,
    block: &mut Block,
    arity: usize,
) -> Result<ValueId, CleanIrRefusal> {
    let (op, lhs, rhs) = match expr {
        BoolExpr::Param(index) => return param_value(*index, arity),
        BoolExpr::Literal(value) => {
            let out = next.take();
            block.body.push(InstrNode {
                inst: Inst::Const { ty: Ty::Bool, value: Constant::Bool(*value) },
                results: vec![out],
                proofs: Vec::new(),
                span: None,
                proof_context: None,
                scope: None,
            });
            return Ok(out);
        }
        BoolExpr::Not(value) => {
            let operand = emit_bool_expr(value, next, block, arity)?;
            let truth = emit_bool_expr(&BoolExpr::Literal(true), next, block, arity)?;
            (BinOp::BXor, operand, truth)
        }
        BoolExpr::And(left, right) | BoolExpr::Or(left, right) => {
            let lhs = emit_bool_expr(left, next, block, arity)?;
            let rhs = emit_bool_expr(right, next, block, arity)?;
            let op = if matches!(expr, BoolExpr::And(..)) { BinOp::BAnd } else { BinOp::BOr };
            (op, lhs, rhs)
        }
    };
    let out = next.take();
    block.body.push(InstrNode {
        inst: Inst::BinOp { op, ty: Ty::Bool, lhs, rhs },
        results: vec![out],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    Ok(out)
}

/// The TrustIR predicate for a Clean comparison.
///
/// UNSIGNED, always: every carrier this lane admits is an unsigned machine
/// integer or `bool`. Emitting a signed predicate would silently reinterpret
/// the high bit, which is a wrong answer rather than a failed proof.
fn icmp_of(cmp: SelectCmp) -> ICmpOp {
    match cmp {
        SelectCmp::Lt => ICmpOp::Ult,
        SelectCmp::Le => ICmpOp::Ule,
        SelectCmp::Eq => ICmpOp::Eq,
    }
}

fn emit_icmp(
    op: ICmpOp,
    ty: &Ty,
    lhs: ValueId,
    rhs: ValueId,
    next: &mut NextValue,
    block: &mut Block,
) -> ValueId {
    let cond = next.take();
    block.body.push(InstrNode {
        inst: Inst::ICmp { op, ty: ty.clone(), lhs, rhs },
        results: vec![cond],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    cond
}

fn emit_select_and_return(
    ty: &Ty,
    cond: ValueId,
    then_val: ValueId,
    else_val: ValueId,
    next: &mut NextValue,
    block: &mut Block,
) {
    let out = next.take();
    block.body.push(InstrNode {
        inst: Inst::Select { ty: ty.clone(), cond, then_val, else_val },
        results: vec![out],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    block.body.push(ret_node(out));
}

/// A `beq` operand: parameter, literal, or a raw binop computed into a
/// temporary before the decision reads it.
fn beq_operand_value(
    operand: &BeqOperand,
    ty: &Ty,
    next: &mut NextValue,
    block: &mut Block,
    arity: usize,
) -> Result<ValueId, CleanIrRefusal> {
    match operand {
        BeqOperand::Param(index) => param_value(*index, arity),
        BeqOperand::Const(value) => {
            operand_value(ArithOperand::Const(*value), ty, next, block, arity)
        }
        // `#[non_exhaustive]`-shaped growth and the raw-binop leaf both land
        // here. The divisor boundary applies to a computed leaf exactly as it
        // does to a whole body, so this refuses rather than guessing.
        _ => {
            Err(CleanIrRefusal::ShapeNotYetSpelled { shape: "SelectBeqGeneral(computed operand)" })
        }
    }
}

/// Every recursion shape in this fragment recurses on `pred(n)`.
///
/// Checked rather than assumed: the plan CARRIES `rec_arg` precisely so the
/// emitter, the recognizer and the kernel identity check all name the same fact,
/// and an emitter that ignored it would be reproducing a termination argument it
/// never read.
fn check_rec_arg(rec_arg: &RecBodyExpr, shape: &'static str) -> Result<(), CleanIrRefusal> {
    match rec_arg {
        RecBodyExpr::Pred => Ok(()),
        _ => Err(CleanIrRefusal::RecursionArgIsNotPred { shape }),
    }
}

/// The handles ONE emitted block allocated, and which of them may be released.
///
/// Per block, not per function: every handle recorded here is defined in the
/// block whose `Return` the releases are emitted before, so each one dominates
/// its own release. The entry block allocates nothing (it only tests the
/// parameter for zero), so there is no cross-block case to reason about.
#[derive(Debug, Default)]
struct OwnedHandles {
    /// Handles this block ALLOCATED, in creation order.
    ///
    /// Exactly the results of the pinned `from_u64` / `add` / `sub` entry
    /// points, plus the self-call's result when it is known fresh. Each is a
    /// brand-new allocation aliasing no operand and no earlier result — a
    /// measured property of the shims, not a convention: `Nat::add` and
    /// `Nat::sub` are `(&self, &Self) -> Self` so they cannot hand back an
    /// operand, `Nat::from_u64` has no operand to hand back, and each shim
    /// returns a `Box::into_raw` of a fresh box
    /// (`trust-bignum/src/handle_abi.rs`, pinned by
    /// `every_produced_handle_is_a_fresh_allocation_distinct_from_its_operands`).
    fresh: Vec<ValueId>,
    /// Fresh handles WITHHELD from release.
    ///
    /// A handle passed to the SELF-CALL in a body that can return one of its
    /// parameters: the callee may hand that very allocation straight back, so
    /// the self-call's result and the argument may denote one allocation, and
    /// releasing the argument would leave the result dangling. Leaking it is
    /// the sound direction.
    withheld: Vec<ValueId>,
}

impl OwnedHandles {
    /// Record a handle this block ALLOCATED.
    fn allocated(&mut self, handle: ValueId) {
        self.fresh.push(handle);
    }

    /// Withhold `handle` from release.
    fn withhold(&mut self, handle: ValueId) {
        self.withheld.push(handle);
    }

    /// The handles to release before returning `returned`, in allocation order.
    ///
    /// `returned` is excluded because returning a handle TRANSFERS it: the
    /// caller owns it after the `Return`, and releasing it here would hand back
    /// a dangling word. That is not a leak in this body — it is the one handle
    /// whose release belongs to somebody else.
    fn releasable(&self, returned: ValueId) -> Vec<ValueId> {
        self.fresh
            .iter()
            .copied()
            .filter(|handle| *handle != returned && !self.withheld.contains(handle))
            .collect()
    }
}

/// Is every handle this body can RETURN a fresh allocation?
///
/// This decides whether the self-call's result may be released, and whether the
/// argument passed to it may be. It is a question about the function being
/// emitted, and it is answerable BECAUSE the self-call's callee IS that
/// function: `check_identities` requires `nat.self_id` to equal the emitted
/// `id`, so there is no third party whose contract would have to be assumed.
///
/// A body returns exactly its arm's top-level value, so the question is whether
/// either arm's ROOT denotes an allocation this body made. [`is_fresh_rooted`]
/// answers it per arm, and the only `false` case is a root that denotes a
/// PARAMETER — a handle the caller owns, handed straight back.
///
/// **Why the `Rec` root is not circular.** `is_fresh_rooted` calls a `Rec` root
/// fresh, which is the very property being computed. The assumption discharges
/// by induction on RECURSION DEPTH, not on syntax: the zero arm contains no
/// `Rec` at all (the plan says so and `emit_rec_body` refuses one there), so
/// the innermost frame returns through a non-`Rec` root; and if every frame
/// below returns a fresh allocation, a frame returning its self-call's result
/// returns a fresh allocation too. So whenever neither root is a parameter,
/// every value this function can actually return at runtime is an allocation it
/// made, distinct from every handle it was given.
fn body_returns_a_fresh_allocation(zero_arm: &RecBodyExpr, nonzero_arm: &RecBodyExpr) -> bool {
    is_fresh_rooted(zero_arm) && is_fresh_rooted(nonzero_arm)
}

/// Does `expr`'s ROOT denote an allocation the emitted body made?
///
/// A POSITIVE enumeration with a fail-closed default, deliberately: written as
/// `!matches!(expr, Decreasing)` it would answer "fresh" for every future
/// `RecBodyExpr` node, including the ones that denote a parameter
/// ([`RecBodyExpr::Param`] already does), and the failure direction of a wrong
/// `true` here is a double free in trusted code.
fn is_fresh_rooted(expr: &RecBodyExpr) -> bool {
    match expr {
        // Each of these emits a pinned entry-point call whose result is a
        // fresh allocation: `sub`, `from_u64`, `add`.
        RecBodyExpr::Pred | RecBodyExpr::NatConst(_) | RecBodyExpr::Add(_, _) => true,
        // The self-call's result. Fresh exactly when this body is
        // return-fresh — see the induction argument in
        // `body_returns_a_fresh_allocation`.
        RecBodyExpr::Rec => true,
        // The decreasing PARAMETER, returned verbatim: the caller's
        // allocation, not ours.
        RecBodyExpr::Decreasing => false,
        // Every other node — `Param`, and anything added later. `Param` is a
        // parameter and is genuinely not fresh; the rest are refused by
        // `emit_rec_body` before they can reach a release decision, and fail
        // closed here as well rather than relying on that.
        _ => false,
    }
}

/// Emit the zero-test / predecessor / self-call contract.
///
/// The same shape the MIR lane emits, in TrustIR's idiom:
///
/// ```text
///   bb0:  z = is_zero(n);  cond_br z -> bb1, bb2
///   bb1:  <zero arm>;      <releases>;  return
///   bb2:  p = sub(n, 1);   r = self(p);  <nonzero arm using r>;  <releases>;  return
/// ```
///
/// A branch rather than the branchless `Select` the comparison shapes use, and
/// that is NOT a style choice: `Select` evaluates BOTH arms, and the nonzero arm
/// contains the self-call. A branchless spelling would recurse unconditionally
/// and never terminate.
///
/// The `<releases>` step is present only when the caller supplied
/// [`NatRuntime::release`]. It is emitted just before the `Return` of the arm
/// that ALLOCATED the handles, which is the last point at which they are all
/// live and still in scope, and after every call that read them — correct
/// because the arithmetic entry points only BORROW their operands
/// (`*const Nat` reborrowed shared; nothing consumes, frees or mutates a
/// handle), so a handle survives every call that reads it.
fn emit_nat_recursion(
    entry: &mut Block,
    blocks: &mut Vec<Block>,
    arity: usize,
    nat: &NatRuntime,
    zero_arm: &RecBodyExpr,
    nonzero_arm: &RecBodyExpr,
) -> Result<(), CleanIrRefusal> {
    if arity != 1 {
        return Err(CleanIrRefusal::ProjectionOutOfRange { projected: 1, arity });
    }
    let n = ValueId::new(0);
    let mut next = NextValue::after_params(arity);

    let zero_block = BlockId::new(1);
    let nonzero_block = BlockId::new(2);

    let is_zero = next.take();
    entry.body.push(call_node(nat.is_zero, vec![n], is_zero));
    entry.body.push(InstrNode {
        inst: Inst::CondBr {
            cond: is_zero,
            then_target: zero_block,
            then_args: Vec::new(),
            else_target: nonzero_block,
            else_args: Vec::new(),
        },
        results: Vec::new(),
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });

    // Decided ONCE, before either arm is built, because both arms' release
    // decisions read it and two independent readings of one fact is how they
    // would come to disagree.
    let returns_fresh = body_returns_a_fresh_allocation(zero_arm, nonzero_arm);

    // ── the zero arm: no `Rec`, no `Pred` (the plan guarantees it) ──────────
    let mut zero = Block::new(zero_block);
    let mut zero_owned = OwnedHandles::default();
    let zero_value = emit_rec_body(zero_arm, &mut zero, &mut next, nat, n, None, &mut zero_owned)?;
    release_owned(&mut zero, nat, &zero_owned, zero_value);
    zero.body.push(ret_node(zero_value));

    // ── the nonzero arm: predecessor, then the self-call ───────────────────
    let mut nonzero = Block::new(nonzero_block);
    let mut owned = OwnedHandles::default();
    // The literal 1, materialized the SAME way `RecBodyExpr::NatConst` does --
    // through `nat_literal`, which passes the value. Open-coding the call here
    // is what let the missing-argument bug exist in two places at once.
    let one = nat_literal(1, nat, &mut nonzero, &mut next, &mut owned);
    let pred = next.take();
    nonzero.body.push(call_node(nat.sub, vec![n, one], pred));
    owned.allocated(pred);
    let rec = next.take();
    nonzero.body.push(call_node(nat.self_id, vec![pred], rec));
    if returns_fresh {
        // The callee is THIS function and it cannot return a parameter, so
        // `rec` is an allocation the call made: releasable, and `pred` stays
        // releasable because nothing aliases it.
        owned.allocated(rec);
    } else {
        // The callee — again, THIS function — can return its parameter, so
        // `rec` may BE `pred`. Release neither: one of them is possibly the
        // value being returned, and the other is possibly the same allocation.
        //
        // Not recording `rec` is the conservative half, and it is deliberately
        // cheaper than it looks: on a body that can return its parameter, the
        // nonzero arm's root is what decides whether `rec` is returned, and on
        // the shape the planner actually produces here (`countdownId`, arm root
        // `Rec`) it IS the returned value — so withholding it costs nothing at
        // all. A longer argument could release it in the remaining case (every
        // frame either hands back its own parameter or an allocation a deeper
        // frame withheld and transferred, so the caller owns it either way),
        // and it is not made here: the gain is one allocation on a shape that
        // does not exist yet, and the cost of getting a transfer chain wrong is
        // a double free in a trusted runtime.
        owned.withhold(pred);
    }
    let value = emit_rec_body(nonzero_arm, &mut nonzero, &mut next, nat, n, Some(rec), &mut owned)?;
    release_owned(&mut nonzero, nat, &owned, value);
    nonzero.body.push(ret_node(value));

    blocks.push(zero);
    blocks.push(nonzero);
    Ok(())
}

/// Release every handle `block` owns except the one it returns.
///
/// A no-op without a release callee ([`NatRuntime::release`] `None`), which is
/// the pre-2026-09-17 behaviour and is sound: leaking loses memory, releasing
/// without ownership corrupts a trusted runtime.
fn release_owned(block: &mut Block, nat: &NatRuntime, owned: &OwnedHandles, returned: ValueId) {
    let Some(release) = nat.release else {
        return;
    };
    for handle in owned.releasable(returned) {
        block.body.push(release_node(release, handle));
    }
}

/// Emit a `RecBodyExpr`, returning the value it denotes.
///
/// `rec` is the self-call's result, present only in the nonzero arm. A `Rec` in
/// the zero arm is refused rather than defaulted: the plan says the zero case
/// contains none, and inventing a value there would emit a body that computes
/// something the declaration does not say.
fn emit_rec_body(
    expr: &RecBodyExpr,
    block: &mut Block,
    next: &mut NextValue,
    nat: &NatRuntime,
    decreasing: ValueId,
    rec: Option<ValueId>,
    owned: &mut OwnedHandles,
) -> Result<ValueId, CleanIrRefusal> {
    match expr {
        // The PARAMETER. Not recorded: the caller owns it, and releasing a
        // borrowed handle is the one mistake here that corrupts the runtime
        // rather than merely losing memory.
        RecBodyExpr::Decreasing => Ok(decreasing),
        // The self-call's result. Recorded (or withheld) at the self-call
        // SITE, in `emit_nat_recursion`, which is where the freshness verdict
        // lives — and recorded once even when the arm reads `Rec` twice.
        RecBodyExpr::Rec => {
            rec.ok_or(CleanIrRefusal::RecursionArgIsNotPred { shape: "Rec in the zero arm" })
        }
        RecBodyExpr::Pred => {
            let one = nat_literal(1, nat, block, next, owned);
            let p = next.take();
            block.body.push(call_node(nat.sub, vec![decreasing, one], p));
            owned.allocated(p);
            Ok(p)
        }
        RecBodyExpr::NatConst(k) => Ok(nat_literal(*k, nat, block, next, owned)),
        RecBodyExpr::Add(left, right) => {
            let l = emit_rec_body(left, block, next, nat, decreasing, rec, owned)?;
            let r = emit_rec_body(right, block, next, nat, decreasing, rec, owned)?;
            let out = next.take();
            block.body.push(call_node(nat.add, vec![l, r], out));
            // `add` allocates and only BORROWS `l` and `r`, so both of them
            // stay owned by whoever owned them and this result is a third
            // allocation.
            owned.allocated(out);
            Ok(out)
        }
        // `RecBodyExpr` carries nodes this producer has no spelling for yet
        // (`Mul`, `Sub`, `Rem`, `Param`); a new one must be given a spelling
        // here rather than silently becoming one of these. Note for whoever
        // adds one: it must also record what it ALLOCATES in `owned`, or the
        // handles it makes leak — and must record nothing it merely borrows.
        _ => Err(CleanIrRefusal::ShapeNotYetSpelled { shape: "RecBodyExpr node" }),
    }
}

/// Materialize a `Nat` literal: a machine constant, then `from_u64` on it.
///
/// The VALUE has to be passed. An earlier version called `from_u64` with no
/// arguments and dropped the literal on the floor, so every `NatConst(k)`
/// produced whatever that runtime happened to return -- `countdownSum 0` came
/// out as 1 instead of 0. The structural tests could not see it (the call was
/// present and in the right place); the kernel-agreement test caught it on the
/// first input. Keep the argument.
fn nat_literal(
    value: u64,
    nat: &NatRuntime,
    block: &mut Block,
    next: &mut NextValue,
    owned: &mut OwnedHandles,
) -> ValueId {
    let raw = next.take();
    block.body.push(InstrNode {
        inst: Inst::Const { ty: Ty::U64, value: canonical_constant(u128::from(value)) },
        results: vec![raw],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    let handle = next.take();
    block.body.push(call_node(nat.from_u64, vec![raw], handle));
    // `raw` is the machine `u64`, not a handle — only `from_u64`'s RESULT is an
    // allocation, and it is a fresh one.
    owned.allocated(handle);
    handle
}

fn call_node(callee: FuncId, args: Vec<ValueId>, out: ValueId) -> InstrNode {
    InstrNode {
        inst: Inst::Call { callee, args },
        results: vec![out],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    }
}

/// A call to the RELEASE entry point: one handle in, NOTHING out.
///
/// `results` is empty, and that is the pinned signature rather than an
/// omission: the pin spells release's result as an EMPTY return list, which is
/// a different `FuncTy` from a one-element `Unit` return, and trust-ir refuses
/// the wrong one (`HandleEntryPointSignatureMismatch`). Separate from
/// [`call_node`] because that one requires a result value.
fn release_node(release: FuncId, handle: ValueId) -> InstrNode {
    InstrNode {
        inst: Inst::Call { callee: release, args: vec![handle] },
        results: Vec::new(),
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn shape_todo(shape: &'static str) -> CleanIrRefusal {
    CleanIrRefusal::ShapeNotYetSpelled { shape }
}

/// Hands out fresh [`ValueId`]s after the block parameters.
///
/// A counter rather than ad-hoc arithmetic at each site: every temporary in a
/// body must be distinct, and two sites computing "params + 1" independently is
/// how two temporaries end up sharing an id.
struct NextValue(u32);

impl NextValue {
    fn after_params(arity: usize) -> Self {
        Self(arity as u32)
    }

    fn take(&mut self) -> ValueId {
        let id = ValueId::new(self.0);
        self.0 += 1;
        id
    }
}

/// The TrustIR op for a Clean wrapping op.
///
/// Total and explicit: `ArithBinOp` is the vocabulary the plan and the MIR
/// recognizer share, and these three are the only wrapping primitives the lane
/// admits.
fn trust_ir_binop(op: ArithBinOp) -> BinOp {
    match op {
        ArithBinOp::Add => BinOp::Add,
        ArithBinOp::Sub => BinOp::Sub,
        ArithBinOp::Mul => BinOp::Mul,
    }
}

/// Materialize an operand as a value: a source parameter is already a block
/// parameter, a literal needs a `Const`.
fn operand_value(
    operand: ArithOperand,
    ty: &Ty,
    next: &mut NextValue,
    block: &mut Block,
    arity: usize,
) -> Result<ValueId, CleanIrRefusal> {
    match operand {
        ArithOperand::Param(index) => {
            if index >= arity {
                return Err(CleanIrRefusal::ProjectionOutOfRange { projected: index, arity });
            }
            Ok(ValueId::new(index as u32))
        }
        ArithOperand::Const(value) => {
            let width = unsigned_width(ty);
            if !fits_unsigned(value, width) {
                return Err(CleanIrRefusal::ConstantOutOfRange { value, width });
            }
            let id = next.take();
            block.body.push(InstrNode {
                inst: Inst::Const { ty: ty.clone(), value: canonical_constant(value) },
                results: vec![id],
                proofs: Vec::new(),
                span: None,
                proof_context: None,
                scope: None,
            });
            Ok(id)
        }
    }
}

/// Emit a composed arithmetic tree in post-order, returning the root's value.
fn emit_arith_expr(
    expr: &ArithExpr,
    ty: &Ty,
    next: &mut NextValue,
    block: &mut Block,
    arity: usize,
) -> Result<ValueId, CleanIrRefusal> {
    match expr {
        ArithExpr::Operand(operand) => operand_value(*operand, ty, next, block, arity),
        ArithExpr::Bin { op, left, right } => {
            // Children first, and LEFT before RIGHT: post-order is what the MIR
            // lane's call chain does, and evaluation order is observable in the
            // emitted body even though these ops are pure.
            let lhs = emit_arith_expr(left, ty, next, block, arity)?;
            let rhs = emit_arith_expr(right, ty, next, block, arity)?;
            let out = next.take();
            block.body.push(InstrNode {
                inst: Inst::BinOp { op: trust_ir_binop(*op), ty: ty.clone(), lhs, rhs },
                results: vec![out],
                proofs: Vec::new(),
                span: None,
                proof_context: None,
                scope: None,
            });
            Ok(out)
        }
    }
}

/// `Constant` is canonical: `Int` carries everything representable in `i128`,
/// `U128` only the upper half of the u128 range. One spelling per value.
fn canonical_constant(value: u128) -> Constant {
    if value > i128::MAX as u128 { Constant::U128(value) } else { Constant::Int(value as i128) }
}

/// The width of an unsigned TrustIR carrier this lane can emit at.
///
/// Only the types [`trust_ir_ty`] produces reach here, so the fallback is
/// `u128`'s width rather than a panic: an unreachable arm that aborts the
/// compiler is worse than one that yields a width the range check will then
/// apply conservatively.
fn unsigned_width(ty: &Ty) -> u32 {
    match ty {
        Ty::Bool => 1,
        Ty::U8 => 8,
        Ty::U16 => 16,
        Ty::U32 => 32,
        Ty::U64 => 64,
        _ => 128,
    }
}

fn ret_node(value: ValueId) -> InstrNode {
    InstrNode {
        inst: Inst::Return { values: vec![value] },
        results: Vec::new(),
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    }
}

/// Does `value` fit an unsigned carrier of `width` bits?
///
/// Written without `1u128 << width` so `width == 128` does not overflow the
/// shift — the case a fixed-width check most easily gets wrong.
fn fits_unsigned(value: u128, width: u32) -> bool {
    match width {
        0 => value == 0,
        w if w >= 128 => true,
        w => value < (1u128 << w),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emitted_clean_origin_definition_uses_the_compiler_minted_rust_abi() {
        let mut session = trust_certify::clean_island::CleanIslandSession::new();
        let batch = session.check_all(&["def pick (a : UInt64) : UInt64 := a"]);
        assert!(!batch.is_rejected(), "the Clean declaration must kernel-check: {batch:?}");
        let env = session.environment().expect("an untainted session has an environment");
        let plan = trust_clean_origin::plan_clean_origin_body(env, "pick")
            .expect("the projection must plan");
        let function = emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .expect("the projection must emit");

        assert_eq!(
            function.calling_conv,
            CallingConv::Rust,
            "the TrustIR definition must agree with the Rust ABI installed for the synthetic item"
        );
    }

    #[test]
    fn composed_boolean_source_emits_valid_ir_with_complete_truth_tables() {
        use trust_ir::interpret::{InterpretValue, Interpreter};

        type Expected = fn(bool, bool, bool) -> bool;
        let cases: [(&str, &str, Expected); 4] = [
            (
                "release",
                "def release (r p e : Bool) : Bool := r || (p && e)",
                |r, p, e| r || (p && e),
            ),
            (
                "negated",
                "def negated (r p e : Bool) : Bool := not (r || (p && e))",
                |r, p, e| !(r || (p && e)),
            ),
            (
                "literal",
                "def literal (r p e : Bool) : Bool := (r || false) && (not p || e)",
                |r, p, e| r && (!p || e),
            ),
            (
                "reversed",
                "def reversed (first middle last : Bool) : Bool := last || (not first && middle)",
                |first, middle, last| last || (!first && middle),
            ),
        ];
        let mut session = trust_certify::clean_island::CleanIslandSession::new();
        let sources: Vec<&str> = cases.iter().map(|(_, source, _)| *source).collect();
        let batch = session.check_all(&sources);
        assert!(!batch.is_rejected(), "the actual Clean sources must check: {batch:?}");
        let env = session.environment().expect("an untainted source environment");
        for (name, _, expected) in cases {
            let plan = trust_clean_origin::plan_clean_origin_body(env, name)
                .unwrap_or_else(|error| panic!("{name} must plan: {error:?}"));
            assert!(matches!(plan.shape(), CleanOriginShape::BoolExpression { .. }));
            let signature = trust_ir_func_ty(plan.signature()).expect("Boolean signature");
            let function = emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
                .unwrap_or_else(|error| panic!("{name} must emit: {error:?}"));
            let mut module = Module::new(format!("composed-boolean::{name}"));
            module.func_types.push(signature);
            module.functions.push(function.clone());
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{name} must validate: {errors:?}");
            assert!(function.summary.is_none() && function.proofs.is_empty());
            for first in [false, true] {
                for middle in [false, true] {
                    for last in [false, true] {
                        let output = Interpreter::new()
                            .execute_function(
                                &function,
                                [first, middle, last].into_iter().map(InterpretValue::bool),
                            )
                            .unwrap_or_else(|error| panic!("{name} must execute: {error:?}"));
                        assert_eq!(
                            output.returns,
                            vec![InterpretValue::bool(expected(first, middle, last))],
                            "{name}({first}, {middle}, {last})",
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn boolean_expression_parameter_indices_remain_source_indices() {
        let mut block = Block::new(BlockId::new(0));
        let mut next = NextValue::after_params(3);
        assert!(matches!(
            emit_bool_expr(&BoolExpr::Param(3), &mut next, &mut block, 3),
            Err(CleanIrRefusal::ProjectionOutOfRange { projected: 3, arity: 3 })
        ));
        assert!(block.body.is_empty(), "invalid parameters emit no partial instruction");
    }

    #[test]
    fn unsigned_conditional_emission_keeps_the_shared_tree_bound() {
        fn chain(decisions: usize) -> UIntConditional {
            if decisions == 0 {
                return UIntConditional::Operand(ArithOperand::Param(0));
            }
            UIntConditional::If {
                cmp: SelectCmp::Lt,
                left: 0,
                right: ArithOperand::Const(19),
                then_branch: Box::new(UIntConditional::Operand(ArithOperand::Const(0))),
                else_branch: Box::new(chain(decisions - 1)),
            }
        }
        let emit = |expr: &UIntConditional| {
            emit_unsigned_conditional(
                expr,
                &Ty::U8,
                &mut NextValue::after_params(1),
                &mut Block::new(BlockId::new(0)),
                1,
            )
        };
        assert!(emit(&chain(UINT_CONDITIONAL_MAX_DECISIONS)).is_ok());
        for count in [0, 1, UINT_CONDITIONAL_MAX_DECISIONS + 1] {
            assert!(matches!(emit(&chain(count)), Err(CleanIrRefusal::InvalidUnsignedConditional)));
        }
        let too_many_across_siblings = UIntConditional::If {
            cmp: SelectCmp::Lt,
            left: 0,
            right: ArithOperand::Const(30),
            then_branch: Box::new(chain(UINT_CONDITIONAL_MAX_DECISIONS / 2)),
            else_branch: Box::new(chain(UINT_CONDITIONAL_MAX_DECISIONS / 2)),
        };
        assert!(matches!(
            emit(&too_many_across_siblings),
            Err(CleanIrRefusal::InvalidUnsignedConditional)
        ));
    }

    #[test]
    fn unsigned_conditional_operands_keep_parameter_and_width_checks() {
        let emit = |left, right, leaf| {
            let expr = UIntConditional::If {
                cmp: SelectCmp::Lt,
                left,
                right,
                then_branch: Box::new(UIntConditional::Operand(leaf)),
                else_branch: Box::new(UIntConditional::If {
                    cmp: SelectCmp::Lt,
                    left: 0,
                    right: ArithOperand::Const(30),
                    then_branch: Box::new(UIntConditional::Operand(ArithOperand::Const(1))),
                    else_branch: Box::new(UIntConditional::Operand(ArithOperand::Const(0))),
                }),
            };
            emit_unsigned_conditional(
                &expr,
                &Ty::U8,
                &mut NextValue::after_params(1),
                &mut Block::new(BlockId::new(0)),
                1,
            )
        };
        assert!(matches!(
            emit(1, ArithOperand::Const(19), ArithOperand::Const(0)),
            Err(CleanIrRefusal::ProjectionOutOfRange { projected: 1, arity: 1 })
        ));
        assert!(matches!(
            emit(0, ArithOperand::Param(1), ArithOperand::Const(0)),
            Err(CleanIrRefusal::ProjectionOutOfRange { projected: 1, arity: 1 })
        ));
        assert!(matches!(
            emit(0, ArithOperand::Const(19), ArithOperand::Param(1)),
            Err(CleanIrRefusal::ProjectionOutOfRange { projected: 1, arity: 1 })
        ));
        assert!(matches!(
            emit(0, ArithOperand::Const(256), ArithOperand::Const(0)),
            Err(CleanIrRefusal::ConstantOutOfRange { value: 256, width: 8 })
        ));
        assert!(matches!(
            emit(0, ArithOperand::Const(19), ArithOperand::Const(256)),
            Err(CleanIrRefusal::ConstantOutOfRange { value: 256, width: 8 })
        ));
    }

    /// The machine set this producer admits, stated once so a drifting arm has
    /// to change a test that says why the set is what it is.
    ///
    /// It is exactly `trust-clean-origin::carrier_class_of`'s `UInt(8|16|32|64)`
    /// and exactly `trust_spec_elab::MachineUIntWidth`. Those three sets are
    /// required to agree: the first decides what a plan may carry, the second
    /// what the island can name, and this one what gets emitted. A width in one
    /// and not the others is either an unwitnessable emission or a plan this
    /// crate refuses for no reason.
    const ADMITTED_WIDTHS: [u32; 4] = [8, 16, 32, 64];

    #[test]
    fn every_admitted_width_has_a_trust_ir_carrier() {
        for w in ADMITTED_WIDTHS {
            for clean in [CleanType::UInt(w), CleanType::BitVec(w)] {
                let ty = trust_ir_ty(clean.clone(), None, None)
                    .unwrap_or_else(|e| panic!("width {w} must carry ({clean:?}): {e}"));
                assert_eq!(
                    ty.bit_width().expect("a machine carrier has a width"),
                    w,
                    "width {w} ({clean:?}) must carry AT {w} bits, not at {ty:?} -- a carrier \
                     emitted at the wrong width is the wrong-binary outcome this lane exists \
                     to prevent",
                );
            }
        }
    }

    /// 128 is refused, and this test is the reason it is not an oversight.
    ///
    /// `MachineUIntWidth` has no `U128` and `island_return_domain` maps no
    /// `UInt128`, so the kernel cannot reduce an application at a 128-bit
    /// carrier and the agreement gate could never cover one. Emitting it would
    /// be a claim no oracle in the lane can check. If `UInt128` is ever added to
    /// the island AND to `MachineUIntWidth` AND to `carrier_class_of`, this test
    /// is what tells you to add the arm back -- together with a gate row.
    #[test]
    fn unwitnessable_widths_are_refused_rather_than_emitted() {
        for w in [1, 7, 24, 128, 256] {
            assert!(
                trust_ir_ty(CleanType::UInt(w), None, None).is_err(),
                "width {w} has no island carrier, so it must refuse rather than emit",
            );
        }
    }

    // ── G4: the call-edge identity guards ──────────────────────────────────
    //
    // These cover the one class of defect in this producer that COMPILES
    // CLEANLY and VALIDATES: a call edge naming the wrong function. Every
    // structural check downstream is satisfied by a well-formed call to the
    // wrong callee, and the whole-module walk that would catch it in the
    // compiler is a debug-gated tripwire that fails no build. So the checks
    // live here, at emission, where the ids are still in hand.

    fn runtime(self_id: u32) -> NatRuntime {
        NatRuntime {
            carrier: NatCarrier::PinnedHandle,
            from_u64: FuncId::new(10),
            add: FuncId::new(11),
            sub: FuncId::new(12),
            is_zero: FuncId::new(13),
            release: Some(FuncId::new(14)),
            self_id: FuncId::new(self_id),
        }
    }

    /// The same runtime with no release callee: the leak-everything request.
    fn runtime_without_release(self_id: u32) -> NatRuntime {
        NatRuntime { release: None, ..runtime(self_id) }
    }

    /// `roles()` is the role-to-field mapping and `NAT_RUNTIME_ROLES` is what
    /// the diagnostics and the pin lookup read. They are two spellings of one
    /// fact, so they are pinned together: a role renamed in one and not the
    /// other would make `check_pinned_callees` look up an entry point the pin
    /// row does not have, which fails closed but says the wrong thing.
    #[test]
    fn roles_are_exactly_the_declared_role_names() {
        let named: Vec<&str> = runtime(3).roles().into_iter().map(|(role, _)| role).collect();
        assert_eq!(named, NAT_RUNTIME_ROLES.to_vec());
    }

    /// Without a release callee the release ROW is absent from `roles()`, not
    /// present with a placeholder id.
    ///
    /// Both consumers of `roles()` would misbehave on a placeholder: the
    /// distinctness check would refuse a perfectly good runtime whose real ids
    /// happened to include it, and `check_pinned_callees` would resolve a
    /// `FuncId` the caller never named and demand it be the release shim.
    #[test]
    fn an_absent_release_callee_is_an_absent_role_row() {
        let named: Vec<&str> =
            runtime_without_release(3).roles().into_iter().map(|(role, _)| role).collect();
        assert_eq!(named, ["from_u64", "add", "sub", "is_zero"]);
        assert!(
            !named.contains(&NAT_RELEASE_ROLE),
            "an unsupplied release callee must not appear as a role"
        );
        // And the four that ARE supplied still agree with the pin's own order.
        assert_eq!(named.as_slice(), &NAT_RUNTIME_ROLES[..4]);
    }

    /// A release callee aliasing another runtime entry point is refused by the
    /// same distinctness check as any other alias.
    ///
    /// This is the alias that would be worst: release aliased onto `add` makes
    /// every release compute a sum, and every `add` free its operand.
    #[test]
    fn a_release_callee_that_aliases_another_entry_point_is_refused() {
        let mut nat = runtime(3);
        nat.release = Some(nat.add);
        let refusal = nat.check_identities(FuncId::new(3)).expect_err("must refuse");
        assert!(matches!(refusal, CleanIrRefusal::NatRuntimeIdsAlias { .. }), "{refusal:?}");

        // And aliasing the function being emitted is refused too: a "release"
        // that called back into the recursion would recurse instead of free.
        let mut nat = runtime(3);
        nat.release = Some(FuncId::new(3));
        let refusal = nat.check_identities(FuncId::new(3)).expect_err("must refuse");
        assert!(
            matches!(refusal, CleanIrRefusal::NatRuntimeIdAliasesTheEmittedFunction { .. }),
            "{refusal:?}"
        );
    }

    /// The coherent case passes — so the checks below are refusing a real
    /// distinction, not refusing everything.
    #[test]
    fn a_coherent_nat_runtime_is_accepted() {
        assert!(runtime(3).check_identities(FuncId::new(3)).is_ok());
    }

    /// `self_id` and the emitted `id` are two independently supplied names for
    /// ONE function. When they disagree the emitted body's "self-call" is a
    /// call to something else: a well-formed, well-typed body that is not the
    /// declaration and is not a recursion.
    #[test]
    fn a_self_id_that_is_not_the_emitted_function_is_refused() {
        let refusal = runtime(0).check_identities(FuncId::new(7)).unwrap_err();
        assert_eq!(
            refusal,
            CleanIrRefusal::NatRuntimeSelfIdIsNotTheEmittedFunction { self_id: 0, emitted: 7 }
        );
        let text = refusal.to_string();
        assert!(text.contains("Options:"), "must name the fix: {text}");
        assert!(text.contains("placeholder"), "must name the placeholder case: {text}");
    }

    /// Two runtime entries at one id makes every call to the first a call to
    /// the second. Checked pairwise, so no pair is checked by accident.
    #[test]
    fn aliased_runtime_ids_are_refused_pairwise() {
        let pairs: [(fn(&mut NatRuntime), &str, &str); 6] = [
            (|n| n.add = n.from_u64, "from_u64", "add"),
            (|n| n.sub = n.from_u64, "from_u64", "sub"),
            (|n| n.is_zero = n.from_u64, "from_u64", "is_zero"),
            (|n| n.sub = n.add, "add", "sub"),
            (|n| n.is_zero = n.add, "add", "is_zero"),
            (|n| n.is_zero = n.sub, "sub", "is_zero"),
        ];
        for (alias, first, second) in pairs {
            let mut nat = runtime(3);
            alias(&mut nat);
            let refusal = nat.check_identities(FuncId::new(3)).unwrap_err();
            let CleanIrRefusal::NatRuntimeIdsAlias { first: got_first, second: got_second, .. } =
                refusal
            else {
                panic!("aliasing `{first}` and `{second}` must refuse, got {refusal:?}");
            };
            assert_eq!(
                (got_first, got_second),
                (first, second),
                "the refusal must name the aliased pair"
            );
        }
    }

    /// A Clean declaration is never one of its own `Nat` primitives. Emitting
    /// against a runtime that says otherwise turns an arithmetic call into
    /// unbounded recursion.
    #[test]
    fn a_runtime_entry_that_aliases_the_emitted_function_is_refused() {
        for (name, alias) in [
            ("from_u64", (|n: &mut NatRuntime, id| n.from_u64 = id) as fn(&mut NatRuntime, FuncId)),
            ("add", |n: &mut NatRuntime, id| n.add = id),
            ("sub", |n: &mut NatRuntime, id| n.sub = id),
            ("is_zero", |n: &mut NatRuntime, id| n.is_zero = id),
        ] {
            let mut nat = runtime(3);
            alias(&mut nat, FuncId::new(3));
            let refusal = nat.check_identities(FuncId::new(3)).unwrap_err();
            assert_eq!(
                refusal,
                CleanIrRefusal::NatRuntimeIdAliasesTheEmittedFunction { runtime: name, id: 3 },
                "`{name}` naming the emitted function must refuse"
            );
        }
    }

    /// `callee_edges` reads BOTH static-callee spellings, because the join
    /// seam's own edge rewriter (`clean_origin_join::repoint_edges`) rewrites
    /// both. A publication precondition that saw only `Inst::Call` would report
    /// "no edges" for a body carrying a function pointer.
    #[test]
    fn callee_edges_reads_both_static_callee_spellings() {
        let mut block = Block::new(BlockId::new(0));
        block.body.push(call_node(FuncId::new(11), vec![ValueId::new(0)], ValueId::new(1)));
        block.body.push(InstrNode {
            inst: Inst::Const { ty: Ty::Ptr, value: Constant::FnDef(FuncId::new(12)) },
            results: vec![ValueId::new(2)],
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        block.body.push(ret_node(ValueId::new(1)));
        let mut function = Function::new(FuncId::new(3), "f", FuncTyId::new(0), BlockId::new(0));
        function.blocks = vec![block];
        assert_eq!(callee_edges(&function), vec![FuncId::new(11), FuncId::new(12)]);
    }

    /// A call-free body reports no edges — the property that makes the
    /// in-compiler seam's placeholder id sound today.
    #[test]
    fn a_call_free_body_reports_no_edges() {
        let mut block = Block::new(BlockId::new(0));
        block.body.push(InstrNode {
            inst: Inst::Const { ty: Ty::U8, value: Constant::Int(7) },
            results: vec![ValueId::new(0)],
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        });
        block.body.push(ret_node(ValueId::new(0)));
        let mut function = Function::new(FuncId::new(0), "k", FuncTyId::new(0), BlockId::new(0));
        function.blocks = vec![block];
        assert!(callee_edges(&function).is_empty());
    }

    /// THE WITNESS for `ShapeMayNotCarryNat`, driven at the emitter's own
    /// boundary rather than through a plan.
    ///
    /// `emit_planned_function` is the layer under test and `CleanOriginShape` is
    /// a public CLOSED enum, so a shape and a signature can be paired here
    /// directly -- which is exactly what a sealed [`CleanOriginPlan`] cannot do
    /// (`plan_clean_origin_body` refuses a bignum carrier for every computing
    /// shape: `recognise_wrapping_expr`'s result-carrier gate, then
    /// `check_arith_signature`'s "EVERY signature position -- used or not"
    /// clause; `tests/nat_carrier_shape_scope.rs` pins both).
    ///
    /// That gap is the whole reason this test exists at this level. Before the
    /// refusal landed, this exact call EMITTED, silently:
    ///
    /// ```text
    /// BinOp { op: Add, ty: Handle(("Nat", "trust_bignum::Nat")), lhs: v0, rhs: v1 }
    /// Return { values: [v2] }
    /// ```
    ///
    /// -- machine arithmetic on an opaque runtime pointer at the pinned
    /// carrier, and a well-typed 64-bit WRAP of an unbounded `Nat` at the
    /// substitute carrier. Both carriers are measured, because only the first
    /// of them fails closed downstream.
    #[test]
    fn a_computing_shape_is_refused_at_the_runtime_nat_carrier() {
        let signature = nat_test_signature();
        // Every shape `shape_that_may_not_carry_nat` names, spelled with the
        // cheapest well-formed payload -- the refusal precedes every arm, so
        // the payload never has to be meaningful.
        let shapes: Vec<(CleanOriginShape, &'static str)> = vec![
            (CleanOriginShape::ConstantUint { value: 1 }, "ConstantUint"),
            (
                CleanOriginShape::WrappingBinOp {
                    op: ArithBinOp::Add,
                    left: ArithOperand::Param(0),
                    right: ArithOperand::Param(1),
                },
                "WrappingBinOp",
            ),
            (
                CleanOriginShape::Composed {
                    expr: ArithExpr::Bin {
                        op: ArithBinOp::Add,
                        left: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
                        right: Box::new(ArithExpr::Operand(ArithOperand::Param(1))),
                    },
                },
                "Composed",
            ),
            (
                CleanOriginShape::Select {
                    cmp: SelectCmp::Lt,
                    cmp_left: 0,
                    cmp_right: 1,
                    then_param: 0,
                    else_param: 1,
                },
                "Select",
            ),
            (
                CleanOriginShape::UnsignedConditional {
                    expr: UIntConditional::Operand(ArithOperand::Param(0)),
                },
                "UnsignedConditional",
            ),
            (
                CleanOriginShape::DecideComparison {
                    cmp: SelectCmp::Lt,
                    cmp_left: 0,
                    cmp_right: 1,
                },
                "DecideComparison",
            ),
            (CleanOriginShape::BoolNot { param: 0 }, "BoolNot"),
            (
                CleanOriginShape::BoolExpression {
                    expr: BoolExpr::And(
                        Box::new(BoolExpr::Param(0)),
                        Box::new(BoolExpr::Literal(true)),
                    ),
                },
                "BoolExpression",
            ),
            (
                CleanOriginShape::RawBinOp {
                    op: RawBinOpKind::BitAnd,
                    left: ArithOperand::Param(0),
                    right: ArithOperand::Param(1),
                },
                "RawBinOp",
            ),
        ];

        for carrier in [NatCarrier::PinnedHandle, NatCarrier::ExecutableSubstitute(Ty::U64)] {
            for (shape, name) in &shapes {
                let error = emit_planned_function(
                    "natCompute",
                    &signature,
                    shape,
                    FuncId::new(0),
                    FuncTyId::new(0),
                    Some(nat_test_runtime(carrier.clone())),
                )
                .expect_err("a computing shape must not take the runtime `Nat` carrier");
                match error {
                    CleanIrRefusal::ShapeMayNotCarryNat { shape, position } => {
                        assert_eq!(shape, *name, "the refusal must name the shape it refused");
                        assert_eq!(position, Some(0), "and the position carried at `Nat`");
                    }
                    other => panic!("{name} at {carrier:?} must be refused BY NAME, got {other}"),
                }
            }
        }
    }

    /// The other half of the same decision: the shapes that MAY carry it still
    /// do, at the same signature and the same runtime.
    ///
    /// Without this, the refusal above could be satisfied by refusing every
    /// `Nat` carrier -- which would delete the recursion lane this crate exists
    /// to emit, and the projection transport `tests/nat_carrier_shape_scope.rs`
    /// measures end to end.
    #[test]
    fn transport_and_the_recursion_shapes_still_take_the_nat_carrier() {
        let signature = nat_test_signature();
        let function = emit_planned_function(
            "natSecond",
            &signature,
            &CleanOriginShape::Projection { projected: 1 },
            FuncId::new(0),
            FuncTyId::new(0),
            Some(nat_test_runtime(NatCarrier::PinnedHandle)),
        )
        .expect("a projection only transports its carrier");
        assert_eq!(function.blocks[0].body.len(), 1, "transport is one `Return`");
        assert!(matches!(&function.blocks[0].body[0].inst, Inst::Return { .. }));

        // The recursion shapes reach their own arms rather than this refusal.
        // `StructuralNatRec` at arity 2 fails LATER, on its own terms
        // (`emit_nat_recursion` admits arity 1 only) -- which is the point: the
        // carrier question is settled, the shape's own preconditions are not.
        let error = emit_planned_function(
            "natRec",
            &signature,
            &CleanOriginShape::StructuralNatRec {
                base: RecBodyExpr::NatConst(0),
                step: RecBodyExpr::Rec,
                rec_arg: RecBodyExpr::Pred,
            },
            FuncId::new(0),
            FuncTyId::new(0),
            Some(nat_test_runtime(NatCarrier::PinnedHandle)),
        )
        .expect_err("arity 2 is outside this producer's recursion fragment");
        assert!(
            !matches!(error, CleanIrRefusal::ShapeMayNotCarryNat { .. }),
            "a recursion shape must never be refused the carrier it was built for: {error}",
        );
    }

    /// `Nat -> Nat -> Nat`, the real thing: `carrier_signature_for` is the only
    /// producer of a [`CarrierSignature`], so the carrier pairing under test is
    /// the one the compiler would grant, not one assembled for the test.
    fn nat_test_signature() -> CarrierSignature {
        let nat = || clean_kernel::Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
        let signature = trust_clean_carrier::carrier_signature_for(&clean_kernel::Expr::arrow(
            nat(),
            clean_kernel::Expr::arrow(nat(), nat()),
        ))
        .expect("`Nat` carries at the Trust-owned bignum in every position");
        assert_eq!(signature.arity(), 2);
        for position in 0..2 {
            assert_eq!(signature.arguments()[position].clean(), CleanType::Nat);
        }
        signature
    }

    fn nat_test_runtime(carrier: NatCarrier) -> NatRuntime {
        NatRuntime {
            carrier,
            from_u64: FuncId::new(10),
            add: FuncId::new(11),
            sub: FuncId::new(12),
            is_zero: FuncId::new(13),
            release: None,
            self_id: FuncId::new(0),
        }
    }

    /// The refusal the placeholder-id guard raises has to say what to do, and
    /// specifically has to name the missing seam — a reader who only learns
    /// "refused" will reach for the wrong fix (widening the emitter) instead of
    /// the right one (a callee remap on the append path).
    #[test]
    fn the_placeholder_id_refusal_names_the_missing_seam() {
        let text = CleanIrRefusal::CallEdgeWithoutOwningModuleIdentity { callee: 11 }.to_string();
        assert!(text.contains("Options:"), "{text}");
        assert!(text.contains("callee-remap"), "must name the missing seam: {text}");
        assert!(
            text.contains("emit_clean_origin_function_with_nat"),
            "must name the entry that CAN spell it: {text}"
        );
    }
}

#[cfg(test)]
mod rust_call_tests {
    use trust_certify::clean_island::{CleanIslandSession, RustCallee};
    use trust_ir::Module;
    use trust_ir::inst::CastOp;
    use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};

    use super::*;

    fn plan(source: &str, name: &str, declared: &[RustCallee]) -> CleanOriginPlan {
        let mut session = CleanIslandSession::new();
        session.declare_rust_callees(declared).expect("callee declarations");
        let batch = session.check_all(&[source]);
        assert!(!batch.is_rejected(), "source must kernel-check: {batch:?}");
        let roster = declared
            .iter()
            .enumerate()
            .map(|(index, callee)| RustCalleeRef {
                clean_name: callee.clean_name.clone(),
                // Test-only source renderings; actual compiler identity is the join's job.
                def_path: format!("DefId(0:{} ~ test[0123]::{})", index + 1, callee.clean_name),
                params: callee.params.clone(),
                result: callee.result.clone(),
            })
            .collect::<Vec<_>>();
        trust_clean_origin::plan_clean_origin_body_with_rust_callees(
            session.environment().expect("kernel environment"),
            name,
            &roster,
        )
        .expect("sealed call plan")
    }

    fn targets(plan: &CleanOriginPlan) -> Vec<RustCalleeTarget> {
        let CleanOriginShape::RustCallChain { nodes } = plan.shape() else { panic!("call chain") };
        let mut used = nodes.iter().map(|node| node.callee).collect::<Vec<_>>();
        used.sort_unstable();
        used.dedup();
        used.into_iter()
            .enumerate()
            .map(|(id, plan_index)| RustCalleeTarget {
                plan_index,
                id: FuncId::new(id as u32),
                signature: rust_callee_func_ty(&plan.callees()[plan_index])
                    .expect("callee carriers"),
            })
            .collect()
    }

    fn ir_node(inst: Inst, result: Option<u32>) -> InstrNode {
        InstrNode {
            inst,
            results: result.map(ValueId::new).into_iter().collect(),
            proofs: Vec::new(),
            span: None,
            proof_context: None,
            scope: None,
        }
    }

    fn add_callee(
        module: &mut Module,
        target: &RustCalleeTarget,
        name: &str,
        body: Vec<InstrNode>,
    ) {
        let ty = module
            .add_func_type(target.signature.clone())
            .expect("Module::add_func_type: test fixture");
        let mut block = Block::new(BlockId::new(0));
        for (index, ty) in target.signature.params.iter().enumerate() {
            block = block.with_param(ValueId::new(index as u32), ty.clone());
        }
        block.body = body;
        let mut function = Function::new(target.id, name, ty, BlockId::new(0));
        function.calling_conv = CallingConv::Rust;
        function.blocks.push(block);
        module.try_add_function(function).expect("Module::try_add_function: test fixture");
    }

    fn append(module: &mut Module, plan: &CleanOriginPlan, targets: &[RustCalleeTarget]) -> FuncId {
        let id = FuncId::new(module.functions.len() as u32);
        let ty = module
            .add_func_type(trust_ir_func_ty(plan.signature()).expect("caller type"))
            .expect("Module::add_func_type: test fixture");
        for target in targets {
            let found = module
                .functions
                .iter()
                .filter(|function| function.id == target.id)
                .collect::<Vec<_>>();
            assert_eq!(found.len(), 1, "actual module callee must be unique");
            assert_eq!(found[0].calling_conv, CallingConv::Rust);
            assert_eq!(module.func_types[found[0].ty.index() as usize], target.signature);
        }
        let function =
            emit_clean_origin_rust_call_function(plan, id, ty, targets).expect("emission");
        assert!(function.attrs.is_empty());
        assert!(function.summary.is_none() && function.proofs.is_empty());
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| &block.body)
                .all(|node| node.proofs.is_empty() && node.proof_context.is_none())
        );
        module.try_add_function(function).expect("Module::try_add_function: test fixture");
        id
    }

    fn scalar(ty: Ty, value: i128) -> InterpretValue {
        InterpretValue::int(ty, value).expect("integer carrier")
    }

    fn seven_plan() -> CleanOriginPlan {
        plan(
            "def getSeven : UInt64 := seven",
            "getSeven",
            &[RustCallee {
                clean_name: "seven".into(),
                params: vec![],
                result: trust_types::Ty::u64(),
            }],
        )
    }

    fn seven_module() -> (Module, FuncId) {
        let plan = seven_plan();
        let targets = targets(&plan);
        let mut module = Module::new("module_owned_seven");
        add_callee(
            &mut module,
            &targets[0],
            "rust_seven",
            vec![
                ir_node(Inst::Const { ty: Ty::U64, value: Constant::Int(7) }, Some(0)),
                ret_node(ValueId::new(0)),
            ],
        );
        let caller = append(&mut module, &plan, &targets);
        (module, caller)
    }

    #[test]
    fn module_owned_nullary_call_executes_actual_callee_and_missing_target_fails() {
        let (mut module, caller) = seven_module();
        let result =
            Interpreter::with_module(&module).execute_func(caller, vec![]).expect("module call");
        assert_eq!(result.returns, vec![scalar(Ty::U64, 7)]);
        assert_eq!(callee_edges(&module.functions[1]), vec![FuncId::new(0)]);
        assert!(module.functions[1].blocks[0].body[0].inst.has_observable_effects());
        // An emitter descriptor alone cannot establish module membership. The
        // owning join must refuse this mutation before publishing a module.
        module.functions.remove(0);
        let error = Interpreter::with_module(&module).execute_func(caller, vec![]).unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::MissingFunction);
    }

    #[test]
    fn rust_call_keeps_callee_panic_and_never_claims_nopanic() {
        let (mut module, caller) = seven_module();
        module.functions[0].blocks[0].body = vec![
            ir_node(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) }, Some(0)),
            ir_node(
                Inst::Assert {
                    cond: ValueId::new(0),
                    kind: trust_ir::AssertKind::Unspecified,
                    site: None,
                },
                None,
            ),
            ir_node(Inst::Const { ty: Ty::U64, value: Constant::Int(7) }, Some(1)),
            ret_node(ValueId::new(1)),
        ];
        let error = Interpreter::with_module(&module).execute_func(caller, vec![]).unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::Panic);
        assert!(
            !module.functions[1].blocks[0]
                .body
                .iter()
                .any(|node| matches!(node.inst, Inst::Invoke { .. }))
        );
    }

    #[test]
    fn placeholder_entry_still_refuses_rust_call_chain() {
        assert!(matches!(
            emit_clean_origin_function(&seven_plan(), FuncId::new(0), FuncTyId::new(0)),
            Err(CleanIrRefusal::ShapeNotYetSpelled { shape: "RustCallChain" })
        ));
    }

    #[test]
    fn full_postorder_chain_keeps_each_call_and_argument_order() {
        let plan = plan(
            "def difference (x y : UInt64) : UInt64 := sub (sub x 1) (sub y 2)",
            "difference",
            &[RustCallee {
                clean_name: "sub".into(),
                params: vec![trust_types::Ty::u64(), trust_types::Ty::u64()],
                result: trust_types::Ty::u64(),
            }],
        );
        let targets = targets(&plan);
        let mut module = Module::new("postorder_calls");
        add_callee(
            &mut module,
            &targets[0],
            "rust_sub",
            vec![
                ir_node(
                    Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::U64,
                        lhs: ValueId::new(0),
                        rhs: ValueId::new(1),
                    },
                    Some(2),
                ),
                ret_node(ValueId::new(2)),
            ],
        );
        let caller = append(&mut module, &plan, &targets);
        let function = &module.functions[1];
        let calls = function.blocks[0]
            .body
            .iter()
            .filter(|node| matches!(node.inst, Inst::Call { .. }))
            .collect::<Vec<_>>();
        assert_eq!(calls.len(), 3);
        let Inst::Call { args: left_args, .. } = &calls[0].inst else { unreachable!() };
        let Inst::Call { args: right_args, .. } = &calls[1].inst else { unreachable!() };
        assert_eq!(left_args[0], ValueId::new(0), "left subtree executes first");
        assert_eq!(right_args[0], ValueId::new(1), "right subtree executes second");
        assert!(calls.iter().all(|node| node.inst.has_observable_effects()));
        assert_eq!(
            calls[2].inst,
            Inst::Call {
                callee: targets[0].id,
                args: vec![calls[0].results[0], calls[1].results[0]]
            }
        );
        assert_ne!(calls[0].results, calls[1].results);
        let result = Interpreter::with_module(&module)
            .execute_func(caller, vec![scalar(Ty::U64, 10), scalar(Ty::U64, 3)])
            .expect("nested calls");
        assert_eq!(result.returns, vec![scalar(Ty::U64, 8)]);
    }

    fn mixed_plan(literals: bool) -> CleanOriginPlan {
        let source = if literals {
            "def mixed (x : UInt8) : UInt64 := choose true (7 : UInt16) (widen x)"
        } else {
            "def mixed (x : UInt8) (y : UInt16) (b : Bool) : UInt64 := choose b y (widen x)"
        };
        plan(
            source,
            "mixed",
            &[
                RustCallee {
                    clean_name: "unused".into(),
                    params: vec![],
                    result: trust_types::Ty::Bool,
                },
                RustCallee {
                    clean_name: "widen".into(),
                    params: vec![trust_types::Ty::Int { width: 8, signed: false }],
                    result: trust_types::Ty::u64(),
                },
                RustCallee {
                    clean_name: "choose".into(),
                    params: vec![
                        trust_types::Ty::Bool,
                        trust_types::Ty::Int { width: 16, signed: false },
                        trust_types::Ty::u64(),
                    ],
                    result: trust_types::Ty::u64(),
                },
            ],
        )
    }

    #[test]
    fn mixed_carriers_and_literals_use_actual_module_types() {
        for literals in [false, true] {
            let plan = mixed_plan(literals);
            let mut targets = targets(&plan);
            assert_eq!(
                targets.iter().map(|target| target.plan_index).collect::<Vec<_>>(),
                vec![1, 2]
            );
            let mut module = Module::new("mixed_call_carriers");
            add_callee(
                &mut module,
                &targets[0],
                "rust_widen",
                vec![
                    ir_node(
                        Inst::Cast {
                            op: CastOp::ZExt,
                            src_ty: Ty::U8,
                            dst_ty: Ty::U64,
                            operand: ValueId::new(0),
                        },
                        Some(1),
                    ),
                    ret_node(ValueId::new(1)),
                ],
            );
            add_callee(
                &mut module,
                &targets[1],
                "rust_choose",
                vec![
                    ir_node(
                        Inst::Cast {
                            op: CastOp::ZExt,
                            src_ty: Ty::U16,
                            dst_ty: Ty::U64,
                            operand: ValueId::new(1),
                        },
                        Some(3),
                    ),
                    ir_node(
                        Inst::Select {
                            ty: Ty::U64,
                            cond: ValueId::new(0),
                            then_val: ValueId::new(3),
                            else_val: ValueId::new(2),
                        },
                        Some(4),
                    ),
                    ret_node(ValueId::new(4)),
                ],
            );
            targets.reverse(); // Bindings are keyed by plan index, not slice position.
            let caller = append(&mut module, &plan, &targets);
            let inputs = if literals {
                vec![scalar(Ty::U8, 42)]
            } else {
                vec![scalar(Ty::U8, 42), scalar(Ty::U16, 11), InterpretValue::bool(false)]
            };
            let result = Interpreter::with_module(&module)
                .execute_func(caller, inputs)
                .expect("mixed carriers");
            assert_eq!(result.returns, vec![scalar(Ty::U64, if literals { 7 } else { 42 })]);
        }
    }

    #[test]
    fn rust_callee_conversion_covers_supported_widths_and_refuses_other_carriers() {
        for (rust, expected) in [
            (trust_types::Ty::Bool, Ty::Bool),
            (trust_types::Ty::Int { width: 8, signed: false }, Ty::U8),
            (trust_types::Ty::Int { width: 16, signed: false }, Ty::U16),
            (trust_types::Ty::Int { width: 32, signed: false }, Ty::U32),
            (trust_types::Ty::Int { width: 64, signed: false }, Ty::U64),
        ] {
            let callee = RustCalleeRef {
                clean_name: "same".into(),
                def_path: "test".into(),
                params: vec![rust.clone()],
                result: rust,
            };
            assert_eq!(
                rust_callee_func_ty(&callee).unwrap(),
                FuncTy {
                    params: vec![expected.clone()],
                    returns: vec![expected],
                    is_vararg: false,
                    abi: None,
                }
            );
        }
        for rust in [
            trust_types::Ty::Int { width: 64, signed: true },
            trust_types::Ty::Int { width: 128, signed: false },
        ] {
            let callee = RustCalleeRef {
                clean_name: "unsupported".into(),
                def_path: "test".into(),
                params: vec![],
                result: rust,
            };
            assert!(rust_callee_func_ty(&callee).is_err());
        }
    }

    #[test]
    fn module_binding_skews_fail_closed() {
        let plan = mixed_plan(false);
        let valid = targets(&plan);
        let mut cases = vec![
            vec![],
            vec![valid[0].clone()],
            vec![valid[0].clone(), valid[0].clone(), valid[1].clone()],
        ];
        let mut skew = valid.clone();
        skew[0].id = FuncId::new(7);
        cases.push(skew);
        let mut skew = valid.clone();
        skew[1].id = skew[0].id;
        cases.push(skew);
        let mut skew = valid.clone();
        skew[0].signature.is_vararg = true;
        cases.push(skew);
        let mut skew = valid.clone();
        skew[0].signature.returns = vec![Ty::Bool];
        cases.push(skew);
        let mut skew = valid.clone();
        skew[0].signature.params = vec![Ty::U64];
        cases.push(skew);
        let mut skew = valid.clone();
        skew[0].plan_index = 99;
        cases.push(skew);
        let mut skew = valid.clone();
        skew.push(RustCalleeTarget {
            plan_index: 0,
            id: FuncId::new(8),
            signature: rust_callee_func_ty(&plan.callees()[0]).unwrap(),
        });
        cases.push(skew);
        for (index, targets) in cases.iter().enumerate() {
            assert!(
                emit_clean_origin_rust_call_function(
                    &plan,
                    FuncId::new(7),
                    FuncTyId::new(0),
                    targets
                )
                .is_err(),
                "accepted binding mutant {index}"
            );
        }
    }

    #[test]
    fn duplicated_or_dropped_call_results_do_not_change_the_sealed_tree() {
        let plan = plan(
            "def difference (x : UInt64) : UInt64 := sub (sub x 1) (sub x 2)",
            "difference",
            &[RustCallee {
                clean_name: "sub".into(),
                params: vec![trust_types::Ty::u64(), trust_types::Ty::u64()],
                result: trust_types::Ty::u64(),
            }],
        );
        let targets = targets(&plan);
        let CleanOriginShape::RustCallChain { nodes } = plan.shape() else { panic!("call chain") };
        let mut duplicate = nodes.clone();
        duplicate[2].args[1] = RustCallArg::Node(0);
        assert!(
            emit_rust_call_chain(
                "test",
                plan.signature(),
                &duplicate,
                plan.callees(),
                FuncId::new(7),
                FuncTyId::new(0),
                &targets
            )
            .is_err()
        );
    }

    #[test]
    fn malformed_nodes_and_missing_source_identity_fail_closed() {
        let plan = mixed_plan(false);
        let targets = targets(&plan);
        let CleanOriginShape::RustCallChain { nodes } = plan.shape() else { panic!("call chain") };
        let emit = |nodes: &[RustCallNode], roster: &[RustCalleeRef]| {
            emit_rust_call_chain(
                "test",
                plan.signature(),
                nodes,
                roster,
                FuncId::new(7),
                FuncTyId::new(0),
                &targets,
            )
        };
        assert!(emit(&[], plan.callees()).is_err());
        let mut forward = nodes.clone();
        forward[0].args[0] = RustCallArg::Node(0);
        assert!(emit(&forward, plan.callees()).is_err());
        let mut parameter = nodes.clone();
        parameter[0].args[0] = RustCallArg::Param(99);
        assert!(emit(&parameter, plan.callees()).is_err());
        let mut wrong_type = nodes.clone();
        wrong_type[0].args[0] = RustCallArg::Param(1);
        assert!(emit(&wrong_type, plan.callees()).is_err());
        let mut arity = nodes.clone();
        arity[0].args.clear();
        assert!(emit(&arity, plan.callees()).is_err());
        let mut identity = plan.callees().to_vec();
        identity[1].def_path.clear();
        assert!(emit(nodes, &identity).is_err());
        let mut result_roster = plan.callees().to_vec();
        result_roster[2].result = trust_types::Ty::Bool;
        let mut result_targets = targets.clone();
        result_targets[1].signature.returns = vec![Ty::Bool];
        assert!(
            emit_rust_call_chain(
                "test",
                plan.signature(),
                nodes,
                &result_roster,
                FuncId::new(7),
                FuncTyId::new(0),
                &result_targets
            )
            .is_err()
        );
        let mut dropped = nodes.clone();
        dropped[1].args[2] = RustCallArg::Literal(RustCallLiteral::UInt(1));
        assert!(emit(&dropped, plan.callees()).is_err());
        let mut numeral = nodes.clone();
        numeral[0].args[0] = RustCallArg::Literal(RustCallLiteral::UInt(256));
        assert!(matches!(
            emit(&numeral, plan.callees()),
            Err(CleanIrRefusal::ConstantOutOfRange { width: 8, .. })
        ));
        let mut boolean = nodes.clone();
        boolean[0].args[0] = RustCallArg::Literal(RustCallLiteral::Bool(true));
        assert!(emit(&boolean, plan.callees()).is_err());
    }
}
