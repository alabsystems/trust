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
//! * Same-crate Rust→Clean call edges whose canonical def path and arity match
//!   are re-pointed to the admitted Clean Function and certified for remap
//!   shape. That is the landed IR-5 same-crate join witnessed by runmake; it is
//!   still not G5 digest-bound cross-crate linking.
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
//! **All thirteen are checked by EXECUTION against the CIC kernel**, but the
//! two groups are not checked over the same domain, and the difference matters.
//!
//! * the eleven straight-line shapes run over the WHOLE domain of their carrier
//!   at `u8` and `u16` — exhaustive, including a 65 536-pair sweep.
//! * the two recursion shapes run over a small range of inputs against a
//!   one-limb model of `Nat` supplied by the test. `trust_ir::interpret` cannot
//!   execute a call to a bodyless declaration (`MissingBlock`) and has no
//!   host-call hook, so the runtime is given TrustIR bodies in the test. That is
//!   possible without weakening the emitter because [`NatRuntime::nat_ty`] lets
//!   the CALLER choose the carrier: production passes [`Ty::Ptr`], an opaque
//!   handle claiming no width, and the emitter never learns a width either way.
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

use trust_clean_carrier::{CarrierSignature, CleanType};
use trust_clean_origin::emit::{CleanOriginPlan, CleanOriginShape};
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, CallingConv, Constant, Function};
use trust_types::admissible_body::{
    ArithBinOp, ArithExpr, ArithOperand, BeqOperand, RawBinOpKind, RecBodyExpr, SelectCmp,
};

/// The TrustIR identities of the bignum `Nat` runtime the recursion shapes call.
///
/// Clean's `Nat` is UNBOUNDED. TrustIR has no `Nat` type, so a faithful emission
/// cannot pick a machine width — it carries the value as an opaque handle
/// ([`Ty::Ptr`]) and calls the same runtime the MIR lane calls. That keeps the
/// arithmetic exactly where Clean's semantics live instead of re-implementing it
/// at a width that would wrap.
///
/// The caller supplies the ids because function identity belongs to the owning
/// [`trust_ir::Module`], not to this producer: minting them here would let two
/// independently emitted modules disagree about which `FuncId` is `Nat::add`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NatRuntime {
    /// The TrustIR type a `Nat` VALUE is carried at.
    ///
    /// Production passes [`Ty::Ptr`]: an opaque handle, which is what a heap
    /// bignum actually is and which claims no width. It is a parameter rather
    /// than hardcoded so a CALLER can substitute a carrier its own runtime
    /// bodies can compute on — which is what lets the emitted recursion be
    /// EXECUTED and checked against the kernel, instead of only inspected.
    ///
    /// This never lets the emitter pick a machine width on its own. Whatever is
    /// passed here, the arithmetic still happens in the named runtime functions;
    /// the emitter contributes the control flow and nothing else.
    pub nat_ty: Ty,
    /// `trust_bignum::Nat::from_u64` — materialize a literal.
    pub from_u64: FuncId,
    /// `trust_bignum::Nat::add`.
    pub add: FuncId,
    /// `trust_bignum::Nat::sub` — Lean's TRUNCATED subtraction, which IS the
    /// predecessor at subtrahend 1 on every input, `Nat.pred 0 = 0` included.
    pub sub: FuncId,
    /// A zero test on a `Nat` handle, returning [`Ty::Bool`].
    pub is_zero: FuncId,
    /// The function being emitted, for the self-call.
    pub self_id: FuncId,
}

/// Why a plan could not be spelled in TrustIR.
///
/// Every variant names the construct and what to do about it. "Unsupported"
/// with no next step is a defect (v7/D3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CleanIrRefusal {
    /// A carrier in the signature has no TrustIR type. Unbounded and
    /// target-dependent Clean types are the cases: `Nat`/`Int` have no
    /// fixed-width carrier at any width, and `USize` is bounded by
    /// `System.Platform.numBits`, which the carrier crate deliberately does not
    /// resolve.
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
                    "Clean type {clean:?} at {where_} has no TrustIR type. TrustIR carries \
                     fixed-width machine integers and `bool`; `Nat` and `Int` are unbounded and \
                     `USize` is target-dependent. Options: give the declaration a machine-width \
                     type (`UInt8`/`UInt16`/`UInt32`/`UInt64`, `BitVec w`, or `Bool`), or keep \
                     this declaration proof-only so no value is produced for it."
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
        }
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
        // there IS a faithful spelling when a runtime owns the arithmetic: an
        // opaque handle. `Ty::Ptr` carries the value without claiming a width,
        // which is exactly what the bignum runtime hands around. Admitted ONLY
        // when the caller named that runtime; otherwise a `Ptr` here would be a
        // value nothing can operate on.
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
    Ok(FuncTy { params, returns, is_vararg: false })
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
    emit_clean_origin_function_with_nat(plan, id, ty, None)
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
    let signature = plan.signature();
    let func_ty = trust_ir_func_ty_with_nat(signature, nat.as_ref().map(|n| &n.nat_ty))?;

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

    match plan.shape() {
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
            let measure = rec_args.get(*measure_index).ok_or(
                CleanIrRefusal::RecursionArgIsNotPred { shape: "WellFoundedNatRec" },
            )?;
            check_rec_arg(measure, "WellFoundedNatRec")?;
            emit_nat_recursion(&mut block, &mut blocks, arity, nat, zero_value, nonzero_value)?;
        }
    }

    // `Function::new` rather than a struct literal: `Function` carries a dozen
    // fields whose defaults are the IR's business (linkage, calling convention,
    // attrs, provenance carriers), and a literal here would silently pin them
    // the day one is added.
    let mut function = Function::new(id, plan.name(), ty, entry);
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

/// A source parameter as a value, bounds-checked against the signature.
fn param_value(index: usize, arity: usize) -> Result<ValueId, CleanIrRefusal> {
    if index >= arity {
        return Err(CleanIrRefusal::ProjectionOutOfRange { projected: index, arity });
    }
    Ok(ValueId::new(index as u32))
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

/// Emit the zero-test / predecessor / self-call contract.
///
/// The same shape the MIR lane emits, in TrustIR's idiom:
///
/// ```text
///   bb0:  z = is_zero(n);  cond_br z -> bb1, bb2
///   bb1:  <zero arm>;      return
///   bb2:  p = sub(n, 1);   r = self(p);  <nonzero arm using r>;  return
/// ```
///
/// A branch rather than the branchless `Select` the comparison shapes use, and
/// that is NOT a style choice: `Select` evaluates BOTH arms, and the nonzero arm
/// contains the self-call. A branchless spelling would recurse unconditionally
/// and never terminate.
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

    // ── the zero arm: no `Rec`, no `Pred` (the plan guarantees it) ──────────
    let mut zero = Block::new(zero_block);
    let zero_value = emit_rec_body(zero_arm, &mut zero, &mut next, nat, n, None)?;
    zero.body.push(ret_node(zero_value));

    // ── the nonzero arm: predecessor, then the self-call ───────────────────
    let mut nonzero = Block::new(nonzero_block);
    // The literal 1, materialized the SAME way `RecBodyExpr::NatConst` does --
    // through `nat_literal`, which passes the value. Open-coding the call here
    // is what let the missing-argument bug exist in two places at once.
    let one = nat_literal(1, nat, &mut nonzero, &mut next);
    let pred = next.take();
    nonzero.body.push(call_node(nat.sub, vec![n, one], pred));
    let rec = next.take();
    nonzero.body.push(call_node(nat.self_id, vec![pred], rec));
    let value = emit_rec_body(nonzero_arm, &mut nonzero, &mut next, nat, n, Some(rec))?;
    nonzero.body.push(ret_node(value));

    blocks.push(zero);
    blocks.push(nonzero);
    Ok(())
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
) -> Result<ValueId, CleanIrRefusal> {
    match expr {
        RecBodyExpr::Decreasing => Ok(decreasing),
        RecBodyExpr::Rec => {
            rec.ok_or(CleanIrRefusal::RecursionArgIsNotPred { shape: "Rec in the zero arm" })
        }
        RecBodyExpr::Pred => {
            let one = nat_literal(1, nat, block, next);
            let p = next.take();
            block.body.push(call_node(nat.sub, vec![decreasing, one], p));
            Ok(p)
        }
        RecBodyExpr::NatConst(k) => Ok(nat_literal(*k, nat, block, next)),
        RecBodyExpr::Add(left, right) => {
            let l = emit_rec_body(left, block, next, nat, decreasing, rec)?;
            let r = emit_rec_body(right, block, next, nat, decreasing, rec)?;
            let out = next.take();
            block.body.push(call_node(nat.add, vec![l, r], out));
            Ok(out)
        }
        // `RecBodyExpr` is a closed five-variant enum today; a new node must be
        // given a spelling here rather than silently becoming one of these.
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
fn nat_literal(value: u64, nat: &NatRuntime, block: &mut Block, next: &mut NextValue) -> ValueId {
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
}
