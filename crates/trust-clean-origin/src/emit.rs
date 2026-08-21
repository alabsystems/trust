// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! I5 decision 2, **applied**: the Clean-origin body plan and the round trip
//! that feeds [`crate::gate::check_faithful`] its side B.
//!
//! # What this module is for
//!
//! [`crate::gate`] is the *decision*: given side A (the Clean `def`'s body) and
//! side B (`R(lowered)`), does the kernel identify them? It has no opinion about
//! where side B comes from, deliberately — that keeps the decision auditable in
//! isolation.
//!
//! This module supplies the two halves around it, and it is the **only** way a
//! [`crate::gate::Faithful`] can be obtained for an *emitted* body:
//!
//! * [`plan_clean_origin_body`] reads a Clean `def` out of the kernel
//!   environment and decides whether the compiler knows how to emit it at all,
//!   returning a [`CleanOriginPlan`] — the total-carrier signature plus the
//!   shape. **A plan is not permission to emit.** It is permission to *attempt*
//!   an emission that will then be checked.
//! * [`admit_lowering`] takes the body the compiler actually produced, already
//!   extracted back out of MIR, routes it through the **pre-existing E6
//!   Rust→Clean path**, and puts the resulting term to the gate.
//!
//! # THE ROUTE, AND WHY IT IS NOT CO-AUTHORED
//!
//! ```text
//! mir::Body  --trust_mir_extract::extract_function-->  VerifiableFunction
//!            --trust_types::recognize_admissible_body-->  AdmissibleBody
//!            --trust_spec_elab::admit_projection_function-->  kernel Expr   (side B)
//!            --crate::gate::check_faithful------------->  Faithful | GateRefusal
//! ```
//!
//! Every step of that chain already existed, and every one of them was written
//! for the OPPOSITE direction — E6 kernel-import, which reflects a Rust `fn`
//! into Clean so a contract can name it. None of it was written to make a
//! Clean-origin body pass. That is the whole reason the comparison means
//! something: side A comes from the Clean parser and elaborator, side B comes
//! from the MIR the backend will actually codegen, and the two producers do not
//! know about each other.
//!
//! The corollary is a standing prohibition, the same one that freezes
//! `crates/trust-clean/src/reflect.rs`: **if a Clean-origin body fails this
//! gate, the fix is never to edit `recognize_admissible_body` or
//! `admit_*_function`.** Those are side B's producers. Editing them to make
//! side B agree with side A converts the gate into a round trip.
//!
//! # Why the round trip goes through MIR rather than short-circuiting
//!
//! The obvious "optimisation" is to skip the emission and compare the plan
//! against side A directly — the plan was derived from side A, so it would
//! always agree. That is exactly the failure mode: it would check that the
//! compiler read the Clean term correctly and say nothing about what it
//! EMITTED. The gate's subject is the emitted body, so the emitted body is what
//! must be re-read. `tests/control_3_clean_origin_emitter_mutation.rs` mutates
//! the emitted body — not the plan — and requires a refusal.
//!
//! # The fragment, stated as a measurement
//!
//! Today: **`Projection`** (`fun x0 … x_{n-1} => x_i` over fixed-width
//! carriers), **`WrappingBinOp`** (a single wrapping `+`/`-`/`*` over
//! parameters and in-range numerals, with EVERY signature position at one
//! unsigned machine width), and **`Composed`** (a nested tree of those same
//! ops at that same one width, `2..=COMPOSED_MAX_OPS` nodes). All are what
//! the kernel demonstrably admits: the probe corpus
//! (`tests/e6-fragment-probe/`) runs this same comparison in the opposite
//! direction and records `Projection` as discharging (d01–d05, d08, d09) and
//! the composed chain discharging end-to-end (f21), and
//! `tests/fragment_widening_probes.rs` measured the single-op arithmetic
//! ADMITs in both side-A spellings — including numeral operands (probes
//! a4–a6, 2026-08-19) — and the nested `(a + b) * a` ADMIT (probe_f) before
//! the respective emitter arms existed. **Every** `ConstantUint` probe
//! remains `defeq-rejected` or `unproved` on the compiler lane (f04,
//! f06–f09): the shape that looks simplest is still one the pipeline refuses.
//!
//! Per ruling v7/D2 that is a statement of where we are, never a design. The
//! way to widen it is to make the two sides agree at the kernel — extending the
//! COMPILER — never to relax the gate.

use clean_kernel::{
    ConstantKind, DeclarationVerification, Environment, Expr, ExprKind, Level, Literal, Name,
};
use trust_clean_carrier::{
    Carrier, CarrierRefused, CarrierSignature, CleanType, carrier_signature_for,
};
use trust_spec_elab::{Domain, MachineUIntWidth};
use trust_types::admissible_body::{
    AdmissibleBody, ArithBinOp, ArithExpr, ArithOperand, SelectCmp, recognize_admissible_body,
};
use trust_types::{Ty, VerifiableFunction};

use crate::gate::{Faithful, GateRefusal, check_faithful};

/// The body shapes the compiler knows how to originate from a Clean `def`.
///
/// Deliberately a closed enum. A widening is a new variant plus its own
/// emitter arm plus its own round-trip arm — never a fall-through.
///
/// # Deliberately NOT `#[non_exhaustive]`
///
/// Every other public type in this crate is, because their consumers should
/// fail closed on a variant they do not know. This one is the opposite: its
/// consumer is `rustc_mir_transform`'s emitter, and a variant the emitter does
/// not know must be a COMPILE ERROR there, not a runtime fall-through.
/// `#[non_exhaustive]` would force that emitter to carry a `_ =>` arm, and a
/// `_ =>` arm on the enum that decides what MIR gets emitted is exactly the
/// place a future shape would silently acquire the wrong body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CleanOriginShape {
    /// `fun x0 … x_{n-1} => x_i` — return the `projected`-th **source**
    /// parameter verbatim. The MIR is one block: `_0 = move _{projected+1};
    /// return`.
    Projection {
        /// The 0-based *source* parameter position returned. Not the de Bruijn
        /// index: under `n` binders, source parameter `i` is `BVar(n-1-i)`, and
        /// getting that inversion backwards is precisely the one-construct
        /// mistranslation this lane can make.
        projected: usize,
    },
    /// A single wrapping binary op over two operands, each a source parameter
    /// or an in-range numeral, at ONE unsigned machine width shared by every
    /// signature position — used or not, because the reflected side B
    /// (`admit_expr_function`) is single-domain over ALL parameters. The MIR:
    /// `bb0: _0 = Call(u{w}::wrapping_{op}, [l, r]) -> bb1: Return`.
    ///
    /// `ArithBinOp`/`ArithOperand` are REUSED from
    /// `trust_types::admissible_body`, not redefined — a vocabulary reuse, not
    /// a producer edit: the values here come from the Clean term, the values
    /// on the recognizer side come from the emitted MIR, and the structural
    /// comparison in [`admit_lowering`] is then direct equality. Width is
    /// deliberately NOT a field — it is derived from the plan's
    /// [`CarrierSignature`], so there is no second place a width can disagree.
    WrappingBinOp {
        /// The operation (`wrapping_add`/`wrapping_sub`/`wrapping_mul`).
        op: ArithBinOp,
        /// Left operand: 0-based source parameter or in-range literal.
        left: ArithOperand,
        /// Right operand: 0-based source parameter or in-range literal.
        right: ArithOperand,
    },
    /// A NESTED composition of wrapping `+`/`-`/`*` — at least two op nodes —
    /// over source parameters and in-range numerals, every signature position
    /// at ONE unsigned machine width (`fun a b => (a + b) * a`). The MIR is
    /// the linear call chain `recognize_call_chain` was written for: one
    /// authenticated `u{w}::wrapping_{op}` `Call` per tree node in POST-ORDER
    /// through fresh temporaries, the root writing `_0`, then `Return`.
    ///
    /// The vocabulary is `trust_types::admissible_body::ArithExpr`, REUSED
    /// for the same reason `WrappingBinOp` reuses `ArithBinOp`/`ArithOperand`
    /// — a vocabulary reuse, not a producer edit: the tree here comes from
    /// the Clean term, the recognizer's from the emitted MIR, and the
    /// structural comparison in [`admit_lowering`] is direct equality. Its
    /// leaves are `Param | Const` and its nodes are binops, so a dangling
    /// intermediate reference is unrepresentable; the invariants the type
    /// cannot carry — node count in `2..=`[`COMPOSED_MAX_OPS`], leaf bounds —
    /// are re-checked on the sealed plan by [`plan_clean_origin_body`]. Width
    /// is derived from the plan's [`CarrierSignature`], exactly as for
    /// `WrappingBinOp`.
    Composed {
        /// The composed expression tree, in the shape the recognizer reports
        /// it. Emission flattens it by post-order traversal.
        expr: ArithExpr,
    },
    /// `fun x0 … x_{n-1} => if xl ⊲ xr then xt else xe` (R2/C5a) — the
    /// parameter-select `ite`, at ONE unsigned machine width across every
    /// signature position (the reflected side B, `admit_select_function`, is
    /// single-domain). All four positions are SOURCE parameters — constant
    /// arms and computed conditions are outside the fragment (e6 probe f03
    /// pins the former). The MIR is the four-block O0 diamond
    /// `recognize_select` was written for, years before this lane.
    ///
    /// `SelectCmp` is REUSED from `trust_types::admissible_body`, same as the
    /// arithmetic vocabulary: plan/recognition agreement stays direct
    /// equality. Kernel ground: `probe_h_select_admits` — check_faithful
    /// ADMITS the reflected diamond against the island `ite`, refuses swapped
    /// arms, and refuses even the Le-for-Lt instance swap (defeq is
    /// intensional on the stuck `ite`).
    Select {
        /// The comparison (`<`, `<=`, `==`); `!=`/`>`/`>=` are outside both
        /// the recognizer and the elaborator, and fail closed at recognition.
        cmp: SelectCmp,
        /// 0-based source parameter on the comparison's left.
        cmp_left: usize,
        /// 0-based source parameter on the comparison's right.
        cmp_right: usize,
        /// Parameter returned when the comparison holds.
        then_param: usize,
        /// Parameter returned otherwise.
        else_param: usize,
    },
}

/// The measured cap on wrapping-op NODES in one [`CleanOriginShape::Composed`]
/// tree.
///
/// Per ruling v7/D2 this is a statement of where we are, never a design: it is
/// the largest chain the reflected rendering was actually put to the kernel at
/// (`tests/fragment_widening_probes.rs` probe_f2 ADMITs a chain of exactly this
/// many ops, in both side-A spellings, and pins the plan-time refusal one past
/// it). Raising it is an edit to the probe first — measure the new depth at
/// the kernel — and to this constant second, never the other way round.
pub const COMPOSED_MAX_OPS: usize = 32;

/// A Clean `def` the compiler may attempt to emit, with the total carrier
/// signature it must be emitted at.
///
/// **Constructible only by [`plan_clean_origin_body`].** The seal matters for
/// the same reason [`crate::mint::MintGrant`]'s does: holding a
/// `CleanOriginPlan` is evidence that the declaration is kernel-checked, has a
/// definition body, and has a TOTAL carrier in **every** position — arguments
/// and result. There is no way to spell "the interesting arguments carry".
#[derive(Debug, Clone)]
pub struct CleanOriginPlan {
    name: String,
    signature: CarrierSignature,
    shape: CleanOriginShape,
}

impl CleanOriginPlan {
    /// The Clean declaration being emitted.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The total carrier signature: one carrier per argument, one for the
    /// result. Its existence is I4's `CarrierEvidence::Total` for the whole
    /// signature.
    #[must_use]
    pub fn signature(&self) -> &CarrierSignature {
        &self.signature
    }

    /// The recognised body shape.
    #[must_use]
    pub fn shape(&self) -> &CleanOriginShape {
        &self.shape
    }

    /// The Rust carrier types of the parameters, in order — what the emitted
    /// MIR's argument locals must be typed at.
    #[must_use]
    pub fn param_tys(&self) -> Vec<Ty> {
        self.signature.arguments().iter().map(|c| c.rust().clone()).collect()
    }

    /// The Rust carrier type of the result — the emitted MIR's `_0`.
    #[must_use]
    pub fn return_ty(&self) -> &Ty {
        self.signature.result().rust()
    }

    /// The result carrier — the type the faithfulness verdict is admitted at.
    #[must_use]
    pub fn result_carrier(&self) -> &Carrier {
        self.signature.result()
    }
}

/// Why no Clean-origin body was produced.
///
/// The variants split into two families that must never be confused, because
/// they mean opposite things about who is at fault:
///
/// * [`Self::NotEmittable`] and [`Self::NoTotalCarrier`] are **capability**
///   refusals about side A. The user wrote something outside the fragment; the
///   compiler is honest about it and the v7/D3 note says what to do.
/// * [`Self::LoweringUnrecognised`], [`Self::LoweringShapeMismatch`],
///   [`Self::ReflectionRejected`] and [`Self::Gate`] are **correctness**
///   refusals about side B. The compiler was about to emit something that
///   disagrees with what it read. Nothing the user writes changes them, and
///   they are internal-compiler-error shaped.
#[derive(Debug, Clone)]
pub enum EmitRefusal {
    /// Side A is not a shape this lane can originate a body for.
    NotEmittable {
        /// The declaration name.
        name: String,
        /// What was found instead, in the user's terms.
        reason: String,
    },
    /// Side A has no total Rust carrier in some signature position.
    NoTotalCarrier {
        /// The declaration name.
        name: String,
        /// I4's refusal, verbatim — it names the position and the true bound.
        refusal: CarrierRefused,
    },
    /// The emitted body did not read back as an admissible shape at all.
    ///
    /// The compiler emitted MIR that its own recognizer does not accept. That
    /// is a defect in the emitter, and it must refuse rather than emit an
    /// unverified body.
    LoweringUnrecognised {
        /// The declaration name.
        name: String,
        /// What the plan said should have been emitted.
        planned: CleanOriginShape,
    },
    /// The emitted body read back as a *different* admissible shape than the
    /// one planned.
    ///
    /// This is the structural half of the mistranslation catch. It is NOT a
    /// substitute for the kernel comparison and never short-circuits it in the
    /// agreeing direction: a shape that matches still goes to the kernel.
    LoweringShapeMismatch {
        /// The declaration name.
        name: String,
        /// What the plan said should have been emitted.
        planned: CleanOriginShape,
        /// What the emitted body actually reads back as.
        recognised: String,
    },
    /// The E6 Rust→Clean reflection refused to mint side B.
    ///
    /// The emitted body was recognised but could not be turned into a kernel
    /// term — an unsupported carrier domain, or the kernel rejecting the
    /// reflected defining equation. Either way there is no side B, so there is
    /// nothing to compare and emission must not proceed.
    ReflectionRejected {
        /// The declaration name.
        name: String,
        /// The producer's own message.
        detail: String,
    },
    /// The gate refused. See [`GateRefusal`].
    Gate(GateRefusal),
}

impl EmitRefusal {
    /// The declaration this refusal is about.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::NotEmittable { name, .. }
            | Self::NoTotalCarrier { name, .. }
            | Self::LoweringUnrecognised { name, .. }
            | Self::LoweringShapeMismatch { name, .. }
            | Self::ReflectionRejected { name, .. } => name,
            Self::Gate(refusal) => refusal.name(),
        }
    }

    /// Whether this refusal is about the emitted code rather than about what
    /// the user wrote.
    ///
    /// A caller renders the two families differently: a capability refusal is a
    /// diagnostic with options, a correctness refusal is a "please report it".
    /// Telling a user to add an annotation because the compiler mistranslated
    /// its own emission would send them to fix something they did not break.
    #[must_use]
    pub fn is_compiler_defect(&self) -> bool {
        match self {
            Self::NotEmittable { .. } | Self::NoTotalCarrier { .. } => false,
            Self::LoweringUnrecognised { .. }
            | Self::LoweringShapeMismatch { .. }
            | Self::ReflectionRejected { .. } => true,
            Self::Gate(refusal) => {
                matches!(
                    refusal,
                    GateRefusal::Disagreement { .. } | GateRefusal::SideANotKernelChecked { .. }
                )
            }
        }
    }

    /// The operator-facing explanation, ruling v7/D3: **why**, and **what to
    /// do**, with options.
    #[must_use]
    pub fn note(&self) -> String {
        match self {
            Self::NotEmittable { name, reason } => format!(
                "`{name}` is kernel-checked, but its body is not a shape this compiler can \
                 emit Rust code for yet: {reason}\n\
                 The callable fragment is currently a PARAMETER PROJECTION over fixed-width \
                 Clean carriers (`fun x y => x`), or WRAPPING `+`/`-`/`*` ARITHMETIC — a \
                 single op or a nested composition of up to {COMPOSED_MAX_OPS} ops — over \
                 parameters and in-range numerals with every signature position at ONE \
                 unsigned machine width (`fun x y => x + y`, `fun x => x - 1`, \
                 `fun x y => (x + y) * x`). This is a measured boundary of the compiler, \
                 not a rule about what you may write.\n\
                 options:\n\
                 - restate `{name}` inside that fragment and call it, keeping the general \
                   definition alongside for proof position;\n\
                 - if the body nests wrapping `+`/`-`/`*` at one unsigned machine width, \
                   it is emittable directly (up to {COMPOSED_MAX_OPS} ops) — no \
                   decomposition needed; past that, or where another operation \
                   intervenes, split it into single-op `def`s (one wrapping `+`/`-`/`*` \
                   each) and compose them at the call site;\n\
                 - cite `{name}` from a contract instead of calling it — proof position \
                   needs no emitted body and has no shape restriction;\n\
                 - write the computation as a Rust `fn` and prove it agrees with `{name}` \
                   in an `ensures` clause, which is the same guarantee reached from the \
                   other side."
            ),
            Self::NoTotalCarrier { name, refusal } => format!(
                "`{name}` is kernel-checked, but some position of its type has no TOTAL \
                 Rust carrier, so there is no Rust type that can hold those values without \
                 loss: {refusal:?}.\n\
                 A partial carrier would make the emitted binary disagree with the \
                 declaration on some inputs, and kernel definitional equality does not \
                 catch that — which is why the carrier is a separate obligation.\n\
                 options:\n\
                 - restate the offending position at a fixed-width Clean type \
                   (`UInt8`/`UInt16`/`UInt32`/`UInt64`), which carries exactly;\n\
                 - keep the unbounded type and cite `{name}` from proof position;\n\
                 - introduce a bounded wrapper in Clean with the bound in its type."
            ),
            Self::LoweringUnrecognised { name, planned } => format!(
                "INTERNAL: the body emitted for Clean-origin `{name}` was not recognised by \
                 the compiler's own body recognizer, so it could not be checked against the \
                 Clean definition and NOTHING WAS EMITTED.\n\
                 planned shape : {planned:?}\n\
                 This is a compiler-correctness refusal, not a proof obligation. Please \
                 report it."
            ),
            Self::LoweringShapeMismatch { name, planned, recognised } => format!(
                "INTERNAL: the body emitted for Clean-origin `{name}` reads back as a \
                 DIFFERENT shape than the one planned, so nothing was emitted.\n\
                 planned    : {planned:?}\n\
                 emitted    : {recognised}\n\
                 This is a compiler-correctness refusal, not a proof obligation. Please \
                 report it."
            ),
            Self::ReflectionRejected { name, detail } => format!(
                "INTERNAL: the body emitted for Clean-origin `{name}` could not be reflected \
                 back into a Clean term, so there was nothing to compare the definition \
                 against and nothing was emitted: {detail}\n\
                 This is a compiler-correctness refusal, not a proof obligation. Please \
                 report it."
            ),
            Self::Gate(refusal) => refusal.note(),
        }
    }
}

impl From<GateRefusal> for EmitRefusal {
    fn from(refusal: GateRefusal) -> Self {
        Self::Gate(refusal)
    }
}

/// Decide whether a Clean `def` can have a Rust body originated for it, and at
/// what carrier signature.
///
/// This reads **side A only**. It is not the gate and it is not permission to
/// emit: it says what an emission would have to look like, so that
/// [`admit_lowering`] has something to compare an actual emission against.
///
/// # Errors
///
/// * [`EmitRefusal::NotEmittable`] — no kernel check, no definition body, or a
///   body outside the emittable fragment;
/// * [`EmitRefusal::NoTotalCarrier`] — some signature position does not carry.
pub fn plan_clean_origin_body(
    env: &Environment,
    name: &str,
) -> Result<CleanOriginPlan, EmitRefusal> {
    let kernel_name = Name::from_string(name);

    // PROVENANCE FIRST, exactly as the gate does. A structurally-inserted or
    // unchecked declaration is not a kernel verdict, and planning an emission
    // from it would mean the emitted code's reference was never validated.
    // Checking it here as well as in the gate is not redundant: it makes the
    // *plan* — which decides the emitted signature — rest on a kernel verdict
    // too, so a bad declaration cannot even shape the MIR.
    match env.declaration_verification(&kernel_name) {
        Some(DeclarationVerification::FullKernelCheck) => {}
        verification => {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: format!(
                    "it did not enter the Clean environment through a full kernel check \
                     (origin: {verification:?})"
                ),
            });
        }
    }

    let Some(constant) = env.get_const(&kernel_name) else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "there is no such declaration in the Clean environment".to_owned(),
        });
    };

    // `Theorem` and `Opaque` are excluded for the reasons `crate::gate` gives:
    // a proof term is proof-irrelevant and an opaque value is deliberately not
    // exposed to reduction, so neither is something emitted code can be
    // faithful to.
    if constant.kind != ConstantKind::Definition {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "it is a `{:?}`, not a `def`; only a definition exhibits a value for \
                 emitted code to agree with",
                constant.kind
            ),
        });
    }

    let Some(body) = constant.value.as_ref() else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "it has no definition body (an axiom or a valueless opaque asserts a \
                     type without exhibiting a value)"
                .to_owned(),
        });
    };

    // I4's decision, over the WHOLE signature. `CarrierSignature` cannot exist
    // with a partial position, so a plan implies total carriers everywhere.
    let signature = carrier_signature_for(&constant.type_)
        .map_err(|refusal| EmitRefusal::NoTotalCarrier { name: name.to_owned(), refusal })?;

    let shape = recognise_clean_shape(name, body, &signature)?;

    match &shape {
        // Belt and braces on the one invariant the emitted MIR depends on: the
        // projected parameter's carrier must be the result carrier, or `_0 =
        // move _{i+1}` is not even type-correct. The kernel already
        // established this when it accepted the definition, so a failure here
        // means the carrier decision and the kernel disagree — refuse rather
        // than emit. (Projection deliberately KEEPS its mixed-width
        // capability across the other positions — `control_3::half_5c` pins
        // it — which is why this check is per-shape rather than hoisted.)
        CleanOriginShape::Projection { projected } => {
            if signature.arguments()[*projected].rust() != signature.result().rust() {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: format!(
                        "the projected parameter carries at `{:?}` but the result carries at \
                         `{:?}`; the compiler will not emit a body whose carrier decision \
                         disagrees with the kernel's typing",
                        signature.arguments()[*projected].rust(),
                        signature.result().rust()
                    ),
                });
            }
        }
        CleanOriginShape::WrappingBinOp { op: _, left, right } => {
            let width = check_arith_signature(name, "a single wrapping op", &signature)?;
            // Operand bounds, RE-CHECKED here even though recognition
            // already enforced them — the plan is the sealed decision the
            // emitter trusts, so the invariants hold on the plan itself.
            for operand in [left, right] {
                check_arith_leaf(name, operand, &signature, width)?;
            }
        }
        CleanOriginShape::Composed { expr } => {
            let width = check_arith_signature(name, "a composed wrapping tree", &signature)?;
            // Tree invariants, RE-CHECKED on the sealed plan for the same
            // reason as the single-op arm: every leaf in bounds, and the node
            // count inside the measured fragment — `ArithExpr` itself cannot
            // carry either bound.
            let ops = check_composed_tree(name, expr, &signature, width)?;
            if !(2..=COMPOSED_MAX_OPS).contains(&ops) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: composed_ops_out_of_range_reason(ops),
                });
            }
        }
        // R2/C5a: the same single-domain constraint as the arithmetic shapes,
        // for the same reason — `admit_select_function` is single-domain over
        // ALL parameters, used or not — plus parameter bounds re-checked on
        // the sealed plan. (The width check reuses the arithmetic helper: a
        // select has no arithmetic, but its positions must still all carry at
        // one unsigned machine width for the reflection to be typeable.)
        CleanOriginShape::Select { cmp: _, cmp_left, cmp_right, then_param, else_param } => {
            check_arith_signature(name, "a parameter select", &signature)?;
            for index in [cmp_left, cmp_right, then_param, else_param] {
                if *index >= signature.arity() {
                    return Err(EmitRefusal::NotEmittable {
                        name: name.to_owned(),
                        reason: format!(
                            "its select names parameter {index} but the signature has \
                             only {} parameter(s)",
                            signature.arity()
                        ),
                    });
                }
            }
        }
    }

    Ok(CleanOriginPlan { name: name.to_owned(), signature, shape })
}

/// The plan-time signature checks shared by the two arithmetic shapes.
///
/// 1. UNIFORM WIDTH, EVERY POSITION — including unused parameters.
///    Load-bearing, not pedantry: the reflected side B
///    (`admit_expr_function`) is single-domain over ALL n parameters, so a
///    mixed-width side A can never be identified with any mintable side B.
///    Refusing at PLAN time keeps the refusal in the user-actionable
///    capability family instead of surfacing later as an internal error.
/// 2. The result must be an unsigned machine integer. `Bool` has a carrier
///    but no arithmetic domain.
///
/// Returns the one width everything carries at. `shape_desc` names the shape
/// in the user's terms (`"a single wrapping op"` / `"a composed wrapping
/// tree"`) so the refusal stays specific.
fn check_arith_signature(
    name: &str,
    shape_desc: &str,
    signature: &CarrierSignature,
) -> Result<u32, EmitRefusal> {
    if let Some((position, argument)) = signature
        .arguments()
        .iter()
        .enumerate()
        .find(|(_, argument)| argument.rust() != signature.result().rust())
    {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "it is {shape_desc}, but parameter {position} carries at \
                 `{:?}` while the result carries at `{:?}`; a wrapping-arithmetic body is \
                 emittable only when EVERY signature position — used or not — \
                 shares one unsigned machine width, because the reflected lowering \
                 it must be checked against is single-domain over all parameters",
                argument.rust(),
                signature.result().rust()
            ),
        });
    }
    let Ty::Int { width, signed: false } = *signature.result().rust() else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "it is {shape_desc}, but its result carries at `{:?}`, \
                 which has no wrapping arithmetic; the op fragment exists only at \
                 the unsigned machine widths (u8/u16/u32/u64)",
                signature.result().rust()
            ),
        });
    };
    if !matches!(width, 8 | 16 | 32 | 64) {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "it is {shape_desc} at width {width}, which is not an \
                 unsigned machine width (u8/u16/u32/u64)"
            ),
        });
    }
    Ok(width)
}

/// One arithmetic leaf's plan-time bounds: a parameter index inside the
/// signature's arity, or a numeral inside the carrier width.
fn check_arith_leaf(
    name: &str,
    operand: &ArithOperand,
    signature: &CarrierSignature,
    width: u32,
) -> Result<(), EmitRefusal> {
    match operand {
        ArithOperand::Param(i) if *i >= signature.arity() => Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "its operand names parameter {i} but the signature has \
                 only {} parameter(s)",
                signature.arity()
            ),
        }),
        ArithOperand::Const(v) if *v > max_uint_value(width) => Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: numeral_out_of_range_reason(*v, width),
        }),
        _ => Ok(()),
    }
}

/// Walk a composed tree checking every leaf with [`check_arith_leaf`], and
/// return the number of binop NODES. Recursion depth is bounded by the node
/// count, which the caller then bounds by [`COMPOSED_MAX_OPS`] — and which
/// recognition already refused to exceed, so a deeper plan cannot exist.
fn check_composed_tree(
    name: &str,
    expr: &ArithExpr,
    signature: &CarrierSignature,
    width: u32,
) -> Result<usize, EmitRefusal> {
    match expr {
        ArithExpr::Operand(leaf) => {
            check_arith_leaf(name, leaf, signature, width)?;
            Ok(0)
        }
        ArithExpr::Bin { op: _, left, right } => {
            let left = check_composed_tree(name, left, signature, width)?;
            let right = check_composed_tree(name, right, signature, width)?;
            Ok(1 + left + right)
        }
    }
}

/// The one refusal reason for a composed tree outside `2..=COMPOSED_MAX_OPS`
/// nodes, shared by recognition and the plan-time re-check so the two
/// spellings cannot drift (the same rule as [`numeral_out_of_range_reason`]).
fn composed_ops_out_of_range_reason(ops: usize) -> String {
    format!(
        "its body reached {ops} composed wrapping operation(s) against a measured \
         fragment of 2..={COMPOSED_MAX_OPS} `+`/`-`/`*` nodes per body \
         (fragment_widening_probes probe_f2 is the measurement); split the definition \
         into smaller `def`s of at most {COMPOSED_MAX_OPS} ops each and compose them at \
         the call site"
    )
}

/// Peel `arity` lambdas and require the remaining body to be a bound variable
/// (a projection) or a wrapping-arithmetic expression — a single binary op or
/// a composed tree of them — at the result carrier.
///
/// Fail-closed on everything else, including a body with FEWER lambdas than the
/// type has arrows (an eta-contracted or partially-applied definition), because
/// the emitted MIR's parameter list is derived from the arity and a mismatch
/// would silently mean a different function.
fn recognise_clean_shape(
    name: &str,
    body: &Expr,
    signature: &CarrierSignature,
) -> Result<CleanOriginShape, EmitRefusal> {
    let arity = signature.arity();
    if arity == 0 {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "it is a nullary constant, and neither emittable shape is nullary: a \
                     projection needs a parameter to project and a wrapping op needs \
                     operands under binders. A constant `def` is still refused on the \
                     compiler lane today (the `ConstantUint` rows of \
                     tests/e6-fragment-probe; `fragment_widening_probes.rs` probe_e3 \
                     locates that defect in the arity-erasing nullary-mint routing, not \
                     in kernel definitional equality)"
                .to_owned(),
        });
    }

    let mut cursor = strip_mdata(body);
    for _ in 0..arity {
        let ExprKind::Lam(_, _, inner) = cursor.kind() else {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: format!(
                    "its type has {arity} argument(s) but its body does not abstract that \
                     many; the emittable shapes — a parameter projection, or a single \
                     wrapping `+`/`-`/`*` — are recognised only under a fully-abstracted \
                     body"
                ),
            });
        };
        cursor = strip_mdata(inner);
    }

    match cursor.kind() {
        &ExprKind::BVar(index) => {
            let index = index as usize;
            if index >= arity {
                // A loose bound variable under the binders we peeled. The
                // kernel would not have accepted this, so reaching it means the
                // environment disagrees with itself; refuse.
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: format!(
                        "its body is a loose bound variable (de Bruijn {index} under {arity} \
                         binders)"
                    ),
                });
            }
            // Under `n` binders, de Bruijn `k` is SOURCE parameter `n-1-k`.
            // This inversion is the one-construct mistake this lane can make;
            // `admit_projection_function` performs the inverse when it mints
            // side B, and the gate is what catches a disagreement.
            Ok(CleanOriginShape::Projection { projected: arity - 1 - index })
        }
        other => {
            if let Some(shape) = recognise_wrapping_expr(name, cursor, arity, signature)? {
                return Ok(shape);
            }
            // R2/C5a: the parameter-select ite.
            if let Some(shape) = recognise_select_ite(cursor, arity, signature) {
                return Ok(shape);
            }
            Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: format!(
                    "its body computes (`{}`) outside the emittable fragment: it is \
                     neither a bare parameter projection, nor a single wrapping \
                     `+`/`-`/`*`, nor a nested composition of wrapping `+`/`-`/`*`, \
                     nor a parameter select (`if x < y then x else y` over bare \
                     parameters), over parameters and in-range numerals at one \
                     unsigned machine width",
                    render_head(other)
                ),
            })
        }
    }
}

/// The largest value an unsigned integer of `width` bits can hold. `width` is
/// already validated to be a machine width (8/16/32/64) by every caller.
fn max_uint_value(width: u32) -> u128 {
    (1u128 << width) - 1
}

/// The one refusal reason for a numeral outside `0..2^width`, shared by
/// recognition and the plan-time re-check so the two spellings cannot drift.
///
/// Emitting `v mod 2^w` would actually be defeq-faithful — `ofNat` wraps — but
/// the claim is subtle and the honest answer is to refuse: fail-closed costs
/// capability, never soundness.
fn numeral_out_of_range_reason(value: u128, width: u32) -> String {
    format!(
        "its numeral operand `{value}` does not fit the u{width} result carrier; restate \
         the literal in range 0..2^{width} — the compiler will not silently reduce it \
         modulo 2^{width}, because the emitted value must be the one the definition names"
    )
}

/// Recognise the parameter-select `ite` at the signature's result carrier, or
/// `None` (the caller renders the capability refusal).
///
/// The exact tree Clean's `elab_if` mints for `if l ⊲ r then t else e` at a
/// machine carrier — and the exact tree `admit_select_function` builds on
/// side B (the 2026-07-25 Option-B ruling made them identical by
/// construction; `probe_h_select_admits` measures rather than assumes it):
///
/// ```text
/// ite.{1} {C} (LT.lt.{0} {C} instLT{C} l r) (instDecidable{C}Lt l r) t e
///             (LE.le / instLE{C} / instDecidable{C}Le for <=;
///              Eq.{1} {C} l r    / instDecidableEq{C} for ==)
/// ```
///
/// Everything is matched EXACTLY — head levels, the carrier type argument,
/// the comparison's instance constant, and the requirement that the Decidable
/// instance is applied to the SAME two operands the proposition names (a
/// different instance argument is a different denotation, the same rule the
/// numeral spelling enforces on `instOfNat`). Every operand and both arms
/// must be bare bound parameters. Anything else fails closed to `None`:
/// notably e6 f02's `toNat` comparison spelling (kernel-equal, but a
/// DIFFERENT tree — admitting it here would put an unmeasured identification
/// on the emit lane) and f03's constant arms.
fn recognise_select_ite(
    cursor: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Option<CleanOriginShape> {
    let CleanType::UInt(width) = signature.result().clean() else {
        return None;
    };
    let carrier = format!("UInt{width}");
    let bvar_param = |expr: &Expr| -> Option<usize> {
        match strip_mdata(expr).kind() {
            &ExprKind::BVar(index) if (index as usize) < arity => {
                Some(arity - 1 - index as usize)
            }
            _ => None,
        }
    };
    let is_carrier_const = |expr: &Expr| -> bool {
        matches!(strip_mdata(expr).kind(), ExprKind::Const(n, levels)
            if n.to_string() == carrier && levels.is_empty())
    };

    let (head, args) = uncurry(cursor);
    let ExprKind::Const(head_name, head_levels) = head.kind() else {
        return None;
    };
    if head_name.to_string() != "ite"
        || head_levels.len() != 1
        || head_levels[0] != Level::succ(Level::zero())
        || args.len() != 5
        || !is_carrier_const(args[0])
    {
        return None;
    }

    // The proposition: LT.lt/LE.le with the homogeneous instance, or Eq.
    let (prop_head, prop_args) = uncurry(args[1]);
    let ExprKind::Const(prop_name, prop_levels) = prop_head.kind() else {
        return None;
    };
    let (cmp, dec_inst_name, l_expr, r_expr) = match prop_name.to_string().as_str() {
        "LT.lt" | "LE.le" => {
            if prop_levels.len() != 1 || !prop_levels[0].is_zero() || prop_args.len() != 4 {
                return None;
            }
            let (cmp, class) = if prop_name.to_string() == "LT.lt" {
                (SelectCmp::Lt, "LT")
            } else {
                (SelectCmp::Le, "LE")
            };
            if !is_carrier_const(prop_args[0]) {
                return None;
            }
            let inst_ok = matches!(strip_mdata(prop_args[1]).kind(), ExprKind::Const(n, levels)
                if n.to_string() == format!("inst{class}{carrier}") && levels.is_empty());
            if !inst_ok {
                return None;
            }
            let suffix = if cmp == SelectCmp::Lt { "Lt" } else { "Le" };
            (cmp, format!("instDecidable{carrier}{suffix}"), prop_args[2], prop_args[3])
        }
        "Eq" => {
            if prop_levels.len() != 1 || prop_args.len() != 3 || !is_carrier_const(prop_args[0])
            {
                return None;
            }
            (SelectCmp::Eq, format!("instDecidableEq{carrier}"), prop_args[1], prop_args[2])
        }
        _ => return None,
    };
    let cmp_left = bvar_param(l_expr)?;
    let cmp_right = bvar_param(r_expr)?;

    // The Decidable instance, applied to the SAME two operands.
    let (inst_head, inst_args) = uncurry(args[2]);
    let inst_ok = matches!(inst_head.kind(), ExprKind::Const(n, levels)
        if n.to_string() == dec_inst_name && levels.is_empty());
    if !inst_ok
        || inst_args.len() != 2
        || bvar_param(inst_args[0]) != Some(cmp_left)
        || bvar_param(inst_args[1]) != Some(cmp_right)
    {
        return None;
    }

    Some(CleanOriginShape::Select {
        cmp,
        cmp_left,
        cmp_right,
        then_param: bvar_param(args[3])?,
        else_param: bvar_param(args[4])?,
    })
}

/// Uncurry an application spine, stripping metadata between every node:
/// `((f a) b)` becomes `(f, [a, b])`. Head and arguments are all
/// `strip_mdata`'d, for the same reason `strip_mdata` itself exists: an
/// elaborator annotation must not take a definition out of the fragment.
fn uncurry(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut cursor = strip_mdata(expr);
    let mut args = Vec::new();
    while let ExprKind::App(function, argument) = cursor.kind() {
        args.push(strip_mdata(argument));
        cursor = strip_mdata(function);
    }
    args.reverse();
    (cursor, args)
}

/// Attempt to read a fully-peeled body as a wrapping-arithmetic expression at
/// the signature's result carrier: a single binary op ([`CleanOriginShape::WrappingBinOp`])
/// or a nested tree of them ([`CleanOriginShape::Composed`]). Exactly the two
/// spellings the kernel probes measured, at every node
/// (`fragment_widening_probes.rs` a/a2/b/c/d, a4–a6, and probe_f for nesting):
///
/// * **carrier:** `{C}.add|sub|mul lhs rhs`;
/// * **surface:** `H{Add,Sub,Mul}.h{add,sub,mul} {C} {C} {C} instH{…}{C} lhs rhs`
///   with the instance constant EXACTLY the prelude's homogeneous instance.
///
/// Returns `Ok(Some(shape))` on a match; `Ok(None)` when the body is not a
/// wrapping-op spine at all — including a BARE numeral body, which parses as
/// a leaf but is not an op — so the caller falls through to the generic
/// fragment refusal (this is what keeps `fun a => 6` refused, probe_e3's
/// boundary); `Err(refusal)` when a spine WAS matched but is outside the
/// fragment for a specific, user-fixable reason — an out-of-range numeral, a
/// non-prelude instance, or more than [`COMPOSED_MAX_OPS`] nodes — so the
/// refusal can name the exact boundary. A user-defined instance constant is
/// well-typed, kernel-reducible, and would even pass defeq; it is refused
/// HERE so it surfaces as a *capability* refusal rather than tunneling into
/// the internal-error family.
fn recognise_wrapping_expr(
    name: &str,
    body: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Result<Option<CleanOriginShape>, EmitRefusal> {
    // The wrapping-op fragment exists only at an unsigned machine width; for
    // any other result carrier there is no `{C}.add` family to match.
    let CleanType::UInt(width) = signature.result().clean() else {
        return Ok(None);
    };
    if !matches!(width, 8 | 16 | 32 | 64) {
        return Ok(None);
    }
    let carrier_name = signature.result().clean().name();

    let mut ops = 0usize;
    let Some(tree) = recognise_arith_tree(name, body, arity, &carrier_name, width, &mut ops)?
    else {
        return Ok(None);
    };
    match tree {
        // A bare leaf body (`fun a => 6`). Not an op: fall through to the
        // generic refusal, keeping the ConstantUint boundary exactly where it
        // was. (A bare BVar body never reaches here — the Projection arm of
        // `recognise_clean_shape` consumed it.)
        ArithExpr::Operand(_) => Ok(None),
        ArithExpr::Bin { op, left, right } => match (*left, *right) {
            // One op over two leaves: the single-op shape, unchanged — its
            // emitter, its structural comparison and its rendering all stay
            // exactly as landed 2026-08-19.
            (ArithExpr::Operand(left), ArithExpr::Operand(right)) => {
                Ok(Some(CleanOriginShape::WrappingBinOp { op, left, right }))
            }
            // Anything nested: the composed tree.
            (left, right) => Ok(Some(CleanOriginShape::Composed {
                expr: ArithExpr::Bin { op, left: Box::new(left), right: Box::new(right) },
            })),
        },
    }
}

/// One node of the recursive wrapping-expression read: a leaf (via the
/// unchanged [`recognise_arith_operand`]) or an op spine in either measured
/// spelling, its operands read by recursion. `ops` counts binop nodes and
/// refuses past [`COMPOSED_MAX_OPS`] — the count bounds the recursion depth,
/// so an adversarially deep Clean term refuses instead of exhausting the
/// stack.
fn recognise_arith_tree(
    name: &str,
    expr: &Expr,
    arity: usize,
    carrier_name: &str,
    width: u32,
    ops: &mut usize,
) -> Result<Option<ArithExpr>, EmitRefusal> {
    // Leaves first: a bound parameter or an in-range numeral. The leaf heads
    // (`BVar`, `{C}.ofNat`, `OfNat.ofNat`) are disjoint from the op heads, so
    // the order here is not a tiebreak.
    if let Some(leaf) = recognise_arith_operand(name, expr, arity, carrier_name, width)? {
        return Ok(Some(ArithExpr::Operand(leaf)));
    }

    let (head, args) = uncurry(expr);
    let ExprKind::Const(head_name, _levels) = head.kind() else {
        return Ok(None);
    };

    // ── carrier spelling: `{C}.op lhs rhs` ──────────────────────────────────
    for (op_name, op) in
        [("add", ArithBinOp::Add), ("sub", ArithBinOp::Sub), ("mul", ArithBinOp::Mul)]
    {
        if *head_name != Name::from_string(&format!("{carrier_name}.{op_name}")) {
            continue;
        }
        let [lhs, rhs] = args[..] else {
            return Ok(None);
        };
        return recognise_arith_node(name, op, lhs, rhs, arity, carrier_name, width, ops);
    }

    // ── surface spelling: `HAdd.hAdd {C} {C} {C} instHAdd{C} lhs rhs` ───────
    for (class, projection, op) in [
        ("HAdd", "hAdd", ArithBinOp::Add),
        ("HSub", "hSub", ArithBinOp::Sub),
        ("HMul", "hMul", ArithBinOp::Mul),
    ] {
        if *head_name != Name::from_string(&format!("{class}.{projection}")) {
            continue;
        }
        let [t1, t2, t3, instance, lhs, rhs] = args[..] else {
            return Ok(None);
        };
        let carrier_const = Name::from_string(carrier_name);
        let is_carrier =
            |t: &Expr| matches!(t.kind(), ExprKind::Const(n, _) if *n == carrier_const);
        if !(is_carrier(t1) && is_carrier(t2) && is_carrier(t3)) {
            // A heterogeneous instantiation. Outside both measured spellings;
            // fall through to the generic fragment refusal.
            return Ok(None);
        }
        let expected_instance = format!("inst{class}{carrier_name}");
        match instance.kind() {
            ExprKind::Const(n, _) if *n == Name::from_string(&expected_instance) => {}
            _ => {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: format!(
                        "its `{class}.{projection}` at `{carrier_name}` routes through an \
                         instance other than the prelude's homogeneous `{expected_instance}`; \
                         only the prelude instance is in the measured emittable fragment \
                         (a user instance may be kernel-reducible to it, but the compiler \
                         will not guess — spell the op so it elaborates through the \
                         prelude instance, or keep the definition for proof position)"
                    ),
                });
            }
        }
        return recognise_arith_node(name, op, lhs, rhs, arity, carrier_name, width, ops);
    }

    Ok(None)
}

/// A matched op spine's node: bump the count against the measured cap, then
/// read both operands by recursion.
#[allow(clippy::too_many_arguments)]
fn recognise_arith_node(
    name: &str,
    op: ArithBinOp,
    lhs: &Expr,
    rhs: &Expr,
    arity: usize,
    carrier_name: &str,
    width: u32,
    ops: &mut usize,
) -> Result<Option<ArithExpr>, EmitRefusal> {
    *ops += 1;
    if *ops > COMPOSED_MAX_OPS {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: composed_ops_out_of_range_reason(*ops),
        });
    }
    let (Some(left), Some(right)) = (
        recognise_arith_tree(name, lhs, arity, carrier_name, width, ops)?,
        recognise_arith_tree(name, rhs, arity, carrier_name, width, ops)?,
    ) else {
        return Ok(None);
    };
    Ok(Some(ArithExpr::Bin { op, left: Box::new(left), right: Box::new(right) }))
}

/// Read one LEAF of a wrapping-arithmetic expression: a bound parameter, or
/// an in-range numeral in either measured spelling (`{C}.ofNat n`, or
/// `OfNat.ofNat {C} n (instOfNat{C} n)` with the two literals equal).
///
/// `Ok(None)` means "not a leaf this fragment covers" (a free variable, a
/// `let`, …) and the caller — [`recognise_arith_tree`] — goes on to try the
/// op spines, falling through to the generic refusal if nothing matches;
/// `Err` means a numeral WAS matched but does not fit the width.
fn recognise_arith_operand(
    name: &str,
    operand: &Expr,
    arity: usize,
    carrier_name: &str,
    width: u32,
) -> Result<Option<ArithOperand>, EmitRefusal> {
    if let &ExprKind::BVar(index) = operand.kind() {
        let index = index as usize;
        if index >= arity {
            // Loose under the peeled binders; the kernel would not have
            // accepted it. Fail closed through the generic refusal.
            return Ok(None);
        }
        // The same de Bruijn inversion the Projection arm documents — and the
        // mutation controls' favourite target.
        return Ok(Some(ArithOperand::Param(arity - 1 - index)));
    }

    let (head, args) = uncurry(operand);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return Ok(None);
    };

    // ── carrier numeral: `{C}.ofNat n` ──────────────────────────────────────
    if *head_name == Name::from_string(&format!("{carrier_name}.ofNat")) {
        let [literal] = args[..] else {
            return Ok(None);
        };
        let Some(value) = nat_literal(literal) else {
            return Ok(None);
        };
        return in_range_numeral(name, value, width).map(Some);
    }

    // ── surface numeral: `OfNat.ofNat {C} n (instOfNat{C} n)` ───────────────
    if *head_name == Name::from_string("OfNat.ofNat") {
        let [ty, literal, instance] = args[..] else {
            return Ok(None);
        };
        if !matches!(ty.kind(), ExprKind::Const(n, _) if *n == Name::from_string(carrier_name)) {
            return Ok(None);
        }
        let Some(value) = nat_literal(literal) else {
            return Ok(None);
        };
        let (instance_head, instance_args) = uncurry(instance);
        if !matches!(
            instance_head.kind(),
            ExprKind::Const(n, _) if *n == Name::from_string(&format!("instOfNat{carrier_name}"))
        ) {
            return Ok(None);
        }
        let [instance_literal] = instance_args[..] else {
            return Ok(None);
        };
        if nat_literal(instance_literal) != Some(value) {
            return Ok(None);
        }
        return in_range_numeral(name, value, width).map(Some);
    }

    Ok(None)
}

/// The value of a kernel `Nat` literal, when it fits `u128`. A multi-limb
/// literal reports `None` from `to_u64` and is treated by the caller as
/// out of range — which it is, for every machine width this lane admits.
fn nat_literal(expr: &Expr) -> Option<NatReading> {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(value)) => Some(match value.to_u64() {
            Some(small) => NatReading::Fits(u128::from(small)),
            None => NatReading::Oversized,
        }),
        _ => None,
    }
}

/// A `Nat` literal reading: either a value small enough to range-check, or a
/// multi-limb literal that is out of range for every admitted width.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NatReading {
    Fits(u128),
    Oversized,
}

/// Range-check a matched numeral against the carrier width, fail-closed.
fn in_range_numeral(
    name: &str,
    value: NatReading,
    width: u32,
) -> Result<ArithOperand, EmitRefusal> {
    match value {
        NatReading::Fits(value) if value <= max_uint_value(width) => {
            Ok(ArithOperand::Const(value))
        }
        NatReading::Fits(value) => Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: numeral_out_of_range_reason(value, width),
        }),
        NatReading::Oversized => Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "its numeral operand does not even fit u64, let alone the u{width} result \
                 carrier; restate the literal in range 0..2^{width} — the compiler will \
                 not silently reduce it modulo 2^{width}"
            ),
        }),
    }
}

/// The head constructor of an expression, for a diagnostic that names what was
/// found without dumping a whole term at the user.
fn render_head(kind: &ExprKind) -> &'static str {
    match kind {
        ExprKind::BVar(_) => "a bound variable",
        ExprKind::FVar(_) => "a free variable",
        ExprKind::Sort(_) => "a sort",
        ExprKind::Const(..) => "a constant",
        ExprKind::App(..) => "an application",
        ExprKind::Lam(..) => "a lambda",
        ExprKind::Pi(..) => "a function type",
        ExprKind::Let(..) => "a `let`",
        ExprKind::Lit(_) => "a literal",
        ExprKind::Proj(..) => "a projection out of a structure",
        ExprKind::MData(..) => "metadata",
        _ => "an expression outside the computational fragment",
    }
}

/// Strip transparent metadata wrappers. `MData` is invisible to type checking,
/// so it must be invisible to shape recognition too — otherwise an elaborator
/// that annotates a term would silently take a definition out of the fragment.
fn strip_mdata(expr: &Expr) -> &Expr {
    let mut cursor = expr;
    while let ExprKind::MData(_, inner) = cursor.kind() {
        cursor = inner;
    }
    cursor
}

/// The name side B is minted under while it is being reflected.
///
/// It is minted into a **clone** of the environment, so this name never enters
/// the crate's real Clean environment and can never be cited, called, or
/// collided with. The suffix is not a namespace separator (`.`) on purpose: a
/// dotted name would create a child of the declaration in the Clean namespace
/// tree, which is exactly the kind of visible side effect a check must not have.
fn reflection_name(name: &str) -> String {
    format!("{name}_trust_clean_origin_reflection")
}

/// **The round trip.** Put the body the compiler actually emitted to the gate.
///
/// `extracted` is the emitted `mir::Body` after
/// `trust_mir_extract::extract_function` — i.e. read back out of MIR, not the
/// plan and not anything this crate produced. It is passed as a
/// `trust_types::VerifiableFunction` rather than a `mir::Body` so that this
/// decision, like every other one in this crate, stays on the fast lane and can
/// be mutation-tested without a compiler.
///
/// The four checks, in order, each fail-closed:
///
/// 1. the emitted body must be recognised by
///    [`recognize_admissible_body`] — the compiler's own recognizer, unmodified;
/// 2. its recognised shape must be the PLANNED shape (a structural catch that
///    never substitutes for the kernel one);
/// 3. it must reflect back into a kernel term via
///    [`trust_spec_elab::admit_projection_function`] (projections) or
///    [`trust_spec_elab::admit_expr_function`] (wrapping binops and composed
///    trees, over the recognizer's own rendering — bare for a single op,
///    fully parenthesized for a tree) — each FULL-KERNEL-CHECKS the reflected
///    defining equation;
/// 4. the kernel must identify that term with side A —
///    [`check_faithful`], **at the carrier type**.
///
/// # Errors
///
/// Any of [`EmitRefusal`]'s side-B variants. There is no degraded mode: a body
/// that does not reach step 4 clean is not emitted.
pub fn admit_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
) -> Result<Faithful, EmitRefusal> {
    let name = plan.name.as_str();

    // ── 1. the compiler's own recognizer, on the emitted body ──────────────
    let Some(recognised) = recognize_admissible_body(extracted) else {
        return Err(EmitRefusal::LoweringUnrecognised {
            name: name.to_owned(),
            planned: plan.shape.clone(),
        });
    };

    // ── 2. structural agreement with the plan ──────────────────────────────
    //
    // Arity first, shared by every shape: a call site passes
    // `plan.signature.arity()` arguments to whatever body this is, and an
    // arity disagreement alone must refuse.
    if extracted.body.arg_count != plan.signature.arity() {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!(
                "{recognised:?} over {} parameter(s), not {}",
                extracted.body.arg_count,
                plan.signature.arity()
            ),
        });
    }
    match (&plan.shape, &recognised) {
        (CleanOriginShape::Projection { projected }, AdmissibleBody::Projection { param })
            if param == projected => {}
        (
            CleanOriginShape::WrappingBinOp { op, left, right },
            AdmissibleBody::Arithmetic { op: emitted_op, left: emitted_left, right: emitted_right },
        ) if op == emitted_op && left == emitted_left && right == emitted_right => {}
        (
            CleanOriginShape::Composed { expr },
            AdmissibleBody::Composed { expr: emitted_expr },
        ) if expr == emitted_expr => {}
        (
            CleanOriginShape::Select { cmp, cmp_left, cmp_right, then_param, else_param },
            AdmissibleBody::Select {
                cmp: emitted_cmp,
                cmp_left: emitted_cl,
                cmp_right: emitted_cr,
                then_param: emitted_then,
                else_param: emitted_else,
            },
        ) if cmp == emitted_cmp
            && cmp_left == emitted_cl
            && cmp_right == emitted_cr
            && then_param == emitted_then
            && else_param == emitted_else => {}
        _ => {
            return Err(EmitRefusal::LoweringShapeMismatch {
                name: name.to_owned(),
                planned: plan.shape.clone(),
                recognised: format!("{recognised:?}"),
            });
        }
    }

    // ── 3. reflect the EMITTED body back into Clean ────────────────────────
    //
    // The domains come from the emitted body's OWN local types, never from the
    // plan. That is load-bearing: taking them from the plan would make side B
    // partly a copy of side A, and the gate would stop being able to see an
    // emitter that typed a local wrongly.
    let Some(param_domains) = param_domains_of(extracted) else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "a parameter of the emitted body is not a supported machine carrier"
                .to_owned(),
        });
    };

    // Minted into a CLONE. The real crate environment must not acquire a
    // constant as a side effect of checking one — a check that mutates the
    // thing it checks cannot be run twice and cannot be reasoned about.
    let mut scratch = env.clone();
    let reflected_name = reflection_name(name);
    let minted = match &recognised {
        AdmissibleBody::Projection { param } => trust_spec_elab::admit_projection_function(
            &mut scratch,
            &reflected_name,
            &param_domains,
            *param,
        ),
        // Both arithmetic shapes: the SINGLE-domain check over the emitted
        // body's own types, then `admit_expr_function` over a rendering of
        // the RECOGNIZER's output, never the plan's — the exact spellings
        // `trust_certify::clean_island::admit_function_into` routes for a
        // recognized `Arithmetic`/`Composed`, and the same renderings the
        // widening probes pin (probe_f: `((p0 + p1) * p0)`).
        AdmissibleBody::Arithmetic { op, left, right } => {
            let domain = shared_machine_domain(name, extracted, &param_domains)?;
            mint_expr_rendering(
                &mut scratch,
                &reflected_name,
                &render_wrapping_binop(*op, *left, *right),
                extracted.body.arg_count,
                &domain,
            )
        }
        AdmissibleBody::Composed { expr } => {
            let domain = shared_machine_domain(name, extracted, &param_domains)?;
            mint_expr_rendering(
                &mut scratch,
                &reflected_name,
                &render_composed(expr),
                extracted.body.arg_count,
                &domain,
            )
        }
        // R2/C5a: the select reflection. `admit_select_function` does its own
        // single-domain and Machine-only guards over `param_domains` — which
        // are read off the emitted body's own types above — so a mixed-width
        // or non-machine emission fails closed inside the frozen producer.
        // The comparison vocabulary is translated at the boundary, the same
        // way `trust_certify::clean_island::admit_function_into` does it.
        AdmissibleBody::Select { cmp, cmp_left, cmp_right, then_param, else_param } => {
            let elaborator_cmp = match cmp {
                SelectCmp::Lt => trust_spec_elab::SelectCmp::Lt,
                SelectCmp::Le => trust_spec_elab::SelectCmp::Le,
                SelectCmp::Eq => trust_spec_elab::SelectCmp::Eq,
            };
            trust_spec_elab::admit_select_function(
                &mut scratch,
                &reflected_name,
                &param_domains,
                elaborator_cmp,
                *cmp_left,
                *cmp_right,
                *then_param,
                *else_param,
            )
        }
        other => {
            // Step 2 already matched `recognised` against the planned shape,
            // so this arm is unreachable today. Fail closed, never panic, if
            // a recognizer widening ever makes it reachable.
            return Err(EmitRefusal::LoweringShapeMismatch {
                name: name.to_owned(),
                planned: plan.shape.clone(),
                recognised: format!("{other:?}"),
            });
        }
    };
    if let Err(detail) = minted {
        return Err(EmitRefusal::ReflectionRejected { name: name.to_owned(), detail });
    }
    let Some(side_b) = scratch
        .get_const(&Name::from_string(&reflected_name))
        .and_then(|c| c.value.clone())
    else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the reflected defining equation was accepted but carries no value"
                .to_owned(),
        });
    };

    // ── 4. THE GATE. Side A from `env`, side B from the emitted MIR. ───────
    //
    // Admitted at the RESULT carrier: that is the value a call produces, and
    // the plan's `CarrierSignature` is already the statement that every
    // argument position carries too (it cannot exist otherwise).
    Ok(check_faithful(env, name, &side_b, plan.result_carrier())?)
}

/// The one machine domain every position of the emitted body denotes.
///
/// The arithmetic reflections are SINGLE-domain: every parameter AND the
/// return of the emitted body must denote one machine domain — read off the
/// emitted body's OWN types, never the plan's, for the reason
/// [`admit_lowering`]'s step 3 states.
fn shared_machine_domain(
    name: &str,
    extracted: &VerifiableFunction,
    param_domains: &[Domain],
) -> Result<Domain, EmitRefusal> {
    let Some(domain @ Domain::Machine(_)) = ty_to_domain(&extracted.body.return_ty) else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the emitted body's return type is not a supported machine carrier"
                .to_owned(),
        });
    };
    if param_domains.iter().any(|parameter_domain| parameter_domain != &domain) {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the emitted body's positions do not share one machine domain".to_owned(),
        });
    }
    Ok(domain)
}

/// Mint a rendered arithmetic body over positional `p{i}` names through the
/// frozen [`trust_spec_elab::admit_expr_function`], which FULL-KERNEL-CHECKS
/// the reflected defining equation.
fn mint_expr_rendering(
    scratch: &mut Environment,
    reflected_name: &str,
    rendered: &str,
    arg_count: usize,
    domain: &Domain,
) -> Result<trust_spec_elab::Admission, String> {
    let parameters: Vec<String> = (0..arg_count).map(|i| format!("p{i}")).collect();
    let parameter_refs: Vec<&str> = parameters.iter().map(String::as_str).collect();
    trust_spec_elab::admit_expr_function(scratch, reflected_name, rendered, &parameter_refs, domain)
}

/// The `clean_island::admit_function_into` rendering of a recognized
/// single-op `Arithmetic` body: positional `p{i}` names and raw literals,
/// `lhs op rhs`. Takes ONLY [`recognize_admissible_body`]'s output — never the
/// plan's shape — for the module-doc reason: side B must be a reading of the
/// EMITTED body. A swap bug here alone is caught by the structural
/// plan-vs-recognizer check; a de Bruijn inversion in side-A recognition alone
/// is caught by the kernel; the mutation control pins each half.
fn render_wrapping_binop(op: ArithBinOp, left: ArithOperand, right: ArithOperand) -> String {
    let operand = |operand: ArithOperand| match operand {
        ArithOperand::Param(index) => format!("p{index}"),
        ArithOperand::Const(value) => value.to_string(),
    };
    let op = match op {
        ArithBinOp::Add => "+",
        ArithBinOp::Sub => "-",
        ArithBinOp::Mul => "*",
    };
    format!("{} {} {}", operand(left), op, operand(right))
}

/// The `clean_island::admit_function_into` rendering of a recognized
/// `Composed` tree: FULLY PARENTHESIZED over positional `p{i}` names and raw
/// literals, so the spec parser reconstructs exactly this tree — precedence
/// can never reshape it. Takes ONLY the recognizer's output, for the same
/// reason as [`render_wrapping_binop`]; the widening probes pin the exact
/// spelling (probe_f: `((p0 + p1) * p0)`). Recursion depth is the tree depth,
/// bounded by [`COMPOSED_MAX_OPS`] through the structural plan match.
fn render_composed(expr: &ArithExpr) -> String {
    match expr {
        ArithExpr::Operand(ArithOperand::Param(index)) => format!("p{index}"),
        ArithExpr::Operand(ArithOperand::Const(value)) => value.to_string(),
        ArithExpr::Bin { op, left, right } => {
            let op = match op {
                ArithBinOp::Add => "+",
                ArithBinOp::Sub => "-",
                ArithBinOp::Mul => "*",
            };
            format!("({} {} {})", render_composed(left), op, render_composed(right))
        }
    }
}

/// The elaboration domain a Rust carrier type denotes, or `None` outside the
/// supported fragment.
///
/// Deliberately a *separate* mapping from `trust_certify`'s private
/// `ty_to_domain`, and deliberately NARROWER: no `PtrSizedInt`. A pointer-sized
/// integer's width is a property of the target, and a Clean-origin body is the
/// one place a width mistake becomes an emitted value rather than a failed
/// proof. `usize` therefore fails closed here even though the E6 reflection
/// direction accepts it — that direction can only decline to prove something.
fn ty_to_domain(ty: &Ty) -> Option<Domain> {
    match ty {
        Ty::Bool => Some(Domain::Bool),
        Ty::Int { width, signed: false } => Some(Domain::Machine(match width {
            8 => MachineUIntWidth::U8,
            16 => MachineUIntWidth::U16,
            32 => MachineUIntWidth::U32,
            64 => MachineUIntWidth::U64,
            _ => return None,
        })),
        // Trust (I6): the bignum carrier, in both spellings this function can
        // meet — the carrier decision's own `Ty::BignumNat`, and the EXTRACTED
        // body's `Adt` naming the runtime type (`trust-mir-extract` renders an
        // ADT by path and knows nothing of the carrier variant).
        //
        // SOUNDNESS NOTE, per the I6 review: the name match here is NOT what
        // makes this sound — nothing stamps or authenticates the ADT at this
        // point. It is sound only because `admit_lowering` re-derives the plan
        // from the kernel declaration, requires structural agreement, and then
        // puts the reflected side B to the kernel gate: a wrong or impostor
        // `Nat` yields a term the kernel refuses to identify with side A. This
        // arm only chooses which DOMAIN the reflection is attempted in.
        Ty::BignumNat => Some(Domain::Nat),
        Ty::Adt { name, .. } if name == "trust_bignum::Nat" => Some(Domain::Nat),
        _ => None,
    }
}

/// The domains of every value parameter of the emitted body, in order.
///
/// Parameters are locals `1..=arg_count` (`_0` is the return place). A missing
/// local or an unsupported type fails the whole reflection closed.
fn param_domains_of(func: &VerifiableFunction) -> Option<Vec<Domain>> {
    (1..=func.body.arg_count)
        .map(|i| func.body.locals.iter().find(|l| l.index == i).and_then(|l| ty_to_domain(&l.ty)))
        .collect()
}
