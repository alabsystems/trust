// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! I5 decision 2 — **the faithfulness gate**.
//!
//! The decision doc's placement, verbatim:
//!
//! > The gate lives in `clean_origin_mir(def)`, the **sole constructor** of a
//! > Clean-origin `Body`, called by BOTH the `optimized_mir` and `mir_for_ctfe`
//! > provider arms — so it covers CTFE and is NOT behind `-Ztrust-verify=off`.
//! > **The faithfulness gate is a compilation-correctness check on emitted code,
//! > not an obligation, and no verification switch may disable it.**
//!
//! This module is the gate's *decision*. It is a plain function so the wired
//! local and cross-crate providers cannot change what the gate decides, only
//! when they run it.
//!
//! # What the gate compares, and why it is not circular
//!
//! Two independently-produced terms:
//!
//! * **side A — the Clean `def`'s own body**, read out of the kernel
//!   [`Environment`]. This side never passes through the lowering.
//! * **side B — `R(lowered)`**, the emitted body reflected back into Clean by
//!   the frozen R functor (`crates/trust-clean/src/reflect.rs`).
//!
//! The gate is meaningful *only because R is frozen against this lane*. If R
//! were edited to make a Clean-origin body pass, side B would be co-authored
//! with the thing it is checking and the gate would be testing a round trip
//! rather than a semantics. `tests/control_2_frozen_r_mutation.rs` is the
//! control that keeps this honest: it injects a one-construct mistranslation
//! into side B and requires the gate to catch it.
//!
//! # Why defeq alone is NOT the gate
//!
//! I4's `control_b_defeq_insufficiency` executes the proof, against the real
//! `clean_kernel::TypeChecker`, that
//! `UInt64.toNat (UInt64.ofNat (2^64))` is definitionally equal to `0`. A
//! defeq-only gate therefore admits a term **whose emitted value wrapped**. So
//! the gate's admitted statement is at the **carrier** type: it requires a
//! [`Carrier`], which I4 seals so it cannot exist without
//! `CarrierEvidence::Total`. A kernel equality verdict decides *did the
//! lowering mistranslate*; the carrier decides *can the result be represented
//! at all*. Neither subsumes the other and the gate demands both.
//!
//! Symbolic recursive arguments expose a second limitation of defeq: a
//! recursor is stuck until its major is constructor-headed. The fallback here
//! therefore proves `forall args, sideA args = sideB args` by structural
//! induction. The automation engine is search only; this module independently
//! kernel-checks the returned recursor term and requires `axiom_deps` to report
//! no non-foundational domain/trust assumptions before minting [`Faithful`].
//!
//! # Fail-closed
//!
//! Both searches are bounded. Kernel heartbeat or wall-clock exhaustion is a
//! typed resource refusal; an unsupported inductive, malformed proof, or
//! non-empty axiom closure also refuses. No incomplete decision is relabelled
//! as disagreement, and every path remains fail-closed. There is no unchecked
//! "unknown means admit" verdict on this lane.

use std::time::{Duration, Instant};

use clean_auto::AutomationEngine;
use clean_kernel::name::NameInner;
use clean_kernel::{
    BinderInfo, ConstantKind, DeclarationVerification, Environment, Expr, ExprKind, Level, Name,
    TypeChecker,
};
use trust_clean_carrier::{Carrier, carrier_signature_for};
use trust_types::Ty;

use crate::emit::WfLowering;

/// Hard wall for the optional structural-induction search.
///
/// `clean-auto` also carries structural-depth and induction-fuel rails. This
/// outer deadline bounds the search as a whole. Expiry is a refusal, never an
/// unchecked or partially checked admission.
const INDUCTION_TIMEOUT: Duration = Duration::from_secs(2);

/// Static operator-facing label for every kernel heartbeat rail used here.
///
/// `is_def_eq` and `whnf` return ordinary values when their counter is spent,
/// while `check_type` may return `HeartbeatExceeded`. Inspecting the public
/// counter immediately after each operation keeps all three shapes out of the
/// completed-disagreement classification.
const KERNEL_HEARTBEAT_ENVELOPE: &str =
    "kernel checking exhausted its two-million-heartbeat work envelope";

/// Maximum core-expression nodes admitted to the induction fallback.
///
/// Definitional equality keeps its own kernel rails. The optional automation
/// path additionally refuses before search when the signature or either side
/// exceeds this structural envelope, and applies the same envelope to the
/// constructed goal and proposed proof.
const INDUCTION_EXPR_NODE_LIMIT: usize = 4_096;

/// Maximum quantified parameters in the optional induction goal.
///
/// Direct definitional equality remains available at any already-carried
/// arity. This rail applies only before constructing the fallback's quantified
/// goal, preventing an attacker-sized signature from allocating an attacker-
/// sized binder/vector search state.
const INDUCTION_MAX_ARITY: usize = 8;

/// The kernel evidence which established faithfulness.
///
/// This is carried through export metadata: an inductive proof is never
/// relabelled as definitional equality merely because both mint the same
/// sealed [`Faithful`] permission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaithfulnessMethod {
    /// The two function bodies are definitionally equal.
    DefinitionalEquality,
    /// A closed, axiom-free recursor proof establishes extensional equality.
    StructuralInduction,
    /// Every defining equation was kernel-identified with its reflected
    /// counterpart, recursive result abstract on both sides (§6e as amended —
    /// [`check_faithful_equations`], the structural-recursion shapes).
    ///
    /// Deliberately has NO wire spelling: the digest mint refuses it
    /// (`DigestMintRefusal::UnencodableFaithfulness`) rather than relabelling
    /// a per-equation judgment as whole-term defeq or induction, so a
    /// recursive def's verdict stays crate-local until a per-equation wire
    /// tag is its own reviewed format change.
    PerEquationDefeq,
    /// A `WellFounded.fix` side A whose FUNCTIONAL was kernel-checked at side
    /// A's own functional type and kernel-identified with it, with side B's
    /// decrease slots filled by side A's proof terms and the axiom closure of
    /// both sides audited empty (R2 — [`check_faithful_wf_functional`]).
    ///
    /// Like [`Self::PerEquationDefeq`] it has NO wire spelling: an F-layer
    /// verdict is not whole-term defeq and must not be relabelled as one, so
    /// the digest mint refuses it and a WF verdict stays crate-local.
    WellFoundedFunctionalDefeq,
}

/// Evidence that a lowered Clean-origin body agrees with its Clean `def`,
/// **at the carrier type**.
///
/// **Constructible only by [`check_faithful`] (whole-term defeq, the
/// non-recursive shapes) and [`check_faithful_equations`] (per-defining-
/// equation defeq under the §6e IMPLEMENTATION AMENDMENT, the structural-
/// recursion shapes) — both in this module, so the seal is unchanged.** This
/// is the token a `clean_origin_mir` implementation must hold before it may
/// return a `Body`. Sealing it is the mechanism behind "sole constructor": a
/// caller that cannot build the token cannot route around the gate by
/// constructing the permission directly.
#[derive(Debug, Clone)]
pub struct Faithful {
    name: String,
    admitted_at: Ty,
    method: FaithfulnessMethod,
}

impl Faithful {
    /// The declaration whose body was admitted.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The **carrier** type the agreement was admitted at.
    ///
    /// Deliberately the Rust carrier and not the Clean type: the Clean type is
    /// what the kernel reasoned about, the carrier is what the binary holds, and
    /// I4 exists because those two can disagree while defeq is satisfied.
    #[must_use]
    pub fn admitted_at(&self) -> &Ty {
        &self.admitted_at
    }

    /// How the kernel established agreement.
    #[must_use]
    pub fn method(&self) -> FaithfulnessMethod {
        self.method
    }
}

/// Why a lowered body was refused.
#[derive(Debug, Clone)]
pub enum GateRefusal {
    /// The kernel did not establish that `R(lowered)` agrees with the Clean
    /// `def` body.
    ///
    /// Definitional equality failed and the bounded induction engine completed
    /// without returning an accepted proof. This is not a mathematical
    /// counter-proof; on the emitted-body path, however, reaching it after a
    /// supported plan means the compiler failed to reproduce the agreement its
    /// own plan requires. Hard deadline/node/name rails use the distinct
    /// [`Self::ResourceExhausted`] variant.
    Disagreement {
        /// The declaration name.
        name: String,
        /// The Clean `def` body — side A.
        clean: String,
        /// `R(lowered)` — side B.
        lowered: String,
    },
    /// The optional structural-induction lane remained inconclusive because a
    /// hard resource rail was reached.
    ///
    /// This is distinct from [`Self::Disagreement`]: both refuse authority,
    /// but exhaustion does not establish that the lowering is wrong and must
    /// not be reported as a definite compiler mistranslation.
    ResourceExhausted {
        /// The declaration name.
        name: String,
        /// Which fixed rail stopped the decision. Constructed only from static,
        /// bounded text; no rejected expression is rendered here.
        limit: &'static str,
    },
    /// The declaration has no body in the kernel environment, so there is
    /// nothing to be faithful *to*.
    ///
    /// An axiom or opaque constant lands here. It must never be emitted: there
    /// is no definition for the binary to agree with.
    NoCleanBody {
        /// The declaration name.
        name: String,
    },
    /// Side A itself did not come from a full kernel check.
    ///
    /// `clean_kernel` distinguishes `FullKernelCheck` from `StructuralOnly` and
    /// `Unchecked` insertion paths. Comparing a lowered body against a
    /// structurally-inserted declaration would let the gate report agreement
    /// with a term the kernel never validated — the gate would be measuring the
    /// lowering against an unchecked reference and calling that faithfulness.
    SideANotKernelChecked {
        /// The declaration name.
        name: String,
        /// How the declaration actually entered the environment. `None` means
        /// the environment tracked no origin for it at all, which is refused
        /// for the same reason.
        verification: Option<DeclarationVerification>,
    },
    /// One defining equation failed kernel identification (per-defining-
    /// equation lane, §6e as amended). Carries WHICH case, because "some but
    /// not all equations hold" is the exact wrong-binary shape this lane
    /// exists to refuse (the strict-subset family of probes e1/e3/s3).
    EquationDisagreement {
        /// The declaration name.
        name: String,
        /// The constructor whose minor premise disagreed (`Nat.zero`,
        /// `Nat.succ`).
        case: String,
        /// Side A's minor premise, verbatim.
        clean: String,
        /// The reflected case term, verbatim.
        lowered: String,
    },
    /// The emitted self-call's argument is not definitionally the case
    /// binder — the recursion STRUCTURE disagrees even if every case value
    /// agrees. THE DIVERGENCE CATCH: probe s2 measures the constant-citing
    /// spelling ADMITTING an off-by-one (diverging) body, and probe s4
    /// measures this identity refusing the same body once the defined
    /// constant is out of the terms. See the §6e IMPLEMENTATION AMENDMENT.
    RecursionStructureDisagreement {
        /// The declaration name.
        name: String,
        /// The reflected self-call argument (as a one-binder function of the
        /// case binder), verbatim.
        lowered_arg: String,
    },
    /// Side A's value is not the recognised structural recursor spine (or is
    /// `WellFounded.fix`-headed): the per-defining-equation judgment does not
    /// apply, and nothing else may.
    NotStructuralRecursor {
        /// The declaration name.
        name: String,
        /// What was found instead.
        found: String,
    },
    /// The reflected equation set does not pair 1:1, in order, with the
    /// KERNEL's minor premises — completeness is decided against the kernel's
    /// own inductive/recursor declarations (probe s5's source), never against
    /// the emission.
    EquationSetMismatch {
        /// The declaration name.
        name: String,
        /// How many cases the reflection carried, and their constructor tags.
        reflected: String,
        /// What the kernel's recursor demands.
        required: String,
    },
    /// **THE R2 PRECONDITION.** A RECURSIVE declaration's verdict would have
    /// rested on assumptions the kernel did not discharge.
    ///
    /// This is the refusal the §6e MEASUREMENT NOTE's finding 2 demands. On a
    /// well-founded spine the kernel's TYPE CHECK is the termination
    /// evidence — `rec : (y : α) → r y x → C y`, so a diverging self-call
    /// needs a proof of `Nat.lt (succ x) x` that does not exist — and a
    /// single `axiom` in scope turns that guarantee off. The closure audit is
    /// therefore not a disclosure nicety on this lane; it is the other half
    /// of the termination argument.
    AssumptionBearingRecursion {
        /// The declaration name.
        name: String,
        /// What was audited, in operator-facing words ("the Clean definition
        /// of `f`", "the emitted functional for `f`", …).
        subject: String,
        /// The assumption names, disclosed individually.
        assumptions: Vec<String>,
        /// Certification-blocking findings that are not assumptions — an
        /// audit that did not COMPLETE is refused for the same reason, since
        /// an incomplete audit is not an empty closure.
        blocking: Vec<String>,
    },
    /// Side A's value is not the `WellFounded.fix` spine the R2 judgment is
    /// defined over.
    NotWellFoundedRecursor {
        /// The declaration name.
        name: String,
        /// What was found instead.
        found: String,
    },
    /// Side B's decrease slots could not be filled from side A's proof terms.
    ///
    /// Side B **may not author a decrease proof** — MIR contains none, and a
    /// proof side B authored is exactly the term whose axiom closure the gate
    /// would then be trusting. Every slot must arrive as the sentinel and be
    /// filled by borrowing, so this refusal covers: a slot count that does
    /// not match side A's, a slot at a different binder depth, a sentinel
    /// left unfilled, a self-call that is not a two-argument application of
    /// the recursive binder, and a borrowed proof that does not TYPE at side
    /// B's chosen argument (the last is the divergence catch — an emission
    /// recursing at a non-decreasing argument cannot accept side A's proof).
    DecreaseSlotBorrowRefused {
        /// The declaration name.
        name: String,
        /// Which of the above, in bounded static-shaped text.
        detail: String,
    },
    /// Side B's functional is not kernel-identified with side A's.
    ///
    /// The R2 analogue of [`Self::Disagreement`], stated at the F layer: the
    /// accessibility witness never enters the comparison, so a disagreement
    /// here is about the emitted VALUE or the recursive ARGUMENT, both of
    /// which the F carries and the witness does not.
    FunctionalDisagreement {
        /// The declaration name.
        name: String,
    },
}

impl GateRefusal {
    /// The declaration this refusal is about.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::Disagreement { name, .. }
            | Self::ResourceExhausted { name, .. }
            | Self::NoCleanBody { name }
            | Self::SideANotKernelChecked { name, .. }
            | Self::EquationDisagreement { name, .. }
            | Self::RecursionStructureDisagreement { name, .. }
            | Self::NotStructuralRecursor { name, .. }
            | Self::EquationSetMismatch { name, .. }
            | Self::AssumptionBearingRecursion { name, .. }
            | Self::NotWellFoundedRecursor { name, .. }
            | Self::DecreaseSlotBorrowRefused { name, .. }
            | Self::FunctionalDisagreement { name } => name,
        }
    }

    /// The operator-facing explanation.
    ///
    /// A gate refusal is **not** a failed user obligation and must not be
    /// phrased as one. It means the compiler could not establish emitted-code
    /// agreement: either reflection/lowering disagreed, or the bounded
    /// structural proof remained inconclusive. In both cases no body escapes.
    #[must_use]
    pub fn note(&self) -> String {
        match self {
            Self::Disagreement { name, clean, lowered } => format!(
                "the compiler did not establish that the lowered body for Clean-origin \
                 `{name}` agrees with its Clean definition, so no code was emitted.\n\
                 clean definition : {clean}\n\
                 lowered (via R)  : {lowered}\n\
                 This is a fail-closed compiler-correctness refusal, not a failed user \
                 theorem: definitional equality failed and no independently accepted \
                 induction proof established the emitted shape. Hard resource exhaustion \
                 is reported separately rather than being mislabeled as disagreement.\n\
                 options:\n\
                 - keep the general definition for proof position and call a smaller \
                   supported helper whose emitted equality is decidable within the bounds;\n\
                 - write the computation as Rust and prove its relation to `{name}` in a \
                   contract, which uses the ordinary obligation lane;\n\
                 - if `{name}` is already an advertised supported shape, report this \
                   compiler refusal with the declaration and trace.\n\
                 Term renderings are deliberately omitted because a rejected, user-sized \
                 term must not allocate an unbounded diagnostic."
            ),
            Self::ResourceExhausted { name, limit } => format!(
                "the compiler could not establish emitted-code faithfulness for \
                 Clean-origin `{name}` within its fixed resource envelope, so no \
                 code was emitted. The limiting rail was: {limit}. This is a \
                 fail-closed incomplete decision, not evidence that the Clean \
                 definition or the lowering is false.\n\
                 options:\n\
                 - keep the general definition for proof position and call a smaller \
                   supported helper whose equality fits the bounded fragment;\n\
                 - write the computation as Rust and prove its relation to `{name}` in \
                   a contract, which uses the ordinary obligation lane;\n\
                 - report this refusal if the declaration is already a small advertised \
                   shape, because that indicates unexpected resource use."
            ),
            Self::NoCleanBody { name } => format!(
                "`{name}` has no definition body in the Clean environment, so there is \
                 nothing for emitted code to agree with.\n\
                 An `axiom` or an opaque constant asserts a type without exhibiting a \
                 value; it can be cited in proof position but never called.\n\
                 options:\n\
                 - give `{name}` a definition (`def {name} … := …`) and it becomes \
                   callable if it also carries;\n\
                 - cite `{name}` from a contract instead of calling it."
            ),
            Self::SideANotKernelChecked { name, verification } => format!(
                "INTERNAL: the Clean definition of `{name}` did not enter the kernel \
                 environment through a full kernel check (origin: {verification:?}), so \
                 it cannot be used as the reference the emitted code is checked \
                 against.\n\
                 The faithfulness gate compares emitted code to a KERNEL-CHECKED \
                 definition. Against a structurally-inserted or unchecked declaration \
                 the comparison would report agreement with a term the kernel never \
                 validated. Refusing is the only sound answer. Please report it."
            ),
            Self::EquationDisagreement { name, case, clean, lowered } => format!(
                "INTERNAL: the recursive body emitted for Clean-origin `{name}` does not \
                 agree with its `{case}` defining equation, so no code was emitted.\n\
                 clean minor premise : {clean}\n\
                 reflected case      : {lowered}\n\
                 This is a compiler-correctness refusal, not a proof obligation: it means \
                 the Clean->Rust lowering mistranslated this case of `{name}`, or a side-B \
                 producer was modified against this lane. Nothing you can write at the \
                 call site changes it. Please report it — the two terms above are the \
                 whole reproduction."
            ),
            Self::RecursionStructureDisagreement { name, lowered_arg } => format!(
                "INTERNAL: the recursive body emitted for Clean-origin `{name}` recurses \
                 on the wrong argument, so no code was emitted.\n\
                 reflected self-call argument (as a function of the case binder): \
                 {lowered_arg}\n\
                 The kernel did not identify it with the case binder itself. This is the \
                 divergence catch: a body whose case VALUES all agree can still loop \
                 forever if its self-call argument is not the structurally smaller one, \
                 and the case-value checks cannot see that. This is a \
                 compiler-correctness refusal — nothing you can write at the call site \
                 changes it. Please report it."
            ),
            Self::NotStructuralRecursor { name, found } => format!(
                "INTERNAL: the per-defining-equation gate was asked to admit `{name}`, \
                 but its Clean value is not the structural recursor spine that judgment \
                 is defined over (found: {found}).\n\
                 The per-equation judgment is sound only for a `Nat.rec`-headed value of \
                 a fully kernel-checked definition, where the kernel's own recursor \
                 machinery is the termination evidence. Anything else must refuse here. \
                 A `WellFounded.fix`-headed value has its own lane — the F-LAYER \
                 comparison `check_faithful_wf_functional` (R2), which states no equation \
                 at all: kernel-checked equation lemmas are NOT R2's prerequisite \
                 (measured `r2_wf_equation_probes` w2/w4 — the defining equations are \
                 already definitional here and the one candidate unfolding lemma closes \
                 by `rfl`), and this refusal used to say otherwise. Please \
                 report it: the plan lane should never have routed this declaration \
                 here."
            ),
            Self::EquationSetMismatch { name, reflected, required } => format!(
                "INTERNAL: the reflected equation set for Clean-origin `{name}` does not \
                 pair one-to-one, in order, with the kernel's minor premises, so no code \
                 was emitted.\n\
                 reflected : {reflected}\n\
                 required  : {required}\n\
                 Completeness is decided against the kernel's own inductive declaration \
                 — never against the emission — so a lowering that dropped or invented a \
                 case is refused even if every case it DID reflect agrees. This is a \
                 compiler-correctness refusal. Please report it."
            ),
            Self::AssumptionBearingRecursion { name, subject, assumptions, blocking } => {
                let mut note = format!(
                    "`{name}` is a RECURSIVE Clean definition and no code was emitted for it, \
                     because {subject} does not rest on the kernel alone.\n"
                );
                if !assumptions.is_empty() {
                    note.push_str(&format!("assumptions reached: {}\n", assumptions.join(", ")));
                }
                if !blocking.is_empty() {
                    note.push_str(&format!(
                        "the audit could not complete: {}\n",
                        blocking.join("; ")
                    ));
                }
                note.push_str(
                    "Why this is refused HERE and not merely disclosed: a recursive Clean \
                     definition's TERMINATION is decided by the kernel's typing rule, and on a \
                     well-founded spine that rule is `rec : (y : a) -> r y x -> C y` — the \
                     recursive call must be handed a proof that its argument DECREASES. One \
                     assumed proof of a false decrease makes a non-terminating definition \
                     kernel-check and admit, and the emitted binary would then loop forever \
                     while the compiler reported agreement. So on this lane an audited-empty \
                     axiom closure is not a disclosure preference; it is the other half of the \
                     termination evidence.\n\
                     The rule is the same one that governs the DefId mint (an audited-empty \
                     closure or no callable name); it is applied again here because a recursive \
                     body's assumptions can sit in a proof slot that no declaration-level check \
                     of the emitted term ever looks at.\n\
                     options:\n\
                     - discharge the listed assumptions and the call becomes available with no \
                       other change;\n\
                     - keep them and cite the definition from PROOF position instead, where the \
                       axiom closure is disclosed BY NAME rather than compiled into a binary;\n\
                     - restate the recursion structurally: a `Nat.rec`-shaped definition needs \
                       no decrease proof at all, so no assumption can enter its termination \
                       argument;\n\
                     - if an assumption is a deliberate domain axiom, state it on the Rust side \
                       as a contract, so the obligation is visible to every caller instead of \
                       being sealed inside emitted code;\n\
                     - if the finding above is a NON-assumption one (a structurally-inserted or \
                       unchecked dependency, a staged header, a dependency cycle), route that \
                       dependency through a full kernel check — an incomplete audit is \
                       deliberately not treated as an empty one.",
                );
                note
            }
            Self::NotWellFoundedRecursor { name, found } => format!(
                "INTERNAL: the well-founded functional gate was asked to admit `{name}`, but its \
                 Clean value is not the `WellFounded.fix` spine that judgment is defined over \
                 (found: {found}).\n\
                 The R2 judgment is (a) side A's spine parses as \
                 `@WellFounded.fix.{{1,1}} a C r hwf F x` with `x` the parameter, (b) side B's \
                 `F` kernel-checks at side A's `F` type with an audited-empty axiom closure, and \
                 (c) the two `F`s are kernel-defeq. A value with any other head has no `F` to \
                 compare, so nothing may admit it here.\n\
                 options:\n\
                 - route a `Nat.rec`-headed value to the per-defining-equation lane instead;\n\
                 - route a non-recursive value to the whole-term lane instead;\n\
                 - report this refusal: the plan lane should never have routed this declaration \
                   here."
            ),
            Self::DecreaseSlotBorrowRefused { name, detail } => format!(
                "INTERNAL: the emitted functional for Clean-origin `{name}` could not take side \
                 A's decrease proofs, so no code was emitted ({detail}).\n\
                 Side B does not author decrease proofs. MIR contains none, and a proof side B \
                 authored would be precisely the term whose axiom closure decides whether the \
                 recursion terminates — the gate would then be trusting a term the emitter \
                 wrote. Every recursive call must therefore arrive with the slot sentinel and \
                 receive side A's own proof by borrowing. That costs nothing in checking power: \
                 two functionals differing only in which proof fills the slot are definitionally \
                 equal, so the proof is never what the comparison decides.\n\
                 A borrow that does not TYPE is the divergence catch doing its job: an emission \
                 that recurses on a non-decreasing argument cannot be handed side A's proof that \
                 the argument decreases.\n\
                 options:\n\
                 - if the emission recursed on a different argument than the declaration, that \
                   is a lowering defect — report it with the declaration;\n\
                 - if the declaration's recursive structure is outside the single-slot shape \
                   this lane parses, keep it for proof position and call a supported helper;\n\
                 - report this refusal: nothing you can write at the call site changes it."
            ),
            Self::FunctionalDisagreement { name } => format!(
                "INTERNAL: the emitted functional for Clean-origin `{name}` is not definitionally \
                 equal to the one in its Clean definition, so no code was emitted.\n\
                 The comparison is made at the FUNCTIONAL layer, where the recursive slot is an \
                 abstract binder on both sides and no accessibility witness appears at all — so \
                 this disagreement is about the emitted VALUE or the recursive ARGUMENT, both of \
                 which the functional carries. A well-typed, genuinely terminating recursion on \
                 the WRONG argument lands here rather than in the borrow refusal, because typing \
                 cannot see it and definitional equality can.\n\
                 Term renderings are omitted: a rejected, user-sized term must not allocate an \
                 unbounded diagnostic.\n\
                 This is a compiler-correctness refusal, not a failed user theorem. Nothing you \
                 can write at the call site changes it. Please report it."
            ),
        }
    }
}

/// The faithfulness gate.
///
/// Decides, by kernel definitional equality or a closed axiom-free structural
/// induction proof **at the carrier type**, whether a lowered Clean-origin body
/// may be emitted for `name`.
///
/// * `env` — the kernel environment holding the Clean `def`.
/// * `name` — the declaration being emitted.
/// * `reflected_lowering` — side B: the lowered body reflected back into Clean
///   by the **frozen** R functor. This crate never produces it; producing it is
///   the lowering's job, and R must not be edited to make it agree.
/// * `carrier` — I4's total carrier. Its mere existence is the representation
///   evidence; its Rust type is what the agreement is admitted at.
///
/// # Errors
///
/// Returns [`GateRefusal`] when the Clean declaration has no body, or when the
/// kernel does not identify the two sides. Both refuse emission outright: there
/// is no degraded mode in which a disagreeing body is emitted with a warning.
pub fn check_faithful(
    env: &Environment,
    name: &str,
    reflected_lowering: &Expr,
    carrier: &Carrier,
) -> Result<Faithful, GateRefusal> {
    check_faithful_impl(env, name, reflected_lowering, carrier, None)
}

/// The crate-internal form used by declaration-wide candidate discovery.
/// Its caller supplies one ABSOLUTE shared deadline, so multiple candidates
/// and every phase around automation cannot each acquire a fresh allowance.
pub(crate) fn check_faithful_with_deadline(
    env: &Environment,
    name: &str,
    reflected_lowering: &Expr,
    carrier: &Carrier,
    deadline: Instant,
) -> Result<Faithful, GateRefusal> {
    check_faithful_impl(env, name, reflected_lowering, carrier, Some(deadline))
}

fn check_faithful_impl(
    env: &Environment,
    name: &str,
    reflected_lowering: &Expr,
    carrier: &Carrier,
    shared_deadline: Option<Instant>,
) -> Result<Faithful, GateRefusal> {
    let kernel_name = Name::from_string(name);

    let deadline_refusal = || GateRefusal::ResourceExhausted {
        name: name.to_owned(),
        limit: "the declaration-wide two-second structural-proof deadline expired",
    };
    if shared_deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return Err(deadline_refusal());
    }

    // Side A's PROVENANCE, before its content. A declaration that entered the
    // environment structurally or unchecked is not a kernel verdict, and
    // agreement with it is not faithfulness.
    match env.declaration_verification(&kernel_name) {
        Some(DeclarationVerification::FullKernelCheck) => {}
        verification => {
            return Err(GateRefusal::SideANotKernelChecked { name: name.to_owned(), verification });
        }
    }

    // Side A: the Clean `def`'s own body. Read from the environment, never from
    // the lowering — this is what makes the comparison non-circular.
    let Some(clean_body) = clean_definition_body(env, &kernel_name) else {
        return Err(GateRefusal::NoCleanBody { name: name.to_owned() });
    };
    if shared_deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return Err(deadline_refusal());
    }

    // THE RECURSIVE PRECONDITION (the §6e MEASUREMENT NOTE, finding 2).
    // Probe w8 measured that this WHOLE-TERM lane admits a `WellFounded.fix`
    // side A today, so it is a recursive-`Faithful`-minting lane whether or
    // not it was designed as one, and the escape is reachable through it. See
    // `require_recursion_rests_on_the_kernel`.
    if side_a_is_recursive(&clean_body) {
        require_recursion_rests_on_the_kernel(env, name, &kernel_name)?;
    }
    if shared_deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return Err(deadline_refusal());
    }

    let type_checker = TypeChecker::new(env);

    // `is_def_eq` is two-valued; an exhausted decision reports `false`, so its
    // public heartbeat state is inspected immediately before `false` can mean
    // completed disagreement. A symbolic recursor can be extensionally equal
    // while remaining stuck under reduction, so the one fallback is a REAL
    // structural-induction proof. Search is not authority:
    // `prove_by_structural_induction` checks the returned term again with this
    // kernel and audits its theorem closure.
    let is_def_eq = type_checker.is_def_eq(&clean_body, reflected_lowering);
    if type_checker.heartbeat_spent() {
        return Err(GateRefusal::ResourceExhausted {
            name: name.to_owned(),
            limit: KERNEL_HEARTBEAT_ENVELOPE,
        });
    }
    if shared_deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return Err(deadline_refusal());
    }
    let induction_deadline = shared_deadline.unwrap_or_else(|| Instant::now() + INDUCTION_TIMEOUT);
    let method = if is_def_eq {
        FaithfulnessMethod::DefinitionalEquality
    } else {
        match prove_by_structural_induction(
            env,
            &kernel_name,
            &clean_body,
            reflected_lowering,
            carrier,
            induction_deadline,
        ) {
            Ok(true) => FaithfulnessMethod::StructuralInduction,
            Ok(false) => {
                return Err(GateRefusal::Disagreement {
                    name: name.to_owned(),
                    clean: "<kernel-checked Clean body; unbounded rendering omitted>".to_owned(),
                    lowered: "<reflected lowering; unbounded rendering omitted>".to_owned(),
                });
            }
            Err(limit) => {
                return Err(GateRefusal::ResourceExhausted { name: name.to_owned(), limit });
            }
        }
    };

    Ok(Faithful { name: name.to_owned(), admitted_at: carrier.rust().clone(), method })
}

/// Prove the extensional equality of two closed function bodies by structural
/// induction, then independently re-check and audit the returned proof.
///
/// This fallback is deliberately narrower than “ask automation whether the
/// bodies look equivalent”:
///
/// * the declaration must have the same total, non-dependent carrier
///   signature the emission lane uses;
/// * the proposition is the closed statement `forall args, clean args =
///   lowered args`, constructed here from both independently produced bodies;
/// * `clean-auto` may only propose a proof term;
/// * `clean-kernel` checks that term against the exact proposition; and
/// * inserting it as a theorem in a scratch environment must yield no
///   non-foundational domain/trust assumptions under `axiom_deps`.
///
/// A completed search with no valid proof returns `Ok(false)`. Deadline,
/// expression-envelope, and bounded audit-namespace exhaustion return a typed
/// resource refusal. Every path refuses emission; none weakens the authority
/// condition.
fn prove_by_structural_induction(
    env: &Environment,
    kernel_name: &Name,
    clean_body: &Expr,
    reflected_lowering: &Expr,
    carrier: &Carrier,
    deadline: Instant,
) -> Result<bool, &'static str> {
    const DEADLINE: &str = "the declaration-wide two-second structural-proof deadline expired";
    const EXPRESSION_ENVELOPE: &str =
        "a signature, Clean body, reflected lowering, goal, or proof exceeded 4,096 core nodes";
    const ARITY_ENVELOPE: &str =
        "the structural-induction signature exceeded eight quantified parameters";
    // (The former `AUDIT_NAMESPACE` rail is gone with the scratch-clone idiom:
    // `crate::closure` audits the `(goal, proof)` pair in place and needs no
    // temporary declaration name at all.)

    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    let body_contains_recursor = bounded_core_scan(clean_body).ok_or(EXPRESSION_ENVELOPE)?;
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    if bounded_core_scan(reflected_lowering).is_none() {
        return Err(EXPRESSION_ENVELOPE);
    }
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    let Some(info) = env.get_const(kernel_name) else {
        return Ok(false);
    };
    if bounded_core_scan(&info.type_).is_none() {
        return Err(EXPRESSION_ENVELOPE);
    }
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    let Ok(signature) = carrier_signature_for(&info.type_) else {
        return Ok(false);
    };
    if signature.arity() > INDUCTION_MAX_ARITY {
        return Err(ARITY_ENVELOPE);
    }
    if signature.arity() == 0 || signature.result().rust() != carrier.rust() {
        return Ok(false);
    }

    // The carrier table currently models value types in `Type` (Sort 1).
    // Build the quantified equality without reducing either side. Under `n`
    // binders, source argument i is BVar(n-1-i).
    let mut domains = Vec::with_capacity(signature.arity());
    let mut result_ty = &info.type_;
    while let ExprKind::Pi(_, domain, body) = result_ty.kind() {
        domains.push((**domain).clone());
        result_ty = body;
    }
    if domains.len() != signature.arity() || result_ty.has_loose_bvars_quick() {
        return Ok(false);
    }
    let Ok(arity) = u32::try_from(domains.len()) else {
        return Ok(false);
    };
    let args: Vec<Expr> = (0..arity).map(|i| Expr::bvar(arity - 1 - i)).collect();
    // Present automation the extensional proposition, not two beta-redex
    // wrappers. The kernel checks the returned proof against this exact
    // normalized goal, so WHNF is only a deterministic adapter step—not proof
    // authority. Without it, the induction matcher sees `(fun .. => ..) x`
    // at the equality heads and declines even the canonical `0 + n = n`
    // control that its direct API proves.
    let type_checker = TypeChecker::new(env);
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    let clean_app = type_checker.whnf(&Expr::apps(clean_body.clone(), args.iter().cloned()));
    if type_checker.heartbeat_spent() {
        return Err(KERNEL_HEARTBEAT_ENVELOPE);
    }
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    let lowered_app = type_checker.whnf(&Expr::apps(reflected_lowering.clone(), args));
    if type_checker.heartbeat_spent() {
        return Err(KERNEL_HEARTBEAT_ENVELOPE);
    }
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    // A source definition may delegate to a checked recursive definition such
    // as `Nat.add`; the lambda itself then contains no literal `.rec`, while
    // its bounded symbolic WHNF exposes the actual recursor. Require it on the
    // Clean side (never merely on the candidate lowering), and scan the whole
    // normalized term before allowing automation.
    let applied_contains_recursor = bounded_core_scan(&clean_app).ok_or(EXPRESSION_ENVELOPE)?;
    if !body_contains_recursor && !applied_contains_recursor {
        return Ok(false);
    }
    if bounded_core_scan(&lowered_app).is_none() {
        return Err(EXPRESSION_ENVELOPE);
    }
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    let mut goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [result_ty.clone(), clean_app, lowered_app],
    );
    for domain in domains.into_iter().rev() {
        goal = Expr::pi(BinderInfo::Default, domain, goal);
    }
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    if bounded_core_scan(&goal).is_none() {
        return Err(EXPRESSION_ENVELOPE);
    }

    let engine = AutomationEngine::new();
    let Some(remaining) = deadline.checked_duration_since(Instant::now()) else {
        return Err(DEADLINE);
    };
    if remaining.is_zero() {
        return Err(DEADLINE);
    }
    let Some(proof) = engine.prove_by_induction(env, &goal, remaining) else {
        return if Instant::now() >= deadline { Err(DEADLINE) } else { Ok(false) };
    };
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    if bounded_core_scan(proof.proof_term()).is_none() {
        return Err(EXPRESSION_ENVELOPE);
    }
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    if proof.proof_context().is_some() {
        return Ok(false);
    }
    let proof_checker = TypeChecker::new(env);
    let kernel_result = proof_checker.check_type(proof.proof_term(), &goal);
    if proof_checker.heartbeat_spent() {
        return Err(KERNEL_HEARTBEAT_ENVELOPE);
    }
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    if kernel_result.is_err() {
        return Ok(false);
    }

    // A kernel-typed proof can still cite an axiom. Route the closure question
    // through the crate's ONE audit ([`crate::closure`]).
    //
    // This used to install the proof as a theorem in a CLONE of the
    // environment under a bounded fresh name and then read
    // `Environment::axiom_deps`. That idiom is strictly weaker than what it
    // was taken to mean: `axiom_deps` returns a NAME LIST and never
    // re-typechecks, so it cannot see a structurally-inserted, unchecked,
    // value-less, staged or non-canonically-founded dependency —
    // `trust_symbols::AxiomClosure` says in terms that a producer holding only
    // `axiom_deps` must record `unrecorded`, and the kernel calls it "the
    // legacy `axiom_deps(name)` pattern" in `audit_certification`'s own
    // documentation. The `(goal, proof)` pair this lane already holds is
    // exactly `audit_certification`'s argument shape, so the stronger walker
    // is a direct substitution — and it removes the 32-name scratch-namespace
    // rail with it.
    let audit = crate::closure::audit_proof_closure(
        env,
        "the structural-induction proof of emitted-code faithfulness",
        &goal,
        proof.proof_term(),
    );
    if Instant::now() >= deadline {
        return Err(DEADLINE);
    }
    Ok(audit.is_clear())
}

/// Scan the CORE expression fragment with a hard node/stack envelope.
///
/// `Some(true)` means a recursive eliminator was found, `Some(false)` means a
/// bounded core term without one, and `None` means either the node rail or an
/// extension expression was reached. Extensions are outside this fallback's
/// measured Nat-recursion fragment and therefore refuse rather than acquiring
/// an accidentally unbounded traversal.
fn bounded_core_scan(expr: &Expr) -> Option<bool> {
    let mut pending = Vec::with_capacity(32);
    pending.push(expr);
    let mut visited = 0usize;
    let mut found_recursor = false;

    while let Some(current) = pending.pop() {
        visited = visited.checked_add(1)?;
        if visited > INDUCTION_EXPR_NODE_LIMIT || pending.len() > INDUCTION_EXPR_NODE_LIMIT {
            return None;
        }
        match current.kind() {
            ExprKind::Const(name, _) => found_recursor |= is_recursive_eliminator(name),
            ExprKind::App(function, argument) => {
                pending.push(argument);
                pending.push(function);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                pending.push(body);
                pending.push(ty);
            }
            ExprKind::Let(_, ty, value, body, _) => {
                pending.push(body);
                pending.push(value);
                pending.push(ty);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                pending.push(inner);
            }
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Lit(_)
            | ExprKind::SProp => {}
            ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1
            | ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. }
            | ExprKind::ZFCSet(_)
            | ExprKind::ZFCMem { .. }
            | ExprKind::ZFCComprehension { .. } => return None,
        }
        if pending.len() > INDUCTION_EXPR_NODE_LIMIT {
            return None;
        }
    }
    Some(found_recursor)
}

/// Inspect the terminal name components without allocating a flattened string
/// proportional to an attacker-controlled name chain.
fn is_recursive_eliminator(name: &Name) -> bool {
    match name.inner() {
        NameInner::Str(_, terminal) if terminal.as_ref() == "rec" => true,
        NameInner::Str(parent, terminal) if terminal.as_ref() == "fix" => {
            matches!(
                parent.inner(),
                NameInner::Str(grandparent, component)
                    if component.as_ref() == "WellFounded" && grandparent.is_anon()
            )
        }
        NameInner::Anon | NameInner::Str(_, _) | NameInner::Num(_, _) => false,
    }
}

#[cfg(test)]
mod bounded_scan_tests {
    use clean_kernel::Declaration;
    use trust_types::Ty;

    use super::*;

    fn mdata_chain(total_nodes: usize, leaf: Expr) -> Expr {
        assert!(total_nodes >= 1);
        (1..total_nodes).fold(leaf, |inner, _| Expr::mdata(Vec::new(), inner))
    }

    #[test]
    fn scanner_accepts_4096_nodes_and_refuses_4097() {
        let at_limit = mdata_chain(
            INDUCTION_EXPR_NODE_LIMIT,
            Expr::const_(Name::from_string("Nat.rec"), vec![]),
        );
        assert_eq!(bounded_core_scan(&at_limit), Some(true));

        let over_limit = mdata_chain(
            INDUCTION_EXPR_NODE_LIMIT + 1,
            Expr::const_(Name::from_string("Nat.rec"), vec![]),
        );
        assert_eq!(bounded_core_scan(&over_limit), None);
    }

    #[test]
    fn finding_recursor_first_does_not_hide_an_oversized_or_extension_tail() {
        let oversized_tail = mdata_chain(INDUCTION_EXPR_NODE_LIMIT + 1, Expr::bvar(0));
        let recursor_then_oversized =
            Expr::app(Expr::const_(Name::from_string("Nat.rec"), vec![]), oversized_tail);
        assert_eq!(bounded_core_scan(&recursor_then_oversized), None);

        let recursor_then_extension = Expr::app(
            Expr::const_(Name::from_string("Nat.rec"), vec![]),
            Expr::from_kind(ExprKind::CubicalInterval),
        );
        assert_eq!(bounded_core_scan(&recursor_then_extension), None);
    }

    #[test]
    fn bounded_symbolic_whnf_exposes_checked_delegated_recursion() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat.add and Nat.rec fixture");
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let body = Expr::lam(
            BinderInfo::Default,
            nat,
            Expr::apps(
                Expr::const_(Name::from_string("Nat.add"), vec![]),
                [Expr::const_(Name::from_string("Nat.zero"), vec![]), Expr::bvar(0)],
            ),
        );

        assert_eq!(
            bounded_core_scan(&body),
            Some(false),
            "the wrapper itself names Nat.add, not the recursor it delegates to"
        );
        let applied = TypeChecker::new(&env).whnf(&Expr::app(body, Expr::bvar(0)));
        assert_eq!(
            bounded_core_scan(&applied),
            Some(true),
            "bounded symbolic WHNF must expose the checked Nat.rec implementation"
        );
    }

    #[test]
    fn an_expired_absolute_deadline_refuses_before_even_defeq() {
        let uint64 = Expr::const_(Name::from_string("UInt64"), vec![]);
        let body = Expr::lam(BinderInfo::Default, uint64.clone(), Expr::bvar(0));
        let mut env = Environment::new();
        env.init_uint_arith().expect("fixture prelude");
        env.add_decl(Declaration::Definition {
            name: Name::from_string("identity"),
            level_params: vec![],
            type_: Expr::arrow(uint64.clone(), uint64.clone()),
            value: body.clone(),
            is_reducible: true,
        })
        .expect("fixture definition");
        let carrier =
            trust_clean_carrier::carrier_at(&uint64, &Ty::u64()).expect("exact UInt64 carrier");

        let refusal =
            check_faithful_with_deadline(&env, "identity", &body, &carrier, Instant::now())
                .expect_err("an expired declaration deadline cannot be refreshed by defeq");
        assert!(matches!(refusal, GateRefusal::ResourceExhausted { .. }));
        assert!(refusal.note().contains("fail-closed incomplete decision"));
        assert!(
            !crate::emit::EmitRefusal::Gate(refusal).is_compiler_defect(),
            "resource exhaustion must not receive the definite-mistranslation headline"
        );
    }

    #[test]
    fn spent_kernel_heartbeat_is_a_resource_rail_not_a_disagreement() {
        let env = Environment::new();
        let mut checker = TypeChecker::new(&env);
        checker.set_heartbeat_limit(1);

        // The first result-returning kernel operation consumes the deliberately
        // tiny budget. This is anti-vacuous: the public probe must report the
        // spent state that non-Result `is_def_eq`/`whnf` callers need to inspect.
        let _ = checker.infer_type(&Expr::sort(Level::zero()));
        assert!(checker.heartbeat_spent());

        let refusal = GateRefusal::ResourceExhausted {
            name: "heartbeat_control".to_owned(),
            limit: KERNEL_HEARTBEAT_ENVELOPE,
        };
        assert!(refusal.note().contains("heartbeat"));
        assert!(
            !crate::emit::EmitRefusal::Gate(refusal).is_compiler_defect(),
            "an inconclusive kernel budget must not be reported as a completed mismatch"
        );
    }
}

/// The body of the `def` named `name`, or `None` when it has none.
///
/// `None` covers unknown names, axioms, **theorems** and **opaque** constants
/// alike — all are "nothing to be faithful to", and the gate refuses them
/// identically.
///
/// The `ConstantKind` filter is not redundant with the `value.is_some()` check.
/// A `Theorem` carries a proof term in `value`, and proof terms are
/// proof-irrelevant — the kernel will happily identify two different proofs of
/// the same proposition. Emitting code "faithful to" a proof term would be
/// emitting a value for something that has no computational content. An
/// `Opaque` constant likewise has a value that is deliberately not exposed to
/// reduction, so a defeq comparison against it is not the comparison it appears
/// to be.
fn clean_definition_body(env: &Environment, name: &Name) -> Option<Expr> {
    let constant = env.get_const(name)?;
    if constant.kind != ConstantKind::Definition {
        return None;
    }
    constant.value.clone()
}

// ───────────────────────────────────────────────────────────────────────────
// The per-defining-equation lane (structural recursion, §6e AS AMENDED)
// ───────────────────────────────────────────────────────────────────────────

/// One reflected case of a structural-recursion emission: the constructor it
/// claims to cover, and the case term with the recursive RESULT held abstract
/// as the recursor's own `ih` binder.
///
/// For `Nat`: the `Nat.zero` case is a closed term of the result type; the
/// `Nat.succ` case is `fun (k : Nat) (ih : Res) => …` — the same binder shape
/// as the recursor's minor premise, which is exactly what makes the per-case
/// comparison a comparison of the two step FUNCTIONS with nothing to unfold
/// (probe s3).
#[derive(Debug, Clone)]
pub struct ReflectedCase {
    /// The constructor this case claims to cover, by kernel name
    /// (`Nat.zero`, `Nat.succ`). Paired against the KERNEL's recursor rules,
    /// in order — a claim, re-decided by [`check_faithful_equations`].
    pub constructor: String,
    /// The reflected case term.
    pub value: Expr,
}

/// Side B for a structural-recursion emission, minted by
/// `crate::reflect_rec::reflect_structural_rec` from the EMITTED body's own
/// dataflow. **The defined constant is cited NOWHERE in these terms** — that
/// is what closes both the circularity (probe r1) and the vacuity (probe s2)
/// of the constant-citing spelling, per the §6e IMPLEMENTATION AMENDMENT.
///
/// Fields are public so the mutation controls can hand the gate adversarial
/// trios directly (the smuggle-past-structural control). That costs no
/// authority: this struct is a CLAIM, and every part of it is re-decided
/// against the kernel by [`check_faithful_equations`] — which is the only
/// place a [`Faithful`] can come from.
#[derive(Debug, Clone)]
pub struct ReflectedStructuralRec {
    /// One reflected case per claimed constructor, in declaration order.
    /// Completeness against the KERNEL's minor-premise count is the gate's
    /// decision, never this struct's.
    pub cases: Vec<ReflectedCase>,
    /// `fun (k : Nat) => <reflected self-call ARGUMENT under the succ-case
    /// substitution>`. For a correct emission this is
    /// `fun k => Nat.sub (Nat.succ k) 1`, which the kernel identifies with
    /// `fun k => k` (probe s6); the off-by-one emission reflects to
    /// `fun k => Nat.succ k`, which it refuses (probe s4).
    pub rec_arg: Expr,
}

/// The faithfulness gate for STRUCTURAL-RECURSION emissions — `Faithful` by
/// per-defining-equation kernel defeq, exactly the judgment the §6e
/// IMPLEMENTATION AMENDMENT records:
///
/// 1. **per-minor-premise defeq with the recursive result held ABSTRACT** —
///    each reflected case against side A's corresponding minor premise, the
///    defined constant appearing nowhere in side B (probes s2/s3: the
///    constant-citing spelling is VACUOUS — it admits a diverging off-by-one
///    body — and the abstract-ih form is decidable with nothing to unfold);
/// 2. **the kernel-checked recursive-argument identity** — the reflected
///    self-call argument, as a function of the case binder, must be
///    definitionally the case binder (probe s4: `sub (succ k) 1 ≡ k` admits,
///    `succ k ≢ k` refuses — THE divergence catch, and what lets side A's
///    kernel termination evidence transfer to the emitted body);
/// 3. **equation-set completeness against the kernel's own declarations** —
///    one reflected case per minor premise, no more, no fewer, paired in
///    order with the recursor's rules, all read from the kernel environment
///    and never from the emission (probe s5).
///
/// Side A is read by THIS function's own recursor-spine parse
/// ([`parse_nat_rec_minors`]) — deliberately independent of the plan lane's
/// recogniser, the same double-read rationale as the provenance re-check: the
/// gate must rest on its own reading of side A. That parse doubles as the
/// termination evidence at the gate layer: a `Nat.rec`-headed value of a
/// `FullKernelCheck` declaration is total by the kernel's own recursor
/// machinery (iota over `RecursorRule`s, strict positivity); a
/// `WellFounded.fix`-headed value refuses here — its lane is
/// [`check_faithful_wf_functional`] (R2), whose judgment is the F-layer
/// comparison and needs no equation lemma at all.
///
/// # Errors
///
/// [`GateRefusal`], every path fail-closed; `is_def_eq` is two-valued and a
/// budget-exhausted decision refuses, exactly as in [`check_faithful`].
pub fn check_faithful_equations(
    env: &Environment,
    name: &str,
    reflected: &ReflectedStructuralRec,
    carrier: &Carrier,
) -> Result<Faithful, GateRefusal> {
    let kernel_name = Name::from_string(name);

    // 1. Side A's PROVENANCE, identical to `check_faithful`.
    match env.declaration_verification(&kernel_name) {
        Some(DeclarationVerification::FullKernelCheck) => {}
        verification => {
            return Err(GateRefusal::SideANotKernelChecked { name: name.to_owned(), verification });
        }
    }

    // 2. Side A's body, from the environment, never from the lowering.
    let Some(clean_body) = clean_definition_body(env, &kernel_name) else {
        return Err(GateRefusal::NoCleanBody { name: name.to_owned() });
    };

    // 2b. THE RECURSIVE PRECONDITION (the §6e MEASUREMENT NOTE, finding 2).
    //     This lane mints a RECURSIVE `Faithful` by construction, so the rule
    //     applies to every call: no recursive `Faithful` while the closure is
    //     non-empty or unaudited. Structural recursion has no decrease slot to
    //     poison — `Nat.rec`'s `ih` erases the argument and carries no proof —
    //     but the audited-empty rule already governs DECLARATIONS (that is
    //     `mint::decide_mint`'s second precondition), and a `Nat.rec`-headed
    //     definition whose VALUE cites an axiom is exactly such a declaration.
    //     Refusing here keeps the two lanes from disagreeing about the same
    //     declaration.
    require_recursion_rests_on_the_kernel(env, name, &kernel_name)?;

    // 3. The gate's OWN spine parse — side A's minor premises.
    let minors = parse_nat_rec_minors(env, name, &clean_body)?;

    // 4. COMPLETENESS, against the kernel's own declarations (probe s5's
    //    source). The inductive and the recursor must agree with each other
    //    (a kernel self-consistency read), and the reflection must pair 1:1,
    //    in order, with the recursor's rules.
    let inductive = env.get_inductive(&Name::from_string("Nat")).ok_or_else(|| {
        GateRefusal::NotStructuralRecursor {
            name: name.to_owned(),
            found: "an environment with no `Nat` inductive declaration".to_owned(),
        }
    })?;
    let recursor = env.get_recursor(&Name::from_string("Nat.rec")).ok_or_else(|| {
        GateRefusal::NotStructuralRecursor {
            name: name.to_owned(),
            found: "an environment with no `Nat.rec` recursor".to_owned(),
        }
    })?;
    let num_minors = usize::try_from(recursor.num_minors).unwrap_or(usize::MAX);
    if inductive.constructor_names.len() != num_minors
        || recursor.rules.len() != num_minors
        || minors.len() != num_minors
    {
        return Err(GateRefusal::NotStructuralRecursor {
            name: name.to_owned(),
            found: format!(
                "a kernel environment whose Nat declarations disagree with themselves \
                 ({} constructors, num_minors {}, {} rules, {} spine minors)",
                inductive.constructor_names.len(),
                recursor.num_minors,
                recursor.rules.len(),
                minors.len()
            ),
        });
    }
    let required = || -> String {
        let names: Vec<String> =
            recursor.rules.iter().map(|rule| rule.constructor_name.to_string()).collect();
        format!("{num_minors} case(s), in order: {}", names.join(", "))
    };
    if reflected.cases.len() != num_minors {
        return Err(GateRefusal::EquationSetMismatch {
            name: name.to_owned(),
            reflected: format!(
                "{} case(s): {}",
                reflected.cases.len(),
                reflected
                    .cases
                    .iter()
                    .map(|case| case.constructor.clone())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            required: required(),
        });
    }
    for (case, rule) in reflected.cases.iter().zip(recursor.rules.iter()) {
        if case.constructor != rule.constructor_name.to_string() {
            return Err(GateRefusal::EquationSetMismatch {
                name: name.to_owned(),
                reflected: format!("a case claiming `{}`", case.constructor),
                required: required(),
            });
        }
    }

    let type_checker = TypeChecker::new(env);

    // 5. PER-MINOR-PREMISE DEFEQ, recursive result abstract on BOTH sides
    //    (side A's own minor binders vs the reflection's) — no `f` anywhere,
    //    so the s2 vacuity is impossible by construction.
    for (case, minor) in reflected.cases.iter().zip(minors.iter()) {
        if !type_checker.is_def_eq(&case.value, minor) {
            return Err(GateRefusal::EquationDisagreement {
                name: name.to_owned(),
                case: case.constructor.clone(),
                clean: format!("{minor:?}"),
                lowered: format!("{:?}", case.value),
            });
        }
    }

    // 6. THE RECURSIVE-ARGUMENT IDENTITY — the divergence catch (probe s4).
    let case_binder = Expr::lam(BinderInfo::Default, nat_const(), Expr::bvar(0));
    if !type_checker.is_def_eq(&reflected.rec_arg, &case_binder) {
        return Err(GateRefusal::RecursionStructureDisagreement {
            name: name.to_owned(),
            lowered_arg: format!("{:?}", reflected.rec_arg),
        });
    }

    Ok(Faithful {
        name: name.to_owned(),
        admitted_at: carrier.rust().clone(),
        method: FaithfulnessMethod::PerEquationDefeq,
    })
}

fn nat_const() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// The gate's OWN parse of a structural side A: peel exactly one lambda over
/// `Nat`, then require the recursor spine
/// `@Nat.rec.{1} (fun _ => Nat) m_0 … m_{k-1} (bvar 0)` — the measured island
/// output shape (`recursion_boundary_probes` r3; the motive body is required
/// to be `Nat` because this slice's judgment is stated at the Nat result
/// only). Deliberately duplicated from the plan lane's recogniser: the gate
/// must rest on its own reading of side A.
///
/// Returns the minor premises in rule order. A `WellFounded.fix`-headed value
/// (or anything else) refuses with [`GateRefusal::NotStructuralRecursor`].
fn parse_nat_rec_minors(
    env: &Environment,
    name: &str,
    body: &Expr,
) -> Result<Vec<Expr>, GateRefusal> {
    let refuse =
        |found: String| GateRefusal::NotStructuralRecursor { name: name.to_owned(), found };
    let is_nat = |expr: &Expr| {
        matches!(gate_strip_mdata(expr).kind(), ExprKind::Const(n, levels)
            if *n == Name::from_string("Nat") && levels.is_empty())
    };

    let cursor = gate_strip_mdata(body);
    let ExprKind::Lam(_, param_ty, inner) = cursor.kind() else {
        return Err(refuse(format!("a value that is not a one-parameter lambda: {cursor:?}")));
    };
    if !is_nat(param_ty) {
        return Err(refuse("a lambda over a non-Nat parameter".to_owned()));
    }

    // Uncurry the application spine.
    let mut head = gate_strip_mdata(inner);
    let mut args: Vec<&Expr> = Vec::new();
    while let ExprKind::App(function, argument) = head.kind() {
        args.push(gate_strip_mdata(argument));
        head = gate_strip_mdata(function);
    }
    args.reverse();

    let ExprKind::Const(head_name, head_levels) = head.kind() else {
        return Err(refuse(format!("a non-constant application head: {head:?}")));
    };
    if *head_name == Name::from_string("WellFounded.fix") {
        return Err(refuse(
            "a `WellFounded.fix` application — well-founded recursion is judged by the \
             F-layer lane `check_faithful_wf_functional` (R2), never by a per-equation \
             comparison against recursor minor premises, of which a fix spine has none"
                .to_owned(),
        ));
    }
    if *head_name != Name::from_string("Nat.rec")
        || head_levels.as_slice() != [Level::succ(Level::zero())]
    {
        return Err(refuse(format!("an application headed by `{head_name}`")));
    }

    // The KERNEL's minor count decides the spine arity: motive + minors + major.
    let num_minors = env
        .get_recursor(&Name::from_string("Nat.rec"))
        .map(|recursor| usize::try_from(recursor.num_minors).unwrap_or(usize::MAX))
        .ok_or_else(|| refuse("an environment with no `Nat.rec` recursor".to_owned()))?;
    if args.len() != 1 + num_minors + 1 {
        return Err(refuse(format!(
            "a `Nat.rec` spine with {} argument(s) where {} were required",
            args.len(),
            1 + num_minors + 1
        )));
    }

    // Motive: `fun _ => Nat` — this slice's judgment is stated at Nat.
    let ExprKind::Lam(_, motive_param, motive_body) = args[0].kind() else {
        return Err(refuse("a non-lambda motive".to_owned()));
    };
    if !is_nat(motive_param) || !is_nat(motive_body) {
        return Err(refuse(
            "a motive other than `fun _ => Nat` (this slice's per-equation judgment is \
             stated at the Nat result only)"
                .to_owned(),
        ));
    }

    // Scrutinee: the lambda's own binder.
    if !matches!(args[1 + num_minors].kind(), &ExprKind::BVar(0)) {
        return Err(refuse("a recursor whose major premise is not the parameter".to_owned()));
    }

    Ok(args[1..1 + num_minors].iter().map(|&minor| minor.clone()).collect())
}

/// Strip transparent metadata wrappers — the gate's own copy, for the same
/// independence reason the spine parse is its own.
fn gate_strip_mdata(expr: &Expr) -> &Expr {
    let mut cursor = expr;
    while let ExprKind::MData(_, inner) = cursor.kind() {
        cursor = inner;
    }
    cursor
}

// ───────────────────────────────────────────────────────────────────────────
// THE RECURSIVE PRECONDITION — the audited-empty axiom closure, extended from
// side A's DECLARATION to side B's PROOF TERMS (the §6e MEASUREMENT NOTE)
// ───────────────────────────────────────────────────────────────────────────

/// Does side A recurse?
///
/// [`bounded_core_scan`] is the crate's existing bounded scan for recursive
/// eliminators; [`is_recursive_eliminator`] already counts both `*.rec` and
/// `WellFounded.fix`. `None` means the scan could not decide (node envelope,
/// or an extension expression), and **an undecided scan applies the
/// precondition** rather than skipping it — the cost of an unnecessary audit
/// is milliseconds, the cost of a skipped one is the escape this precondition
/// exists to close.
fn side_a_is_recursive(body: &Expr) -> bool {
    bounded_core_scan(body).unwrap_or(true)
}

/// **The hard precondition: a recursive `Faithful` requires an audited-empty
/// axiom closure over side A's whole declaration.**
///
/// # Why a recursive lane needs this and a non-recursive one does not
///
/// A non-recursive Clean-origin body is emitted because the kernel identified
/// two terms. An assumption in that closure is a disclosure problem — real,
/// and `mint::decide_mint` refuses the DefId for it — but it cannot change
/// what the emitted code DOES.
///
/// A recursive one is different in kind, and the difference is measured
/// (`tests/r2_wf_equation_probes.rs`, probe w7):
///
/// * d1 — a well-founded functional's recursive slot has type
///   `rec : (y : α) → r y x → C y`. A diverging off-by-one is refused **by
///   the kernel's typing rule**, because no proof of `Nat.lt (succ x) x`
///   exists to fill the slot. That typing rule is R2's termination evidence.
/// * d4 — with `axiom bogus : (x : Nat) → Nat.lt (Nat.succ x) x` in scope,
///   the diverging functional kernel-checks and the definition **ADMITS**.
///
/// So on a recursive lane the axiom closure is not disclosure metadata; it is
/// the other half of the termination argument. One assumed decrease turns
/// "this definition terminates" into "this definition terminates if the user
/// was right", and the emitted binary is what loops.
///
/// The audit covers the declaration's TYPE and VALUE — everything, not only
/// the decrease slots. That is deliberate, and it is not a widening invented
/// here: `mint::decide_mint` already requires an audited-empty closure over
/// the whole declaration before a `DefId` may exist, and a gate that admitted
/// what the mint refuses would put the two decisions into disagreement about
/// one declaration. An axiom in the definition's VALUE but unrelated to the
/// decrease therefore refuses too (probe c4).
fn require_recursion_rests_on_the_kernel(
    env: &Environment,
    name: &str,
    kernel_name: &Name,
) -> Result<(), GateRefusal> {
    let Some(info) = env.get_const(kernel_name) else {
        return Err(GateRefusal::NoCleanBody { name: name.to_owned() });
    };
    let Some(value) = info.value.clone() else {
        return Err(GateRefusal::NoCleanBody { name: name.to_owned() });
    };
    let audit = crate::closure::audit_term_closure(
        env,
        &format!("the Clean definition of `{name}`"),
        &info.type_,
        &value,
    );
    require_clear_closure(name, &audit)
}

/// Turn a [`crate::closure::ClosureAudit`] into the v7/D3 refusal, or pass.
fn require_clear_closure(
    name: &str,
    audit: &crate::closure::ClosureAudit,
) -> Result<(), GateRefusal> {
    if audit.is_clear() {
        return Ok(());
    }
    Err(GateRefusal::AssumptionBearingRecursion {
        name: name.to_owned(),
        subject: audit.subject().to_owned(),
        assumptions: audit.assumptions().to_vec(),
        blocking: audit.blocking().to_vec(),
    })
}

// ───────────────────────────────────────────────────────────────────────────
// R2 — the WELL-FOUNDED functional lane
// ───────────────────────────────────────────────────────────────────────────

/// The sentinel side B writes where a decrease proof belongs.
///
/// It is a constant name that must NOT exist in the kernel environment; the
/// gate checks that before it substitutes, so the sentinel can never resolve
/// to a real term someone declared.
pub const DECREASE_SLOT_SENTINEL: &str = "Trust.CleanOrigin.decreaseSlot";

/// The sentinel side B writes where **the MEASURE** belongs — phase 3 only.
///
/// # Why a second sentinel exists at all (R3d, 2026-08-27)
///
/// At [`WfLowering::OnParameter`] side B can author every part of the
/// functional except the decrease proof: the recursion variable is a parameter,
/// so the recursive slot's type is `(y : Nat) → Nat.lt y x → Nat^(N-1) → Nat`,
/// a term over binders and nothing else.
///
/// At [`WfLowering::OnMeasureValue`] the recursion runs on the value of the
/// `termination_by` MEASURE, and the measure is a term the emitted body holds
/// **no trace of** — MIR computes the guard, the two branch values and the
/// self-call's arguments, and never the measure. It occupies exactly three
/// positions in the functional:
///
/// ```text
/// binder 1        rec : (k : Nat) → Nat.lt k n → (Π p⃗, Nat.lt m[p⃗] k → Nat)
/// binder arity+2  hm  : Nat.lt m n
/// call argument 0       the major premise, `m` at the enclosing parameters
/// ```
///
/// Side B writes the bare sentinel in each, and the gate replaces it with side
/// A's own term **at that same position**. No lifting, no reconstruction, no
/// arithmetic: the two functionals have the same binder structure by the time
/// the borrow runs (`peel_functional` has already required side B's telescope
/// to be the length this lowering binds), so "the term at this position" is
/// well defined.
///
/// # Why this is the decrease-proof borrow and not a new kind of trust
///
/// [`ReflectedWfFunctional`] states the test: side A may supply what the
/// comparison is not deciding about the EMITTED BODY. The measure is not a
/// value the emitted body computes, not an argument it passes and not a branch
/// it takes — it is the termination plumbing that makes side A a legal
/// definition. Borrowing it therefore removes nothing about the binary from the
/// comparison, and the four MIR-determined components — the guarded parameter,
/// the zero value, the nonzero value and the self-call's source arguments — are
/// still decided in full by the type check at side A's functional type and the
/// kernel defeq. `control_18`'s rows are the measurement that says so: a
/// swapped self-call operand pair, a guard on the wrong parameter, a wrong
/// threaded index and the exchanged `|a-b|` / `min a b` legs are all REFUSED
/// with the borrow in place.
///
/// It is NOT a licence: the borrow fills exactly the three positions above.
/// A sentinel anywhere else in side B's functional is refused
/// ([`rebuild_functional`]), and — like the decrease sentinel — the name must
/// not resolve in the environment, or a borrowed slot could not be told apart
/// from a term someone declared.
pub const MEASURE_SLOT_SENTINEL: &str = "Trust.CleanOrigin.measureSlot";

/// Side B for a WELL-FOUNDED-recursion emission: the functional, with every
/// decrease proof left as [`DECREASE_SLOT_SENTINEL`].
///
/// # Why side B does not carry a proof — and why that is not a weakening
///
/// MIR contains no proof terms. A side-B producer that put a term in the
/// `r y x` slot would be *inventing* one, and probe w7/d4 measures what that
/// buys an adversary: with a single assumed decrease the diverging functional
/// kernel-checks and the definition admits. The gate's termination evidence
/// would then rest on a term the emitter authored — the emitter being the very
/// thing the gate exists to check.
///
/// The borrow costs nothing, and that is measured too. Probe w7/**d2**: two
/// functionals differing ONLY in which proof fills the decrease slot are
/// definitionally equal. The proof is not what the comparison decides; the
/// ARGUMENT is (probe w7/d3 — a well-typed, genuinely decreasing `x - 2`
/// against side A's `x - 1` is REFUSED by defeq). So filling side B's slots
/// from side A leaves every question the gate actually answers untouched, and
/// removes from the gate's evidence the one term side B could have poisoned.
///
/// **This is not side A co-authoring side B.** Co-authoring would mean side A
/// supplying something the comparison *reads* — a value, an argument, a
/// branch. It supplies none of those. What it supplies is the one component
/// the comparison is provably blind to (d2) and the audit is not: the proof
/// slot contributes NOTHING to the defeq verdict and EVERYTHING to the axiom
/// closure, so borrowing it moves the audited surface from an emitter-authored
/// term to a kernel-checked declaration without moving the checked surface at
/// all.
#[derive(Debug, Clone)]
pub struct ReflectedWfFunctional {
    /// `fun (x : α) (rec : (y : α) → r y x → C y) => …`, with every recursive
    /// call spelled `rec <argument> Trust.CleanOrigin.decreaseSlot`.
    ///
    /// Public so the mutation controls can hand the gate adversarial
    /// functionals directly. That costs no authority: this is a CLAIM, and
    /// every part of it is re-decided against the kernel by
    /// [`check_faithful_wf_functional`].
    pub functional: Expr,
}

/// The six components of a `WellFounded.fix` side A.
struct WfSpine {
    /// The functional `F`.
    f: Expr,
    /// WHICH LOWERING side A is in, derived by the gate from its own parse.
    ///
    /// The tag's *type* is shared with the plan lane; the *answer* is not — the
    /// gate re-derives it below from the spine it read itself, exactly as it
    /// re-derives the arity. Every downstream number (the functional's binder
    /// count, `rec`'s de Bruijn index, a self-call's argument count, and which
    /// of those arguments is the decrease slot) is a function of this and the
    /// arity, so reading it wrong is a refusal, never a silent re-layout.
    lowering: WfLowering,
    /// How many parameters the declaration takes, DERIVED BY THE GATE from
    /// side A's own spine — never supplied by the plan lane.
    ///
    /// R3a. `F` binds `x`, `rec` and then one binder per threaded parameter, so
    /// every downstream walk (`peel_functional`, the `rec`-call arity in
    /// `walk_functional`/`rebuild_functional`, and the re-clothing in
    /// `fill_decrease_slots`) is a function of this number. Reading it from the
    /// SPINE and then requiring `F` to agree makes the two a cross-check: a
    /// declaration whose functional binds a different number of binders than
    /// its spine passes arguments refuses instead of being read at the wrong
    /// layout.
    arity: usize,
    /// The `termination_by` MEASURE, read by the gate out of side A's own seed
    /// `Nat.succ m`. `None` at [`WfLowering::OnParameter`], which has no seed.
    ///
    /// **R3e.** This is the term three borrowed positions are stated in — the
    /// `rec` binder's type, the `hm` binder's type and every self-call's major
    /// premise — and the gate borrows all three from side A. Reading it HERE,
    /// out of the spine the gate parsed itself, is what lets the borrow's
    /// assumption be CHECKED at each of those positions instead of inherited
    /// from whoever built the plan. See [`require_sum_measure_side_a`].
    measure: Option<Expr>,
}

/// One recursive call site inside a functional.
struct DecreaseSlot {
    /// Binders entered between the functional's `rec` binder and this call
    /// site: `rec` is `BVar(depth)` here. Recorded so the borrow can refuse a
    /// side B whose call sits at a different depth, where side A's proof term
    /// would be read against a different de Bruijn context.
    depth: u32,
    /// The term occupying the `r y x` slot.
    proof: Expr,
    /// The term in the call's FIRST argument position.
    ///
    /// Phase 2: the decreasing argument, which side B authors and the
    /// comparison decides — recorded but never borrowed. Phase 3: the MAJOR
    /// PREMISE, the measure at the enclosing parameters, which side B cannot
    /// author (see [`MEASURE_SLOT_SENTINEL`]) and which IS borrowed.
    major: Expr,
    /// The term in the call's SECOND argument position.
    ///
    /// Phase 3: `hm`, the course-of-values hypothesis, which must be the
    /// functional's own hypothesis binder — the term that makes the major
    /// premise beside it the measure and not merely something defeq to it
    /// (`require_sum_measure_calls`). Phase 2 has no such position and never
    /// reads this; it is carried for the same reason
    /// [`WfBorrowSource::binder_tys`] is — one borrow source, one shape, so the
    /// two lowerings cannot acquire two different notions of what a call site
    /// is. A self-call always carries at least two arguments at both lowerings
    /// (`rec_call_arity` is `arity + 1` and `arity + 3`, and `arity >= 1`), so
    /// this position always exists.
    hypothesis: Expr,
}

/// What one borrow takes FROM side A: its decrease slots, and its own
/// functional binder types.
///
/// The binder types are read here rather than reconstructed because phase 3's
/// `rec` and `hm` binders are stated in terms of the measure — see
/// [`MEASURE_SLOT_SENTINEL`]. At phase 2 nothing reads them and the vector is
/// carried unused, which is deliberate: one borrow source, one shape, so the
/// two lowerings cannot acquire two different notions of what a borrow is.
struct WfBorrowSource {
    slots: Vec<DecreaseSlot>,
    binder_tys: Vec<Expr>,
}

/// A bounded traversal envelope for the functional walks.
///
/// **R3d (2026-08-27): no longer [`INDUCTION_EXPR_NODE_LIMIT`].** It was, and
/// the reuse read as economy until the two rails were measured against
/// different terms. The induction fallback's 4,096 bounds a term this crate
/// hands to proof SEARCH; this one bounds a walk over a term the kernel has
/// already accepted, whose size is dominated by a component neither the walk
/// nor the comparison reads — the decrease proof. The pin's own subtractive
/// `gcd` carries a 14,013-node cascade proof inside a 14,283-node functional
/// (`emit::SUM_MEASURE_NODE_LIMIT` records the full measurement), so at 4,096
/// the gate refused side A before reaching any question about side B.
///
/// Held to the same number as the reader's envelope deliberately: the two walks
/// are structurally identical by design (`rebuild_functional`'s doc), and two
/// rails that could disagree about the same term is exactly the drift that doc
/// exists to prevent.
const FUNCTIONAL_NODE_LIMIT: usize = crate::emit::SUM_MEASURE_NODE_LIMIT;

/// A bounded NESTING-DEPTH envelope for the functional walks — the STACK rail.
///
/// **R3e (2026-08-28).** [`FUNCTIONAL_NODE_LIMIT`] is a WORK rail and was never
/// anything else; until R3d raised it, it happened to bound this walk's stack
/// too, because a term cannot nest deeper than it has nodes. At 262,144 that
/// incidental guard is gone, and `walk_functional`/`rebuild_functional` are
/// direct Rust recursions with no `stacker` under them, over a term
/// `clean-kernel` accepted using its OWN `stack_safe` growth. The failure that
/// removes is a `SIGSEGV`, not a wrong verdict — and a compiler that segfaults
/// on input the kernel admitted is a defect either way.
///
/// Held to the same number as the reader's rail
/// ([`crate::emit::SUM_MEASURE_DEPTH_LIMIT`], which carries the measurement and
/// the reasoning) for exactly the reason the node rail is: the two walks are
/// structurally identical by design, and two rails that could disagree about
/// the same term is the drift `rebuild_functional`'s doc exists to prevent.
const FUNCTIONAL_DEPTH_LIMIT: usize = crate::emit::SUM_MEASURE_DEPTH_LIMIT;

/// The faithfulness gate for WELL-FOUNDED-recursion emissions (R2).
///
/// The judgment, exactly as `tests/r2_wf_equation_probes.rs` derived it (w5–w7)
/// and **plus the precondition its finding 2 demands**:
///
/// 1. **side A's spine parses** as `@WellFounded.fix.{1,1} α C r hwf F x` with
///    `x` the definition's own parameter (w5) — and, R3e, applied to those
///    parameters IN SOURCE ORDER, with every component the borrow will take
///    from side A read by the gate itself ([`require_sum_measure_side_a`],
///    [`require_sum_measure_calls`]);
/// 2. **side A's declaration closure is audited empty** — the mint's rule,
///    applied at the gate, because the gate is what emits;
/// 3. **the borrow** — side B's decrease slots are filled from side A's own
///    proof terms, one per call site, at matching binder depth
///    ([`ReflectedWfFunctional`] documents why this is not co-authoring);
/// 4. **side B's closure is audited empty** after the borrow — the extension
///    the §6e MEASUREMENT NOTE names, and the reason the borrow exists: the
///    audited surface is now a kernel-checked declaration's terms, never an
///    emitter-authored one, and the audit still runs over the term the kernel
///    is actually handed;
/// 5. **side B's `F` kernel-checks at side A's `F` TYPE** — this is w7/d1, the
///    divergence catch, and with step 4 in place it is a real one again;
/// 6. **kernel defeq of the two `F`s** (w6), which is argument-sensitive even
///    among terminating alternatives (w7/d3).
///
/// Equation lemmas appear nowhere, and no accessibility witness ever enters
/// the comparison — w2/w4 measured the equation route's real boundary, and
/// w1 measured that the three witness spellings are mutually defeq, so an
/// F-layer gate crosses neither.
///
/// # Errors
///
/// [`GateRefusal`], every path fail-closed.
pub fn check_faithful_wf_functional(
    env: &Environment,
    name: &str,
    reflected: &ReflectedWfFunctional,
    carrier: &Carrier,
) -> Result<Faithful, GateRefusal> {
    let kernel_name = Name::from_string(name);

    // 1. Side A's PROVENANCE, identical to the other two lanes.
    match env.declaration_verification(&kernel_name) {
        Some(DeclarationVerification::FullKernelCheck) => {}
        verification => {
            return Err(GateRefusal::SideANotKernelChecked { name: name.to_owned(), verification });
        }
    }

    // 2. Side A's body, from the environment, never from the lowering.
    let Some(clean_body) = clean_definition_body(env, &kernel_name) else {
        return Err(GateRefusal::NoCleanBody { name: name.to_owned() });
    };

    // 3. THE RECURSIVE PRECONDITION over side A.
    require_recursion_rests_on_the_kernel(env, name, &kernel_name)?;

    // 4. The gate's OWN spine parse of side A.
    let spine = parse_wf_fix_spine(env, name, &clean_body)?;
    let f_a = spine.f;
    let arity = spine.arity;
    // R3c: the borrow's whole de Bruijn layout, derived once from the spine the
    // gate parsed itself. Phase 2's numbers are unchanged by construction —
    // `WfBorrowLayout::of` reproduces the literals R2/R3a shipped.
    let layout = WfBorrowLayout::of(spine.lowering, arity);

    // 5. THE BORROW.
    let decrease_sentinel = Name::from_string(DECREASE_SLOT_SENTINEL);
    let measure_sentinel = Name::from_string(MEASURE_SLOT_SENTINEL);
    // BOTH sentinels must be absent, for the one reason: a sentinel that
    // resolves could not be told apart from a term someone declared, and the
    // borrow's whole shape is "this position is provably not side B's".
    for sentinel in [&decrease_sentinel, &measure_sentinel] {
        if env.get_const(sentinel).is_some() {
            return Err(GateRefusal::DecreaseSlotBorrowRefused {
                name: name.to_owned(),
                detail: format!(
                    "the borrow sentinel `{sentinel}` resolves to a real declaration in this \
                     environment, so a borrowed slot could not be told apart from a term \
                     someone declared"
                ),
            });
        }
    }
    let sentinels = Sentinels { decrease: &decrease_sentinel, measure: &measure_sentinel };
    let borrow =
        |detail: String| GateRefusal::DecreaseSlotBorrowRefused { name: name.to_owned(), detail };
    let source = collect_decrease_slots(&f_a, layout).map_err(|detail| {
        borrow(format!(
            "side A's functional is outside the single-`rec` shape this lane parses: {detail}"
        ))
    })?;
    if source.slots.is_empty() {
        return Err(borrow(
            "side A's functional never uses its recursive slot, so there is no recursion for \
             this lane to gate — route it to the whole-term lane"
                .to_owned(),
        ));
    }
    // 5a. **R3e — WHAT THE BORROW ASSUMES ABOUT SIDE A'S CALL SITES, DECIDED.**
    //     `require_sum_measure_side_a` has already read the static half of the
    //     phase-3 anatomy out of the spine; this is the half that only exists
    //     per call site. Both must run BEFORE the borrow, because after it side
    //     B carries side A's terms at these positions by construction and
    //     neither the type check nor the defeq can see a thing about them.
    if let Some(measure) = spine.measure.as_ref() {
        require_sum_measure_calls(name, &source, layout, measure)?;
    }
    let f_b =
        fill_decrease_slots(&reflected.functional, layout, &source, sentinels).map_err(borrow)?;

    // 6. Side A's functional TYPE — what side B must check at, and what the
    //    audit in step 7b takes the term at.
    let f_a_type = {
        let checker = TypeChecker::new(env);
        let inferred = checker.infer_type(&f_a);
        if checker.heartbeat_spent() {
            return Err(GateRefusal::ResourceExhausted {
                name: name.to_owned(),
                limit: KERNEL_HEARTBEAT_ENVELOPE,
            });
        }
        inferred.map_err(|_| GateRefusal::NotWellFoundedRecursor {
            name: name.to_owned(),
            found: "a `WellFounded.fix` spine whose functional does not type-check".to_owned(),
        })?
    };
    // 7. THE TYPE CHECK (w7/d1, the divergence catch) — BEFORE the audit.
    //    Order is load-bearing for the DIAGNOSTIC, not for soundness: both
    //    must pass. An ill-typed side B would otherwise surface out of the
    //    audit as `TermRejected`/`GoalNotProposition`, i.e. as an
    //    assumption-bearing refusal with a kernel type error inside it —
    //    which reports a divergence as an axiom problem and sends the reader
    //    to look for an `axiom` that is not there. Measured: probe c6.
    let checker = TypeChecker::new(env);
    let typed = checker.check_type(&f_b, &f_a_type);
    if checker.heartbeat_spent() {
        return Err(GateRefusal::ResourceExhausted {
            name: name.to_owned(),
            limit: KERNEL_HEARTBEAT_ENVELOPE,
        });
    }
    if typed.is_err() {
        return Err(GateRefusal::DecreaseSlotBorrowRefused {
            name: name.to_owned(),
            detail: "the emitted functional does not kernel-check at the declaration's own \
                     functional type once side A's decrease proofs are in its slots — the \
                     emission recurses somewhere side A's proof does not reach"
                .to_owned(),
        });
    }
    drop(checker);

    // 7b. THE EXTENSION the §6e MEASUREMENT NOTE names: audit side B's
    //     closure over the term the kernel was just handed — borrowed proofs
    //     included. With the borrow in place this can only ever re-find what
    //     side A already carries, which is the point: the audited surface is a
    //     kernel-checked declaration's terms rather than an emitter's. It is
    //     run anyway, on the actual term, because a gate that trusted the
    //     borrow to have worked would be trusting this crate's own rebuild.
    let side_b_audit = crate::closure::audit_term_closure(
        env,
        &format!("the emitted functional for `{name}`, with side A's decrease proofs in its slots"),
        &f_a_type,
        &f_b,
    );
    require_clear_closure(name, &side_b_audit)?;

    // 8. The defeq (w6).
    let checker = TypeChecker::new(env);
    let agree = checker.is_def_eq(&f_b, &f_a);
    if checker.heartbeat_spent() {
        return Err(GateRefusal::ResourceExhausted {
            name: name.to_owned(),
            limit: KERNEL_HEARTBEAT_ENVELOPE,
        });
    }
    if !agree {
        return Err(GateRefusal::FunctionalDisagreement { name: name.to_owned() });
    }

    Ok(Faithful {
        name: name.to_owned(),
        admitted_at: carrier.rust().clone(),
        method: FaithfulnessMethod::WellFoundedFunctionalDefeq,
    })
}

/// The gate's OWN parse of a well-founded side A — peel at most one lambda,
/// then require `@WellFounded.fix.{1,1}` in either of the two spellings the
/// island is recorded as producing.
///
/// Deliberately the gate's own, for the same reason `parse_nat_rec_minors` is:
/// the gate must rest on its own reading of side A, never on the plan lane's.
/// The shape is the one probe w5 measured against the real island lowering,
/// including that the surface-implicit `{α} {C} {r}` are ordinary leading
/// arguments in raw kernel terms.
///
/// # BOTH spellings, and why accepting the second is not a weakening
///
/// ```text
/// ETA-EXPANDED  (probe w1, and every probe in the R2 batteries):
///   fun (n : Nat) => @WellFounded.fix.{1,1} α C r hwf F (bvar 0)
/// ETA-CONTRACTED (the §6e MEASUREMENT NOTE's recorded refutation of a design
///   that assumed R1's shape):
///   @WellFounded.fix.{1,1} α C r hwf F
/// ```
///
/// The record disagrees with itself about which the island emits, so the gate
/// reads both. That costs no checking power and adds no trust: the F-layer
/// judgment reads argument 4 and nothing else, argument 4 is the same term in
/// both spellings, and eta is definitional in this kernel (measured — the
/// contracted body kernel-checks at `Nat -> Nat` and is defeq to the expanded
/// one). Refusing the contracted spelling would only make the lane
/// unreachable for a body it can decide correctly; it would not make any
/// verdict stricter. Every other component — the closure audit, the borrow,
/// the type check, the defeq — is untouched.
fn parse_wf_fix_spine(env: &Environment, name: &str, body: &Expr) -> Result<WfSpine, GateRefusal> {
    let refuse =
        |found: String| GateRefusal::NotWellFoundedRecursor { name: name.to_owned(), found };

    // Peel EVERY leading lambda, not at most one. R3a: an arity-N declaration
    // abstracts N parameters before its spine (`r7` q1). Bounded by the term
    // itself; a lambda tower is a term the environment already kernel-checked.
    let mut peeled_lambdas = 0usize;
    let mut cursor = gate_strip_mdata(body);
    while let ExprKind::Lam(_, _, inner) = cursor.kind() {
        peeled_lambdas += 1;
        cursor = gate_strip_mdata(inner);
    }

    let mut head = cursor;
    let mut args: Vec<&Expr> = Vec::new();
    while let ExprKind::App(function, argument) = head.kind() {
        args.push(gate_strip_mdata(argument));
        head = gate_strip_mdata(function);
    }
    args.reverse();

    let ExprKind::Const(head_name, head_levels) = head.kind() else {
        return Err(refuse("a non-constant application head".to_owned()));
    };
    if *head_name == Name::from_string("Nat.rec") {
        return Err(refuse(
            "a `Nat.rec` application — structural recursion belongs to the per-defining-equation \
             lane, which needs no decrease proof at all"
                .to_owned(),
        ));
    }
    if *head_name != Name::from_string("WellFounded.fix") {
        return Err(refuse(format!("an application headed by `{head_name}`")));
    }
    if head_levels.len() != 2 {
        return Err(refuse(format!(
            "a `WellFounded.fix` at {} universe parameter(s) where 2 were required",
            head_levels.len()
        )));
    }
    // α, C, r, hwf, F, then one major/threaded argument per parameter.
    //
    // ETA-CONTRACTED: 0 binders, 5 arguments — arity 1 (`countdownSum` is
    //   measured in exactly this spelling, `r7` q1).
    // ETA-EXPANDED:   N binders, 5 + N arguments — arity N.
    // SUM-MEASURE:    N binders, 7 + N arguments — arity N (phase 3; see
    //   `parse_wf_sum_measure_seed` for what the two extra arguments are).
    //
    // The three counts cannot collide at one peel depth (`5 + N` and `7 + N`
    // differ by two for every N), so the LOWERING is decided by arithmetic
    // rather than guessed.
    //
    // Every one of the N parameter arguments must be a DISTINCT parameter the
    // outer lambdas bound, together they must be all of them, and — R3e — they
    // must arrive IN THE ORDER THIS LOWERING THREADS THEM. That is what makes
    // "this spine is the declaration applied to its own parameters" checked
    // rather than assumed: a spine that passed one parameter twice, passed a
    // computed argument, or passed them PERMUTED would be a recursion over
    // something other than the arguments the emitted body will hold.
    //
    // Under `fun p_0 … p_{N-1} =>` source parameter `i` is `BVar(N - 1 - i)`.
    let source_of = |argument: &&Expr| -> Option<usize> {
        match gate_strip_mdata(argument).kind() {
            &ExprKind::BVar(index) => usize::try_from(index)
                .ok()
                .filter(|index| *index < peeled_lambdas)
                .map(|index| peeled_lambdas - 1 - index),
            _ => None,
        }
    };
    // **R3e — THE ORDER CHECK, and why its absence was a hole rather than a
    // nicety.** Before this, the gate marked a `seen` slot and refused only a
    // REPEAT or a non-parameter, so a PERMUTATION passed. A permuted spine can
    // carry a BYTE-IDENTICAL functional — the permutation lives entirely in the
    // spine's argument list, which the F-layer comparison never reads — so side
    // B was compared against, and agreed with, a functional whose declaration
    // applies it to its parameters in a different order. For a non-symmetric
    // body that is a different function:
    //
    // ```text
    // def cnt (a b : Nat) : Nat := if h : 0 < b then cnt (a - b) (b - 1) else a
    // termination_by a + b        -- cnt 5 1 = 4, cnt 1 5 = 0
    // ```
    //
    // The plan lane has always read this (`recognise_wf_nat_rec`'s threaded
    // check, `read_wf_sum_measure_anatomy`'s parameter loop). The gate did not,
    // which made the PLAN LANE the sole enforcement of a property the gate's
    // own admission rests on — exactly what this file's parse doc forbids. It
    // is re-decided here, from the gate's own spine parse, and the expected
    // sequence is passed in because the two lowerings thread differently: phase
    // 2 leads with the measure PARAMETER and threads the rest, phase 3 runs on
    // the measure's VALUE and threads all N in source order.
    let require_own_parameters =
        |parameters: &[&Expr], expected: &[usize]| -> Result<(), GateRefusal> {
            let mut found: Vec<usize> = Vec::with_capacity(parameters.len());
            for argument in parameters {
                let Some(source) = source_of(argument) else {
                    return Err(refuse(
                        if matches!(gate_strip_mdata(argument).kind(), ExprKind::BVar(_)) {
                            "a `WellFounded.fix` applied to a variable bound outside the \
                             definition's own parameters"
                                .to_owned()
                        } else {
                            "a `WellFounded.fix` applied to something other than the \
                             definition's own parameters, so the recursion is over a computed \
                             argument"
                                .to_owned()
                        },
                    ));
                };
                found.push(source);
            }
            let mut seen = vec![false; peeled_lambdas];
            for source in &found {
                if std::mem::replace(&mut seen[*source], true) {
                    return Err(refuse(
                        "a `WellFounded.fix` that passes one of the definition's parameters \
                         twice, so its arguments are not the parameters the emitted body holds"
                            .to_owned(),
                    ));
                }
            }
            if found.as_slice() != expected {
                return Err(refuse(format!(
                    "a `WellFounded.fix` that applies itself to the definition's own parameters \
                     PERMUTED — source parameter(s) {found:?} where this lowering threads \
                     {expected:?}. The emitted body holds parameter `i` in argument position \
                     `i`, and the functional is the same term either way, so a permuted spine \
                     denotes a DIFFERENT function than the one that would be emitted while \
                     every F-layer question about it still answers yes.\n\
                     options:\n\
                     - restate the declaration so its recursion carries its parameters \
                       unpermuted, and it becomes emittable with no other change;\n\
                     - keep this spelling for PROOF position and call a helper whose spine is \
                       in source order;\n\
                     - if the compiler produced this spine, report it with the declaration: \
                       nothing at the call site changes it"
                )));
            }
            Ok(())
        };
    let (f, arity, lowering, measure) = if peeled_lambdas == 0 && args.len() == 5 {
        (args[4].clone(), 1, WfLowering::OnParameter, None)
    } else if peeled_lambdas >= 1
        && args.len() == WfLowering::OnParameter.spine_arguments(peeled_lambdas)
    {
        // PHASE 2. The MAJOR premise is the recursion's own measure PARAMETER —
        // any one of them — and the threaded arguments are all the others, in
        // SOURCE order. Measured both ways, `r7` q1: `addAcc` (measure at
        // source 0) gives `#1 #0`, `addAcc2` (measure at source 1) gives
        // `#0 #1`. So the expected sequence is derived from the measure the
        // spine itself names, never assumed to start at parameter 0.
        let Some(measure_index) = source_of(&args[5]) else {
            return Err(refuse(
                "a `WellFounded.fix` applied to something other than the definition's own \
                 parameter, so the recursion is over a computed argument"
                    .to_owned(),
            ));
        };
        let mut expected = vec![measure_index];
        expected.extend((0..peeled_lambdas).filter(|index| *index != measure_index));
        require_own_parameters(&args[5..], &expected)?;
        (args[4].clone(), peeled_lambdas, WfLowering::OnParameter, None)
    } else if peeled_lambdas >= 1
        && args.len() == WfLowering::OnMeasureValue.spine_arguments(peeled_lambdas)
    {
        // PHASE 3. The parameters sit BETWEEN the seed and the seed proof, so
        // the same "these are the declaration's own parameters" rule applies to
        // a different slice — in plain source order, because the recursion runs
        // on the measure's VALUE and no parameter is singled out. Everything
        // around them gets its own check too (R3e): a seed that does not match
        // its own proof is a recursion started somewhere the proof does not
        // justify, and the components stated in terms of the MEASURE are the
        // ones the borrow takes from side A sight unseen.
        let measure = require_sum_measure_side_a(name, &args, peeled_lambdas)?;
        require_own_parameters(
            &args[6..6 + peeled_lambdas],
            &(0..peeled_lambdas).collect::<Vec<usize>>(),
        )?;
        (args[4].clone(), peeled_lambdas, WfLowering::OnMeasureValue, Some(measure))
    } else {
        return Err(refuse(format!(
            "a `WellFounded.fix` spine with {} argument(s) under {peeled_lambdas} outer \
             binder(s), where the eta-expanded spelling at arity N carries 5 + N under N, the \
             eta-contracted spelling carries 5 under 0, and the sum-measure spelling carries \
             7 + N under N",
            args.len()
        )));
    };
    if f.has_loose_bvars_quick() {
        return Err(refuse(
            "a functional that mentions the definition's parameter, which the F-layer comparison \
             is not defined over"
                .to_owned(),
        ));
    }
    // The environment read is the same self-consistency check the structural
    // lane makes: a `WellFounded.fix` the environment does not declare is not
    // a spine, it is a name collision.
    if env.get_const(&Name::from_string("WellFounded.fix")).is_none() {
        return Err(refuse("an environment with no `WellFounded.fix` declaration".to_owned()));
    }
    Ok(WfSpine { f, arity, lowering, measure })
}

/// Whether `expr` is the bare constant `Nat` — the gate's own copy, for the
/// same independence reason [`gate_strip_mdata`] is.
fn gate_is_nat(expr: &Expr) -> bool {
    gate_is_bare_const(expr, "Nat")
}

/// Whether `expr` is the bare constant `name`, at no universe arguments.
fn gate_is_bare_const(expr: &Expr, name: &str) -> bool {
    matches!(gate_strip_mdata(expr).kind(), ExprKind::Const(n, levels)
        if *n == Name::from_string(name) && levels.is_empty())
}

/// `name ARG` for a bare unary constant, or `None`.
fn gate_unary_const_app<'e>(expr: &'e Expr, name: &str) -> Option<&'e Expr> {
    let (head, args) = gate_uncurry(expr);
    (gate_is_bare_const(head, name) && args.len() == 1).then(|| args[0])
}

/// Whether `expr` is `Nat.lt <measure> (BVar bound)`, in the RAW spelling.
///
/// Raw only, and unlike the guard the plan lane reads: a user's `0 < n` reaches
/// the term through instance resolution and has a surface spelling, but this
/// proposition is built by `first-party/clean`'s `sum_measure.rs` itself out of
/// `Expr::const_("Nat.lt")`. There is one spelling to read, and accepting a
/// second would be accepting a term the lowering does not produce.
fn gate_is_raw_nat_lt_at(expr: &Expr, measure: &Expr, bound: u32) -> bool {
    let (head, args) = gate_uncurry(expr);
    gate_is_bare_const(head, "Nat.lt")
        && args.len() == 2
        && *gate_strip_mdata(args[0]) == *measure
        && matches!(gate_strip_mdata(args[1]).kind(), &ExprKind::BVar(index) if index == bound)
}

/// **R3e — THE GATE'S OWN READ OF A PHASE-3 SIDE A**, component by component,
/// returning the `termination_by` MEASURE it read out of the seed.
///
/// # Why this exists, and why it is not a call into the plan lane
///
/// The phase-3 borrow takes FOUR things from side A that MIR contains no trace
/// of: every self-call's decrease proof, its major premise, and the types of
/// the `rec` and `hm` binders ([`MEASURE_SLOT_SENTINEL`]). Side B writes a
/// sentinel at each and the gate fills it from side A. That is sound only if
/// the gate has itself established WHAT side A holds there — otherwise the
/// borrow imports a term on the strength of an assumption nobody checked, and
/// the defeq in step 8 cannot see it, because after the borrow both sides carry
/// the same term BY CONSTRUCTION.
///
/// Until R3e the gate checked, of this whole anatomy, only the seed and its
/// proof. Everything else — `α = Nat`, `r = Nat.lt`, the motive's shape and its
/// hypothesis, both borrowed binder types, and every major premise — was read
/// ONLY by [`crate::emit::read_wf_sum_measure_anatomy`] on the plan lane. That
/// made the gate's reading of side A a strict SUBSET of the plan's at exactly
/// the borrowed positions, so the plan lane was the sole enforcement of
/// properties the gate's admission rests on. `parse_wf_fix_spine`'s doc forbids
/// precisely that ("the gate must rest on its own reading of side A, never on
/// the plan lane's") and `docs/TCB.md` denies it of this row.
///
/// So this is deliberately a SECOND reader of the same shape rather than a
/// shared one. The plan lane decides whether to shape MIR; this decides whether
/// to admit a binary. Two readers that must agree are a cross-check; one reader
/// called twice is a single point of failure with two call sites.
///
/// # The shape, from `first-party/clean`'s `wf_recursion::sum_measure`
///
/// ```text
/// C     := fun (n : Nat) => Π (p⃗ : Nat), Nat.lt m n → Nat
/// F     := fun (n : Nat) (rec : (k : Nat) → Nat.lt k n → C k) (p⃗ : Nat)
///              (hm : Nat.lt m n) => body[ f a⃗ ↦ rec m hm a⃗ prf ]
/// value := fun (p⃗) => @WellFounded.fix.{1,1} Nat C Nat.lt hwf F
///              (Nat.succ m) p⃗ (Nat.le.refl (Nat.succ m))
/// ```
///
/// The measure `m` occurs in FOUR places — the seed, the motive's hypothesis,
/// the `hm` binder and every self-call's major premise — and the lowering
/// builds all four from one term. They are therefore compared ON THE NOSE, each
/// at the de Bruijn depth its own context gives it. A side A whose four sites
/// merely happen to be definitionally equal is refused rather than read at
/// whichever spelling it has: the borrow copies TERMS, and "the three sites name
/// one measure" is what makes the copied ones the measure at all.
///
/// `hwf` (argument 3) is deliberately NOT read. It is an accessibility witness,
/// it never enters the F-layer comparison, and w1 measured that its spellings
/// are mutually defeq — reading it would add a refusal without adding a check.
///
/// # Errors
///
/// [`GateRefusal::NotWellFoundedRecursor`], naming the component that refused.
fn require_sum_measure_side_a(
    name: &str,
    args: &[&Expr],
    arity: usize,
) -> Result<Expr, GateRefusal> {
    let refuse =
        |found: String| GateRefusal::NotWellFoundedRecursor { name: name.to_owned(), found };
    let seed_index = 5;
    let seed_proof_index = 6 + arity;

    // α — the carrier the recursion is eliminated over. The sum-measure
    // lowering runs on the measure's VALUE, which is a `Nat`, so anything else
    // is a different lowering and the binder types below would be read against
    // the wrong one.
    if !gate_is_nat(args[0]) {
        return Err(refuse(
            "a sum-measure `WellFounded.fix` that eliminates over a type other than `Nat`, where \
             this lowering recurses on the measure's own `Nat` value"
                .to_owned(),
        ));
    }
    // r — the BARE constant. Phase 2's relation is an eta-expanded
    // `fun a b => Nat.lt a b`; `sum_measure.rs` cites `Nat.lt` itself, and
    // reading that difference is part of telling the two lowerings apart.
    if !gate_is_bare_const(args[2], "Nat.lt") {
        return Err(refuse(
            "a sum-measure `WellFounded.fix` whose relation is not the bare constant `Nat.lt`, \
             which is the only relation this lowering runs on"
                .to_owned(),
        ));
    }

    // THE SEED and its proof. `Nat.lt m (Nat.succ m)` is
    // `Nat.le (Nat.succ m) (Nat.succ m)` by δ — that identity is the whole
    // reason the seed proof is a `refl` — so a `Nat.le.refl` at a DIFFERENT
    // bound proves something else, and saying so here beats letting it surface
    // as a kernel error inside the functional's type.
    let Some(measure) = gate_unary_const_app(args[seed_index], "Nat.succ") else {
        return Err(refuse(
            "a sum-measure `WellFounded.fix` seeded with something other than \
             `Nat.succ <measure>`"
                .to_owned(),
        ));
    };
    let measure = measure.clone();
    let Some(seed_bound) = gate_unary_const_app(args[seed_proof_index], "Nat.le.refl") else {
        return Err(refuse(
            "a sum-measure `WellFounded.fix` whose accessibility seed is not \
             `Nat.le.refl <bound>`"
                .to_owned(),
        ));
    };
    if *seed_bound != *gate_strip_mdata(args[seed_index]) {
        return Err(refuse(
            "a sum-measure `WellFounded.fix` whose seed proof is `Nat.le.refl` at a different \
             bound than the seed it is supposed to justify"
                .to_owned(),
        ));
    }

    // THE MOTIVE — `fun n => Π (p⃗ : Nat), Nat.lt m n → Nat`, n-DEPENDENT.
    //
    // It is the motive that says what `rec m hm` is a function of, so the
    // borrowed `rec` binder type below is only the slot the emitted self-call
    // needs if the motive really re-binds all N parameters and then demands the
    // measure hypothesis. A motive that dropped the hypothesis would be phase
    // 2's constant family wearing phase 3's argument count.
    let motive = gate_strip_mdata(args[1]);
    let ExprKind::Lam(_, motive_binder, motive_body) = motive.kind() else {
        return Err(refuse(
            "a sum-measure `WellFounded.fix` whose motive is not a lambda over the \
             course-of-values bound"
                .to_owned(),
        ));
    };
    if !gate_is_nat(motive_binder) {
        return Err(refuse(
            "a sum-measure `WellFounded.fix` whose motive binds the course-of-values bound at a \
             type other than `Nat`"
                .to_owned(),
        ));
    }
    let mut motive_cursor = gate_strip_mdata(motive_body);
    for source_index in 0..arity {
        let ExprKind::Pi(_, ty, inner) = motive_cursor.kind() else {
            return Err(refuse(format!(
                "a sum-measure `WellFounded.fix` whose motive re-binds {source_index} \
                 parameter(s) where this lowering re-binds all {arity} of them before the \
                 measure hypothesis"
            )));
        };
        if !gate_is_nat(ty) {
            return Err(refuse(format!(
                "a sum-measure `WellFounded.fix` whose motive re-binds parameter {source_index} \
                 at a type other than `Nat`; this lane is stated at the bignum carrier only"
            )));
        }
        motive_cursor = gate_strip_mdata(inner);
    }
    let ExprKind::Pi(_, hypothesis, motive_return) = motive_cursor.kind() else {
        return Err(refuse(
            "a sum-measure `WellFounded.fix` whose motive does not end in the measure hypothesis \
             `Nat.lt m n -> ret`; a motive with no hypothesis is phase 2's constant family, not \
             this one"
                .to_owned(),
        ));
    };
    // At the hypothesis the motive's context is [n, p⃗], so `n` is `BVar(arity)`
    // and source parameter `i` is `BVar(arity - 1 - i)` — the SAME spelling the
    // seed carries, which is why the measure compares on the nose.
    let motive_bound = u32::try_from(arity).unwrap_or(u32::MAX);
    if !gate_is_raw_nat_lt_at(hypothesis, &measure, motive_bound) {
        return Err(refuse(
            "a sum-measure `WellFounded.fix` whose motive's hypothesis is not `Nat.lt m n` at \
             the SAME measure its seed carries. The motive, the seed, the functional's \
             hypothesis binder and every self-call's major premise must name ONE measure — the \
             gate borrows three of those four positions from this declaration, so a side A whose \
             sites merely happen to be definitionally equal is refused rather than read at \
             whichever spelling it has.\n\
             options:\n\
             - state the measure once and let the lowering place it, which is what \
               `termination_by` does;\n\
             - if the compiler produced this spine, report it with the declaration"
                .to_owned(),
        ));
    }
    if !gate_is_nat(motive_return) {
        return Err(refuse(
            "a sum-measure `WellFounded.fix` whose motive returns at a type other than `Nat`; \
             this lane is stated at the bignum carrier only, because the reflected functional's \
             arithmetic is `Nat`'s"
                .to_owned(),
        ));
    }

    // THE FUNCTIONAL TELESCOPE — `n, rec, p⃗, hm`, exactly `arity + 3` binders.
    // Two of those types are BORROWED (`rec` and `hm`), so both are read here.
    let layout = WfBorrowLayout::of(WfLowering::OnMeasureValue, arity);
    let mut telescope: Vec<&Expr> = Vec::with_capacity(layout.binders);
    let mut cursor = gate_strip_mdata(args[4]);
    for _ in 0..layout.binders {
        let ExprKind::Lam(_, ty, inner) = cursor.kind() else {
            return Err(refuse(format!(
                "a sum-measure functional that binds {} binder(s) where this lowering at arity \
                 {arity} binds {} (the course-of-values bound, the recursive slot, one per \
                 parameter, and the measure hypothesis)",
                telescope.len(),
                layout.binders
            )));
        };
        telescope.push(gate_strip_mdata(ty));
        cursor = gate_strip_mdata(inner);
    }
    if !gate_is_nat(telescope[0]) {
        return Err(refuse(
            "a sum-measure functional whose course-of-values bound is not at `Nat`".to_owned(),
        ));
    }
    for (source_index, ty) in telescope[2..2 + arity].iter().enumerate() {
        if !gate_is_nat(ty) {
            return Err(refuse(format!(
                "a sum-measure functional that re-binds parameter {source_index} at a type other \
                 than `Nat`"
            )));
        }
    }
    // `rec : (k : Nat) → Nat.lt k n → C k`, BORROWED.
    //
    // Read structurally rather than by equality against a rebuilt term: binder
    // NAMES take part in `Expr` equality and this reader must not depend on
    // what the elaborator called its binders. The codomain is the un-reduced
    // redex `C k` the lowering builds; the beta-reduced spelling is accepted
    // too, because the two are the same type and neither is this crate's to
    // prefer.
    {
        let ExprKind::Pi(_, k_ty, after_k) = telescope[1].kind() else {
            return Err(refuse(
                "a sum-measure functional that does not bind a recursive slot".to_owned(),
            ));
        };
        if !gate_is_nat(k_ty) {
            return Err(refuse(
                "a sum-measure functional whose recursive slot does not take a `Nat` major \
                 premise; this lowering recurses on the measure's VALUE"
                    .to_owned(),
            ));
        }
        let ExprKind::Pi(_, k_lt_n, codomain) = gate_strip_mdata(after_k).kind() else {
            return Err(refuse(
                "a sum-measure functional whose recursive slot does not demand a decrease proof, \
                 so it is not a well-founded slot at all"
                    .to_owned(),
            ));
        };
        let raw_lt = {
            let (lt_head, lt_args) = gate_uncurry(gate_strip_mdata(k_lt_n));
            gate_is_bare_const(lt_head, "Nat.lt")
                && lt_args.len() == 2
                && matches!(gate_strip_mdata(lt_args[0]).kind(), ExprKind::BVar(0))
                && matches!(gate_strip_mdata(lt_args[1]).kind(), ExprKind::BVar(1))
        };
        if !raw_lt {
            return Err(refuse(
                "a sum-measure functional whose recursive slot demands something other than \
                 `Nat.lt k n`. This binder's type is one the gate BORROWS from the declaration — \
                 the emitted body computes a guard, two branch values and a self-call's \
                 arguments and contains no measure at all — so what it holds is checked here \
                 rather than taken on trust.\n\
                 options:\n\
                 - if the compiler produced this functional, report it with the declaration;\n\
                 - keep the declaration for proof position and call a helper this lane parses"
                    .to_owned(),
            ));
        }
        let codomain = gate_strip_mdata(codomain);
        let redex = matches!(codomain.kind(), ExprKind::App(function, argument)
            if *gate_strip_mdata(function) == *motive
                && matches!(gate_strip_mdata(argument).kind(), ExprKind::BVar(1)));
        let reduced = *codomain == gate_strip_mdata(motive_body).instantiate(&Expr::bvar(1));
        if !(redex || reduced) {
            return Err(refuse(
                "a sum-measure functional whose recursive slot returns at something other than \
                 the fix's own motive applied to the major premise"
                    .to_owned(),
            ));
        }
    }
    // `hm : Nat.lt m n`, BORROWED, at the context [n, rec, p⃗] — where `n` is
    // `BVar(arity + 1)` and source parameter `i` is `BVar(arity - 1 - i)`, the
    // same spelling the seed uses.
    let hm_bound = u32::try_from(arity + 1).unwrap_or(u32::MAX);
    if !gate_is_raw_nat_lt_at(telescope[arity + 2], &measure, hm_bound) {
        return Err(refuse(
            "a sum-measure functional whose last binder is not the measure hypothesis \
             `Nat.lt m n` at the measure its seed carries. Without it the recursive slot has no \
             argument to be applied to and this is not the sum-measure lowering — and this \
             binder's type is BORROWED, so the gate decides what it holds instead of inheriting \
             it.\n\
             options:\n\
             - if the compiler produced this functional, report it with the declaration;\n\
             - keep the declaration for proof position and call a helper this lane parses"
                .to_owned(),
        ));
    }
    Ok(measure)
}

/// **R3e — the gate's own read of every PHASE-3 SELF-CALL's borrowed
/// positions**, over the slots the gate's own walk collected from side A.
///
/// A self-call is `rec m hm a⃗ prf`. Two of those the gate borrows:
///
/// * `m`, the MAJOR premise — the measure at THIS call site's enclosing
///   parameters, i.e. the seed's spelling lifted out of the declaration's
///   context into the functional's. Side B writes [`MEASURE_SLOT_SENTINEL`]
///   here and receives side A's term.
/// * `prf`, the decrease proof, which [`fill_decrease_slots`] borrows.
///
/// `hm` is checked beside the major premise although it is NOT borrowed,
/// because it is what pins the major premise down: `rec m hm : Π p⃗', Nat.lt
/// m[p⃗'] m → ret` only when `hm` is the functional's own hypothesis binder, so
/// a side A that reached the same slot through some other proof of
/// `Nat.lt m' n` would have `m'` borrowed into side B unexamined.
///
/// Deliberately over the ALREADY-COLLECTED slots rather than a second walk:
/// [`collect_decrease_slots`] is the gate's own traversal, it is bounded by
/// [`FUNCTIONAL_NODE_LIMIT`], and it has already established that every use of
/// `rec` is a full self-call. Walking twice would only give two places for the
/// call-site rule to drift.
///
/// # Errors
///
/// [`GateRefusal::NotWellFoundedRecursor`] — this is a statement about SIDE A,
/// not about the borrow, so it is not a `DecreaseSlotBorrowRefused`.
fn require_sum_measure_calls(
    name: &str,
    source: &WfBorrowSource,
    layout: WfBorrowLayout,
    measure: &Expr,
) -> Result<(), GateRefusal> {
    let refuse =
        |found: String| GateRefusal::NotWellFoundedRecursor { name: name.to_owned(), found };
    for slot in &source.slots {
        // `slot.depth` counts from the functional's `rec` binder; the measure
        // is lifted by the binders entered SINCE the functional's body, plus
        // one for `hm` itself.
        let entered = slot.depth.saturating_sub(layout.rec_depth);
        if slot.major != measure.lift(entered.saturating_add(1)) {
            return Err(refuse(
                "a sum-measure self-call whose MAJOR PREMISE is not the measure at the enclosing \
                 parameters. That position is BORROWED: side B cannot author a measure, writes \
                 the sentinel there, and receives whatever this declaration holds — so the gate \
                 decides what that is rather than inheriting the assumption from the plan lane. \
                 A term that is merely definitionally equal to the measure is refused too, \
                 because the borrow copies the TERM.\n\
                 options:\n\
                 - if the compiler produced this functional, report it with the declaration;\n\
                 - keep the declaration for proof position and call a helper this lane parses"
                    .to_owned(),
            ));
        }
        if !matches!(gate_strip_mdata(&slot.hypothesis).kind(),
            &ExprKind::BVar(index) if index == entered)
        {
            return Err(refuse(
                "a sum-measure self-call that does not pass the functional's own measure \
                 hypothesis to the recursive slot, so the major premise beside it is not pinned \
                 to the measure and the call is not this lowering's"
                    .to_owned(),
            ));
        }
    }
    Ok(())
}

/// The de Bruijn layout ONE borrow runs at, derived from the lowering and the
/// arity the gate parsed out of side A's own spine.
///
/// R3c gathered four numbers that were previously computed at five call sites
/// into one value, because phase 3 moves ALL of them at once: the functional
/// opens one more binder, `rec` sits `arity + 1` out instead of `arity - 1`, a
/// self-call carries two more arguments, and the decrease proof stops being the
/// second argument and becomes the last. Deriving them separately at each site
/// is how a reader silently reads one lowering at the other's layout.
///
/// **Phase 2's numbers are unchanged**, and `tests/phase3_spine_reader_probes`
/// asserts that against the literals R2/R3a shipped rather than against this
/// function.
#[derive(Clone, Copy)]
struct WfBorrowLayout {
    /// How many binders the functional opens before its body.
    binders: usize,
    /// Where `rec` sits at the functional's body.
    rec_depth: u32,
    /// How many arguments one self-call carries.
    call_arity: usize,
    /// Which of those arguments is the decrease slot.
    proof_position: usize,
    /// Which lowering — R3d, because the MEASURE borrow exists at one of them
    /// and must be refused at the other.
    lowering: WfLowering,
    /// Which telescope positions hold a type stated in terms of the MEASURE,
    /// and are therefore borrowed. Empty at phase 2.
    measure_binders: &'static [usize],
    /// The telescope position of `hm`, phase 3's measure hypothesis. `None` at
    /// phase 2, which has no such binder.
    hypothesis_binder: Option<usize>,
}

impl WfBorrowLayout {
    fn of(lowering: WfLowering, arity: usize) -> Self {
        Self {
            binders: lowering.functional_binders(arity),
            rec_depth: lowering.rec_binder_depth(arity),
            call_arity: lowering.rec_call_arity(arity),
            proof_position: lowering.decrease_slot_position(arity),
            lowering,
            measure_binders: match lowering {
                WfLowering::OnParameter => &[],
                // `rec` is always binder 1; `hm` is the innermost, which
                // `hypothesis_binder` names. Both are checked against
                // `binders`, never assumed in range.
                WfLowering::OnMeasureValue => &[1],
            },
            hypothesis_binder: match lowering {
                WfLowering::OnParameter => None,
                WfLowering::OnMeasureValue => Some(arity + 2),
            },
        }
    }

    /// Whether the binder at `position` is one whose TYPE the borrow supplies.
    fn is_measure_binder(self, position: usize) -> bool {
        self.measure_binders.contains(&position) || self.hypothesis_binder == Some(position)
    }

    /// Whether the self-call argument at `position` is one the borrow supplies.
    ///
    /// Position 0 is the MAJOR PREMISE. Phase 2's is the decreasing argument —
    /// side B's to author and the comparison's to decide (probe w7/d3 measured
    /// that a well-typed `x - 2` against side A's `x - 1` is REFUSED by defeq),
    /// so it is NOT borrowed. Phase 3's is the measure.
    fn is_measure_argument(self, position: usize) -> bool {
        position == 0 && matches!(self.lowering, WfLowering::OnMeasureValue)
    }
}

/// Peel a functional's binders — `fun (x : α) (rec : …) (threaded : α)^(N-1) =>
/// BODY` at phase 2, `fun (n) (rec) (p⃗) (hm) => BODY` at phase 3 — exactly
/// `layout.binders` of them.
///
/// EXACTLY, not at least: the count is the cross-check between side A's spine
/// (which said arity N in lowering L) and side A's functional (which must bind
/// what L binds). Peeling greedily would read a functional whose telescope
/// disagreed with its own spine at whatever layout it happened to have, and
/// every de Bruijn index downstream is computed from that number.
fn peel_functional(f: &Expr, layout: WfBorrowLayout) -> Result<&Expr, String> {
    let mut cursor = gate_strip_mdata(f);
    for binder in 0..layout.binders {
        let ExprKind::Lam(_, _, inner) = cursor.kind() else {
            return Err(match binder {
                0 => "the functional is not a lambda over the recursion's argument".to_owned(),
                1 => "the functional does not bind a recursive slot".to_owned(),
                _ => format!(
                    "the functional binds {binder} binder(s) where this lowering binds {}",
                    layout.binders
                ),
            });
        };
        cursor = gate_strip_mdata(inner);
    }
    if matches!(cursor.kind(), ExprKind::Lam(..)) {
        return Err(format!(
            "the functional binds more than the {} binder(s) this lowering binds, so its \
             telescope disagrees with its own `WellFounded.fix` spine",
            layout.binders
        ));
    }
    Ok(cursor)
}

/// Collect side A's decrease-slot proof terms, in a deterministic pre-order.
///
/// Every use of the `rec` binder must be a **two-argument application**
/// `rec <arg> <proof>`. Anything else — a bare or partially applied `rec`, or
/// one applied to more arguments — refuses: a slot the walk cannot see is a
/// slot the borrow cannot fill and the audit cannot cover, and silently
/// tolerating one would reopen the hole this lane exists to close.
fn collect_decrease_slots(f: &Expr, layout: WfBorrowLayout) -> Result<WfBorrowSource, String> {
    let body = peel_functional(f, layout)?;
    let mut slots = Vec::new();
    walk_functional(body, layout.rec_depth, layout, 0, 0, &mut |args: &[&Expr], depth: u32| {
        slots.push(DecreaseSlot {
            depth,
            proof: args[layout.proof_position].clone(),
            major: args[0].clone(),
            // Position 1 always exists: `walk_functional` has just required the
            // call to carry `layout.call_arity` arguments, which is `arity + 1`
            // or `arity + 3` at `arity >= 1`.
            hypothesis: args[1].clone(),
        });
        Ok(())
    })?;
    // Side A's own binder types, outside-in. `peel_functional` above has
    // already established that there are exactly `layout.binders` of them.
    let mut binder_tys = Vec::with_capacity(layout.binders);
    let mut cursor = gate_strip_mdata(f);
    for _ in 0..layout.binders {
        let ExprKind::Lam(_, ty, inner) = cursor.kind() else {
            return Err("side A's functional telescope changed length between two reads".to_owned());
        };
        binder_tys.push((**ty).clone());
        cursor = gate_strip_mdata(inner);
    }
    Ok(WfBorrowSource { slots, binder_tys })
}

/// Uncurry an application spine, outermost head first.
fn gate_uncurry(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args: Vec<&Expr> = Vec::new();
    let mut head = gate_strip_mdata(expr);
    while let ExprKind::App(function, argument) = head.kind() {
        args.push(gate_strip_mdata(argument));
        head = gate_strip_mdata(function);
    }
    args.reverse();
    (head, args)
}

/// Walk a functional body, reporting each self-call's decrease slot.
///
/// `depth` counts binders entered since the `rec` binder, so `rec` is
/// `BVar(depth)` at the current node. `layout` says how many arguments a
/// self-call must carry and which of them is the decrease proof — the two
/// numbers phase 3 moves. `visited` is the shared node budget.
///
/// `descent` is the shared STACK budget, and it is not `depth`: `depth` counts
/// BINDERS, and an application spine adds none of those while costing a frame
/// per level. See [`FUNCTIONAL_DEPTH_LIMIT`].
fn walk_functional(
    expr: &Expr,
    depth: u32,
    layout: WfBorrowLayout,
    mut visited: usize,
    descent: usize,
    report: &mut dyn FnMut(&[&Expr], u32) -> Result<(), String>,
) -> Result<usize, String> {
    let call_arity = layout.call_arity;
    visited = visited.checked_add(1).ok_or("the functional exceeded its traversal envelope")?;
    if visited > FUNCTIONAL_NODE_LIMIT {
        return Err(format!(
            "the functional exceeded its {FUNCTIONAL_NODE_LIMIT}-node traversal envelope"
        ));
    }
    // Checked BEFORE any recursive call below, so the frame that would have
    // overflowed is the one that refuses.
    let descent = descent
        .checked_add(1)
        .ok_or_else(|| crate::emit::depth_envelope_refusal("the functional"))?;
    if descent > FUNCTIONAL_DEPTH_LIMIT {
        return Err(crate::emit::depth_envelope_refusal("the functional"));
    }
    let cursor = gate_strip_mdata(expr);
    match cursor.kind() {
        ExprKind::BVar(index) if *index == depth => Err(format!(
            "the recursive slot is used somewhere other than as a {call_arity}-argument \
             self-call, so a decrease slot could not be located"
        )),
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::Lit(_) => Ok(visited),
        ExprKind::App(function, argument) => {
            // The WHOLE self-call spine is recognised here, so the `rec` binder
            // itself is never visited as a bare occurrence and a PARTIALLY
            // applied `rec` reaches the `BVar(depth)` arm above or the count
            // check below rather than passing silently.
            let (head, args) = gate_uncurry(cursor);
            if matches!(head.kind(), ExprKind::BVar(index) if *index == depth) {
                if args.len() != call_arity {
                    return Err(format!(
                        "the recursive slot is applied to {} argument(s) where a self-call at \
                         this arity and lowering carries {call_arity}, so a decrease slot could \
                         not be located",
                        args.len()
                    ));
                }
                report(&args, depth)?;
                for argument in args {
                    visited = walk_functional(argument, depth, layout, visited, descent, report)?;
                }
                return Ok(visited);
            }
            visited = walk_functional(function, depth, layout, visited, descent, report)?;
            walk_functional(argument, depth, layout, visited, descent, report)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            visited = walk_functional(ty, depth, layout, visited, descent, report)?;
            walk_functional(body, depth + 1, layout, visited, descent, report)
        }
        ExprKind::Let(_, ty, value, body, _) => {
            visited = walk_functional(ty, depth, layout, visited, descent, report)?;
            visited = walk_functional(value, depth, layout, visited, descent, report)?;
            walk_functional(body, depth + 1, layout, visited, descent, report)
        }
        ExprKind::Proj(_, _, inner) => {
            walk_functional(inner, depth, layout, visited, descent, report)
        }
        other => Err(format!(
            "the functional leaves the core expression fragment this lane is measured over \
             ({}), so its recursive call sites cannot be located",
            core_fragment_name(other)
        )),
    }
}

/// Fill side B's sentinels with side A's proofs, one call site at a time.
///
/// The pairing is by traversal order, and the walk is the same one that
/// collected side A's slots. A mis-pairing cannot produce a false admission:
/// the borrowed proof would fail to type at side B's argument (step 7's
/// `check_type`) or the functionals would differ (step 8's defeq). The only
/// outcomes are the right borrow or a refusal.
fn fill_decrease_slots(
    f: &Expr,
    layout: WfBorrowLayout,
    source: &WfBorrowSource,
    sentinels: Sentinels<'_>,
) -> Result<Expr, String> {
    let slots = source.slots.as_slice();
    let body = peel_functional(f, layout)?;
    let mut index = 0usize;
    let mut filled = rebuild_functional(
        body,
        layout.rec_depth,
        layout,
        &mut 0,
        0,
        &mut index,
        slots,
        sentinels,
    )?;
    if index != slots.len() {
        return Err(format!(
            "side B's functional has {index} recursive call site(s) where side A's has {} — a \
             borrow is only defined when the two agree",
            slots.len()
        ));
    }
    // Re-clothe side B's binders. Collected outside-in and re-applied
    // inside-out, so a threaded binder cannot silently change position — which
    // would change what every `Param` index in the body denotes.
    //
    // R3d: at phase 3 exactly TWO of those positions hold a type stated in
    // terms of the measure (`rec` and `hm`), which MIR contains no trace of.
    // Side B must write the bare measure sentinel there and side A's own type
    // at the same position is used. Every OTHER position is side B's own, and
    // a measure sentinel at one of them is refused — the borrow is three fixed
    // positions, never a licence to blank a binder.
    let mut binders = Vec::with_capacity(layout.binders);
    let mut cursor = gate_strip_mdata(f);
    for binder in 0..layout.binders {
        let ExprKind::Lam(info, ty, inner) = cursor.kind() else {
            return Err(match binder {
                0 => "the functional is not a lambda over the recursion's argument".to_owned(),
                1 => "the functional does not bind a recursive slot".to_owned(),
                _ => format!(
                    "side B's functional binds {binder} binder(s) where this lowering binds {}",
                    layout.binders
                ),
            });
        };
        let wrote_sentinel = is_bare_sentinel(ty, sentinels.measure);
        let borrowed = match (layout.is_measure_binder(binder), wrote_sentinel) {
            (true, true) => source.binder_tys.get(binder).cloned().ok_or_else(|| {
                "side A's functional telescope is shorter than the lowering it was parsed at, so \
                 there is no type at the measure binder to borrow"
                    .to_owned()
            })?,
            (true, false) => {
                return Err(format!(
                    "side B supplied its own type at binder {binder}, which this lowering states \
                     in terms of the `termination_by` MEASURE. Side B may not author the measure: \
                     the emitted body computes a guard, two branch values and a self-call's \
                     arguments, and contains no measure at all. Write the binder's type as the \
                     sentinel `{}` and it is borrowed from the declaration",
                    sentinels.measure
                ));
            }
            (false, true) => {
                return Err(format!(
                    "side B wrote the measure sentinel `{}` at binder {binder}, which is not one \
                     of the positions this lowering states in terms of the measure, so nothing \
                     could be borrowed for it",
                    sentinels.measure
                ));
            }
            (false, false) => (**ty).clone(),
        };
        binders.push((*info, borrowed));
        cursor = gate_strip_mdata(inner);
    }
    for (info, ty) in binders.into_iter().rev() {
        filled = Expr::lam(info, ty, filled);
    }
    Ok(filled)
}

/// The two constants side B may write where a term it cannot author belongs.
///
/// Passed as one value so no call site can pass the decrease sentinel where the
/// measure sentinel belongs — they are both `&Name` and the compiler would not
/// notice.
#[derive(Clone, Copy)]
struct Sentinels<'a> {
    decrease: &'a Name,
    measure: &'a Name,
}

/// Whether `expr` is exactly the bare sentinel constant, at no universe
/// arguments.
fn is_bare_sentinel(expr: &Expr, sentinel: &Name) -> bool {
    matches!(gate_strip_mdata(expr).kind(), ExprKind::Const(name, levels)
        if name == sentinel && levels.is_empty())
}

/// The rebuild half of [`walk_functional`], structurally identical so the two
/// cannot drift about which nodes are call sites — including about the two
/// rails: `visited` is the shared node budget, `descent` the shared stack
/// budget ([`FUNCTIONAL_DEPTH_LIMIT`]).
fn rebuild_functional(
    expr: &Expr,
    depth: u32,
    layout: WfBorrowLayout,
    visited: &mut usize,
    descent: usize,
    index: &mut usize,
    slots: &[DecreaseSlot],
    sentinels: Sentinels<'_>,
) -> Result<Expr, String> {
    let call_arity = layout.call_arity;
    *visited = visited.checked_add(1).ok_or("the functional exceeded its traversal envelope")?;
    if *visited > FUNCTIONAL_NODE_LIMIT {
        return Err(format!(
            "the functional exceeded its {FUNCTIONAL_NODE_LIMIT}-node traversal envelope"
        ));
    }
    // Checked BEFORE any recursive call below, so the frame that would have
    // overflowed is the one that refuses.
    let descent = descent
        .checked_add(1)
        .ok_or_else(|| crate::emit::depth_envelope_refusal("side B's functional"))?;
    if descent > FUNCTIONAL_DEPTH_LIMIT {
        return Err(crate::emit::depth_envelope_refusal("side B's functional"));
    }
    // Metadata wrappers are transparent to type checking; the borrow drops
    // them rather than reconstructing them, which changes nothing the kernel
    // reads and keeps this rebuild total over the fragment.
    let cursor = gate_strip_mdata(expr);
    match cursor.kind() {
        ExprKind::BVar(i) if *i == depth => Err(format!(
            "side B uses its recursive slot somewhere other than as a {call_arity}-argument \
             self-call, so the gate cannot tell where a decrease proof would go"
        )),
        ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {
            Ok(cursor.clone())
        }
        ExprKind::Const(name, _) if name == sentinels.decrease => Err(
            "side B wrote a decrease-slot sentinel outside a recursive call site, where no proof \
             could be borrowed for it"
                .to_owned(),
        ),
        ExprKind::Const(name, _) if name == sentinels.measure => Err(
            "side B wrote a measure sentinel outside the three positions this lowering states in \
             terms of the `termination_by` measure, where nothing could be borrowed for it"
                .to_owned(),
        ),
        ExprKind::Const(_, _) => Ok(cursor.clone()),
        ExprKind::App(function, argument) => {
            let (head, args) = gate_uncurry(cursor);
            if matches!(head.kind(), ExprKind::BVar(i) if *i == depth) {
                if args.len() != call_arity {
                    return Err(format!(
                        "side B applies its recursive slot to {} argument(s) where a self-call at \
                         this arity and lowering carries {call_arity}, so the gate cannot tell \
                         where a decrease proof would go",
                        args.len()
                    ));
                }
                // THE BORROW, at one call site.
                let Some(slot) = slots.get(*index) else {
                    return Err("side B has more recursive call sites than side A".to_owned());
                };
                if slot.depth != depth {
                    return Err(format!(
                        "side B's recursive call sits under {depth} binder(s) where side A's sits \
                         under {} — side A's proof term would be read against a different \
                         variable context, so it is not borrowable here",
                        slot.depth
                    ));
                }
                if !is_bare_sentinel(args[layout.proof_position], sentinels.decrease) {
                    return Err(
                        "side B supplied its own term in a decrease slot. Side B may not author a \
                         decrease proof: it is the term the recursion's termination rests on, and \
                         MIR contains none. Write the slot as the sentinel and it is borrowed \
                         from the declaration"
                            .to_owned(),
                    );
                }
                // R3d: at phase 3 the call's FIRST argument is the major
                // premise — the measure at the enclosing parameters — which
                // side B likewise cannot author. Same rule, same shape, and
                // refused the same way when side B writes its own term there.
                if layout.is_measure_argument(0)
                    && !is_bare_sentinel(args[0], sentinels.measure)
                {
                    return Err(format!(
                        "side B supplied its own term as the self-call's major premise, which the \
                         sum-measure lowering states as the `termination_by` MEASURE at the \
                         enclosing parameters. Side B may not author the measure: the emitted \
                         body contains none. Write the position as the sentinel `{}` and it is \
                         borrowed from the declaration",
                        sentinels.measure
                    ));
                }
                *index += 1;
                // Rebuild every argument EXCEPT the proof slot, which is
                // replaced wholesale by side A's. The threaded arguments are
                // ordinary values and are rebuilt exactly like any other
                // sub-term — a threaded argument that itself contained a
                // self-call would be borrowed for at its own site, in this same
                // deterministic pre-order.
                let mut rebuilt = head.clone();
                for (position, argument) in args.iter().enumerate() {
                    let piece = if position == layout.proof_position {
                        slot.proof.clone()
                    } else if layout.is_measure_argument(position) {
                        slot.major.clone()
                    } else {
                        rebuild_functional(
                            argument, depth, layout, visited, descent, index, slots, sentinels,
                        )?
                    };
                    rebuilt = Expr::app(rebuilt, piece);
                }
                return Ok(rebuilt);
            }
            let rebuilt_fn = rebuild_functional(
                function, depth, layout, visited, descent, index, slots, sentinels,
            )?;
            let rebuilt_arg = rebuild_functional(
                argument, depth, layout, visited, descent, index, slots, sentinels,
            )?;
            Ok(Expr::app(rebuilt_fn, rebuilt_arg))
        }
        ExprKind::Lam(binder, ty, body) => {
            let rebuilt_ty =
                rebuild_functional(ty, depth, layout, visited, descent, index, slots, sentinels)?;
            let rebuilt_body = rebuild_functional(
                body,
                depth + 1,
                layout,
                visited,
                descent,
                index,
                slots,
                sentinels,
            )?;
            Ok(Expr::lam(*binder, rebuilt_ty, rebuilt_body))
        }
        ExprKind::Pi(binder, ty, body) => {
            let rebuilt_ty =
                rebuild_functional(ty, depth, layout, visited, descent, index, slots, sentinels)?;
            let rebuilt_body = rebuild_functional(
                body,
                depth + 1,
                layout,
                visited,
                descent,
                index,
                slots,
                sentinels,
            )?;
            Ok(Expr::pi(*binder, rebuilt_ty, rebuilt_body))
        }
        ExprKind::Let(binder_name, ty, value, body, non_dep) => {
            let rebuilt_ty =
                rebuild_functional(ty, depth, layout, visited, descent, index, slots, sentinels)?;
            let rebuilt_value = rebuild_functional(
                value, depth, layout, visited, descent, index, slots, sentinels,
            )?;
            let rebuilt_body = rebuild_functional(
                body,
                depth + 1,
                layout,
                visited,
                descent,
                index,
                slots,
                sentinels,
            )?;
            Ok(Expr::let_named(
                binder_name.clone(),
                rebuilt_ty,
                rebuilt_value,
                rebuilt_body,
                *non_dep,
            ))
        }
        ExprKind::Proj(structure, field, inner) => {
            let rebuilt = rebuild_functional(
                inner, depth, layout, visited, descent, index, slots, sentinels,
            )?;
            Ok(Expr::proj(structure.clone(), *field, rebuilt))
        }
        other => Err(format!(
            "side B's functional leaves the core expression fragment this lane is measured over \
             ({})",
            core_fragment_name(other)
        )),
    }
}

/// A bounded, static-shaped name for an out-of-fragment expression kind.
///
/// Never renders the expression: a rejected user-sized term must not allocate
/// an unbounded diagnostic.
fn core_fragment_name(kind: &ExprKind) -> &'static str {
    match kind {
        ExprKind::SProp => "SProp",
        ExprKind::Squash(_) => "a Squash type",
        ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1
        | ExprKind::CubicalPath { .. }
        | ExprKind::CubicalPathLam { .. }
        | ExprKind::CubicalPathApp { .. } => "a cubical expression",
        _ => "an expression kind outside the core fragment",
    }
}

// ───────────────────────────────────────────────────────────────────────────
// R3e — THE STACK RAIL ON THE TWO FUNCTIONAL WALKS, MUTATION-PROVED
// ───────────────────────────────────────────────────────────────────────────

/// [`FUNCTIONAL_DEPTH_LIMIT`] decided rather than asserted.
///
/// Every row runs its walk on a thread with an **explicitly sized stack**,
/// derived from the same two measurements the rail itself is derived from
/// ([`crate::emit::SUM_MEASURE_DEPTH_LIMIT`]): a full-depth descent fits in
/// [`crate::emit::DESCENT_STACK_BUDGET`] by construction, so a probe thread of
/// twice that holds one with room, and a rail that had stopped bounding the
/// descent would overflow the thread rather than quietly pass.
///
/// # What each row fails on, on a build without the rail
///
/// * `d1` walks one level PAST the rail — a size that does not crash, so on an
///   unrailed build it fails as an ordinary assertion (the walk returns `Ok`)
///   instead of taking the test binary down with it. This is the row that
///   fails, red and readable, without the fix.
/// * `d2` walks a term 150,000 levels deep. That is inside the 262,144-node
///   budget — a lambda chain costs two nodes per level, so the node rail would
///   not fire until about level 131,072 — and 240x past the ~620 levels an
///   8 MB stack holds at the measured 13,552 B frame. On an unrailed build this
///   row does not fail, it **SIGSEGVs**: it is the crash itself, executed.
/// * `d3` keeps the rail's own derivation honest.
#[cfg(test)]
mod bounded_descent_tests {
    use super::*;

    /// Twice the stack budget the rail is derived from, so a full-depth descent
    /// fits with 2x room and a runaway one does not.
    const PROBE_STACK: usize = 2 * crate::emit::DESCENT_STACK_BUDGET;

    /// `fun (_ : Nat) => … => Nat`, exactly `levels` lambdas deep.
    ///
    /// Built with a fold, never recursively: the point of these terms is that a
    /// recursive walk over them does not return, and that would include a walk
    /// that built one. Releasing one is safe for the same reason from the other
    /// side — `Expr`'s own `Drop` switches to an iterative teardown once cached
    /// depth saturates (`clean-kernel`'s `expr/drop.rs`).
    fn lam_chain(levels: usize) -> Expr {
        let leaf = Expr::const_(Name::from_string("Nat"), vec![]);
        (0..levels)
            .fold(leaf.clone(), |inner, _| Expr::lam(BinderInfo::Default, leaf.clone(), inner))
    }

    /// Phase 2 at arity 1, the shallowest layout, so the peeled body is the
    /// chain itself and the harness contributes no depth of its own.
    fn layout() -> WfBorrowLayout {
        WfBorrowLayout::of(WfLowering::OnParameter, 1)
    }

    /// Run `f` on a thread of [`PROBE_STACK`] bytes and return its value.
    ///
    /// An overflow inside `f` aborts the process — which is exactly the defect
    /// under test, and the harness reports it as a hard failure rather than a
    /// passing row.
    fn on_a_bounded_stack<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
        std::thread::Builder::new()
            .stack_size(PROBE_STACK)
            .spawn(f)
            .expect("the probe thread must spawn")
            .join()
            .expect("the walk must return a value rather than unwind or overflow the stack")
    }

    fn walk(levels: usize) -> Result<usize, String> {
        let body = lam_chain(levels);
        let layout = layout();
        walk_functional(&body, layout.rec_depth, layout, 0, 0, &mut |_: &[&Expr], _: u32| Ok(()))
    }

    fn rebuild(levels: usize) -> Result<Expr, String> {
        let body = lam_chain(levels);
        let layout = layout();
        let decrease = Name::from_string(DECREASE_SLOT_SENTINEL);
        let measure = Name::from_string(MEASURE_SLOT_SENTINEL);
        let sentinels = Sentinels { decrease: &decrease, measure: &measure };
        rebuild_functional(&body, layout.rec_depth, layout, &mut 0, 0, &mut 0, &[], sentinels)
    }

    /// The two halves of the refusal v7/D3 requires: the bound, and the fix.
    fn assert_names_the_bound_and_the_fix(who: &str, message: &str) {
        assert!(
            message.contains(&FUNCTIONAL_DEPTH_LIMIT.to_string()),
            "{who}'s refusal must NAME the bound it hit; got {message}"
        );
        assert!(
            message.contains("Options:"),
            "v7/D3: a refusal must carry the fix, with options. {who} said {message}"
        );
        assert!(
            message.contains("DESCENT_STACK_BUDGET"),
            "{who}'s refusal must name what actually moves the rail — it is derived, so \
             'raise the number' is not by itself a fix; got {message}"
        );
    }

    /// **(d1) ONE LEVEL PAST THE RAIL IS A REFUSAL, AND THE RAIL IS NOT A
    /// FRAGMENT BOUNDARY.**
    ///
    /// Both halves are load-bearing. A term exactly AT the rail must still be
    /// read — a resource number that quietly narrowed what is readable would be
    /// a capability change wearing a resource number, which v7/D2 forbids — and
    /// the term one level deeper must refuse with a message that names the
    /// bound and what to do about it.
    #[test]
    fn d1_the_walks_refuse_one_level_past_the_rail() {
        // `lam_chain(n)` is n lambdas over a leaf, so the descent is n + 1
        // frames: the rail admits `FUNCTIONAL_DEPTH_LIMIT - 1` lambdas.
        let at_limit = FUNCTIONAL_DEPTH_LIMIT - 1;

        let accepted = on_a_bounded_stack(move || walk(at_limit));
        assert!(
            accepted.is_ok(),
            "a term exactly at the rail must still be walked, or the number has become a \
             fragment boundary. Got {accepted:?}"
        );
        let rebuilt = on_a_bounded_stack(move || rebuild(at_limit));
        assert!(
            rebuilt.is_ok(),
            "…and the same for the rebuild half, which must agree with the walk about every \
             term it is handed. Got {}",
            rebuilt.err().unwrap_or_default()
        );

        let refused = on_a_bounded_stack(move || walk(at_limit + 1))
            .expect_err("one level past the rail must refuse");
        assert_names_the_bound_and_the_fix("walk_functional", &refused);

        let refused = on_a_bounded_stack(move || rebuild(at_limit + 1))
            .expect_err("one level past the rail must refuse");
        assert_names_the_bound_and_the_fix("rebuild_functional", &refused);
    }

    /// **(d2) THE CRASH SCALE — a term the kernel accepts and these walks used
    /// to die on.**
    ///
    /// `clean-kernel` descends terms this deep safely because it grows its own
    /// stack (`stack_safe`). These walks do not, so before R3e this row was a
    /// `SIGSEGV` in `trustc`, not a refusal. It is the regression test for the
    /// defect itself; `d1` is the one that stays readable when it fires.
    #[test]
    fn d2_a_crash_scale_term_refuses_instead_of_overflowing_the_stack() {
        const CRASH_SCALE: usize = 150_000;
        // The premises, asserted so they cannot rot into a row that measures
        // nothing. A lambda chain costs two nodes per level.
        assert!(
            2 * CRASH_SCALE > FUNCTIONAL_NODE_LIMIT,
            "if the NODE budget alone caught this term there would be nothing to fix — the \
             whole defect is that the node rail stopped implying a depth rail"
        );
        assert!(
            CRASH_SCALE * crate::emit::WIDEST_MEASURED_FRAME > 8 * 1024 * 1024,
            "the term must be deeper than an 8 MB stack holds at the measured frame width, or \
             the row is not standing where the crash was"
        );

        let walked = on_a_bounded_stack(|| walk(CRASH_SCALE))
            .expect_err("a crash-scale term must refuse, not be read");
        assert!(
            walked.contains(&FUNCTIONAL_DEPTH_LIMIT.to_string()),
            "the refusal must be the DEPTH rail's, not the node budget's — the node budget \
             fires only after ~131,000 frames, which is well past the crash. Got {walked}"
        );
        let rebuilt = on_a_bounded_stack(|| rebuild(CRASH_SCALE))
            .expect_err("a crash-scale term must refuse, not be rebuilt");
        assert!(
            rebuilt.contains(&FUNCTIONAL_DEPTH_LIMIT.to_string()),
            "the rebuild half must refuse on the same rail as the walk. Got {rebuilt}"
        );
    }

    /// **(d3) THE RAIL'S DERIVATION, PINNED.**
    ///
    /// The number is `DESCENT_STACK_BUDGET / WIDEST_MEASURED_FRAME` and it has
    /// to stay between two things: above the deepest term this lane has ever
    /// been shown (`gcd_phase3_probes` p1 measures the shipped phase-3
    /// functional at 14,283 nodes and **53 levels**), and below the node budget,
    /// which already bounds depth from above and would make a depth rail
    /// vacuous.
    #[test]
    fn d3_the_rail_sits_between_the_deepest_real_term_and_the_node_budget() {
        const DEEPEST_MEASURED_FUNCTIONAL: usize = 53;
        assert!(
            FUNCTIONAL_DEPTH_LIMIT > 4 * DEEPEST_MEASURED_FUNCTIONAL,
            "the rail must clear the deepest measured functional several times over, or a \
             legitimate program refuses on a resource number; it is {FUNCTIONAL_DEPTH_LIMIT} \
             against {DEEPEST_MEASURED_FUNCTIONAL}"
        );
        assert!(
            FUNCTIONAL_DEPTH_LIMIT < FUNCTIONAL_NODE_LIMIT,
            "a depth rail at or above the node budget is not a rail at all — a term cannot \
             nest deeper than it has nodes"
        );
        assert!(
            FUNCTIONAL_DEPTH_LIMIT * crate::emit::WIDEST_MEASURED_FRAME
                <= crate::emit::DESCENT_STACK_BUDGET,
            "a full-depth descent must fit the stack budget the rail was derived from; if this \
             fires, the frame was re-measured without re-deriving the rail"
        );
    }
}
