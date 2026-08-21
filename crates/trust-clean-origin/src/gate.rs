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
//! This module is the gate's *decision*. It is a plain function so that the
//! provider wiring — which is blocked, see the crate docs — cannot change what
//! the gate decides, only when it runs.
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
//! `CarrierEvidence::Total`. Defeq decides *did the lowering mistranslate*; the
//! carrier decides *can the result be represented at all*. Neither subsumes the
//! other and the gate demands both.
//!
//! # Fail-closed
//!
//! `clean_kernel::TypeChecker::is_def_eq` is two-valued, and a budget-exhausted
//! decision reports `false`. That is the correct polarity here: an undecided
//! comparison must REFUSE, never admit. There is no "unknown" verdict on this
//! lane, because the output of this lane is a binary.

use clean_kernel::{
    ConstantKind, DeclarationVerification, Environment, Expr, Name, TypeChecker,
};
use trust_clean_carrier::Carrier;
use trust_types::Ty;

/// Evidence that a lowered Clean-origin body agrees with its Clean `def`,
/// **at the carrier type**.
///
/// **Constructible only by [`check_faithful`].** This is the token a
/// `clean_origin_mir` implementation must hold before it may return a `Body`.
/// Sealing it is the mechanism behind "sole constructor": a caller that cannot
/// build the token cannot route around the gate by constructing the permission
/// directly.
#[derive(Debug, Clone)]
pub struct Faithful {
    name: String,
    admitted_at: Ty,
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
}

/// Why a lowered body was refused.
#[derive(Debug, Clone)]
pub enum GateRefusal {
    /// The kernel did not identify `R(lowered)` with the Clean `def` body.
    ///
    /// This is the mistranslation verdict. It is also what a budget-exhausted
    /// decision collapses to, by design: undecided must refuse.
    Disagreement {
        /// The declaration name.
        name: String,
        /// The Clean `def` body — side A.
        clean: String,
        /// `R(lowered)` — side B.
        lowered: String,
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
}

impl GateRefusal {
    /// The declaration this refusal is about.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::Disagreement { name, .. }
            | Self::NoCleanBody { name }
            | Self::SideANotKernelChecked { name, .. } => name,
        }
    }

    /// The operator-facing explanation.
    ///
    /// A gate refusal is **not** a proof failure and must not be phrased as one.
    /// It means the compiler was about to emit code that disagrees with the
    /// declaration it came from — a compiler defect or a frozen-R violation,
    /// not a user error. The note says so, because telling a user to "add an
    /// invariant" here would send them to fix something they did not break.
    #[must_use]
    pub fn note(&self) -> String {
        match self {
            Self::Disagreement { name, clean, lowered } => format!(
                "INTERNAL: the lowered body for Clean-origin `{name}` does not agree \
                 with its Clean definition, so no code was emitted.\n\
                 clean definition : {clean}\n\
                 lowered (via R)  : {lowered}\n\
                 This is a compiler-correctness refusal, not a proof obligation: it \
                 means the Clean->Rust lowering mistranslated `{name}`, or the R \
                 functor was modified against this lane. Nothing you can write at the \
                 call site changes it. Please report it — the two terms above are the \
                 whole reproduction."
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
        }
    }
}

/// The faithfulness gate.
///
/// Decides, by kernel definitional equality **at the carrier type**, whether a
/// lowered Clean-origin body may be emitted for `name`.
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
    let kernel_name = Name::from_string(name);

    // Side A's PROVENANCE, before its content. A declaration that entered the
    // environment structurally or unchecked is not a kernel verdict, and
    // agreement with it is not faithfulness.
    match env.declaration_verification(&kernel_name) {
        Some(DeclarationVerification::FullKernelCheck) => {}
        verification => {
            return Err(GateRefusal::SideANotKernelChecked {
                name: name.to_owned(),
                verification,
            });
        }
    }

    // Side A: the Clean `def`'s own body. Read from the environment, never from
    // the lowering — this is what makes the comparison non-circular.
    let Some(clean_body) = clean_definition_body(env, &kernel_name) else {
        return Err(GateRefusal::NoCleanBody { name: name.to_owned() });
    };

    let type_checker = TypeChecker::new(env);

    // `is_def_eq` is two-valued; an exhausted decision reports `false` and thus
    // refuses. Undecided must never admit on the one lane that emits a value.
    if !type_checker.is_def_eq(&clean_body, reflected_lowering) {
        return Err(GateRefusal::Disagreement {
            name: name.to_owned(),
            clean: format!("{clean_body:?}"),
            lowered: format!("{reflected_lowering:?}"),
        });
    }

    Ok(Faithful { name: name.to_owned(), admitted_at: carrier.rust().clone() })
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
