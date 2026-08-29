// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! I5 decision 1 — **may a `DefId` be minted for this Clean declaration?**
//!
//! The decision doc's invariant, verbatim:
//!
//! > `def_collector`, on `ItemKind::CleanIsland`, additionally mints
//! > `DefPathData::ValueNs(name)` siblings under the current parent — but *only*
//! > for decls the graph reports as `KernelChecked` with an empty axiom closure
//! > [and a total carrier].
//!
//! This module is that "only" as a total function. It is deliberately pure: it
//! takes the three preconditions as values and returns a grant or a refusal. It
//! does not go looking for them, because *where they can be evaluated* is the
//! open sequencing question recorded in the crate docs — and a decision
//! procedure that silently sourced its own inputs would hide that.
//!
//! # Fail-closed, three ways
//!
//! * **`KernelChecked` is required.** `Parsed` buys a name and a sort;
//!   `Elaborated` buys a core term the kernel never re-checked; `Reflected` is a
//!   Rust item projected INTO Clean by the R functor, which is the opposite
//!   direction and carries no claim that the constant denotes the `fn`. Only
//!   `KernelChecked` is a kernel verdict about this declaration.
//! * **The axiom closure must be AUDITED EMPTY, not merely empty-looking.**
//!   [`AxiomClosure::is_audited_empty`] is a conjunction: recorded AND empty. A
//!   producer holding only `axiom_deps(&Name)` has *unrecorded* closure
//!   information, and `trust-symbols` documents that this must never soften into
//!   "empty". A declaration resting on `sorry` is kernel-checked and worthless.
//! * **A total carrier is required.** Carried as a [`Carrier`], which I4 seals so
//!   it cannot be constructed without `CarrierEvidence::Total`. Passing the type
//!   rather than a boolean is the point: there is no way to spell "I checked the
//!   carrier" without having checked it.
//!
//! # Why the refusal shape matters (ruling v7/D3)
//!
//! A refused mint means the name is never entered in the value namespace, so the
//! call site gets `E0425`. Bare, that is a *lie by omission*: the declaration is
//! right there in the island and the user can see it. Every refusal therefore
//! carries [`MintRefusal::note`] — what was missing, and what to do about it,
//! with options. "Unsupported" with no next step is a defect.

use trust_clean_carrier::{Carrier, CarrierRefused, CarrierSignature, CleanOriginPrecondition};
use trust_symbols::{AxiomClosure, KernelStatus};

/// Permission to mint one `DefId` for a Clean island declaration.
///
/// **Constructible only by [`decide_mint`].** The fields are private and there
/// is no public constructor, so a `MintGrant` in hand is evidence that all three
/// preconditions were checked — the same sealing discipline I4 applies to
/// `CarrierWitness`. A caller cannot fabricate one to get past the mint site.
#[derive(Debug, Clone)]
pub struct MintGrant {
    name: String,
    carrier: Carrier,
    preconditions: Vec<CleanOriginPrecondition>,
}

impl MintGrant {
    /// The declaration name that earned the grant.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The total carrier the `DefId` will be typed at.
    ///
    /// This is the type the eventual faithfulness gate admits at — never the
    /// Clean type. See [`crate::gate`].
    #[must_use]
    pub fn carrier(&self) -> &Carrier {
        &self.carrier
    }

    /// The **caller obligations** this `DefId` is minted with — one per erased
    /// hypothesis binder of the Clean declaration.
    ///
    /// A mint site must forward these alongside the `fn_sig`. They are what
    /// makes the erasure of a proof argument sound: the requirement the proof
    /// stood for becomes an ordinary Rust obligation discharged at every call
    /// site, never a `Faithful` token and never a kernel claim.
    ///
    /// Empty for every grant from [`decide_mint`], which cannot see a
    /// hypothesis — see that function's doc.
    #[must_use]
    pub fn preconditions(&self) -> &[CleanOriginPrecondition] {
        &self.preconditions
    }
}

/// Why no `DefId` was minted.
///
/// Each variant names the missing precondition. [`MintRefusal::note`] turns it
/// into the v7/D3 diagnostic that must accompany the resulting `E0425`.
#[derive(Debug, Clone)]
pub enum MintRefusal {
    /// The kernel has not re-checked this declaration.
    NotKernelChecked {
        /// The declaration name.
        name: String,
        /// I2's own explanation, carried verbatim. `KernelCheckRequired`
        /// distinguishes a `Reflected` carrier from a merely-unchecked one, and
        /// that distinction is the whole point of the seam — paraphrasing it
        /// here would lose it.
        explanation: String,
    },
    /// The producing pipeline did not record axiom-closure information at all.
    ///
    /// Distinct from [`Self::AxiomClosureNonEmpty`] on purpose: "we did not
    /// look" and "we looked and found nothing" are different facts, and
    /// collapsing them is exactly the softening `trust-symbols` forbids.
    AxiomClosureUnrecorded {
        /// The declaration name.
        name: String,
    },
    /// The declaration rests on assumptions the kernel did not discharge.
    AxiomClosureNonEmpty {
        /// The declaration name.
        name: String,
        /// The assumption names, disclosed individually.
        assumptions: Vec<String>,
    },
    /// No total Rust carrier exists for the declaration's type.
    NoTotalCarrier {
        /// The declaration name.
        name: String,
        /// I4's refusal, carried verbatim so the diagnostic can state the true
        /// bound rather than a paraphrase.
        refusal: CarrierRefused,
    },
}

impl MintRefusal {
    /// The declaration this refusal is about.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::NotKernelChecked { name, .. }
            | Self::AxiomClosureUnrecorded { name }
            | Self::AxiomClosureNonEmpty { name, .. }
            | Self::NoTotalCarrier { name, .. } => name,
        }
    }

    /// The v7/D3 note: **why** the name is not callable, and **what to do**.
    ///
    /// Ruling v7/D3: *"we state the rules but if somebody doesn't follow the
    /// rules, then provide feedback via the compiler on how to fix the situation
    /// (provide options)."* Every arm below names at least two courses of
    /// action, because a refusal with exactly one escape is an ultimatum.
    #[must_use]
    pub fn note(&self) -> String {
        match self {
            Self::NotKernelChecked { name, explanation } => format!(
                "`{name}` is declared in this island and is visible, but it is not \
                 callable from Rust: {explanation}\n\
                 A Clean declaration becomes callable only when the CIC kernel has \
                 re-checked THIS declaration — parsing and elaboration are not kernel \
                 verdicts, and a reflected Rust carrier is the opposite direction.\n\
                 options:\n\
                 - remove any `sorry`/`trusted` from `{name}` and its dependencies so \
                   the kernel can discharge it;\n\
                 - if `{name}` is meant to be specification-only, cite it from a \
                   contract instead of calling it — proof position needs no carrier;\n\
                 - if you meant to call a Rust function, define it as a Rust `fn`; a \
                   `clean {{ … }}` island declares Clean, not Rust."
            ),
            Self::AxiomClosureUnrecorded { name } => format!(
                "`{name}` is kernel-checked, but its axiom closure was never RECORDED, \
                 so the compiler cannot show it rests on nothing.\n\
                 An unrecorded closure is not an empty one. Minting a callable \
                 `{name}` here would emit code justified by assumptions nobody \
                 enumerated.\n\
                 options:\n\
                 - route the declaration through the auditing path so the closure is \
                   recorded (an audited-empty closure is what unlocks the call);\n\
                 - cite `{name}` from proof position, which does not require a carrier \
                   and discloses assumptions rather than depending on their absence."
            ),
            Self::AxiomClosureNonEmpty { name, assumptions } => {
                let listed = assumptions.join(", ");
                format!(
                    "`{name}` is kernel-checked but rests on assumptions the kernel did \
                     not discharge: {listed}.\n\
                     Calling `{name}` from Rust would put those assumptions behind an \
                     emitted value, where nothing discloses them at the call site.\n\
                     options:\n\
                     - discharge the listed assumptions and the call becomes available \
                       with no other change;\n\
                     - keep them and cite `{name}` from proof position instead, where \
                       the axiom closure is disclosed BY NAME;\n\
                     - if an assumption is a deliberate domain axiom, state it on the \
                       Rust side as a contract so the obligation is visible to callers."
                )
            }
            // `{refusal}` — DISPLAY, not `{refusal:?}`. This was a Debug dump
            // until 2026-08-27, which silently defeated the whole point of the
            // field: `CarrierRefused`'s doc says it is "carried verbatim so the
            // diagnostic can state the true bound rather than a paraphrase",
            // and every `CarrierRefused` variant's Display carries a v7/D3
            // `options:` list that Debug throws away. What the user actually
            // saw was `UnrecognisedHypothesis { binder_index: 2, rendered:
            // "LT.lt .. .. .. ..", signature: … }` — a struct dump with no next
            // step, which ruling v7/D3 calls a defect outright. Found by
            // `control_20`'s note assertion, which is why that assertion greps
            // for the FORM THAT WORKS rather than for the word "options".
            Self::NoTotalCarrier { name, refusal } => format!(
                "`{name}` is kernel-checked, but its type has no TOTAL Rust carrier, so \
                 there is no Rust type that can hold its values without loss:\n\
                 {refusal}\n\
                 This is not a limitation of the call syntax. A partial carrier would \
                 make the emitted binary disagree with the declaration on some inputs \
                 — kernel definitional equality does not catch that, which is why the \
                 carrier is a separate obligation.\n\
                 options:\n\
                 - restate `{name}` at a fixed-width Clean type (`UInt8`/`UInt16`/\
                   `UInt32`/`UInt64`/`BitVec w`), which carries exactly;\n\
                 - keep the unbounded type and cite `{name}` from proof position, where \
                   no carrier is needed;\n\
                 - introduce a bounded wrapper in Clean with the bound as part of its \
                   type, and call that."
            ),
        }
    }
}

/// Decide whether a Clean island declaration may acquire a `DefId`.
///
/// The three preconditions are checked in the order a reader would want them
/// reported: kernel status first (the coarsest), then the axiom closure, then
/// the carrier. Order is not load-bearing for soundness — any failure refuses —
/// but reporting "not kernel-checked" is more useful than reporting a carrier
/// problem on a declaration that was never checked at all.
///
/// `carrier` is the *result* of I4's carrier decision, so a caller cannot reach
/// this function having skipped it.
///
/// # The axiom closure is NOT a separate parameter, on purpose
///
/// It is read from `status` via [`KernelStatus::closure`]. An earlier shape took
/// the closure alongside the status, which let a caller supply a closure that
/// disagreed with the verdict the kernel actually produced — the exact
/// substitution this lane cannot survive. Taking only the status makes the two
/// impossible to desynchronise: a non-`KernelChecked` status reports
/// `AxiomClosure::unrecorded()`, which fails closed on its own.
///
/// The conjunction checked here is the same one [`KernelStatus::certification`]
/// computes for `Certified`. It is spelled out rather than delegated so each
/// failure can be reported separately — v7/D3 needs to tell the user *which*
/// precondition is missing, and a single `is_certified()` boolean cannot.
///
/// # Errors
///
/// Returns [`MintRefusal`] when any precondition is missing. There is no
/// partial success and no warning path: a refusal means no `DefId`, which means
/// `E0425` at the call site, carrying [`MintRefusal::note`].
pub fn decide_mint(
    name: &str,
    status: &KernelStatus,
    carrier: Result<Carrier, CarrierRefused>,
) -> Result<MintGrant, MintRefusal> {
    require_kernel_and_closure(name, status)?;

    let carrier = match carrier {
        Ok(carrier) => carrier,
        Err(refusal) => {
            return Err(MintRefusal::NoTotalCarrier { name: name.to_owned(), refusal });
        }
    };

    // No preconditions, and this door cannot ever drop one: a bare `Carrier` is
    // a single position's evidence and has no hypothesis binders to lose. A
    // declaration that DOES carry hypotheses can only be witnessed by a
    // `CarrierSignature`, and the only producer of a hypothesis-bearing one is
    // `carrier_signature_with_hypotheses_for`, whose grants come through
    // [`decide_mint_from_signature`]. So "the caller forgot to forward the
    // obligations" is not a reachable state — it is a type that does not exist.
    Ok(MintGrant { name: name.to_owned(), carrier, preconditions: Vec::new() })
}

/// Decide whether a Clean island declaration may acquire a `DefId`, **and with
/// what caller obligations**.
///
/// The same three preconditions as [`decide_mint`], taken over the WHOLE
/// signature rather than one carrier — which is what the mint site already
/// demanded in practice (a declaration whose result carries but whose second
/// argument does not is not callable). The difference that matters is the
/// fourth thing it returns: [`MintGrant::preconditions`], the requirements the
/// declaration's erased hypothesis binders impose on every call site.
///
/// # Why this is the door for a hypothesis-carrying declaration
///
/// `def safe_rem (a b : UInt64) (h : b ≠ 0) : UInt64` mints a Rust `fn` of
/// arity 2 — the proof is erased. That erasure is sound only if `b != 0`
/// travels to the callers, so the grant carries it and the mint site forwards
/// it alongside the `fn_sig`. `trust-clean-carrier`'s hypothesis lift refuses
/// any hypothesis it cannot restate, so a grant from here can never describe a
/// weaker contract than the declaration the kernel checked.
///
/// # Errors
///
/// Exactly [`decide_mint`]'s refusals. A signature-level carrier refusal —
/// including [`CarrierRefused::UnrecognisedHypothesis`] — arrives as
/// [`MintRefusal::NoTotalCarrier`] carrying the inner refusal verbatim, so the
/// v7/D3 note states the true bound rather than a paraphrase.
pub fn decide_mint_from_signature(
    name: &str,
    status: &KernelStatus,
    signature: Result<CarrierSignature, CarrierRefused>,
) -> Result<MintGrant, MintRefusal> {
    require_kernel_and_closure(name, status)?;

    let signature = match signature {
        Ok(signature) => signature,
        Err(refusal) => {
            return Err(MintRefusal::NoTotalCarrier { name: name.to_owned(), refusal });
        }
    };

    Ok(MintGrant {
        name: name.to_owned(),
        carrier: signature.result().clone(),
        preconditions: signature.preconditions(),
    })
}

/// Preconditions 1 and 2, shared by both doors so they cannot drift apart.
fn require_kernel_and_closure(name: &str, status: &KernelStatus) -> Result<(), MintRefusal> {
    // I2's sealed enforcement seam. Fail-closed by construction: every
    // non-`KernelChecked` status refuses, including variants added later, since
    // `KernelStatus` is `#[non_exhaustive]`.
    if let Err(refusal) = status.require_kernel_check(name) {
        return Err(MintRefusal::NotKernelChecked {
            name: name.to_owned(),
            explanation: refusal.to_string(),
        });
    }

    // The closure the kernel recorded for THIS verdict — not one supplied
    // alongside it.
    let axioms: AxiomClosure = status.closure();

    // `is_audited_empty` is the conjunction (recorded AND empty). Split the two
    // failures apart so the diagnostic can tell the user which one happened.
    if !axioms.is_recorded() {
        return Err(MintRefusal::AxiomClosureUnrecorded { name: name.to_owned() });
    }
    if !axioms.is_audited_empty() {
        return Err(MintRefusal::AxiomClosureNonEmpty {
            name: name.to_owned(),
            assumptions: axioms.names().into_iter().map(str::to_owned).collect(),
        });
    }

    Ok(())
}
