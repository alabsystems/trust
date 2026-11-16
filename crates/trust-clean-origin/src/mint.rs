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
    /// The certified re-admission of this declaration was ATTEMPTED and
    /// refused, for a reason the admitter stated.
    ///
    /// Distinct from [`Self::NotKernelChecked`] on purpose. That variant is
    /// what a status that never reached the audit produces, and its note says
    /// so ("a `parsed` symbol … remove any `sorry`"). The mint site used to
    /// map EVERY admission error onto it by fabricating a `Parsed` status
    /// (`Err(_) => KernelStatus::Parsed`), so a declaration the batch had
    /// accepted — measured 2026-09-16: `def sfst (a : Int64) (b : Int64) :
    /// Int64 := a`, registered and reported "kernel-checked" by the very same
    /// build — was described as merely parsed and the user was told to remove
    /// a `sorry` that was not there. None of the options offered could fix the
    /// situation, which ruling v7/D3 calls a defect outright. The admitter's
    /// own reason is carried verbatim instead.
    ///
    /// Exactly as fail-closed as the variant it replaces: a refusal mints
    /// nothing, whatever it is called.
    CertifiedAdmissionRefused {
        /// The declaration name.
        name: String,
        /// `trust_certify::clean_island::admit_certified_island_definition`'s
        /// `Err`, verbatim.
        reason: String,
        /// The carrier refusal for the declaration's signature, rendered, when
        /// its type ALSO has no total Rust carrier. The admitter's reasons are
        /// stated in kernel terms ("is universe-polymorphic"), and the usual
        /// cause is a signature type — so when the carrier lane has something
        /// to say about that signature, the user is shown both rather than
        /// fixing one refusal to meet the next. `None` when the signature
        /// carries, or when the mint site had no constant to read it from.
        carrier: Option<String>,
        /// [`leading_type_variable_binders`] of the declaration's kernel type.
        ///
        /// Measured 2026-09-16 on the repro this variant exists for: the type
        /// the kernel holds for `def sfst (a : Int64) (b : Int64) : Int64 := a`
        /// is `Sort -> #0 -> #1 -> #2`. The Clean prelude declares no `Int64`,
        /// so Lean's auto-bound-implicit rule made the NAME a type VARIABLE —
        /// `sfst` is a projection polymorphic over an arbitrary type that
        /// happens to be called `Int64`, which is why it is universe-polymorphic
        /// and why its signature is dependent. Neither refusal says that, and
        /// kernel binders carry no names, so the note says the one thing that
        /// can be said truthfully from a count: check the type names.
        type_variable_binders: usize,
    },
    /// The declaration is a `def`, but it is not a TOP-LEVEL declaration of
    /// its island, so it is given no Rust path at all.
    ///
    /// The island's Rust-side payload is the island's top-level declarations;
    /// a `def` inside `namespace N … end N` (registered as `N.f`), inside a
    /// `section`, or inside a `mutual` block is kernel-checked with the rest of
    /// the batch and is visible to every Clean declaration in the crate, but
    /// nothing mints a `DefId` for it. Until this variant existed the call
    /// site got a bare `E0425`/`E0433` (measured 2026-09-16, probe 24:
    /// `m::Geo::area` and `m::area` over `namespace Geo def area … end Geo`).
    /// Existing Lean libraries are namespaced throughout, so this is the first
    /// refusal a converted crate meets.
    NotTopLevel {
        /// The bare final component — the name a Rust call site spells.
        name: String,
        /// The name the Clean environment holds it under (`Geo.area`).
        clean_name: String,
        /// The enclosing Clean namespace (`Geo`), or `None` when the
        /// declaration is nested in a block that does not qualify its name
        /// (`section`, `mutual`).
        namespace: Option<String>,
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
            | Self::CertifiedAdmissionRefused { name, .. }
            | Self::NotTopLevel { name, .. }
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
            // The admitter's reason, VERBATIM — never a paraphrase, and never
            // the `parsed`/`sorry` story a fabricated status used to produce.
            // The options are the ones that hold for EVERY reason the admitter
            // can state (trust provenance, a failed audit, a non-Definition, a
            // universe-polymorphic or partial/unsafe declaration, a facet-key
            // collision): none of them tells the user to remove something the
            // reason does not name.
            Self::CertifiedAdmissionRefused { name, reason, carrier, type_variable_binders } => {
                format!(
                    "`{name}` is declared in this island and the crate's Clean batch accepted \
                 it, but it is not callable from Rust: the certified re-admission of THIS \
                 declaration — the audit of its own type, body and complete dependency \
                 closure that a callable declaration must pass — refused it: {reason}.\n\
                 {carrier}\
                 {type_variables}\
                 This is not a parse or elaboration failure, and nothing here says `{name}` \
                 contains a `sorry`: what is stated above is the whole reason. A refused \
                 admission mints no Rust function, fail-closed, so the call site cannot \
                 resolve.\n\
                 options:\n\
                 - restate `{name}` so that the refusal above no longer applies — a \
                   monomorphic, total `def` over `Bool`/`UInt8`/`UInt16`/`UInt32`/`UInt64`/\
                   `Nat` whose dependencies are all kernel-checked definitions passes this \
                   audit and is callable from Rust today;\n\
                 - keep `{name}` as it is and use it from CLEAN only — other island \
                   declarations and theorems can name it, because the batch accepted it; \
                   only the Rust call is refused;\n\
                 - write the function in Rust instead, and state the correspondence you \
                   need as a Clean `theorem`.",
                    carrier = carrier.as_deref().map_or_else(String::new, |refusal| format!(
                        "Its signature ALSO has no total Rust carrier, which would refuse the \
                     call on its own:\n{refusal}\n"
                    )),
                    // Conditional on purpose: a binder the author wrote (`{{α : Type}}`)
                    // and one the elaborator auto-bound look the same to the kernel.
                    type_variables = if *type_variable_binders == 0 {
                        String::new()
                    } else {
                        format!(
                            "LIKELY CAUSE: the type the kernel holds for `{name}` begins with \
                         {type_variable_binders} type-VARIABLE binder(s) (`{{_ : Sort _}}`). If \
                         you did not write them, a type NAME in `{name}`'s signature is not \
                         declared by the Clean prelude this island is checked against, and \
                         Lean's auto-bound-implicit rule silently made that name a type \
                         variable — so `{name}` was kernel-checked as a function polymorphic \
                         over an ARBITRARY type, not over the type you meant. Check every type \
                         name in the signature against the fixed-width types listed below.\n"
                        )
                    },
                )
            }
            // A Clean namespace is not a Rust module. Say which of the two the
            // declaration is in, and give the wrapper that works today
            // (measured 2026-09-16, probe 24c: a root-level
            // `def area_w … := Geo.area w h` mints and runs).
            Self::NotTopLevel { name, clean_name, namespace } => {
                let placement = match namespace {
                    Some(namespace) => format!(
                        "`{clean_name}` is declared inside the Clean `namespace {namespace}` \
                         of this island. A Clean namespace is not a Rust module: no Rust path \
                         — not `{name}`, and not `{rust_path}` — names it",
                        rust_path = format!("{namespace}.{name}").replace('.', "::"),
                    ),
                    None => format!(
                        "`{clean_name}` is declared inside a `section`/`mutual` block of this \
                         island, not at the island's top level"
                    ),
                };
                format!(
                    "{placement}.\n\
                     Only a TOP-LEVEL island `def` is given a Rust function: the island's \
                     Rust-side payload is its top-level declarations, and a declaration \
                     nested in a block is kernel-checked with the rest of the crate's Clean \
                     but mints nothing. `{clean_name}` is still visible to every Clean \
                     declaration in the crate.\n\
                     options:\n\
                     - add a top-level wrapper to the island and call that from Rust — \
                       `def {wrapper} <the same binders> : <the same type> := {clean_name} \
                       <the same arguments>` mints `{wrapper}` in the island's Rust module;\n\
                     - move `def {name}` out of the block to the island's top level, if it \
                       is meant to be called from Rust;\n\
                     - keep `{clean_name}` specification-only and name it from other Clean \
                       declarations and theorems, which resolve it directly.",
                    wrapper = format!("{}_w", name),
                )
            }
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
                   `UInt32`/`UInt64`), which carries exactly AND is callable from Rust \
                   today. A LITERAL-width `BitVec 8/16/32/64` also carries exactly, but it \
                   is refused one step later at the reflection, so it is a fix for a \
                   proof-position use and not for a call \
                   (`docs/design/2026-09-14-bitvec-return-direction.md`);\n\
                 - keep the unbounded type and cite `{name}` from proof position, where \
                   no carrier is needed;\n\
                 - introduce a bounded wrapper in Clean with the bound as part of its \
                   type, and call that."
            ),
        }
    }
}

/// How many leading binders of a declaration's kernel type range over a
/// `Sort` — i.e. bind a TYPE variable.
///
/// Diagnostics only ([`MintRefusal::CertifiedAdmissionRefused`]). Zero for
/// every declaration this lane can call: a callable signature is monomorphic.
/// Non-zero means the declaration is polymorphic over a type, whether the
/// author wrote the binder or the elaborator auto-bound an undeclared type
/// name; the kernel term cannot tell the two apart and neither does this.
#[must_use]
pub fn leading_type_variable_binders(ty: &clean_kernel::Expr) -> usize {
    use clean_kernel::ExprKind;

    let mut count = 0;
    let mut cursor = ty;
    while let ExprKind::Pi(_, domain, body) = cursor.kind() {
        if !matches!(domain.kind(), ExprKind::Sort(_)) {
            break;
        }
        count += 1;
        cursor = body;
    }
    count
}

/// The `def`s an island REGISTERED that are not among its top-level
/// declarations — each as the [`MintRefusal::NotTopLevel`] its call site must
/// be told about.
///
/// `registered` is the island's `CleanIslandOutcome::registered` list (kernel
/// names as the batch reports them, `Geo.area`), and `top_level_defs` the
/// source spellings of the island's top-level `def`s — the only declarations
/// the mint decision ever considers. Whatever is registered, IS a kernel
/// `Definition`, and is not top-level was declared inside a `namespace`,
/// `section` or `mutual` block.
///
/// Diagnostics only, and deliberately so: nothing here mints, and nothing here
/// un-mints. A registered name the environment does not hold as a
/// `Definition` (a theorem, a structure, an inductive) is skipped — those are
/// not callable from any position, so a note promising a wrapper would be
/// false. Order follows `registered`, which is authored order.
#[must_use]
pub fn nested_island_definitions(
    env: &clean_kernel::Environment,
    registered: &[String],
    top_level_defs: &[&str],
) -> Vec<MintRefusal> {
    use clean_kernel::name::NameInner;

    let mut nested = Vec::new();
    for clean_name in registered {
        if top_level_defs.contains(&clean_name.as_str()) {
            continue;
        }
        let kernel_name = clean_kernel::Name::from_string(clean_name);
        let Some(info) = env.get_const(&kernel_name) else { continue };
        if info.kind != clean_kernel::ConstantKind::Definition {
            continue;
        }
        // Only a final STRING component is a name a Rust call site could have
        // spelled; a generated numeric component never is.
        let NameInner::Str(parent, bare) = kernel_name.inner() else { continue };
        // A name qualified by a DEFINITION is not a `def` the author nested in
        // a namespace: it is that definition's `where` helper or an auxiliary
        // the elaborator generated for it (`f.go`, `f.match_1`). Promising a
        // wrapper for one of those would be a guess about source the user did
        // not write that way. (A namespace that is also a TYPE — `structure
        // Point` beside `namespace Point` — is the ordinary Lean idiom and is
        // kept: `Point` is not a `Definition`.)
        if env
            .get_const(parent)
            .is_some_and(|owner| owner.kind == clean_kernel::ConstantKind::Definition)
        {
            continue;
        }
        let namespace = (!parent.is_anon()).then(|| parent.to_string());
        nested.push(MintRefusal::NotTopLevel {
            name: bare.to_string(),
            clean_name: clean_name.clone(),
            namespace,
        });
    }
    nested
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
