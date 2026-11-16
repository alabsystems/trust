// trust-clean/kernel_check.rs: Clean kernel proof checking interface
//
// Provides a typed interface to the Clean kernel for proof term validation,
// type inference, and definitional equality checking. This module bridges
// the gap between reconstructed proof terms and the kernel's type-checking
// judgement.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::fx::FxHashMap;

use crate::error::CertificateError;

// ---------------------------------------------------------------------------
// Proof term representation (kernel-level)
// ---------------------------------------------------------------------------

/// A proof term in the Clean kernel's expression language.
///
/// This is the kernel-level representation used for type checking. It mirrors
/// the Calculus of Inductive Constructions (CIC) core: variables, applications,
/// lambda abstractions, dependent products (Pi types), constants, and sorts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofTerm {
    /// A bound variable (de Bruijn index).
    Var(usize),
    /// Function application: `f a`.
    App(Box<ProofTerm>, Box<ProofTerm>),
    /// Lambda abstraction: `fun (x : A) => body`.
    Lambda {
        /// Binder name (for display only; de Bruijn indices are canonical).
        binder_name: String,
        /// Type of the bound variable.
        binder_type: Box<ProofTerm>,
        /// Body of the lambda (variable 0 refers to this binder).
        body: Box<ProofTerm>,
    },
    /// Dependent product (Pi type): `(x : A) -> B`.
    ///
    /// When the body does not depend on the variable, this is a simple
    /// function type `A -> B`.
    Pi {
        /// Binder name (for display only).
        binder_name: String,
        /// Domain type.
        domain: Box<ProofTerm>,
        /// Codomain (may reference variable 0 for dependent types).
        codomain: Box<ProofTerm>,
    },
    /// A named constant (definition or axiom from the environment).
    Const(String),
    /// A universe sort: `Sort u`. `Sort 0` = `Prop`, `Sort 1` = `Type`.
    Sort(u32),
}

// ---------------------------------------------------------------------------
// Kernel query and result types
// ---------------------------------------------------------------------------

/// A query to the Clean kernel for proof checking.
#[derive(Debug, Clone)]
pub struct KernelQuery {
    /// The proof term to check.
    pub term: ProofTerm,
    /// The expected type (proposition) this term should inhabit.
    pub expected_type: ProofTerm,
}

/// Result of a kernel proof check.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum KernelResult {
    /// The proof term is valid and inhabits the expected type.
    Valid,
    /// The proof term is structurally valid but does not inhabit the expected type.
    Invalid(String),
    /// The proof term has a type error (ill-formed).
    TypeError(String),
}

impl KernelResult {
    /// Returns `true` if the result is `Valid`.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        matches!(self, KernelResult::Valid)
    }
}

// ---------------------------------------------------------------------------
// Kernel context (environment of definitions and axioms)
// ---------------------------------------------------------------------------

/// An entry in the kernel context: either a definition or an axiom.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ContextEntry {
    /// A definition: `def name : type := value`.
    Definition {
        /// The type of the definition.
        ty: ProofTerm,
        /// The value (body) of the definition.
        value: ProofTerm,
    },
    /// An axiom: `axiom name : type` (no body, taken on faith).
    Axiom {
        /// The type of the axiom.
        ty: ProofTerm,
    },
}

// ---------------------------------------------------------------------------
// Kernel-owned names
// ---------------------------------------------------------------------------

/// A name the Clean kernel itself declares, which a [`KernelContext`] may never
/// (re)declare.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ReservedKernelName {
    /// A logical foundation (`propext`, `Quot.sound`, `Classical.choice`) or a
    /// quotient kernel primitive (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`).
    Foundation,
    /// A trust-envelope marker (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`):
    /// an incomplete proof or an external solver's word.
    TrustMarker,
}

/// Classify `name` as kernel-owned, by the Clean kernel's own list
/// (`clean_kernel::canonical_ambient_axiom_kind`), never a copy of it here.
///
/// A `ProofTerm` names a constant by its exact string, so the string is
/// converted with `Name::from_string` (dots separate components). The pinned
/// kernel (clean `5390f432b`) compares printed forms; from clean `2618b4347`
/// the comparison is structural. Either way every string this crate can
/// spell for a kernel-owned name is classified, and a ProofTerm string that
/// differs from it is simply a different constant in this context's map.
#[must_use]
pub fn reserved_kernel_name(name: &str) -> Option<ReservedKernelName> {
    use clean_kernel::{CanonicalAmbientAxiomKind, Name, canonical_ambient_axiom_kind};
    match canonical_ambient_axiom_kind(&Name::from_string(name))? {
        CanonicalAmbientAxiomKind::CertificationFoundation => Some(ReservedKernelName::Foundation),
        CanonicalAmbientAxiomKind::TrustMarker => Some(ReservedKernelName::TrustMarker),
    }
}

/// Universe arity of each kernel-owned foundation's CANONICAL declaration —
/// the kernel's `level_params.len()`, pinned against
/// `clean_kernel::Environment::with_prelude()` by
/// `canonical_foundation_arities_match_the_kernel_prelude` below, so this copy
/// cannot drift silently.
const CANONICAL_FOUNDATION_UNIVERSE_ARITY: [(&str, usize); 7] = [
    ("propext", 0),
    ("Classical.choice", 1),
    ("Quot.sound", 1),
    ("Quot", 1),
    ("Quot.mk", 1),
    ("Quot.lift", 2),
    ("Quot.ind", 1),
];

/// Appended to every foundation refusal: what to do instead of declaring it.
const UNDECLARED_FOUNDATION_NOTE: &str = "; do not declare it — an undeclared reference to \
     `propext`, `Quot.sound` or `Classical.choice` already denotes the kernel's own axiom";

/// Why declaring `name` (as an axiom when `as_axiom`, else as a definition) in
/// a [`KernelContext`] is refused, or `None` when `name` is not kernel-owned.
///
/// # The canonical-declaration check, in this term language
///
/// The Clean kernel admits a foundation only as its exact canonical
/// declaration: `Axiom` kind, no value, the canonical statement, and the
/// canonical universe arity (`Environment::validate_canonical_ambient_axiom`;
/// from clean `2618b4347` also `Environment::is_canonical_foundational_axiom`).
/// This crate cannot call those on a `KernelContext` — they read a kernel
/// `Environment` — so the same check is made structurally here, and in this
/// term language it never succeeds:
///
/// * a `Definition` is never the canonical declaration (it has a value, and
///   the closure walk would unfold its body in place of the kernel's axiom);
/// * `ProofTerm` has no universe parameters, so every declaration here has
///   universe arity 0, and `Classical.choice`, `Quot.sound` and the quotient
///   primitives are canonically universe-polymorphic (arity 1 or 2);
/// * `propext` has arity 0, but its canonical statement
///   `∀ {a b : Prop}, Iff a b → @Eq.{1} Prop a b` names the kernel inductives
///   `Iff` and `Eq.{1}`. `ProofTerm` has no inductives and its `Const` carries
///   no universe levels, so any `Iff`/`Eq` a context could resolve would be
///   context-supplied — and a canonical-SHAPED `propext` over a context-defined
///   `Eq := fun _ _ _ => ∀ P, P` proves `False`.
///
/// So every declaration of a kernel-owned name is non-canonical by
/// construction and is refused. A term that NAMES a foundation needs no
/// declaration: [`crate::axioms::axiom_closure`] resolves an undeclared
/// `propext` / `Quot.sound` / `Classical.choice` to the kernel's own axiom.
/// Trust markers are refused by name in every declaration kind: as an axiom
/// the context would admit a gap, as a definition it would counterfeit one.
///
/// Future simplification: if `ProofTerm` gains universe parameters and
/// inductives, replace the arity table and this reasoning with a
/// `ProofTerm -> clean_kernel::Expr` translation checked by the kernel's own
/// canonical-declaration predicate.
#[must_use]
pub fn reserved_declaration_refusal(name: &str, as_axiom: bool) -> Option<String> {
    let kind = if as_axiom { "an Axiom" } else { "a Definition" };
    let reason = match reserved_kernel_name(name)? {
        ReservedKernelName::TrustMarker => format!(
            "`{name}` is a Clean trust marker (an incomplete-proof or external-solver \
             envelope); a context may not declare it in any kind, and this is {kind}"
        ),
        ReservedKernelName::Foundation if !as_axiom => format!(
            "`{name}` is a kernel-owned foundation, canonically a value-less Axiom; a \
             Definition under its name is a counterfeit whose body would stand in for the \
             kernel's axiom{UNDECLARED_FOUNDATION_NOTE}"
        ),
        ReservedKernelName::Foundation => {
            match CANONICAL_FOUNDATION_UNIVERSE_ARITY.iter().find(|(n, _)| *n == name) {
                Some((_, arity)) if *arity > 0 => format!(
                    "`{name}` is a kernel-owned foundation whose canonical declaration has \
                     universe arity {arity}; a ProofTerm declaration has universe arity 0 (the \
                     term language has no universe parameters), so it cannot be the canonical \
                     declaration{UNDECLARED_FOUNDATION_NOTE}"
                ),
                Some(_) => format!(
                    "`{name}` is a kernel-owned foundation whose canonical statement names the \
                     kernel inductives `Iff` and `Eq.{{1}}`; a ProofTerm context has no \
                     inductives and no universe-instantiated constants, so any `Iff`/`Eq` it \
                     resolves is context-supplied and the declaration cannot be the canonical \
                     one{UNDECLARED_FOUNDATION_NOTE}"
                ),
                // The kernel classifies a foundation this table does not know:
                // fail closed with the generic reason.
                None => format!(
                    "`{name}` is a kernel-owned foundation with no known canonical ProofTerm form"
                ),
            }
        }
    };
    Some(format!("reserved kernel name: {reason}"))
}

/// Manages the Clean kernel environment of definitions and axioms.
///
/// The context maps constant names to their types (and optionally values).
/// It is used during type inference and proof checking to resolve `Const`
/// references in proof terms.
///
/// It never holds a kernel-owned name ([`reserved_declaration_refusal`]):
/// before 2026-09-28 a context could declare `propext : False` or define
/// `sorryAx`, and both [`crate::axioms::axiom_closure`] (which classified
/// foundations by NAME) and [`check_proof`] (which types a `Const` by its
/// entry) took the counterfeit at its word.
///
/// And it never holds a definition the kernel has not checked
/// ([`definition_refusal`]): before 2026-09-29 `add_definition` stored any
/// `(ty, value)` pair, so `mySorry : False := Sort 0` — an axiom of `False`
/// under a name no reserved list knows — or a definition whose value is its own
/// name read `CLEAN` through [`crate::axioms::axiom_closure`] (which unfolds a
/// definition instead of counting it) and typed as `False` in [`check_proof`]
/// (which types a `Const` by its declared type). Each definition is now checked
/// against the entries added BEFORE it, so the context is built in dependency
/// order and a self-reference or a cycle is unresolvable by construction.
#[derive(Debug, Clone, Default)]
pub struct KernelContext {
    entries: FxHashMap<String, ContextEntry>,
}

impl KernelContext {
    /// Create an empty kernel context.
    #[must_use]
    pub fn new() -> Self {
        Self { entries: FxHashMap::default() }
    }

    /// Add a definition to the context.
    ///
    /// # Errors
    ///
    /// Returns `CertificateError::InvalidProofTerm` if the name is already
    /// defined, is kernel-owned ([`reserved_declaration_refusal`]), or the
    /// definition does not kernel-check against the entries added before it
    /// ([`definition_refusal`]).
    pub fn add_definition(
        &mut self,
        name: &str,
        ty: ProofTerm,
        value: ProofTerm,
    ) -> Result<(), CertificateError> {
        if let Some(reason) = reserved_declaration_refusal(name, false) {
            return Err(CertificateError::InvalidProofTerm { reason });
        }
        if self.entries.contains_key(name) {
            return Err(CertificateError::InvalidProofTerm {
                reason: format!("duplicate definition: {name}"),
            });
        }
        if let Some(reason) = definition_refusal(name, &ty, &value, self) {
            return Err(CertificateError::InvalidProofTerm { reason });
        }
        self.entries.insert(name.to_string(), ContextEntry::Definition { ty, value });
        Ok(())
    }

    /// Add an axiom to the context.
    ///
    /// # Errors
    ///
    /// Returns `CertificateError::InvalidProofTerm` if the name is already
    /// defined, is kernel-owned ([`reserved_declaration_refusal`]), or its
    /// type is not a well-formed CLOSED type over the entries added before it
    /// ([`axiom_refusal`]).
    pub fn add_axiom(&mut self, name: &str, ty: ProofTerm) -> Result<(), CertificateError> {
        if let Some(reason) = reserved_declaration_refusal(name, true) {
            return Err(CertificateError::InvalidProofTerm { reason });
        }
        if self.entries.contains_key(name) {
            return Err(CertificateError::InvalidProofTerm {
                reason: format!("duplicate axiom: {name}"),
            });
        }
        if let Some(reason) = axiom_refusal(name, &ty, self) {
            return Err(CertificateError::InvalidProofTerm { reason });
        }
        self.entries.insert(name.to_string(), ContextEntry::Axiom { ty });
        Ok(())
    }

    /// Look up a constant in the context.
    #[must_use]
    pub fn lookup(&self, name: &str) -> Option<&ContextEntry> {
        self.entries.get(name)
    }

    /// Returns the number of entries in the context.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if the context has no entries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// Why `def name : ty := value` may not enter `ctx`, or `None` when it
/// kernel-checks: `ty` is a well-formed type (its type is a `Sort`) and
/// `value` infers a type definitionally equal to `ty`, both in `ctx` AS IT
/// STANDS — the entries added before this one, never `name` itself.
///
/// Checking against the prefix is what orders a context: a definition may use
/// only what precedes it, so a self-reference (`x := x`) or a cycle (`a := b`,
/// `b := a`) names an unknown constant and is refused. A definition over a
/// kernel foundation (`propext`, …) is refused too: the foundations are never
/// context entries (their canonical statements need kernel inductives this
/// term language lacks), so such a value cannot be typed here.
#[must_use]
pub fn definition_refusal(
    name: &str,
    ty: &ProofTerm,
    value: &ProofTerm,
    ctx: &KernelContext,
) -> Option<String> {
    if mentions_constant(ty, name) || mentions_constant(value, name) {
        return Some(format!(
            "definition `{name}` refers to itself; a context definition may use only the \
             entries declared before it (no self-reference, no cycle)"
        ));
    }
    if let Err(err) = infer_sort_level(ty, ctx, &[]) {
        return Some(format!(
            "the declared type of definition `{name}` is not a well-formed type over the \
             entries declared before it: {err}"
        ));
    }
    let inferred = match infer_type(value, ctx, &[]) {
        Ok(inferred) => inferred,
        Err(err) => {
            return Some(format!(
                "the value of definition `{name}` does not type-check over the entries \
                 declared before it: {err}"
            ));
        }
    };
    if !is_definitionally_equal(&inferred, ty, ctx) {
        return Some(format!(
            "the value of definition `{name}` has type {inferred:?}, not its declared type {ty:?}"
        ));
    }
    None
}

/// Why `axiom name : ty` may not enter `ctx`, or `None` when `ty` is a
/// well-formed type (its type a `Sort`) over the entries added before it.
///
/// Trust (2026-09-29): the `Const` rule of [`infer_type`] returns a context
/// type UNSHIFTED under whatever binders surround the use — correct only
/// because every context type is closed. A definition's type is checked with
/// no locals ([`definition_refusal`]), so it is; an axiom's type was stored
/// unchecked, so `ax : Var 0` was accepted and `λP:Prop. ax` typed as
/// `ΠP:Prop. P` — the free `Var 0` captured by the binder at the use site.
#[must_use]
pub fn axiom_refusal(name: &str, ty: &ProofTerm, ctx: &KernelContext) -> Option<String> {
    infer_sort_level(ty, ctx, &[]).err().map(|err| {
        format!(
            "the declared type of axiom `{name}` is not a well-formed closed type over the \
             entries declared before it: {err}"
        )
    })
}

/// Whether `term` names the constant `name` anywhere.
fn mentions_constant(term: &ProofTerm, name: &str) -> bool {
    match term {
        ProofTerm::Const(constant) => constant == name,
        ProofTerm::Var(_) | ProofTerm::Sort(_) => false,
        ProofTerm::App(f, a) => mentions_constant(f, name) || mentions_constant(a, name),
        ProofTerm::Lambda { binder_type, body, .. } => {
            mentions_constant(binder_type, name) || mentions_constant(body, name)
        }
        ProofTerm::Pi { domain, codomain, .. } => {
            mentions_constant(domain, name) || mentions_constant(codomain, name)
        }
    }
}

// ---------------------------------------------------------------------------
// Type inference
// ---------------------------------------------------------------------------

/// Infer the type of a proof term in the given context.
///
/// Uses a simplified Clean type-checking algorithm:
/// - `Var(i)` is looked up in the local type stack
/// - `Const(name)` is looked up in the kernel context
/// - `Sort(u)` has type `Sort(u+1)` (universe hierarchy)
/// - `Lambda { A, body }` has type `Pi { A, infer(body) }`
/// - `Pi { A, B }` has type `Sort(max(u_A, u_B))`
/// - `App(f, a)` checks `f : Pi(A, B)` and `a : A`, returns `B[0 := a]`
///
/// # Errors
///
/// Returns `CertificateError::KernelRejected` if the term is ill-typed.
pub fn infer_type(
    term: &ProofTerm,
    ctx: &KernelContext,
    locals: &[ProofTerm],
) -> Result<ProofTerm, CertificateError> {
    let mut stack: Vec<&ProofTerm> = if locals.is_empty() {
        Vec::new()
    } else {
        locals.iter().collect()
    };
    infer_type_in(term, ctx, &mut stack)
}

fn infer_type_in<'a>(
    term: &'a ProofTerm,
    ctx: &KernelContext,
    locals: &mut Vec<&'a ProofTerm>,
) -> Result<ProofTerm, CertificateError> {
    match term {
        ProofTerm::Var(idx) => {
            let depth = locals.len();
            if *idx >= depth {
                return Err(CertificateError::KernelRejected {
                    reason: format!("variable index {idx} out of scope (depth {depth})"),
                });
            }
            // de Bruijn: index 0 = most recently bound. Trust (2026-09-29):
            // `locals[k]` was pushed when k binders were in scope, so its free
            // variables count from THAT depth; `Var(idx)` reads entry
            // `depth - 1 - idx` from `idx + 1` binders deeper, and its type
            // must be lifted past them (`shift(_, 0, idx + 1)`). Returned
            // unshifted, `λP:Sort 2. λx:P. λQ:Prop. x` typed as
            // `ΠP. Πx:P. ΠQ:Prop. Q` — the `x : P` read as `x : Q` — which
            // applied to `Type` and `Prop` proves `∀Q:Prop, Q`; and the
            // polymorphic identity `λA:Type. λa:A. a` was refused its true
            // type `ΠA. Πa:A. A`.
            Ok(shift(locals[depth - 1 - idx], 0, idx + 1))
        }
        ProofTerm::Const(name) => match ctx.lookup(name) {
            Some(ContextEntry::Definition { ty, .. }) => Ok(ty.clone()),
            Some(ContextEntry::Axiom { ty }) => Ok(ty.clone()),
            None => Err(CertificateError::KernelRejected {
                reason: format!("unknown constant: {name}"),
            }),
        },
        ProofTerm::Sort(u) => {
            // Sort u : Sort (u+1). Trust (2026-09-29): the top level has no
            // successor. `saturating_add` typed `Sort MAX : Sort MAX` — Type :
            // Type, under which Girard's paradox inhabits every type of that
            // universe — so it is refused, never clamped.
            u.checked_add(1).map(ProofTerm::Sort).ok_or_else(|| CertificateError::KernelRejected {
                reason: format!("universe level overflow: Sort {u} has no successor"),
            })
        }
        ProofTerm::Lambda { binder_name, binder_type, body } => {
            // Trust (2026-09-29): the binder's type must be a TYPE — its own
            // type a `Sort`, exactly as the `Pi` rule below demands of a
            // domain. Before, any well-typed term was accepted here (a proof
            // as a binder "type"), so a lambda could have a type the kernel
            // cannot even form.
            infer_sort_level_in(binder_type, ctx, locals)?;

            // Push borrowed binder type in O(1) instead of cloning the whole local stack.
            locals.push(binder_type);
            let body_res = infer_type_in(body, ctx, locals);
            locals.pop();
            let body_type = body_res?;

            Ok(ProofTerm::Pi {
                binder_name: binder_name.clone(),
                domain: binder_type.clone(),
                codomain: Box::new(body_type),
            })
        }
        ProofTerm::Pi { domain, codomain, .. } => {
            let domain_sort = infer_sort_level_in(domain, ctx, locals)?;
            locals.push(domain);
            let codomain_res = infer_sort_level_in(codomain, ctx, locals);
            locals.pop();
            let codomain_sort = codomain_res?;
            Ok(ProofTerm::Sort(domain_sort.max(codomain_sort)))
        }
        ProofTerm::App(f, a) => {
            let f_type = infer_type_in(f, ctx, locals)?;
            match f_type {
                ProofTerm::Pi { domain, codomain, .. } => {
                    let a_type = infer_type_in(a, ctx, locals)?;
                    if !is_definitionally_equal(&a_type, &domain, ctx) {
                        return Err(CertificateError::KernelRejected {
                            reason: format!(
                                "argument type mismatch: expected {domain:?}, got {a_type:?}"
                            ),
                        });
                    }
                    // Substitute the argument into the codomain
                    Ok(substitute(&codomain, 0, a))
                }
                _ => Err(CertificateError::KernelRejected {
                    reason: format!("application of non-function type: {f_type:?}"),
                }),
            }
        }
    }
}

/// Extract the sort level of a type. Returns the universe level if the
/// term's type is `Sort(u)`, otherwise returns an error.
fn infer_sort_level(
    term: &ProofTerm,
    ctx: &KernelContext,
    locals: &[ProofTerm],
) -> Result<u32, CertificateError> {
    let mut stack: Vec<&ProofTerm> = if locals.is_empty() {
        Vec::new()
    } else {
        locals.iter().collect()
    };
    infer_sort_level_in(term, ctx, &mut stack)
}

fn infer_sort_level_in<'a>(
    term: &'a ProofTerm,
    ctx: &KernelContext,
    locals: &mut Vec<&'a ProofTerm>,
) -> Result<u32, CertificateError> {
    let ty = infer_type_in(term, ctx, locals)?;
    match ty {
        ProofTerm::Sort(u) => Ok(u),
        // Trust: F5 soundness fix — non-Sort types must not silently become Prop
        _ => Err(CertificateError::KernelRejected {
            reason: format!("expected Sort(_) when inferring sort level, got {ty:?}"),
        }),
    }
}

// ---------------------------------------------------------------------------
// Substitution
// ---------------------------------------------------------------------------

/// Single-pass `O(N)` shift returning `None` when `amount == 0` or `term` has
/// no free de Bruijn variable `>= cutoff`.
fn shift_opt(term: &ProofTerm, cutoff: usize, amount: usize) -> Option<ProofTerm> {
    if amount == 0 {
        return None;
    }
    match term {
        ProofTerm::Var(idx) => (*idx >= cutoff).then(|| ProofTerm::Var(idx + amount)),
        ProofTerm::Const(_) | ProofTerm::Sort(_) => None,
        ProofTerm::App(f, a) => match (shift_opt(f, cutoff, amount), shift_opt(a, cutoff, amount)) {
            (None, None) => None,
            (Some(nf), None) => Some(ProofTerm::App(Box::new(nf), a.clone())),
            (None, Some(na)) => Some(ProofTerm::App(f.clone(), Box::new(na))),
            (Some(nf), Some(na)) => Some(ProofTerm::App(Box::new(nf), Box::new(na))),
        },
        ProofTerm::Lambda { binder_name, binder_type, body } => match (
            shift_opt(binder_type, cutoff, amount),
            shift_opt(body, cutoff + 1, amount),
        ) {
            (None, None) => None,
            (nt, nb) => Some(ProofTerm::Lambda {
                binder_name: binder_name.clone(),
                binder_type: nt.map_or_else(|| binder_type.clone(), Box::new),
                body: nb.map_or_else(|| body.clone(), Box::new),
            }),
        },
        ProofTerm::Pi { binder_name, domain, codomain } => match (
            shift_opt(domain, cutoff, amount),
            shift_opt(codomain, cutoff + 1, amount),
        ) {
            (None, None) => None,
            (nd, nc) => Some(ProofTerm::Pi {
                binder_name: binder_name.clone(),
                domain: nd.map_or_else(|| domain.clone(), Box::new),
                codomain: nc.map_or_else(|| codomain.clone(), Box::new),
            }),
        },
    }
}

/// Shift (lift) free variables in `term` by `amount`.
///
/// All variables with de Bruijn index >= `cutoff` are incremented by `amount`.
/// This is needed during substitution: when entering a binder, free variables
/// in the replacement term must be shifted up by 1 so they are not captured
/// by the new binder.
///
/// Reference: Barendregt, "The Lambda Calculus", Chapter 2 (de Bruijn indices).
#[must_use]
pub fn shift(term: &ProofTerm, cutoff: usize, amount: usize) -> ProofTerm {
    shift_opt(term, cutoff, amount).unwrap_or_else(|| term.clone())
}

/// Single-pass `O(N)` capture-avoiding de Bruijn substitution accumulating
/// `binder_depth` in `O(1)` across binders and computing `shift(replacement, 0, binder_depth)`
/// only at matching `Var(target_idx)` leaves (returning `None` when every `Var` in `term`
/// has `idx < target_idx`).
fn substitute_opt(
    term: &ProofTerm,
    target_idx: usize,
    replacement: &ProofTerm,
    binder_depth: usize,
) -> Option<ProofTerm> {
    match term {
        ProofTerm::Var(idx) => {
            if *idx == target_idx {
                Some(shift(replacement, 0, binder_depth))
            } else if *idx > target_idx {
                // Shift down since the binder is being removed
                Some(ProofTerm::Var(idx - 1))
            } else {
                None
            }
        }
        ProofTerm::Const(_) | ProofTerm::Sort(_) => None,
        ProofTerm::App(f, a) => match (
            substitute_opt(f, target_idx, replacement, binder_depth),
            substitute_opt(a, target_idx, replacement, binder_depth),
        ) {
            (None, None) => None,
            (Some(nf), None) => Some(ProofTerm::App(Box::new(nf), a.clone())),
            (None, Some(na)) => Some(ProofTerm::App(f.clone(), Box::new(na))),
            (Some(nf), Some(na)) => Some(ProofTerm::App(Box::new(nf), Box::new(na))),
        },
        ProofTerm::Lambda { binder_name, binder_type, body } => match (
            substitute_opt(binder_type, target_idx, replacement, binder_depth),
            substitute_opt(body, target_idx + 1, replacement, binder_depth + 1),
        ) {
            (None, None) => None,
            (nt, nb) => Some(ProofTerm::Lambda {
                binder_name: binder_name.clone(),
                binder_type: nt.map_or_else(|| binder_type.clone(), Box::new),
                body: nb.map_or_else(|| body.clone(), Box::new),
            }),
        },
        ProofTerm::Pi { binder_name, domain, codomain } => match (
            substitute_opt(domain, target_idx, replacement, binder_depth),
            substitute_opt(codomain, target_idx + 1, replacement, binder_depth + 1),
        ) {
            (None, None) => None,
            (nd, nc) => Some(ProofTerm::Pi {
                binder_name: binder_name.clone(),
                domain: nd.map_or_else(|| domain.clone(), Box::new),
                codomain: nc.map_or_else(|| codomain.clone(), Box::new),
            }),
        },
    }
}

/// Substitute `replacement` for variable `target_idx` in `term`.
///
/// This is capture-avoiding substitution for de Bruijn indexed terms.
/// When recursing under a binder (Lambda/Pi), the replacement term is shifted
/// up by 1 to prevent free variable capture.
///
/// Reference: Barendregt, "The Lambda Calculus", Chapter 2.
#[must_use]
pub fn substitute(term: &ProofTerm, target_idx: usize, replacement: &ProofTerm) -> ProofTerm {
    substitute_opt(term, target_idx, replacement, 0).unwrap_or_else(|| term.clone())
}

// ---------------------------------------------------------------------------
// Definitional equality
// ---------------------------------------------------------------------------

/// Check whether two proof terms are definitionally equal.
///
/// Two terms are definitionally equal if they reduce to the same normal form.
/// This implementation handles:
/// - Syntactic equality
/// - Delta reduction (unfolding definitions)
/// - Beta reduction (lambda application)
/// - Eta equivalence (structural)
#[must_use]
pub fn is_definitionally_equal(lhs: &ProofTerm, rhs: &ProofTerm, ctx: &KernelContext) -> bool {
    // Fast path: syntactic equality
    if lhs == rhs {
        return true;
    }

    // Try delta/beta reduction without cloning non-reducing subtrees
    match (delta_reduce_opt(lhs, ctx), delta_reduce_opt(rhs, ctx)) {
        (Some(l), Some(r)) if l != *lhs || r != *rhs => {
            return is_definitionally_equal(&l, &r, ctx);
        }
        (Some(l), None) if l != *lhs => {
            return is_definitionally_equal(&l, rhs, ctx);
        }
        (None, Some(r)) if r != *rhs => {
            return is_definitionally_equal(lhs, &r, ctx);
        }
        _ => {}
    }

    // Structural comparison after reduction
    match (lhs, rhs) {
        (ProofTerm::App(f1, a1), ProofTerm::App(f2, a2)) => {
            is_definitionally_equal(f1, f2, ctx) && is_definitionally_equal(a1, a2, ctx)
        }
        (
            ProofTerm::Lambda { binder_type: t1, body: b1, .. },
            ProofTerm::Lambda { binder_type: t2, body: b2, .. },
        ) => is_definitionally_equal(t1, t2, ctx) && is_definitionally_equal(b1, b2, ctx),
        (
            ProofTerm::Pi { domain: d1, codomain: c1, .. },
            ProofTerm::Pi { domain: d2, codomain: c2, .. },
        ) => is_definitionally_equal(d1, d2, ctx) && is_definitionally_equal(c1, c2, ctx),
        _ => false,
    }
}

/// Perform one head delta/beta step, returning `None` when `term` does not reduce
/// (avoiding full-tree `ProofTerm` clones on every non-reducing equality check).
fn delta_reduce_opt(term: &ProofTerm, ctx: &KernelContext) -> Option<ProofTerm> {
    match term {
        ProofTerm::Const(name) => {
            if let Some(ContextEntry::Definition { value, .. }) = ctx.lookup(name) {
                Some(value.clone())
            } else {
                None
            }
        }
        ProofTerm::App(f, a) => {
            // Direct beta reduction without cloning `f` first
            if let ProofTerm::Lambda { body, .. } = f.as_ref() {
                return Some(substitute(body, 0, a));
            }
            let f_reduced = delta_reduce_opt(f, ctx)?;
            if let ProofTerm::Lambda { body, .. } = &f_reduced {
                Some(substitute(body, 0, a))
            } else if f_reduced != **f {
                Some(ProofTerm::App(Box::new(f_reduced), a.clone()))
            } else {
                None
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Proof checking
// ---------------------------------------------------------------------------

/// Check that a proof term inhabits the expected type.
///
/// This is the main entry point for kernel proof checking. It infers the
/// type of the proof term and checks that it is definitionally equal to
/// the expected type.
///
/// # Errors
///
/// Returns `CertificateError` if the term is ill-typed or does not match.
pub fn check_proof(
    query: &KernelQuery,
    ctx: &KernelContext,
) -> Result<KernelResult, CertificateError> {
    let inferred = match infer_type(&query.term, ctx, &[]) {
        Ok(ty) => ty,
        Err(e) => {
            return Ok(KernelResult::TypeError(e.to_string()));
        }
    };

    if is_definitionally_equal(&inferred, &query.expected_type, ctx) {
        Ok(KernelResult::Valid)
    } else {
        Ok(KernelResult::Invalid(format!(
            "inferred type {inferred:?} is not definitionally equal to expected {expected:?}",
            expected = query.expected_type,
        )))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // Helpers
    fn prop() -> ProofTerm {
        ProofTerm::Sort(0)
    }

    fn type_sort() -> ProofTerm {
        ProofTerm::Sort(1)
    }

    fn arrow(domain: ProofTerm, codomain: ProofTerm) -> ProofTerm {
        ProofTerm::Pi {
            binder_name: "_".to_string(),
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    fn lam(name: &str, ty: ProofTerm, body: ProofTerm) -> ProofTerm {
        ProofTerm::Lambda {
            binder_name: name.to_string(),
            binder_type: Box::new(ty),
            body: Box::new(body),
        }
    }

    // -----------------------------------------------------------------------
    // 1. KernelContext: add and lookup
    // -----------------------------------------------------------------------

    #[test]
    fn test_kernel_context_add_axiom_and_lookup() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("True", prop()).expect("should add axiom");
        let entry = ctx.lookup("True");
        assert!(entry.is_some());
        assert!(matches!(entry.unwrap(), ContextEntry::Axiom { .. }));
        assert_eq!(ctx.len(), 1);
    }

    // -----------------------------------------------------------------------
    // 2. KernelContext: duplicate name rejected
    // -----------------------------------------------------------------------

    #[test]
    fn test_kernel_context_duplicate_rejected() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("A", prop()).expect("first add succeeds");
        let err = ctx.add_axiom("A", prop());
        assert!(err.is_err(), "duplicate should be rejected");
    }

    // -----------------------------------------------------------------------
    // 3. KernelContext: definition lookup
    // -----------------------------------------------------------------------

    #[test]
    fn test_kernel_context_definition_lookup() {
        let mut ctx = KernelContext::new();
        let id_ty = arrow(prop(), prop());
        let id_val = lam("x", prop(), ProofTerm::Var(0));
        ctx.add_definition("id", id_ty.clone(), id_val.clone()).expect("should add definition");
        match ctx.lookup("id").unwrap() {
            ContextEntry::Definition { ty, value } => {
                assert_eq!(*ty, id_ty);
                assert_eq!(*value, id_val);
            }
            _ => panic!("expected Definition"),
        }
    }

    // -----------------------------------------------------------------------
    // 4. infer_type: Sort(0) has type Sort(1)
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_type_sort_has_next_sort() {
        let ctx = KernelContext::new();
        let ty = infer_type(&prop(), &ctx, &[]).expect("Sort(0) should type-check");
        assert_eq!(ty, type_sort());
    }

    // -----------------------------------------------------------------------
    // 5. infer_type: constant lookup
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_type_const_lookup() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("P", prop()).expect("add axiom");
        let ty = infer_type(&ProofTerm::Const("P".to_string()), &ctx, &[])
            .expect("should infer axiom type");
        assert_eq!(ty, prop());
    }

    // -----------------------------------------------------------------------
    // 6. infer_type: unknown constant is an error
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_type_unknown_const_error() {
        let ctx = KernelContext::new();
        let result = infer_type(&ProofTerm::Const("missing".to_string()), &ctx, &[]);
        assert!(result.is_err());
    }

    // -----------------------------------------------------------------------
    // 7. infer_type: variable out of scope is an error
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_type_var_out_of_scope_error() {
        let ctx = KernelContext::new();
        let result = infer_type(&ProofTerm::Var(0), &ctx, &[]);
        assert!(result.is_err());
    }

    // -----------------------------------------------------------------------
    // 8. infer_type: identity lambda has Pi type
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_type_identity_lambda() {
        let mut ctx = KernelContext::new();
        // We need Prop in the context so Sort(0) is well-typed
        ctx.add_axiom("A", prop()).expect("add A");
        let a = ProofTerm::Const("A".to_string());
        // fun (x : A) => x  should have type  (x : A) -> A
        let id = lam("x", a.clone(), ProofTerm::Var(0));
        let ty = infer_type(&id, &ctx, &[]).expect("id should type-check");
        assert!(matches!(ty, ProofTerm::Pi { .. }));
        if let ProofTerm::Pi { domain, codomain, .. } = &ty {
            assert_eq!(**domain, a);
            assert_eq!(**codomain, a);
        }
    }

    // -----------------------------------------------------------------------
    // 9. check_proof: valid proof
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_proof_valid() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("A", prop()).expect("add A");
        let a = ProofTerm::Const("A".to_string());
        // Identity: fun (x : A) => x
        let id = lam("x", a.clone(), ProofTerm::Var(0));
        let expected = arrow(a.clone(), a);
        let query = KernelQuery { term: id, expected_type: expected };
        let result = check_proof(&query, &ctx).expect("should not error");
        assert!(result.is_valid(), "identity should be valid, got: {result:?}");
    }

    // -----------------------------------------------------------------------
    // 10. check_proof: type mismatch yields Invalid
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_proof_type_mismatch_invalid() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("A", prop()).expect("add A");
        ctx.add_axiom("B", prop()).expect("add B");
        let a = ProofTerm::Const("A".to_string());
        let b = ProofTerm::Const("B".to_string());
        // fun (x : A) => x  has type  A -> A, not A -> B
        let id = lam("x", a.clone(), ProofTerm::Var(0));
        let wrong_type = arrow(a, b);
        let query = KernelQuery { term: id, expected_type: wrong_type };
        let result = check_proof(&query, &ctx).expect("should not error");
        assert!(
            matches!(result, KernelResult::Invalid(_)),
            "type mismatch should be Invalid, got: {result:?}"
        );
    }

    // -----------------------------------------------------------------------
    // 11. check_proof: ill-typed term yields TypeError
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_proof_ill_typed_yields_type_error() {
        let ctx = KernelContext::new();
        // App(Sort(0), Sort(0)) is ill-typed: Sort is not a function
        let bad = ProofTerm::App(Box::new(prop()), Box::new(prop()));
        let query = KernelQuery { term: bad, expected_type: prop() };
        let result = check_proof(&query, &ctx).expect("should not error");
        assert!(
            matches!(result, KernelResult::TypeError(_)),
            "ill-typed should be TypeError, got: {result:?}"
        );
    }

    // -----------------------------------------------------------------------
    // 12. is_definitionally_equal: syntactic equality
    // -----------------------------------------------------------------------

    #[test]
    fn test_def_equal_syntactic() {
        let ctx = KernelContext::new();
        let t = prop();
        assert!(is_definitionally_equal(&t, &t, &ctx));
    }

    // -----------------------------------------------------------------------
    // 13. is_definitionally_equal: delta reduction
    // -----------------------------------------------------------------------

    #[test]
    fn test_def_equal_delta_reduction() {
        let mut ctx = KernelContext::new();
        // def MyProp : Sort 1 := Sort 0
        ctx.add_definition("MyProp", type_sort(), prop()).expect("add def");
        let const_ref = ProofTerm::Const("MyProp".to_string());
        assert!(is_definitionally_equal(&const_ref, &prop(), &ctx));
    }

    // -----------------------------------------------------------------------
    // 14. is_definitionally_equal: not equal
    // -----------------------------------------------------------------------

    #[test]
    fn test_def_equal_not_equal() {
        let ctx = KernelContext::new();
        assert!(!is_definitionally_equal(&prop(), &type_sort(), &ctx));
    }

    // -----------------------------------------------------------------------
    // 15. substitute: basic variable replacement
    // -----------------------------------------------------------------------

    #[test]
    fn test_substitute_var_replaced() {
        let term = ProofTerm::Var(0);
        let replacement = ProofTerm::Const("x".to_string());
        let result = substitute(&term, 0, &replacement);
        assert_eq!(result, replacement);
    }

    // -----------------------------------------------------------------------
    // 16. substitute: higher variable shifted down
    // -----------------------------------------------------------------------

    #[test]
    fn test_substitute_higher_var_shifted() {
        let term = ProofTerm::Var(1);
        let replacement = ProofTerm::Const("x".to_string());
        let result = substitute(&term, 0, &replacement);
        assert_eq!(result, ProofTerm::Var(0));
    }

    // -----------------------------------------------------------------------
    // 17. KernelResult::is_valid
    // -----------------------------------------------------------------------

    #[test]
    fn test_kernel_result_is_valid() {
        assert!(KernelResult::Valid.is_valid());
        assert!(!KernelResult::Invalid("mismatch".to_string()).is_valid());
        assert!(!KernelResult::TypeError("bad".to_string()).is_valid());
    }

    // -----------------------------------------------------------------------
    // 18. KernelContext::is_empty
    // -----------------------------------------------------------------------

    #[test]
    fn test_kernel_context_is_empty() {
        let ctx = KernelContext::new();
        assert!(ctx.is_empty());
    }

    // -----------------------------------------------------------------------
    // 19. infer_type: application with beta reduction
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_type_application() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("A", prop()).expect("add A");
        ctx.add_axiom("a", ProofTerm::Const("A".to_string())).expect("add a");
        let a = ProofTerm::Const("A".to_string());
        let proof_a = ProofTerm::Const("a".to_string());
        // (fun (x : A) => x) a  should have type A
        let id = lam("x", a.clone(), ProofTerm::Var(0));
        let app = ProofTerm::App(Box::new(id), Box::new(proof_a));
        let ty = infer_type(&app, &ctx, &[]).expect("app should type-check");
        assert_eq!(ty, a);
    }

    // -----------------------------------------------------------------------
    // 20. is_definitionally_equal: structural Pi comparison
    // -----------------------------------------------------------------------

    #[test]
    fn test_def_equal_pi_structural() {
        let ctx = KernelContext::new();
        let pi1 = arrow(prop(), prop());
        let pi2 = ProofTerm::Pi {
            binder_name: "different_name".to_string(),
            domain: Box::new(prop()),
            codomain: Box::new(prop()),
        };
        // Names differ but structure is the same
        assert!(is_definitionally_equal(&pi1, &pi2, &ctx));
    }

    // -----------------------------------------------------------------------
    // 21. shift: free variables shifted, bound variables unchanged
    // -----------------------------------------------------------------------

    #[test]
    fn test_shift_free_var_incremented() {
        // Var(0) with cutoff 0 should become Var(1)
        let term = ProofTerm::Var(0);
        let result = shift(&term, 0, 1);
        assert_eq!(result, ProofTerm::Var(1));
    }

    #[test]
    fn test_shift_bound_var_unchanged() {
        // Inside a lambda, Var(0) is bound. shift with cutoff=1 leaves it alone.
        let term = ProofTerm::Var(0);
        let result = shift(&term, 1, 1);
        assert_eq!(result, ProofTerm::Var(0));
    }

    #[test]
    fn test_shift_under_lambda() {
        // Lambda(Prop, Var(1)) — Var(1) is free (references outside).
        // shift by 1 at cutoff 0 should produce Lambda(Prop, Var(2)).
        let term = lam("x", prop(), ProofTerm::Var(1));
        let result = shift(&term, 0, 1);
        let expected = lam("x", prop(), ProofTerm::Var(2));
        assert_eq!(result, expected);
    }

    // -----------------------------------------------------------------------
    // 22. substitute: no variable capture under lambda
    // -----------------------------------------------------------------------

    #[test]
    fn test_substitute_no_capture_under_lambda() {
        // Substituting Var(0) (a free variable from outer context) for target 0
        // into Lambda(ty, Var(1)):
        //   - Var(1) in the body refers to target 0 (shifted by the binder)
        //   - The replacement Var(0) must be shifted to Var(1) inside the lambda
        //   - Result body should be Var(1), NOT Var(0) (which would be captured)
        let term = lam("x", prop(), ProofTerm::Var(1));
        let replacement = ProofTerm::Var(0);
        let result = substitute(&term, 0, &replacement);

        // After substitution:
        //   binder_type: substitute(Prop, 0, Var(0)) = Prop
        //   body: substitute(Var(1), 1, shift(Var(0),0,1)) = substitute(Var(1), 1, Var(1)) = Var(1)
        // But then Var(1) matches target_idx=1, so it gets replaced with Var(1).
        // Result: Lambda(Prop, Var(1))
        let expected = lam("x", prop(), ProofTerm::Var(1));
        assert_eq!(
            result, expected,
            "free variable in replacement must be shifted to avoid capture by lambda binder"
        );
    }

    #[test]
    fn test_substitute_nested_lambdas_shift_correctly() {
        // Term: Lambda(Prop, Lambda(Prop, Var(2)))
        // This is: fun x : Prop => fun y : Prop => <free_var_at_depth_2>
        // Var(2) refers to target_idx=0 at depth 2.
        //
        // Substituting Var(0) for target 0:
        //   Outer lambda: shifted_repl = Var(1), recurse body with target=1
        //   Inner lambda: shifted_repl = Var(2), recurse body with target=2
        //   Var(2) == target 2 → replaced with Var(2)
        //
        // Result: Lambda(Prop, Lambda(Prop, Var(2)))
        // The replacement Var(0) was shifted to Var(2) at depth 2, preserving
        // its meaning as a reference to the outer context.
        let inner = lam("y", prop(), ProofTerm::Var(2));
        let term = lam("x", prop(), inner);
        let replacement = ProofTerm::Var(0);
        let result = substitute(&term, 0, &replacement);

        let expected_inner = lam("y", prop(), ProofTerm::Var(2));
        let expected = lam("x", prop(), expected_inner);
        assert_eq!(result, expected, "replacement must be shifted by +1 for each binder crossed");
    }

    #[test]
    fn test_substitute_const_replacement_under_binder() {
        // Constants have no free variables, so shifting is a no-op.
        // Lambda(Prop, Var(1))  with replacement Const("c") for target 0:
        //   body: substitute(Var(1), 1, shift(Const("c"), 0, 1))
        //       = substitute(Var(1), 1, Const("c"))
        //       = Const("c")   (since Var(1) == target 1)
        let term = lam("x", prop(), ProofTerm::Var(1));
        let replacement = ProofTerm::Const("c".to_string());
        let result = substitute(&term, 0, &replacement);
        let expected = lam("x", prop(), ProofTerm::Const("c".to_string()));
        assert_eq!(result, expected, "constant replacement should work correctly under binder");
    }

    #[test]
    fn test_substitute_no_capture_under_pi() {
        // Same capture-avoidance test but for Pi instead of Lambda.
        // Pi(Prop, Var(1)) with replacement Var(0) for target 0:
        //   codomain: substitute(Var(1), 1, shift(Var(0), 0, 1))
        //           = substitute(Var(1), 1, Var(1))
        //           = Var(1)
        let term = ProofTerm::Pi {
            binder_name: "x".to_string(),
            domain: Box::new(prop()),
            codomain: Box::new(ProofTerm::Var(1)),
        };
        let replacement = ProofTerm::Var(0);
        let result = substitute(&term, 0, &replacement);
        let expected = ProofTerm::Pi {
            binder_name: "x".to_string(),
            domain: Box::new(prop()),
            codomain: Box::new(ProofTerm::Var(1)),
        };
        assert_eq!(
            result, expected,
            "free variable in replacement must be shifted to avoid capture by Pi binder"
        );
    }

    // -----------------------------------------------------------------------
    // Kernel-owned names (2026-09-28): a context cannot counterfeit a
    // foundation or declare a trust marker.
    // -----------------------------------------------------------------------

    /// Every kernel-owned name, as the kernel classifies it.
    const RESERVED: [(&str, ReservedKernelName); 11] = [
        ("propext", ReservedKernelName::Foundation),
        ("Quot.sound", ReservedKernelName::Foundation),
        ("Classical.choice", ReservedKernelName::Foundation),
        ("Quot", ReservedKernelName::Foundation),
        ("Quot.mk", ReservedKernelName::Foundation),
        ("Quot.lift", ReservedKernelName::Foundation),
        ("Quot.ind", ReservedKernelName::Foundation),
        ("sorry", ReservedKernelName::TrustMarker),
        ("sorryAx", ReservedKernelName::TrustMarker),
        ("trustedArith", ReservedKernelName::TrustMarker),
        ("trustedAy", ReservedKernelName::TrustMarker),
    ];

    #[test]
    fn kernel_owned_names_are_refused_in_every_declaration_kind() {
        for (name, class) in RESERVED {
            assert_eq!(reserved_kernel_name(name), Some(class), "{name}");
            let mut ctx = KernelContext::new();
            for (kind, result) in [
                ("axiom", ctx.add_axiom(name, prop())),
                ("definition", ctx.add_definition(name, prop(), prop())),
            ] {
                let err = result.expect_err(&format!("{name} as {kind} must be refused"));
                assert!(err.to_string().contains("reserved kernel name"), "{name}: {err}");
            }
            assert!(ctx.is_empty(), "a refused declaration must leave nothing behind");
        }
    }

    /// The refusal names WHY no ProofTerm declaration is the canonical one.
    #[test]
    fn foundation_refusals_state_the_canonical_mismatch() {
        let arity = reserved_declaration_refusal("Classical.choice", true).unwrap();
        assert!(arity.contains("universe arity 1"), "{arity}");
        let lift = reserved_declaration_refusal("Quot.lift", true).unwrap();
        assert!(lift.contains("universe arity 2"), "{lift}");
        let propext = reserved_declaration_refusal("propext", true).unwrap();
        assert!(propext.contains("`Iff` and `Eq.{1}`"), "{propext}");
        let def = reserved_declaration_refusal("Quot.sound", false).unwrap();
        assert!(def.contains("counterfeit"), "{def}");
        let marker = reserved_declaration_refusal("sorryAx", false).unwrap();
        assert!(marker.contains("trust marker") && marker.contains("a Definition"), "{marker}");
    }

    /// The boundary: names that merely resemble a kernel-owned one, and the
    /// historical whitelist entries that are not kernel axioms, stay declarable.
    #[test]
    fn near_miss_names_stay_declarable() {
        for name in [
            "proofIrrel",
            "Eq.refl",
            "funext",
            "propext.x",
            "Quot.sound2",
            "Quot.soundness",
            "sorryAxiom",
            "trustedAyx",
            "Classical",
            "False",
            "Trust.Int",
        ] {
            assert_eq!(reserved_kernel_name(name), None, "{name}");
            let mut ctx = KernelContext::new();
            ctx.add_axiom(name, prop()).unwrap_or_else(|e| panic!("{name}: {e}"));
        }
    }

    /// The pre-fix attack on the checker itself: with `propext : False` in the
    /// context, `check_proof` accepted the bare constant as a proof of `False`.
    /// The declaration is now refused, so the constant is unknown to the local
    /// checker and the query is a type error.
    #[test]
    fn a_counterfeit_foundation_cannot_type_a_proof_of_false() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("False", prop()).expect("an ordinary axiom");
        let false_ty = ProofTerm::Const("False".to_string());
        assert!(ctx.add_axiom("propext", false_ty.clone()).is_err());
        let query =
            KernelQuery { term: ProofTerm::Const("propext".to_string()), expected_type: false_ty };
        let result = check_proof(&query, &ctx).expect("check_proof reports, never errors");
        assert!(matches!(result, KernelResult::TypeError(_)), "{result:?}");
    }

    /// Pins the local arity table (and the `propext` statement claim) against
    /// the Clean kernel's OWN canonical declarations, so neither can drift.
    #[test]
    fn canonical_foundation_arities_match_the_kernel_prelude() {
        use clean_kernel::{ConstantKind, Environment, Expr, ExprKind, Name};

        fn consts(expr: &Expr, out: &mut Vec<(String, usize)>) {
            match expr.kind() {
                ExprKind::Const(name, levels) => out.push((name.to_string(), levels.len())),
                ExprKind::App(f, a) => {
                    consts(f, out);
                    consts(a, out);
                }
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    consts(t, out);
                    consts(b, out);
                }
                _ => {}
            }
        }

        let env = Environment::with_prelude();
        for (name, arity) in CANONICAL_FOUNDATION_UNIVERSE_ARITY {
            assert_eq!(reserved_kernel_name(name), Some(ReservedKernelName::Foundation), "{name}");
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("the kernel prelude declares {name}"));
            assert_eq!(info.kind, ConstantKind::Axiom, "{name} is canonically an Axiom");
            assert!(info.value.is_none(), "{name} is canonically value-less");
            assert_eq!(info.level_params.len(), arity, "{name}: canonical universe arity");
        }
        let propext = env.get_const(&Name::from_string("propext")).expect("propext");
        let mut named = Vec::new();
        consts(&propext.type_, &mut named);
        assert!(named.contains(&("Iff".to_string(), 0)), "{named:?}");
        assert!(named.contains(&("Eq".to_string(), 1)), "propext names Eq.{{1}}: {named:?}");
        // Every kernel foundation is covered by the table.
        for (name, class) in RESERVED {
            if class == ReservedKernelName::Foundation {
                assert!(
                    CANONICAL_FOUNDATION_UNIVERSE_ARITY.iter().any(|(n, _)| *n == name),
                    "{name} missing from the arity table"
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // Definitions are kernel-checked (2026-09-29, cb/track-b review)
    // -----------------------------------------------------------------------

    fn named(name: &str) -> ProofTerm {
        ProofTerm::Const(name.to_string())
    }

    /// The reviewer's `mySorry : False := Sort 0`: `False` is a well-typed
    /// definition (`Sort 0 : Sort 1`), but `Sort 0` is not a term of it. Before,
    /// the entry was stored and `check_proof` typed `mySorry` as `False`.
    #[test]
    fn an_ill_typed_definition_is_refused_and_cannot_prove_its_type() {
        let mut ctx = KernelContext::new();
        ctx.add_definition("False", ProofTerm::Sort(1), prop()).expect("Prop : Type");
        let err = ctx
            .add_definition("mySorry", named("False"), prop())
            .expect_err("`Sort 0` is not a term of `False`");
        assert!(err.to_string().contains("not its declared type"), "{err}");
        assert!(ctx.lookup("mySorry").is_none());
        let query = KernelQuery { term: named("mySorry"), expected_type: named("False") };
        assert!(!check_proof(&query, &ctx).expect("no kernel error").is_valid());
    }

    /// A declared type must be a TYPE (its own type a `Sort`), and a value must
    /// type-check at all; the refusal names which half failed.
    #[test]
    fn a_definition_needs_a_well_formed_type_and_a_typeable_value() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("P", prop()).unwrap();
        ctx.add_axiom("p", named("P")).unwrap();
        let err = ctx.add_definition("q", named("p"), named("p")).expect_err("`p` is a proof");
        assert!(err.to_string().contains("declared type of definition `q`"), "{err}");
        let err = ctx.add_definition("r", named("P"), named("ghost")).expect_err("undeclared");
        assert!(err.to_string().contains("value of definition `r`"), "{err}");
        assert!(err.to_string().contains("unknown constant: ghost"), "{err}");
        // Control: `p : P` is a well-typed definition body.
        ctx.add_definition("s", named("P"), named("p")).expect("well-typed");
        // And a later definition may unfold an earlier one through its type.
        ctx.add_definition("T", ProofTerm::Sort(1), prop()).unwrap();
        ctx.add_definition(
            "idT",
            arrow(named("T"), named("T")),
            lam("x", named("T"), ProofTerm::Var(0)),
        )
        .expect("unfolds nothing it has not seen");
    }

    /// `Sort MAX` has no successor: `saturating_add` used to type it as itself
    /// (Type : Type).
    #[test]
    fn the_top_universe_has_no_type() {
        let ctx = KernelContext::new();
        let err = infer_type(&ProofTerm::Sort(u32::MAX), &ctx, &[]).expect_err("no successor");
        assert!(err.to_string().contains("universe level overflow"), "{err}");
        assert_eq!(
            infer_type(&ProofTerm::Sort(u32::MAX - 1), &ctx, &[]).expect("has a successor"),
            ProofTerm::Sort(u32::MAX)
        );
    }

    /// A lambda's binder type must be a TYPE, as a `Pi`'s domain must.
    #[test]
    fn a_lambda_binder_must_be_a_type() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("P", prop()).unwrap();
        ctx.add_axiom("p", named("P")).unwrap();
        let err = infer_type(&lam("x", named("p"), ProofTerm::Var(0)), &ctx, &[])
            .expect_err("`p` is a proof, not a type");
        assert!(err.to_string().contains("expected Sort(_)"), "{err}");
        assert!(infer_type(&lam("x", named("P"), ProofTerm::Var(0)), &ctx, &[]).is_ok());
    }

    // -----------------------------------------------------------------------
    // de Bruijn: a local's type is lifted past the binders after it
    // (2026-09-29, cb/track-b round-2 review)
    // -----------------------------------------------------------------------

    fn pi(name: &str, domain: ProofTerm, codomain: ProofTerm) -> ProofTerm {
        ProofTerm::Pi {
            binder_name: name.to_string(),
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    fn app(f: ProofTerm, a: ProofTerm) -> ProofTerm {
        ProofTerm::App(Box::new(f), Box::new(a))
    }

    fn var(idx: usize) -> ProofTerm {
        ProofTerm::Var(idx)
    }

    /// The polymorphic identity `λA:Type. λa:A. a` has type `ΠA:Type. Πa:A. A`
    /// — `A` is `Var 1` under the `a` binder. Unshifted, the lookup returned
    /// `a`'s stored type `Var 0` verbatim, `ΠA. Πa:A. a`, and the true type
    /// was refused.
    #[test]
    fn a_locals_type_is_lifted_past_the_binders_after_it() {
        let ctx = KernelContext::new();
        let id = lam("A", type_sort(), lam("a", var(0), var(0)));
        let ty = infer_type(&id, &ctx, &[]).expect("the polymorphic identity types");
        assert_eq!(ty, pi("A", type_sort(), pi("a", var(0), var(1))));
        // Directly, at depth 3: `Var 1` reads the entry pushed at depth 1,
        // whose `Var 0` (the first binder) is `Var 2` at the use site.
        let locals = [ProofTerm::Sort(2), var(0), prop()];
        assert_eq!(infer_type(&var(1), &ctx, &locals).unwrap(), var(2));
        assert_eq!(infer_type(&var(0), &ctx, &locals).unwrap(), prop());
        assert_eq!(infer_type(&var(2), &ctx, &locals).unwrap(), ProofTerm::Sort(2));
    }

    /// The reviewer's attack: `(λP:Sort 2. λx:P. λQ:Prop. x) Type Prop` typed as
    /// `∀Q:Prop, Q` and so passed as a definition of that type. Its true type is
    /// `ΠQ:Prop. Type`, and `K`'s is `ΠP. Πx:P. ΠQ:Prop. P`, not `… Q`.
    #[test]
    fn the_k_combinator_does_not_prove_every_proposition() {
        let mut ctx = KernelContext::new();
        let all_props = pi("Q", prop(), var(0));
        ctx.add_definition("False", type_sort(), all_props.clone()).expect("∀Q:Prop, Q : Type");
        let k = lam("P", ProofTerm::Sort(2), lam("x", var(0), lam("Q", prop(), var(1))));
        let k_true = pi("P", ProofTerm::Sort(2), pi("x", var(0), pi("Q", prop(), var(2))));
        let k_false = pi("P", ProofTerm::Sort(2), pi("x", var(0), pi("Q", prop(), var(0))));
        assert_eq!(infer_type(&k, &ctx, &[]).unwrap(), k_true);
        let err = ctx.add_definition("K_bad", k_false, k.clone()).expect_err("not K's type");
        assert!(err.to_string().contains("not its declared type"), "{err}");
        ctx.add_definition("K", k_true, k.clone()).expect("K at its true type");
        let bad = app(app(k, type_sort()), prop());
        assert_eq!(infer_type(&bad, &ctx, &[]).unwrap(), pi("Q", prop(), type_sort()));
        let err = ctx.add_definition("bad", named("False"), bad.clone()).expect_err("not False");
        assert!(err.to_string().contains("not its declared type"), "{err}");
        let query = KernelQuery { term: bad, expected_type: all_props };
        assert!(matches!(check_proof(&query, &ctx).unwrap(), KernelResult::Invalid(_)));
    }

    /// A dependent hypothesis: in `λA. λP:A→Prop. λa:A. λb:A. λh:P a. h`, the
    /// stored `P a` is `Var 2 Var 1` (spelled at depth 4) and reads
    /// `Var 3 Var 2` under `h`. Unlifted, `Var 2 Var 1` under `h` names `a b`,
    /// an application of a non-function.
    #[test]
    fn a_dependent_hypothesis_keeps_its_predicate_and_witness() {
        let ctx = KernelContext::new();
        let a_to_prop = |a: usize| pi("_", var(a), prop());
        let body = lam("h", app(var(2), var(1)), var(0));
        let term =
            lam("A", type_sort(), lam("P", a_to_prop(0), lam("a", var(1), lam("b", var(2), body))));
        let ty = infer_type(&term, &ctx, &[]).expect("types");
        let want = pi(
            "A",
            type_sort(),
            pi(
                "P",
                a_to_prop(0),
                pi("a", var(1), pi("b", var(2), pi("h", app(var(2), var(1)), app(var(3), var(2))))),
            ),
        );
        assert_eq!(ty, want);
    }

    /// Every context type is closed, because the `Const` rule returns it
    /// unshifted under any binders: an axiom whose type has a free variable,
    /// or is not a type at all, is refused like an ill-formed definition type.
    #[test]
    fn an_axiom_type_must_be_a_closed_type() {
        let mut ctx = KernelContext::new();
        let err = ctx.add_axiom("ax", var(0)).expect_err("free variable");
        assert!(err.to_string().contains("declared type of axiom `ax`"), "{err}");
        assert!(err.to_string().contains("out of scope"), "{err}");
        // Before: `λP:Prop. ax` typed as `ΠP:Prop. P`.
        assert!(infer_type(&lam("P", prop(), named("ax")), &ctx, &[]).is_err());
        ctx.add_axiom("P", prop()).unwrap();
        ctx.add_axiom("p", named("P")).unwrap();
        let err = ctx.add_axiom("q", named("p")).expect_err("`p` is a proof, not a type");
        assert!(err.to_string().contains("expected Sort(_)"), "{err}");
        let err = ctx.add_axiom("r", named("later")).expect_err("declared after");
        assert!(err.to_string().contains("unknown constant: later"), "{err}");
        assert_eq!(ctx.len(), 2, "a refused axiom leaves nothing behind");
    }

    #[test]
    fn wave493_deep_binder_stack_and_accumulated_shift_substitution_match_oracle() {
        // Verify `shift(shift(...shift(rep, 0, 1)..., 0, 1), 0, 1) == shift(rep, 0, d)`
        // and multi-binder capture-avoiding `substitute`.
        let rep = lam("inner", prop(), app(var(0), app(var(1), var(3))));
        let mut iter_shifted = rep.clone();
        for d in 1..=5 {
            iter_shifted = shift(&iter_shifted, 0, 1);
            assert_eq!(iter_shifted, shift(&rep, 0, d));
        }
        assert!(shift_opt(&prop(), 0, 5).is_none());

        // Under 3 nested binders, Var(3) targets outer `target_idx = 0`, Var(4) shifts down to Var(3),
        // and bound Vars 0..=2 stay untouched.
        let nested = lam(
            "b1",
            prop(),
            pi("b2", prop(), lam("b3", prop(), app(app(var(3), var(4)), var(1)))),
        );
        let subbed = substitute(&nested, 0, &rep);
        let expected = lam(
            "b1",
            prop(),
            pi("b2", prop(), lam("b3", prop(), app(app(shift(&rep, 0, 3), var(3)), var(1)))),
        );
        assert_eq!(subbed, expected);
    }
}
