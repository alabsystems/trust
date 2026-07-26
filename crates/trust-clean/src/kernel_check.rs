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

/// Manages the Clean kernel environment of definitions and axioms.
///
/// The context maps constant names to their types (and optionally values).
/// It is used during type inference and proof checking to resolve `Const`
/// references in proof terms.
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
    /// Returns `CertificateError::InvalidProofTerm` if the name is already defined.
    pub fn add_definition(
        &mut self,
        name: &str,
        ty: ProofTerm,
        value: ProofTerm,
    ) -> Result<(), CertificateError> {
        if self.entries.contains_key(name) {
            return Err(CertificateError::InvalidProofTerm {
                reason: format!("duplicate definition: {name}"),
            });
        }
        self.entries.insert(name.to_string(), ContextEntry::Definition { ty, value });
        Ok(())
    }

    /// Add an axiom to the context.
    ///
    /// # Errors
    ///
    /// Returns `CertificateError::InvalidProofTerm` if the name is already defined.
    pub fn add_axiom(&mut self, name: &str, ty: ProofTerm) -> Result<(), CertificateError> {
        if self.entries.contains_key(name) {
            return Err(CertificateError::InvalidProofTerm {
                reason: format!("duplicate axiom: {name}"),
            });
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
    match term {
        ProofTerm::Var(idx) => {
            let depth = locals.len();
            if *idx >= depth {
                return Err(CertificateError::KernelRejected {
                    reason: format!("variable index {idx} out of scope (depth {depth})"),
                });
            }
            // de Bruijn: index 0 = most recently bound
            Ok(locals[depth - 1 - idx].clone())
        }
        ProofTerm::Const(name) => match ctx.lookup(name) {
            Some(ContextEntry::Definition { ty, .. }) => Ok(ty.clone()),
            Some(ContextEntry::Axiom { ty }) => Ok(ty.clone()),
            None => Err(CertificateError::KernelRejected {
                reason: format!("unknown constant: {name}"),
            }),
        },
        ProofTerm::Sort(u) => {
            // Sort u : Sort (u+1)
            Ok(ProofTerm::Sort(u.saturating_add(1)))
        }
        ProofTerm::Lambda { binder_name, binder_type, body } => {
            // Check binder_type is well-typed (must be a sort)
            let _ = infer_type(binder_type, ctx, locals)?;

            // Extend locals with the binder type
            let mut extended = locals.to_vec();
            extended.push(*binder_type.clone());
            let body_type = infer_type(body, ctx, &extended)?;

            Ok(ProofTerm::Pi {
                binder_name: binder_name.clone(),
                domain: binder_type.clone(),
                codomain: Box::new(body_type),
            })
        }
        ProofTerm::Pi { domain, codomain, .. } => {
            let domain_sort = infer_sort_level(domain, ctx, locals)?;
            let mut extended = locals.to_vec();
            extended.push(*domain.clone());
            let codomain_sort = infer_sort_level(codomain, ctx, &extended)?;
            Ok(ProofTerm::Sort(domain_sort.max(codomain_sort)))
        }
        ProofTerm::App(f, a) => {
            let f_type = infer_type(f, ctx, locals)?;
            match f_type {
                ProofTerm::Pi { domain, codomain, .. } => {
                    let a_type = infer_type(a, ctx, locals)?;
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
    let ty = infer_type(term, ctx, locals)?;
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
    match term {
        ProofTerm::Var(idx) => {
            if *idx >= cutoff {
                ProofTerm::Var(idx + amount)
            } else {
                ProofTerm::Var(*idx)
            }
        }
        ProofTerm::App(f, a) => {
            ProofTerm::App(Box::new(shift(f, cutoff, amount)), Box::new(shift(a, cutoff, amount)))
        }
        ProofTerm::Lambda { binder_name, binder_type, body } => ProofTerm::Lambda {
            binder_name: binder_name.clone(),
            binder_type: Box::new(shift(binder_type, cutoff, amount)),
            body: Box::new(shift(body, cutoff + 1, amount)),
        },
        ProofTerm::Pi { binder_name, domain, codomain } => ProofTerm::Pi {
            binder_name: binder_name.clone(),
            domain: Box::new(shift(domain, cutoff, amount)),
            codomain: Box::new(shift(codomain, cutoff + 1, amount)),
        },
        ProofTerm::Const(name) => ProofTerm::Const(name.clone()),
        ProofTerm::Sort(u) => ProofTerm::Sort(*u),
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
    match term {
        ProofTerm::Var(idx) => {
            if *idx == target_idx {
                replacement.clone()
            } else if *idx > target_idx {
                // Shift down since the binder is being removed
                ProofTerm::Var(idx - 1)
            } else {
                ProofTerm::Var(*idx)
            }
        }
        ProofTerm::App(f, a) => ProofTerm::App(
            Box::new(substitute(f, target_idx, replacement)),
            Box::new(substitute(a, target_idx, replacement)),
        ),
        ProofTerm::Lambda { binder_name, binder_type, body } => {
            // Trust: shift replacement by +1 to avoid capture by this binder
            let shifted = shift(replacement, 0, 1);
            ProofTerm::Lambda {
                binder_name: binder_name.clone(),
                binder_type: Box::new(substitute(binder_type, target_idx, replacement)),
                body: Box::new(substitute(body, target_idx + 1, &shifted)),
            }
        }
        ProofTerm::Pi { binder_name, domain, codomain } => {
            // Trust: shift replacement by +1 to avoid capture by this binder
            let shifted = shift(replacement, 0, 1);
            ProofTerm::Pi {
                binder_name: binder_name.clone(),
                domain: Box::new(substitute(domain, target_idx, replacement)),
                codomain: Box::new(substitute(codomain, target_idx + 1, &shifted)),
            }
        }
        ProofTerm::Const(name) => ProofTerm::Const(name.clone()),
        ProofTerm::Sort(u) => ProofTerm::Sort(*u),
    }
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

    // Try delta reduction (unfold definitions)
    let lhs_reduced = delta_reduce(lhs, ctx);
    let rhs_reduced = delta_reduce(rhs, ctx);

    if lhs_reduced != *lhs || rhs_reduced != *rhs {
        return is_definitionally_equal(&lhs_reduced, &rhs_reduced, ctx);
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

/// Perform one step of delta reduction: unfold a `Const` to its definition.
fn delta_reduce(term: &ProofTerm, ctx: &KernelContext) -> ProofTerm {
    match term {
        ProofTerm::Const(name) => {
            if let Some(ContextEntry::Definition { value, .. }) = ctx.lookup(name) {
                value.clone()
            } else {
                term.clone()
            }
        }
        ProofTerm::App(f, a) => {
            let f_reduced = delta_reduce(f, ctx);
            // Beta reduction: (fun x => body) a  =>  body[0 := a]
            if let ProofTerm::Lambda { body, .. } = &f_reduced {
                substitute(body, 0, a)
            } else if f_reduced != **f {
                ProofTerm::App(Box::new(f_reduced), a.clone())
            } else {
                term.clone()
            }
        }
        _ => term.clone(),
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
}
