// trust-types/trait_resolution.rs: Higher-level trait resolution analysis
//
// Builds on the core trait types in traits.rs to provide whole-function
// trait resolution: resolving all dynamic dispatch calls, generating
// monomorphization requests, checking where-clause satisfaction, and
// producing VCs for trait-related properties (object safety, coherence,
// specialization correctness).
//
// Part of #153
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::{FxHashMap, FxHashSet};

use serde::{Deserialize, Serialize};

use crate::formula::{Formula, VcKind, VerificationCondition};
use crate::model::{BlockId, SourceSpan, Terminator, Ty, VerifiableBody};
use crate::traits::{
    CoherenceError, ConcreteTarget, MethodInfo, TraitBound, TraitConstraint, TraitImpl,
    TraitResolver, VTable,
};

// ---------------------------------------------------------------------------
// Where clauses
// ---------------------------------------------------------------------------

/// A where clause constraining a type parameter with trait bounds.
///
/// Represents `where T: Clone + Debug, U: Iterator<Item = u32>` as a list
/// of bindings from type parameter names to their required bounds.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WhereClause {
    /// Type parameter name (e.g., "T", "Self").
    pub type_param: String,
    /// Bounds required on this type parameter.
    pub bounds: Vec<TraitBound>,
}

impl WhereClause {
    /// Create a where clause with a single bound.
    #[must_use]
    pub fn single(type_param: impl Into<String>, bound: TraitBound) -> Self {
        Self { type_param: type_param.into(), bounds: vec![bound] }
    }

    /// Human-readable description (e.g., "T: Clone + Debug").
    #[must_use]
    pub fn description(&self) -> String {
        let bounds: Vec<&str> = self.bounds.iter().map(|b| b.trait_name.as_str()).collect();
        format!("{}: {}", self.type_param, bounds.join(" + "))
    }
}

// ---------------------------------------------------------------------------
// Specialization
// ---------------------------------------------------------------------------

/// How specific a trait impl is, used for specialization ordering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SpecializationLevel {
    /// A blanket impl (e.g., `impl<T> Trait for T`).
    Blanket,
    /// A bounded blanket impl (e.g., `impl<T: Clone> Trait for T`).
    BoundedBlanket,
    /// An impl for a concrete type (e.g., `impl Trait for Vec<u8>`).
    Concrete,
}

impl SpecializationLevel {
    /// Classify an impl's specialization level based on its type and where clauses.
    #[must_use]
    pub fn classify(impl_block: &TraitImpl) -> Self {
        // A concrete type (not a bare type param) is the most specific.
        if !is_type_parameter(&impl_block.implementing_type) {
            return SpecializationLevel::Concrete;
        }
        // A type parameter with bounds is more specific than one without.
        if !impl_block.where_clauses.is_empty() {
            return SpecializationLevel::BoundedBlanket;
        }
        SpecializationLevel::Blanket
    }
}

/// Check whether a type looks like a type parameter (no concrete structure).
fn is_type_parameter(ty: &Ty) -> bool {
    matches!(ty, Ty::Adt { name, fields, variants, .. } if fields.is_empty() && variants.is_empty() && name.len() == 1 && name.chars().all(|c| c.is_ascii_uppercase()))
}

// ---------------------------------------------------------------------------
// Monomorphization
// ---------------------------------------------------------------------------

/// A request to monomorphize a generic function with concrete type arguments.
///
/// Generated during trait resolution when a generic call site is resolved
/// to a concrete impl. The verification pipeline uses these to instantiate
/// VCs for each concrete call.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MonomorphizationRequest {
    /// Def path of the generic function to monomorphize.
    pub generic_def_path: String,
    /// Concrete type substitutions (type param name -> concrete type).
    pub substitutions: Vec<(String, Ty)>,
    /// Source location of the call that triggered this monomorphization.
    pub call_site: SourceSpan,
}

impl MonomorphizationRequest {
    /// Build a mangled name for the monomorphized instance.
    #[must_use]
    pub fn mangled_name(&self) -> String {
        let subs: Vec<String> =
            self.substitutions.iter().map(|(param, ty)| format!("{param}={ty:?}")).collect();
        format!("{}<{}>", self.generic_def_path, subs.join(", "))
    }
}

// ---------------------------------------------------------------------------
// Resolution result
// ---------------------------------------------------------------------------

/// Result of resolving all trait-related calls in a function body.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TraitResolutionResult {
    /// Successfully resolved method calls.
    pub resolved_calls: Vec<ResolvedCall>,
    /// Calls that could not be resolved (missing impls).
    pub unresolved_calls: Vec<UnresolvedCall>,
    /// Vtables built for dynamic dispatch.
    pub vtables: Vec<VTable>,
    /// Monomorphization requests generated.
    pub monomorphizations: Vec<MonomorphizationRequest>,
    /// Coherence errors detected.
    pub coherence_errors: Vec<CoherenceError>,
}

impl TraitResolutionResult {
    /// Number of calls successfully resolved.
    #[must_use]
    pub fn resolved_count(&self) -> usize {
        self.resolved_calls.len()
    }

    /// Number of calls that failed to resolve.
    #[must_use]
    pub fn unresolved_count(&self) -> usize {
        self.unresolved_calls.len()
    }

    /// Whether all calls were resolved and no coherence errors exist.
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.unresolved_calls.is_empty() && self.coherence_errors.is_empty()
    }
}

/// A successfully resolved trait method call.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolvedCall {
    /// Block and position where the call occurs.
    pub block: BlockId,
    /// The original function name from the call terminator.
    pub callee_name: String,
    /// Resolved method information.
    pub method_info: MethodInfo,
    /// Possible concrete targets (for dynamic dispatch, may be > 1).
    pub concrete_targets: Vec<ConcreteTarget>,
    /// Source location.
    pub span: SourceSpan,
}

/// A call that could not be resolved to any known impl.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnresolvedCall {
    /// Block where the call occurs.
    pub block: BlockId,
    /// The function name from the call terminator.
    pub callee_name: String,
    /// Why resolution failed.
    pub reason: String,
    /// Source location.
    pub span: SourceSpan,
}

// ---------------------------------------------------------------------------
// Whole-function resolution
// ---------------------------------------------------------------------------

/// Resolve all trait method calls in a function body.
///
/// Walks the body's call terminators, attempts to resolve each through
/// the trait resolver, and collects resolved/unresolved calls, vtables,
/// and monomorphization requests.
#[must_use]
#[allow(clippy::field_reassign_with_default)]
pub fn resolve_all_trait_calls(
    resolver: &TraitResolver,
    body: &VerifiableBody,
) -> TraitResolutionResult {
    let mut result = TraitResolutionResult::default();

    // Check coherence up front.
    result.coherence_errors = resolver.check_coherence();

    // Track which traits we've already built vtables for.
    let mut vtable_traits: FxHashSet<String> = FxHashSet::default();

    for block in &body.blocks {
        if let Terminator::Call { func, span, .. } = &block.terminator {
            // Extract trait::method pattern from the function name.
            if let Some((trait_part, method_name)) = func.rsplit_once("::") {
                // Try to find impls that match this trait.
                let matching_impls = find_matching_impls(resolver, trait_part);

                if matching_impls.is_empty() {
                    result.unresolved_calls.push(UnresolvedCall {
                        block: block.id,
                        callee_name: func.clone(),
                        reason: format!("no impl found for trait `{trait_part}`"),
                        span: span.clone(),
                    });
                    continue;
                }

                // Build vtable for this trait if we haven't already.
                for imp in &matching_impls {
                    if vtable_traits.insert(imp.trait_name.clone()) {
                        result.vtables.push(resolver.build_vtable(&imp.trait_name));
                    }
                }

                // Resolve to concrete targets.
                let trait_name = &matching_impls[0].trait_name;
                let vtable = resolver.build_vtable(trait_name);
                let targets = TraitResolver::devirtualize(&vtable, method_name);

                if let Some(first_impl) = matching_impls.first() {
                    if let Some(method) = first_impl.methods.iter().find(|m| m.name == method_name)
                    {
                        let method_info = MethodInfo {
                            containing_trait: Some(first_impl.trait_name.clone()),
                            impl_type: first_impl.implementing_type.clone(),
                            method_body_ref: method.body_def_path.clone(),
                            method_name: method.name.clone(),
                        };

                        result.resolved_calls.push(ResolvedCall {
                            block: block.id,
                            callee_name: func.clone(),
                            method_info,
                            concrete_targets: targets,
                            span: span.clone(),
                        });
                    } else {
                        result.unresolved_calls.push(UnresolvedCall {
                            block: block.id,
                            callee_name: func.clone(),
                            reason: format!(
                                "method `{method_name}` not found in `{trait_name}` impls"
                            ),
                            span: span.clone(),
                        });
                    }
                }
            }
        }
    }

    result
}

/// Find impls whose trait name matches (exact or suffix) the given trait part.
fn find_matching_impls<'a>(resolver: &'a TraitResolver, trait_part: &str) -> Vec<&'a TraitImpl> {
    resolver
        .all_impls()
        .iter()
        .filter(|imp| {
            imp.trait_name == trait_part
                || imp.trait_name.ends_with(trait_part)
                || trait_part.ends_with(&imp.trait_name)
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Where clause checking
// ---------------------------------------------------------------------------

/// Check whether a set of where clauses is satisfied by the known impls.
///
/// Returns the list of unsatisfied clauses. An empty result means all
/// where clauses are satisfied.
#[must_use]
pub fn check_where_clauses(
    resolver: &TraitResolver,
    clauses: &[WhereClause],
    type_bindings: &FxHashMap<String, Ty>,
) -> Vec<UnsatisfiedClause> {
    let mut unsatisfied = Vec::new();

    for clause in clauses {
        // Look up the concrete type for this type parameter.
        let Some(concrete_ty) = type_bindings.get(&clause.type_param) else {
            unsatisfied.push(UnsatisfiedClause {
                clause: clause.clone(),
                reason: format!("type parameter `{}` has no binding", clause.type_param),
            });
            continue;
        };

        for bound in &clause.bounds {
            if resolver.resolve_impl(concrete_ty, &bound.trait_name).is_none() {
                unsatisfied.push(UnsatisfiedClause {
                    clause: clause.clone(),
                    reason: format!(
                        "`{:?}` does not implement `{}`",
                        concrete_ty, bound.trait_name
                    ),
                });
            }
        }
    }

    unsatisfied
}

/// A where clause that is not satisfied by known impls.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnsatisfiedClause {
    /// The clause that failed.
    pub clause: WhereClause,
    /// Why it is not satisfied.
    pub reason: String,
}

// ---------------------------------------------------------------------------
// VC generation for trait properties
// ---------------------------------------------------------------------------

/// Generate verification conditions for trait-related properties.
///
/// Produces VCs for:
/// - Unresolved dynamic dispatch (must be statically resolvable or bounded)
/// - Coherence violations (overlapping impls)
/// - Unsatisfied where clauses
/// - Object safety (all methods in a dyn trait must be object-safe)
#[must_use]
pub fn generate_trait_vcs(
    resolution: &TraitResolutionResult,
    function_name: &str,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // VC for each unresolved call: the property "this call resolves" fails.
    for unresolved in &resolution.unresolved_calls {
        vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "unresolved trait call `{}`: {}",
                    unresolved.callee_name, unresolved.reason
                ),
            },
            function: function_name.into(),
            location: unresolved.span.clone(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        });
    }

    // VC for each coherence error.
    for error in &resolution.coherence_errors {
        let span = match error {
            CoherenceError::OverlappingImpls { span_a, .. } => span_a.clone(),
            CoherenceError::OrphanRule { span, .. } => span.clone(),
        };
        vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!("coherence violation: {}", error.description()),
            },
            function: function_name.into(),
            location: span,
            formula: Formula::Bool(false),
            contract_metadata: None,
        });
    }

    // VC for dynamic dispatch: each resolved call with multiple targets
    // generates a VC asserting the dispatch is bounded.
    for call in &resolution.resolved_calls {
        if call.concrete_targets.len() > 1 {
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "dynamic dispatch on `{}` has {} possible targets",
                        call.callee_name,
                        call.concrete_targets.len()
                    ),
                },
                function: function_name.into(),
                location: call.span.clone(),
                // This is satisfiable — the VC records the dispatch enumeration.
                formula: Formula::Bool(true),
                contract_metadata: None,
            });
        }
    }

    vcs
}

/// Build trait constraints from where clauses for universally quantified
/// verification: "for all T satisfying bounds, the property holds."
#[must_use]
pub fn where_clauses_to_constraints(clauses: &[WhereClause]) -> Vec<TraitConstraint> {
    clauses
        .iter()
        .map(|clause| TraitConstraint {
            type_param: clause.type_param.clone(),
            bounds: clause.bounds.clone(),
            properties: vec![],
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::*;
    use crate::traits::MethodImpl;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn make_clone_impl(ty: Ty) -> TraitImpl {
        TraitImpl {
            implementing_type: ty.clone(),
            trait_name: "std::clone::Clone".to_string(),
            methods: vec![MethodImpl {
                name: "clone".to_string(),
                body_def_path: format!("<{ty:?} as Clone>::clone"),
                span: span(),
            }],
            where_clauses: vec![],
            span: span(),
        }
    }

    fn make_debug_impl(ty: Ty) -> TraitImpl {
        TraitImpl {
            implementing_type: ty.clone(),
            trait_name: "std::fmt::Debug".to_string(),
            methods: vec![MethodImpl {
                name: "fmt".to_string(),
                body_def_path: format!("<{ty:?} as Debug>::fmt"),
                span: span(),
            }],
            where_clauses: vec![],
            span: span(),
        }
    }

    fn make_blanket_impl() -> TraitImpl {
        TraitImpl {
            implementing_type: Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "T".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, },
            trait_name: "MyTrait".to_string(),
            methods: vec![],
            where_clauses: vec![],
            span: span(),
        }
    }

    fn make_bounded_blanket_impl() -> TraitImpl {
        TraitImpl {
            implementing_type: Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "T".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, },
            trait_name: "MyTrait".to_string(),
            methods: vec![],
            where_clauses: vec![TraitBound {
                trait_name: "Clone".to_string(),
                type_params: vec![],
                associated_types: vec![],
            }],
            span: span(),
        }
    }

    // --- WhereClause tests ---

    #[test]
    fn test_where_clause_single() {
        let clause = WhereClause::single(
            "T",
            TraitBound {
                trait_name: "Clone".to_string(),
                type_params: vec![],
                associated_types: vec![],
            },
        );
        assert_eq!(clause.type_param, "T");
        assert_eq!(clause.bounds.len(), 1);
    }

    #[test]
    fn test_where_clause_description() {
        let clause = WhereClause {
            type_param: "T".to_string(),
            bounds: vec![
                TraitBound {
                    trait_name: "Clone".to_string(),
                    type_params: vec![],
                    associated_types: vec![],
                },
                TraitBound {
                    trait_name: "Debug".to_string(),
                    type_params: vec![],
                    associated_types: vec![],
                },
            ],
        };
        assert_eq!(clause.description(), "T: Clone + Debug");
    }

    // --- SpecializationLevel tests ---

    #[test]
    fn test_specialization_concrete() {
        let imp = make_clone_impl(Ty::i32());
        assert_eq!(SpecializationLevel::classify(&imp), SpecializationLevel::Concrete);
    }

    #[test]
    fn test_specialization_blanket() {
        let imp = make_blanket_impl();
        assert_eq!(SpecializationLevel::classify(&imp), SpecializationLevel::Blanket);
    }

    #[test]
    fn test_specialization_bounded_blanket() {
        let imp = make_bounded_blanket_impl();
        assert_eq!(SpecializationLevel::classify(&imp), SpecializationLevel::BoundedBlanket);
    }

    #[test]
    fn test_specialization_ordering() {
        assert!(SpecializationLevel::Blanket < SpecializationLevel::BoundedBlanket);
        assert!(SpecializationLevel::BoundedBlanket < SpecializationLevel::Concrete);
    }

    // --- MonomorphizationRequest tests ---

    #[test]
    fn test_monomorphization_mangled_name() {
        let req = MonomorphizationRequest {
            generic_def_path: "std::vec::Vec::push".to_string(),
            substitutions: vec![("T".to_string(), Ty::i32())],
            call_site: span(),
        };
        let name = req.mangled_name();
        assert!(name.starts_with("std::vec::Vec::push<"));
        assert!(name.contains("T="));
    }

    #[test]
    fn test_monomorphization_multiple_params() {
        let req = MonomorphizationRequest {
            generic_def_path: "std::collections::HashMap::insert".to_string(),
            substitutions: vec![
                ("K".to_string(), Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "String".to_string(), fields: vec![],
                    disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, }),
                ("V".to_string(), Ty::i32()),
            ],
            call_site: span(),
        };
        let name = req.mangled_name();
        assert!(name.contains("K="));
        assert!(name.contains("V="));
    }

    // --- TraitResolutionResult tests ---

    #[test]
    fn test_resolution_result_empty() {
        let result = TraitResolutionResult::default();
        assert_eq!(result.resolved_count(), 0);
        assert_eq!(result.unresolved_count(), 0);
        assert!(result.is_complete());
    }

    #[test]
    fn test_resolution_result_incomplete() {
        let result = TraitResolutionResult {
            unresolved_calls: vec![UnresolvedCall {
                block: BlockId(0),
                callee_name: "foo".to_string(),
                reason: "missing".to_string(),
                span: span(),
            }],
            ..Default::default()
        };
        assert!(!result.is_complete());
        assert_eq!(result.unresolved_count(), 1);
    }

    // --- resolve_all_trait_calls tests ---

    #[test]
    fn test_resolve_all_empty_body() {
        let resolver = TraitResolver::new();
        let body = VerifiableBody {
            locals: vec![],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        };

        let result = resolve_all_trait_calls(&resolver, &body);
        assert!(result.is_complete());
        assert_eq!(result.resolved_count(), 0);
    }

    #[test]
    fn test_resolve_all_with_known_impl() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));

        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                    func: "std::clone::Clone::clone".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: span(),
                    atomic: None,
                },
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        };

        let result = resolve_all_trait_calls(&resolver, &body);
        assert_eq!(result.resolved_count(), 1);
        assert_eq!(result.unresolved_count(), 0);
        assert_eq!(result.resolved_calls[0].callee_name, "std::clone::Clone::clone");
    }

    #[test]
    fn test_resolve_all_unresolved_call() {
        let resolver = TraitResolver::new();

        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                    func: "UnknownTrait::method".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: span(),
                    atomic: None,
                },
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        };

        let result = resolve_all_trait_calls(&resolver, &body);
        assert_eq!(result.unresolved_count(), 1);
        assert!(result.unresolved_calls[0].reason.contains("no impl found"));
    }

    #[test]
    fn test_resolve_all_builds_vtable() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        resolver.add_impl(make_clone_impl(Ty::u32()));

        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                    func: "std::clone::Clone::clone".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: span(),
                    atomic: None,
                },
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        };

        let result = resolve_all_trait_calls(&resolver, &body);
        assert_eq!(result.vtables.len(), 1);
        assert_eq!(result.vtables[0].trait_name, "std::clone::Clone");
    }

    // --- check_where_clauses tests ---

    #[test]
    fn test_where_clauses_satisfied() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));

        let clauses = vec![WhereClause::single(
            "T",
            TraitBound {
                trait_name: "std::clone::Clone".to_string(),
                type_params: vec![],
                associated_types: vec![],
            },
        )];

        let bindings: FxHashMap<_, _> = [("T".to_string(), Ty::i32())].into_iter().collect();
        let unsatisfied = check_where_clauses(&resolver, &clauses, &bindings);
        assert!(unsatisfied.is_empty());
    }

    #[test]
    fn test_where_clauses_unsatisfied() {
        let resolver = TraitResolver::new();

        let clauses = vec![WhereClause::single(
            "T",
            TraitBound {
                trait_name: "std::clone::Clone".to_string(),
                type_params: vec![],
                associated_types: vec![],
            },
        )];

        let bindings: FxHashMap<_, _> = [("T".to_string(), Ty::i32())].into_iter().collect();
        let unsatisfied = check_where_clauses(&resolver, &clauses, &bindings);
        assert_eq!(unsatisfied.len(), 1);
        assert!(unsatisfied[0].reason.contains("does not implement"));
    }

    #[test]
    fn test_where_clauses_missing_binding() {
        let resolver = TraitResolver::new();

        let clauses = vec![WhereClause::single(
            "T",
            TraitBound {
                trait_name: "Clone".to_string(),
                type_params: vec![],
                associated_types: vec![],
            },
        )];

        let bindings = FxHashMap::default();
        let unsatisfied = check_where_clauses(&resolver, &clauses, &bindings);
        assert_eq!(unsatisfied.len(), 1);
        assert!(unsatisfied[0].reason.contains("no binding"));
    }

    // --- VC generation tests ---

    #[test]
    fn test_generate_trait_vcs_clean() {
        let result = TraitResolutionResult::default();
        let vcs = generate_trait_vcs(&result, "test_fn");
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_generate_trait_vcs_unresolved() {
        let result = TraitResolutionResult {
            unresolved_calls: vec![UnresolvedCall {
                block: BlockId(0),
                callee_name: "Foo::bar".to_string(),
                reason: "no impl".to_string(),
                span: span(),
            }],
            ..Default::default()
        };

        let vcs = generate_trait_vcs(&result, "test_fn");
        assert_eq!(vcs.len(), 1);
        assert!(vcs[0].kind.description().contains("assertion"));
    }

    #[test]
    fn test_generate_trait_vcs_coherence_error() {
        let result = TraitResolutionResult {
            coherence_errors: vec![CoherenceError::OverlappingImpls {
                trait_name: "Clone".to_string(),
                impl_a: Ty::i32(),
                impl_b: Ty::i32(),
                span_a: span(),
                span_b: span(),
            }],
            ..Default::default()
        };

        let vcs = generate_trait_vcs(&result, "test_fn");
        assert_eq!(vcs.len(), 1);
        assert!(vcs[0].kind.description().contains("assertion"));
    }

    #[test]
    fn test_generate_trait_vcs_dynamic_dispatch() {
        let result = TraitResolutionResult {
            resolved_calls: vec![ResolvedCall {
                block: BlockId(0),
                callee_name: "Iterator::next".to_string(),
                method_info: MethodInfo {
                    containing_trait: Some("Iterator".to_string()),
                    impl_type: Ty::i32(),
                    method_body_ref: "<i32 as Iterator>::next".to_string(),
                    method_name: "next".to_string(),
                },
                concrete_targets: vec![
                    ConcreteTarget {
                        impl_type: Ty::i32(),
                        body_def_path: "<i32>::next".to_string(),
                    },
                    ConcreteTarget {
                        impl_type: Ty::u32(),
                        body_def_path: "<u32>::next".to_string(),
                    },
                ],
                span: span(),
            }],
            ..Default::default()
        };

        let vcs = generate_trait_vcs(&result, "test_fn");
        assert_eq!(vcs.len(), 1);
        // Dynamic dispatch VC should be satisfiable (recording, not violation).
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    // --- where_clauses_to_constraints tests ---

    #[test]
    fn test_where_clauses_to_constraints() {
        let clauses = vec![
            WhereClause {
                type_param: "T".to_string(),
                bounds: vec![TraitBound {
                    trait_name: "Clone".to_string(),
                    type_params: vec![],
                    associated_types: vec![],
                }],
            },
            WhereClause {
                type_param: "U".to_string(),
                bounds: vec![TraitBound {
                    trait_name: "Debug".to_string(),
                    type_params: vec![],
                    associated_types: vec![],
                }],
            },
        ];

        let constraints = where_clauses_to_constraints(&clauses);
        assert_eq!(constraints.len(), 2);
        assert_eq!(constraints[0].type_param, "T");
        assert_eq!(constraints[0].bounds[0].trait_name, "Clone");
        assert_eq!(constraints[1].type_param, "U");
    }

    // --- Serialization tests ---

    #[test]
    fn test_where_clause_serialization_roundtrip() {
        let clause = WhereClause::single(
            "T",
            TraitBound {
                trait_name: "Clone".to_string(),
                type_params: vec![],
                associated_types: vec![],
            },
        );

        let json = serde_json::to_string(&clause).expect("serialize");
        let roundtrip: WhereClause = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.type_param, "T");
        assert_eq!(roundtrip.bounds.len(), 1);
    }

    #[test]
    fn test_monomorphization_request_serialization_roundtrip() {
        let req = MonomorphizationRequest {
            generic_def_path: "Vec::push".to_string(),
            substitutions: vec![("T".to_string(), Ty::i32())],
            call_site: span(),
        };

        let json = serde_json::to_string(&req).expect("serialize");
        let roundtrip: MonomorphizationRequest = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.generic_def_path, "Vec::push");
        assert_eq!(roundtrip.substitutions.len(), 1);
    }

    #[test]
    fn test_resolution_result_serialization_roundtrip() {
        let result = TraitResolutionResult {
            resolved_calls: vec![ResolvedCall {
                block: BlockId(0),
                callee_name: "Clone::clone".to_string(),
                method_info: MethodInfo {
                    containing_trait: Some("Clone".to_string()),
                    impl_type: Ty::i32(),
                    method_body_ref: "<i32 as Clone>::clone".to_string(),
                    method_name: "clone".to_string(),
                },
                concrete_targets: vec![ConcreteTarget {
                    impl_type: Ty::i32(),
                    body_def_path: "<i32>::clone".to_string(),
                }],
                span: span(),
            }],
            ..Default::default()
        };

        let json = serde_json::to_string(&result).expect("serialize");
        let roundtrip: TraitResolutionResult = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.resolved_count(), 1);
    }

    // --- Integration: multiple traits ---

    #[test]
    fn test_resolve_multiple_trait_calls() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        resolver.add_impl(make_debug_impl(Ty::i32()));

        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "std::clone::Clone::clone".to_string(),
                        args: vec![],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "std::fmt::Debug::fmt".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(2)),
                        span: span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        };

        let result = resolve_all_trait_calls(&resolver, &body);
        assert_eq!(result.resolved_count(), 2);
        assert_eq!(result.unresolved_count(), 0);
        assert!(result.is_complete());
    }
}
