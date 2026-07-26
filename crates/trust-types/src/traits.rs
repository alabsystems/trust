// trust-types/traits.rs: Trait resolution model for verification
//
// Models Rust's trait system for verification purposes: trait bounds,
// implementations, method resolution, vtable devirtualization, and
// coherence checking. Used by trust_vcgen to resolve dynamic dispatch
// and verify generic code over all satisfying types.
//
// Part of #153
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::{FxHashMap, FxHashSet};

use serde::{Deserialize, Deserializer, Serialize};

use crate::model::{SourceSpan, Ty};

// ---------------------------------------------------------------------------
// Core trait types
// ---------------------------------------------------------------------------

/// A trait bound constraining a type parameter (e.g., `T: Clone + Debug`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraitBound {
    /// Fully qualified trait name (e.g., "std::clone::Clone").
    pub trait_name: String,
    /// Type parameters applied to the trait (e.g., `Iterator<Item = u32>`).
    pub type_params: Vec<Ty>,
    /// Associated type bindings (e.g., `Item = u32` in `Iterator<Item = u32>`).
    pub associated_types: Vec<AssociatedTypeBinding>,
}

/// A binding for an associated type in a trait bound.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AssociatedTypeBinding {
    /// Name of the associated type (e.g., "Item").
    pub name: String,
    /// The concrete type it is bound to.
    pub ty: Ty,
}

/// A concrete trait implementation: `impl Trait for Type`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraitImpl {
    /// The type implementing the trait.
    pub implementing_type: Ty,
    /// Fully qualified trait name.
    pub trait_name: String,
    /// Methods provided by this impl block.
    pub methods: Vec<MethodImpl>,
    /// Where clauses on the impl block.
    pub where_clauses: Vec<TraitBound>,
    /// Source location of the impl block.
    pub span: SourceSpan,
}

/// A method within a trait impl block.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodImpl {
    /// Method name (e.g., "clone", "next").
    pub name: String,
    /// Def path of the method body (for looking up the `VerifiableFunction`).
    pub body_def_path: String,
    /// Source location of the method.
    pub span: SourceSpan,
}

/// Information about a resolved method call.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodInfo {
    /// Trait that contains this method (None for inherent methods).
    pub containing_trait: Option<String>,
    /// The concrete type whose impl provides this method.
    pub impl_type: Ty,
    /// Def path of the method body.
    pub method_body_ref: String,
    /// Method name.
    pub method_name: String,
}

// ---------------------------------------------------------------------------
// VTable and dynamic dispatch
// ---------------------------------------------------------------------------

/// A virtual dispatch table for a `dyn Trait` object.
///
/// Maps method names to the set of concrete implementations that could
/// be dispatched to at runtime. Used by trust_vcgen to enumerate all
/// possible call targets for dynamic dispatch verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VTable {
    /// The trait this vtable is for.
    pub trait_name: String,
    /// Method slots: each maps a method name to its concrete targets.
    pub slots: Vec<VTableSlot>,
}

/// A single slot in a vtable: one trait method and its implementations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VTableSlot {
    /// Method name.
    pub method_name: String,
    /// Concrete implementations that could be dispatched to.
    pub targets: Vec<ConcreteTarget>,
}

/// A concrete dispatch target resolved from a vtable lookup.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConcreteTarget {
    /// The concrete type providing this implementation.
    pub impl_type: Ty,
    /// Def path of the method body.
    pub body_def_path: String,
}

// ---------------------------------------------------------------------------
// Generic verification constraints
// ---------------------------------------------------------------------------

/// A constraint for verifying generic code: "for all T satisfying bounds,
/// the property holds." Used to generate universally quantified VCs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraitConstraint {
    /// The type parameter being constrained (e.g., "T").
    pub type_param: String,
    /// Bounds the type parameter must satisfy.
    pub bounds: Vec<TraitBound>,
    /// Properties that must hold for all satisfying types.
    pub properties: Vec<String>,
}

// ---------------------------------------------------------------------------
// Coherence checking
// ---------------------------------------------------------------------------

/// An error from coherence checking: overlapping trait implementations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CoherenceError {
    /// Two impls overlap: both could apply to the same type.
    OverlappingImpls {
        trait_name: String,
        impl_a: Ty,
        impl_b: Ty,
        span_a: SourceSpan,
        span_b: SourceSpan,
    },
    /// An orphan rule violation: neither the trait nor the type is local.
    OrphanRule { trait_name: String, implementing_type: Ty, span: SourceSpan },
}

impl CoherenceError {
    /// Human-readable description of the coherence error.
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            CoherenceError::OverlappingImpls { trait_name, impl_a, impl_b, .. } => {
                format!("overlapping impls of `{trait_name}` for `{impl_a:?}` and `{impl_b:?}`")
            }
            CoherenceError::OrphanRule { trait_name, implementing_type, .. } => {
                format!(
                    "orphan rule: `{trait_name}` impl for `{implementing_type:?}` \
                     violates coherence"
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// TraitResolver
// ---------------------------------------------------------------------------

/// Resolves trait method calls to concrete implementations.
///
/// Maintains a registry of known trait impls and provides method
/// resolution, devirtualization, and coherence checking.
#[derive(Debug, Clone, Default, Serialize)]
pub struct TraitResolver {
    /// All known trait implementations.
    impls: Vec<TraitImpl>,
    /// Index: trait_name -> indices into `impls`.
    trait_index: FxHashMap<String, Vec<usize>>,
}

impl TraitResolver {
    /// Create a new empty resolver.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a trait implementation.
    pub fn add_impl(&mut self, trait_impl: TraitImpl) {
        let idx = self.impls.len();
        self.trait_index.entry(trait_impl.trait_name.clone()).or_default().push(idx);
        self.impls.push(trait_impl);
    }

    /// Rebuild the trait lookup index from the registered impls.
    pub fn rebuild_index(&mut self) {
        self.trait_index.clear();
        for (idx, trait_impl) in self.impls.iter().enumerate() {
            self.trait_index.entry(trait_impl.trait_name.clone()).or_default().push(idx);
        }
    }

    /// Return all registered implementations.
    #[must_use]
    pub fn all_impls(&self) -> &[TraitImpl] {
        &self.impls
    }

    /// Return implementations for a specific trait.
    #[must_use]
    pub fn impls_for_trait(&self, trait_name: &str) -> Vec<&TraitImpl> {
        self.trait_index
            .get(trait_name)
            .map(|indices| indices.iter().map(|&i| &self.impls[i]).collect())
            .unwrap_or_default()
    }

    /// Resolve which impl applies for a given type and trait.
    ///
    /// Returns the first matching impl (exact type match). In a full
    /// implementation this would handle specialization and blanket impls.
    #[must_use]
    pub fn resolve_impl(&self, ty: &Ty, trait_name: &str) -> Option<&TraitImpl> {
        self.impls_for_trait(trait_name).into_iter().find(|imp| &imp.implementing_type == ty)
    }

    /// Resolve a method call on a receiver type.
    ///
    /// Searches all trait impls for a method matching the given name on
    /// the receiver type. Returns the first match.
    #[must_use]
    pub fn resolve_method(&self, receiver_ty: &Ty, method_name: &str) -> Option<MethodInfo> {
        for imp in &self.impls {
            if &imp.implementing_type != receiver_ty {
                continue;
            }
            if let Some(method) = imp.methods.iter().find(|m| m.name == method_name) {
                return Some(MethodInfo {
                    containing_trait: Some(imp.trait_name.clone()),
                    impl_type: imp.implementing_type.clone(),
                    method_body_ref: method.body_def_path.clone(),
                    method_name: method.name.clone(),
                });
            }
        }
        None
    }

    /// Build a vtable for a trait, collecting all known implementations.
    ///
    /// The vtable maps each method name to the set of concrete targets
    /// from all registered impls of the trait.
    #[must_use]
    pub fn build_vtable(&self, trait_name: &str) -> VTable {
        let impls = self.impls_for_trait(trait_name);

        // Collect all method names across impls.
        let mut method_names: Vec<String> = Vec::new();
        let mut seen: FxHashSet<&str> = FxHashSet::default();
        for imp in &impls {
            for method in &imp.methods {
                if seen.insert(&method.name) {
                    method_names.push(method.name.clone());
                }
            }
        }

        let slots = method_names
            .into_iter()
            .map(|method_name| {
                let targets = impls
                    .iter()
                    .filter_map(|imp| {
                        imp.methods.iter().find(|m| m.name == method_name).map(|m| ConcreteTarget {
                            impl_type: imp.implementing_type.clone(),
                            body_def_path: m.body_def_path.clone(),
                        })
                    })
                    .collect();
                VTableSlot { method_name, targets }
            })
            .collect();

        VTable { trait_name: trait_name.to_string(), slots }
    }

    /// Devirtualize a dynamic dispatch call: given a vtable and method name,
    /// return all possible concrete targets.
    #[must_use]
    pub fn devirtualize(vtable: &VTable, method_name: &str) -> Vec<ConcreteTarget> {
        vtable
            .slots
            .iter()
            .find(|slot| slot.method_name == method_name)
            .map(|slot| slot.targets.clone())
            .unwrap_or_default()
    }

    /// Check trait coherence: detect overlapping implementations.
    ///
    /// Two impls overlap if they implement the same trait for the same type.
    /// This is a simplified check; a full implementation would also handle
    /// blanket impls, negative impls, and specialization.
    #[must_use]
    pub fn check_coherence(&self) -> Vec<CoherenceError> {
        let mut errors = Vec::new();

        for (trait_name, indices) in &self.trait_index {
            for i in 0..indices.len() {
                for j in (i + 1)..indices.len() {
                    let a = &self.impls[indices[i]];
                    let b = &self.impls[indices[j]];

                    if a.implementing_type == b.implementing_type {
                        errors.push(CoherenceError::OverlappingImpls {
                            trait_name: trait_name.clone(),
                            impl_a: a.implementing_type.clone(),
                            impl_b: b.implementing_type.clone(),
                            span_a: a.span.clone(),
                            span_b: b.span.clone(),
                        });
                    }
                }
            }
        }

        errors
    }
}

impl<'de> Deserialize<'de> for TraitResolver {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct TraitResolverData {
            impls: Vec<TraitImpl>,
        }

        let TraitResolverData { impls } = TraitResolverData::deserialize(deserializer)?;
        let mut resolver = TraitResolver { impls, trait_index: FxHashMap::default() };
        resolver.rebuild_index();
        Ok(resolver)
    }
}

/// Collect trait implementations referenced in a function body.
///
/// Scans call terminators for method calls that match known trait impl
/// patterns and returns the set of trait impls used.
#[must_use]
pub fn collect_trait_impls(
    resolver: &TraitResolver,
    body: &crate::model::VerifiableBody,
) -> Vec<TraitImpl> {
    let mut found: Vec<TraitImpl> = Vec::new();
    let mut seen_traits: FxHashSet<String> = FxHashSet::default();

    for block in &body.blocks {
        if let crate::model::Terminator::Call { func, .. } = &block.terminator {
            // Extract trait name from qualified method paths like "TraitName::method".
            if let Some((trait_part, _method_part)) = func.rsplit_once("::") {
                for imp in resolver.all_impls() {
                    if imp.trait_name.ends_with(trait_part) || trait_part.ends_with(&imp.trait_name)
                    {
                        let key = format!("{}::{:?}", imp.trait_name, imp.implementing_type);
                        if seen_traits.insert(key) {
                            found.push(imp.clone());
                        }
                    }
                }
            }
        }
    }

    found
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::SourceSpan;

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

    fn make_iterator_impl(ty: Ty, _item_ty: Ty) -> TraitImpl {
        TraitImpl {
            implementing_type: ty.clone(),
            trait_name: "std::iter::Iterator".to_string(),
            methods: vec![
                MethodImpl {
                    name: "next".to_string(),
                    body_def_path: format!("<{ty:?} as Iterator>::next"),
                    span: span(),
                },
                MethodImpl {
                    name: "size_hint".to_string(),
                    body_def_path: format!("<{ty:?} as Iterator>::size_hint"),
                    span: span(),
                },
            ],
            where_clauses: vec![],
            span: SourceSpan {
                file: "src/iter.rs".to_string(),
                line_start: 1,
                col_start: 1,
                line_end: 10,
                col_end: 1,
            },
        }
    }

    #[test]
    fn test_trait_bound_construction() {
        let bound = TraitBound {
            trait_name: "std::iter::Iterator".to_string(),
            type_params: vec![],
            associated_types: vec![AssociatedTypeBinding {
                name: "Item".to_string(),
                ty: Ty::u32(),
            }],
        };
        assert_eq!(bound.trait_name, "std::iter::Iterator");
        assert_eq!(bound.associated_types.len(), 1);
        assert_eq!(bound.associated_types[0].name, "Item");
    }

    #[test]
    fn test_resolver_add_and_lookup() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        resolver.add_impl(make_clone_impl(Ty::u32()));

        assert_eq!(resolver.all_impls().len(), 2);
        assert_eq!(resolver.impls_for_trait("std::clone::Clone").len(), 2);
        assert_eq!(resolver.impls_for_trait("std::fmt::Debug").len(), 0);
    }

    #[test]
    fn test_resolve_impl_exact_type_match() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        resolver.add_impl(make_clone_impl(Ty::u32()));

        let result = resolver.resolve_impl(&Ty::i32(), "std::clone::Clone");
        assert!(result.is_some());
        assert_eq!(result.unwrap().implementing_type, Ty::i32());

        let missing = resolver.resolve_impl(&Ty::Bool, "std::clone::Clone");
        assert!(missing.is_none());
    }

    #[test]
    fn test_resolve_method() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));

        let method = resolver.resolve_method(&Ty::i32(), "clone");
        assert!(method.is_some());
        let info = method.unwrap();
        assert_eq!(info.method_name, "clone");
        assert_eq!(info.containing_trait, Some("std::clone::Clone".to_string()));
        assert_eq!(info.impl_type, Ty::i32());

        let missing = resolver.resolve_method(&Ty::i32(), "nonexistent");
        assert!(missing.is_none());

        let wrong_type = resolver.resolve_method(&Ty::Bool, "clone");
        assert!(wrong_type.is_none());
    }

    #[test]
    fn test_build_vtable() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_iterator_impl(
            Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "VecIter".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, },
            Ty::u32(),
        ));
        resolver.add_impl(make_iterator_impl(
            Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "SliceIter".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, },
            Ty::u32(),
        ));

        let vtable = resolver.build_vtable("std::iter::Iterator");
        assert_eq!(vtable.trait_name, "std::iter::Iterator");
        assert_eq!(vtable.slots.len(), 2); // next, size_hint

        let next_slot = vtable.slots.iter().find(|s| s.method_name == "next").unwrap();
        assert_eq!(next_slot.targets.len(), 2);
    }

    #[test]
    fn test_devirtualize() {
        let mut resolver = TraitResolver::new();
        let vec_iter = Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "VecIter".to_string(), fields: vec![],
            disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, };
        let slice_iter = Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "SliceIter".to_string(), fields: vec![],
            disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, };
        resolver.add_impl(make_iterator_impl(vec_iter.clone(), Ty::u32()));
        resolver.add_impl(make_iterator_impl(slice_iter.clone(), Ty::u32()));

        let vtable = resolver.build_vtable("std::iter::Iterator");
        let targets = TraitResolver::devirtualize(&vtable, "next");
        assert_eq!(targets.len(), 2);

        let target_types: FxHashSet<String> =
            targets.iter().map(|t| format!("{:?}", t.impl_type)).collect();
        assert!(target_types.contains(&format!("{vec_iter:?}")));
        assert!(target_types.contains(&format!("{slice_iter:?}")));

        // Nonexistent method returns empty
        let empty = TraitResolver::devirtualize(&vtable, "nonexistent");
        assert!(empty.is_empty());
    }

    #[test]
    fn test_coherence_no_overlap() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        resolver.add_impl(make_clone_impl(Ty::u32()));

        let errors = resolver.check_coherence();
        assert!(errors.is_empty(), "distinct types should not overlap");
    }

    #[test]
    fn test_coherence_detects_overlap() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        // Duplicate impl for same type
        resolver.add_impl(make_clone_impl(Ty::i32()));

        let errors = resolver.check_coherence();
        assert_eq!(errors.len(), 1);
        match &errors[0] {
            CoherenceError::OverlappingImpls { trait_name, impl_a, impl_b, .. } => {
                assert_eq!(trait_name, "std::clone::Clone");
                assert_eq!(impl_a, &Ty::i32());
                assert_eq!(impl_b, &Ty::i32());
            }
            other => panic!("expected OverlappingImpls, got {other:?}"),
        }
    }

    #[test]
    fn test_coherence_error_description() {
        let err = CoherenceError::OverlappingImpls {
            trait_name: "Clone".to_string(),
            impl_a: Ty::i32(),
            impl_b: Ty::i32(),
            span_a: span(),
            span_b: span(),
        };
        let desc = err.description();
        assert!(desc.contains("overlapping impls"));
        assert!(desc.contains("Clone"));

        let orphan = CoherenceError::OrphanRule {
            trait_name: "Display".to_string(),
            implementing_type: Ty::Bool,
            span: span(),
        };
        assert!(orphan.description().contains("orphan rule"));
    }

    #[test]
    fn test_trait_constraint() {
        let constraint = TraitConstraint {
            type_param: "T".to_string(),
            bounds: vec![TraitBound {
                trait_name: "std::cmp::Ord".to_string(),
                type_params: vec![],
                associated_types: vec![],
            }],
            properties: vec!["a.cmp(b) is total ordering".to_string()],
        };
        assert_eq!(constraint.type_param, "T");
        assert_eq!(constraint.bounds.len(), 1);
        assert_eq!(constraint.properties.len(), 1);
    }

    #[test]
    fn test_collect_trait_impls_from_body() {
        use crate::model::*;

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
                    span: SourceSpan::default(),
                    atomic: None,
                },
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        };

        let found = collect_trait_impls(&resolver, &body);
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].trait_name, "std::clone::Clone");
    }

    #[test]
    fn test_serialization_roundtrip_rebuilds_trait_index() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        resolver.add_impl(make_iterator_impl(
            Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "MyIter".to_string(), fields: vec![],
                disc_index_safe: false,  faithful_enum_repr: None, enum_layout: None, },
            Ty::u32(),
        ));

        let json = serde_json::to_string(&resolver).expect("serialize");
        let deserialized: TraitResolver = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(deserialized.all_impls().len(), 2);
        assert_eq!(deserialized.impls_for_trait("std::clone::Clone").len(), 1);
        assert_eq!(deserialized.impls_for_trait("std::iter::Iterator").len(), 1);
    }

    #[test]
    fn test_vtable_serialization_roundtrip() {
        let vtable = VTable {
            trait_name: "Iterator".to_string(),
            slots: vec![VTableSlot {
                method_name: "next".to_string(),
                targets: vec![ConcreteTarget {
                    impl_type: Ty::i32(),
                    body_def_path: "<i32 as Iterator>::next".to_string(),
                }],
            }],
        };

        let json = serde_json::to_string(&vtable).expect("serialize");
        let roundtrip: VTable = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.trait_name, "Iterator");
        assert_eq!(roundtrip.slots.len(), 1);
        assert_eq!(roundtrip.slots[0].targets.len(), 1);
    }

    #[test]
    fn test_method_info_fields() {
        let info = MethodInfo {
            containing_trait: Some("Display".to_string()),
            impl_type: Ty::Bool,
            method_body_ref: "<bool as Display>::fmt".to_string(),
            method_name: "fmt".to_string(),
        };
        assert_eq!(info.method_name, "fmt");
        assert_eq!(info.containing_trait, Some("Display".to_string()));
    }

    #[test]
    fn test_multiple_traits_same_type() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        resolver.add_impl(TraitImpl {
            implementing_type: Ty::i32(),
            trait_name: "std::fmt::Debug".to_string(),
            methods: vec![MethodImpl {
                name: "fmt".to_string(),
                body_def_path: "<i32 as Debug>::fmt".to_string(),
                span: span(),
            }],
            where_clauses: vec![],
            span: span(),
        });

        // Can resolve methods from different traits on same type
        let clone = resolver.resolve_method(&Ty::i32(), "clone");
        assert!(clone.is_some());
        assert_eq!(clone.unwrap().containing_trait, Some("std::clone::Clone".to_string()));

        let fmt = resolver.resolve_method(&Ty::i32(), "fmt");
        assert!(fmt.is_some());
        assert_eq!(fmt.unwrap().containing_trait, Some("std::fmt::Debug".to_string()));

        // Coherence: no overlap (different traits)
        assert!(resolver.check_coherence().is_empty());
    }
}
