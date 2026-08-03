// trust_vcgen/vtable_model.rs: Trait object verification with vtable modeling
//
// Verifies dynamic dispatch through trait objects (dyn Trait) by modeling
// vtables and generating VCs for all possible implementations. Ensures that
// every known impl satisfies the trait contract when called through a trait
// object pointer.
//
// Components:
// - VtableModel: Maps trait to known implementations, generates dispatch VCs
// - DynDispatchVc: For each trait method call on dyn Trait, generate VCs for all impls
// - TraitBoundPropagation: Propagate trait bounds (Send, Sync, Clone) as proof obligations
// - ObjectSafetyChecker: Verify trait object safety rules statically
// - WitnessType: Generate witness types showing bounds are satisfiable
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    Formula, Sort, SourceSpan, TraitBound, TraitResolver, VTable, VcKind, VerificationCondition,
};

fn generated_vtable_symbol(unqualified: &str) -> String {
    crate::generated_formula_symbol("vtable", unqualified)
}

// ---------------------------------------------------------------------------
// Sealedness — the closed-world soundness premise
// ---------------------------------------------------------------------------

/// Whether the set of impls a `VtableModel` enumerates is exhaustive.
///
/// Dispatch reasoning that quantifies over "all known impls" is only sound
/// under a *closed-world* premise: that no impl exists outside the enumerated
/// set. For a trait a downstream crate can implement, that premise is false.
///
/// This is the single fact that separates a sound use of [`VtableModel`] from
/// an unsound one. Rather than leave it implicit (the bug that made the prior
/// model unsafe to wire into VC generation), every dispatch VC set carries the
/// premise as an explicit obligation via
/// [`VtableModel::closed_world_obligation`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraitSealedness {
    /// The enumerated impls are exhaustive: no downstream crate can add another
    /// impl that could be coerced to this trait object. True for sealed traits
    /// (private supertrait idiom), traits not exported from the crate, or
    /// whole-program analysis of a final binary. Closed-world reasoning is
    /// sound; the obligation is discharged.
    Sealed,
    /// Downstream crates may add impls not visible here. Closed-world reasoning
    /// over the enumerated impls is **unsound**; the obligation is undischarged
    /// and dispatch must fall back to the conservative default (havoc the
    /// result, assume nothing — what extraction does today for an indirect
    /// call). This is the conservative default.
    Open,
}

// ---------------------------------------------------------------------------
// VtableModel
// ---------------------------------------------------------------------------

/// Maps a trait to its known implementations and generates dispatch VCs.
///
/// The model maintains a registry of trait impls and can produce VCs
/// asserting that every known impl satisfies the trait's contract for
/// each method. This is the core data structure for trait object verification.
///
/// Dispatch VCs are only sound to use as proof evidence when the impl set is
/// closed; see [`TraitSealedness`]. The model defaults to
/// [`TraitSealedness::Open`] — the conservative assumption — so that wiring it
/// into VC generation cannot silently introduce an open-world unsoundness.
#[derive(Debug, Clone)]
pub struct VtableModel {
    /// Trait name this model covers.
    trait_name: String,
    /// Method contracts: method_name -> (preconditions, postconditions).
    method_contracts: FxHashMap<String, MethodContract>,
    /// Known implementing types with their VTable entries.
    vtable: VTable,
    /// Whether the enumerated impls are exhaustive (closed-world premise).
    sealedness: TraitSealedness,
}

/// Contract for a single trait method.
#[derive(Debug, Clone)]
pub struct MethodContract {
    /// Method name.
    pub method_name: String,
    /// Preconditions the trait promises callers can rely on.
    pub preconditions: Vec<Formula>,
    /// Postconditions the trait promises callers will hold after the call.
    pub postconditions: Vec<Formula>,
}

impl VtableModel {
    /// Create a new vtable model from a trait resolver.
    ///
    /// Builds the vtable for the given trait and initializes empty contracts.
    #[must_use]
    pub fn from_resolver(resolver: &TraitResolver, trait_name: &str) -> Self {
        let vtable = resolver.build_vtable(trait_name);
        let method_contracts = vtable
            .slots
            .iter()
            .map(|slot| {
                (
                    slot.method_name.clone(),
                    MethodContract {
                        method_name: slot.method_name.clone(),
                        preconditions: vec![],
                        postconditions: vec![],
                    },
                )
            })
            .collect();

        Self {
            trait_name: trait_name.to_string(),
            method_contracts,
            vtable,
            sealedness: TraitSealedness::Open,
        }
    }

    /// Create a vtable model directly from a vtable and contracts.
    #[must_use]
    pub fn new(trait_name: String, vtable: VTable, contracts: Vec<MethodContract>) -> Self {
        let method_contracts = contracts.into_iter().map(|c| (c.method_name.clone(), c)).collect();
        Self { trait_name, method_contracts, vtable, sealedness: TraitSealedness::Open }
    }

    /// Builder: declare whether the enumerated impls are exhaustive.
    ///
    /// Defaults to [`TraitSealedness::Open`]. Only set [`TraitSealedness::Sealed`]
    /// when the caller has *established* exhaustiveness (sealed-trait idiom,
    /// non-exported trait, or whole-program analysis) — doing so discharges the
    /// closed-world obligation, so an incorrect claim here is an unsoundness.
    #[must_use]
    pub fn with_sealedness(mut self, sealedness: TraitSealedness) -> Self {
        self.sealedness = sealedness;
        self
    }

    /// Declare whether the enumerated impls are exhaustive. See
    /// [`VtableModel::with_sealedness`].
    pub fn set_sealedness(&mut self, sealedness: TraitSealedness) {
        self.sealedness = sealedness;
    }

    /// Whether the enumerated impls are treated as exhaustive.
    #[must_use]
    pub fn sealedness(&self) -> TraitSealedness {
        self.sealedness
    }

    /// Set the contract for a specific method.
    pub fn set_contract(&mut self, contract: MethodContract) {
        self.method_contracts.insert(contract.method_name.clone(), contract);
    }

    /// Get the trait name.
    #[must_use]
    pub fn trait_name(&self) -> &str {
        &self.trait_name
    }

    /// Get the vtable.
    #[must_use]
    pub fn vtable(&self) -> &VTable {
        &self.vtable
    }

    /// Number of known implementing types.
    #[must_use]
    pub fn impl_count(&self) -> usize {
        let mut types: FxHashSet<String> = FxHashSet::default();
        for slot in &self.vtable.slots {
            for target in &slot.targets {
                types.insert(format!("{:?}", target.impl_type));
            }
        }
        types.len()
    }

    /// Number of method slots in the vtable.
    #[must_use]
    pub fn method_count(&self) -> usize {
        self.vtable.slots.len()
    }

    /// The closed-world obligation for this trait's dispatch reasoning.
    ///
    /// Per-impl dispatch VCs only let a caller rely on a `dyn` callee's contract
    /// if the enumerated impls are exhaustive. This VC makes that premise
    /// explicit so it is verified rather than assumed:
    ///
    /// - [`TraitSealedness::Sealed`] → `Formula::Bool(false)`: no violation
    ///   exists because exhaustiveness was established by the caller.
    /// - [`TraitSealedness::Open`] → `Formula::Bool(true)`: the premise is
    ///   undischarged. A downstream crate can add an impl, so relying on the
    ///   enumerated impls is unsound; the obligation fails and dispatch must
    ///   fall back to the conservative default (havoc the result).
    ///
    /// Emitting this on every dispatch site is what makes [`VtableModel`] safe
    /// to wire into VC generation: an open trait can never silently "prove"
    /// caller-side reliance on a closed set of impls.
    #[must_use]
    pub fn closed_world_obligation(&self, function_name: &str) -> VerificationCondition {
        let impl_names: Vec<String> = self
            .vtable
            .slots
            .iter()
            .flat_map(|s| &s.targets)
            .map(|t| format!("{:?}", t.impl_type))
            .collect();
        let (formula, message) = match self.sealedness {
            TraitSealedness::Sealed => (
                Formula::Bool(false),
                format!(
                    "dyn {}: closed-world premise discharged — impl set is sealed/exhaustive [{}]",
                    self.trait_name,
                    impl_names.join(", ")
                ),
            ),
            TraitSealedness::Open => (
                Formula::Bool(true),
                format!(
                    "dyn {}: closed-world premise UNDISCHARGED — trait is open, downstream crates may add impls beyond [{}]; \
                     caller-side reliance on enumerated impls is unsound (fall back to havoc)",
                    self.trait_name,
                    impl_names.join(", ")
                ),
            ),
        };
        VerificationCondition {
            kind: VcKind::Assertion { message },
            function: function_name.into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// Generate VCs for all methods across all known implementations.
    ///
    /// For each method with a contract and each known impl, produces VCs
    /// checking that the impl satisfies the trait contract (Liskov-style).
    /// When the vtable has any method slot, the set is prefixed with the
    /// [`closed_world_obligation`](Self::closed_world_obligation): the per-impl
    /// VCs are sound to *rely on* only if that obligation discharges.
    #[must_use]
    pub fn generate_dispatch_vcs(&self, function_name: &str) -> Vec<VerificationCondition> {
        let mut vcs = Vec::new();
        if !self.vtable.slots.is_empty() {
            vcs.push(self.closed_world_obligation(function_name));
        }
        for slot in &self.vtable.slots {
            if let Some(contract) = self.method_contracts.get(&slot.method_name) {
                let dispatch = DynDispatchVc::new(
                    &self.trait_name,
                    &slot.method_name,
                    contract,
                    &slot.targets,
                );
                vcs.extend(dispatch.generate_vcs(function_name));
            }
        }
        vcs
    }

    /// Build a modular-verification summary for a `dyn` call to one of this
    /// trait's methods.
    ///
    /// A `dyn Trait` method call already extracts as a `Terminator::Call` whose
    /// callee is the trait-method path; inserting the returned summary under
    /// that name into a [`SummaryDatabase`](crate::modular::SummaryDatabase)
    /// lets the caller emit direct precondition VCs. Postconditions remain
    /// recorded contract data only until precise call-site return binding,
    /// dominance, and artifact-backed dispatch proof evidence are implemented.
    ///
    /// Returns `Some` only when sealed dispatch evidence is available:
    /// 1. the impl set is [`TraitSealedness::Sealed`] (closed world: no
    ///    downstream crate can add an impl that violates the contract — the
    ///    premise [`closed_world_obligation`](Self::closed_world_obligation)
    ///    makes explicit);
    /// 2. `all_impls_verified` is `true` — every enumerated impl was proved to
    ///    satisfy the contract (precondition contravariance + postcondition
    ///    covariance, the obligations [`generate_dispatch_vcs`] emits); and
    /// 3. the method has at least one contract condition to carry.
    ///
    /// Otherwise returns `None`, so the caller falls back to the conservative
    /// default. An open trait, or one whose impls were not all verified, never
    /// yields a proved summary. The summary's `proved` flag is only a modular
    /// precondition-checking marker; it is not enough to export postconditions
    /// into [`crate::specdb::SpecDatabase`] without artifact-backed proof
    /// evidence.
    ///
    /// `callee_name` must match the call's callee key as it appears in extracted
    /// MIR (the trait-method def path) so [`crate::modular`] can find it.
    ///
    /// [`generate_dispatch_vcs`]: Self::generate_dispatch_vcs
    #[must_use]
    pub fn dyn_dispatch_summary(
        &self,
        method_name: &str,
        callee_name: impl Into<String>,
        all_impls_verified: bool,
    ) -> Option<crate::modular::FunctionSummary> {
        // Closed-world premise is necessary regardless of how many *known* impls
        // were verified: an open trait admits a future downstream impl that need
        // not satisfy the contract.
        if self.sealedness != TraitSealedness::Sealed || !all_impls_verified {
            return None;
        }
        let contract = self.method_contracts.get(method_name)?;
        if contract.preconditions.is_empty() && contract.postconditions.is_empty() {
            return None;
        }
        let mut summary = crate::modular::FunctionSummary::new(callee_name).proved();
        summary.preconditions = contract.preconditions.clone();
        summary.postconditions = contract.postconditions.clone();
        Some(summary)
    }
}

// ---------------------------------------------------------------------------
// DynDispatchVc
// ---------------------------------------------------------------------------

/// Generates VCs for a single trait method call through dynamic dispatch.
///
/// For a call `obj.method()` where `obj: dyn Trait`, this generates one VC
/// per known impl type, asserting that the impl's behavior satisfies the
/// trait contract. The formula is a disjunction over all possible dispatch
/// targets, with each branch requiring the impl to satisfy the postcondition
/// given the precondition holds.
pub struct DynDispatchVc<'a> {
    trait_name: &'a str,
    method_name: &'a str,
    contract: &'a MethodContract,
    targets: &'a [trust_types::ConcreteTarget],
}

impl<'a> DynDispatchVc<'a> {
    /// Create a new dynamic dispatch VC generator.
    #[must_use]
    pub fn new(
        trait_name: &'a str,
        method_name: &'a str,
        contract: &'a MethodContract,
        targets: &'a [trust_types::ConcreteTarget],
    ) -> Self {
        Self { trait_name, method_name, contract, targets }
    }

    /// Generate VCs for this dispatch site.
    ///
    /// Produces:
    /// 1. One VC per impl checking precondition contravariance
    /// 2. One VC per impl checking postcondition covariance
    /// 3. A dispatch completeness VC asserting at least one impl exists
    #[must_use]
    pub fn generate_vcs(&self, function_name: &str) -> Vec<VerificationCondition> {
        let mut vcs = Vec::new();
        let location = SourceSpan::default();

        if self.targets.is_empty() {
            // No known impls: generate an assertion failure VC.
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "no known implementations for dyn {}::{}",
                        self.trait_name, self.method_name
                    ),
                },
                function: function_name.into(),
                location,
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            });
            return vcs;
        }

        let pre_conj = conjunction(&self.contract.preconditions);
        let post_conj = conjunction(&self.contract.postconditions);

        // For each known impl, generate VCs ensuring the dispatch is sound
        for target in self.targets {
            let impl_ty_name = format!("{:?}", target.impl_type);

            // Precondition VC: trait precondition must be accepted by each impl
            // Formula: NOT(pre_trait => pre_impl) -- if SAT, impl rejects valid input
            if !self.contract.preconditions.is_empty() {
                let impl_pre_var = Formula::Var(
                    generated_vtable_symbol(&format!(
                        "impl_pre_{}_{}",
                        impl_ty_name, self.method_name
                    )),
                    Sort::Bool,
                );
                let implication =
                    Formula::Implies(Box::new(pre_conj.clone()), Box::new(impl_pre_var));
                vcs.push(VerificationCondition {
                    kind: VcKind::Precondition {
                        callee: format!(
                            "<{} as {}>::{}",
                            impl_ty_name, self.trait_name, self.method_name
                        ),
                    },
                    function: function_name.into(),
                    location: location.clone(),
                    formula: Formula::Not(Box::new(implication)),
                    contract_metadata: None,
                    obligation: None,
                });
            }

            // Postcondition VC: each impl must guarantee at least what the trait promises
            // Formula: NOT(post_impl => post_trait) -- if SAT, impl fails to deliver
            if !self.contract.postconditions.is_empty() {
                let impl_post_var = Formula::Var(
                    generated_vtable_symbol(&format!(
                        "impl_post_{}_{}",
                        impl_ty_name, self.method_name
                    )),
                    Sort::Bool,
                );
                let implication =
                    Formula::Implies(Box::new(impl_post_var), Box::new(post_conj.clone()));
                vcs.push(VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: format!(
                        "<{} as {}>::{}",
                        impl_ty_name, self.trait_name, self.method_name
                    )
                    .into(),
                    location: location.clone(),
                    formula: Formula::Not(Box::new(implication)),
                    contract_metadata: None,
                    obligation: None,
                });
            }
        }

        // Dispatch completeness: a finite enumerated target set is not a
        // violation by itself. Open-world unsoundness is represented by the
        // separate closed-world obligation.
        if self.targets.len() > 1 {
            let target_names: Vec<String> =
                self.targets.iter().map(|t| format!("{:?}", t.impl_type)).collect();
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "dyn {}::{} dispatches to {} impls: [{}]",
                        self.trait_name,
                        self.method_name,
                        self.targets.len(),
                        target_names.join(", ")
                    ),
                },
                function: function_name.into(),
                location,
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            });
        }

        vcs
    }
}

// ---------------------------------------------------------------------------
// TraitBoundPropagation
// ---------------------------------------------------------------------------

/// Propagates trait bounds (Send, Sync, Clone, etc.) as proof obligations.
///
/// When a type is required to implement certain marker traits (via where
/// clauses or trait object bounds), this generates VCs ensuring those
/// bounds are satisfied by all known implementations.
#[derive(Debug, Clone)]
pub struct TraitBoundPropagation {
    /// The type parameter or concrete type being checked.
    type_name: String,
    /// Required trait bounds.
    bounds: Vec<TraitBound>,
}

/// A single bound propagation result.
#[derive(Debug, Clone)]
pub struct BoundCheckResult {
    /// The bound being checked.
    pub bound: TraitBound,
    /// Whether the bound is satisfied.
    pub satisfied: bool,
    /// Explanation of why or why not.
    pub reason: String,
}

impl TraitBoundPropagation {
    /// Create a new bound propagation checker.
    #[must_use]
    pub fn new(type_name: impl Into<String>, bounds: Vec<TraitBound>) -> Self {
        Self { type_name: type_name.into(), bounds }
    }

    /// Check which bounds are satisfied by known impls.
    #[must_use]
    pub fn check_bounds(
        &self,
        resolver: &TraitResolver,
        concrete_ty: &trust_types::Ty,
    ) -> Vec<BoundCheckResult> {
        self.bounds
            .iter()
            .map(|bound| {
                let satisfied = resolver.resolve_impl(concrete_ty, &bound.trait_name).is_some();
                BoundCheckResult {
                    bound: bound.clone(),
                    satisfied,
                    reason: if satisfied {
                        format!("{:?} implements {}", concrete_ty, bound.trait_name)
                    } else {
                        format!("{:?} does not implement {}", concrete_ty, bound.trait_name)
                    },
                }
            })
            .collect()
    }

    /// Generate VCs for unsatisfied bounds.
    ///
    /// Each unsatisfied bound produces an assertion VC with formula `true`
    /// (a satisfiable violation), indicating the bound cannot be proven.
    #[must_use]
    pub fn generate_bound_vcs(
        &self,
        resolver: &TraitResolver,
        concrete_ty: &trust_types::Ty,
        function_name: &str,
    ) -> Vec<VerificationCondition> {
        let results = self.check_bounds(resolver, concrete_ty);
        results
            .into_iter()
            .filter(|r| !r.satisfied)
            .map(|r| VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "trait bound `{}: {}` not satisfied: {}",
                        self.type_name, r.bound.trait_name, r.reason
                    ),
                },
                function: function_name.into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            })
            .collect()
    }

    /// Generate VCs for all bounds across multiple concrete types.
    ///
    /// Used when verifying that all known impls of a trait object satisfy
    /// additional marker trait bounds (e.g., `dyn Trait + Send`).
    #[must_use]
    pub fn generate_multi_type_vcs(
        &self,
        resolver: &TraitResolver,
        concrete_types: &[trust_types::Ty],
        function_name: &str,
    ) -> Vec<VerificationCondition> {
        concrete_types
            .iter()
            .flat_map(|ty| self.generate_bound_vcs(resolver, ty, function_name))
            .collect()
    }
}

// ---------------------------------------------------------------------------
// ObjectSafetyChecker
// ---------------------------------------------------------------------------

/// Verifies trait object safety rules statically.
///
/// A trait is object-safe if:
/// 1. It has no associated constants
/// 2. It has no GATs (generic associated types) used in method signatures
/// 3. All methods are dispatchable:
///    a. No `Self: Sized` bound on the method
///    b. Method does not use `Self` in return position
///    c. Method has a receiver (self, &self, &mut self, etc.)
///    d. Method has no type parameters
#[derive(Debug, Clone)]
pub struct ObjectSafetyChecker {
    /// Trait name being checked.
    trait_name: String,
    /// Method signatures for the trait.
    methods: Vec<ObjectSafetyMethod>,
    /// Whether the trait has `Self: Sized` as a supertrait.
    has_sized_supertrait: bool,
}

/// Method information relevant to object safety checking.
#[derive(Debug, Clone)]
pub struct ObjectSafetyMethod {
    /// Method name.
    pub name: String,
    /// Whether the method has a receiver (self, &self, &mut self, etc.).
    pub has_receiver: bool,
    /// Whether the method returns Self.
    pub returns_self: bool,
    /// Whether the method has generic type parameters.
    pub has_type_params: bool,
    /// Whether the method has a `Self: Sized` where clause.
    pub where_self_sized: bool,
}

/// Reason why a trait is not object-safe.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ObjectSafetyViolation {
    /// Trait requires Self: Sized.
    SizedSupertrait,
    /// Method has no receiver (not dispatchable).
    NoReceiver { method: String },
    /// Method returns Self (cannot determine size through vtable).
    ReturnsSelf { method: String },
    /// Method has generic type parameters (cannot be dispatched).
    GenericMethod { method: String },
}

impl ObjectSafetyViolation {
    /// Human-readable description of the violation.
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            Self::SizedSupertrait => {
                "trait has `Self: Sized` supertrait, cannot be made into object".to_string()
            }
            Self::NoReceiver { method } => {
                format!("method `{method}` has no receiver (self)")
            }
            Self::ReturnsSelf { method } => {
                format!("method `{method}` returns Self")
            }
            Self::GenericMethod { method } => {
                format!("method `{method}` has generic type parameters")
            }
        }
    }
}

impl ObjectSafetyChecker {
    /// Create a new checker for the given trait.
    #[must_use]
    pub fn new(
        trait_name: impl Into<String>,
        methods: Vec<ObjectSafetyMethod>,
        has_sized_supertrait: bool,
    ) -> Self {
        Self { trait_name: trait_name.into(), methods, has_sized_supertrait }
    }

    /// Check whether the trait is object-safe.
    ///
    /// Returns an empty list if safe, or the list of violations.
    #[must_use]
    pub fn check(&self) -> Vec<ObjectSafetyViolation> {
        let mut violations = Vec::new();

        if self.has_sized_supertrait {
            violations.push(ObjectSafetyViolation::SizedSupertrait);
        }

        for method in &self.methods {
            // Methods with where Self: Sized are excluded from vtable dispatch
            // and thus don't affect object safety.
            if method.where_self_sized {
                continue;
            }

            if !method.has_receiver {
                violations.push(ObjectSafetyViolation::NoReceiver { method: method.name.clone() });
            }

            if method.returns_self {
                violations.push(ObjectSafetyViolation::ReturnsSelf { method: method.name.clone() });
            }

            if method.has_type_params {
                violations
                    .push(ObjectSafetyViolation::GenericMethod { method: method.name.clone() });
            }
        }

        violations
    }

    /// Whether the trait is object-safe.
    #[must_use]
    pub fn is_object_safe(&self) -> bool {
        self.check().is_empty()
    }

    /// Generate VCs for object safety violations.
    ///
    /// Each violation produces an assertion VC with formula `true`.
    #[must_use]
    pub fn generate_vcs(&self, function_name: &str) -> Vec<VerificationCondition> {
        self.check()
            .into_iter()
            .map(|violation| VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "object safety violation in trait `{}`: {}",
                        self.trait_name,
                        violation.description()
                    ),
                },
                function: function_name.into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// WitnessType
// ---------------------------------------------------------------------------

/// Generates witness types showing that trait bounds are satisfiable.
///
/// Given a set of required trait bounds, a witness type demonstrates that
/// at least one concrete type satisfies all the bounds. This is used to
/// prove that generic constraints are not vacuously true (i.e., the
/// set of satisfying types is non-empty).
#[derive(Debug, Clone)]
pub struct WitnessType {
    /// Type parameter being witnessed.
    pub type_param: String,
    /// Required bounds.
    pub bounds: Vec<TraitBound>,
    /// The witness: a concrete type that satisfies all bounds.
    pub witness: Option<trust_types::Ty>,
}

impl WitnessType {
    /// Search for a witness type among known impls.
    ///
    /// Returns a `WitnessType` with `witness = Some(ty)` if a satisfying
    /// type is found, or `witness = None` if no type satisfies all bounds.
    #[must_use]
    pub fn find_witness(
        type_param: impl Into<String>,
        bounds: &[TraitBound],
        resolver: &TraitResolver,
    ) -> Self {
        let type_param = type_param.into();

        // Collect all concrete types known to implement at least one required trait.
        let mut candidate_types: FxHashSet<String> = FxHashSet::default();
        let mut type_map: FxHashMap<String, trust_types::Ty> = FxHashMap::default();

        for bound in bounds {
            for imp in resolver.impls_for_trait(&bound.trait_name) {
                let key = format!("{:?}", imp.implementing_type);
                candidate_types.insert(key.clone());
                type_map.insert(key, imp.implementing_type.clone());
            }
        }

        // Find a type that satisfies ALL bounds.
        let witness = candidate_types.iter().find_map(|type_key| {
            let ty = &type_map[type_key];
            let all_satisfied =
                bounds.iter().all(|bound| resolver.resolve_impl(ty, &bound.trait_name).is_some());
            if all_satisfied { Some(ty.clone()) } else { None }
        });

        Self { type_param, bounds: bounds.to_vec(), witness }
    }

    /// Whether a witness was found.
    #[must_use]
    pub fn is_satisfiable(&self) -> bool {
        self.witness.is_some()
    }

    /// Generate a VC asserting the bounds are satisfiable.
    ///
    /// If no witness exists, produces an assertion failure.
    /// If a witness exists, produces a passing assertion.
    #[must_use]
    pub fn generate_vc(&self, function_name: &str) -> VerificationCondition {
        let bound_names: Vec<&str> = self.bounds.iter().map(|b| b.trait_name.as_str()).collect();
        let bound_desc = bound_names.join(" + ");

        match &self.witness {
            Some(witness_ty) => VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "witness for `{}: {}` found: {:?}",
                        self.type_param, bound_desc, witness_ty
                    ),
                },
                function: function_name.into(),
                location: SourceSpan::default(),
                // Witness found: no violation exists.
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            None => VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "no witness for `{}: {}` -- bounds may be unsatisfiable",
                        self.type_param, bound_desc
                    ),
                },
                function: function_name.into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a conjunction of formulas. Returns `true` for empty input.
fn conjunction(formulas: &[Formula]) -> Formula {
    match formulas.len() {
        0 => Formula::Bool(true),
        1 => formulas[0].clone(),
        _ => Formula::And(formulas.to_vec()),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use trust_types::{ConcreteTarget, MethodImpl, SourceSpan, TraitImpl, Ty, VTableSlot};

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn make_trait_bound(name: &str) -> TraitBound {
        TraitBound { trait_name: name.to_string(), type_params: vec![], associated_types: vec![] }
    }

    fn x_gt_0() -> Formula {
        Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)))
    }

    fn result_ge_0() -> Formula {
        Formula::Ge(Box::new(Formula::Var("result".into(), Sort::Int)), Box::new(Formula::Int(0)))
    }

    fn make_compute_impl(ty: Ty) -> TraitImpl {
        TraitImpl {
            implementing_type: ty.clone(),
            trait_name: "Compute".to_string(),
            methods: vec![MethodImpl {
                name: "compute".to_string(),
                body_def_path: format!("<{ty:?} as Compute>::compute"),
                span: span(),
            }],
            where_clauses: vec![],
            span: span(),
        }
    }

    fn make_clone_impl(ty: Ty) -> TraitImpl {
        TraitImpl {
            implementing_type: ty.clone(),
            trait_name: "Clone".to_string(),
            methods: vec![MethodImpl {
                name: "clone".to_string(),
                body_def_path: format!("<{ty:?} as Clone>::clone"),
                span: span(),
            }],
            where_clauses: vec![],
            span: span(),
        }
    }

    fn make_send_impl(ty: Ty) -> TraitImpl {
        TraitImpl {
            implementing_type: ty.clone(),
            trait_name: "Send".to_string(),
            methods: vec![],
            where_clauses: vec![],
            span: span(),
        }
    }

    fn setup_resolver_with_compute() -> TraitResolver {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_compute_impl(Ty::i32()));
        resolver.add_impl(make_compute_impl(Ty::u32()));
        resolver
    }

    // --- VtableModel tests ---

    #[test]
    fn test_vtable_model_from_resolver() {
        let resolver = setup_resolver_with_compute();
        let model = VtableModel::from_resolver(&resolver, "Compute");

        assert_eq!(model.trait_name(), "Compute");
        assert_eq!(model.method_count(), 1);
        assert_eq!(model.impl_count(), 2);
    }

    #[test]
    fn test_vtable_model_empty_trait() {
        let resolver = TraitResolver::new();
        let model = VtableModel::from_resolver(&resolver, "Empty");

        assert_eq!(model.trait_name(), "Empty");
        assert_eq!(model.method_count(), 0);
        assert_eq!(model.impl_count(), 0);
    }

    #[test]
    fn test_vtable_model_with_contracts() {
        let resolver = setup_resolver_with_compute();
        let mut model = VtableModel::from_resolver(&resolver, "Compute");

        model.set_contract(MethodContract {
            method_name: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        });

        let vcs = model.generate_dispatch_vcs("test_fn");

        // 1 closed-world obligation + 2 impls * (1 pre + 1 post) + 1 completeness = 6 VCs
        assert_eq!(vcs.len(), 6);

        let pre_count =
            vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::Precondition { .. })).count();
        let post_count = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).count();
        assert_eq!(pre_count, 2);
        assert_eq!(post_count, 2);

        // The first VC is the closed-world obligation; default sealedness is
        // Open, so the premise is a satisfiable violation (Bool(true)).
        assert!(
            matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("closed-world premise UNDISCHARGED"))
        );
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    #[test]
    fn test_vtable_model_no_contracts_no_vcs() {
        let resolver = setup_resolver_with_compute();
        let model = VtableModel::from_resolver(&resolver, "Compute");

        // No contracts set, so dispatch VCs should still be generated
        // but only completeness VCs (no pre/post to check)
        let vcs = model.generate_dispatch_vcs("test_fn");
        // 1 closed-world obligation + 1 completeness (2 impls, 1 method) = 2
        assert_eq!(vcs.len(), 2);
        assert!(
            matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("closed-world premise"))
        );
    }

    #[test]
    fn test_vtable_model_new_direct() {
        let vtable = VTable {
            trait_name: "MyTrait".to_string(),
            slots: vec![VTableSlot {
                method_name: "do_thing".to_string(),
                targets: vec![ConcreteTarget {
                    impl_type: Ty::i32(),
                    body_def_path: "<i32>::do_thing".to_string(),
                }],
            }],
        };

        let contracts = vec![MethodContract {
            method_name: "do_thing".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![],
        }];

        let model = VtableModel::new("MyTrait".to_string(), vtable, contracts);
        assert_eq!(model.method_count(), 1);
        assert_eq!(model.impl_count(), 1);

        let vcs = model.generate_dispatch_vcs("test_fn");
        // 1 closed-world obligation + 1 impl precondition (no completeness, single impl) = 2
        assert_eq!(vcs.len(), 2);
        assert!(
            matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("closed-world premise"))
        );
        assert!(matches!(&vcs[1].kind, VcKind::Precondition { .. }));
    }

    // --- Closed-world / sealedness obligation tests ---

    #[test]
    fn test_default_sealedness_is_open() {
        let resolver = setup_resolver_with_compute();
        let model = VtableModel::from_resolver(&resolver, "Compute");
        // Conservative default: an unannotated trait is treated as open so
        // wiring this model in cannot silently assume a closed world.
        assert_eq!(model.sealedness(), TraitSealedness::Open);
    }

    #[test]
    fn test_open_trait_obligation_is_undischarged() {
        let resolver = setup_resolver_with_compute();
        let model = VtableModel::from_resolver(&resolver, "Compute");

        let ob = model.closed_world_obligation("test_fn");
        // Open trait: the closed-world premise is a satisfiable violation.
        assert_eq!(ob.formula, Formula::Bool(true));
        assert!(
            matches!(&ob.kind, VcKind::Assertion { message } if message.contains("UNDISCHARGED"))
        );
    }

    #[test]
    fn test_sealed_trait_obligation_is_discharged() {
        let resolver = setup_resolver_with_compute();
        let model = VtableModel::from_resolver(&resolver, "Compute")
            .with_sealedness(TraitSealedness::Sealed);

        assert_eq!(model.sealedness(), TraitSealedness::Sealed);
        let ob = model.closed_world_obligation("test_fn");
        // Sealed trait: premise established, so no violation exists.
        assert_eq!(ob.formula, Formula::Bool(false));
        assert!(
            matches!(&ob.kind, VcKind::Assertion { message } if message.contains("discharged"))
        );
    }

    #[test]
    fn test_dispatch_vcs_prefixed_with_obligation() {
        let resolver = setup_resolver_with_compute();
        let mut model = VtableModel::from_resolver(&resolver, "Compute");
        model.set_contract(MethodContract {
            method_name: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        });

        // Sealing the trait flips only the obligation's formula, not the VC count:
        // the obligation is always present so the premise is never implicit.
        let open_vcs = model.generate_dispatch_vcs("test_fn");
        model.set_sealedness(TraitSealedness::Sealed);
        let sealed_vcs = model.generate_dispatch_vcs("test_fn");

        assert_eq!(open_vcs.len(), sealed_vcs.len());
        assert_eq!(open_vcs[0].formula, Formula::Bool(true));
        assert_eq!(sealed_vcs[0].formula, Formula::Bool(false));
    }

    // --- dyn_dispatch_summary: sound closed-world bridge to modular verification ---

    fn sealed_compute_model_with_post() -> VtableModel {
        let resolver = setup_resolver_with_compute();
        let mut model = VtableModel::from_resolver(&resolver, "Compute")
            .with_sealedness(TraitSealedness::Sealed);
        model.set_contract(MethodContract {
            method_name: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        });
        model
    }

    /// Minimal caller whose only call is a `dyn` dispatch to `Compute::compute`.
    fn caller_with_dyn_call() -> trust_types::VerifiableFunction {
        use trust_types::{
            BasicBlock, BlockId, LocalDecl, Place, Terminator, VerifiableBody, VerifiableFunction,
        };
        VerifiableFunction {
            name: "use_compute".to_string(),
            def_path: "test::use_compute".to_string(),
            span: span(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("r".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "Compute::compute".to_string(),
                            args: vec![],
                            dest: Place::local(1),
                            target: Some(BlockId(1)),
                            span: span(),
                            atomic: None,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_dyn_summary_sealed_and_verified_is_proved() {
        let model = sealed_compute_model_with_post();
        let summary =
            model.dyn_dispatch_summary("compute", "Compute::compute", true).expect("summary");
        assert!(summary.proved);
        assert_eq!(summary.name, "Compute::compute");
        assert_eq!(summary.postconditions, vec![result_ge_0()]);
        assert_eq!(summary.preconditions, vec![x_gt_0()]);
        assert!(summary.proof_evidence_id.is_none());
        assert!(summary.proof_strength.is_none());
    }

    #[test]
    fn test_dyn_summary_open_trait_is_none() {
        // Open world: a downstream impl could violate the contract, so even with
        // every *known* impl verified the postcondition is unsound to assume.
        let resolver = setup_resolver_with_compute();
        let mut model = VtableModel::from_resolver(&resolver, "Compute"); // default Open
        model.set_contract(MethodContract {
            method_name: "compute".to_string(),
            preconditions: vec![],
            postconditions: vec![result_ge_0()],
        });
        assert!(model.dyn_dispatch_summary("compute", "Compute::compute", true).is_none());
    }

    #[test]
    fn test_dyn_summary_unverified_impls_is_none() {
        // Sealed, but the impls were not (yet) proved to satisfy the contract.
        let model = sealed_compute_model_with_post();
        assert!(model.dyn_dispatch_summary("compute", "Compute::compute", false).is_none());
    }

    #[test]
    fn test_dyn_summary_precondition_only_is_proved() {
        let resolver = setup_resolver_with_compute();
        let mut model = VtableModel::from_resolver(&resolver, "Compute")
            .with_sealedness(TraitSealedness::Sealed);
        model.set_contract(MethodContract {
            method_name: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![],
        });
        let summary =
            model.dyn_dispatch_summary("compute", "Compute::compute", true).expect("summary");
        assert!(summary.proved);
        assert_eq!(summary.preconditions, vec![x_gt_0()]);
        assert!(summary.postconditions.is_empty());
    }

    #[test]
    fn test_dyn_summary_unknown_method_is_none() {
        let model = sealed_compute_model_with_post();
        assert!(model.dyn_dispatch_summary("nonexistent", "Compute::nonexistent", true).is_none());
    }

    #[test]
    fn test_modular_records_but_does_not_assume_sealed_dyn_postcondition() {
        // End-to-end: a sealed+verified trait method carries contract data for
        // modular precondition checks, but does not turn postconditions into
        // reusable facts without artifact-backed proof evidence.
        use crate::modular::{SummaryDatabase, modular_vcgen};

        let model = sealed_compute_model_with_post();
        let summary =
            model.dyn_dispatch_summary("compute", "Compute::compute", true).expect("summary");
        let mut db = SummaryDatabase::new();
        db.insert(summary);

        let mut spec_db = crate::specdb::SpecDatabase::new();
        db.sync_to_spec_db(&mut spec_db);
        assert_eq!(spec_db.len(), 0);

        let result = modular_vcgen(&caller_with_dyn_call(), &db);
        assert_eq!(result.assumptions_injected, 0);
        assert_eq!(result.havoced_calls, 1);
    }

    #[test]
    fn test_discharge_path_does_not_assume_sealed_dyn_postcondition() {
        // The live compiler path uses `generate_vcs_with_discharge_and_summaries`,
        // not `modular_vcgen`. Verify it preserves the discharge contract:
        // summary postconditions do not globally rewrite solver VCs.
        use crate::modular::SummaryDatabase;

        let caller = caller_with_dyn_call();

        // Empty DB: identical to the plain discharge function (VerificationCondition
        // has no PartialEq, so compare counts and per-VC formulas).
        let (plain_solver, plain_discharged) = crate::generate_vcs_with_discharge(&caller);
        let (empty_solver, empty_discharged) =
            crate::generate_vcs_with_discharge_and_summaries(&caller, &SummaryDatabase::new());
        assert_eq!(plain_solver.len(), empty_solver.len(), "empty summaries must not add/drop VCs");
        assert_eq!(plain_discharged.len(), empty_discharged.len());
        for (a, b) in plain_solver.iter().zip(empty_solver.iter()) {
            assert_eq!(a.formula, b.formula, "empty summaries must not rewrite VC formulas");
        }

        // Proved sealed summary: body VCs remain identical to the plain path.
        let summary = sealed_compute_model_with_post()
            .dyn_dispatch_summary("compute", "Compute::compute", true)
            .expect("summary");
        let mut db = SummaryDatabase::new();
        db.insert(summary);
        let (solver_vcs, discharged) =
            crate::generate_vcs_with_discharge_and_summaries(&caller, &db);
        assert_eq!(plain_discharged.len(), discharged.len());
        let summary_body_vcs: Vec<_> = solver_vcs
            .iter()
            .filter(|vc| !matches!(vc.kind, VcKind::Precondition { .. }))
            .collect();
        let precondition_vcs: Vec<_> =
            solver_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).collect();
        assert_eq!(precondition_vcs.len(), 1, "dyn summary precondition should be enforced");
        assert_eq!(plain_solver.len(), summary_body_vcs.len());
        for (plain, vc) in plain_solver.iter().zip(summary_body_vcs.iter()) {
            assert_eq!(plain.formula, vc.formula);
            assert!(
                !matches!(&vc.formula, Formula::Implies(premise, _) if **premise == result_ge_0()),
                "solver VCs must not assume the sealed dyn callee's postcondition"
            );
        }
    }

    #[test]
    fn test_modular_havocs_open_dyn_call() {
        // Safety net: an open trait yields no proved summary, so the dyn call is
        // havoced (today's sound-but-incomplete default). The closed-world
        // assumption is never made without sealedness.
        use crate::modular::{SummaryDatabase, modular_vcgen};

        let resolver = setup_resolver_with_compute();
        let mut model = VtableModel::from_resolver(&resolver, "Compute"); // Open
        model.set_contract(MethodContract {
            method_name: "compute".to_string(),
            preconditions: vec![],
            postconditions: vec![result_ge_0()],
        });
        assert!(model.dyn_dispatch_summary("compute", "Compute::compute", true).is_none());

        // With no summary in the DB the dyn call is havoced.
        let result = modular_vcgen(&caller_with_dyn_call(), &SummaryDatabase::new());
        assert_eq!(result.assumptions_injected, 0);
        assert_eq!(result.havoced_calls, 1, "open dyn call must fall back to havoc");
    }

    // --- DynDispatchVc tests ---

    #[test]
    fn test_dyn_dispatch_empty_targets() {
        let contract = MethodContract {
            method_name: "foo".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let dispatch = DynDispatchVc::new("Trait", "foo", &contract, &[]);
        let vcs = dispatch.generate_vcs("test_fn");

        assert_eq!(vcs.len(), 1);
        assert!(
            matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("no known implementations"))
        );
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    #[test]
    fn test_dyn_dispatch_single_target() {
        let contract = MethodContract {
            method_name: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let targets = vec![ConcreteTarget {
            impl_type: Ty::i32(),
            body_def_path: "<i32 as Compute>::compute".to_string(),
        }];

        let dispatch = DynDispatchVc::new("Compute", "compute", &contract, &targets);
        let vcs = dispatch.generate_vcs("test_fn");

        // 1 target * (1 pre + 1 post) = 2 VCs, no completeness for single target
        assert_eq!(vcs.len(), 2);
    }

    #[test]
    fn generated_impl_contract_vars_cannot_alias_contract_variables() {
        // `Bool` has an identifier-shaped Debug spelling, so both of these
        // were legal source-contract variable spellings in the old scheme.
        let legacy_pre = "pre_Bool_compute";
        let legacy_post = "post_Bool_compute";
        let contract = MethodContract {
            method_name: "compute".into(),
            preconditions: vec![Formula::Var(legacy_pre.into(), Sort::Bool)],
            postconditions: vec![Formula::Var(legacy_post.into(), Sort::Bool)],
        };
        let targets = vec![ConcreteTarget {
            impl_type: Ty::Bool,
            body_def_path: "<bool as Compute>::compute".into(),
        }];

        let vcs =
            DynDispatchVc::new("Compute", "compute", &contract, &targets).generate_vcs("test_fn");
        let pre_vars = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
            .expect("precondition VC")
            .formula
            .free_variables();
        let post_vars = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::Postcondition))
            .expect("postcondition VC")
            .formula
            .free_variables();
        let generated_pre = generated_vtable_symbol("impl_pre_Bool_compute");
        let generated_post = generated_vtable_symbol("impl_post_Bool_compute");

        assert!(pre_vars.contains(legacy_pre) && pre_vars.contains(&generated_pre));
        assert!(post_vars.contains(legacy_post) && post_vars.contains(&generated_post));
        assert_ne!(generated_pre, legacy_pre);
        assert_ne!(generated_post, legacy_post);
    }

    #[test]
    fn test_dyn_dispatch_multi_target() {
        let contract = MethodContract {
            method_name: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let targets = vec![
            ConcreteTarget { impl_type: Ty::i32(), body_def_path: "<i32>::compute".to_string() },
            ConcreteTarget { impl_type: Ty::u32(), body_def_path: "<u32>::compute".to_string() },
            ConcreteTarget { impl_type: Ty::u64(), body_def_path: "<u64>::compute".to_string() },
        ];

        let dispatch = DynDispatchVc::new("Compute", "compute", &contract, &targets);
        let vcs = dispatch.generate_vcs("test_fn");

        // 3 targets * (1 pre + 1 post) + 1 completeness = 7 VCs
        assert_eq!(vcs.len(), 7);

        let completeness_vc = vcs.last().unwrap();
        assert!(
            matches!(&completeness_vc.kind, VcKind::Assertion { message } if message.contains("3 impls"))
        );
    }

    #[test]
    fn test_dyn_dispatch_precondition_only() {
        let contract = MethodContract {
            method_name: "check".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![],
        };

        let targets = vec![ConcreteTarget {
            impl_type: Ty::i32(),
            body_def_path: "<i32>::check".to_string(),
        }];

        let dispatch = DynDispatchVc::new("Check", "check", &contract, &targets);
        let vcs = dispatch.generate_vcs("test_fn");

        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { .. }));
    }

    #[test]
    fn test_dyn_dispatch_postcondition_only() {
        let contract = MethodContract {
            method_name: "produce".to_string(),
            preconditions: vec![],
            postconditions: vec![result_ge_0()],
        };

        let targets = vec![ConcreteTarget {
            impl_type: Ty::i32(),
            body_def_path: "<i32>::produce".to_string(),
        }];

        let dispatch = DynDispatchVc::new("Produce", "produce", &contract, &targets);
        let vcs = dispatch.generate_vcs("test_fn");

        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::Postcondition));
    }

    #[test]
    fn test_dyn_dispatch_vc_function_names() {
        let contract = MethodContract {
            method_name: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let targets = vec![ConcreteTarget {
            impl_type: Ty::i32(),
            body_def_path: "<i32>::compute".to_string(),
        }];

        let dispatch = DynDispatchVc::new("Compute", "compute", &contract, &targets);
        let vcs = dispatch.generate_vcs("test_fn");

        // Pre VC uses function_name, Post VC uses <Type as Trait>::method
        let post_vc = vcs.iter().find(|vc| matches!(vc.kind, VcKind::Postcondition)).unwrap();
        assert!(post_vc.function.contains("Compute"));
    }

    // --- TraitBoundPropagation tests ---

    #[test]
    fn test_bound_propagation_all_satisfied() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        resolver.add_impl(make_send_impl(Ty::i32()));

        let propagation = TraitBoundPropagation::new(
            "T",
            vec![make_trait_bound("Clone"), make_trait_bound("Send")],
        );

        let results = propagation.check_bounds(&resolver, &Ty::i32());
        assert!(results.iter().all(|r| r.satisfied));

        let vcs = propagation.generate_bound_vcs(&resolver, &Ty::i32(), "test_fn");
        assert!(vcs.is_empty(), "no VCs when all bounds satisfied");
    }

    #[test]
    fn test_bound_propagation_partial_satisfaction() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        // No Send impl for i32

        let propagation = TraitBoundPropagation::new(
            "T",
            vec![make_trait_bound("Clone"), make_trait_bound("Send")],
        );

        let results = propagation.check_bounds(&resolver, &Ty::i32());
        assert_eq!(results.iter().filter(|r| r.satisfied).count(), 1);
        assert_eq!(results.iter().filter(|r| !r.satisfied).count(), 1);

        let vcs = propagation.generate_bound_vcs(&resolver, &Ty::i32(), "test_fn");
        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("Send")));
    }

    #[test]
    fn test_bound_propagation_none_satisfied() {
        let resolver = TraitResolver::new();

        let propagation = TraitBoundPropagation::new(
            "T",
            vec![make_trait_bound("Clone"), make_trait_bound("Send")],
        );

        let vcs = propagation.generate_bound_vcs(&resolver, &Ty::i32(), "test_fn");
        assert_eq!(vcs.len(), 2);
    }

    #[test]
    fn test_bound_propagation_multi_type() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_send_impl(Ty::i32()));
        // u32 does NOT implement Send in this test setup

        let propagation = TraitBoundPropagation::new("T", vec![make_trait_bound("Send")]);

        let types = vec![Ty::i32(), Ty::u32()];
        let vcs = propagation.generate_multi_type_vcs(&resolver, &types, "test_fn");

        // i32 satisfies Send, u32 does not -> 1 VC
        assert_eq!(vcs.len(), 1);
    }

    #[test]
    fn test_bound_propagation_empty_bounds() {
        let resolver = TraitResolver::new();
        let propagation = TraitBoundPropagation::new("T", vec![]);

        let vcs = propagation.generate_bound_vcs(&resolver, &Ty::i32(), "test_fn");
        assert!(vcs.is_empty());
    }

    // --- ObjectSafetyChecker tests ---

    #[test]
    fn test_object_safety_safe_trait() {
        let checker = ObjectSafetyChecker::new(
            "Iterator",
            vec![ObjectSafetyMethod {
                name: "next".to_string(),
                has_receiver: true,
                returns_self: false,
                has_type_params: false,
                where_self_sized: false,
            }],
            false,
        );

        assert!(checker.is_object_safe());
        assert!(checker.check().is_empty());
        assert!(checker.generate_vcs("test_fn").is_empty());
    }

    #[test]
    fn test_object_safety_sized_supertrait() {
        let checker = ObjectSafetyChecker::new("SizedTrait", vec![], true);

        assert!(!checker.is_object_safe());
        let violations = checker.check();
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0], ObjectSafetyViolation::SizedSupertrait);
    }

    #[test]
    fn test_object_safety_no_receiver() {
        let checker = ObjectSafetyChecker::new(
            "BadTrait",
            vec![ObjectSafetyMethod {
                name: "associated_fn".to_string(),
                has_receiver: false,
                returns_self: false,
                has_type_params: false,
                where_self_sized: false,
            }],
            false,
        );

        assert!(!checker.is_object_safe());
        let violations = checker.check();
        assert_eq!(violations.len(), 1);
        assert!(matches!(
            &violations[0],
            ObjectSafetyViolation::NoReceiver { method } if method == "associated_fn"
        ));
    }

    #[test]
    fn test_object_safety_returns_self() {
        let checker = ObjectSafetyChecker::new(
            "Clone",
            vec![ObjectSafetyMethod {
                name: "clone".to_string(),
                has_receiver: true,
                returns_self: true,
                has_type_params: false,
                where_self_sized: false,
            }],
            false,
        );

        assert!(!checker.is_object_safe());
        let violations = checker.check();
        assert!(violations.iter().any(|v| matches!(v, ObjectSafetyViolation::ReturnsSelf { .. })));
    }

    #[test]
    fn test_object_safety_generic_method() {
        let checker = ObjectSafetyChecker::new(
            "GenericTrait",
            vec![ObjectSafetyMethod {
                name: "generic_method".to_string(),
                has_receiver: true,
                returns_self: false,
                has_type_params: true,
                where_self_sized: false,
            }],
            false,
        );

        assert!(!checker.is_object_safe());
        let violations = checker.check();
        assert!(
            violations.iter().any(|v| matches!(v, ObjectSafetyViolation::GenericMethod { .. }))
        );
    }

    #[test]
    fn test_object_safety_where_self_sized_excluded() {
        // Methods with where Self: Sized are excluded from object safety checks
        let checker = ObjectSafetyChecker::new(
            "MixedTrait",
            vec![
                ObjectSafetyMethod {
                    name: "safe_method".to_string(),
                    has_receiver: true,
                    returns_self: false,
                    has_type_params: false,
                    where_self_sized: false,
                },
                ObjectSafetyMethod {
                    name: "sized_method".to_string(),
                    has_receiver: false,   // would normally violate, but excluded
                    returns_self: true,    // would normally violate, but excluded
                    has_type_params: true, // would normally violate, but excluded
                    where_self_sized: true,
                },
            ],
            false,
        );

        assert!(checker.is_object_safe());
    }

    #[test]
    fn test_object_safety_multiple_violations() {
        let checker = ObjectSafetyChecker::new(
            "BadTrait",
            vec![
                ObjectSafetyMethod {
                    name: "no_self".to_string(),
                    has_receiver: false,
                    returns_self: false,
                    has_type_params: false,
                    where_self_sized: false,
                },
                ObjectSafetyMethod {
                    name: "returns_self".to_string(),
                    has_receiver: true,
                    returns_self: true,
                    has_type_params: false,
                    where_self_sized: false,
                },
            ],
            true, // sized supertrait
        );

        let violations = checker.check();
        assert_eq!(violations.len(), 3); // Sized + NoReceiver + ReturnsSelf
    }

    #[test]
    fn test_object_safety_generates_vcs() {
        let checker = ObjectSafetyChecker::new(
            "BadTrait",
            vec![ObjectSafetyMethod {
                name: "bad".to_string(),
                has_receiver: false,
                returns_self: true,
                has_type_params: false,
                where_self_sized: false,
            }],
            false,
        );

        let vcs = checker.generate_vcs("test_fn");
        assert_eq!(vcs.len(), 2); // NoReceiver + ReturnsSelf
        for vc in &vcs {
            assert_eq!(vc.formula, Formula::Bool(true));
            assert!(
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("object safety"))
            );
        }
    }

    // --- WitnessType tests ---

    #[test]
    fn test_witness_found() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        resolver.add_impl(make_send_impl(Ty::i32()));

        let witness = WitnessType::find_witness(
            "T",
            &[make_trait_bound("Clone"), make_trait_bound("Send")],
            &resolver,
        );

        assert!(witness.is_satisfiable());
        assert!(witness.witness.is_some());
    }

    #[test]
    fn test_witness_not_found() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        // i32 has Clone but not Sync; no type has both

        let witness = WitnessType::find_witness(
            "T",
            &[make_trait_bound("Clone"), make_trait_bound("Sync")],
            &resolver,
        );

        assert!(!witness.is_satisfiable());
        assert!(witness.witness.is_none());
    }

    #[test]
    fn test_witness_single_bound() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));

        let witness = WitnessType::find_witness("T", &[make_trait_bound("Clone")], &resolver);

        assert!(witness.is_satisfiable());
    }

    #[test]
    fn test_witness_no_impls() {
        let resolver = TraitResolver::new();

        let witness = WitnessType::find_witness("T", &[make_trait_bound("Clone")], &resolver);

        assert!(!witness.is_satisfiable());
    }

    #[test]
    fn test_witness_empty_bounds() {
        let resolver = TraitResolver::new();

        let witness = WitnessType::find_witness("T", &[], &resolver);

        // Empty bounds means any type satisfies, but with no impls there are
        // no candidate types so no witness is found.
        assert!(!witness.is_satisfiable());
    }

    #[test]
    fn test_witness_vc_satisfiable() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));

        let witness = WitnessType::find_witness("T", &[make_trait_bound("Clone")], &resolver);
        let vc = witness.generate_vc("test_fn");

        // Witness found -> formula is Bool(false) (no violation)
        assert_eq!(vc.formula, Formula::Bool(false));
    }

    #[test]
    fn test_witness_vc_unsatisfiable() {
        let resolver = TraitResolver::new();

        let witness = WitnessType::find_witness("T", &[make_trait_bound("Clone")], &resolver);
        let vc = witness.generate_vc("test_fn");

        // No witness -> formula is Bool(true) (violation)
        assert_eq!(vc.formula, Formula::Bool(true));
    }

    #[test]
    fn test_witness_multiple_satisfying_types() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));
        resolver.add_impl(make_clone_impl(Ty::u32()));
        resolver.add_impl(make_send_impl(Ty::i32()));
        resolver.add_impl(make_send_impl(Ty::u32()));

        let witness = WitnessType::find_witness(
            "T",
            &[make_trait_bound("Clone"), make_trait_bound("Send")],
            &resolver,
        );

        // At least one of i32, u32 should be found as witness
        assert!(witness.is_satisfiable());
    }

    // --- Integration tests ---

    #[test]
    fn test_full_vtable_verification_pipeline() {
        // Set up: Compute trait with i32 and u32 impls, plus Send bound
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_compute_impl(Ty::i32()));
        resolver.add_impl(make_compute_impl(Ty::u32()));
        resolver.add_impl(make_send_impl(Ty::i32()));
        resolver.add_impl(make_send_impl(Ty::u32()));

        // 1. Build vtable model with contracts
        let mut model = VtableModel::from_resolver(&resolver, "Compute");
        model.set_contract(MethodContract {
            method_name: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        });

        // 2. Generate dispatch VCs
        let dispatch_vcs = model.generate_dispatch_vcs("test_fn");
        assert!(!dispatch_vcs.is_empty());

        // 3. Check trait bound propagation (dyn Compute + Send)
        let bound_prop = TraitBoundPropagation::new("T", vec![make_trait_bound("Send")]);
        let bound_vcs =
            bound_prop.generate_multi_type_vcs(&resolver, &[Ty::i32(), Ty::u32()], "test_fn");
        assert!(bound_vcs.is_empty(), "both types implement Send");

        // 4. Check object safety
        let safety = ObjectSafetyChecker::new(
            "Compute",
            vec![ObjectSafetyMethod {
                name: "compute".to_string(),
                has_receiver: true,
                returns_self: false,
                has_type_params: false,
                where_self_sized: false,
            }],
            false,
        );
        assert!(safety.is_object_safe());

        // 5. Find witness
        let witness = WitnessType::find_witness(
            "T",
            &[make_trait_bound("Compute"), make_trait_bound("Send")],
            &resolver,
        );
        assert!(witness.is_satisfiable());
    }

    #[test]
    fn test_conjunction_helper() {
        assert_eq!(conjunction(&[]), Formula::Bool(true));
        let f = x_gt_0();
        assert_eq!(conjunction(std::slice::from_ref(&f)), f);
        let g = result_ge_0();
        let conj = conjunction(&[f.clone(), g.clone()]);
        assert!(matches!(conj, Formula::And(ref v) if v.len() == 2));
    }

    #[test]
    fn test_object_safety_violation_descriptions() {
        let v1 = ObjectSafetyViolation::SizedSupertrait;
        assert!(v1.description().contains("Sized"));

        let v2 = ObjectSafetyViolation::NoReceiver { method: "foo".to_string() };
        assert!(v2.description().contains("foo"));
        assert!(v2.description().contains("receiver"));

        let v3 = ObjectSafetyViolation::ReturnsSelf { method: "bar".to_string() };
        assert!(v3.description().contains("bar"));
        assert!(v3.description().contains("Self"));

        let v4 = ObjectSafetyViolation::GenericMethod { method: "baz".to_string() };
        assert!(v4.description().contains("baz"));
        assert!(v4.description().contains("generic"));
    }

    #[test]
    fn test_bound_check_result_reason_messages() {
        let mut resolver = TraitResolver::new();
        resolver.add_impl(make_clone_impl(Ty::i32()));

        let propagation = TraitBoundPropagation::new("T", vec![make_trait_bound("Clone")]);
        let results = propagation.check_bounds(&resolver, &Ty::i32());

        assert_eq!(results.len(), 1);
        assert!(results[0].satisfied);
        assert!(results[0].reason.contains("implements"));
    }
}
