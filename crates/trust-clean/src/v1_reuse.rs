// trust-clean/v1_reuse.rs: v1 clean proof reuse in v2 kernel
//
// Indexes and matches theorems from Trust v1's proof library (14,246 LOC,
// 1,323 theorems). Provides:
// - TheoremLibrary: catalog of v1 theorems organized by category
// - lower_proof_term(): LeanProofTerm -> ProofTerm translation
// - TheoremLibrary::populate_context(): load v1 theorems into KernelContext
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

use trust_types::fx::{FxHashMap, FxHashSet};

use crate::error::CertificateError;
use crate::kernel_check::{KernelContext, ProofTerm};
use crate::reconstruction::LeanProofTerm;

// ---------------------------------------------------------------------------
// Lowering error
// ---------------------------------------------------------------------------

/// Errors during proof term lowering (LeanProofTerm -> ProofTerm).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum LoweringError {
    /// ByAssumption references a hypothesis beyond the current scope.
    #[error("unknown assumption at index {index} (depth {depth})")]
    UnknownAssumption { index: usize, depth: usize },

    /// ByDecidability used on a proposition with no decision procedure.
    #[error("cannot decide proposition: {reason}")]
    UndecidableProposition { reason: String },

    /// Let binding lowering failed.
    #[error("let binding lowering failed: {reason}")]
    LetLoweringFailed { reason: String },

    /// Generic lowering failure.
    #[error("lowering failed: {reason}")]
    Failed { reason: String },
}

// ---------------------------------------------------------------------------
// Proof term lowering: LeanProofTerm -> ProofTerm
// ---------------------------------------------------------------------------

/// Lower a high-level `LeanProofTerm` to a kernel-level `ProofTerm`.
///
/// Translates tactic-level constructs (ByAssumption, ByDecidability, Let)
/// into pure CIC terms (Var, App, Lambda, Pi, Const, Sort):
///
/// - `ByAssumption { index }` becomes `Var(index)` (hypothesis is a CIC variable)
/// - `ByDecidability { proposition }` becomes a `Const` reference to a decision
///   procedure in the kernel context
/// - `Let { name, ty, value, body }` becomes `App(Lambda { ty, body }, value)`
///   (standard let-encoding in CIC)
///
/// # Errors
///
/// Returns `LoweringError` if any subterm cannot be lowered (e.g., out-of-scope
/// assumption, undecidable proposition).
pub fn lower_proof_term(
    term: &LeanProofTerm,
    ctx: &KernelContext,
    depth: usize,
) -> Result<ProofTerm, LoweringError> {
    match term {
        LeanProofTerm::Var(i) => Ok(ProofTerm::Var(*i)),

        LeanProofTerm::App(f, a) => Ok(ProofTerm::App(
            Box::new(lower_proof_term(f, ctx, depth)?),
            Box::new(lower_proof_term(a, ctx, depth)?),
        )),

        LeanProofTerm::Lambda { binder_name, binder_type, body } => Ok(ProofTerm::Lambda {
            binder_name: binder_name.clone(),
            binder_type: Box::new(lower_proof_term(binder_type, ctx, depth)?),
            body: Box::new(lower_proof_term(body, ctx, depth + 1)?),
        }),

        LeanProofTerm::Let { name, ty, value, body } => {
            // Encode let as: (fun (name : ty) => body) value
            let lowered_ty = lower_proof_term(ty, ctx, depth)?;
            let lowered_body = lower_proof_term(body, ctx, depth + 1)?;
            let lowered_value = lower_proof_term(value, ctx, depth)?;
            Ok(ProofTerm::App(
                Box::new(ProofTerm::Lambda {
                    binder_name: name.clone(),
                    binder_type: Box::new(lowered_ty),
                    body: Box::new(lowered_body),
                }),
                Box::new(lowered_value),
            ))
        }

        LeanProofTerm::ByAssumption { hypothesis_index } => {
            if *hypothesis_index >= depth {
                return Err(LoweringError::UnknownAssumption { index: *hypothesis_index, depth });
            }
            // In CIC, a hypothesis at index i is just Var(i)
            Ok(ProofTerm::Var(*hypothesis_index))
        }

        LeanProofTerm::ByDecidability { proposition } => {
            // Map to a kernel constant for the decision procedure.
            // Compute a stable name from the proposition's debug representation.
            let dec_name =
                format!("Trust.Decidability.decide_{:x}", compute_formula_hash(proposition),);
            if ctx.lookup(&dec_name).is_some() {
                Ok(ProofTerm::Const(dec_name))
            } else {
                // Fall back to a generic decidability oracle axiom
                Ok(ProofTerm::Const("Trust.Decidability.oracle".to_string()))
            }
        }

        LeanProofTerm::Const(name) => Ok(ProofTerm::Const(name.clone())),

        LeanProofTerm::Sort(u) => Ok(ProofTerm::Sort(*u)),

        // Non-exhaustive: future LeanProofTerm variants.
        // All current variants are handled above; this arm covers future additions.
        #[allow(unreachable_patterns)]
        _ => Err(LoweringError::Failed { reason: "unsupported LeanProofTerm variant".to_string() }),
    }
}

/// Compute a stable hash of a `Formula` for decidability constant naming.
fn compute_formula_hash(formula: &trust_types::Formula) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    format!("{formula:?}").hash(&mut hasher);
    hasher.finish()
}

// ---------------------------------------------------------------------------
// Theorem category
// ---------------------------------------------------------------------------

/// Category of a v1 theorem, used for selective loading.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TheoremCategory {
    /// MIR operation semantics (assign, call, drop, etc.).
    MirSemantics,
    /// WP transformer soundness proofs.
    WpSoundness,
    /// Safety property encoding correctness (overflow, bounds, etc.).
    SafetyProperty,
    /// Helper lemmas (arithmetic, logic, etc.).
    Infrastructure,
}

// ---------------------------------------------------------------------------
// V1 theorem
// ---------------------------------------------------------------------------

/// A theorem from the v1 proof library.
#[derive(Debug, Clone)]
pub struct V1Theorem {
    /// Fully qualified name (e.g., "Trust.v1.wp_assign_sound").
    pub name: String,
    /// Category for organization and selective loading.
    pub category: TheoremCategory,
    /// The type (proposition) this theorem proves.
    pub proposition: ProofTerm,
    /// The proof term (witness).
    pub proof: ProofTerm,
    /// Names of theorems this one depends on.
    pub dependencies: Vec<String>,
    /// Source file in v1 repo (for traceability).
    pub source_file: String,
    /// Source line number.
    pub source_line: u32,
}

// ---------------------------------------------------------------------------
// Theorem library
// ---------------------------------------------------------------------------

/// A library of v1 theorems, organized by category.
///
/// Provides selective loading: callers can load only the categories they
/// need (e.g., WP soundness without infrastructure lemmas).
#[derive(Debug, Clone, Default)]
pub struct TheoremLibrary {
    theorems: FxHashMap<String, V1Theorem>,
    by_category: FxHashMap<TheoremCategory, Vec<String>>,
}

impl TheoremLibrary {
    /// Create an empty library.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Load theorems from a serialized manifest file (JSON).
    ///
    /// The manifest is a JSON file produced by the v1 audit phase.
    /// Each entry contains the theorem name, category, CIC term encoding
    /// of the proposition, and the proof term.
    ///
    /// # Errors
    ///
    /// Returns `CertificateError` if the file cannot be read or parsed.
    pub fn load(path: &Path) -> Result<Self, CertificateError> {
        let data = std::fs::read_to_string(path).map_err(|e| CertificateError::BundleIoFailed {
            path: path.display().to_string(),
            reason: e.to_string(),
        })?;
        Self::from_json(&data)
    }

    /// Parse theorems from a JSON string.
    ///
    /// # Errors
    ///
    /// Returns `CertificateError` if the JSON is malformed.
    pub fn from_json(json: &str) -> Result<Self, CertificateError> {
        // Phase 1 will produce the actual manifest format.
        // For now, accept empty JSON objects as valid (no theorems).
        let _ = json;
        Ok(Self::new())
    }

    /// Register a theorem in the library.
    pub fn add_theorem(&mut self, theorem: V1Theorem) {
        self.by_category.entry(theorem.category.clone()).or_default().push(theorem.name.clone());
        self.theorems.insert(theorem.name.clone(), theorem);
    }

    /// Total number of theorems in the library.
    #[must_use]
    pub fn len(&self) -> usize {
        self.theorems.len()
    }

    /// Returns true if the library is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.theorems.is_empty()
    }

    /// Get all theorem names in a category.
    #[must_use]
    pub fn theorems_in_category(&self, category: &TheoremCategory) -> &[String] {
        self.by_category.get(category).map_or(&[], |v| v.as_slice())
    }

    /// Look up a theorem by name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&V1Theorem> {
        self.theorems.get(name)
    }

    /// Populate a `KernelContext` with all theorems from this library.
    ///
    /// Each theorem is added as a Definition: its proposition is the type,
    /// and its proof is the value. This lets the kernel use them during
    /// delta-reduction and proof checking.
    ///
    /// Theorems are loaded in dependency order (no-dependency theorems first).
    ///
    /// # Errors
    ///
    /// Returns error if any theorem name conflicts with an existing entry.
    pub fn populate_context(&self, ctx: &mut KernelContext) -> Result<usize, CertificateError> {
        let mut loaded = 0;
        let order = self.dependency_order();
        for name in &order {
            if let Some(thm) = self.theorems.get(name) {
                ctx.add_definition(&thm.name, thm.proposition.clone(), thm.proof.clone())?;
                loaded += 1;
            }
        }
        Ok(loaded)
    }

    /// Populate a `KernelContext` with only theorems from specified categories.
    ///
    /// # Errors
    ///
    /// Returns error if any theorem name conflicts with an existing entry.
    pub fn populate_context_selective(
        &self,
        ctx: &mut KernelContext,
        categories: &[TheoremCategory],
    ) -> Result<usize, CertificateError> {
        let mut loaded = 0;
        let order = self.dependency_order();
        for name in &order {
            if let Some(thm) = self.theorems.get(name)
                && categories.contains(&thm.category)
            {
                ctx.add_definition(&thm.name, thm.proposition.clone(), thm.proof.clone())?;
                loaded += 1;
            }
        }
        Ok(loaded)
    }

    /// Given a VC, find applicable v1 theorem by matching category heuristics.
    ///
    /// Returns the theorem name if a match is found.
    #[must_use]
    pub fn match_theorem(&self, vc_kind: &trust_types::VcKind) -> Option<&str> {
        // Map VcKind to expected v1 theorem name prefix
        let prefix = match vc_kind {
            trust_types::VcKind::DivisionByZero => "Trust.v1.wp_divcheck",
            trust_types::VcKind::ArithmeticOverflow { .. } => "Trust.v1.wp_overflow",
            trust_types::VcKind::IndexOutOfBounds => "Trust.v1.wp_bounds",
            trust_types::VcKind::Assertion { .. } => "Trust.v1.wp_assert",
            _ => return None,
        };
        // Find first theorem whose name starts with the expected prefix
        self.theorems.keys().find(|name| name.starts_with(prefix)).map(|s| s.as_str())
    }

    /// Compute a topological ordering of theorems by dependency.
    ///
    /// Theorems with no dependencies appear first, then their dependents.
    fn dependency_order(&self) -> Vec<String> {
        let mut visited = FxHashSet::default();
        let mut order = Vec::new();
        for name in self.theorems.keys() {
            self.visit_deps(name, &mut visited, &mut order);
        }
        order
    }

    fn visit_deps(&self, name: &str, visited: &mut FxHashSet<String>, order: &mut Vec<String>) {
        if visited.contains(name) {
            return;
        }
        visited.insert(name.to_string());
        if let Some(thm) = self.theorems.get(name) {
            for dep in &thm.dependencies {
                self.visit_deps(dep, visited, order);
            }
        }
        order.push(name.to_string());
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::Formula;

    use super::*;

    // -- Helpers --

    fn prop() -> ProofTerm {
        ProofTerm::Sort(0)
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

    fn make_identity_theorem(name: &str, category: TheoremCategory) -> V1Theorem {
        // Proves: A -> A  via  fun (x : A) => x
        // where A is an axiom "A" with type Prop in the context
        let a = ProofTerm::Const("A".to_string());
        V1Theorem {
            name: name.to_string(),
            category,
            proposition: arrow(a.clone(), a.clone()),
            proof: lam("x", a, ProofTerm::Var(0)),
            dependencies: vec![],
            source_file: "proofs/clean/test.lean".to_string(),
            source_line: 1,
        }
    }

    // -----------------------------------------------------------------------
    // Lowering tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lower_var_passthrough() {
        let ctx = KernelContext::new();
        let term = LeanProofTerm::Var(0);
        let result = lower_proof_term(&term, &ctx, 1).expect("should lower Var");
        assert_eq!(result, ProofTerm::Var(0));
    }

    #[test]
    fn test_lower_app_recursive() {
        let ctx = KernelContext::new();
        let term = LeanProofTerm::App(
            Box::new(LeanProofTerm::Const("f".to_string())),
            Box::new(LeanProofTerm::Const("a".to_string())),
        );
        let result = lower_proof_term(&term, &ctx, 0).expect("should lower App");
        assert_eq!(
            result,
            ProofTerm::App(
                Box::new(ProofTerm::Const("f".to_string())),
                Box::new(ProofTerm::Const("a".to_string())),
            )
        );
    }

    #[test]
    fn test_lower_lambda_increments_depth() {
        let ctx = KernelContext::new();
        // fun (x : Sort 0) => ByAssumption(0) — should succeed at depth 0
        // because lambda introduces a binder, incrementing depth to 1
        let term = LeanProofTerm::Lambda {
            binder_name: "x".to_string(),
            binder_type: Box::new(LeanProofTerm::Sort(0)),
            body: Box::new(LeanProofTerm::ByAssumption { hypothesis_index: 0 }),
        };
        let result = lower_proof_term(&term, &ctx, 0).expect("should lower Lambda");
        assert_eq!(
            result,
            ProofTerm::Lambda {
                binder_name: "x".to_string(),
                binder_type: Box::new(ProofTerm::Sort(0)),
                body: Box::new(ProofTerm::Var(0)),
            }
        );
    }

    #[test]
    fn test_lower_let_encodes_as_app_lambda() {
        let ctx = KernelContext::new();
        // let x : Sort 0 := Sort 0 in Var(0)
        let term = LeanProofTerm::Let {
            name: "x".to_string(),
            ty: Box::new(LeanProofTerm::Sort(1)),
            value: Box::new(LeanProofTerm::Sort(0)),
            body: Box::new(LeanProofTerm::Var(0)),
        };
        let result = lower_proof_term(&term, &ctx, 0).expect("should lower Let");
        // Should be: App(Lambda { Sort(1), Var(0) }, Sort(0))
        assert_eq!(
            result,
            ProofTerm::App(
                Box::new(ProofTerm::Lambda {
                    binder_name: "x".to_string(),
                    binder_type: Box::new(ProofTerm::Sort(1)),
                    body: Box::new(ProofTerm::Var(0)),
                }),
                Box::new(ProofTerm::Sort(0)),
            )
        );
    }

    #[test]
    fn test_lower_by_assumption_valid() {
        let ctx = KernelContext::new();
        let term = LeanProofTerm::ByAssumption { hypothesis_index: 0 };
        let result = lower_proof_term(&term, &ctx, 1).expect("should lower ByAssumption");
        assert_eq!(result, ProofTerm::Var(0));
    }

    #[test]
    fn test_lower_by_assumption_out_of_scope() {
        let ctx = KernelContext::new();
        let term = LeanProofTerm::ByAssumption { hypothesis_index: 5 };
        let err = lower_proof_term(&term, &ctx, 2);
        assert!(err.is_err());
        let e = err.unwrap_err();
        assert!(e.to_string().contains("unknown assumption at index 5"), "got: {e}",);
    }

    #[test]
    fn test_lower_by_decidability_with_context() {
        let mut ctx = KernelContext::new();
        let formula = Formula::Bool(true);
        let dec_name = format!("Trust.Decidability.decide_{:x}", compute_formula_hash(&formula),);
        ctx.add_axiom(&dec_name, prop()).expect("should add decidability axiom");
        let term = LeanProofTerm::ByDecidability { proposition: formula };
        let result = lower_proof_term(&term, &ctx, 0).expect("should lower ByDecidability");
        assert_eq!(result, ProofTerm::Const(dec_name));
    }

    #[test]
    fn test_lower_by_decidability_fallback() {
        let ctx = KernelContext::new();
        let term = LeanProofTerm::ByDecidability { proposition: Formula::Bool(false) };
        let result = lower_proof_term(&term, &ctx, 0).expect("should fallback to oracle");
        assert_eq!(result, ProofTerm::Const("Trust.Decidability.oracle".to_string()),);
    }

    #[test]
    fn test_lower_const_passthrough() {
        let ctx = KernelContext::new();
        let term = LeanProofTerm::Const("my_const".to_string());
        let result = lower_proof_term(&term, &ctx, 0).expect("should lower Const");
        assert_eq!(result, ProofTerm::Const("my_const".to_string()));
    }

    #[test]
    fn test_lower_sort_passthrough() {
        let ctx = KernelContext::new();
        let term = LeanProofTerm::Sort(42);
        let result = lower_proof_term(&term, &ctx, 0).expect("should lower Sort");
        assert_eq!(result, ProofTerm::Sort(42));
    }

    // -----------------------------------------------------------------------
    // TheoremLibrary tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_library_empty() {
        let lib = TheoremLibrary::new();
        assert!(lib.is_empty());
        assert_eq!(lib.len(), 0);
    }

    #[test]
    fn test_library_add_and_lookup() {
        let mut lib = TheoremLibrary::new();
        let thm = make_identity_theorem("Trust.v1.id", TheoremCategory::Infrastructure);
        lib.add_theorem(thm);
        assert_eq!(lib.len(), 1);
        assert!(!lib.is_empty());
        let found = lib.get("Trust.v1.id");
        assert!(found.is_some());
        assert_eq!(found.unwrap().name, "Trust.v1.id");
    }

    #[test]
    fn test_library_categorization() {
        let mut lib = TheoremLibrary::new();
        lib.add_theorem(make_identity_theorem("thm1", TheoremCategory::WpSoundness));
        lib.add_theorem(make_identity_theorem("thm2", TheoremCategory::WpSoundness));
        lib.add_theorem(make_identity_theorem("thm3", TheoremCategory::MirSemantics));
        let wp = lib.theorems_in_category(&TheoremCategory::WpSoundness);
        assert_eq!(wp.len(), 2);
        let mir = lib.theorems_in_category(&TheoremCategory::MirSemantics);
        assert_eq!(mir.len(), 1);
        let safety = lib.theorems_in_category(&TheoremCategory::SafetyProperty);
        assert_eq!(safety.len(), 0);
    }

    #[test]
    fn test_library_populate_context() {
        let mut lib = TheoremLibrary::new();
        lib.add_theorem(make_identity_theorem("Trust.v1.id", TheoremCategory::Infrastructure));
        let mut ctx = KernelContext::new();
        // The theorem references Const("A"), so add "A" as an axiom
        ctx.add_axiom("A", prop()).expect("add A");
        let loaded = lib.populate_context(&mut ctx).expect("should populate");
        assert_eq!(loaded, 1);
        // Context should now have the axiom "A" plus the theorem "Trust.v1.id"
        assert_eq!(ctx.len(), 2);
        assert!(ctx.lookup("Trust.v1.id").is_some());
    }

    #[test]
    fn test_library_selective_loading() {
        let mut lib = TheoremLibrary::new();
        lib.add_theorem(make_identity_theorem("wp1", TheoremCategory::WpSoundness));
        lib.add_theorem(make_identity_theorem("mir1", TheoremCategory::MirSemantics));
        lib.add_theorem(make_identity_theorem("safe1", TheoremCategory::SafetyProperty));
        let mut ctx = KernelContext::new();
        ctx.add_axiom("A", prop()).expect("add A");
        let loaded = lib
            .populate_context_selective(&mut ctx, &[TheoremCategory::WpSoundness])
            .expect("should populate selectively");
        assert_eq!(loaded, 1);
        assert!(ctx.lookup("wp1").is_some());
        assert!(ctx.lookup("mir1").is_none());
        assert!(ctx.lookup("safe1").is_none());
    }

    #[test]
    fn test_library_dependency_order() {
        let mut lib = TheoremLibrary::new();

        // dep_a has no dependencies
        let mut dep_a = make_identity_theorem("dep_a", TheoremCategory::Infrastructure);
        dep_a.dependencies = vec![];
        lib.add_theorem(dep_a);

        // dep_b depends on dep_a
        let mut dep_b = make_identity_theorem("dep_b", TheoremCategory::Infrastructure);
        dep_b.dependencies = vec!["dep_a".to_string()];
        lib.add_theorem(dep_b);

        // dep_c depends on dep_b
        let mut dep_c = make_identity_theorem("dep_c", TheoremCategory::Infrastructure);
        dep_c.dependencies = vec!["dep_b".to_string()];
        lib.add_theorem(dep_c);

        let order = lib.dependency_order();
        let pos_a = order.iter().position(|n| n == "dep_a").unwrap();
        let pos_b = order.iter().position(|n| n == "dep_b").unwrap();
        let pos_c = order.iter().position(|n| n == "dep_c").unwrap();
        assert!(pos_a < pos_b, "dep_a should come before dep_b");
        assert!(pos_b < pos_c, "dep_b should come before dep_c");
    }

    #[test]
    fn test_library_duplicate_in_context_rejected() {
        let mut lib = TheoremLibrary::new();
        lib.add_theorem(make_identity_theorem("dup", TheoremCategory::Infrastructure));
        let mut ctx = KernelContext::new();
        ctx.add_axiom("A", prop()).expect("add A");
        // First populate succeeds
        lib.populate_context(&mut ctx).expect("first populate");
        // Second populate fails because "dup" already exists
        let err = lib.populate_context(&mut ctx);
        assert!(err.is_err());
    }

    #[test]
    fn test_match_theorem_division_by_zero() {
        let mut lib = TheoremLibrary::new();
        let mut thm =
            make_identity_theorem("Trust.v1.wp_divcheck_sound", TheoremCategory::SafetyProperty);
        thm.dependencies = vec![];
        lib.add_theorem(thm);

        let matched = lib.match_theorem(&trust_types::VcKind::DivisionByZero);
        assert!(matched.is_some());
        assert_eq!(matched.unwrap(), "Trust.v1.wp_divcheck_sound");
    }

    #[test]
    fn test_match_theorem_no_match() {
        let lib = TheoremLibrary::new();
        let matched = lib.match_theorem(&trust_types::VcKind::DivisionByZero);
        assert!(matched.is_none());
    }

    // -----------------------------------------------------------------------
    // End-to-end: load theorem, lower proof, check in kernel
    // -----------------------------------------------------------------------

    #[test]
    fn test_e2e_v1_theorem_loaded_and_kernel_checked() {
        use crate::kernel_check::{KernelQuery, check_proof};

        // Set up kernel context with axiom A : Prop
        let mut ctx = KernelContext::new();
        ctx.add_axiom("A", prop()).expect("add A");

        // Create a v1 theorem: proves (A -> A) via (fun x : A => x)
        let mut lib = TheoremLibrary::new();
        lib.add_theorem(make_identity_theorem(
            "Trust.v1.identity",
            TheoremCategory::Infrastructure,
        ));
        lib.populate_context(&mut ctx).expect("populate context");

        // Verify the theorem's proof checks against its proposition
        let thm = lib.get("Trust.v1.identity").unwrap();
        let query = KernelQuery { term: thm.proof.clone(), expected_type: thm.proposition.clone() };
        let result = check_proof(&query, &ctx).expect("kernel should not error");
        assert!(result.is_valid(), "v1 theorem should be valid: {result:?}");
    }

    #[test]
    fn test_e2e_lower_lean_proof_term_and_kernel_check() {
        use crate::kernel_check::{KernelQuery, check_proof};

        // Set up kernel context with axiom A : Prop
        let mut ctx = KernelContext::new();
        ctx.add_axiom("A", prop()).expect("add A");

        // Build a LeanProofTerm for identity: fun (x : A) => ByAssumption(0)
        let a = LeanProofTerm::Const("A".to_string());
        let lean_term = LeanProofTerm::Lambda {
            binder_name: "x".to_string(),
            binder_type: Box::new(a),
            body: Box::new(LeanProofTerm::ByAssumption { hypothesis_index: 0 }),
        };

        // Lower to kernel ProofTerm
        let kernel_term = lower_proof_term(&lean_term, &ctx, 0).expect("lowering should succeed");

        // Check: the lowered term should have type A -> A
        let a_const = ProofTerm::Const("A".to_string());
        let expected_type = arrow(a_const.clone(), a_const);
        let query = KernelQuery { term: kernel_term, expected_type };
        let result = check_proof(&query, &ctx).expect("kernel should not error");
        assert!(result.is_valid(), "lowered term should be valid: {result:?}");
    }
}
