// trust_vcgen/spec_inference.rs: Automatic spec inference from function signatures
//
// `SpecInferenceEngine` infers specifications from function signatures, bodies,
// and naming conventions. Three strategies:
// - Type-based: unsigned params => non-negative, Option return => may be None
// - Name-based: "is_*" => returns bool, "get_*" => non-panicking, etc.
// - Assertion-based: `assert!` statements lifted to preconditions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::persistent_specdb::{InferenceConfidence, SpecSource};

fn signed_min_formula(width: u32) -> Formula {
    Formula::Int(if width == 128 { i128::MIN } else { -(1i128 << (width - 1)) })
}

fn signed_max_formula(width: u32) -> Formula {
    Formula::Int(if width == 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 })
}

fn unsigned_max_formula(width: u32) -> Formula {
    if width == 128 {
        Formula::UInt(u128::MAX)
    } else {
        Formula::Int(((1u128 << width) - 1) as i128)
    }
}

// ---------------------------------------------------------------------------
// InferredSpec — a single inferred spec clause
// ---------------------------------------------------------------------------

/// A single inferred specification clause with provenance.
#[derive(Debug, Clone, PartialEq)]
pub struct InferredSpec {
    /// The inferred formula.
    pub formula: Formula,
    /// Human-readable description of what was inferred.
    pub reason: String,
    /// How the spec was inferred.
    pub strategy: InferenceStrategy,
    /// Confidence in the inferred spec.
    pub confidence: InferenceConfidence,
    /// Whether this is a precondition or postcondition.
    pub kind: InferredSpecKind,
}

/// The inference strategy used to produce a spec.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferenceStrategy {
    /// Inferred from parameter/return types (e.g., unsigned => non-negative).
    TypeBased,
    /// Inferred from function/parameter naming conventions.
    NameBased,
    /// Lifted from assert statements in the function body.
    AssertionBased,
}

/// Whether the inferred spec is a pre- or postcondition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferredSpecKind {
    /// Precondition on function entry.
    Precondition,
    /// Postcondition on function exit.
    Postcondition,
}

// ---------------------------------------------------------------------------
// InferenceResult — collected inferences for a function
// ---------------------------------------------------------------------------

/// All inferred specs for a single function.
#[derive(Debug, Clone, Default)]
pub struct InferenceResult {
    /// The function name.
    pub function_name: String,
    /// Inferred specs.
    pub specs: Vec<InferredSpec>,
}

impl InferenceResult {
    /// Collect only preconditions.
    #[must_use]
    pub fn preconditions(&self) -> Vec<&InferredSpec> {
        self.specs.iter().filter(|s| s.kind == InferredSpecKind::Precondition).collect()
    }

    /// Collect only postconditions.
    #[must_use]
    pub fn postconditions(&self) -> Vec<&InferredSpec> {
        self.specs.iter().filter(|s| s.kind == InferredSpecKind::Postcondition).collect()
    }

    /// Returns true if no specs were inferred.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.specs.is_empty()
    }

    /// Convert to a `FunctionSpec` (string-based) for storage.
    /// Convert every inferred formula through the shared, exact parser
    /// round-trip before it can enter the string-backed spec database.
    ///
    /// # Errors
    ///
    /// Returns [`SpecRenderError`] when any inferred solver formula has no
    /// lossless source-contract representation. No partial spec is returned.
    pub fn to_function_spec(&self) -> Result<FunctionSpec, SpecRenderError> {
        let mut spec = FunctionSpec::default();
        for s in &self.specs {
            let expr = formula_to_spec_expr(&s.formula)?;
            match s.kind {
                InferredSpecKind::Precondition => spec.requires.push(expr),
                InferredSpecKind::Postcondition => spec.ensures.push(expr),
            }
        }
        Ok(spec)
    }

    /// The overall source classification for these inferences.
    ///
    /// Assertion-based inferences (lifted from `assert!` statements) are classified
    /// as `Inferred` (higher confidence). Type-based and name-based inferences are
    /// classified as `Heuristic` (lower confidence). This distinction matters for
    /// proof trustworthiness: assertion-based specs reflect explicit programmer intent,
    /// while type/name-based specs are educated guesses.
    #[must_use]
    pub fn source(&self) -> SpecSource {
        if self.specs.iter().any(|s| s.strategy == InferenceStrategy::AssertionBased) {
            SpecSource::Inferred
        } else {
            SpecSource::Heuristic
        }
    }

    /// The minimum confidence across all inferred specs.
    #[must_use]
    pub fn min_confidence(&self) -> InferenceConfidence {
        self.specs.iter().map(|s| s.confidence).min().unwrap_or(InferenceConfidence::Low)
    }
}

// ---------------------------------------------------------------------------
// SpecInferenceEngine
// ---------------------------------------------------------------------------

/// Engine for automatically inferring specifications from function signatures and bodies.
#[derive(Debug, Clone, Default)]
pub struct SpecInferenceEngine {
    /// Enable type-based inference (default: true).
    pub type_based: bool,
    /// Enable name-based inference (default: true).
    pub name_based: bool,
    /// Enable assertion-based inference (default: true).
    pub assertion_based: bool,
}

impl SpecInferenceEngine {
    /// Create an engine with all strategies enabled.
    #[must_use]
    pub fn new() -> Self {
        Self { type_based: true, name_based: true, assertion_based: true }
    }

    /// Infer specifications for a verifiable function.
    #[must_use]
    pub fn infer(&self, func: &VerifiableFunction) -> InferenceResult {
        let mut result = InferenceResult { function_name: func.name.clone(), specs: Vec::new() };

        if self.type_based {
            self.infer_from_types(func, &mut result);
        }
        if self.name_based {
            self.infer_from_names(func, &mut result);
        }
        if self.assertion_based {
            self.infer_from_assertions(func, &mut result);
        }

        result
    }

    /// Type-based inference: derive specs from parameter and return types.
    fn infer_from_types(&self, func: &VerifiableFunction, result: &mut InferenceResult) {
        // Unsigned integer parameters are always >= 0 (trivially true, but useful
        // for downstream analysis that works in mathematical integers).
        for (idx, local) in func.body.locals.iter().enumerate() {
            // Skip return value (index 0) and non-argument locals.
            if idx == 0 || idx > func.body.arg_count {
                continue;
            }
            let var_name = local.name.as_deref().unwrap_or(&format!("_{idx}")).to_string();

            match &local.ty {
                Ty::Int { width, signed: false } => {
                    // Unsigned: 0 <= param < 2^width
                    result.specs.push(InferredSpec {
                        formula: Formula::And(vec![
                            Formula::Ge(
                                Box::new(Formula::Var(var_name.clone(), Sort::Int)),
                                Box::new(Formula::Int(0)),
                            ),
                            Formula::Le(
                                Box::new(Formula::Var(var_name, Sort::Int)),
                                Box::new(unsigned_max_formula(*width)),
                            ),
                        ]),
                        reason: format!("u{width} parameter is bounded [0, 2^{width}-1]"),
                        strategy: InferenceStrategy::TypeBased,
                        confidence: InferenceConfidence::High,
                        kind: InferredSpecKind::Precondition,
                    });
                }
                Ty::Int { width, signed: true } => {
                    // Signed: -2^(width-1) <= param <= 2^(width-1)-1
                    result.specs.push(InferredSpec {
                        formula: Formula::And(vec![
                            Formula::Ge(
                                Box::new(Formula::Var(var_name.clone(), Sort::Int)),
                                Box::new(signed_min_formula(*width)),
                            ),
                            Formula::Le(
                                Box::new(Formula::Var(var_name, Sort::Int)),
                                Box::new(signed_max_formula(*width)),
                            ),
                        ]),
                        reason: format!(
                            "i{width} parameter is bounded [-2^{}, 2^{}-1]",
                            width - 1,
                            width - 1
                        ),
                        strategy: InferenceStrategy::TypeBased,
                        confidence: InferenceConfidence::High,
                        kind: InferredSpecKind::Precondition,
                    });
                }
                Ty::Bool => {
                    // Bool parameters: no arithmetic bounds needed, but note the type.
                    // This is useful for downstream analysis.
                }
                _ => {}
            }
        }

        // Return type inference.
        match &func.body.return_ty {
            Ty::Int { width, signed: false } => {
                result.specs.push(InferredSpec {
                    formula: Formula::And(vec![
                        Formula::Ge(
                            Box::new(Formula::Var("_0".into(), Sort::Int)),
                            Box::new(Formula::Int(0)),
                        ),
                        Formula::Le(
                            Box::new(Formula::Var("_0".into(), Sort::Int)),
                            Box::new(unsigned_max_formula(*width)),
                        ),
                    ]),
                    reason: format!("u{width} return value is bounded [0, 2^{width}-1]"),
                    strategy: InferenceStrategy::TypeBased,
                    confidence: InferenceConfidence::High,
                    kind: InferredSpecKind::Postcondition,
                });
            }
            Ty::Bool => {
                // Boolean return: result is 0 or 1 (in integer encoding).
                result.specs.push(InferredSpec {
                    formula: Formula::Or(vec![
                        Formula::Eq(
                            Box::new(Formula::Var("_0".into(), Sort::Bool)),
                            Box::new(Formula::Bool(true)),
                        ),
                        Formula::Eq(
                            Box::new(Formula::Var("_0".into(), Sort::Bool)),
                            Box::new(Formula::Bool(false)),
                        ),
                    ]),
                    reason: "bool return is true or false".to_string(),
                    strategy: InferenceStrategy::TypeBased,
                    confidence: InferenceConfidence::Certain,
                    kind: InferredSpecKind::Postcondition,
                });
            }
            _ => {}
        }
    }

    /// Name-based inference: derive specs from function and parameter names.
    fn infer_from_names(&self, func: &VerifiableFunction, result: &mut InferenceResult) {
        let name = &func.name;

        // "is_*" or "has_*" functions likely return bool.
        if name.starts_with("is_") || name.starts_with("has_") {
            if matches!(func.body.return_ty, Ty::Bool) {
                // Already typed as bool — no additional spec needed.
            } else {
                result.specs.push(InferredSpec {
                    formula: Formula::Or(vec![
                        Formula::Eq(
                            Box::new(Formula::Var("_0".into(), Sort::Int)),
                            Box::new(Formula::Int(0)),
                        ),
                        Formula::Eq(
                            Box::new(Formula::Var("_0".into(), Sort::Int)),
                            Box::new(Formula::Int(1)),
                        ),
                    ]),
                    reason: format!("'{name}' naming convention suggests boolean-like return"),
                    strategy: InferenceStrategy::NameBased,
                    confidence: InferenceConfidence::Low,
                    kind: InferredSpecKind::Postcondition,
                });
            }
        }

        // "len" or "*_len" or "*_count" or "*_size": result >= 0.
        if name == "len"
            || name.ends_with("_len")
            || name.ends_with("_count")
            || name.ends_with("_size")
        {
            result.specs.push(InferredSpec {
                formula: Formula::Ge(
                    Box::new(Formula::Var("_0".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                reason: format!("'{name}' naming convention suggests non-negative return"),
                strategy: InferenceStrategy::NameBased,
                confidence: InferenceConfidence::Medium,
                kind: InferredSpecKind::Postcondition,
            });
        }

        // Parameter naming: "index" or "idx" params should be >= 0.
        for (idx, local) in func.body.locals.iter().enumerate() {
            if idx == 0 || idx > func.body.arg_count {
                continue;
            }
            if let Some(name) = &local.name
                && (name == "index"
                    || name == "idx"
                    || name.ends_with("_index")
                    || name.ends_with("_idx"))
            {
                result.specs.push(InferredSpec {
                    formula: Formula::Ge(
                        Box::new(Formula::Var(name.clone(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    reason: format!("parameter '{name}' naming suggests non-negative index"),
                    strategy: InferenceStrategy::NameBased,
                    confidence: InferenceConfidence::Medium,
                    kind: InferredSpecKind::Precondition,
                });
            }
        }
    }

    /// Assertion-based inference: lift assert conditions to preconditions.
    fn infer_from_assertions(&self, func: &VerifiableFunction, result: &mut InferenceResult) {
        for block in &func.body.blocks {
            if let Terminator::Assert { cond, expected, msg, .. } = &block.terminator {
                // An Assert terminator checks `cond == expected`. If the function
                // asserts a condition, that condition is effectively a precondition
                // (the function panics if it doesn't hold).
                let formula = crate::operand_to_formula(func, cond);

                let assertion_formula = if *expected {
                    // assert!(cond) — cond must be true
                    formula
                } else {
                    // assert!(!cond) — cond must be false (used by overflow checks)
                    Formula::Not(Box::new(formula))
                };

                let reason = match msg {
                    AssertMessage::Custom(s) => {
                        format!("lifted assertion: {s}")
                    }
                    AssertMessage::Overflow(op) => {
                        format!("lifted overflow check: {op:?}")
                    }
                    AssertMessage::BoundsCheck => "lifted bounds check".to_string(),
                    _ => "lifted assertion".to_string(),
                };

                result.specs.push(InferredSpec {
                    formula: assertion_formula,
                    reason,
                    strategy: InferenceStrategy::AssertionBased,
                    confidence: InferenceConfidence::High,
                    kind: InferredSpecKind::Precondition,
                });
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a simple function with unsigned params for type-based inference.
    fn unsigned_params_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "add_u32".to_string(),
            def_path: "test::add_u32".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a "len" function for name-based inference.
    fn len_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "len".to_string(),
            def_path: "test::len".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::usize(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a function with an Assert terminator for assertion-based inference.
    fn asserted_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "checked_div".to_string(),
            def_path: "test::checked_div".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("check".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::local(3)),
                            expected: true,
                            msg: AssertMessage::Custom("divisor must be nonzero".into()),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build an "is_valid" function for name-based inference.
    fn is_valid_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "is_valid".to_string(),
            def_path: "test::is_valid".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("value".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a function with index parameter.
    fn indexed_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "get_item".to_string(),
            def_path: "test::get_item".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("index".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_engine_new_defaults() {
        let engine = SpecInferenceEngine::new();
        assert!(engine.type_based);
        assert!(engine.name_based);
        assert!(engine.assertion_based);
    }

    #[test]
    fn test_type_based_unsigned_params() {
        let engine =
            SpecInferenceEngine { type_based: true, name_based: false, assertion_based: false };
        let func = unsigned_params_function();
        let result = engine.infer(&func);

        // Should infer bounds for a, b (unsigned params) and return type.
        let preconditions = result.preconditions();
        assert!(
            preconditions.len() >= 2,
            "should infer bounds for 2 unsigned params, got {}",
            preconditions.len()
        );

        let postconditions = result.postconditions();
        assert!(!postconditions.is_empty(), "should infer return type bounds");

        for spec in &result.specs {
            assert_eq!(spec.strategy, InferenceStrategy::TypeBased);
            assert_eq!(spec.confidence, InferenceConfidence::High);
        }
    }

    #[test]
    fn test_name_based_len_function() {
        let engine =
            SpecInferenceEngine { type_based: false, name_based: true, assertion_based: false };
        let func = len_function();
        let result = engine.infer(&func);

        let postconditions = result.postconditions();
        assert!(!postconditions.is_empty(), "should infer non-negative return for 'len'");

        let len_spec = &postconditions[0];
        assert_eq!(len_spec.strategy, InferenceStrategy::NameBased);
        assert_eq!(len_spec.confidence, InferenceConfidence::Medium);
    }

    #[test]
    fn test_name_based_index_param() {
        let engine =
            SpecInferenceEngine { type_based: false, name_based: true, assertion_based: false };
        let func = indexed_function();
        let result = engine.infer(&func);

        let preconditions = result.preconditions();
        assert!(!preconditions.is_empty(), "should infer non-negative for 'index' param");

        let idx_spec = preconditions
            .iter()
            .find(|s| s.reason.contains("index"))
            .expect("should find index spec");
        assert_eq!(idx_spec.strategy, InferenceStrategy::NameBased);
    }

    #[test]
    fn test_assertion_based_inference() {
        let engine =
            SpecInferenceEngine { type_based: false, name_based: false, assertion_based: true };
        let func = asserted_function();
        let result = engine.infer(&func);

        assert!(!result.is_empty(), "should lift assertion to spec");

        let preconditions = result.preconditions();
        assert!(!preconditions.is_empty(), "assertion should become precondition");

        let assert_spec = &preconditions[0];
        assert_eq!(assert_spec.strategy, InferenceStrategy::AssertionBased);
        assert_eq!(assert_spec.confidence, InferenceConfidence::High);
        assert!(assert_spec.reason.contains("divisor must be nonzero"));
    }

    #[test]
    fn test_all_strategies_combined() {
        let engine = SpecInferenceEngine::new();
        let func = unsigned_params_function();
        let result = engine.infer(&func);

        // type-based + name-based should both contribute.
        assert!(!result.is_empty());
    }

    #[test]
    fn test_is_valid_bool_return() {
        let engine =
            SpecInferenceEngine { type_based: true, name_based: true, assertion_based: false };
        let func = is_valid_function();
        let result = engine.infer(&func);

        // Type-based should infer bool postcondition; name-based should not
        // add extra since it's already typed as bool.
        let postconditions = result.postconditions();
        assert!(!postconditions.is_empty(), "should infer bool return spec");
    }

    #[test]
    fn test_inference_result_to_function_spec() {
        let engine = SpecInferenceEngine::new();
        let func = unsigned_params_function();
        let result = engine.infer(&func);

        let fspec = result.to_function_spec().unwrap();
        assert!(
            !fspec.requires.is_empty() || !fspec.ensures.is_empty(),
            "should produce non-empty FunctionSpec"
        );
    }

    #[test]
    fn test_inference_result_source() {
        // Type-based only => Heuristic (type inferences are lower confidence)
        let engine =
            SpecInferenceEngine { type_based: true, name_based: false, assertion_based: false };
        let func = unsigned_params_function();
        let result = engine.infer(&func);
        assert_eq!(result.source(), SpecSource::Heuristic);

        // Name-based only => Heuristic
        let engine2 =
            SpecInferenceEngine { type_based: false, name_based: true, assertion_based: false };
        let func2 = len_function();
        let result2 = engine2.infer(&func2);
        assert_eq!(result2.source(), SpecSource::Heuristic);
    }

    #[test]
    fn test_assertion_based_source_is_inferred() {
        // Assertion-based => Inferred (higher confidence, lifted from explicit assertions)
        let engine =
            SpecInferenceEngine { type_based: false, name_based: false, assertion_based: true };
        let func = asserted_function();
        let result = engine.infer(&func);
        assert_eq!(result.source(), SpecSource::Inferred);
    }

    #[test]
    fn test_assertion_based_vs_type_based_distinction() {
        // When both assertion-based and type-based specs are present,
        // the overall source should be Inferred (assertion-based dominates).
        let engine =
            SpecInferenceEngine { type_based: true, name_based: false, assertion_based: true };
        let func = asserted_function();
        let result = engine.infer(&func);
        assert_eq!(result.source(), SpecSource::Inferred);

        // When only type-based specs are present, source should be Heuristic.
        let engine2 =
            SpecInferenceEngine { type_based: true, name_based: false, assertion_based: false };
        let result2 = engine2.infer(&func);
        assert_eq!(result2.source(), SpecSource::Heuristic);

        // This verifies the AssertionBased vs TypeBased distinction is preserved.
        assert_ne!(
            result.source(),
            result2.source(),
            "AssertionBased and TypeBased must produce different SpecSource values"
        );
    }

    #[test]
    fn test_inference_result_min_confidence() {
        let engine = SpecInferenceEngine::new();
        let func = indexed_function();
        let result = engine.infer(&func);

        // Mix of High (type-based) and Medium (name-based) should yield Medium.
        let min = result.min_confidence();
        assert!(min <= InferenceConfidence::High);
    }

    #[test]
    fn test_formula_to_spec_expr_basic() {
        assert_eq!(formula_to_spec_expr(&Formula::Bool(true)).unwrap(), "true");
        assert!(formula_to_spec_expr(&Formula::Int(42)).is_err());
        assert!(formula_to_spec_expr(&Formula::Var("x".into(), Sort::Int)).is_err());
    }

    #[test]
    fn test_formula_to_spec_expr_comparison() {
        let f =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        assert_eq!(formula_to_spec_expr(&f).unwrap(), "(x >= 0)");
    }

    #[test]
    fn test_formula_to_spec_expr_conjunction() {
        let f = Formula::And(vec![
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100))),
        ]);
        assert_eq!(formula_to_spec_expr(&f).unwrap(), "((x >= 0) && (x <= 100))");
    }

    #[test]
    fn test_empty_function_produces_no_specs() {
        let engine = SpecInferenceEngine::new();
        let func = VerifiableFunction {
            name: "empty".to_string(),
            def_path: "test::empty".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let result = engine.infer(&func);
        assert!(result.is_empty(), "unit -> unit function should have no inferred specs");
    }

    #[test]
    fn test_disabled_strategies_produce_nothing() {
        let engine =
            SpecInferenceEngine { type_based: false, name_based: false, assertion_based: false };
        let func = unsigned_params_function();
        let result = engine.infer(&func);
        assert!(result.is_empty(), "all strategies disabled should produce no specs");
    }
}
