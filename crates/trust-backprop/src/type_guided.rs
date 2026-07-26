//! Type-guided specification insertion.
//!
//! Analyzes function signatures to derive specification hints from types alone.
//! For example, `usize` parameters imply non-negative bounds, `Option<T>`
//! implies nullability checks, and `&mut` references imply lifetime constraints.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, LocalDecl, Sort, SpecSuggestion, Ty, VerifiableBody};

// ---------------------------------------------------------------------------
// Type patterns
// ---------------------------------------------------------------------------

/// A pattern recognized from a Rust type that implies verification constraints.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TypePattern {
    /// Numeric type with known bounds (min, max inclusive).
    Numeric { min: i128, max: i128, width: u32 },
    /// `Option<T>` — the value may be `None`.
    Optional { inner_name: String },
    /// Reference with a lifetime / mutability constraint.
    Reference { mutable: bool },
    /// Collection-like type (slice, array, Vec) with a length concept.
    Collection { has_known_length: bool, length: Option<u64> },
}

/// All type-derived constraints for a single function.
#[derive(Debug, Clone, Default)]
pub struct SignatureHints {
    /// Suggested preconditions derived from parameter types.
    pub requires: Vec<FormulaHint>,
    /// Suggested postconditions derived from the return type.
    pub ensures: Vec<FormulaHint>,
    /// Per-parameter pattern matches.
    pub parameter_patterns: Vec<(String, Vec<TypePattern>)>,
    /// Return-type pattern matches.
    pub return_patterns: Vec<TypePattern>,
}

/// A formula hint with provenance information.
#[derive(Debug, Clone)]
pub struct FormulaHint {
    /// The logical formula.
    pub formula: Formula,
    /// Human-readable explanation of why this formula was inferred.
    pub reason: String,
    /// Name of the parameter or return value that motivated it.
    pub source: String,
}

// ---------------------------------------------------------------------------
// TypeAnalyzer
// ---------------------------------------------------------------------------

/// Analyzes function signatures for specification hints.
#[derive(Debug, Default)]
pub struct TypeAnalyzer {
    /// Whether to infer bounds from unsigned integer types.
    pub infer_unsigned_bounds: bool,
    /// Whether to infer nullability from `Option` types.
    pub infer_nullability: bool,
    /// Whether to infer reference/lifetime constraints.
    pub infer_lifetime: bool,
    /// Whether to infer collection length constraints.
    pub infer_collection: bool,
}

impl TypeAnalyzer {
    /// Create a new analyzer with all inference strategies enabled.
    #[must_use]
    pub fn new() -> Self {
        Self {
            infer_unsigned_bounds: true,
            infer_nullability: true,
            infer_lifetime: true,
            infer_collection: true,
        }
    }

    /// Analyze a function body to produce signature hints.
    #[must_use]
    pub fn analyze(&self, body: &VerifiableBody) -> SignatureHints {
        let mut hints = SignatureHints::default();

        // Parameters are locals 1..=arg_count (local 0 is the return place).
        for local in body.locals.iter().take(body.arg_count + 1).skip(1) {
            let name = local.name.clone().unwrap_or_else(|| format!("_arg{}", local.index));
            let patterns = match_patterns(&local.ty);

            let requires = self.generate_requires_for_param(&name, &local.ty, &patterns);
            hints.requires.extend(requires);
            hints.parameter_patterns.push((name, patterns));
        }

        // Return type
        let ret_patterns = match_patterns(&body.return_ty);
        let ensures = self.generate_ensures_for_return(&body.return_ty, &ret_patterns);
        hints.ensures.extend(ensures);
        hints.return_patterns = ret_patterns;

        hints
    }

    /// Generate precondition hints for a single parameter.
    fn generate_requires_for_param(
        &self,
        name: &str,
        ty: &Ty,
        patterns: &[TypePattern],
    ) -> Vec<FormulaHint> {
        let mut out = Vec::new();

        for pat in patterns {
            match pat {
                TypePattern::Numeric { min, max, width } if self.infer_unsigned_bounds => {
                    out.extend(infer_bounds_from_type_inner(name, *min, *max, *width));
                }
                TypePattern::Optional { .. } if self.infer_nullability => {
                    if let Some(hint) = infer_nullability_hint(name, ty) {
                        out.push(hint);
                    }
                }
                TypePattern::Reference { mutable } if self.infer_lifetime => {
                    out.extend(infer_lifetime_hint(name, *mutable));
                }
                TypePattern::Collection { has_known_length, length } if self.infer_collection => {
                    out.extend(infer_collection_hint(name, *has_known_length, *length));
                }
                _ => {}
            }
        }
        out
    }

    /// Generate postcondition hints for the return type.
    fn generate_ensures_for_return(&self, _ty: &Ty, patterns: &[TypePattern]) -> Vec<FormulaHint> {
        let mut out = Vec::new();
        let name = "result";

        for pat in patterns {
            match pat {
                TypePattern::Numeric { min, max, width } if self.infer_unsigned_bounds => {
                    out.extend(infer_bounds_from_type_inner(name, *min, *max, *width));
                }
                TypePattern::Optional { .. } if self.infer_nullability => {
                    // For return types, note that the result may be None.
                    // This is informational rather than a constraint.
                }
                TypePattern::Collection { has_known_length, length } if self.infer_collection => {
                    out.extend(infer_collection_hint(name, *has_known_length, *length));
                }
                _ => {}
            }
        }
        out
    }
}

// ---------------------------------------------------------------------------
// Public API functions
// ---------------------------------------------------------------------------

/// Match a type against known patterns.
#[must_use]
pub fn match_patterns(ty: &Ty) -> Vec<TypePattern> {
    let mut patterns = Vec::new();
    match ty {
        Ty::Int { width, signed: false } => {
            let max = if *width >= 128 { i128::MAX } else { (1i128 << width) - 1 };
            patterns.push(TypePattern::Numeric { min: 0, max, width: *width });
        }
        Ty::Int { width, signed: true } => {
            let half = if *width >= 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 };
            let min = if *width >= 128 { i128::MIN } else { -(1i128 << (width - 1)) };
            patterns.push(TypePattern::Numeric { min, max: half, width: *width });
        }
        Ty::Float { .. } => {
            // Floats don't have simple integer bounds — skip for now.
        }
        Ty::Ref { mutable, inner } => {
            patterns.push(TypePattern::Reference { mutable: *mutable });
            // Also match inner type patterns.
            patterns.extend(match_patterns(inner));
        }
        Ty::Slice { .. } => {
            patterns.push(TypePattern::Collection { has_known_length: false, length: None });
        }
        Ty::Array { len, .. } => {
            patterns.push(TypePattern::Collection { has_known_length: true, length: Some(*len) });
        }
        Ty::Adt { name, .. } if is_option_type(name) => {
            patterns.push(TypePattern::Optional { inner_name: extract_inner_type_name(name) });
        }
        Ty::Adt { name, .. } if is_collection_type(name) => {
            patterns.push(TypePattern::Collection { has_known_length: false, length: None });
        }
        Ty::Tuple(elems) => {
            // Each element may have patterns — not directly actionable at the tuple level.
            for (i, elem) in elems.iter().enumerate() {
                let inner = match_patterns(elem);
                if !inner.is_empty() {
                    // We flatten inner patterns up (they'll carry context from the caller).
                    patterns.extend(inner);
                    let _ = i; // suppress unused warning
                }
            }
        }
        _ => {}
    }
    patterns
}

/// Infer bound formulas from a type.
#[must_use]
pub fn infer_bounds_from_type(name: &str, ty: &Ty) -> Vec<Formula> {
    let patterns = match_patterns(ty);
    patterns
        .iter()
        .filter_map(|p| match p {
            TypePattern::Numeric { min, max, width } => {
                Some(infer_bounds_from_type_inner(name, *min, *max, *width))
            }
            _ => None,
        })
        .flatten()
        .map(|h| h.formula)
        .collect()
}

/// Infer a nullability formula from an `Option<T>` type.
#[must_use]
pub fn infer_nullability(name: &str, ty: &Ty) -> Option<Formula> {
    infer_nullability_hint(name, ty).map(|h| h.formula)
}

/// Infer lifetime constraint formulas from a function signature's parameters.
#[must_use]
pub fn infer_lifetime_constraints(params: &[LocalDecl]) -> Vec<Formula> {
    params
        .iter()
        .filter_map(|local| {
            let name = local.name.as_deref().unwrap_or("_");
            if let Ty::Ref { mutable, .. } = &local.ty {
                Some(infer_lifetime_hint(name, *mutable))
            } else {
                None
            }
        })
        .flatten()
        .map(|h| h.formula)
        .collect()
}

/// Generate native `requires` suggestions from parameter types.
#[must_use]
pub fn generate_requires_from_types(body: &VerifiableBody) -> Vec<SpecSuggestion> {
    let analyzer = TypeAnalyzer::new();
    let hints = analyzer.analyze(body);
    hints.requires.into_iter().map(|h| hint_to_suggestion(&h, "requires")).collect()
}

/// Generate native `ensures` suggestions from return type (and optionally body analysis).
#[must_use]
pub fn generate_ensures_from_types(body: &VerifiableBody) -> Vec<SpecSuggestion> {
    let analyzer = TypeAnalyzer::new();
    let hints = analyzer.analyze(body);
    hints.ensures.into_iter().map(|h| hint_to_suggestion(&h, "ensures")).collect()
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Create bound formulas for a named variable with known numeric range.
fn infer_bounds_from_type_inner(name: &str, min: i128, max: i128, width: u32) -> Vec<FormulaHint> {
    let sort = Sort::BitVec(width);
    let var = Formula::Var(name.to_owned(), sort);
    let mut hints = Vec::new();

    // Lower bound (interesting only if min >= 0 for unsigned)
    if min >= 0 {
        hints.push(FormulaHint {
            formula: Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(min))),
            reason: format!("{name} is unsigned {width}-bit: always >= {min}"),
            source: name.to_owned(),
        });
    }

    // Upper bound
    hints.push(FormulaHint {
        formula: Formula::Le(Box::new(var), Box::new(Formula::Int(max))),
        reason: format!("{name} is {width}-bit: always <= {max}"),
        source: name.to_owned(),
    });

    hints
}

/// Infer nullability hint from an Option type.
fn infer_nullability_hint(name: &str, ty: &Ty) -> Option<FormulaHint> {
    match ty {
        Ty::Adt { name: adt_name, .. } if is_option_type(adt_name) => {
            // Create a formula expressing that the value may be None.
            // Represented as: !(name == None) i.e., "name is Some"
            let var = Formula::Var(name.to_owned(), Sort::Bool);
            Some(FormulaHint {
                formula: Formula::Or(vec![var.clone(), Formula::Not(Box::new(var))]),
                reason: format!("{name} is Option<_>: may be None"),
                source: name.to_owned(),
            })
        }
        _ => None,
    }
}

/// Infer lifetime-related hints for references.
fn infer_lifetime_hint(name: &str, _mutable: bool) -> Vec<FormulaHint> {
    let mut hints = Vec::new();
    let var = Formula::Var(name.to_owned(), Sort::Bool);

    // All references must be valid (non-null in the logical model).
    hints.push(FormulaHint {
        formula: Formula::Not(Box::new(Formula::Eq(
            Box::new(var.clone()),
            Box::new(Formula::Int(0)),
        ))),
        reason: format!("{name} is a reference: must be non-null"),
        source: name.to_owned(),
    });

    // `&mut` uniqueness needs alias/provenance context. Do not emit a `true`
    // placeholder, because backprop would turn it into a no-op spec.

    hints
}

/// Infer collection-length hints.
fn infer_collection_hint(
    name: &str,
    has_known_length: bool,
    length: Option<u64>,
) -> Vec<FormulaHint> {
    let mut hints = Vec::new();
    let len_var = Formula::Var(format!("{name}.len"), Sort::Int);

    // Length is always non-negative.
    hints.push(FormulaHint {
        formula: Formula::Ge(Box::new(len_var.clone()), Box::new(Formula::Int(0))),
        reason: format!("{name} collection length >= 0"),
        source: name.to_owned(),
    });

    if has_known_length && let Some(len) = length {
        hints.push(FormulaHint {
            formula: Formula::Eq(Box::new(len_var), Box::new(Formula::Int(len as i128))),
            reason: format!("{name} is a fixed-size array of length {len}"),
            source: name.to_owned(),
        });
    }

    hints
}

/// Check if an ADT name looks like `Option`.
fn is_option_type(name: &str) -> bool {
    name == "Option"
        || name.ends_with("::Option")
        || name.starts_with("Option<")
        || name.contains("::Option<")
}

/// Check if an ADT name looks like a collection (Vec, VecDeque, HashMap, etc.).
fn is_collection_type(name: &str) -> bool {
    let base = name.split('<').next().unwrap_or(name);
    let base = base.rsplit("::").next().unwrap_or(base);
    matches!(
        base,
        "Vec" | "VecDeque" | "HashMap" | "HashSet" | "BTreeMap" | "BTreeSet" | "LinkedList"
    )
}

/// Extract the inner type name from an Option-like ADT name.
fn extract_inner_type_name(name: &str) -> String {
    // "Option<Foo>" → "Foo", "std::option::Option<Bar>" → "Bar"
    if let Some(start) = name.find('<') {
        let end = name.rfind('>').unwrap_or(name.len());
        name[start + 1..end].to_owned()
    } else {
        "T".to_owned()
    }
}

/// Convert a `FormulaHint` into a `SpecSuggestion`.
fn hint_to_suggestion(hint: &FormulaHint, kind: &str) -> SpecSuggestion {
    use trust_types::{FairnessConstraint, LivenessProperty, PatternKind, TemporalOperator};

    SpecSuggestion::new(
        format!("type_guided_{kind}_{}", hint.source),
        LivenessProperty {
            name: format!("type_bound_{}", hint.source),
            operator: TemporalOperator::Always,
            predicate: hint.reason.clone(),
            consequent: None,
            fairness: vec![FairnessConstraint::Weak {
                action: "type_check".into(),
                vars: vec![hint.source.clone()],
            }],
        },
        0.95, // Type-derived constraints are high confidence.
        vec![hint.reason.clone()],
        PatternKind::custom(format!("type_guided_{kind}")),
        None,
    )
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{LocalDecl, Ty, VerifiableBody};

    fn make_body(params: Vec<LocalDecl>, return_ty: Ty) -> VerifiableBody {
        let arg_count = params.len();
        let mut locals = vec![LocalDecl { index: 0, ty: return_ty, name: Some("_return".into()) }];
        locals.extend(params);
        VerifiableBody { locals, blocks: vec![], arg_count, return_ty: Ty::Unit }
    }

    fn make_param(index: usize, name: &str, ty: Ty) -> LocalDecl {
        LocalDecl { index, ty, name: Some(name.into()) }
    }

    // -- Pattern matching tests --

    #[test]
    fn test_match_patterns_unsigned_int() {
        let patterns = match_patterns(&Ty::Int { width: 32, signed: false });
        assert_eq!(patterns.len(), 1);
        assert!(matches!(
            &patterns[0],
            TypePattern::Numeric { min: 0, max, width: 32 } if *max == (1i128 << 32) - 1
        ));
    }

    #[test]
    fn test_match_patterns_signed_int() {
        let patterns = match_patterns(&Ty::Int { width: 16, signed: true });
        assert_eq!(patterns.len(), 1);
        assert!(matches!(
            &patterns[0],
            TypePattern::Numeric { min, max, width: 16 }
                if *min == -(1i128 << 15) && *max == (1i128 << 15) - 1
        ));
    }

    #[test]
    fn test_match_patterns_u64() {
        let patterns = match_patterns(&Ty::usize());
        assert_eq!(patterns.len(), 1);
        assert!(matches!(&patterns[0], TypePattern::Numeric { min: 0, .. }));
    }

    #[test]
    fn test_match_patterns_option_adt() {
        let ty = Ty::Adt {
            variants: Vec::new(),
            name: "Option<u32>".into(),
            fields: vec![],
            disc_index_safe: false,
         faithful_enum_repr: None, layout: None, enum_layout: None, adt_kind: None };
        let patterns = match_patterns(&ty);
        assert_eq!(patterns.len(), 1);
        assert!(matches!(
            &patterns[0],
            TypePattern::Optional { inner_name } if inner_name == "u32"
        ));
    }

    #[test]
    fn test_match_patterns_reference() {
        let ty = Ty::Ref { mutable: true, inner: Box::new(Ty::Int { width: 64, signed: false }) };
        let patterns = match_patterns(&ty);
        assert_eq!(patterns.len(), 2);
        assert!(matches!(&patterns[0], TypePattern::Reference { mutable: true }));
        assert!(matches!(&patterns[1], TypePattern::Numeric { min: 0, .. }));
    }

    #[test]
    fn test_match_patterns_slice() {
        let ty = Ty::Slice { elem: Box::new(Ty::Bool) };
        let patterns = match_patterns(&ty);
        assert_eq!(patterns.len(), 1);
        assert!(matches!(
            &patterns[0],
            TypePattern::Collection { has_known_length: false, length: None }
        ));
    }

    #[test]
    fn test_match_patterns_array() {
        let ty = Ty::Array { elem: Box::new(Ty::u32()), len: 10 };
        let patterns = match_patterns(&ty);
        assert_eq!(patterns.len(), 1);
        assert!(matches!(
            &patterns[0],
            TypePattern::Collection { has_known_length: true, length: Some(10) }
        ));
    }

    #[test]
    fn test_match_patterns_vec_adt() {
        let ty = Ty::Adt {
            variants: Vec::new(),
            name: "Vec<i32>".into(),
            fields: vec![],
            disc_index_safe: false,
         faithful_enum_repr: None, layout: None, enum_layout: None, adt_kind: None };
        let patterns = match_patterns(&ty);
        assert_eq!(patterns.len(), 1);
        assert!(matches!(
            &patterns[0],
            TypePattern::Collection { has_known_length: false, length: None }
        ));
    }

    #[test]
    fn test_match_patterns_unit_and_never() {
        assert!(match_patterns(&Ty::Unit).is_empty());
        assert!(match_patterns(&Ty::Never).is_empty());
    }

    #[test]
    fn test_match_patterns_bool() {
        assert!(match_patterns(&Ty::Bool).is_empty());
    }

    // -- Inference function tests --

    #[test]
    fn test_infer_bounds_usize() {
        let formulas = infer_bounds_from_type("x", &Ty::usize());
        assert_eq!(formulas.len(), 2); // >= 0 and <= max
        // First formula should be x >= 0
        assert!(matches!(&formulas[0], Formula::Ge(_, _)));
        // Second should be x <= max
        assert!(matches!(&formulas[1], Formula::Le(_, _)));
    }

    #[test]
    fn test_infer_bounds_i32() {
        let formulas = infer_bounds_from_type("y", &Ty::i32());
        // Signed: only upper bound (min is negative, so no >= 0 hint)
        assert_eq!(formulas.len(), 1);
        assert!(matches!(&formulas[0], Formula::Le(_, _)));
    }

    #[test]
    fn test_infer_nullability_option() {
        let ty = Ty::Adt {
            variants: Vec::new(),
            name: "Option<String>".into(),
            fields: vec![],
            disc_index_safe: false,
         faithful_enum_repr: None, layout: None, enum_layout: None, adt_kind: None };
        let formula = infer_nullability("val", &ty);
        assert!(formula.is_some());
    }

    #[test]
    fn test_infer_nullability_non_option() {
        let formula = infer_nullability("x", &Ty::u32());
        assert!(formula.is_none());
    }

    #[test]
    fn test_infer_lifetime_constraints_mixed() {
        let params = vec![
            make_param(
                1,
                "data",
                Ty::Ref { mutable: false, inner: Box::new(Ty::Int { width: 8, signed: false }) },
            ),
            make_param(2, "count", Ty::Int { width: 32, signed: false }),
            make_param(
                3,
                "out",
                Ty::Ref { mutable: true, inner: Box::new(Ty::Int { width: 64, signed: false }) },
            ),
        ];
        let formulas = infer_lifetime_constraints(&params);
        // data: 1 non-null hint, out: 1 non-null. `&mut` uniqueness is not
        // emitted as a `true` placeholder because that would be a no-op spec.
        assert_eq!(formulas.len(), 2);
        assert!(!formulas.iter().any(|formula| matches!(formula, Formula::Bool(true))));
    }

    #[test]
    fn test_mut_ref_lifetime_does_not_emit_true_placeholder() {
        let params = vec![make_param(
            1,
            "out",
            Ty::Ref { mutable: true, inner: Box::new(Ty::Int { width: 64, signed: false }) },
        )];

        let formulas = infer_lifetime_constraints(&params);
        assert_eq!(formulas.len(), 1);
        assert!(
            !formulas.iter().any(|formula| matches!(formula, Formula::Bool(true))),
            "backprop must not turn unmodeled &mut uniqueness into a no-op formula"
        );
    }

    // -- Analyzer integration tests --

    #[test]
    fn test_analyzer_simple_unsigned_param() {
        let body =
            make_body(vec![make_param(1, "n", Ty::Int { width: 64, signed: false })], Ty::Unit);
        let analyzer = TypeAnalyzer::new();
        let hints = analyzer.analyze(&body);

        assert!(!hints.requires.is_empty());
        assert_eq!(hints.parameter_patterns.len(), 1);
        assert_eq!(hints.parameter_patterns[0].0, "n");
    }

    #[test]
    fn test_analyzer_option_param() {
        let body = make_body(
            vec![make_param(
                1,
                "maybe",
                Ty::Adt {
                    variants: Vec::new(),
                    name: "Option<u32>".into(),
                    fields: vec![],
                    disc_index_safe: false,
                 faithful_enum_repr: None, layout: None, enum_layout: None, adt_kind: None },
            )],
            Ty::Unit,
        );
        let analyzer = TypeAnalyzer::new();
        let hints = analyzer.analyze(&body);

        assert!(!hints.requires.is_empty());
        // Should have an Optional pattern
        assert!(
            hints.parameter_patterns[0].1.iter().any(|p| matches!(p, TypePattern::Optional { .. }))
        );
    }

    #[test]
    fn test_analyzer_return_type_unsigned() {
        let body = make_body(vec![], Ty::Int { width: 32, signed: false });
        // Override return_ty properly
        let body = VerifiableBody { return_ty: Ty::Int { width: 32, signed: false }, ..body };
        let analyzer = TypeAnalyzer::new();
        let hints = analyzer.analyze(&body);

        assert!(!hints.ensures.is_empty());
        assert!(!hints.return_patterns.is_empty());
    }

    #[test]
    fn test_analyzer_complex_signature() {
        let body = make_body(
            vec![
                make_param(
                    1,
                    "data",
                    Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Slice {
                            elem: Box::new(Ty::Int { width: 8, signed: false }),
                        }),
                    },
                ),
                make_param(2, "index", Ty::Int { width: 64, signed: false }),
                make_param(
                    3,
                    "default",
                    Ty::Adt {
                        variants: Vec::new(),
                        name: "Option<u8>".into(),
                        fields: vec![],
                        disc_index_safe: false,
                     faithful_enum_repr: None, layout: None, enum_layout: None, adt_kind: None },
                ),
            ],
            Ty::Int { width: 8, signed: false },
        );
        let body = VerifiableBody { return_ty: Ty::Int { width: 8, signed: false }, ..body };
        let analyzer = TypeAnalyzer::new();
        let hints = analyzer.analyze(&body);

        // data: reference + collection, index: numeric bounds, default: optional
        assert_eq!(hints.parameter_patterns.len(), 3);
        assert!(hints.requires.len() >= 3);
        assert!(!hints.ensures.is_empty());
    }

    #[test]
    fn test_analyzer_disabled_strategies() {
        let body =
            make_body(vec![make_param(1, "n", Ty::Int { width: 32, signed: false })], Ty::Unit);
        let analyzer = TypeAnalyzer {
            infer_unsigned_bounds: false,
            infer_nullability: false,
            infer_lifetime: false,
            infer_collection: false,
        };
        let hints = analyzer.analyze(&body);
        assert!(hints.requires.is_empty());
    }

    // -- Spec suggestion generation tests --

    #[test]
    fn test_generate_requires_from_types() {
        let body = make_body(
            vec![
                make_param(1, "a", Ty::Int { width: 64, signed: false }),
                make_param(2, "b", Ty::Int { width: 64, signed: false }),
            ],
            Ty::Int { width: 64, signed: false },
        );
        let suggestions = generate_requires_from_types(&body);
        assert!(!suggestions.is_empty());
        assert!(suggestions.iter().all(|s| s.id.contains("type_guided_requires")));
    }

    #[test]
    fn test_generate_ensures_from_types() {
        let body = VerifiableBody {
            locals: vec![LocalDecl {
                index: 0,
                ty: Ty::Int { width: 32, signed: false },
                name: Some("_return".into()),
            }],
            blocks: vec![],
            arg_count: 0,
            return_ty: Ty::Int { width: 32, signed: false },
        };
        let suggestions = generate_ensures_from_types(&body);
        assert!(!suggestions.is_empty());
        assert!(suggestions.iter().all(|s| s.id.contains("type_guided_ensures")));
    }

    // -- Helper function tests --

    #[test]
    fn test_is_option_type_variants() {
        assert!(is_option_type("Option"));
        assert!(is_option_type("Option<u32>"));
        assert!(is_option_type("std::option::Option"));
        assert!(is_option_type("core::option::Option<String>"));
        assert!(!is_option_type("OptionBuilder"));
        assert!(!is_option_type("MyOption"));
    }

    #[test]
    fn test_is_collection_type_variants() {
        assert!(is_collection_type("Vec<u32>"));
        assert!(is_collection_type("std::collections::HashMap<K, V>"));
        assert!(is_collection_type("VecDeque<T>"));
        assert!(is_collection_type("HashSet<T>"));
        assert!(is_collection_type("BTreeMap<K, V>"));
        assert!(is_collection_type("BTreeSet<T>"));
        assert!(is_collection_type("LinkedList<T>"));
        assert!(!is_collection_type("String"));
        assert!(!is_collection_type("MyVec"));
    }

    #[test]
    fn test_extract_inner_type_name() {
        assert_eq!(extract_inner_type_name("Option<u32>"), "u32");
        assert_eq!(extract_inner_type_name("std::option::Option<String>"), "String");
        assert_eq!(extract_inner_type_name("Option"), "T");
    }

    #[test]
    fn test_match_patterns_tuple() {
        let ty = Ty::Tuple(vec![Ty::Int { width: 32, signed: false }, Ty::Bool]);
        let patterns = match_patterns(&ty);
        // The u32 element should produce a Numeric pattern; Bool produces nothing.
        assert_eq!(patterns.len(), 1);
        assert!(matches!(&patterns[0], TypePattern::Numeric { .. }));
    }

    #[test]
    fn test_match_patterns_nested_ref_slice() {
        let ty = Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) }),
        };
        let patterns = match_patterns(&ty);
        // Reference + Collection (from inner slice)
        assert_eq!(patterns.len(), 2);
        assert!(matches!(&patterns[0], TypePattern::Reference { mutable: false }));
        assert!(matches!(&patterns[1], TypePattern::Collection { has_known_length: false, .. }));
    }

    #[test]
    fn test_u128_bounds() {
        let patterns = match_patterns(&Ty::Int { width: 128, signed: false });
        assert_eq!(patterns.len(), 1);
        match &patterns[0] {
            TypePattern::Numeric { min, max, width } => {
                assert_eq!(*min, 0);
                assert_eq!(*max, i128::MAX);
                assert_eq!(*width, 128);
            }
            _ => panic!("expected Numeric pattern"),
        }
    }

    #[test]
    fn test_i128_bounds() {
        let patterns = match_patterns(&Ty::Int { width: 128, signed: true });
        assert_eq!(patterns.len(), 1);
        match &patterns[0] {
            TypePattern::Numeric { min, max, width } => {
                assert_eq!(*min, i128::MIN);
                assert_eq!(*max, i128::MAX);
                assert_eq!(*width, 128);
            }
            _ => panic!("expected Numeric pattern"),
        }
    }
}
