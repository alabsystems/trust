// trust-strengthen/template_match.rs: Signature-based template matching
//
// Matches function signatures against common patterns (getter, setter,
// constructor, validator, converter) and instantiates spec templates
// with concrete parameter names. LLM-free, fast, deterministic.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use crate::heuristic::FunctionSignature;
use crate::proposer::{Proposal, ProposalKind};
use crate::templates::{SpecTemplate, SpecTemplateKind, instantiate_template};

/// A function category recognized from naming and signature patterns.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FunctionCategory {
    /// Getter: `get_*`, `*_of`, returns a value, typically 0-1 params.
    Getter,
    /// Setter: `set_*`, `with_*`, takes a value, returns Self or ().
    Setter,
    /// Constructor: `new`, `create_*`, `build_*`, `from_*`.
    Constructor,
    /// Validator: `is_*`, `has_*`, `check_*`, `validate_*`, returns bool.
    Validator,
    /// Converter: `to_*`, `into_*`, `as_*`, `from_*`.
    Converter,
    /// Predicate: returns bool, name suggests a condition.
    Predicate,
    /// Finder: `find_*`, `search_*`, `lookup_*`, returns Option.
    Finder,
    /// Accumulator: `sum_*`, `count_*`, `total_*`, returns numeric.
    Accumulator,
}

impl FunctionCategory {
    /// Human-readable description.
    #[must_use]
    pub fn description(self) -> &'static str {
        match self {
            Self::Getter => "getter function",
            Self::Setter => "setter function",
            Self::Constructor => "constructor",
            Self::Validator => "validator / predicate",
            Self::Converter => "type converter",
            Self::Predicate => "boolean predicate",
            Self::Finder => "search / lookup",
            Self::Accumulator => "accumulator / aggregator",
        }
    }
}

/// Result of matching a function signature against known patterns.
#[derive(Debug, Clone)]
pub struct TemplateMatchResult {
    /// The matched category.
    pub category: FunctionCategory,
    /// Confidence of the match (0.0-1.0).
    pub confidence: f64,
    /// Spec proposals instantiated from templates.
    pub proposals: Vec<Proposal>,
}

/// Classify a function signature into a category.
///
/// Returns the best-matching category with confidence, or None.
#[must_use]
pub fn classify_function(sig: &FunctionSignature) -> Option<(FunctionCategory, f64)> {
    let lower = sig.name.to_lowercase();
    let ret = sig.return_type.as_deref().unwrap_or("");

    let mut candidates: Vec<(FunctionCategory, f64)> = Vec::new();

    // Getter patterns
    if (lower.starts_with("get_") || lower.starts_with("fetch_") || lower.ends_with("_of"))
        && !ret.is_empty()
        && ret != "()"
    {
        candidates.push((FunctionCategory::Getter, 0.8));
    }

    // Setter patterns
    if (lower.starts_with("set_") || lower.starts_with("with_")) && !sig.params.is_empty() {
        let conf = if ret == "()" || ret.contains("Self") || ret.is_empty() { 0.85 } else { 0.65 };
        candidates.push((FunctionCategory::Setter, conf));
    }

    // Constructor patterns
    if lower == "new"
        || lower.starts_with("create_")
        || lower.starts_with("build_")
        || (lower.starts_with("from_") && !lower.contains("str"))
    {
        candidates.push((FunctionCategory::Constructor, 0.85));
    }

    // Validator patterns
    if (lower.starts_with("is_")
        || lower.starts_with("has_")
        || lower.starts_with("check_")
        || lower.starts_with("validate_"))
        && ret.trim() == "bool"
    {
        candidates.push((FunctionCategory::Validator, 0.9));
    }

    // Converter patterns
    if lower.starts_with("to_")
        || lower.starts_with("into_")
        || lower.starts_with("as_")
        || lower.starts_with("from_str")
    {
        candidates.push((FunctionCategory::Converter, 0.8));
    }

    // Predicate (returns bool but not explicitly a validator name)
    let is_validator = candidates.iter().any(|(c, _)| *c == FunctionCategory::Validator);
    if ret.trim() == "bool" && !is_validator {
        candidates.push((FunctionCategory::Predicate, 0.6));
    }

    // Finder patterns
    if (lower.starts_with("find_") || lower.starts_with("search_") || lower.starts_with("lookup_"))
        && ret.starts_with("Option<")
    {
        candidates.push((FunctionCategory::Finder, 0.85));
    }

    // Accumulator patterns
    if (lower.starts_with("sum") || lower.starts_with("count") || lower.starts_with("total"))
        && is_numeric_ret(ret)
    {
        candidates.push((FunctionCategory::Accumulator, 0.75));
    }

    // Return the highest confidence match
    candidates.into_iter().max_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal))
}

/// Match a function signature against templates and produce proposals.
///
/// Combines category classification with template instantiation to produce
/// concrete spec proposals with real parameter names.
#[must_use]
pub fn match_and_propose(sig: &FunctionSignature) -> Vec<TemplateMatchResult> {
    let mut results = Vec::new();

    if let Some((category, confidence)) = classify_function(sig) {
        let proposals = generate_proposals_for_category(sig, category, confidence);
        if !proposals.is_empty() {
            results.push(TemplateMatchResult { category, confidence, proposals });
        }
    }

    results
}

/// Generate proposals for a specific function category.
fn generate_proposals_for_category(
    sig: &FunctionSignature,
    category: FunctionCategory,
    base_confidence: f64,
) -> Vec<Proposal> {
    match category {
        FunctionCategory::Getter => getter_proposals(sig, base_confidence),
        FunctionCategory::Setter => setter_proposals(sig, base_confidence),
        FunctionCategory::Constructor => constructor_proposals(sig, base_confidence),
        FunctionCategory::Validator => validator_proposals(sig, base_confidence),
        FunctionCategory::Converter => converter_proposals(sig, base_confidence),
        FunctionCategory::Predicate => predicate_proposals(sig, base_confidence),
        FunctionCategory::Finder => finder_proposals(sig, base_confidence),
        FunctionCategory::Accumulator => accumulator_proposals(sig, base_confidence),
    }
}

fn getter_proposals(sig: &FunctionSignature, confidence: f64) -> Vec<Proposal> {
    let mut proposals = Vec::new();

    // Getter should not modify state (pure function)
    proposals.push(Proposal {
        function_path: sig.path.clone(),
        function_name: sig.name.clone(),
        kind: ProposalKind::AddPostcondition {
            spec_body: "self is unchanged (pure getter)".to_string(),
        },
        confidence: confidence * 0.9,
        rationale: format!("Getter `{}`: should be a pure function with no side effects", sig.name),
    });

    // If it takes an index-like param, add bounds check
    for (pname, pty) in &sig.params {
        if pty.trim() == "usize" && is_likely_index(pname) {
            proposals.push(Proposal {
                function_path: sig.path.clone(),
                function_name: sig.name.clone(),
                kind: ProposalKind::AddPrecondition { spec_body: format!("{pname} < self.len()") },
                confidence,
                rationale: format!(
                    "Getter `{}`: index parameter `{pname}` must be in bounds",
                    sig.name
                ),
            });
        }
    }

    proposals
}

fn setter_proposals(sig: &FunctionSignature, confidence: f64) -> Vec<Proposal> {
    let mut proposals = Vec::new();

    // Extract the field name from set_* pattern
    let field = sig
        .name
        .strip_prefix("set_")
        .or_else(|| sig.name.strip_prefix("with_"))
        .unwrap_or(&sig.name);

    // Value parameter (last non-self param)
    if let Some((val_name, _)) = sig.params.last() {
        proposals.push(Proposal {
            function_path: sig.path.clone(),
            function_name: sig.name.clone(),
            kind: ProposalKind::AddPostcondition {
                spec_body: format!("self.{field} == {val_name}"),
            },
            confidence,
            rationale: format!(
                "Setter `{}`: after setting, field `{field}` should equal `{val_name}`",
                sig.name
            ),
        });
    }

    proposals
}

fn constructor_proposals(sig: &FunctionSignature, confidence: f64) -> Vec<Proposal> {
    let mut proposals = Vec::new();

    // Constructor should produce a valid instance
    proposals.push(Proposal {
        function_path: sig.path.clone(),
        function_name: sig.name.clone(),
        kind: ProposalKind::AddPostcondition {
            spec_body: "result satisfies type invariant".to_string(),
        },
        confidence: confidence * 0.85,
        rationale: format!(
            "Constructor `{}`: returned value must satisfy the type's invariant",
            sig.name
        ),
    });

    // Constructor params should be reflected in the output
    for (pname, _) in &sig.params {
        proposals.push(Proposal {
            function_path: sig.path.clone(),
            function_name: sig.name.clone(),
            kind: ProposalKind::AddPostcondition {
                spec_body: format!("result.{pname} == {pname}"),
            },
            confidence: confidence * 0.7,
            rationale: format!(
                "Constructor `{}`: field `{pname}` should be initialized from parameter",
                sig.name
            ),
        });
    }

    proposals
}

fn validator_proposals(sig: &FunctionSignature, confidence: f64) -> Vec<Proposal> {
    let mut proposals = Vec::new();

    // Validator is a pure function
    proposals.push(Proposal {
        function_path: sig.path.clone(),
        function_name: sig.name.clone(),
        kind: ProposalKind::AddPostcondition {
            spec_body: "self is unchanged (pure predicate)".to_string(),
        },
        confidence: confidence * 0.85,
        rationale: format!("Validator `{}`: should not modify state", sig.name),
    });

    // Validator should be deterministic
    proposals.push(Proposal {
        function_path: sig.path.clone(),
        function_name: sig.name.clone(),
        kind: ProposalKind::AddPostcondition {
            spec_body: "result is deterministic for same input".to_string(),
        },
        confidence: confidence * 0.8,
        rationale: format!(
            "Validator `{}`: same input should always produce same result",
            sig.name
        ),
    });

    proposals
}

fn converter_proposals(sig: &FunctionSignature, confidence: f64) -> Vec<Proposal> {
    let mut proposals = Vec::new();

    let ret = sig.return_type.as_deref().unwrap_or("");

    // Result-returning converter: Ok path is valid
    if ret.starts_with("Result<") {
        proposals.push(Proposal {
            function_path: sig.path.clone(),
            function_name: sig.name.clone(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "result.is_ok() ==> output represents same value".to_string(),
            },
            confidence,
            rationale: format!(
                "Converter `{}`: successful conversion preserves semantic value",
                sig.name
            ),
        });
    } else {
        // Non-fallible converter: roundtrip property
        proposals.push(Proposal {
            function_path: sig.path.clone(),
            function_name: sig.name.clone(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "result represents the same semantic value as input".to_string(),
            },
            confidence: confidence * 0.85,
            rationale: format!("Converter `{}`: conversion preserves meaning", sig.name),
        });
    }

    // If converting from a narrower type, no information loss
    if sig.name.starts_with("from_") || sig.name.starts_with("into_") {
        proposals.push(Proposal {
            function_path: sig.path.clone(),
            function_name: sig.name.clone(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "conversion is lossless or error is returned".to_string(),
            },
            confidence: confidence * 0.7,
            rationale: format!(
                "Converter `{}`: should either succeed losslessly or report error",
                sig.name
            ),
        });
    }

    proposals
}

fn predicate_proposals(sig: &FunctionSignature, confidence: f64) -> Vec<Proposal> {
    vec![Proposal {
        function_path: sig.path.clone(),
        function_name: sig.name.clone(),
        kind: ProposalKind::AddPostcondition {
            spec_body: "result == (condition holds)".to_string(),
        },
        confidence: confidence * 0.85,
        rationale: format!("Predicate `{}`: bool return encodes a condition", sig.name),
    }]
}

fn finder_proposals(sig: &FunctionSignature, confidence: f64) -> Vec<Proposal> {
    let mut proposals = Vec::new();

    // None means not found
    proposals.push(Proposal {
        function_path: sig.path.clone(),
        function_name: sig.name.clone(),
        kind: ProposalKind::AddPostcondition {
            spec_body: "result.is_none() ==> element not present in collection".to_string(),
        },
        confidence,
        rationale: format!("Finder `{}`: None means the element was not found", sig.name),
    });

    // Some means found and valid
    proposals.push(Proposal {
        function_path: sig.path.clone(),
        function_name: sig.name.clone(),
        kind: ProposalKind::AddPostcondition {
            spec_body: "result.is_some() ==> returned element matches search criteria".to_string(),
        },
        confidence: confidence * 0.9,
        rationale: format!("Finder `{}`: Some contains an element matching the query", sig.name),
    });

    proposals
}

fn accumulator_proposals(sig: &FunctionSignature, confidence: f64) -> Vec<Proposal> {
    let mut proposals = Vec::new();

    // Non-empty precondition if taking a slice
    let has_slice = sig.params.iter().any(|(_, ty)| {
        let t = ty.trim();
        t.starts_with("&[") || t.starts_with("&mut [") || t.starts_with("Vec<")
    });

    if has_slice
        && let Some((name, _)) = sig.params.iter().find(|(_, ty)| {
            let t = ty.trim();
            t.starts_with("&[") || t.starts_with("&mut [") || t.starts_with("Vec<")
        })
    {
        proposals.push(Proposal {
            function_path: sig.path.clone(),
            function_name: sig.name.clone(),
            kind: ProposalKind::AddPrecondition { spec_body: format!("!{name}.is_empty()") },
            confidence: confidence * 0.8,
            rationale: format!(
                "Accumulator `{}`: collection `{name}` should be non-empty",
                sig.name
            ),
        });
    }

    // Result >= 0 for unsigned accumulators
    if let Some(ref ret) = sig.return_type
        && is_unsigned_type(ret.trim())
    {
        proposals.push(Proposal {
            function_path: sig.path.clone(),
            function_name: sig.name.clone(),
            kind: ProposalKind::AddPostcondition { spec_body: "result >= 0".to_string() },
            confidence: confidence * 0.9,
            rationale: format!("Accumulator `{}`: result is non-negative", sig.name),
        });
    }

    proposals
}

/// Build template-instantiated proposal from a template and bindings.
///
/// Returns None if required template parameters are missing.
#[must_use]
pub fn proposal_from_template(
    sig: &FunctionSignature,
    template: &SpecTemplate,
    bindings: &FxHashMap<String, String>,
    confidence: f64,
    rationale: &str,
) -> Option<Proposal> {
    let spec_body = instantiate_template(template, bindings)?;

    let kind = match template.spec_kind {
        SpecTemplateKind::Precondition => ProposalKind::AddPrecondition { spec_body },
        SpecTemplateKind::Postcondition => ProposalKind::AddPostcondition { spec_body },
        SpecTemplateKind::Invariant => ProposalKind::AddInvariant { spec_body },
    };

    Some(Proposal {
        function_path: sig.path.clone(),
        function_name: sig.name.clone(),
        kind,
        confidence,
        rationale: rationale.to_string(),
    })
}

// --- Utility functions ---

fn is_likely_index(name: &str) -> bool {
    let lower = name.to_lowercase();
    lower == "i"
        || lower == "j"
        || lower == "k"
        || lower == "idx"
        || lower == "index"
        || lower == "pos"
        || lower == "offset"
        || lower.ends_with("_idx")
        || lower.ends_with("_index")
}

fn is_numeric_ret(ty: &str) -> bool {
    let t = ty.trim();
    matches!(
        t,
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "f32"
            | "f64"
    )
}

fn is_unsigned_type(ty: &str) -> bool {
    matches!(ty, "u8" | "u16" | "u32" | "u64" | "u128" | "usize")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_sig(
        name: &str,
        params: Vec<(&str, &str)>,
        return_type: Option<&str>,
    ) -> FunctionSignature {
        FunctionSignature {
            path: format!("test::{name}"),
            name: name.into(),
            params: params.into_iter().map(|(n, t)| (n.into(), t.into())).collect(),
            return_type: return_type.map(Into::into),
        }
    }

    // --- classify_function ---

    #[test]
    fn test_classify_getter() {
        let sig = make_sig("get_name", vec![], Some("&str"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Getter));
    }

    #[test]
    fn test_classify_fetch_getter() {
        let sig = make_sig("fetch_data", vec![], Some("Vec<u8>"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Getter));
    }

    #[test]
    fn test_classify_setter() {
        let sig = make_sig("set_name", vec![("name", "&str")], Some("()"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Setter));
    }

    #[test]
    fn test_classify_with_setter() {
        let sig = make_sig("with_timeout", vec![("timeout", "Duration")], Some("Self"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Setter));
    }

    #[test]
    fn test_classify_constructor_new() {
        let sig = make_sig("new", vec![("capacity", "usize")], Some("Self"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Constructor));
    }

    #[test]
    fn test_classify_constructor_create() {
        let sig = make_sig("create_config", vec![("path", "&str")], Some("Config"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Constructor));
    }

    #[test]
    fn test_classify_constructor_build() {
        let sig = make_sig("build_widget", vec![], Some("Widget"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Constructor));
    }

    #[test]
    fn test_classify_validator() {
        let sig = make_sig("is_valid", vec![], Some("bool"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Validator));
    }

    #[test]
    fn test_classify_has_validator() {
        let sig = make_sig("has_permission", vec![("user", "&User")], Some("bool"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Validator));
    }

    #[test]
    fn test_classify_check_validator() {
        let sig = make_sig("check_bounds", vec![("idx", "usize")], Some("bool"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Validator));
    }

    #[test]
    fn test_classify_converter_to() {
        let sig = make_sig("to_string", vec![], Some("String"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Converter));
    }

    #[test]
    fn test_classify_converter_into() {
        let sig = make_sig("into_inner", vec![], Some("T"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Converter));
    }

    #[test]
    fn test_classify_converter_as() {
        let sig = make_sig("as_bytes", vec![], Some("&[u8]"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Converter));
    }

    #[test]
    fn test_classify_finder() {
        let sig = make_sig("find_user", vec![("id", "u64")], Some("Option<User>"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Finder));
    }

    #[test]
    fn test_classify_search_finder() {
        let sig = make_sig("search_items", vec![("query", "&str")], Some("Option<Item>"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Finder));
    }

    #[test]
    fn test_classify_accumulator_sum() {
        let sig = make_sig("sum_values", vec![("data", "&[f64]")], Some("f64"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Accumulator));
    }

    #[test]
    fn test_classify_accumulator_count() {
        let sig = make_sig("count_items", vec![("items", "&[Item]")], Some("usize"));
        let result = classify_function(&sig);
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Accumulator));
    }

    #[test]
    fn test_classify_unknown_returns_none() {
        let sig = make_sig("frobulate", vec![("x", "Widget")], Some("Sprocket"));
        let result = classify_function(&sig);
        assert!(result.is_none());
    }

    #[test]
    fn test_classify_predicate_generic_bool() {
        let sig = make_sig("should_retry", vec![], Some("bool"));
        let result = classify_function(&sig);
        // Not a validator (no is_/has_/check_ prefix), so falls to Predicate
        assert_eq!(result.map(|(c, _)| c), Some(FunctionCategory::Predicate));
    }

    // --- match_and_propose ---

    #[test]
    fn test_match_and_propose_getter() {
        let sig = make_sig("get_value", vec![("idx", "usize")], Some("i32"));
        let results = match_and_propose(&sig);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].category, FunctionCategory::Getter);
        assert!(!results[0].proposals.is_empty());
    }

    #[test]
    fn test_match_and_propose_setter() {
        let sig = make_sig("set_name", vec![("name", "String")], Some("()"));
        let results = match_and_propose(&sig);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].category, FunctionCategory::Setter);
        let has_field_post = results[0].proposals.iter().any(|p| {
            if let ProposalKind::AddPostcondition { ref spec_body } = p.kind {
                spec_body.contains("name")
            } else {
                false
            }
        });
        assert!(has_field_post, "setter should produce field-update postcondition");
    }

    #[test]
    fn test_match_and_propose_constructor() {
        let sig = make_sig("new", vec![("capacity", "usize"), ("name", "&str")], Some("Self"));
        let results = match_and_propose(&sig);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].category, FunctionCategory::Constructor);
        // Should have invariant + per-field proposals
        assert!(results[0].proposals.len() >= 3);
    }

    #[test]
    fn test_match_and_propose_validator() {
        let sig = make_sig("is_valid", vec![], Some("bool"));
        let results = match_and_propose(&sig);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].category, FunctionCategory::Validator);
        assert!(results[0].proposals.len() >= 2);
    }

    #[test]
    fn test_match_and_propose_converter() {
        let sig = make_sig("to_string", vec![], Some("String"));
        let results = match_and_propose(&sig);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].category, FunctionCategory::Converter);
    }

    #[test]
    fn test_match_and_propose_finder() {
        let sig = make_sig("find_item", vec![("key", "&str")], Some("Option<Item>"));
        let results = match_and_propose(&sig);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].category, FunctionCategory::Finder);
        assert!(results[0].proposals.len() >= 2);
    }

    #[test]
    fn test_match_and_propose_empty_for_unknown() {
        let sig = make_sig("frobulate", vec![("x", "Widget")], Some("Sprocket"));
        let results = match_and_propose(&sig);
        assert!(results.is_empty());
    }

    // --- proposal_from_template ---

    #[test]
    fn test_proposal_from_template_success() {
        let sig = make_sig("get_element", vec![("arr", "&[i32]"), ("idx", "usize")], Some("i32"));
        let template = SpecTemplate::new(
            "bounds_check",
            "{index} < {bound}",
            vec!["index".into(), "bound".into()],
            SpecTemplateKind::Precondition,
            "Index must be within bounds",
        );

        let mut bindings = FxHashMap::default();
        bindings.insert("index".to_string(), "idx".to_string());
        bindings.insert("bound".to_string(), "arr.len()".to_string());

        let proposal = proposal_from_template(&sig, &template, &bindings, 0.9, "bounds check");
        assert!(proposal.is_some());
        let p = proposal.unwrap();
        if let ProposalKind::AddPrecondition { ref spec_body } = p.kind {
            assert_eq!(spec_body, "idx < arr.len()");
        } else {
            panic!("expected AddPrecondition");
        }
    }

    #[test]
    fn test_proposal_from_template_missing_binding() {
        let sig = make_sig("f", vec![], None);
        let template = SpecTemplate::new(
            "test",
            "{a} < {b}",
            vec!["a".into(), "b".into()],
            SpecTemplateKind::Precondition,
            "test",
        );

        let mut bindings = FxHashMap::default();
        bindings.insert("a".to_string(), "x".to_string());
        // missing "b"

        let proposal = proposal_from_template(&sig, &template, &bindings, 0.9, "test");
        assert!(proposal.is_none());
    }

    #[test]
    fn test_proposal_from_template_postcondition() {
        let sig = make_sig("sort", vec![("arr", "&mut [i32]")], None);
        let template = SpecTemplate::new(
            "sorted",
            "{collection} is sorted",
            vec!["collection".into()],
            SpecTemplateKind::Postcondition,
            "test",
        );

        let mut bindings = FxHashMap::default();
        bindings.insert("collection".to_string(), "arr".to_string());

        let proposal = proposal_from_template(&sig, &template, &bindings, 0.85, "sorted post");
        assert!(proposal.is_some());
        let p = proposal.unwrap();
        assert!(matches!(p.kind, ProposalKind::AddPostcondition { .. }));
    }

    #[test]
    fn test_proposal_from_template_invariant() {
        let sig = make_sig("loop_fn", vec![], None);
        let template = SpecTemplate::new(
            "loop_var",
            "0 <= {var} && {var} <= {upper}",
            vec!["var".into(), "upper".into()],
            SpecTemplateKind::Invariant,
            "test",
        );

        let mut bindings = FxHashMap::default();
        bindings.insert("var".to_string(), "i".to_string());
        bindings.insert("upper".to_string(), "n".to_string());

        let proposal = proposal_from_template(&sig, &template, &bindings, 0.8, "loop invariant");
        assert!(proposal.is_some());
        let p = proposal.unwrap();
        if let ProposalKind::AddInvariant { ref spec_body } = p.kind {
            assert_eq!(spec_body, "0 <= i && i <= n");
        } else {
            panic!("expected AddInvariant");
        }
    }

    // --- FunctionCategory ---

    #[test]
    fn test_function_category_descriptions_nonempty() {
        let categories = vec![
            FunctionCategory::Getter,
            FunctionCategory::Setter,
            FunctionCategory::Constructor,
            FunctionCategory::Validator,
            FunctionCategory::Converter,
            FunctionCategory::Predicate,
            FunctionCategory::Finder,
            FunctionCategory::Accumulator,
        ];
        for cat in categories {
            assert!(!cat.description().is_empty(), "{cat:?} should have description");
        }
    }

    // --- Getter with index param ---

    #[test]
    fn test_getter_with_index_produces_bounds_check() {
        let sig = make_sig("get_item", vec![("idx", "usize")], Some("Item"));
        let results = match_and_propose(&sig);
        assert_eq!(results.len(), 1);
        let has_bounds = results[0].proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { ref spec_body } = p.kind {
                spec_body.contains("idx") && spec_body.contains("len")
            } else {
                false
            }
        });
        assert!(has_bounds, "getter with index should have bounds check");
    }

    // --- Converter with Result return ---

    #[test]
    fn test_converter_result_return() {
        let sig = make_sig("from_str", vec![("s", "&str")], Some("Result<Self, Error>"));
        let results = match_and_propose(&sig);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].category, FunctionCategory::Converter);
        let has_ok_post = results[0].proposals.iter().any(|p| {
            if let ProposalKind::AddPostcondition { ref spec_body } = p.kind {
                spec_body.contains("is_ok")
            } else {
                false
            }
        });
        assert!(has_ok_post, "converter with Result should have Ok postcondition");
    }

    // --- Accumulator with slice ---

    #[test]
    fn test_accumulator_nonempty_precondition() {
        let sig = make_sig("sum_values", vec![("data", "&[f64]")], Some("f64"));
        let results = match_and_propose(&sig);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].category, FunctionCategory::Accumulator);
        let has_nonempty = results[0].proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { ref spec_body } = p.kind {
                spec_body.contains("is_empty")
            } else {
                false
            }
        });
        assert!(has_nonempty, "accumulator should have non-empty precondition");
    }

    // --- Confidence values ---

    #[test]
    fn test_all_proposals_have_valid_confidence() {
        let sigs = vec![
            make_sig("get_name", vec![], Some("&str")),
            make_sig("set_value", vec![("v", "i32")], Some("()")),
            make_sig("new", vec![("x", "u32")], Some("Self")),
            make_sig("is_valid", vec![], Some("bool")),
            make_sig("to_string", vec![], Some("String")),
            make_sig("find_item", vec![("k", "&str")], Some("Option<Item>")),
            make_sig("count_items", vec![("items", "&[Item]")], Some("usize")),
        ];

        for sig in &sigs {
            let results = match_and_propose(sig);
            for r in &results {
                for p in &r.proposals {
                    assert!(
                        (0.0..=1.0).contains(&p.confidence),
                        "proposal for `{}` has invalid confidence {}: {:?}",
                        sig.name,
                        p.confidence,
                        p.kind
                    );
                }
            }
        }
    }

    #[test]
    fn test_proposals_reference_correct_function() {
        let sig = make_sig("get_name", vec![], Some("&str"));
        let results = match_and_propose(&sig);
        for r in &results {
            for p in &r.proposals {
                assert_eq!(p.function_path, "test::get_name");
                assert_eq!(p.function_name, "get_name");
            }
        }
    }

    // --- Validator confidence higher than predicate ---

    #[test]
    fn test_validator_higher_confidence_than_predicate() {
        let validator = make_sig("is_valid", vec![], Some("bool"));
        let predicate = make_sig("should_retry", vec![], Some("bool"));

        let v_res = classify_function(&validator);
        let p_res = classify_function(&predicate);

        assert!(v_res.is_some());
        assert!(p_res.is_some());
        assert!(
            v_res.unwrap().1 > p_res.unwrap().1,
            "validator should have higher confidence than generic predicate"
        );
    }
}
