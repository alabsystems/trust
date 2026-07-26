// trust-strengthen/heuristic_rules.rs: Rule-based heuristic spec strengthening
//
// Provides a trait-based rule engine for LLM-free spec inference. Each rule
// matches against a function signature pattern and produces spec proposals.
// Fast, deterministic, and suitable for CI/CD pipelines.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

use crate::heuristic::FunctionSignature;
use crate::proposer::{Proposal, ProposalKind};

/// A heuristic rule that matches a function pattern and proposes specs.
///
/// Implementors inspect function signatures (name, parameters, return type)
/// and produce zero or more spec proposals without any LLM calls.
pub trait HeuristicRule: Send + Sync {
    /// Human-readable name of this rule.
    fn name(&self) -> &str;

    /// Check whether this rule applies to the given function signature.
    fn matches(&self, sig: &FunctionSignature) -> bool;

    /// Produce spec proposals for a matching function.
    ///
    /// Only called when `matches` returns true, but implementations should
    /// still be safe if called on non-matching signatures (return empty vec).
    fn propose(&self, sig: &FunctionSignature) -> Vec<Proposal>;
}

/// Functions returning raw pointers or references should return non-null.
pub struct NonNullReturn;

impl HeuristicRule for NonNullReturn {
    fn name(&self) -> &str {
        "NonNullReturn"
    }

    fn matches(&self, sig: &FunctionSignature) -> bool {
        if let Some(ref ret) = sig.return_type {
            let trimmed = ret.trim();
            trimmed.starts_with('*')
                || trimmed.starts_with("*const")
                || trimmed.starts_with("*mut")
                || trimmed.starts_with("NonNull")
                || (trimmed.starts_with('&') && !trimmed.starts_with("&["))
        } else {
            false
        }
    }

    fn propose(&self, sig: &FunctionSignature) -> Vec<Proposal> {
        let ret = match sig.return_type {
            Some(ref r) => r.trim(),
            None => return vec![],
        };

        let spec_body = if ret.starts_with('*') {
            "result != null".to_string()
        } else if ret.starts_with("NonNull") {
            "result is non-null (guaranteed by NonNull type)".to_string()
        } else {
            "result reference is valid".to_string()
        };

        vec![Proposal {
            function_path: sig.path.clone(),
            function_name: sig.name.clone(),
            kind: ProposalKind::AddPostcondition { spec_body },
            confidence: 0.75,
            rationale: format!(
                "NonNullReturn: function `{}` returns a pointer/reference type `{}`",
                sig.name, ret
            ),
        }]
    }
}

/// Array/slice-accessing functions need index < length preconditions.
pub struct BoundsCheck;

impl HeuristicRule for BoundsCheck {
    fn name(&self) -> &str {
        "BoundsCheck"
    }

    fn matches(&self, sig: &FunctionSignature) -> bool {
        let has_index_param =
            sig.params.iter().any(|(name, ty)| is_index_name(name) && ty.trim() == "usize");
        let has_slice_param = sig.params.iter().any(|(_, ty)| {
            let t = ty.trim();
            t.starts_with("&[") || t.starts_with("&mut [") || t.starts_with("Vec<")
        });
        has_index_param && has_slice_param
    }

    fn propose(&self, sig: &FunctionSignature) -> Vec<Proposal> {
        let mut proposals = Vec::new();

        let index_params: Vec<&str> = sig
            .params
            .iter()
            .filter(|(name, ty)| is_index_name(name) && ty.trim() == "usize")
            .map(|(name, _)| name.as_str())
            .collect();

        let slice_params: Vec<&str> = sig
            .params
            .iter()
            .filter(|(_, ty)| {
                let t = ty.trim();
                t.starts_with("&[") || t.starts_with("&mut [") || t.starts_with("Vec<")
            })
            .map(|(name, _)| name.as_str())
            .collect();

        for idx in &index_params {
            let collection = slice_params.first().copied().unwrap_or("collection");
            proposals.push(Proposal {
                function_path: sig.path.clone(),
                function_name: sig.name.clone(),
                kind: ProposalKind::AddPrecondition {
                    spec_body: format!("{idx} < {collection}.len()"),
                },
                confidence: 0.85,
                rationale: format!(
                    "BoundsCheck: `{idx}: usize` is likely an index into `{collection}`"
                ),
            });
        }

        proposals
    }
}

/// Division operations need divisor != 0 preconditions.
pub struct DivisionGuard;

impl HeuristicRule for DivisionGuard {
    fn name(&self) -> &str {
        "DivisionGuard"
    }

    fn matches(&self, sig: &FunctionSignature) -> bool {
        // Match if function name suggests division or has a divisor-like param
        let name_suggests_div = {
            let lower = sig.name.to_lowercase();
            lower.contains("div")
                || lower.contains("rem")
                || lower.contains("mod")
                || lower.contains("ratio")
                || lower.contains("percent")
                || lower.contains("average")
                || lower.contains("mean")
        };
        let has_divisor_param =
            sig.params.iter().any(|(name, ty)| is_divisor_name(name) && is_numeric_type(ty.trim()));
        name_suggests_div || has_divisor_param
    }

    fn propose(&self, sig: &FunctionSignature) -> Vec<Proposal> {
        let mut proposals = Vec::new();

        // Find explicit divisor-like parameters
        let divisor_params: Vec<&str> = sig
            .params
            .iter()
            .filter(|(name, ty)| is_divisor_name(name) && is_numeric_type(ty.trim()))
            .map(|(name, _)| name.as_str())
            .collect();

        if !divisor_params.is_empty() {
            for d in &divisor_params {
                proposals.push(Proposal {
                    function_path: sig.path.clone(),
                    function_name: sig.name.clone(),
                    kind: ProposalKind::AddPrecondition { spec_body: format!("{d} != 0") },
                    confidence: 0.9,
                    rationale: format!(
                        "DivisionGuard: parameter `{d}` is likely used as a divisor"
                    ),
                });
            }
        } else {
            // Function name suggests division but no obvious divisor param;
            // pick numeric params that could be divisors (second numeric param, or "n", "b", etc.)
            let numeric_params: Vec<&str> = sig
                .params
                .iter()
                .filter(|(_, ty)| is_numeric_type(ty.trim()))
                .map(|(name, _)| name.as_str())
                .collect();

            if numeric_params.len() >= 2 {
                // Second numeric param is likely the divisor
                let divisor = numeric_params[1];
                proposals.push(Proposal {
                    function_path: sig.path.clone(),
                    function_name: sig.name.clone(),
                    kind: ProposalKind::AddPrecondition {
                        spec_body: format!("{divisor} != 0"),
                    },
                    confidence: 0.7,
                    rationale: format!(
                        "DivisionGuard: `{}` likely involves division; `{divisor}` may be the divisor",
                        sig.name
                    ),
                });
            } else if numeric_params.len() == 1 {
                let param = numeric_params[0];
                proposals.push(Proposal {
                    function_path: sig.path.clone(),
                    function_name: sig.name.clone(),
                    kind: ProposalKind::AddPrecondition {
                        spec_body: format!("{param} != 0"),
                    },
                    confidence: 0.6,
                    rationale: format!(
                        "DivisionGuard: `{}` suggests division; `{param}` is the only numeric param",
                        sig.name
                    ),
                });
            }
        }

        proposals
    }
}

/// Arithmetic functions should have checked/overflow preconditions.
pub struct OverflowGuard;

impl HeuristicRule for OverflowGuard {
    fn name(&self) -> &str {
        "OverflowGuard"
    }

    fn matches(&self, sig: &FunctionSignature) -> bool {
        let lower = sig.name.to_lowercase();
        let name_suggests_arith = lower.contains("add")
            || lower.contains("sub")
            || lower.contains("mul")
            || lower.contains("sum")
            || lower.contains("product")
            || lower.contains("total")
            || lower.contains("accumulate")
            || lower.contains("midpoint")
            || lower.contains("average");

        let has_numeric_params =
            sig.params.iter().filter(|(_, ty)| is_integer_type(ty.trim())).count() >= 2;

        name_suggests_arith && has_numeric_params
    }

    fn propose(&self, sig: &FunctionSignature) -> Vec<Proposal> {
        let mut proposals = Vec::new();

        let int_params: Vec<(&str, &str)> = sig
            .params
            .iter()
            .filter(|(_, ty)| is_integer_type(ty.trim()))
            .map(|(name, ty)| (name.as_str(), ty.as_str()))
            .collect();

        if int_params.len() >= 2 {
            let (a, ty_a) = int_params[0];
            let (b, _) = int_params[1];
            let type_max = type_max_const(ty_a.trim());

            let lower = sig.name.to_lowercase();
            if lower.contains("add")
                || lower.contains("sum")
                || lower.contains("total")
                || lower.contains("accumulate")
                || lower.contains("midpoint")
                || lower.contains("average")
            {
                proposals.push(Proposal {
                    function_path: sig.path.clone(),
                    function_name: sig.name.clone(),
                    kind: ProposalKind::AddPrecondition {
                        spec_body: format!("{a} <= {type_max} - {b}"),
                    },
                    confidence: 0.8,
                    rationale: format!(
                        "OverflowGuard: addition in `{}` may overflow `{}`",
                        sig.name,
                        ty_a.trim()
                    ),
                });
            }

            if lower.contains("sub") && is_unsigned_type(ty_a.trim()) {
                proposals.push(Proposal {
                    function_path: sig.path.clone(),
                    function_name: sig.name.clone(),
                    kind: ProposalKind::AddPrecondition { spec_body: format!("{a} >= {b}") },
                    confidence: 0.85,
                    rationale: format!(
                        "OverflowGuard: unsigned subtraction in `{}` may underflow",
                        sig.name
                    ),
                });
            }

            if lower.contains("mul") || lower.contains("product") {
                proposals.push(Proposal {
                    function_path: sig.path.clone(),
                    function_name: sig.name.clone(),
                    kind: ProposalKind::AddPrecondition {
                        spec_body: format!("{b} == 0 || {a} <= {type_max} / {b}"),
                    },
                    confidence: 0.8,
                    rationale: format!(
                        "OverflowGuard: multiplication in `{}` may overflow",
                        sig.name
                    ),
                });
            }

            // Generic overflow postcondition for all arithmetic
            if let Some(ref ret) = sig.return_type
                && is_integer_type(ret.trim())
            {
                proposals.push(Proposal {
                    function_path: sig.path.clone(),
                    function_name: sig.name.clone(),
                    kind: ProposalKind::AddPostcondition {
                        spec_body: format!("result fits in {}", ret.trim()),
                    },
                    confidence: 0.65,
                    rationale: format!(
                        "OverflowGuard: result of `{}` must fit in `{}`",
                        sig.name,
                        ret.trim()
                    ),
                });
            }
        }

        proposals
    }
}

/// Fallible functions (returning Result) should have Ok-path postconditions.
pub struct ResultOk;

impl HeuristicRule for ResultOk {
    fn name(&self) -> &str {
        "ResultOk"
    }

    fn matches(&self, sig: &FunctionSignature) -> bool {
        sig.return_type.as_ref().is_some_and(|r| r.trim().starts_with("Result<"))
    }

    fn propose(&self, sig: &FunctionSignature) -> Vec<Proposal> {
        let mut proposals = Vec::new();

        // Ok path postcondition
        proposals.push(Proposal {
            function_path: sig.path.clone(),
            function_name: sig.name.clone(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "result.is_ok() ==> output is valid".to_string(),
            },
            confidence: 0.7,
            rationale: format!(
                "ResultOk: `{}` returns Result; Ok path should produce valid output",
                sig.name
            ),
        });

        // Err path postcondition
        proposals.push(Proposal {
            function_path: sig.path.clone(),
            function_name: sig.name.clone(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "result.is_err() ==> no side effects occurred".to_string(),
            },
            confidence: 0.55,
            rationale: format!(
                "ResultOk: `{}` returns Result; Err path should be side-effect-free",
                sig.name
            ),
        });

        // If function name suggests validation/parsing, add input-related postcondition
        let lower = sig.name.to_lowercase();
        if lower.contains("parse") || lower.contains("validate") || lower.contains("from_str") {
            proposals.push(Proposal {
                function_path: sig.path.clone(),
                function_name: sig.name.clone(),
                kind: ProposalKind::AddPostcondition {
                    spec_body: "result.is_ok() ==> input was well-formed".to_string(),
                },
                confidence: 0.6,
                rationale: format!(
                    "ResultOk: `{}` parses/validates; Ok implies well-formed input",
                    sig.name
                ),
            });
        }

        proposals
    }
}

/// Engine that runs all registered heuristic rules against a function signature.
pub struct RuleEngine {
    rules: Vec<Box<dyn HeuristicRule>>,
    min_confidence: f64,
    max_proposals: usize,
}

impl RuleEngine {
    /// Create a new rule engine with the default set of built-in rules.
    #[must_use]
    pub fn new() -> Self {
        Self {
            rules: vec![
                Box::new(NonNullReturn),
                Box::new(BoundsCheck),
                Box::new(DivisionGuard),
                Box::new(OverflowGuard),
                Box::new(ResultOk),
            ],
            min_confidence: 0.5,
            max_proposals: 20,
        }
    }

    /// Create a rule engine with custom configuration.
    #[must_use]
    pub fn with_config(min_confidence: f64, max_proposals: usize) -> Self {
        Self {
            rules: vec![
                Box::new(NonNullReturn),
                Box::new(BoundsCheck),
                Box::new(DivisionGuard),
                Box::new(OverflowGuard),
                Box::new(ResultOk),
            ],
            min_confidence,
            max_proposals,
        }
    }

    /// Add a custom rule to the engine.
    pub fn add_rule(&mut self, rule: Box<dyn HeuristicRule>) {
        self.rules.push(rule);
    }

    /// Run all rules against a function signature and return combined proposals.
    ///
    /// Proposals are deduplicated, filtered by confidence, sorted descending,
    /// and capped at `max_proposals`.
    #[must_use]
    pub fn run(&self, sig: &FunctionSignature) -> Vec<Proposal> {
        let mut proposals: Vec<Proposal> = self
            .rules
            .iter()
            .filter(|rule| rule.matches(sig))
            .flat_map(|rule| rule.propose(sig))
            .collect();

        // Deduplicate by spec body
        dedup_by_spec(&mut proposals);

        // Filter and sort
        proposals.retain(|p| p.confidence >= self.min_confidence);
        proposals.sort_by(|a, b| {
            b.confidence.partial_cmp(&a.confidence).unwrap_or(std::cmp::Ordering::Equal)
        });
        proposals.truncate(self.max_proposals);

        proposals
    }

    /// Return the names of all registered rules.
    #[must_use]
    pub fn rule_names(&self) -> Vec<&str> {
        self.rules.iter().map(|r| r.name()).collect()
    }
}

impl Default for RuleEngine {
    fn default() -> Self {
        Self::new()
    }
}

// --- Utility functions ---

fn dedup_by_spec(proposals: &mut Vec<Proposal>) {
    let mut seen = FxHashSet::default();
    proposals.retain(|p| {
        let key = format!("{:?}:{}", std::mem::discriminant(&p.kind), extract_spec_body(&p.kind));
        seen.insert(key)
    });
}

fn extract_spec_body(kind: &ProposalKind) -> &str {
    match kind {
        ProposalKind::AddPrecondition { spec_body }
        | ProposalKind::AddPostcondition { spec_body }
        | ProposalKind::AddInvariant { spec_body } => spec_body,
        ProposalKind::SafeArithmetic { replacement, .. } => replacement,
        ProposalKind::AddBoundsCheck { check_expr } => check_expr,
        ProposalKind::AddNonZeroCheck { check_expr } => check_expr,
    }
}

fn is_index_name(name: &str) -> bool {
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

fn is_divisor_name(name: &str) -> bool {
    let lower = name.to_lowercase();
    lower == "divisor"
        || lower == "denominator"
        || lower == "denom"
        || lower == "d"
        || lower == "y"
        || lower == "b"
        || lower == "n"
        || lower == "modulus"
        || lower == "count"
        || lower.ends_with("_divisor")
        || lower.ends_with("_denom")
}

fn is_numeric_type(ty: &str) -> bool {
    matches!(
        ty,
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

fn is_integer_type(ty: &str) -> bool {
    matches!(
        ty,
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
    )
}

fn is_unsigned_type(ty: &str) -> bool {
    matches!(ty, "u8" | "u16" | "u32" | "u64" | "u128" | "usize")
}

fn type_max_const(ty: &str) -> &str {
    match ty {
        "u8" => "u8::MAX",
        "u16" => "u16::MAX",
        "u32" => "u32::MAX",
        "u64" => "u64::MAX",
        "u128" => "u128::MAX",
        "usize" => "usize::MAX",
        "i8" => "i8::MAX",
        "i16" => "i16::MAX",
        "i32" => "i32::MAX",
        "i64" => "i64::MAX",
        "i128" => "i128::MAX",
        "isize" => "isize::MAX",
        _ => "MAX",
    }
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

    // --- NonNullReturn ---

    #[test]
    fn test_non_null_return_matches_raw_pointer() {
        let rule = NonNullReturn;
        let sig = make_sig("get_ptr", vec![], Some("*const u8"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_non_null_return_matches_mut_pointer() {
        let rule = NonNullReturn;
        let sig = make_sig("get_mut_ptr", vec![], Some("*mut u8"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_non_null_return_matches_nonnull_type() {
        let rule = NonNullReturn;
        let sig = make_sig("alloc", vec![], Some("NonNull<u8>"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_non_null_return_matches_reference() {
        let rule = NonNullReturn;
        let sig = make_sig("get_ref", vec![], Some("&str"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_non_null_return_no_match_for_value_type() {
        let rule = NonNullReturn;
        let sig = make_sig("compute", vec![], Some("u64"));
        assert!(!rule.matches(&sig));
    }

    #[test]
    fn test_non_null_return_no_match_for_slice_ref() {
        let rule = NonNullReturn;
        let sig = make_sig("get_data", vec![], Some("&[u8]"));
        assert!(!rule.matches(&sig));
    }

    #[test]
    fn test_non_null_return_propose_pointer() {
        let rule = NonNullReturn;
        let sig = make_sig("get_ptr", vec![], Some("*const u8"));
        let proposals = rule.propose(&sig);
        assert_eq!(proposals.len(), 1);
        if let ProposalKind::AddPostcondition { ref spec_body } = proposals[0].kind {
            assert!(spec_body.contains("null"));
        } else {
            panic!("expected AddPostcondition");
        }
    }

    // --- BoundsCheck ---

    #[test]
    fn test_bounds_check_matches_index_and_slice() {
        let rule = BoundsCheck;
        let sig = make_sig("get", vec![("arr", "&[i32]"), ("idx", "usize")], Some("i32"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_bounds_check_matches_vec_param() {
        let rule = BoundsCheck;
        let sig = make_sig("get", vec![("items", "Vec<String>"), ("i", "usize")], Some("String"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_bounds_check_no_match_without_index() {
        let rule = BoundsCheck;
        let sig = make_sig("get", vec![("arr", "&[i32]"), ("key", "usize")], Some("i32"));
        assert!(!rule.matches(&sig));
    }

    #[test]
    fn test_bounds_check_no_match_without_slice() {
        let rule = BoundsCheck;
        let sig = make_sig("get", vec![("idx", "usize")], Some("i32"));
        assert!(!rule.matches(&sig));
    }

    #[test]
    fn test_bounds_check_propose() {
        let rule = BoundsCheck;
        let sig = make_sig("get_element", vec![("data", "&[f64]"), ("idx", "usize")], Some("f64"));
        let proposals = rule.propose(&sig);
        assert_eq!(proposals.len(), 1);
        if let ProposalKind::AddPrecondition { ref spec_body } = proposals[0].kind {
            assert_eq!(spec_body, "idx < data.len()");
        } else {
            panic!("expected AddPrecondition");
        }
    }

    #[test]
    fn test_bounds_check_multiple_indices() {
        let rule = BoundsCheck;
        let sig =
            make_sig("swap", vec![("arr", "&mut [i32]"), ("i", "usize"), ("j", "usize")], None);
        let proposals = rule.propose(&sig);
        assert_eq!(proposals.len(), 2);
    }

    // --- DivisionGuard ---

    #[test]
    fn test_division_guard_matches_divisor_param() {
        let rule = DivisionGuard;
        let sig = make_sig("compute", vec![("x", "u64"), ("divisor", "u64")], Some("u64"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_division_guard_matches_div_name() {
        let rule = DivisionGuard;
        let sig = make_sig("safe_div", vec![("a", "i32"), ("b", "i32")], Some("i32"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_division_guard_matches_average() {
        let rule = DivisionGuard;
        let sig = make_sig("average", vec![("sum", "u64"), ("count", "u64")], Some("u64"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_division_guard_no_match_add() {
        let rule = DivisionGuard;
        let sig = make_sig("add", vec![("a", "u64"), ("x", "u64")], Some("u64"));
        assert!(!rule.matches(&sig));
    }

    #[test]
    fn test_division_guard_propose_explicit_divisor() {
        let rule = DivisionGuard;
        let sig = make_sig("divide", vec![("x", "u64"), ("divisor", "u64")], Some("u64"));
        let proposals = rule.propose(&sig);
        assert!(!proposals.is_empty());
        let has_nonzero = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { ref spec_body } = p.kind {
                spec_body == "divisor != 0"
            } else {
                false
            }
        });
        assert!(has_nonzero, "should propose divisor != 0");
    }

    #[test]
    fn test_division_guard_propose_inferred_divisor() {
        let rule = DivisionGuard;
        let sig = make_sig("safe_div", vec![("a", "u64"), ("x", "u64")], Some("u64"));
        let proposals = rule.propose(&sig);
        assert!(!proposals.is_empty());
        // Should infer second param as divisor
        let has_nonzero = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { ref spec_body } = p.kind {
                spec_body == "x != 0"
            } else {
                false
            }
        });
        assert!(has_nonzero, "should infer second param as divisor");
    }

    // --- OverflowGuard ---

    #[test]
    fn test_overflow_guard_matches_add_function() {
        let rule = OverflowGuard;
        let sig = make_sig("safe_add", vec![("a", "u64"), ("b", "u64")], Some("u64"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_overflow_guard_matches_midpoint() {
        let rule = OverflowGuard;
        let sig = make_sig("midpoint", vec![("lo", "usize"), ("hi", "usize")], Some("usize"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_overflow_guard_no_match_single_param() {
        let rule = OverflowGuard;
        let sig = make_sig("add_one", vec![("x", "u64")], Some("u64"));
        assert!(!rule.matches(&sig));
    }

    #[test]
    fn test_overflow_guard_no_match_non_arith_name() {
        let rule = OverflowGuard;
        let sig = make_sig("lookup", vec![("a", "u64"), ("b", "u64")], Some("u64"));
        assert!(!rule.matches(&sig));
    }

    #[test]
    fn test_overflow_guard_propose_add() {
        let rule = OverflowGuard;
        let sig = make_sig("safe_add", vec![("a", "u64"), ("b", "u64")], Some("u64"));
        let proposals = rule.propose(&sig);
        assert!(!proposals.is_empty());
        let has_overflow_pre = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { ref spec_body } = p.kind {
                spec_body.contains("u64::MAX")
            } else {
                false
            }
        });
        assert!(has_overflow_pre, "should propose overflow guard with u64::MAX");
    }

    #[test]
    fn test_overflow_guard_propose_sub_unsigned() {
        let rule = OverflowGuard;
        let sig = make_sig("safe_sub", vec![("a", "u32"), ("b", "u32")], Some("u32"));
        let proposals = rule.propose(&sig);
        let has_underflow = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { ref spec_body } = p.kind {
                spec_body == "a >= b"
            } else {
                false
            }
        });
        assert!(has_underflow, "should propose a >= b for unsigned subtraction");
    }

    #[test]
    fn test_overflow_guard_propose_mul() {
        let rule = OverflowGuard;
        let sig = make_sig("mul_checked", vec![("a", "u64"), ("b", "u64")], Some("u64"));
        let proposals = rule.propose(&sig);
        let has_mul_guard = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { ref spec_body } = p.kind {
                spec_body.contains("/")
            } else {
                false
            }
        });
        assert!(has_mul_guard, "should propose multiplication overflow guard");
    }

    // --- ResultOk ---

    #[test]
    fn test_result_ok_matches_result_return() {
        let rule = ResultOk;
        let sig = make_sig("parse", vec![("input", "&str")], Some("Result<Config, Error>"));
        assert!(rule.matches(&sig));
    }

    #[test]
    fn test_result_ok_no_match_option() {
        let rule = ResultOk;
        let sig = make_sig("find", vec![("key", "&str")], Some("Option<Value>"));
        assert!(!rule.matches(&sig));
    }

    #[test]
    fn test_result_ok_propose_basic() {
        let rule = ResultOk;
        let sig = make_sig("process", vec![("data", "&[u8]")], Some("Result<Output, Error>"));
        let proposals = rule.propose(&sig);
        assert!(proposals.len() >= 2);
        let has_ok_post = proposals.iter().any(|p| {
            if let ProposalKind::AddPostcondition { ref spec_body } = p.kind {
                spec_body.contains("is_ok")
            } else {
                false
            }
        });
        assert!(has_ok_post, "should propose Ok-path postcondition");
    }

    #[test]
    fn test_result_ok_propose_parse_extra() {
        let rule = ResultOk;
        let sig = make_sig("parse_config", vec![("input", "&str")], Some("Result<Config, Error>"));
        let proposals = rule.propose(&sig);
        assert!(proposals.len() >= 3, "parse function should get extra proposal");
    }

    // --- RuleEngine ---

    #[test]
    fn test_rule_engine_default_has_five_rules() {
        let engine = RuleEngine::new();
        assert_eq!(engine.rule_names().len(), 5);
    }

    #[test]
    fn test_rule_engine_runs_matching_rules() {
        let engine = RuleEngine::new();
        let sig = make_sig("get_element", vec![("arr", "&[i32]"), ("idx", "usize")], Some("i32"));
        let proposals = engine.run(&sig);
        assert!(!proposals.is_empty());
        // Should have bounds check proposal
        let has_bounds = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { ref spec_body } = p.kind {
                spec_body.contains("idx") && spec_body.contains("len")
            } else {
                false
            }
        });
        assert!(has_bounds, "RuleEngine should produce bounds check proposal");
    }

    #[test]
    fn test_rule_engine_respects_min_confidence() {
        let engine = RuleEngine::with_config(0.99, 20);
        let sig = make_sig("get_element", vec![("arr", "&[i32]"), ("idx", "usize")], Some("i32"));
        let proposals = engine.run(&sig);
        for p in &proposals {
            assert!(p.confidence >= 0.99);
        }
    }

    #[test]
    fn test_rule_engine_respects_max_proposals() {
        let engine = RuleEngine::with_config(0.0, 2);
        let sig = make_sig(
            "safe_div",
            vec![("arr", "&[i32]"), ("idx", "usize"), ("divisor", "u64")],
            Some("Result<i32, Error>"),
        );
        let proposals = engine.run(&sig);
        assert!(proposals.len() <= 2);
    }

    #[test]
    fn test_rule_engine_sorted_descending() {
        let engine = RuleEngine::with_config(0.0, 50);
        let sig = make_sig(
            "safe_div",
            vec![("x", "u64"), ("divisor", "u64")],
            Some("Result<u64, Error>"),
        );
        let proposals = engine.run(&sig);
        for window in proposals.windows(2) {
            assert!(
                window[0].confidence >= window[1].confidence,
                "proposals not sorted: {} < {}",
                window[0].confidence,
                window[1].confidence
            );
        }
    }

    #[test]
    fn test_rule_engine_custom_rule() {
        struct AlwaysMatch;
        impl HeuristicRule for AlwaysMatch {
            fn name(&self) -> &str {
                "AlwaysMatch"
            }
            fn matches(&self, _: &FunctionSignature) -> bool {
                true
            }
            fn propose(&self, sig: &FunctionSignature) -> Vec<Proposal> {
                vec![Proposal {
                    function_path: sig.path.clone(),
                    function_name: sig.name.clone(),
                    kind: ProposalKind::AddPrecondition { spec_body: "custom rule fired".into() },
                    confidence: 1.0,
                    rationale: "custom rule".into(),
                }]
            }
        }

        let mut engine = RuleEngine::new();
        engine.add_rule(Box::new(AlwaysMatch));
        assert_eq!(engine.rule_names().len(), 6);

        let sig = make_sig("anything", vec![], None);
        let proposals = engine.run(&sig);
        let has_custom = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { ref spec_body } = p.kind {
                spec_body == "custom rule fired"
            } else {
                false
            }
        });
        assert!(has_custom, "custom rule should fire");
    }

    #[test]
    fn test_rule_engine_no_proposals_for_unmatched() {
        let engine = RuleEngine::new();
        let sig = make_sig("frobulate", vec![("x", "String")], Some("String"));
        let proposals = engine.run(&sig);
        assert!(proposals.is_empty(), "no rules should match frobulate(String) -> String");
    }

    #[test]
    fn test_rule_engine_deduplicates() {
        // Both DivisionGuard and OverflowGuard could fire; ensure no duplicate spec bodies
        let engine = RuleEngine::with_config(0.0, 50);
        let sig = make_sig("safe_div", vec![("a", "u64"), ("b", "u64")], Some("u64"));
        let proposals = engine.run(&sig);

        let spec_bodies: Vec<String> = proposals
            .iter()
            .map(|p| {
                format!("{:?}:{}", std::mem::discriminant(&p.kind), extract_spec_body(&p.kind))
            })
            .collect();

        let unique: FxHashSet<&String> = spec_bodies.iter().collect();
        assert_eq!(spec_bodies.len(), unique.len(), "should have no duplicate proposals");
    }

    // --- Utility function tests ---

    #[test]
    fn test_is_index_name_variants() {
        assert!(is_index_name("i"));
        assert!(is_index_name("idx"));
        assert!(is_index_name("index"));
        assert!(is_index_name("pos"));
        assert!(is_index_name("row_idx"));
        assert!(is_index_name("col_index"));
        assert!(!is_index_name("name"));
        assert!(!is_index_name("value"));
    }

    #[test]
    fn test_is_divisor_name_variants() {
        assert!(is_divisor_name("divisor"));
        assert!(is_divisor_name("denominator"));
        assert!(is_divisor_name("denom"));
        assert!(is_divisor_name("modulus"));
        assert!(is_divisor_name("count"));
        assert!(is_divisor_name("n"));
        assert!(!is_divisor_name("result"));
    }

    #[test]
    fn test_is_integer_type_includes_all() {
        for ty in &[
            "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
        ] {
            assert!(is_integer_type(ty), "{ty} should be integer");
        }
        assert!(!is_integer_type("f32"));
        assert!(!is_integer_type("f64"));
        assert!(!is_integer_type("String"));
    }

    #[test]
    fn test_is_unsigned_type() {
        assert!(is_unsigned_type("u64"));
        assert!(is_unsigned_type("usize"));
        assert!(!is_unsigned_type("i64"));
        assert!(!is_unsigned_type("isize"));
    }

    #[test]
    fn test_type_max_const_mapping() {
        assert_eq!(type_max_const("u64"), "u64::MAX");
        assert_eq!(type_max_const("usize"), "usize::MAX");
        assert_eq!(type_max_const("i32"), "i32::MAX");
        assert_eq!(type_max_const("String"), "MAX");
    }
}
