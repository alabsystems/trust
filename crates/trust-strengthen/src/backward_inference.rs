// Trust: trust-strengthen/backward_inference.rs
//
// The prompt/response contract for the backward pass of the
// prove-strengthen-backprop loop. Takes function signatures, body summaries,
// and verification failures, then generates structured prompts for LLM-based
// spec inference and parses the results into `InferredSpec` objects.
//
// Formatting and parsing only: this module speaks to no model and holds no
// client. `validate_inferred_spec` checks well-formedness against the function
// summary (a `result` in a precondition, an unknown identifier) — it decides
// nothing about whether the spec HOLDS, which is still the prover's job.
//
// Supports template-based prompt generation for different spec categories:
// safety (overflow, bounds, null), functional (correctness, relationships),
// and ownership (borrow, lifetime, aliasing).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write;

use crate::analyzer::FailurePattern;
use crate::source_reader::SourceContext;

/// Trust: Error types for spec inference parsing and validation.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum SpecParseError {
    /// The LLM response was not valid JSON.
    #[error("invalid JSON in response: {reason}")]
    InvalidJson { reason: String },
    /// The JSON structure did not match the expected schema.
    #[error("unexpected response structure: {reason}")]
    UnexpectedStructure { reason: String },
    /// A spec expression was malformed.
    #[error("malformed spec expression in field '{field}': {reason}")]
    MalformedSpec { field: String, reason: String },
    /// The response was empty or contained no specs.
    #[error("empty response: no specs inferred")]
    EmptyResponse,
}

/// Trust: Category of spec being inferred, used to select prompt templates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SpecCategory {
    /// Safety specs: overflow guards, bounds checks, null checks, division guards.
    Safety,
    /// Functional specs: input-output relationships, correctness properties.
    Functional,
    /// Ownership specs: borrow validity, lifetime relationships, aliasing rules.
    Ownership,
}

impl std::fmt::Display for SpecCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Safety => write!(f, "safety"),
            Self::Functional => write!(f, "functional"),
            Self::Ownership => write!(f, "ownership"),
        }
    }
}

/// Trust: Description of a verification failure for the LLM prompt.
#[derive(Debug, Clone)]
pub struct FailureDescription {
    /// Classification of the failure pattern.
    pub pattern: FailurePattern,
    /// Human-readable description.
    pub description: String,
    /// Solver that reported the failure, if known.
    pub solver: Option<String>,
    /// Counterexample values, if available (e.g., "a = 18446744073709551615, b = 1").
    pub counterexample_summary: Option<String>,
}

/// Trust: Input to the spec inference pipeline. Captures everything the LLM
/// needs to infer specifications for a single function.
#[derive(Debug, Clone)]
pub struct SpecInferenceRequest {
    /// Fully qualified function name (e.g., "crate::module::func").
    pub function_path: String,
    /// Short function name (e.g., "func").
    pub function_name: String,
    /// The function signature line (e.g., "fn func(a: usize, b: usize) -> usize").
    pub signature: String,
    /// Summary of the function body. May be the full source or a condensed form.
    pub body_summary: String,
    /// Parameter names and types.
    pub params: Vec<(String, String)>,
    /// Return type, if any.
    pub return_type: Option<String>,
    /// Verification failures that triggered this inference request.
    pub failures: Vec<FailureDescription>,
    /// Which category of specs to focus on.
    pub category: SpecCategory,
    /// Existing specs already on the function (to avoid duplication).
    pub existing_specs: Vec<String>,
}

impl SpecInferenceRequest {
    /// Trust: Build a request from a `SourceContext` and failure descriptions.
    #[must_use]
    pub fn from_source_context(
        function_path: &str,
        ctx: &SourceContext,
        failures: Vec<FailureDescription>,
        category: SpecCategory,
    ) -> Self {
        Self {
            function_path: function_path.to_string(),
            function_name: ctx.function_name.clone(),
            signature: ctx.signature.clone(),
            body_summary: ctx.body.clone(),
            params: ctx.params.clone(),
            return_type: ctx.return_type.clone(),
            failures,
            category,
            existing_specs: Vec::new(),
        }
    }
}

/// Trust: A single inferred specification from the LLM.
#[derive(Debug, Clone, PartialEq)]
pub struct InferredSpecItem {
    /// The kind of spec: "precondition", "postcondition", or "invariant".
    pub kind: String,
    /// The spec expression body.
    pub expression: String,
    /// Confidence from the LLM (0.0 to 1.0).
    pub confidence: f64,
    /// Rationale explaining why this spec was inferred.
    pub rationale: String,
}

/// Trust: Complete inference result containing all specs for one function.
#[derive(Debug, Clone)]
pub struct InferredSpec {
    /// Target function path.
    pub function_path: String,
    /// Target function name.
    pub function_name: String,
    /// Inferred native `requires ...` clauses.
    pub preconditions: Vec<InferredSpecItem>,
    /// Inferred native `ensures ...` clauses.
    pub postconditions: Vec<InferredSpecItem>,
    /// Inferred native `invariant ...` clauses.
    pub invariants: Vec<InferredSpecItem>,
    /// Which category of specs was requested.
    pub category: SpecCategory,
}

impl InferredSpec {
    /// Trust: Total number of inferred specs across all kinds.
    #[must_use]
    pub fn total_count(&self) -> usize {
        self.preconditions.len() + self.postconditions.len() + self.invariants.len()
    }

    /// Trust: Whether any specs were inferred.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.total_count() == 0
    }

    /// Trust: Iterate over all specs with their kind label.
    pub fn all_specs(&self) -> impl Iterator<Item = &InferredSpecItem> {
        self.preconditions.iter().chain(self.postconditions.iter()).chain(self.invariants.iter())
    }

    /// Trust: Highest confidence across all inferred specs, or 0.0 if empty.
    #[must_use]
    pub fn max_confidence(&self) -> f64 {
        self.all_specs().map(|s| s.confidence).fold(0.0_f64, f64::max)
    }
}

/// Trust: Result of validating an `InferredSpec` against a function's signature.
#[derive(Debug, Clone)]
pub struct ValidationResult {
    /// Whether the overall spec set is considered valid.
    pub is_valid: bool,
    /// Per-spec validation errors (empty if all valid).
    pub errors: Vec<ValidationError>,
    /// Warnings that don't prevent use but suggest issues.
    pub warnings: Vec<String>,
}

/// Trust: A single validation error for a spec item.
#[derive(Debug, Clone)]
pub struct ValidationError {
    /// Which spec failed validation.
    pub spec_kind: String,
    /// The expression that failed.
    pub expression: String,
    /// Why it failed.
    pub reason: String,
}

/// Trust: Summary of a function for use in inference context.
/// This is a lightweight representation used when full `SourceContext` is unavailable.
#[derive(Debug, Clone)]
pub struct FunctionSummary {
    /// Function name.
    pub name: String,
    /// Parameter names.
    pub param_names: Vec<String>,
    /// Parameter types.
    pub param_types: Vec<String>,
    /// Return type, if known.
    pub return_type: Option<String>,
}

// ---------------------------------------------------------------------------
// Trust: Prompt generation
// ---------------------------------------------------------------------------

/// Trust: Generate a structured inference prompt for the given request.
///
/// The prompt is tailored to the `SpecCategory`, including:
/// - Safety: focuses on overflow, bounds, null, and division guards
/// - Functional: focuses on input-output relationships and correctness
/// - Ownership: focuses on borrow validity and lifetime constraints
///
/// Returns a prompt string suitable for an LLM like Claude.
#[must_use]
pub fn format_inference_prompt(req: &SpecInferenceRequest) -> String {
    let category_instructions = category_template(req.category);
    let failures_text = format_failures(&req.failures);
    let params_text = format_params(&req.params);
    let return_text = req.return_type.as_deref().unwrap_or("()");
    let existing_text = if req.existing_specs.is_empty() {
        String::new()
    } else {
        format!(
            "\n## Existing Specifications\n\n{}\n\nDo not duplicate these. \
             New specs should be consistent with and complementary to them.\n",
            req.existing_specs.join("\n")
        )
    };

    format!(
        r#"You are a formal verification expert specializing in Rust program correctness.

## Task

Infer {category} specifications for the function `{name}` that would make its verification conditions provable.

## Function Signature

```rust
{signature}
```

## Parameters

{params_text}

## Return Type

`{return_type}`

## Function Body

```rust
{body}
```
{existing}
## Verification Failures

The following verification conditions failed for this function:

{failures}

## {category_title} Specification Guidelines

{category_instructions}

## Response Format

Respond with ONLY a JSON array. Each element must have:
- `kind`: one of "precondition", "postcondition", "invariant"
- `expression`: the spec expression as a Rust-like boolean expression
- `confidence`: a number from 0.0 to 1.0
- `rationale`: a brief explanation of why this spec is needed

Example:
```json
[
  {{
    "kind": "precondition",
    "expression": "b != 0",
    "confidence": 0.95,
    "rationale": "Prevents division by zero in the denominator"
  }}
]
```"#,
        category = req.category,
        name = req.function_name,
        signature = req.signature,
        params_text = params_text,
        return_type = return_text,
        body = req.body_summary,
        existing = existing_text,
        failures = failures_text,
        category_title = category_title(req.category),
        category_instructions = category_instructions,
    )
}

/// Trust: Get the category-specific prompt template.
#[must_use]
fn category_template(category: SpecCategory) -> &'static str {
    match category {
        SpecCategory::Safety => {
            "Focus on **safety** specifications:\n\
             - Arithmetic overflow guards: ensure operands are within bounds before +, -, *\n\
             - Division by zero guards: ensure divisor is non-zero before / and %\n\
             - Index bounds: ensure indices are within slice/array length\n\
             - Null/None guards: ensure Option values are Some before unwrap\n\
             - Cast overflow: ensure values fit in target type before `as` casts\n\
             - Shift overflow: ensure shift amount is less than bit width\n\n\
             Prefer precise preconditions with concrete variable names over generic descriptions.\n\
             Use the actual parameter names from the signature."
        }
        SpecCategory::Functional => {
            "Focus on **functional correctness** specifications:\n\
             - Input-output relationships: how the return value relates to inputs\n\
             - Monotonicity: if inputs increase, does the output increase?\n\
             - Idempotence: does applying the function twice give the same result?\n\
             - Commutativity: does order of arguments matter?\n\
             - Preservation: what properties of inputs are preserved in outputs?\n\
             - Range: what range of values can the output take?\n\n\
             Postconditions are especially valuable here. Express relationships using\n\
             `result` to refer to the return value."
        }
        SpecCategory::Ownership => {
            "Focus on **ownership and borrowing** specifications:\n\
             - Borrow validity: ensure references are valid for their required lifetimes\n\
             - Aliasing rules: no mutable reference aliases\n\
             - Slice validity: slices point to valid, initialized memory\n\
             - Container invariants: Vec capacity >= len, sorted order maintained\n\
             - Drop safety: resources are properly released\n\n\
             These specs help the verifier reason about Rust's ownership model.\n\
             Express constraints on reference validity and aliasing."
        }
    }
}

/// Trust: Get a human-readable title for a spec category.
#[must_use]
fn category_title(category: SpecCategory) -> &'static str {
    match category {
        SpecCategory::Safety => "Safety",
        SpecCategory::Functional => "Functional Correctness",
        SpecCategory::Ownership => "Ownership & Borrowing",
    }
}

/// Trust: Format failure descriptions for the prompt.
fn format_failures(failures: &[FailureDescription]) -> String {
    if failures.is_empty() {
        return "No specific failures recorded. Infer general specifications.".to_string();
    }
    failures
        .iter()
        .enumerate()
        .map(|(i, f)| {
            let mut line =
                format!("{}. **{}**: {}", i + 1, format_pattern(&f.pattern), f.description);
            if let Some(ref solver) = f.solver {
                let _ = write!(line, " (solver: {solver})");
            }
            if let Some(ref cex) = f.counterexample_summary {
                let _ = write!(line, "\n   Counterexample: {cex}");
            }
            line
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Trust: Format a failure pattern name for display.
fn format_pattern(pattern: &FailurePattern) -> String {
    match pattern {
        FailurePattern::ArithmeticOverflow { op } => format!("Arithmetic overflow ({op:?})"),
        FailurePattern::DivisionByZero => "Division by zero".to_string(),
        FailurePattern::IndexOutOfBounds => "Index out of bounds".to_string(),
        FailurePattern::CastOverflow => "Cast overflow".to_string(),
        FailurePattern::NegationOverflow => "Negation overflow".to_string(),
        FailurePattern::ShiftOverflow => "Shift overflow".to_string(),
        FailurePattern::AssertionFailure { message } => format!("Assertion failure: {message}"),
        FailurePattern::PreconditionViolation { callee } => {
            format!("Precondition violation on {callee}")
        }
        FailurePattern::PostconditionViolation => "Postcondition violation".to_string(),
        FailurePattern::UnreachableReached => "Unreachable code reached".to_string(),
        FailurePattern::Temporal => "Temporal property violation".to_string(),
        FailurePattern::UnboundedAllocation { count, .. } => {
            format!("Unbounded allocation sized by {count}")
        }
        FailurePattern::Unknown => "Unknown failure".to_string(),
    }
}

/// Trust: Format parameters for display in the prompt.
fn format_params(params: &[(String, String)]) -> String {
    if params.is_empty() {
        return "(no parameters)".to_string();
    }
    params.iter().map(|(name, ty)| format!("- `{name}`: `{ty}`")).collect::<Vec<_>>().join("\n")
}

// ---------------------------------------------------------------------------
// Trust: Response parsing
// ---------------------------------------------------------------------------

/// Trust: Parse an LLM response string into an `InferredSpec`.
///
/// Expects a JSON array of spec objects. Handles common LLM response quirks:
/// - JSON wrapped in markdown code fences
/// - Extra text before/after the JSON
/// - Missing optional fields
///
/// Returns `Err` if no valid specs can be extracted.
pub fn parse_inference_response(
    response: &str,
    function_path: &str,
    function_name: &str,
    category: SpecCategory,
) -> Result<InferredSpec, SpecParseError> {
    let json_text = extract_json(response)?;

    let raw_specs: Vec<RawSpecItem> = serde_json::from_str(&json_text)
        .map_err(|e| SpecParseError::InvalidJson { reason: e.to_string() })?;

    if raw_specs.is_empty() {
        return Err(SpecParseError::EmptyResponse);
    }

    let mut preconditions = Vec::new();
    let mut postconditions = Vec::new();
    let mut invariants = Vec::new();

    for raw in raw_specs {
        let item = InferredSpecItem {
            kind: raw.kind.clone(),
            expression: raw.expression,
            confidence: raw.confidence.clamp(0.0, 1.0),
            rationale: raw.rationale.unwrap_or_default(),
        };

        match raw.kind.as_str() {
            "precondition" => preconditions.push(item),
            "postcondition" => postconditions.push(item),
            "invariant" => invariants.push(item),
            other => {
                return Err(SpecParseError::UnexpectedStructure {
                    reason: format!("unknown spec kind: '{other}'"),
                });
            }
        }
    }

    Ok(InferredSpec {
        function_path: function_path.to_string(),
        function_name: function_name.to_string(),
        preconditions,
        postconditions,
        invariants,
        category,
    })
}

/// Trust: Raw deserialized spec item from JSON.
#[derive(serde::Deserialize)]
struct RawSpecItem {
    kind: String,
    expression: String,
    confidence: f64,
    rationale: Option<String>,
}

/// Trust: Extract a JSON array from LLM response text.
///
/// Handles code fences, extra prose, and whitespace.
fn extract_json(text: &str) -> Result<String, SpecParseError> {
    let trimmed = text.trim();

    // Try ```json ... ``` fences first
    if let Some(start) = trimmed.find("```json") {
        let after_fence = &trimmed[start + 7..];
        if let Some(end) = after_fence.find("```") {
            let inner = after_fence[..end].trim();
            if inner.starts_with('[') {
                return Ok(inner.to_string());
            }
        }
    }

    // Try ``` ... ``` fences
    if let Some(start) = trimmed.find("```") {
        let after_fence = &trimmed[start + 3..];
        if let Some(end) = after_fence.find("```") {
            let inner = after_fence[..end].trim();
            if inner.starts_with('[') {
                return Ok(inner.to_string());
            }
        }
    }

    // Try raw JSON array
    if trimmed.starts_with('[') && trimmed.ends_with(']') {
        return Ok(trimmed.to_string());
    }

    // Try to find [ ... ] anywhere in the text
    if let (Some(start), Some(end)) = (trimmed.find('['), trimmed.rfind(']'))
        && start < end
    {
        return Ok(trimmed[start..=end].to_string());
    }

    Err(SpecParseError::InvalidJson { reason: "no JSON array found in response".to_string() })
}

// ---------------------------------------------------------------------------
// Trust: Spec validation
// ---------------------------------------------------------------------------

/// Trust: Validate an `InferredSpec` against a function summary.
///
/// Checks for:
/// - Empty expressions
/// - `result` used in preconditions (only valid in postconditions)
/// - References to unknown identifiers (not in parameter list)
/// - Unbalanced parentheses
/// - `result` in postconditions when function returns `()`
#[must_use]
pub fn validate_inferred_spec(spec: &InferredSpec, func: &FunctionSummary) -> ValidationResult {
    let mut errors = Vec::new();
    let mut warnings = Vec::new();

    // Trust: Validate preconditions
    for item in &spec.preconditions {
        validate_one_item(item, "precondition", func, &mut errors, &mut warnings);
        // Trust: "result" in a precondition is always wrong
        if item.expression.contains("result") {
            errors.push(ValidationError {
                spec_kind: "precondition".to_string(),
                expression: item.expression.clone(),
                reason: "\"result\" cannot appear in a precondition (only in postconditions)"
                    .to_string(),
            });
        }
    }

    // Trust: Validate postconditions
    for item in &spec.postconditions {
        validate_one_item(item, "postcondition", func, &mut errors, &mut warnings);
        // Trust: "result" in a void postcondition is suspicious
        if item.expression.contains("result") && func.return_type.is_none() {
            errors.push(ValidationError {
                spec_kind: "postcondition".to_string(),
                expression: item.expression.clone(),
                reason: "\"result\" used but function returns ()".to_string(),
            });
        }
    }

    // Trust: Validate invariants
    for item in &spec.invariants {
        validate_one_item(item, "invariant", func, &mut errors, &mut warnings);
    }

    ValidationResult { is_valid: errors.is_empty(), errors, warnings }
}

/// Trust: Validate a single spec item.
fn validate_one_item(
    item: &InferredSpecItem,
    kind: &str,
    func: &FunctionSummary,
    errors: &mut Vec<ValidationError>,
    warnings: &mut Vec<String>,
) {
    // Trust: Empty expression check
    if item.expression.trim().is_empty() {
        errors.push(ValidationError {
            spec_kind: kind.to_string(),
            expression: item.expression.clone(),
            reason: "empty spec expression".to_string(),
        });
        return;
    }

    // Trust: Balanced parentheses check
    let mut paren_depth: i32 = 0;
    for ch in item.expression.chars() {
        match ch {
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            _ => {}
        }
        if paren_depth < 0 {
            errors.push(ValidationError {
                spec_kind: kind.to_string(),
                expression: item.expression.clone(),
                reason: "unbalanced parentheses".to_string(),
            });
            return;
        }
    }
    if paren_depth != 0 {
        errors.push(ValidationError {
            spec_kind: kind.to_string(),
            expression: item.expression.clone(),
            reason: "unbalanced parentheses".to_string(),
        });
    }

    // Trust: Confidence range warning
    if item.confidence < 0.0 || item.confidence > 1.0 {
        warnings.push(format!(
            "{kind} '{}' has out-of-range confidence: {}",
            item.expression, item.confidence
        ));
    }

    // Trust: Check for identifiers not in param list (soft warning)
    if !func.param_names.is_empty() {
        let builtins = [
            "result", "self", "true", "false", "len", "MAX", "MIN", "usize", "u8", "u16", "u32",
            "u64", "u128", "isize", "i8", "i16", "i32", "i64", "i128", "f32", "f64", "bool", "old",
            "forall", "exists", "is_some", "is_none", "is_null", "is_ok", "is_err",
        ];
        for ident in extract_identifiers(&item.expression) {
            if ident.len() > 1
                && !func.param_names.contains(&ident)
                && !builtins.contains(&ident.as_str())
                && !ident.contains("::")
            {
                warnings.push(format!(
                    "{kind} '{}': identifier '{ident}' not in parameter list",
                    item.expression,
                ));
            }
        }
    }
}

/// Trust: Extract word-like identifiers from a spec expression.
fn extract_identifiers(expr: &str) -> Vec<String> {
    let mut ids = Vec::new();
    let mut current = String::new();

    for ch in expr.chars() {
        if ch.is_alphanumeric() || ch == '_' {
            current.push(ch);
        } else {
            if !current.is_empty() && !current.chars().next().unwrap_or('0').is_ascii_digit() {
                ids.push(std::mem::take(&mut current));
            } else {
                current.clear();
            }
        }
    }
    if !current.is_empty() && !current.chars().next().unwrap_or('0').is_ascii_digit() {
        ids.push(current);
    }

    ids
}

// ---------------------------------------------------------------------------
// Trust: Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyzer::FailurePattern;

    // --- Helper constructors ---

    fn midpoint_request(category: SpecCategory) -> SpecInferenceRequest {
        SpecInferenceRequest {
            function_path: "crate::math::get_midpoint".to_string(),
            function_name: "get_midpoint".to_string(),
            signature: "fn get_midpoint(a: usize, b: usize) -> usize".to_string(),
            body_summary: "(a + b) / 2".to_string(),
            params: vec![
                ("a".to_string(), "usize".to_string()),
                ("b".to_string(), "usize".to_string()),
            ],
            return_type: Some("usize".to_string()),
            failures: vec![FailureDescription {
                pattern: FailurePattern::ArithmeticOverflow { op: trust_types::BinOp::Add },
                description: "Addition a + b may overflow usize".to_string(),
                solver: Some("ay".to_string()),
                counterexample_summary: Some("a = 18446744073709551615, b = 1".to_string()),
            }],
            category,
            existing_specs: Vec::new(),
        }
    }

    fn divide_request() -> SpecInferenceRequest {
        SpecInferenceRequest {
            function_path: "crate::math::safe_divide".to_string(),
            function_name: "safe_divide".to_string(),
            signature: "fn safe_divide(x: u64, y: u64) -> u64".to_string(),
            body_summary: "x / y".to_string(),
            params: vec![
                ("x".to_string(), "u64".to_string()),
                ("y".to_string(), "u64".to_string()),
            ],
            return_type: Some("u64".to_string()),
            failures: vec![FailureDescription {
                pattern: FailurePattern::DivisionByZero,
                description: "Division by zero when y == 0".to_string(),
                solver: Some("ay".to_string()),
                counterexample_summary: Some("x = 42, y = 0".to_string()),
            }],
            category: SpecCategory::Safety,
            existing_specs: Vec::new(),
        }
    }

    fn midpoint_summary() -> FunctionSummary {
        FunctionSummary {
            name: "get_midpoint".to_string(),
            param_names: vec!["a".to_string(), "b".to_string()],
            param_types: vec!["usize".to_string(), "usize".to_string()],
            return_type: Some("usize".to_string()),
        }
    }

    // === Prompt generation tests ===

    #[test]
    fn test_format_prompt_contains_function_name() {
        let req = midpoint_request(SpecCategory::Safety);
        let prompt = format_inference_prompt(&req);
        assert!(prompt.contains("get_midpoint"), "prompt should contain function name");
    }

    #[test]
    fn test_format_prompt_contains_signature() {
        let req = midpoint_request(SpecCategory::Safety);
        let prompt = format_inference_prompt(&req);
        assert!(
            prompt.contains("fn get_midpoint(a: usize, b: usize) -> usize"),
            "prompt should contain full signature"
        );
    }

    #[test]
    fn test_format_prompt_contains_body() {
        let req = midpoint_request(SpecCategory::Safety);
        let prompt = format_inference_prompt(&req);
        assert!(prompt.contains("(a + b) / 2"), "prompt should contain body summary");
    }

    #[test]
    fn test_format_prompt_contains_failure_info() {
        let req = midpoint_request(SpecCategory::Safety);
        let prompt = format_inference_prompt(&req);
        assert!(
            prompt.contains("Arithmetic overflow"),
            "prompt should describe the failure pattern"
        );
        assert!(prompt.contains("ay"), "prompt should mention the solver");
    }

    #[test]
    fn test_format_prompt_contains_counterexample() {
        let req = midpoint_request(SpecCategory::Safety);
        let prompt = format_inference_prompt(&req);
        assert!(
            prompt.contains("18446744073709551615"),
            "prompt should contain counterexample values"
        );
    }

    #[test]
    fn test_format_prompt_safety_category_instructions() {
        let req = midpoint_request(SpecCategory::Safety);
        let prompt = format_inference_prompt(&req);
        assert!(prompt.contains("Safety"), "prompt should contain safety category title");
        assert!(prompt.contains("overflow guards"), "safety prompt should mention overflow guards");
    }

    #[test]
    fn test_format_prompt_functional_category_instructions() {
        let req = midpoint_request(SpecCategory::Functional);
        let prompt = format_inference_prompt(&req);
        assert!(
            prompt.contains("Functional Correctness"),
            "prompt should contain functional category title"
        );
        assert!(
            prompt.contains("Input-output relationships"),
            "functional prompt should mention I/O relationships"
        );
    }

    #[test]
    fn test_format_prompt_ownership_category_instructions() {
        let req = midpoint_request(SpecCategory::Ownership);
        let prompt = format_inference_prompt(&req);
        assert!(prompt.contains("Ownership"), "prompt should contain ownership category title");
        assert!(prompt.contains("borrow"), "ownership prompt should mention borrows");
    }

    #[test]
    fn test_format_prompt_contains_json_instructions() {
        let req = midpoint_request(SpecCategory::Safety);
        let prompt = format_inference_prompt(&req);
        assert!(prompt.contains("JSON"), "prompt should request JSON output");
        assert!(prompt.contains("\"kind\""), "prompt should specify the JSON schema");
    }

    #[test]
    fn test_format_prompt_contains_parameter_list() {
        let req = midpoint_request(SpecCategory::Safety);
        let prompt = format_inference_prompt(&req);
        assert!(prompt.contains("`a`: `usize`"), "prompt should list parameter a with type");
        assert!(prompt.contains("`b`: `usize`"), "prompt should list parameter b with type");
    }

    #[test]
    fn test_format_prompt_with_existing_specs() {
        let mut req = midpoint_request(SpecCategory::Safety);
        req.existing_specs = vec!["requires a > 0".to_string(), "ensures result <= a".to_string()];
        let prompt = format_inference_prompt(&req);
        assert!(prompt.contains("Existing Specifications"), "prompt should mention existing specs");
        assert!(prompt.contains("a > 0"), "prompt should include existing spec body");
        assert!(prompt.contains("Do not duplicate"), "prompt should warn against duplication");
    }

    #[test]
    fn test_format_prompt_no_failures() {
        let mut req = midpoint_request(SpecCategory::Functional);
        req.failures.clear();
        let prompt = format_inference_prompt(&req);
        assert!(
            prompt.contains("No specific failures"),
            "prompt should handle empty failures gracefully"
        );
    }

    #[test]
    fn test_format_prompt_division_by_zero() {
        let req = divide_request();
        let prompt = format_inference_prompt(&req);
        assert!(prompt.contains("Division by zero"), "prompt should describe div-by-zero failure");
        assert!(prompt.contains("y = 0"), "prompt should include counterexample");
    }

    // === Response parsing tests ===

    #[test]
    fn test_parse_valid_precondition() {
        let json = r#"[
            {
                "kind": "precondition",
                "expression": "a <= usize::MAX - b",
                "confidence": 0.95,
                "rationale": "Prevents addition overflow"
            }
        ]"#;

        let spec =
            parse_inference_response(json, "test::midpoint", "midpoint", SpecCategory::Safety)
                .expect("should parse valid JSON");
        assert_eq!(spec.preconditions.len(), 1);
        assert_eq!(spec.preconditions[0].expression, "a <= usize::MAX - b");
        assert!((spec.preconditions[0].confidence - 0.95).abs() < f64::EPSILON);
        assert_eq!(spec.preconditions[0].rationale, "Prevents addition overflow");
        assert!(spec.postconditions.is_empty());
        assert!(spec.invariants.is_empty());
    }

    #[test]
    fn test_parse_valid_postcondition() {
        let json = r#"[
            {
                "kind": "postcondition",
                "expression": "result >= a && result >= b",
                "confidence": 0.8,
                "rationale": "Max returns the larger"
            }
        ]"#;

        let spec = parse_inference_response(json, "test::max", "max", SpecCategory::Functional)
            .expect("should parse postcondition");
        assert_eq!(spec.postconditions.len(), 1);
        assert_eq!(spec.postconditions[0].expression, "result >= a && result >= b");
    }

    #[test]
    fn test_parse_valid_invariant() {
        let json = r#"[{"kind": "invariant", "expression": "i < n", "confidence": 0.85, "rationale": "Loop bound"}]"#;

        let spec = parse_inference_response(json, "test::loop_fn", "loop_fn", SpecCategory::Safety)
            .expect("should parse invariant");
        assert_eq!(spec.invariants.len(), 1);
        assert_eq!(spec.invariants[0].expression, "i < n");
    }

    #[test]
    fn test_parse_mixed_specs() {
        let json = r#"[
            {"kind": "precondition", "expression": "b != 0", "confidence": 0.95, "rationale": "Guard"},
            {"kind": "postcondition", "expression": "result * b <= x", "confidence": 0.7, "rationale": "Div bound"},
            {"kind": "invariant", "expression": "lo <= hi", "confidence": 0.8, "rationale": "Binary search"}
        ]"#;

        let spec = parse_inference_response(json, "test::f", "f", SpecCategory::Safety)
            .expect("should parse mixed specs");
        assert_eq!(spec.preconditions.len(), 1);
        assert_eq!(spec.postconditions.len(), 1);
        assert_eq!(spec.invariants.len(), 1);
        assert_eq!(spec.total_count(), 3);
        assert!(!spec.is_empty());
    }

    #[test]
    fn test_parse_json_in_markdown_fences() {
        let response = r#"Here is my analysis:

```json
[{"kind": "precondition", "expression": "y != 0", "confidence": 0.9, "rationale": "Div guard"}]
```

This prevents division by zero."#;

        let spec = parse_inference_response(response, "test::div", "div", SpecCategory::Safety)
            .expect("should extract JSON from markdown fences");
        assert_eq!(spec.preconditions.len(), 1);
        assert_eq!(spec.preconditions[0].expression, "y != 0");
    }

    #[test]
    fn test_parse_json_in_plain_fences() {
        let response = "```\n[{\"kind\": \"precondition\", \"expression\": \"n < 64\", \"confidence\": 0.85, \"rationale\": \"Shift\"}]\n```";

        let spec = parse_inference_response(response, "test::shift", "shift", SpecCategory::Safety)
            .expect("should extract JSON from plain fences");
        assert_eq!(spec.preconditions.len(), 1);
    }

    #[test]
    fn test_parse_confidence_clamped() {
        let json = r#"[{"kind": "precondition", "expression": "x > 0", "confidence": 1.5, "rationale": "Over-confident"}]"#;

        let spec = parse_inference_response(json, "test::f", "f", SpecCategory::Safety)
            .expect("should clamp confidence");
        assert!((spec.preconditions[0].confidence - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_parse_negative_confidence_clamped() {
        let json = r#"[{"kind": "postcondition", "expression": "result > 0", "confidence": -0.5, "rationale": "Negative"}]"#;

        let spec = parse_inference_response(json, "test::f", "f", SpecCategory::Safety)
            .expect("should clamp negative confidence");
        assert!(spec.postconditions[0].confidence.abs() < f64::EPSILON);
    }

    #[test]
    fn test_parse_missing_rationale_uses_default() {
        let json = r#"[{"kind": "precondition", "expression": "x > 0", "confidence": 0.8}]"#;

        let spec = parse_inference_response(json, "test::f", "f", SpecCategory::Safety)
            .expect("should handle missing rationale");
        assert!(spec.preconditions[0].rationale.is_empty());
    }

    #[test]
    fn test_parse_empty_array_returns_error() {
        let result = parse_inference_response("[]", "test::f", "f", SpecCategory::Safety);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), SpecParseError::EmptyResponse));
    }

    #[test]
    fn test_parse_invalid_json_returns_error() {
        let result =
            parse_inference_response("not json at all", "test::f", "f", SpecCategory::Safety);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), SpecParseError::InvalidJson { .. }));
    }

    #[test]
    fn test_parse_unknown_kind_returns_error() {
        let json =
            r#"[{"kind": "magic", "expression": "x > 0", "confidence": 0.5, "rationale": "Bad"}]"#;
        let result = parse_inference_response(json, "test::f", "f", SpecCategory::Safety);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), SpecParseError::UnexpectedStructure { .. }));
    }

    // === Validation tests ===

    #[test]
    fn test_validate_valid_spec() {
        let spec = InferredSpec {
            function_path: "test::midpoint".to_string(),
            function_name: "midpoint".to_string(),
            preconditions: vec![InferredSpecItem {
                kind: "precondition".to_string(),
                expression: "a <= usize::MAX - b".to_string(),
                confidence: 0.9,
                rationale: "Overflow guard".to_string(),
            }],
            postconditions: vec![InferredSpecItem {
                kind: "postcondition".to_string(),
                expression: "result <= a || result <= b".to_string(),
                confidence: 0.7,
                rationale: "Midpoint bound".to_string(),
            }],
            invariants: Vec::new(),
            category: SpecCategory::Safety,
        };

        let result = validate_inferred_spec(&spec, &midpoint_summary());
        assert!(result.is_valid, "valid spec should pass validation: {:?}", result.errors);
    }

    #[test]
    fn test_validate_result_in_precondition_fails() {
        let spec = InferredSpec {
            function_path: "test::f".to_string(),
            function_name: "f".to_string(),
            preconditions: vec![InferredSpecItem {
                kind: "precondition".to_string(),
                expression: "result > 0".to_string(),
                confidence: 0.9,
                rationale: "Bad".to_string(),
            }],
            postconditions: Vec::new(),
            invariants: Vec::new(),
            category: SpecCategory::Functional,
        };

        let result = validate_inferred_spec(&spec, &midpoint_summary());
        assert!(!result.is_valid, "result in precondition should fail");
        assert!(
            result.errors.iter().any(|e| e.reason.contains("result")),
            "should report 'result' error"
        );
    }

    #[test]
    fn test_validate_empty_expression_fails() {
        let spec = InferredSpec {
            function_path: "test::f".to_string(),
            function_name: "f".to_string(),
            preconditions: vec![InferredSpecItem {
                kind: "precondition".to_string(),
                expression: "".to_string(),
                confidence: 0.5,
                rationale: "Empty".to_string(),
            }],
            postconditions: Vec::new(),
            invariants: Vec::new(),
            category: SpecCategory::Safety,
        };

        let result = validate_inferred_spec(&spec, &midpoint_summary());
        assert!(!result.is_valid);
        assert!(result.errors.iter().any(|e| e.reason.contains("empty")));
    }

    #[test]
    fn test_validate_unbalanced_parens_fails() {
        let spec = InferredSpec {
            function_path: "test::f".to_string(),
            function_name: "f".to_string(),
            preconditions: vec![InferredSpecItem {
                kind: "precondition".to_string(),
                expression: "(a + b".to_string(),
                confidence: 0.5,
                rationale: "Unbalanced".to_string(),
            }],
            postconditions: Vec::new(),
            invariants: Vec::new(),
            category: SpecCategory::Safety,
        };

        let result = validate_inferred_spec(&spec, &midpoint_summary());
        assert!(!result.is_valid);
        assert!(result.errors.iter().any(|e| e.reason.contains("parentheses")));
    }

    #[test]
    fn test_validate_unknown_identifier_warns() {
        let spec = InferredSpec {
            function_path: "test::f".to_string(),
            function_name: "f".to_string(),
            preconditions: vec![InferredSpecItem {
                kind: "precondition".to_string(),
                expression: "xyz > 0".to_string(),
                confidence: 0.5,
                rationale: "Unknown id".to_string(),
            }],
            postconditions: Vec::new(),
            invariants: Vec::new(),
            category: SpecCategory::Safety,
        };

        let result = validate_inferred_spec(&spec, &midpoint_summary());
        // Unknown identifiers are warnings, not errors
        assert!(result.is_valid);
        assert!(
            result.warnings.iter().any(|w| w.contains("xyz")),
            "should warn about unknown identifier 'xyz'"
        );
    }

    #[test]
    fn test_validate_void_function_result_in_postcondition() {
        let func = FunctionSummary {
            name: "process".to_string(),
            param_names: vec!["x".to_string()],
            param_types: vec!["i32".to_string()],
            return_type: None,
        };

        let spec = InferredSpec {
            function_path: "test::process".to_string(),
            function_name: "process".to_string(),
            preconditions: Vec::new(),
            postconditions: vec![InferredSpecItem {
                kind: "postcondition".to_string(),
                expression: "result == 0".to_string(),
                confidence: 0.5,
                rationale: "Bad: void function".to_string(),
            }],
            invariants: Vec::new(),
            category: SpecCategory::Functional,
        };

        let result = validate_inferred_spec(&spec, &func);
        assert!(!result.is_valid);
        assert!(
            result.errors.iter().any(|e| e.reason.contains("returns ()")),
            "should flag result in void function postcondition"
        );
    }

    // === InferredSpec utility method tests ===

    #[test]
    fn test_inferred_spec_total_count() {
        let spec = InferredSpec {
            function_path: "test::f".to_string(),
            function_name: "f".to_string(),
            preconditions: vec![
                InferredSpecItem {
                    kind: "precondition".to_string(),
                    expression: "a > 0".to_string(),
                    confidence: 0.9,
                    rationale: "r".to_string(),
                },
                InferredSpecItem {
                    kind: "precondition".to_string(),
                    expression: "b > 0".to_string(),
                    confidence: 0.8,
                    rationale: "r".to_string(),
                },
            ],
            postconditions: vec![InferredSpecItem {
                kind: "postcondition".to_string(),
                expression: "result > 0".to_string(),
                confidence: 0.7,
                rationale: "r".to_string(),
            }],
            invariants: Vec::new(),
            category: SpecCategory::Functional,
        };
        assert_eq!(spec.total_count(), 3);
        assert!(!spec.is_empty());
    }

    #[test]
    fn test_inferred_spec_empty() {
        let spec = InferredSpec {
            function_path: "test::f".to_string(),
            function_name: "f".to_string(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            invariants: Vec::new(),
            category: SpecCategory::Safety,
        };
        assert_eq!(spec.total_count(), 0);
        assert!(spec.is_empty());
        assert!(spec.max_confidence().abs() < f64::EPSILON);
    }

    #[test]
    fn test_inferred_spec_max_confidence() {
        let spec = InferredSpec {
            function_path: "test::f".to_string(),
            function_name: "f".to_string(),
            preconditions: vec![InferredSpecItem {
                kind: "precondition".to_string(),
                expression: "a > 0".to_string(),
                confidence: 0.7,
                rationale: "r".to_string(),
            }],
            postconditions: vec![InferredSpecItem {
                kind: "postcondition".to_string(),
                expression: "result > 0".to_string(),
                confidence: 0.95,
                rationale: "r".to_string(),
            }],
            invariants: Vec::new(),
            category: SpecCategory::Functional,
        };
        assert!((spec.max_confidence() - 0.95).abs() < f64::EPSILON);
    }

    // === SpecCategory display test ===

    #[test]
    fn test_spec_category_display() {
        assert_eq!(format!("{}", SpecCategory::Safety), "safety");
        assert_eq!(format!("{}", SpecCategory::Functional), "functional");
        assert_eq!(format!("{}", SpecCategory::Ownership), "ownership");
    }

    // === from_source_context test ===

    #[test]
    fn test_from_source_context() {
        let ctx = SourceContext {
            function_name: "get_midpoint".to_string(),
            params: vec![
                ("a".to_string(), "usize".to_string()),
                ("b".to_string(), "usize".to_string()),
            ],
            return_type: Some("usize".to_string()),
            signature: "fn get_midpoint(a: usize, b: usize) -> usize".to_string(),
            body: "(a + b) / 2".to_string(),
            full_source: "fn get_midpoint(a: usize, b: usize) -> usize {\n    (a + b) / 2\n}"
                .to_string(),
        };

        let req = SpecInferenceRequest::from_source_context(
            "crate::math::get_midpoint",
            &ctx,
            vec![],
            SpecCategory::Safety,
        );

        assert_eq!(req.function_name, "get_midpoint");
        assert_eq!(req.function_path, "crate::math::get_midpoint");
        assert_eq!(req.params.len(), 2);
        assert_eq!(req.return_type, Some("usize".to_string()));
        assert_eq!(req.category, SpecCategory::Safety);
        assert!(req.existing_specs.is_empty());
    }

    // === SpecParseError display tests ===

    #[test]
    fn test_spec_parse_error_display() {
        let e = SpecParseError::InvalidJson { reason: "unexpected EOF".to_string() };
        assert!(e.to_string().contains("unexpected EOF"));

        let e = SpecParseError::EmptyResponse;
        assert!(e.to_string().contains("empty response"));

        let e = SpecParseError::MalformedSpec {
            field: "expression".to_string(),
            reason: "contains SQL".to_string(),
        };
        assert!(e.to_string().contains("expression"));
        assert!(e.to_string().contains("SQL"));
    }

    // === extract_identifiers tests ===

    #[test]
    fn test_extract_identifiers_basic() {
        let ids = extract_identifiers("a <= usize::MAX - b");
        assert!(ids.contains(&"a".to_string()));
        assert!(ids.contains(&"usize".to_string()));
        assert!(ids.contains(&"MAX".to_string()));
        assert!(ids.contains(&"b".to_string()));
    }

    #[test]
    fn test_extract_identifiers_skips_numbers() {
        let ids = extract_identifiers("x > 0 && y < 100");
        assert!(ids.contains(&"x".to_string()));
        assert!(ids.contains(&"y".to_string()));
        assert!(!ids.iter().any(|i| i == "0" || i == "100"));
    }

    // === End-to-end pipeline test ===

    #[test]
    fn test_end_to_end_pipeline() {
        // 1. Build request
        let req = midpoint_request(SpecCategory::Safety);

        // 2. Generate prompt
        let prompt = format_inference_prompt(&req);
        assert!(!prompt.is_empty());

        // 3. Simulate LLM response
        let mock_response = r#"```json
[
    {"kind": "precondition", "expression": "a <= usize::MAX - b", "confidence": 0.95, "rationale": "Prevents addition overflow"},
    {"kind": "postcondition", "expression": "result == (a + b) / 2", "confidence": 0.85, "rationale": "Midpoint definition"}
]
```"#;

        // 4. Parse response
        let spec = parse_inference_response(
            mock_response,
            &req.function_path,
            &req.function_name,
            req.category,
        )
        .expect("should parse mock response");

        assert_eq!(spec.preconditions.len(), 1);
        assert_eq!(spec.postconditions.len(), 1);
        assert_eq!(spec.total_count(), 2);

        // 5. Validate
        let validation = validate_inferred_spec(&spec, &midpoint_summary());
        assert!(validation.is_valid, "end-to-end spec should validate: {:?}", validation.errors);
    }
}
