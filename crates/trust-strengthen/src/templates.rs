// trust-strengthen/templates.rs: Parameterized spec templates for common properties
//
// Provides reusable spec templates that can be instantiated with concrete
// variable names and types extracted from counterexamples or source context.
// Avoids LLM calls for well-understood verification conditions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

/// A parameterized specification template.
///
/// Templates use `{placeholder}` syntax for variables that are filled in
/// during instantiation. For example: `"{var} < {bound}"` becomes `"i < n"`
/// when instantiated with `var="i"` and `bound="n"`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecTemplate {
    /// Human-readable name for this template.
    pub name: String,
    /// The template string with `{placeholder}` variables.
    pub template: String,
    /// Names of required placeholder variables.
    pub parameters: Vec<String>,
    /// The kind of spec this template produces.
    pub spec_kind: SpecTemplateKind,
    /// Description of when to use this template.
    pub description: String,
}

/// What kind of spec a template produces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecTemplateKind {
    /// Precondition: `requires ...`
    Precondition,
    /// Postcondition: `ensures ...`
    Postcondition,
    /// Loop invariant: `invariant ...`
    Invariant,
}

impl SpecTemplate {
    /// Create a new spec template.
    #[must_use]
    pub fn new(
        name: impl Into<String>,
        template: impl Into<String>,
        parameters: Vec<String>,
        spec_kind: SpecTemplateKind,
        description: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            template: template.into(),
            parameters,
            spec_kind,
            description: description.into(),
        }
    }
}

/// Instantiate a template by replacing `{placeholder}` variables with bindings.
///
/// Returns `None` if any required parameter is missing from the bindings.
///
/// # Examples
///
/// ```
/// use trust_types::fx::FxHashMap;
/// use trust_strengthen::{SpecTemplate, SpecTemplateKind, instantiate_template};
///
/// let template = SpecTemplate::new(
///     "bounds_check",
///     "{index} < {bound}",
///     vec!["index".into(), "bound".into()],
///     SpecTemplateKind::Precondition,
///     "Index must be less than bound",
/// );
///
/// let mut bindings = FxHashMap::default();
/// bindings.insert("index".to_string(), "i".to_string());
/// bindings.insert("bound".to_string(), "arr.len()".to_string());
///
/// let result = instantiate_template(&template, &bindings);
/// assert_eq!(result, Some("i < arr.len()".to_string()));
/// ```
#[must_use]
pub fn instantiate_template(
    template: &SpecTemplate,
    bindings: &FxHashMap<String, String>,
) -> Option<String> {
    // Verify all required parameters are present
    for param in &template.parameters {
        if !bindings.contains_key(param) {
            return None;
        }
    }

    let mut result = template.template.clone();
    let mut placeholders: Vec<_> = template.parameters.iter().collect();
    placeholders
        .sort_by(|key_a, key_b| key_b.len().cmp(&key_a.len()).then_with(|| key_a.cmp(key_b)));
    for key in placeholders {
        let value = bindings.get(key).expect("required template parameter was checked above");
        let placeholder = format!("{{{key}}}");
        result = result.replace(&placeholder, value);
    }
    Some(result)
}

/// Build the standard template library.
///
/// Returns a collection of commonly-needed spec templates organized by category.
#[must_use]
pub fn standard_templates() -> Vec<SpecTemplate> {
    vec![
        // --- Bounds checks ---
        SpecTemplate::new(
            "bounds_check",
            "{index} < {bound}",
            vec!["index".into(), "bound".into()],
            SpecTemplateKind::Precondition,
            "Index must be within bounds",
        ),
        SpecTemplate::new(
            "bounds_check_len",
            "{index} < {collection}.len()",
            vec!["index".into(), "collection".into()],
            SpecTemplateKind::Precondition,
            "Index must be less than collection length",
        ),
        SpecTemplate::new(
            "range_check",
            "{lower} <= {var} && {var} < {upper}",
            vec!["var".into(), "lower".into(), "upper".into()],
            SpecTemplateKind::Precondition,
            "Variable must be within a range [lower, upper)",
        ),
        // --- Overflow guards ---
        SpecTemplate::new(
            "add_overflow_guard",
            "{a} <= {type_max} - {b}",
            vec!["a".into(), "b".into(), "type_max".into()],
            SpecTemplateKind::Precondition,
            "Addition must not overflow: a + b <= MAX",
        ),
        SpecTemplate::new(
            "sub_underflow_guard",
            "{a} >= {b}",
            vec!["a".into(), "b".into()],
            SpecTemplateKind::Precondition,
            "Subtraction must not underflow: a >= b for unsigned types",
        ),
        SpecTemplate::new(
            "mul_overflow_guard",
            "{b} == 0 || {a} <= {type_max} / {b}",
            vec!["a".into(), "b".into(), "type_max".into()],
            SpecTemplateKind::Precondition,
            "Multiplication must not overflow",
        ),
        // --- Non-null / non-zero ---
        SpecTemplate::new(
            "non_zero",
            "{var} != 0",
            vec!["var".into()],
            SpecTemplateKind::Precondition,
            "Variable must be non-zero (for division or other operations)",
        ),
        SpecTemplate::new(
            "non_empty",
            "!{collection}.is_empty()",
            vec!["collection".into()],
            SpecTemplateKind::Precondition,
            "Collection must not be empty",
        ),
        // --- Sorted ---
        SpecTemplate::new(
            "sorted_ascending",
            "forall i in 0..{collection}.len()-1, {collection}[i] <= {collection}[i+1]",
            vec!["collection".into()],
            SpecTemplateKind::Postcondition,
            "Collection is sorted in ascending order after operation",
        ),
        SpecTemplate::new(
            "sorted_precondition",
            "{collection} is sorted in ascending order",
            vec!["collection".into()],
            SpecTemplateKind::Precondition,
            "Collection must be sorted (e.g., for binary search)",
        ),
        // --- Permutation ---
        SpecTemplate::new(
            "permutation",
            "{output} is a permutation of {input}",
            vec!["output".into(), "input".into()],
            SpecTemplateKind::Postcondition,
            "Output must contain exactly the same elements as input",
        ),
        // --- Loop invariants ---
        SpecTemplate::new(
            "loop_bounds_invariant",
            "{lower} <= {var} && {var} <= {upper}",
            vec!["var".into(), "lower".into(), "upper".into()],
            SpecTemplateKind::Invariant,
            "Loop variable stays within bounds",
        ),
        SpecTemplate::new(
            "loop_variant_decreasing",
            "{measure} >= 0 && {measure} decreases each iteration",
            vec!["measure".into()],
            SpecTemplateKind::Invariant,
            "Loop variant decreases toward zero (termination)",
        ),
        // --- Result type specs ---
        SpecTemplate::new(
            "result_ok_implies",
            "result.is_ok() ==> {condition}",
            vec!["condition".into()],
            SpecTemplateKind::Postcondition,
            "If the result is Ok, a condition holds",
        ),
        SpecTemplate::new(
            "result_err_implies",
            "result.is_err() ==> {condition}",
            vec!["condition".into()],
            SpecTemplateKind::Postcondition,
            "If the result is Err, a condition holds",
        ),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- instantiate_template ---

    #[test]
    fn test_instantiate_bounds_check() {
        let template = SpecTemplate::new(
            "bounds_check",
            "{index} < {bound}",
            vec!["index".into(), "bound".into()],
            SpecTemplateKind::Precondition,
            "test",
        );

        let mut bindings = FxHashMap::default();
        bindings.insert("index".to_string(), "i".to_string());
        bindings.insert("bound".to_string(), "arr.len()".to_string());

        let result = instantiate_template(&template, &bindings);
        assert_eq!(result, Some("i < arr.len()".to_string()));
    }

    #[test]
    fn test_instantiate_overflow_guard() {
        let template = SpecTemplate::new(
            "add_overflow_guard",
            "{a} <= {type_max} - {b}",
            vec!["a".into(), "b".into(), "type_max".into()],
            SpecTemplateKind::Precondition,
            "test",
        );

        let mut bindings = FxHashMap::default();
        bindings.insert("a".to_string(), "x".to_string());
        bindings.insert("b".to_string(), "y".to_string());
        bindings.insert("type_max".to_string(), "u64::MAX".to_string());

        let result = instantiate_template(&template, &bindings);
        assert_eq!(result, Some("x <= u64::MAX - y".to_string()));
    }

    #[test]
    fn test_instantiate_non_zero() {
        let template = SpecTemplate::new(
            "non_zero",
            "{var} != 0",
            vec!["var".into()],
            SpecTemplateKind::Precondition,
            "test",
        );

        let mut bindings = FxHashMap::default();
        bindings.insert("var".to_string(), "divisor".to_string());

        let result = instantiate_template(&template, &bindings);
        assert_eq!(result, Some("divisor != 0".to_string()));
    }

    #[test]
    fn test_instantiate_missing_parameter_returns_none() {
        let template = SpecTemplate::new(
            "bounds_check",
            "{index} < {bound}",
            vec!["index".into(), "bound".into()],
            SpecTemplateKind::Precondition,
            "test",
        );

        let mut bindings = FxHashMap::default();
        bindings.insert("index".to_string(), "i".to_string());
        // missing "bound"

        let result = instantiate_template(&template, &bindings);
        assert_eq!(result, None);
    }

    #[test]
    fn test_instantiate_extra_bindings_ignored() {
        let template = SpecTemplate::new(
            "non_zero",
            "{var} != 0",
            vec!["var".into()],
            SpecTemplateKind::Precondition,
            "test",
        );

        let mut bindings = FxHashMap::default();
        bindings.insert("var".to_string(), "x".to_string());
        bindings.insert("extra".to_string(), "ignored".to_string());

        let result = instantiate_template(&template, &bindings);
        assert_eq!(result, Some("x != 0".to_string()));
    }

    // --- standard_templates ---

    #[test]
    fn test_standard_templates_nonempty() {
        let templates = standard_templates();
        assert!(templates.len() >= 10, "should have at least 10 standard templates");
    }

    #[test]
    fn test_standard_templates_all_have_names() {
        for t in &standard_templates() {
            assert!(!t.name.is_empty(), "every template should have a name");
            assert!(!t.template.is_empty(), "every template should have a template string");
            assert!(!t.description.is_empty(), "every template should have a description");
        }
    }

    #[test]
    fn test_standard_templates_parameters_match_placeholders() {
        for t in &standard_templates() {
            for param in &t.parameters {
                let placeholder = format!("{{{param}}}");
                assert!(
                    t.template.contains(&placeholder),
                    "template '{}' declares parameter '{}' but template '{}' doesn't contain '{}'",
                    t.name,
                    param,
                    t.template,
                    placeholder
                );
            }
        }
    }

    #[test]
    fn test_bounds_check_template_instantiation() {
        let templates = standard_templates();
        let bounds = templates.iter().find(|t| t.name == "bounds_check").unwrap();

        let mut bindings = FxHashMap::default();
        bindings.insert("index".to_string(), "idx".to_string());
        bindings.insert("bound".to_string(), "n".to_string());

        let result = instantiate_template(bounds, &bindings);
        assert_eq!(result, Some("idx < n".to_string()));
    }

    #[test]
    fn test_sorted_ascending_template() {
        let templates = standard_templates();
        let sorted = templates.iter().find(|t| t.name == "sorted_ascending").unwrap();

        let mut bindings = FxHashMap::default();
        bindings.insert("collection".to_string(), "arr".to_string());

        let result = instantiate_template(sorted, &bindings);
        assert!(result.is_some());
        assert!(result.unwrap().contains("arr"));
    }

    #[test]
    fn test_permutation_template() {
        let templates = standard_templates();
        let perm = templates.iter().find(|t| t.name == "permutation").unwrap();

        let mut bindings = FxHashMap::default();
        bindings.insert("output".to_string(), "result".to_string());
        bindings.insert("input".to_string(), "original".to_string());

        let result = instantiate_template(perm, &bindings);
        assert_eq!(result, Some("result is a permutation of original".to_string()));
    }

    #[test]
    fn test_loop_bounds_invariant_template() {
        let templates = standard_templates();
        let inv = templates.iter().find(|t| t.name == "loop_bounds_invariant").unwrap();
        assert_eq!(inv.spec_kind, SpecTemplateKind::Invariant);

        let mut bindings = FxHashMap::default();
        bindings.insert("var".to_string(), "i".to_string());
        bindings.insert("lower".to_string(), "0".to_string());
        bindings.insert("upper".to_string(), "n".to_string());

        let result = instantiate_template(inv, &bindings);
        assert_eq!(result, Some("0 <= i && i <= n".to_string()));
    }

    #[test]
    fn test_result_ok_implies_template() {
        let templates = standard_templates();
        let ok_t = templates.iter().find(|t| t.name == "result_ok_implies").unwrap();
        assert_eq!(ok_t.spec_kind, SpecTemplateKind::Postcondition);

        let mut bindings = FxHashMap::default();
        bindings.insert("condition".to_string(), "value > 0".to_string());

        let result = instantiate_template(ok_t, &bindings);
        assert_eq!(result, Some("result.is_ok() ==> value > 0".to_string()));
    }

    // --- SpecTemplateKind ---

    #[test]
    fn test_spec_template_kind_equality() {
        assert_eq!(SpecTemplateKind::Precondition, SpecTemplateKind::Precondition);
        assert_ne!(SpecTemplateKind::Precondition, SpecTemplateKind::Postcondition);
        assert_ne!(SpecTemplateKind::Postcondition, SpecTemplateKind::Invariant);
    }

    // --- Integration: templates + counterexample hints ---

    #[test]
    fn test_template_with_counterexample_bindings() {
        // Simulate: counterexample shows i=5, len=3 for IndexOutOfBounds
        // We instantiate a bounds_check template with these concrete hints
        let templates = standard_templates();
        let bounds = templates.iter().find(|t| t.name == "bounds_check_len").unwrap();

        let mut bindings = FxHashMap::default();
        bindings.insert("index".to_string(), "i".to_string());
        bindings.insert("collection".to_string(), "arr".to_string());

        let result = instantiate_template(bounds, &bindings);
        assert_eq!(result, Some("i < arr.len()".to_string()));
    }

    #[test]
    fn test_template_mul_overflow_with_concrete_types() {
        let templates = standard_templates();
        let mul = templates.iter().find(|t| t.name == "mul_overflow_guard").unwrap();

        let mut bindings = FxHashMap::default();
        bindings.insert("a".to_string(), "width".to_string());
        bindings.insert("b".to_string(), "height".to_string());
        bindings.insert("type_max".to_string(), "u32::MAX".to_string());

        let result = instantiate_template(mul, &bindings);
        assert_eq!(result, Some("height == 0 || width <= u32::MAX / height".to_string()));
    }

    #[test]
    fn test_range_check_template() {
        let templates = standard_templates();
        let range = templates.iter().find(|t| t.name == "range_check").unwrap();
        assert_eq!(range.spec_kind, SpecTemplateKind::Precondition);

        let mut bindings = FxHashMap::default();
        bindings.insert("var".to_string(), "x".to_string());
        bindings.insert("lower".to_string(), "0".to_string());
        bindings.insert("upper".to_string(), "100".to_string());

        let result = instantiate_template(range, &bindings);
        assert_eq!(result, Some("0 <= x && x < 100".to_string()));
    }
}
