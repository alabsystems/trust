// trust-strengthen/pattern_library.rs: Common spec patterns for automatic application
//
// Captures well-known verification patterns (non-null, bounds check, non-empty,
// monotonic, etc.) and matches them to functions based on signature, counterexample
// values, and code structure. Complements the name-based pattern recognition in
// patterns.rs with type-driven and value-driven matching.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_types::fx::FxHashSet;
use trust_types::{Counterexample, CounterexampleValue};

use crate::proposer::{Proposal, ProposalKind};

/// A common verification pattern that can be automatically applied.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SpecPattern {
    /// Variable is non-null: `x != null` (or `x.is_some()` for Option).
    NonNull { variable: String },
    /// Variable is within bounds: `lo <= x && x < hi`.
    BoundsCheck { variable: String, lo: String, hi: String },
    /// Collection is non-empty: `!col.is_empty()`.
    NonEmpty { collection: String },
    /// Variable is monotonically changing.
    Monotonic { variable: String, direction: MonotonicDirection },
    /// Loop invariant over a specific loop.
    Invariant { loop_id: String, formula: String },
    /// Return value is bounded: `lo <= result && result <= hi`.
    ReturnBounds { function: String, lo: String, hi: String },
    /// Divisor is non-zero: `divisor != 0`.
    NonZeroDivisor { variable: String },
    /// Index is within array bounds: `idx < arr.len()`.
    IndexInBounds { index: String, collection: String },
    /// Collection is sorted in ascending order: `collection.is_sorted()`.
    /// Precondition inference for binary search.
    Sorted { collection: String },
}

/// Direction for monotonic patterns.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MonotonicDirection {
    /// Variable increases over iterations.
    Increasing,
    /// Variable decreases over iterations.
    Decreasing,
}

impl SpecPattern {
    /// Convert this pattern into a spec body string.
    #[must_use]
    pub fn to_spec_body(&self) -> String {
        match self {
            Self::NonNull { variable } => format!("{variable}.is_some()"),
            Self::BoundsCheck { variable, lo, hi } => {
                format!("{lo} <= {variable} && {variable} < {hi}")
            }
            Self::NonEmpty { collection } => format!("!{collection}.is_empty()"),
            Self::Monotonic { variable, direction } => {
                let dir = match direction {
                    MonotonicDirection::Increasing => "monotonically increasing",
                    MonotonicDirection::Decreasing => "monotonically decreasing",
                };
                format!("{variable} is {dir}")
            }
            Self::Invariant { formula, .. } => formula.clone(),
            Self::ReturnBounds { lo, hi, .. } => {
                format!("{lo} <= result && result <= {hi}")
            }
            Self::NonZeroDivisor { variable } => format!("{variable} != 0"),
            Self::IndexInBounds { index, collection } => {
                format!("{index} < {collection}.len()")
            }
            Self::Sorted { collection } => {
                format!("{collection}.is_sorted()")
            }
        }
    }

    /// Descriptive name for this pattern kind.
    #[must_use]
    pub fn kind_name(&self) -> &'static str {
        match self {
            Self::NonNull { .. } => "non_null",
            Self::BoundsCheck { .. } => "bounds_check",
            Self::NonEmpty { .. } => "non_empty",
            Self::Monotonic { .. } => "monotonic",
            Self::Invariant { .. } => "invariant",
            Self::ReturnBounds { .. } => "return_bounds",
            Self::NonZeroDivisor { .. } => "non_zero_divisor",
            Self::IndexInBounds { .. } => "index_in_bounds",
            Self::Sorted { .. } => "sorted",
        }
    }
}

/// A spec suggestion derived from pattern matching.
#[derive(Debug, Clone)]
pub struct PatternSuggestion {
    /// The pattern that was matched.
    pub pattern: SpecPattern,
    /// Confidence in this suggestion.
    pub confidence: f64,
    /// Rationale for why this pattern applies.
    pub rationale: String,
}

/// Matches applicable patterns from function signatures and counterexamples.
pub struct PatternMatcher {
    /// Minimum confidence to include a suggestion.
    min_confidence: f64,
}

impl PatternMatcher {
    /// Create a new pattern matcher with the given minimum confidence.
    #[must_use]
    pub fn new(min_confidence: f64) -> Self {
        Self { min_confidence }
    }

    /// Detect applicable patterns from a function's parameter types.
    #[must_use]
    pub fn match_from_signature(&self, params: &[(&str, &str)]) -> Vec<PatternSuggestion> {
        let mut suggestions = Vec::new();

        for &(name, ty) in params {
            // Option parameters suggest NonNull
            if ty.starts_with("Option<") {
                suggestions.push(PatternSuggestion {
                    pattern: SpecPattern::NonNull { variable: name.into() },
                    confidence: 0.6,
                    rationale: format!("Option parameter `{name}` may be unwrapped"),
                });
            }

            // Slice/Vec parameters suggest NonEmpty
            if ty.starts_with("&[") || ty.starts_with("&mut [") || ty.starts_with("Vec<") {
                suggestions.push(PatternSuggestion {
                    pattern: SpecPattern::NonEmpty { collection: name.into() },
                    confidence: 0.5,
                    rationale: format!("Collection parameter `{name}` may need non-empty check"),
                });
            }

            // usize parameters with index-like names suggest IndexInBounds
            if ty == "usize" && is_index_name(name) {
                let collection = guess_collection_name(params, name);
                suggestions.push(PatternSuggestion {
                    pattern: SpecPattern::IndexInBounds { index: name.into(), collection },
                    confidence: 0.65,
                    rationale: format!("Parameter `{name}: usize` likely used as index"),
                });
            }

            // Numeric parameters with divisor-like names suggest NonZeroDivisor
            if is_numeric_type(ty) && is_divisor_name(name) {
                suggestions.push(PatternSuggestion {
                    pattern: SpecPattern::NonZeroDivisor { variable: name.into() },
                    confidence: 0.8,
                    rationale: format!("Parameter `{name}` likely used as divisor"),
                });
            }
        }

        suggestions.into_iter().filter(|s| s.confidence >= self.min_confidence).collect()
    }

    /// Detect applicable patterns using both function name and parameter types.
    ///
    /// This extends `match_from_signature` with function-name-based heuristics.
    /// For example, a function named `binary_search` with a slice parameter gets
    /// a high-confidence `Sorted` precondition suggestion.
    /// is_sorted precondition inference for binary search.
    #[must_use]
    pub fn match_from_signature_with_name(
        &self,
        func_name: &str,
        params: &[(&str, &str)],
    ) -> Vec<PatternSuggestion> {
        let mut suggestions = self.match_from_signature(params);

        let lower_name = func_name.to_lowercase();
        let is_search_fn = lower_name.contains("binary_search")
            || lower_name.contains("bsearch")
            || lower_name.contains("bisect")
            || lower_name.contains("lower_bound")
            || lower_name.contains("upper_bound");

        if is_search_fn {
            // Find the slice/vec parameter to use as the sorted collection
            let collection_name = params
                .iter()
                .find(|(_, ty)| {
                    ty.starts_with("&[") || ty.starts_with("&mut [") || ty.starts_with("Vec<")
                })
                .map(|(name, _)| (*name).to_string())
                .unwrap_or_else(|| "slice".to_string());

            suggestions.push(PatternSuggestion {
                pattern: SpecPattern::Sorted { collection: collection_name.clone() },
                confidence: 0.92,
                rationale: format!(
                    "Binary search requires `{collection_name}` to be sorted in ascending order"
                ),
            });
        }

        suggestions.into_iter().filter(|s| s.confidence >= self.min_confidence).collect()
    }

    /// Detect applicable patterns from counterexample values.
    #[must_use]
    pub fn match_from_counterexamples(
        &self,
        counterexamples: &[Counterexample],
    ) -> Vec<PatternSuggestion> {
        let mut suggestions = Vec::new();

        for cex in counterexamples {
            for (name, value) in &cex.assignments {
                match value {
                    // Zero values suggest NonZeroDivisor
                    CounterexampleValue::Uint(0) | CounterexampleValue::Int(0) => {
                        suggestions.push(PatternSuggestion {
                            pattern: SpecPattern::NonZeroDivisor { variable: name.clone() },
                            confidence: 0.75,
                            rationale: format!(
                                "Counterexample has {name} = 0, suggesting non-zero requirement"
                            ),
                        });
                    }
                    // Very large unsigned values suggest overflow / bounds
                    CounterexampleValue::Uint(v) if *v > (u64::MAX as u128 - 100) => {
                        suggestions.push(PatternSuggestion {
                            pattern: SpecPattern::BoundsCheck {
                                variable: name.clone(),
                                lo: "0".into(),
                                hi: format!("{}", u64::MAX / 2),
                            },
                            confidence: 0.7,
                            rationale: format!(
                                "Counterexample has {name} near MAX, suggesting bounds check"
                            ),
                        });
                    }
                    // Negative values for signed types may suggest bounds
                    CounterexampleValue::Int(v) if *v < 0 => {
                        suggestions.push(PatternSuggestion {
                            pattern: SpecPattern::BoundsCheck {
                                variable: name.clone(),
                                lo: "0".into(),
                                hi: "MAX".into(),
                            },
                            confidence: 0.55,
                            rationale: format!(
                                "Counterexample has {name} = {v} (negative), suggesting non-negative bound"
                            ),
                        });
                    }
                    _ => {}
                }
            }
        }

        suggestions.into_iter().filter(|s| s.confidence >= self.min_confidence).collect()
    }
}

impl Default for PatternMatcher {
    fn default() -> Self {
        Self::new(0.5)
    }
}

/// Database of known-good patterns with their historical success rates.
pub struct PatternDatabase {
    /// Pattern kind name -> (successes, total attempts).
    success_records: BTreeMap<String, (u64, u64)>,
}

impl PatternDatabase {
    /// Create a new empty pattern database.
    #[must_use]
    pub fn new() -> Self {
        Self { success_records: BTreeMap::new() }
    }

    /// Record whether applying a pattern succeeded.
    pub fn record_outcome(&mut self, pattern: &SpecPattern, succeeded: bool) {
        let key = pattern.kind_name().to_string();
        let entry = self.success_records.entry(key).or_insert((0, 0));
        if succeeded {
            entry.0 += 1;
        }
        entry.1 += 1;
    }

    /// Get the success rate for a pattern kind.
    #[must_use]
    pub fn success_rate(&self, pattern: &SpecPattern) -> Option<f64> {
        let key = pattern.kind_name();
        self.success_records.get(key).and_then(|&(successes, total)| {
            if total > 0 { Some(successes as f64 / total as f64) } else { None }
        })
    }

    /// Boost a suggestion's confidence based on historical success rate.
    #[must_use]
    pub fn adjust_confidence(&self, suggestion: &PatternSuggestion) -> f64 {
        match self.success_rate(&suggestion.pattern) {
            Some(rate) => {
                // Blend: 70% original confidence + 30% historical rate
                (0.7 * suggestion.confidence + 0.3 * rate).clamp(0.0, 1.0)
            }
            None => suggestion.confidence,
        }
    }

    /// Get total recorded outcomes across all patterns.
    #[must_use]
    pub fn total_records(&self) -> u64 {
        self.success_records.values().map(|&(_, t)| t).sum()
    }
}

impl Default for PatternDatabase {
    fn default() -> Self {
        Self::new()
    }
}

/// Apply pattern matching to a function signature and counterexamples,
/// returning spec proposals ready for the strengthen pipeline.
#[must_use]
pub fn apply_patterns(
    function_path: &str,
    function_name: &str,
    params: &[(&str, &str)],
    counterexamples: &[Counterexample],
) -> Vec<Proposal> {
    let matcher = PatternMatcher::default();

    let mut suggestions = matcher.match_from_signature(params);
    suggestions.extend(matcher.match_from_counterexamples(counterexamples));

    // Deduplicate by pattern kind + variable
    dedup_suggestions(&mut suggestions);

    suggestions
        .into_iter()
        .map(|s| suggestion_to_proposal(function_path, function_name, &s))
        .collect()
}

/// Apply patterns with a database for confidence adjustment.
#[must_use]
pub fn apply_patterns_with_db(
    function_path: &str,
    function_name: &str,
    params: &[(&str, &str)],
    counterexamples: &[Counterexample],
    db: &PatternDatabase,
) -> Vec<Proposal> {
    let matcher = PatternMatcher::default();

    let mut suggestions = matcher.match_from_signature(params);
    suggestions.extend(matcher.match_from_counterexamples(counterexamples));

    dedup_suggestions(&mut suggestions);

    suggestions
        .into_iter()
        .map(|s| {
            let adjusted_confidence = db.adjust_confidence(&s);
            let mut proposal = suggestion_to_proposal(function_path, function_name, &s);
            proposal.confidence = adjusted_confidence;
            proposal
        })
        .collect()
}

/// Convert a pattern suggestion into a Proposal.
fn suggestion_to_proposal(
    function_path: &str,
    function_name: &str,
    suggestion: &PatternSuggestion,
) -> Proposal {
    let (kind, confidence_modifier) = match &suggestion.pattern {
        SpecPattern::Invariant { .. } => {
            (ProposalKind::AddInvariant { spec_body: suggestion.pattern.to_spec_body() }, 0.0)
        }
        SpecPattern::ReturnBounds { .. } => {
            (ProposalKind::AddPostcondition { spec_body: suggestion.pattern.to_spec_body() }, 0.0)
        }
        SpecPattern::IndexInBounds { .. } => (
            ProposalKind::AddBoundsCheck {
                check_expr: format!("assert!({})", suggestion.pattern.to_spec_body()),
            },
            0.0,
        ),
        SpecPattern::NonZeroDivisor { variable } => (
            ProposalKind::AddNonZeroCheck {
                check_expr: format!("assert!({variable} != 0, \"division by zero\")"),
            },
            0.0,
        ),
        _ => (ProposalKind::AddPrecondition { spec_body: suggestion.pattern.to_spec_body() }, 0.0),
    };

    Proposal {
        function_path: function_path.into(),
        function_name: function_name.into(),
        kind,
        confidence: (suggestion.confidence + confidence_modifier).clamp(0.0, 1.0),
        rationale: suggestion.rationale.clone(),
    }
}

/// Deduplicate suggestions by pattern kind + key variable.
fn dedup_suggestions(suggestions: &mut Vec<PatternSuggestion>) {
    let mut seen = FxHashSet::default();
    suggestions.retain(|s| {
        let key = format!("{}:{}", s.pattern.kind_name(), s.pattern.to_spec_body());
        seen.insert(key)
    });
}

/// Check if a parameter name looks like an index variable.
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

/// Check if a parameter name looks like a divisor.
fn is_divisor_name(name: &str) -> bool {
    let lower = name.to_lowercase();
    lower == "divisor"
        || lower == "denominator"
        || lower == "denom"
        || lower == "d"
        || lower == "modulus"
        || lower.ends_with("_divisor")
}

/// Check if a type string represents a numeric type.
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

/// Guess the collection name for an index parameter.
fn guess_collection_name(params: &[(&str, &str)], _index_param: &str) -> String {
    // Look for a slice or Vec parameter
    for &(name, ty) in params {
        if ty.starts_with("&[") || ty.starts_with("&mut [") || ty.starts_with("Vec<") {
            return name.into();
        }
    }
    "collection".into()
}

// ---------------------------------------------------------------------------
// Reusable spec pattern catalog
// ---------------------------------------------------------------------------

/// Category of specification patterns for organizational grouping.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum PatternCategory {
    /// Bounds checking patterns (index < len, value in range).
    BoundsCheck,
    /// Null/None safety patterns (Option::is_some, non-null pointers).
    NullSafety,
    /// Arithmetic overflow prevention patterns.
    Overflow,
    /// Aliasing and ownership safety patterns.
    Aliasing,
    /// Loop termination and progress patterns.
    Termination,
    /// Purity / side-effect-freedom patterns.
    Purity,
}

impl PatternCategory {
    /// Human-readable label for this category.
    #[must_use]
    pub fn label(&self) -> &'static str {
        match self {
            Self::BoundsCheck => "bounds-check",
            Self::NullSafety => "null-safety",
            Self::Overflow => "overflow",
            Self::Aliasing => "aliasing",
            Self::Termination => "termination",
            Self::Purity => "purity",
        }
    }
}

/// A reusable, cataloged specification pattern with applicability metadata.
///
/// Unlike [`SpecPattern`] (which encodes a concrete matched instance),
/// `CatalogEntry` describes a *template* that can be instantiated with
/// concrete types and variable names via [`instantiate_pattern`].
#[derive(Debug, Clone, PartialEq)]
pub struct CatalogEntry {
    /// Short human-readable name (e.g. "index-in-bounds").
    pub name: String,
    /// Template string with placeholders: `{param}`, `{collection}`, `{type}`.
    pub template: String,
    /// Category this pattern belongs to.
    pub category: PatternCategory,
    /// Parameter type names that make this pattern applicable
    /// (e.g. `["usize"]` for an index pattern, `["Option"]` for null-safety).
    pub applicable_param_types: Vec<String>,
    /// Parameter name substrings that trigger applicability
    /// (e.g. `["idx", "index"]`).
    pub applicable_param_names: Vec<String>,
    /// Base confidence when this pattern matches.
    pub base_confidence: f64,
}

/// Describes how a catalog pattern matched a concrete function parameter.
#[derive(Debug, Clone, PartialEq)]
pub struct CatalogMatch {
    /// The catalog entry that matched.
    pub entry: CatalogEntry,
    /// The parameter name that triggered the match.
    pub matched_param: String,
    /// The parameter type that triggered the match.
    pub matched_type: String,
    /// Confidence score (0.0 -- 1.0), possibly adjusted from `base_confidence`.
    pub confidence: f64,
    /// Instantiated spec body with placeholders replaced.
    pub instantiated: String,
}

/// A collection of [`CatalogEntry`] patterns.
#[derive(Debug, Clone, Default)]
pub struct PatternCatalog {
    entries: Vec<CatalogEntry>,
}

impl PatternCatalog {
    /// Create an empty catalog.
    #[must_use]
    pub fn new() -> Self {
        Self { entries: Vec::new() }
    }

    /// Add a pattern to the catalog.
    pub fn add(&mut self, entry: CatalogEntry) {
        self.entries.push(entry);
    }

    /// Number of patterns in the catalog.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the catalog is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Iterate over catalog entries.
    pub fn iter(&self) -> impl Iterator<Item = &CatalogEntry> {
        self.entries.iter()
    }

    /// Filter entries by category.
    #[must_use]
    pub fn by_category(&self, cat: PatternCategory) -> Vec<&CatalogEntry> {
        self.entries.iter().filter(|e| e.category == cat).collect()
    }
}

/// Create the default catalog of builtin specification patterns.
///
/// Returns a [`PatternCatalog`] populated with well-known verification
/// patterns covering bounds checks, null safety, overflow, aliasing,
/// termination, and purity.
#[must_use]
pub fn builtin_patterns() -> PatternCatalog {
    let mut catalog = PatternCatalog::new();

    // --- BoundsCheck patterns ---
    catalog.add(CatalogEntry {
        name: "index-in-bounds".into(),
        template: "{param} < {collection}.len()".into(),
        category: PatternCategory::BoundsCheck,
        applicable_param_types: vec!["usize".into()],
        applicable_param_names: vec![
            "i".into(),
            "j".into(),
            "k".into(),
            "idx".into(),
            "index".into(),
            "pos".into(),
            "offset".into(),
        ],
        base_confidence: 0.75,
    });

    catalog.add(CatalogEntry {
        name: "range-bounds".into(),
        template: "{lo} <= {param} && {param} < {hi}".into(),
        category: PatternCategory::BoundsCheck,
        applicable_param_types: vec![
            "usize".into(),
            "u32".into(),
            "u64".into(),
            "i32".into(),
            "i64".into(),
        ],
        applicable_param_names: vec!["start".into(), "end".into(), "range".into(), "bound".into()],
        base_confidence: 0.6,
    });

    catalog.add(CatalogEntry {
        name: "non-empty-collection".into(),
        template: "!{param}.is_empty()".into(),
        category: PatternCategory::BoundsCheck,
        applicable_param_types: vec!["Vec".into(), "&[".into(), "&mut [".into()],
        applicable_param_names: vec![],
        base_confidence: 0.55,
    });

    // sorted-collection pattern for binary search precondition inference.
    catalog.add(CatalogEntry {
        name: "sorted-collection".into(),
        template: "{param}.is_sorted()".into(),
        category: PatternCategory::BoundsCheck,
        applicable_param_types: vec!["&[".into(), "&mut [".into(), "Vec".into()],
        applicable_param_names: vec!["sorted".into(), "haystack".into()],
        base_confidence: 0.7,
    });

    // --- NullSafety patterns ---
    catalog.add(CatalogEntry {
        name: "option-is-some".into(),
        template: "{param}.is_some()".into(),
        category: PatternCategory::NullSafety,
        applicable_param_types: vec!["Option".into()],
        applicable_param_names: vec![],
        base_confidence: 0.65,
    });

    catalog.add(CatalogEntry {
        name: "result-is-ok".into(),
        template: "{param}.is_ok()".into(),
        category: PatternCategory::NullSafety,
        applicable_param_types: vec!["Result".into()],
        applicable_param_names: vec![],
        base_confidence: 0.5,
    });

    // --- Overflow patterns ---
    catalog.add(CatalogEntry {
        name: "non-zero-divisor".into(),
        template: "{param} != 0".into(),
        category: PatternCategory::Overflow,
        applicable_param_types: vec![
            "u8".into(),
            "u16".into(),
            "u32".into(),
            "u64".into(),
            "u128".into(),
            "usize".into(),
            "i8".into(),
            "i16".into(),
            "i32".into(),
            "i64".into(),
            "i128".into(),
            "isize".into(),
        ],
        applicable_param_names: vec![
            "divisor".into(),
            "denominator".into(),
            "denom".into(),
            "modulus".into(),
        ],
        base_confidence: 0.85,
    });

    catalog.add(CatalogEntry {
        name: "addition-no-overflow".into(),
        template: "{param} <= {type}::MAX - {other}".into(),
        category: PatternCategory::Overflow,
        applicable_param_types: vec![
            "u8".into(),
            "u16".into(),
            "u32".into(),
            "u64".into(),
            "u128".into(),
            "usize".into(),
        ],
        applicable_param_names: vec![],
        base_confidence: 0.7,
    });

    catalog.add(CatalogEntry {
        name: "shift-in-range".into(),
        template: "{param} < {bit_width}".into(),
        category: PatternCategory::Overflow,
        applicable_param_types: vec!["u32".into(), "usize".into()],
        applicable_param_names: vec!["shift".into(), "shift_amount".into(), "bits".into()],
        base_confidence: 0.8,
    });

    // --- Aliasing patterns ---
    catalog.add(CatalogEntry {
        name: "no-alias".into(),
        template: "no_alias({param_a}, {param_b})".into(),
        category: PatternCategory::Aliasing,
        applicable_param_types: vec!["&mut".into()],
        applicable_param_names: vec![],
        base_confidence: 0.6,
    });

    // --- Termination patterns ---
    catalog.add(CatalogEntry {
        name: "loop-variant-decreasing".into(),
        template: "{param} is monotonically decreasing".into(),
        category: PatternCategory::Termination,
        applicable_param_types: vec!["usize".into(), "u32".into(), "u64".into()],
        applicable_param_names: vec![
            "fuel".into(),
            "remaining".into(),
            "budget".into(),
            "gas".into(),
            "count".into(),
        ],
        base_confidence: 0.7,
    });

    // --- Purity patterns ---
    catalog.add(CatalogEntry {
        name: "pure-function".into(),
        template: "pure({fn_name})".into(),
        category: PatternCategory::Purity,
        applicable_param_types: vec![],
        applicable_param_names: vec![],
        base_confidence: 0.4,
    });

    catalog
}

/// Find all catalog entries that match a given function parameter.
///
/// A pattern matches if the parameter type contains any of the entry's
/// `applicable_param_types` OR the parameter name matches any of the
/// entry's `applicable_param_names`.
#[must_use]
pub fn match_pattern(
    catalog: &PatternCatalog,
    param_name: &str,
    param_type: &str,
) -> Vec<CatalogMatch> {
    let lower_name = param_name.to_lowercase();

    catalog
        .iter()
        .filter(|entry| {
            let type_match =
                entry.applicable_param_types.iter().any(|t| param_type.contains(t.as_str()));
            let name_match = entry.applicable_param_names.iter().any(|n| {
                lower_name == n.to_lowercase()
                    || lower_name.ends_with(&format!("_{}", n.to_lowercase()))
            });
            type_match || name_match
        })
        .map(|entry| {
            let instantiated = instantiate_pattern(&entry.template, param_name, param_type);
            CatalogMatch {
                entry: entry.clone(),
                matched_param: param_name.into(),
                matched_type: param_type.into(),
                confidence: entry.base_confidence,
                instantiated,
            }
        })
        .collect()
}

/// Replace placeholders in a pattern template with concrete values.
///
/// Supported placeholders:
/// - `{param}` -- replaced with `param_name`
/// - `{type}` -- replaced with `param_type`
/// - `{collection}` -- replaced with `"collection"` (default; caller can
///   post-process for a better name)
/// - `{lo}`, `{hi}` -- replaced with `"0"` and `"{type}::MAX"` respectively
/// - `{other}` -- replaced with `"other"`
/// - `{bit_width}` -- replaced with the bit width of the type
/// - `{fn_name}` -- replaced with `param_name` (reused for function context)
/// - `{param_a}`, `{param_b}` -- replaced with `param_name` and `"other"`
#[must_use]
pub fn instantiate_pattern(template: &str, param_name: &str, param_type: &str) -> String {
    let bit_width = match param_type {
        "u8" | "i8" => "8",
        "u16" | "i16" => "16",
        "u32" | "i32" => "32",
        "u64" | "i64" => "64",
        "u128" | "i128" => "128",
        _ => "64",
    };

    template
        .replace("{param}", param_name)
        .replace("{type}", param_type)
        .replace("{collection}", "collection")
        .replace("{lo}", "0")
        .replace("{hi}", &format!("{param_type}::MAX"))
        .replace("{other}", "other")
        .replace("{bit_width}", bit_width)
        .replace("{fn_name}", param_name)
        .replace("{param_a}", param_name)
        .replace("{param_b}", "other")
}

#[cfg(test)]
mod tests {
    use trust_types::{Counterexample, CounterexampleValue};

    use super::*;

    // --- SpecPattern ---

    #[test]
    fn test_spec_pattern_non_null_to_spec_body() {
        let pattern = SpecPattern::NonNull { variable: "config".into() };
        assert_eq!(pattern.to_spec_body(), "config.is_some()");
    }

    #[test]
    fn test_spec_pattern_bounds_check_to_spec_body() {
        let pattern =
            SpecPattern::BoundsCheck { variable: "x".into(), lo: "0".into(), hi: "100".into() };
        assert_eq!(pattern.to_spec_body(), "0 <= x && x < 100");
    }

    #[test]
    fn test_spec_pattern_non_empty_to_spec_body() {
        let pattern = SpecPattern::NonEmpty { collection: "items".into() };
        assert_eq!(pattern.to_spec_body(), "!items.is_empty()");
    }

    #[test]
    fn test_spec_pattern_monotonic_increasing() {
        let pattern = SpecPattern::Monotonic {
            variable: "counter".into(),
            direction: MonotonicDirection::Increasing,
        };
        assert_eq!(pattern.to_spec_body(), "counter is monotonically increasing");
    }

    #[test]
    fn test_spec_pattern_monotonic_decreasing() {
        let pattern = SpecPattern::Monotonic {
            variable: "fuel".into(),
            direction: MonotonicDirection::Decreasing,
        };
        assert_eq!(pattern.to_spec_body(), "fuel is monotonically decreasing");
    }

    #[test]
    fn test_spec_pattern_invariant() {
        let pattern =
            SpecPattern::Invariant { loop_id: "loop_0".into(), formula: "0 <= i && i <= n".into() };
        assert_eq!(pattern.to_spec_body(), "0 <= i && i <= n");
    }

    #[test]
    fn test_spec_pattern_return_bounds() {
        let pattern = SpecPattern::ReturnBounds {
            function: "clamp".into(),
            lo: "min_val".into(),
            hi: "max_val".into(),
        };
        assert_eq!(pattern.to_spec_body(), "min_val <= result && result <= max_val");
    }

    #[test]
    fn test_spec_pattern_non_zero_divisor() {
        let pattern = SpecPattern::NonZeroDivisor { variable: "denom".into() };
        assert_eq!(pattern.to_spec_body(), "denom != 0");
    }

    #[test]
    fn test_spec_pattern_index_in_bounds() {
        let pattern = SpecPattern::IndexInBounds { index: "i".into(), collection: "arr".into() };
        assert_eq!(pattern.to_spec_body(), "i < arr.len()");
    }

    #[test]
    fn test_spec_pattern_kind_names() {
        let patterns: Vec<(SpecPattern, &str)> = vec![
            (SpecPattern::NonNull { variable: "x".into() }, "non_null"),
            (
                SpecPattern::BoundsCheck { variable: "x".into(), lo: "0".into(), hi: "10".into() },
                "bounds_check",
            ),
            (SpecPattern::NonEmpty { collection: "v".into() }, "non_empty"),
            (
                SpecPattern::Monotonic {
                    variable: "c".into(),
                    direction: MonotonicDirection::Increasing,
                },
                "monotonic",
            ),
            (SpecPattern::Invariant { loop_id: "l".into(), formula: "f".into() }, "invariant"),
            (
                SpecPattern::ReturnBounds { function: "f".into(), lo: "0".into(), hi: "1".into() },
                "return_bounds",
            ),
            (SpecPattern::NonZeroDivisor { variable: "d".into() }, "non_zero_divisor"),
            (
                SpecPattern::IndexInBounds { index: "i".into(), collection: "a".into() },
                "index_in_bounds",
            ),
        ];
        for (pattern, expected_name) in &patterns {
            assert_eq!(pattern.kind_name(), *expected_name, "wrong kind_name for {pattern:?}");
        }
    }

    // --- PatternMatcher from signature ---

    #[test]
    fn test_matcher_option_param_suggests_non_null() {
        let matcher = PatternMatcher::default();
        let suggestions = matcher.match_from_signature(&[("config", "Option<Config>")]);
        assert_eq!(suggestions.len(), 1);
        assert!(matches!(
            suggestions[0].pattern,
            SpecPattern::NonNull { ref variable } if variable == "config"
        ));
    }

    #[test]
    fn test_matcher_slice_param_suggests_non_empty() {
        let matcher = PatternMatcher::default();
        let suggestions = matcher.match_from_signature(&[("items", "&[i32]")]);
        assert_eq!(suggestions.len(), 1);
        assert!(matches!(
            suggestions[0].pattern,
            SpecPattern::NonEmpty { ref collection } if collection == "items"
        ));
    }

    #[test]
    fn test_matcher_vec_param_suggests_non_empty() {
        let matcher = PatternMatcher::default();
        let suggestions = matcher.match_from_signature(&[("data", "Vec<u8>")]);
        assert_eq!(suggestions.len(), 1);
        assert!(matches!(
            suggestions[0].pattern,
            SpecPattern::NonEmpty { ref collection } if collection == "data"
        ));
    }

    #[test]
    fn test_matcher_index_param_suggests_index_in_bounds() {
        let matcher = PatternMatcher::default();
        let suggestions = matcher.match_from_signature(&[("arr", "&[i32]"), ("idx", "usize")]);
        let index_suggestion =
            suggestions.iter().find(|s| matches!(s.pattern, SpecPattern::IndexInBounds { .. }));
        assert!(index_suggestion.is_some());
        if let SpecPattern::IndexInBounds { ref index, ref collection } =
            index_suggestion.unwrap().pattern
        {
            assert_eq!(index, "idx");
            assert_eq!(collection, "arr");
        }
    }

    #[test]
    fn test_matcher_divisor_param_suggests_non_zero() {
        let matcher = PatternMatcher::default();
        let suggestions = matcher.match_from_signature(&[("x", "u64"), ("divisor", "u64")]);
        let divisor_suggestion =
            suggestions.iter().find(|s| matches!(s.pattern, SpecPattern::NonZeroDivisor { .. }));
        assert!(divisor_suggestion.is_some());
    }

    #[test]
    fn test_matcher_respects_min_confidence() {
        let matcher = PatternMatcher::new(0.9);
        let suggestions = matcher.match_from_signature(&[("items", "&[i32]")]);
        // Non-empty has confidence 0.5, should be filtered
        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_matcher_no_suggestions_for_plain_types() {
        let matcher = PatternMatcher::default();
        let suggestions = matcher.match_from_signature(&[("x", "i32"), ("y", "i32")]);
        assert!(suggestions.is_empty());
    }

    // --- PatternMatcher from counterexamples ---

    #[test]
    fn test_matcher_cex_zero_value_suggests_non_zero() {
        let matcher = PatternMatcher::default();
        let cex = Counterexample::new(vec![("y".into(), CounterexampleValue::Uint(0))]);
        let suggestions = matcher.match_from_counterexamples(&[cex]);
        let has_non_zero =
            suggestions.iter().any(|s| matches!(s.pattern, SpecPattern::NonZeroDivisor { .. }));
        assert!(has_non_zero);
    }

    #[test]
    fn test_matcher_cex_large_value_suggests_bounds() {
        let matcher = PatternMatcher::default();
        let cex =
            Counterexample::new(vec![("a".into(), CounterexampleValue::Uint(u64::MAX as u128))]);
        let suggestions = matcher.match_from_counterexamples(&[cex]);
        let has_bounds =
            suggestions.iter().any(|s| matches!(s.pattern, SpecPattern::BoundsCheck { .. }));
        assert!(has_bounds);
    }

    #[test]
    fn test_matcher_cex_negative_value_suggests_bounds() {
        let matcher = PatternMatcher::default();
        let cex = Counterexample::new(vec![("x".into(), CounterexampleValue::Int(-5))]);
        let suggestions = matcher.match_from_counterexamples(&[cex]);
        let has_bounds =
            suggestions.iter().any(|s| matches!(s.pattern, SpecPattern::BoundsCheck { .. }));
        assert!(has_bounds);
    }

    #[test]
    fn test_matcher_cex_normal_values_no_suggestions() {
        let matcher = PatternMatcher::default();
        let cex = Counterexample::new(vec![
            ("x".into(), CounterexampleValue::Uint(42)),
            ("y".into(), CounterexampleValue::Uint(7)),
        ]);
        let suggestions = matcher.match_from_counterexamples(&[cex]);
        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_matcher_multiple_counterexamples() {
        let matcher = PatternMatcher::default();
        let cex1 = Counterexample::new(vec![("y".into(), CounterexampleValue::Uint(0))]);
        let cex2 =
            Counterexample::new(vec![("x".into(), CounterexampleValue::Uint(u64::MAX as u128))]);
        let suggestions = matcher.match_from_counterexamples(&[cex1, cex2]);
        assert!(suggestions.len() >= 2);
    }

    // --- PatternDatabase ---

    #[test]
    fn test_database_empty_returns_none() {
        let db = PatternDatabase::new();
        let pattern = SpecPattern::NonZeroDivisor { variable: "x".into() };
        assert_eq!(db.success_rate(&pattern), None);
    }

    #[test]
    fn test_database_tracks_success_rate() {
        let mut db = PatternDatabase::new();
        let pattern = SpecPattern::NonZeroDivisor { variable: "x".into() };

        db.record_outcome(&pattern, true);
        db.record_outcome(&pattern, true);
        db.record_outcome(&pattern, false);

        let rate = db.success_rate(&pattern).expect("should have data");
        assert!((rate - 2.0 / 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_database_groups_by_kind() {
        let mut db = PatternDatabase::new();
        let p1 = SpecPattern::NonZeroDivisor { variable: "x".into() };
        let p2 = SpecPattern::NonZeroDivisor { variable: "y".into() };

        db.record_outcome(&p1, true);
        db.record_outcome(&p2, false);

        // Both are "non_zero_divisor", so grouped together
        let rate = db.success_rate(&p1).expect("should have data");
        assert!((rate - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_database_adjust_confidence() {
        let mut db = PatternDatabase::new();
        let pattern = SpecPattern::NonZeroDivisor { variable: "d".into() };

        // Record 100% success
        for _ in 0..10 {
            db.record_outcome(&pattern, true);
        }

        let suggestion = PatternSuggestion {
            pattern: pattern.clone(),
            confidence: 0.5,
            rationale: "test".into(),
        };

        let adjusted = db.adjust_confidence(&suggestion);
        // 0.7 * 0.5 + 0.3 * 1.0 = 0.65
        assert!((adjusted - 0.65).abs() < f64::EPSILON);
    }

    #[test]
    fn test_database_adjust_no_data_returns_original() {
        let db = PatternDatabase::new();
        let suggestion = PatternSuggestion {
            pattern: SpecPattern::NonEmpty { collection: "v".into() },
            confidence: 0.7,
            rationale: "test".into(),
        };
        let adjusted = db.adjust_confidence(&suggestion);
        assert!((adjusted - 0.7).abs() < f64::EPSILON);
    }

    #[test]
    fn test_database_total_records() {
        let mut db = PatternDatabase::new();
        db.record_outcome(&SpecPattern::NonZeroDivisor { variable: "x".into() }, true);
        db.record_outcome(&SpecPattern::NonEmpty { collection: "v".into() }, false);
        assert_eq!(db.total_records(), 2);
    }

    // --- apply_patterns ---

    #[test]
    fn test_apply_patterns_from_signature() {
        let proposals = apply_patterns(
            "test::safe_divide",
            "safe_divide",
            &[("x", "u64"), ("divisor", "u64")],
            &[],
        );
        let has_nonzero =
            proposals.iter().any(|p| matches!(p.kind, ProposalKind::AddNonZeroCheck { .. }));
        assert!(has_nonzero, "should propose non-zero check for divisor param");
    }

    #[test]
    fn test_apply_patterns_from_counterexample() {
        let cex = Counterexample::new(vec![("y".into(), CounterexampleValue::Uint(0))]);
        let proposals = apply_patterns("test::f", "f", &[], &[cex]);
        assert!(!proposals.is_empty());
    }

    #[test]
    fn test_apply_patterns_combined() {
        let cex = Counterexample::new(vec![("divisor".into(), CounterexampleValue::Uint(0))]);
        let proposals =
            apply_patterns("test::divide", "divide", &[("x", "u64"), ("divisor", "u64")], &[cex]);
        // Should get deduplicated suggestions
        assert!(!proposals.is_empty());
        // All proposals should reference the right function
        for p in &proposals {
            assert_eq!(p.function_path, "test::divide");
            assert_eq!(p.function_name, "divide");
        }
    }

    #[test]
    fn test_apply_patterns_empty_inputs() {
        let proposals = apply_patterns("test::f", "f", &[], &[]);
        assert!(proposals.is_empty());
    }

    #[test]
    fn test_apply_patterns_with_db_adjusts_confidence() {
        let mut db = PatternDatabase::new();
        for _ in 0..10 {
            db.record_outcome(&SpecPattern::NonZeroDivisor { variable: "d".into() }, true);
        }

        let proposals =
            apply_patterns_with_db("test::f", "f", &[("d", "u64"), ("divisor", "u64")], &[], &db);

        // With 100% historical success, confidence should be boosted
        for p in &proposals {
            assert!(
                p.confidence >= 0.5,
                "confidence {} should be at least 0.5 with good history",
                p.confidence
            );
        }
    }

    #[test]
    fn test_apply_patterns_deduplicates() {
        // Both signature and counterexample suggest non-zero for divisor
        let cex = Counterexample::new(vec![("divisor".into(), CounterexampleValue::Uint(0))]);
        let proposals = apply_patterns("test::f", "f", &[("divisor", "u64")], &[cex]);
        // Count how many NonZeroDivisor-related proposals we get
        let nonzero_count = proposals
            .iter()
            .filter(|p| matches!(p.kind, ProposalKind::AddNonZeroCheck { .. }))
            .count();
        // After dedup, should have at most 1
        assert!(nonzero_count <= 1, "should deduplicate non-zero suggestions, got {nonzero_count}");
    }

    // --- Utility functions ---

    #[test]
    fn test_is_index_name() {
        assert!(is_index_name("i"));
        assert!(is_index_name("idx"));
        assert!(is_index_name("index"));
        assert!(is_index_name("pos"));
        assert!(is_index_name("row_idx"));
        assert!(!is_index_name("name"));
        assert!(!is_index_name("value"));
    }

    #[test]
    fn test_is_divisor_name() {
        assert!(is_divisor_name("divisor"));
        assert!(is_divisor_name("denominator"));
        assert!(is_divisor_name("denom"));
        assert!(is_divisor_name("modulus"));
        assert!(!is_divisor_name("numerator"));
        assert!(!is_divisor_name("result"));
    }

    #[test]
    fn test_guess_collection_name_finds_slice() {
        let params = vec![("arr", "&[i32]"), ("idx", "usize")];
        assert_eq!(guess_collection_name(&params, "idx"), "arr");
    }

    #[test]
    fn test_guess_collection_name_fallback() {
        let params = vec![("x", "i32"), ("idx", "usize")];
        assert_eq!(guess_collection_name(&params, "idx"), "collection");
    }

    // --- PatternCategory ---

    #[test]
    fn test_pattern_category_labels() {
        assert_eq!(PatternCategory::BoundsCheck.label(), "bounds-check");
        assert_eq!(PatternCategory::NullSafety.label(), "null-safety");
        assert_eq!(PatternCategory::Overflow.label(), "overflow");
        assert_eq!(PatternCategory::Aliasing.label(), "aliasing");
        assert_eq!(PatternCategory::Termination.label(), "termination");
        assert_eq!(PatternCategory::Purity.label(), "purity");
    }

    // --- builtin_patterns ---

    #[test]
    fn test_builtin_patterns_non_empty() {
        let catalog = builtin_patterns();
        assert!(
            catalog.len() >= 10,
            "builtin catalog should have at least 10 patterns, got {}",
            catalog.len()
        );
    }

    #[test]
    fn test_builtin_patterns_has_all_categories() {
        let catalog = builtin_patterns();
        for cat in [
            PatternCategory::BoundsCheck,
            PatternCategory::NullSafety,
            PatternCategory::Overflow,
            PatternCategory::Aliasing,
            PatternCategory::Termination,
            PatternCategory::Purity,
        ] {
            assert!(
                !catalog.by_category(cat).is_empty(),
                "builtin catalog should have at least one pattern in category {:?}",
                cat
            );
        }
    }

    #[test]
    fn test_builtin_patterns_by_category_bounds_check() {
        let catalog = builtin_patterns();
        let bounds = catalog.by_category(PatternCategory::BoundsCheck);
        assert!(
            bounds.len() >= 2,
            "should have multiple bounds-check patterns, got {}",
            bounds.len()
        );
        let names: Vec<&str> = bounds.iter().map(|e| e.name.as_str()).collect();
        assert!(names.contains(&"index-in-bounds"), "missing index-in-bounds pattern");
        assert!(names.contains(&"non-empty-collection"), "missing non-empty-collection pattern");
    }

    // --- match_pattern ---

    #[test]
    fn test_match_pattern_usize_index_param() {
        let catalog = builtin_patterns();
        let matches = match_pattern(&catalog, "idx", "usize");
        assert!(!matches.is_empty(), "idx: usize should match at least one pattern");
        let has_index = matches.iter().any(|m| m.entry.name == "index-in-bounds");
        assert!(has_index, "idx: usize should match index-in-bounds pattern");
    }

    #[test]
    fn test_match_pattern_option_type() {
        let catalog = builtin_patterns();
        let matches = match_pattern(&catalog, "config", "Option<Config>");
        let has_some = matches.iter().any(|m| m.entry.name == "option-is-some");
        assert!(has_some, "Option param should match option-is-some pattern");
    }

    #[test]
    fn test_match_pattern_divisor_name() {
        let catalog = builtin_patterns();
        let matches = match_pattern(&catalog, "divisor", "u64");
        let has_nonzero = matches.iter().any(|m| m.entry.name == "non-zero-divisor");
        assert!(has_nonzero, "divisor: u64 should match non-zero-divisor pattern");
    }

    #[test]
    fn test_match_pattern_no_match_for_plain_string() {
        let catalog = builtin_patterns();
        let matches = match_pattern(&catalog, "name", "String");
        assert!(
            matches.is_empty(),
            "name: String should not match any pattern, got {}",
            matches.len()
        );
    }

    #[test]
    fn test_match_pattern_vec_param() {
        let catalog = builtin_patterns();
        let matches = match_pattern(&catalog, "items", "Vec<i32>");
        let has_non_empty = matches.iter().any(|m| m.entry.name == "non-empty-collection");
        assert!(has_non_empty, "Vec param should match non-empty-collection");
    }

    #[test]
    fn test_match_pattern_fuel_param_termination() {
        let catalog = builtin_patterns();
        let matches = match_pattern(&catalog, "fuel", "usize");
        let has_termination =
            matches.iter().any(|m| m.entry.category == PatternCategory::Termination);
        assert!(has_termination, "fuel: usize should match a termination pattern");
    }

    // --- instantiate_pattern ---

    #[test]
    fn test_instantiate_pattern_index() {
        let result = instantiate_pattern("{param} < {collection}.len()", "idx", "usize");
        assert_eq!(result, "idx < collection.len()");
    }

    #[test]
    fn test_instantiate_pattern_non_zero() {
        let result = instantiate_pattern("{param} != 0", "divisor", "u64");
        assert_eq!(result, "divisor != 0");
    }

    #[test]
    fn test_instantiate_pattern_overflow() {
        let result = instantiate_pattern("{param} <= {type}::MAX - {other}", "a", "u32");
        assert_eq!(result, "a <= u32::MAX - other");
    }

    #[test]
    fn test_instantiate_pattern_bit_width() {
        let result = instantiate_pattern("{param} < {bit_width}", "shift", "u32");
        assert_eq!(result, "shift < 32");
    }

    #[test]
    fn test_instantiate_pattern_bit_width_u8() {
        let result = instantiate_pattern("{param} < {bit_width}", "shift", "u8");
        assert_eq!(result, "shift < 8");
    }

    // --- CatalogMatch fields ---

    #[test]
    fn test_catalog_match_has_correct_instantiation() {
        let catalog = builtin_patterns();
        let matches = match_pattern(&catalog, "divisor", "u64");
        let nz = matches.iter().find(|m| m.entry.name == "non-zero-divisor");
        assert!(nz.is_some(), "should find non-zero-divisor match");
        let nz = nz.unwrap();
        assert_eq!(nz.instantiated, "divisor != 0");
        assert_eq!(nz.matched_param, "divisor");
        assert_eq!(nz.matched_type, "u64");
        assert!(nz.confidence > 0.0);
    }

    // --- PatternCatalog methods ---

    #[test]
    fn test_pattern_catalog_add_and_len() {
        let mut catalog = PatternCatalog::new();
        assert!(catalog.is_empty());
        assert_eq!(catalog.len(), 0);

        catalog.add(CatalogEntry {
            name: "test-pattern".into(),
            template: "{param} > 0".into(),
            category: PatternCategory::BoundsCheck,
            applicable_param_types: vec!["i32".into()],
            applicable_param_names: vec![],
            base_confidence: 0.5,
        });

        assert!(!catalog.is_empty());
        assert_eq!(catalog.len(), 1);
    }

    #[test]
    fn test_pattern_catalog_iter() {
        let catalog = builtin_patterns();
        let count = catalog.iter().count();
        assert_eq!(count, catalog.len());
    }
}
