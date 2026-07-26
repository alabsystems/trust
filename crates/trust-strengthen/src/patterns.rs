// trust-strengthen/patterns.rs: Pattern library for spec inference without LLM
//
// Recognizes common Rust code patterns from function names and VC failure kinds,
// then proposes appropriate specs. This avoids LLM calls for well-understood
// patterns like binary search, sorting, bounded loops, etc.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::VcKind;

use crate::proposer::{Proposal, ProposalKind};

/// A recognized code pattern with associated spec knowledge.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CodePattern {
    /// Binary search over a sorted collection.
    BinarySearch,
    /// Sorting algorithm (any variant).
    Sort,
    /// Loop with a known bound (e.g., for i in 0..n).
    BoundedLoop,
    /// Iterator-based transformation.
    Iterator,
    /// Error handling / Result propagation.
    ErrorHandling,
    /// Vec::push or dynamic collection growth.
    VecPush,
    /// HashMap/BTreeMap lookup.
    HashLookup,
    /// Arithmetic operation (add, sub, mul, div).
    MathOp,
    /// String parsing / conversion.
    StringParse,
    /// File or network I/O.
    FileIO,
}

impl CodePattern {
    /// Human-readable description of this pattern.
    #[must_use]
    pub fn description(&self) -> &'static str {
        match self {
            Self::BinarySearch => "binary search over a sorted collection",
            Self::Sort => "sorting algorithm",
            Self::BoundedLoop => "loop with a known iteration bound",
            Self::Iterator => "iterator-based transformation",
            Self::ErrorHandling => "error handling / Result propagation",
            Self::VecPush => "dynamic collection growth (Vec::push)",
            Self::HashLookup => "hash map or tree map lookup",
            Self::MathOp => "arithmetic operation",
            Self::StringParse => "string parsing / conversion",
            Self::FileIO => "file or network I/O",
        }
    }
}

/// A match result from pattern recognition.
#[derive(Debug, Clone)]
pub struct PatternMatch {
    /// The recognized pattern.
    pub pattern: CodePattern,
    /// Confidence score in [0.0, 1.0].
    pub confidence: f64,
    /// Proposed preconditions for this pattern.
    pub preconditions: Vec<String>,
    /// Proposed postconditions for this pattern.
    pub postconditions: Vec<String>,
    /// Proposed loop invariants for this pattern.
    pub invariants: Vec<String>,
}

/// A library of recognizable patterns with their expected specs.
pub struct PatternLibrary {
    entries: Vec<PatternEntry>,
}

/// Internal: a pattern with its recognition criteria and specs.
struct PatternEntry {
    pattern: CodePattern,
    /// Substrings in function name that suggest this pattern.
    name_keywords: Vec<&'static str>,
    /// VC kinds that are typical for this pattern.
    typical_vc_kinds: Vec<VcKindClass>,
    /// Base confidence when name matches.
    name_confidence: f64,
    /// Confidence boost when VC kinds also match.
    vc_boost: f64,
    /// Spec templates for this pattern.
    preconditions: Vec<&'static str>,
    postconditions: Vec<&'static str>,
    invariants: Vec<&'static str>,
}

/// Broad classification of VcKind for pattern matching (avoids matching on inner data).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VcKindClass {
    ArithmeticOverflow,
    DivisionByZero,
    IndexOutOfBounds,
    CastOverflow,
    Assertion,
    Postcondition,
    Unreachable,
    NonTermination,
}

impl PatternLibrary {
    /// Build the default pattern library with all known patterns.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: vec![
                // Binary search pattern with formal spec text for
                // is_sorted precondition inference.
                PatternEntry {
                    pattern: CodePattern::BinarySearch,
                    name_keywords: vec![
                        "binary_search",
                        "bsearch",
                        "bisect",
                        "lower_bound",
                        "upper_bound",
                    ],
                    typical_vc_kinds: vec![
                        VcKindClass::ArithmeticOverflow,
                        VcKindClass::IndexOutOfBounds,
                    ],
                    name_confidence: 0.85,
                    vc_boost: 0.10,
                    preconditions: vec!["slice.is_sorted()", "!slice.is_empty()"],
                    postconditions: vec![
                        "result.is_some() ==> slice[result.unwrap()] == target",
                        "result.is_none() ==> forall i: usize, i < slice.len() ==> slice[i] != target",
                    ],
                    invariants: vec![
                        "0 <= low && low <= high + 1 && high < slice.len()",
                        "forall i: usize, i < low ==> slice[i] < target",
                        "forall i: usize, high < i && i < slice.len() ==> slice[i] > target",
                    ],
                },
                PatternEntry {
                    pattern: CodePattern::Sort,
                    name_keywords: vec![
                        "sort",
                        "quicksort",
                        "mergesort",
                        "heapsort",
                        "insertion_sort",
                        "bubble_sort",
                    ],
                    typical_vc_kinds: vec![
                        VcKindClass::IndexOutOfBounds,
                        VcKindClass::ArithmeticOverflow,
                    ],
                    name_confidence: 0.80,
                    vc_boost: 0.10,
                    preconditions: vec![],
                    postconditions: vec![
                        "result is a permutation of input",
                        "result is sorted: forall i < result.len()-1, result[i] <= result[i+1]",
                    ],
                    invariants: vec!["0 <= i && i <= slice.len()", "slice[..i] is sorted"],
                },
                PatternEntry {
                    pattern: CodePattern::BoundedLoop,
                    name_keywords: vec!["bounded", "count", "iterate", "scan", "walk", "traverse"],
                    typical_vc_kinds: vec![
                        VcKindClass::ArithmeticOverflow,
                        VcKindClass::IndexOutOfBounds,
                        VcKindClass::NonTermination,
                    ],
                    name_confidence: 0.60,
                    vc_boost: 0.15,
                    preconditions: vec!["n >= 0 (loop bound is non-negative)"],
                    postconditions: vec!["loop executed exactly n iterations"],
                    invariants: vec![
                        "0 <= i && i <= n",
                        "loop variant: n - i decreases each iteration",
                    ],
                },
                PatternEntry {
                    pattern: CodePattern::Iterator,
                    name_keywords: vec![
                        "iter",
                        "map",
                        "filter",
                        "fold",
                        "reduce",
                        "collect",
                        "enumerate",
                        "zip",
                    ],
                    typical_vc_kinds: vec![VcKindClass::ArithmeticOverflow],
                    name_confidence: 0.65,
                    vc_boost: 0.10,
                    preconditions: vec![],
                    postconditions: vec!["result.len() <= input.len()"],
                    invariants: vec![],
                },
                PatternEntry {
                    pattern: CodePattern::ErrorHandling,
                    name_keywords: vec![
                        "try_",
                        "parse",
                        "validate",
                        "check",
                        "handle_error",
                        "from_str",
                    ],
                    typical_vc_kinds: vec![
                        VcKindClass::Assertion,
                        VcKindClass::Postcondition,
                        VcKindClass::Unreachable,
                    ],
                    name_confidence: 0.60,
                    vc_boost: 0.15,
                    preconditions: vec![],
                    postconditions: vec![
                        "result.is_ok() ==> output satisfies validation",
                        "result.is_err() ==> input was malformed",
                    ],
                    invariants: vec![],
                },
                PatternEntry {
                    pattern: CodePattern::VecPush,
                    name_keywords: vec!["push", "append", "extend", "add_to", "vec_insert"],
                    typical_vc_kinds: vec![
                        VcKindClass::ArithmeticOverflow,
                        VcKindClass::IndexOutOfBounds,
                    ],
                    name_confidence: 0.60,
                    vc_boost: 0.10,
                    preconditions: vec!["vec.len() < usize::MAX"],
                    postconditions: vec![
                        "vec'.len() == vec.len() + 1",
                        "vec'.last() == Some(&item)",
                    ],
                    invariants: vec![],
                },
                PatternEntry {
                    pattern: CodePattern::HashLookup,
                    name_keywords: vec![
                        "lookup",
                        "get_entry",
                        "find_key",
                        "contains_key",
                        "hash_get",
                    ],
                    typical_vc_kinds: vec![VcKindClass::Assertion, VcKindClass::Postcondition],
                    name_confidence: 0.55,
                    vc_boost: 0.10,
                    preconditions: vec![],
                    postconditions: vec![
                        "result.is_some() ==> map.contains_key(&key)",
                        "result.is_none() ==> !map.contains_key(&key)",
                    ],
                    invariants: vec![],
                },
                PatternEntry {
                    pattern: CodePattern::MathOp,
                    name_keywords: vec![
                        "add",
                        "sub",
                        "mul",
                        "div",
                        "rem",
                        "pow",
                        "sqrt",
                        "abs",
                        "midpoint",
                        "average",
                        "mean",
                        "clamp",
                        "saturating",
                    ],
                    typical_vc_kinds: vec![
                        VcKindClass::ArithmeticOverflow,
                        VcKindClass::DivisionByZero,
                        VcKindClass::CastOverflow,
                    ],
                    name_confidence: 0.70,
                    vc_boost: 0.15,
                    preconditions: vec![
                        "operands do not overflow result type",
                        "divisor != 0 (if division involved)",
                    ],
                    postconditions: vec!["result is within bounds of result type"],
                    invariants: vec![],
                },
                PatternEntry {
                    pattern: CodePattern::StringParse,
                    name_keywords: vec![
                        "parse",
                        "from_str",
                        "to_string",
                        "format",
                        "encode",
                        "decode",
                        "serialize",
                        "deserialize",
                    ],
                    typical_vc_kinds: vec![
                        VcKindClass::Assertion,
                        VcKindClass::Postcondition,
                        VcKindClass::Unreachable,
                    ],
                    name_confidence: 0.60,
                    vc_boost: 0.10,
                    preconditions: vec!["input is valid UTF-8"],
                    postconditions: vec!["parse(format(x)) == x (roundtrip)"],
                    invariants: vec![],
                },
                PatternEntry {
                    pattern: CodePattern::FileIO,
                    name_keywords: vec![
                        "read_file",
                        "write_file",
                        "open_file",
                        "read_from",
                        "write_to",
                        "flush",
                        "close_file",
                        "connect",
                        "send_data",
                        "recv_data",
                    ],
                    typical_vc_kinds: vec![VcKindClass::Assertion, VcKindClass::Postcondition],
                    name_confidence: 0.55,
                    vc_boost: 0.10,
                    preconditions: vec!["file path exists and is readable (for read operations)"],
                    postconditions: vec!["result.is_ok() ==> operation completed successfully"],
                    invariants: vec![],
                },
            ],
        }
    }
}

impl Default for PatternLibrary {
    fn default() -> Self {
        Self::new()
    }
}

/// Classify a `VcKind` into a broad class for pattern matching.
fn classify_vc(kind: &VcKind) -> Option<VcKindClass> {
    match kind {
        VcKind::ArithmeticOverflow { .. } => Some(VcKindClass::ArithmeticOverflow),
        VcKind::DivisionByZero | VcKind::RemainderByZero => Some(VcKindClass::DivisionByZero),
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => Some(VcKindClass::IndexOutOfBounds),
        VcKind::CastOverflow { .. } => Some(VcKindClass::CastOverflow),
        VcKind::Assertion { .. } => Some(VcKindClass::Assertion),
        VcKind::Postcondition => Some(VcKindClass::Postcondition),
        VcKind::Unreachable => Some(VcKindClass::Unreachable),
        VcKind::NonTermination { .. } => Some(VcKindClass::NonTermination),
        _ => None,
    }
}

/// Recognize patterns from a function name and its failed VC kinds.
///
/// Returns a list of matched patterns sorted by confidence (highest first).
/// Each match includes proposed preconditions, postconditions, and invariants
/// tailored to the recognized pattern.
#[must_use]
pub fn recognize_patterns(func_name: &str, vc_kinds: &[VcKind]) -> Vec<PatternMatch> {
    let library = PatternLibrary::new();
    recognize_patterns_with_library(func_name, vc_kinds, &library)
}

/// Recognize patterns using a specific library instance (for reuse).
#[must_use]
pub(crate) fn recognize_patterns_with_library(
    func_name: &str,
    vc_kinds: &[VcKind],
    library: &PatternLibrary,
) -> Vec<PatternMatch> {
    let lower_name = func_name.to_lowercase();
    let vc_classes: Vec<VcKindClass> = vc_kinds.iter().filter_map(classify_vc).collect();

    let mut matches: Vec<PatternMatch> = library
        .entries
        .iter()
        .filter_map(|entry| {
            // Check if function name matches any keyword
            let name_hit = entry.name_keywords.iter().any(|kw| lower_name.contains(kw));

            if !name_hit {
                return None;
            }

            // Calculate confidence: base from name, boosted by VC match
            let mut confidence = entry.name_confidence;
            let vc_match =
                entry.typical_vc_kinds.iter().any(|expected| vc_classes.contains(expected));
            if vc_match {
                confidence = (confidence + entry.vc_boost).min(1.0);
            }

            Some(PatternMatch {
                pattern: entry.pattern.clone(),
                confidence,
                preconditions: entry.preconditions.iter().map(|s| (*s).to_string()).collect(),
                postconditions: entry.postconditions.iter().map(|s| (*s).to_string()).collect(),
                invariants: entry.invariants.iter().map(|s| (*s).to_string()).collect(),
            })
        })
        .collect();

    // Sort by confidence descending
    matches.sort_by(|a, b| {
        b.confidence.partial_cmp(&a.confidence).unwrap_or(std::cmp::Ordering::Equal)
    });
    matches
}

/// Convert pattern matches into spec proposals for the strengthen pipeline.
///
/// This bridges the pattern library with the existing `Proposal` type used by
/// the proposer and the rest of the strengthen pass.
#[must_use]
pub fn pattern_matches_to_proposals(
    function_path: &str,
    function_name: &str,
    matches: &[PatternMatch],
) -> Vec<Proposal> {
    let mut proposals = Vec::new();

    for m in matches {
        for pre in &m.preconditions {
            proposals.push(Proposal {
                function_path: function_path.into(),
                function_name: function_name.into(),
                kind: ProposalKind::AddPrecondition { spec_body: pre.clone() },
                confidence: m.confidence,
                rationale: format!("Pattern '{}': {}", m.pattern.description(), pre),
            });
        }

        for post in &m.postconditions {
            proposals.push(Proposal {
                function_path: function_path.into(),
                function_name: function_name.into(),
                kind: ProposalKind::AddPostcondition { spec_body: post.clone() },
                confidence: m.confidence * 0.9, // slightly lower for postconditions
                rationale: format!("Pattern '{}': {}", m.pattern.description(), post),
            });
        }

        for inv in &m.invariants {
            proposals.push(Proposal {
                function_path: function_path.into(),
                function_name: function_name.into(),
                kind: ProposalKind::AddInvariant { spec_body: inv.clone() },
                confidence: m.confidence * 0.85, // slightly lower for invariants
                rationale: format!("Pattern '{}': {}", m.pattern.description(), inv),
            });
        }
    }

    proposals
}

#[cfg(test)]
mod tests {
    use trust_types::{BinOp, Ty};

    use super::*;

    // --- CodePattern description ---

    #[test]
    fn test_code_pattern_descriptions_are_nonempty() {
        let patterns = vec![
            CodePattern::BinarySearch,
            CodePattern::Sort,
            CodePattern::BoundedLoop,
            CodePattern::Iterator,
            CodePattern::ErrorHandling,
            CodePattern::VecPush,
            CodePattern::HashLookup,
            CodePattern::MathOp,
            CodePattern::StringParse,
            CodePattern::FileIO,
        ];
        for p in &patterns {
            assert!(!p.description().is_empty(), "{p:?} should have a description");
        }
    }

    // --- Pattern recognition ---

    #[test]
    fn test_recognize_binary_search_by_name() {
        let matches = recognize_patterns("binary_search", &[]);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].pattern, CodePattern::BinarySearch);
        assert!(matches[0].confidence >= 0.80);
        assert!(!matches[0].preconditions.is_empty());
        assert!(!matches[0].postconditions.is_empty());
        assert!(!matches[0].invariants.is_empty());
    }

    #[test]
    fn test_recognize_binary_search_with_vc_boost() {
        let vc_kinds = vec![VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (
                Ty::Int { width: 64, signed: false },
                Ty::Int { width: 64, signed: false },
            ),
        }];
        let matches = recognize_patterns("binary_search", &vc_kinds);
        assert_eq!(matches.len(), 1);
        // Should get VC boost
        assert!(matches[0].confidence > 0.85);
    }

    #[test]
    fn test_recognize_sort_by_name() {
        let matches = recognize_patterns("quicksort", &[]);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].pattern, CodePattern::Sort);
        assert!(matches[0].postconditions.iter().any(|p| p.contains("sorted")));
        assert!(matches[0].postconditions.iter().any(|p| p.contains("permutation")));
    }

    #[test]
    fn test_recognize_insertion_sort() {
        let matches = recognize_patterns("insertion_sort", &[]);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].pattern, CodePattern::Sort);
    }

    #[test]
    fn test_recognize_midpoint_as_math_op() {
        let matches = recognize_patterns("get_midpoint", &[]);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].pattern, CodePattern::MathOp);
    }

    #[test]
    fn test_recognize_safe_divide_as_math_op() {
        let vc_kinds = vec![VcKind::DivisionByZero];
        let matches = recognize_patterns("safe_div", &vc_kinds);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].pattern, CodePattern::MathOp);
        // Should have VC boost
        assert!(matches[0].confidence > 0.70);
    }

    #[test]
    fn test_recognize_try_parse_as_error_handling() {
        let matches = recognize_patterns("try_parse_config", &[]);
        assert!(!matches.is_empty());
        let error_match = matches.iter().find(|m| m.pattern == CodePattern::ErrorHandling);
        assert!(error_match.is_some());
    }

    #[test]
    fn test_recognize_vec_push() {
        let matches = recognize_patterns("push_element", &[]);
        assert!(!matches.is_empty());
        let push_match = matches.iter().find(|m| m.pattern == CodePattern::VecPush);
        assert!(push_match.is_some());
        assert!(push_match.unwrap().postconditions.iter().any(|p| p.contains("len")));
    }

    #[test]
    fn test_recognize_hash_lookup() {
        let matches = recognize_patterns("lookup_user", &[]);
        assert!(!matches.is_empty());
        let lookup_match = matches.iter().find(|m| m.pattern == CodePattern::HashLookup);
        assert!(lookup_match.is_some());
    }

    #[test]
    fn test_recognize_hash_get_entry() {
        let matches = recognize_patterns("get_entry_by_id", &[]);
        assert!(!matches.is_empty());
        let lookup_match = matches.iter().find(|m| m.pattern == CodePattern::HashLookup);
        assert!(lookup_match.is_some());
    }

    #[test]
    fn test_recognize_iterator_pattern() {
        let matches = recognize_patterns("filter_active", &[]);
        assert!(!matches.is_empty());
        let iter_match = matches.iter().find(|m| m.pattern == CodePattern::Iterator);
        assert!(iter_match.is_some());
    }

    #[test]
    fn test_recognize_string_parse() {
        let matches = recognize_patterns("parse_json", &[]);
        assert!(!matches.is_empty());
        // May match both StringParse and ErrorHandling since "parse" is in both
        let parse_match = matches.iter().find(|m| m.pattern == CodePattern::StringParse);
        assert!(parse_match.is_some());
    }

    #[test]
    fn test_recognize_file_io() {
        let matches = recognize_patterns("read_file", &[]);
        assert!(!matches.is_empty());
        let io_match = matches.iter().find(|m| m.pattern == CodePattern::FileIO);
        assert!(io_match.is_some());
    }

    #[test]
    fn test_no_match_for_unknown_function() {
        let matches = recognize_patterns("frobulate_the_widget", &[]);
        assert!(matches.is_empty());
    }

    #[test]
    fn test_matches_sorted_by_confidence_descending() {
        // "parse" matches both ErrorHandling and StringParse
        let matches = recognize_patterns("parse", &[]);
        assert!(matches.len() >= 2);
        for window in matches.windows(2) {
            assert!(
                window[0].confidence >= window[1].confidence,
                "matches should be sorted by confidence descending"
            );
        }
    }

    #[test]
    fn test_multiple_vc_kinds_boost() {
        let vc_kinds = vec![
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            VcKind::IndexOutOfBounds,
        ];
        let matches = recognize_patterns("binary_search", &vc_kinds);
        assert_eq!(matches.len(), 1);
        assert!(matches[0].confidence > 0.85, "both VC kinds should trigger boost");
    }

    // --- PatternLibrary default ---

    #[test]
    fn test_pattern_library_default_has_entries() {
        let lib = PatternLibrary::default();
        assert!(lib.entries.len() >= 10, "should have at least 10 pattern entries");
    }

    // --- pattern_matches_to_proposals ---

    #[test]
    fn test_pattern_matches_to_proposals_binary_search() {
        let matches = recognize_patterns("binary_search", &[]);
        let proposals =
            pattern_matches_to_proposals("crate::binary_search", "binary_search", &matches);
        assert!(!proposals.is_empty());

        // Should have preconditions, postconditions, and invariants
        let has_pre =
            proposals.iter().any(|p| matches!(p.kind, ProposalKind::AddPrecondition { .. }));
        let has_post =
            proposals.iter().any(|p| matches!(p.kind, ProposalKind::AddPostcondition { .. }));
        let has_inv = proposals.iter().any(|p| matches!(p.kind, ProposalKind::AddInvariant { .. }));
        assert!(has_pre, "binary search should have precondition proposals");
        assert!(has_post, "binary search should have postcondition proposals");
        assert!(has_inv, "binary search should have invariant proposals");
    }

    #[test]
    fn test_pattern_matches_to_proposals_empty() {
        let proposals = pattern_matches_to_proposals("test::f", "f", &[]);
        assert!(proposals.is_empty());
    }

    #[test]
    fn test_pattern_matches_to_proposals_confidence_ordering() {
        let matches = recognize_patterns("binary_search", &[]);
        let proposals =
            pattern_matches_to_proposals("crate::binary_search", "binary_search", &matches);

        // Preconditions should have highest confidence, then postconditions, then invariants
        let pre_conf: Vec<f64> = proposals
            .iter()
            .filter(|p| matches!(p.kind, ProposalKind::AddPrecondition { .. }))
            .map(|p| p.confidence)
            .collect();
        let post_conf: Vec<f64> = proposals
            .iter()
            .filter(|p| matches!(p.kind, ProposalKind::AddPostcondition { .. }))
            .map(|p| p.confidence)
            .collect();
        let inv_conf: Vec<f64> = proposals
            .iter()
            .filter(|p| matches!(p.kind, ProposalKind::AddInvariant { .. }))
            .map(|p| p.confidence)
            .collect();

        if let (Some(&pre), Some(&post)) = (pre_conf.first(), post_conf.first()) {
            assert!(pre >= post, "precondition confidence should >= postcondition");
        }
        if let (Some(&post), Some(&inv)) = (post_conf.first(), inv_conf.first()) {
            assert!(post >= inv, "postcondition confidence should >= invariant");
        }
    }

    #[test]
    fn test_all_proposals_have_valid_confidence() {
        let test_names = vec![
            "binary_search",
            "quicksort",
            "count_items",
            "filter_active",
            "try_parse",
            "push_element",
            "lookup_user",
            "midpoint",
            "parse_json",
            "read_file",
        ];
        for name in test_names {
            let matches = recognize_patterns(name, &[]);
            let proposals = pattern_matches_to_proposals("test::f", name, &matches);
            for p in &proposals {
                assert!(
                    (0.0..=1.0).contains(&p.confidence),
                    "proposal for '{name}' has invalid confidence {}: {:?}",
                    p.confidence,
                    p.kind
                );
            }
        }
    }

    #[test]
    fn test_proposals_reference_correct_function() {
        let matches = recognize_patterns("binary_search", &[]);
        let proposals =
            pattern_matches_to_proposals("my_crate::binary_search", "binary_search", &matches);
        for p in &proposals {
            assert_eq!(p.function_path, "my_crate::binary_search");
            assert_eq!(p.function_name, "binary_search");
        }
    }

    // --- classify_vc ---

    #[test]
    fn test_classify_vc_arithmetic_overflow() {
        let kind = VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (
                Ty::Int { width: 64, signed: false },
                Ty::Int { width: 64, signed: false },
            ),
        };
        assert_eq!(classify_vc(&kind), Some(VcKindClass::ArithmeticOverflow));
    }

    #[test]
    fn test_classify_vc_division_by_zero() {
        assert_eq!(classify_vc(&VcKind::DivisionByZero), Some(VcKindClass::DivisionByZero));
        assert_eq!(classify_vc(&VcKind::RemainderByZero), Some(VcKindClass::DivisionByZero));
    }

    #[test]
    fn test_classify_vc_index_out_of_bounds() {
        assert_eq!(classify_vc(&VcKind::IndexOutOfBounds), Some(VcKindClass::IndexOutOfBounds));
        assert_eq!(classify_vc(&VcKind::SliceBoundsCheck), Some(VcKindClass::IndexOutOfBounds));
    }

    #[test]
    fn test_classify_vc_unknown_returns_none() {
        assert_eq!(classify_vc(&VcKind::Deadlock), None);
    }
}
