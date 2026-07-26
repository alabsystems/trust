//! Structured diff generation from rewrite proposals.
//!
//! Produces human-readable diffs in unified, colored, and GitHub-flavored formats.
//! Supports applying, reversing, and merging diffs.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;
use std::fmt::Write;

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A single hunk in a unified diff.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffHunk {
    /// 1-based line number where this hunk starts in the original.
    pub old_start: usize,
    /// Number of lines in the original range.
    pub old_count: usize,
    /// 1-based line number where this hunk starts in the new version.
    pub new_start: usize,
    /// Number of lines in the new range.
    pub new_count: usize,
    /// Context lines before the change.
    pub context_before: Vec<String>,
    /// Lines removed from the original.
    pub removed: Vec<String>,
    /// Lines added in the new version.
    pub added: Vec<String>,
    /// Context lines after the change.
    pub context_after: Vec<String>,
}

impl DiffHunk {
    /// Whether this hunk represents an actual change (not just context).
    #[must_use]
    pub fn has_changes(&self) -> bool {
        !self.removed.is_empty() || !self.added.is_empty()
    }
}

/// A unified diff containing one or more hunks.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnifiedDiff {
    /// Original file path (for the `---` header).
    pub original_path: String,
    /// Modified file path (for the `+++` header).
    pub modified_path: String,
    /// The hunks that make up this diff.
    pub hunks: Vec<DiffHunk>,
}

impl UnifiedDiff {
    /// Whether this diff has any actual changes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.hunks.is_empty() || self.hunks.iter().all(|h| !h.has_changes())
    }

    /// Total number of lines removed across all hunks.
    #[must_use]
    pub fn total_removed(&self) -> usize {
        self.hunks.iter().map(|h| h.removed.len()).sum()
    }

    /// Total number of lines added across all hunks.
    #[must_use]
    pub fn total_added(&self) -> usize {
        self.hunks.iter().map(|h| h.added.len()).sum()
    }
}

impl fmt::Display for UnifiedDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", format_unified(self))
    }
}

// ---------------------------------------------------------------------------
// DiffGenerator
// ---------------------------------------------------------------------------

/// Generates structured diffs from original and rewritten source text.
#[derive(Debug, Clone)]
pub struct DiffGenerator {
    /// Number of context lines to include around each change.
    pub context_lines: usize,
}

impl Default for DiffGenerator {
    fn default() -> Self {
        Self { context_lines: 3 }
    }
}

impl DiffGenerator {
    /// Create a new diff generator with default settings (3 context lines).
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a diff generator with a custom context line count.
    #[must_use]
    pub fn with_context(context_lines: usize) -> Self {
        Self { context_lines }
    }

    /// Generate a unified diff between original and rewritten text.
    #[must_use]
    pub fn generate(&self, original: &str, rewritten: &str, path: &str) -> UnifiedDiff {
        generate_diff_inner(original, rewritten, path, self.context_lines)
    }
}

/// Generate a unified diff between original and rewritten text.
///
/// Uses a simple line-by-line LCS-based diff algorithm.
#[must_use]
pub fn generate_diff(original: &str, rewritten: &str, path: &str) -> UnifiedDiff {
    generate_diff_inner(original, rewritten, path, 3)
}

// ---------------------------------------------------------------------------
// Formatting
// ---------------------------------------------------------------------------

/// Format a diff as a standard unified diff string.
#[must_use]
pub fn format_unified(diff: &UnifiedDiff) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "--- {}", diff.original_path);
    let _ = writeln!(out, "+++ {}", diff.modified_path);

    for hunk in &diff.hunks {
        let _ = writeln!(
            out,
            "@@ -{},{} +{},{} @@",
            hunk.old_start, hunk.old_count, hunk.new_start, hunk.new_count,
        );
        for line in &hunk.context_before {
            let _ = writeln!(out, " {line}");
        }
        for line in &hunk.removed {
            let _ = writeln!(out, "-{line}");
        }
        for line in &hunk.added {
            let _ = writeln!(out, "+{line}");
        }
        for line in &hunk.context_after {
            let _ = writeln!(out, " {line}");
        }
    }
    out
}

/// Format a diff with ANSI terminal colors.
///
/// Red for removed lines, green for added, cyan for hunk headers.
#[must_use]
pub fn format_colored(diff: &UnifiedDiff) -> String {
    const RED: &str = "\x1b[31m";
    const GREEN: &str = "\x1b[32m";
    const CYAN: &str = "\x1b[36m";
    const RESET: &str = "\x1b[0m";

    let mut out = String::new();
    let _ = writeln!(out, "{RED}--- {}{RESET}", diff.original_path);
    let _ = writeln!(out, "{GREEN}+++ {}{RESET}", diff.modified_path);

    for hunk in &diff.hunks {
        let _ = writeln!(
            out,
            "{CYAN}@@ -{},{} +{},{} @@{RESET}",
            hunk.old_start, hunk.old_count, hunk.new_start, hunk.new_count,
        );
        for line in &hunk.context_before {
            let _ = writeln!(out, " {line}");
        }
        for line in &hunk.removed {
            let _ = writeln!(out, "{RED}-{line}{RESET}");
        }
        for line in &hunk.added {
            let _ = writeln!(out, "{GREEN}+{line}{RESET}");
        }
        for line in &hunk.context_after {
            let _ = writeln!(out, " {line}");
        }
    }
    out
}

/// Format a diff in GitHub-flavored Markdown (fenced code block with diff syntax).
#[must_use]
pub fn format_github(diff: &UnifiedDiff) -> String {
    let mut out = String::from("```diff\n");
    out.push_str(&format_unified(diff));
    out.push_str("```\n");
    out
}

// ---------------------------------------------------------------------------
// Apply / Reverse / Merge
// ---------------------------------------------------------------------------

/// Apply a unified diff to source text, producing the rewritten version.
///
/// # Errors
///
/// Returns `DiffApplyError` if context lines don't match or hunks are out of range.
pub fn apply_diff(source: &str, diff: &UnifiedDiff) -> Result<String, DiffApplyError> {
    let lines: Vec<&str> = source.lines().collect();
    let mut result: Vec<String> = Vec::with_capacity(lines.len());
    let mut src_idx: usize = 0;

    for (hunk_idx, hunk) in diff.hunks.iter().enumerate() {
        let hunk_start = hunk.old_start.saturating_sub(1); // Convert to 0-based.

        // Copy lines before this hunk.
        if hunk_start < src_idx {
            return Err(DiffApplyError::OverlappingHunks { hunk_index: hunk_idx });
        }
        while src_idx < hunk_start && src_idx < lines.len() {
            result.push(lines[src_idx].to_owned());
            src_idx += 1;
        }

        // Verify context_before matches.
        for (i, ctx_line) in hunk.context_before.iter().enumerate() {
            if src_idx + i >= lines.len() || lines[src_idx + i] != ctx_line.as_str() {
                return Err(DiffApplyError::ContextMismatch {
                    hunk_index: hunk_idx,
                    expected: ctx_line.clone(),
                    actual: lines.get(src_idx + i).unwrap_or(&"<EOF>").to_string(),
                });
            }
        }
        // Emit context_before.
        for line in &hunk.context_before {
            result.push(line.clone());
        }
        src_idx += hunk.context_before.len();

        // Verify removed lines match.
        for (i, rm_line) in hunk.removed.iter().enumerate() {
            if src_idx + i >= lines.len() || lines[src_idx + i] != rm_line.as_str() {
                return Err(DiffApplyError::RemovedLineMismatch {
                    hunk_index: hunk_idx,
                    expected: rm_line.clone(),
                    actual: lines.get(src_idx + i).unwrap_or(&"<EOF>").to_string(),
                });
            }
        }
        // Skip removed lines in source, emit added lines.
        src_idx += hunk.removed.len();
        for line in &hunk.added {
            result.push(line.clone());
        }

        // Verify and emit context_after.
        for (i, ctx_line) in hunk.context_after.iter().enumerate() {
            if src_idx + i >= lines.len() || lines[src_idx + i] != ctx_line.as_str() {
                return Err(DiffApplyError::ContextMismatch {
                    hunk_index: hunk_idx,
                    expected: ctx_line.clone(),
                    actual: lines.get(src_idx + i).unwrap_or(&"<EOF>").to_string(),
                });
            }
        }
        for line in &hunk.context_after {
            result.push(line.clone());
        }
        src_idx += hunk.context_after.len();
    }

    // Copy remaining lines.
    while src_idx < lines.len() {
        result.push(lines[src_idx].to_owned());
        src_idx += 1;
    }

    // Preserve trailing newline if the original had one.
    let mut text = result.join("\n");
    if source.ends_with('\n') && !text.ends_with('\n') {
        text.push('\n');
    }
    Ok(text)
}

/// Reverse a diff (swap added/removed, swap old/new metadata).
#[must_use]
pub fn reverse_diff(diff: &UnifiedDiff) -> UnifiedDiff {
    UnifiedDiff {
        original_path: diff.modified_path.clone(),
        modified_path: diff.original_path.clone(),
        hunks: diff
            .hunks
            .iter()
            .map(|h| DiffHunk {
                old_start: h.new_start,
                old_count: h.new_count,
                new_start: h.old_start,
                new_count: h.old_count,
                context_before: h.context_before.clone(),
                removed: h.added.clone(),
                added: h.removed.clone(),
                context_after: h.context_after.clone(),
            })
            .collect(),
    }
}

/// Merge multiple non-overlapping diffs into a single diff.
///
/// Diffs must target the same file. Hunks are sorted by `old_start` and
/// checked for overlap.
///
/// # Errors
///
/// Returns `DiffApplyError::OverlappingHunks` if any hunks overlap.
pub fn merge_diffs(diffs: &[UnifiedDiff]) -> Result<UnifiedDiff, DiffApplyError> {
    if diffs.is_empty() {
        return Ok(UnifiedDiff {
            original_path: String::new(),
            modified_path: String::new(),
            hunks: vec![],
        });
    }

    let original_path = diffs[0].original_path.clone();
    let modified_path = diffs[0].modified_path.clone();

    let mut all_hunks: Vec<DiffHunk> = diffs.iter().flat_map(|d| d.hunks.clone()).collect();
    all_hunks.sort_by_key(|h| h.old_start);

    // Check for overlaps.
    for window in all_hunks.windows(2) {
        let a_end = window[0].old_start + window[0].old_count;
        if a_end > window[1].old_start {
            return Err(DiffApplyError::OverlappingHunks { hunk_index: 0 });
        }
    }

    Ok(UnifiedDiff { original_path, modified_path, hunks: all_hunks })
}

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors that can occur when applying a diff.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum DiffApplyError {
    /// A context line did not match the source.
    #[error("context mismatch in hunk {hunk_index}: expected `{expected}`, got `{actual}`")]
    ContextMismatch { hunk_index: usize, expected: String, actual: String },
    /// A removed line did not match the source.
    #[error("removed line mismatch in hunk {hunk_index}: expected `{expected}`, got `{actual}`")]
    RemovedLineMismatch { hunk_index: usize, expected: String, actual: String },
    /// Hunks overlap and cannot be applied sequentially.
    #[error("overlapping hunks at index {hunk_index}")]
    OverlappingHunks { hunk_index: usize },
}

// ---------------------------------------------------------------------------
// Internal diff algorithm
// ---------------------------------------------------------------------------

/// Simple LCS-based line diff.
fn generate_diff_inner(original: &str, rewritten: &str, path: &str, context: usize) -> UnifiedDiff {
    let old_lines: Vec<&str> = original.lines().collect();
    let new_lines: Vec<&str> = rewritten.lines().collect();

    // Compute edit script via LCS.
    let edits = compute_edit_script(&old_lines, &new_lines);

    // Group edits into hunks with context.
    let hunks = group_into_hunks(&old_lines, &new_lines, &edits, context);

    UnifiedDiff { original_path: format!("a/{path}"), modified_path: format!("b/{path}"), hunks }
}

/// An edit operation in the diff.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EditOp {
    /// Line is the same in both.
    Equal,
    /// Line was removed from original.
    Remove,
    /// Line was added in new version.
    Add,
}

/// Compute an edit script using the LCS (longest common subsequence) algorithm.
fn compute_edit_script<'a>(old: &[&'a str], new: &[&'a str]) -> Vec<(EditOp, Option<&'a str>)> {
    let m = old.len();
    let n = new.len();

    // LCS table (O(mn) space — acceptable for source files).
    let mut dp = vec![vec![0u32; n + 1]; m + 1];
    for i in 1..=m {
        for j in 1..=n {
            if old[i - 1] == new[j - 1] {
                dp[i][j] = dp[i - 1][j - 1] + 1;
            } else {
                dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
            }
        }
    }

    // Backtrack to produce edit script.
    let mut edits = Vec::new();
    let mut i = m;
    let mut j = n;
    while i > 0 || j > 0 {
        if i > 0 && j > 0 && old[i - 1] == new[j - 1] {
            edits.push((EditOp::Equal, Some(old[i - 1])));
            i -= 1;
            j -= 1;
        } else if j > 0 && (i == 0 || dp[i][j - 1] >= dp[i - 1][j]) {
            edits.push((EditOp::Add, Some(new[j - 1])));
            j -= 1;
        } else {
            edits.push((EditOp::Remove, Some(old[i - 1])));
            i -= 1;
        }
    }
    edits.reverse();
    edits
}

/// Group edit operations into hunks with surrounding context.
fn group_into_hunks(
    old_lines: &[&str],
    _new_lines: &[&str],
    edits: &[(EditOp, Option<&str>)],
    context: usize,
) -> Vec<DiffHunk> {
    // Find change regions (runs of non-Equal edits).
    let mut change_starts = Vec::new();
    let mut in_change = false;
    for (idx, (op, _)) in edits.iter().enumerate() {
        match op {
            EditOp::Equal => {
                in_change = false;
            }
            _ => {
                if !in_change {
                    change_starts.push(idx);
                }
                in_change = true;
            }
        }
    }

    if change_starts.is_empty() {
        return vec![];
    }

    // Build hunks around each change region.
    let mut hunks = Vec::new();
    let _ = old_lines; // Used via edits

    for &start in &change_starts {
        // Find the end of this change region.
        let mut end = start;
        while end < edits.len() && edits[end].0 != EditOp::Equal {
            end += 1;
        }

        // Gather context_before.
        let ctx_before_start = start.saturating_sub(context);
        let context_before: Vec<String> = edits[ctx_before_start..start]
            .iter()
            .filter_map(
                |(op, line)| {
                    if *op == EditOp::Equal { line.map(|l| l.to_owned()) } else { None }
                },
            )
            .collect();

        // Gather removed and added.
        let mut removed = Vec::new();
        let mut added = Vec::new();
        for &(op, line) in &edits[start..end] {
            match op {
                EditOp::Remove => {
                    if let Some(l) = line {
                        removed.push(l.to_owned());
                    }
                }
                EditOp::Add => {
                    if let Some(l) = line {
                        added.push(l.to_owned());
                    }
                }
                EditOp::Equal => {}
            }
        }

        // Gather context_after.
        let ctx_after_end = (end + context).min(edits.len());
        let context_after: Vec<String> = edits[end..ctx_after_end]
            .iter()
            .filter_map(
                |(op, line)| {
                    if *op == EditOp::Equal { line.map(|l| l.to_owned()) } else { None }
                },
            )
            .collect();

        // Compute line numbers.
        let mut old_line = 1usize;
        let mut new_line = 1usize;
        for &(op, _) in &edits[..ctx_before_start] {
            match op {
                EditOp::Equal => {
                    old_line += 1;
                    new_line += 1;
                }
                EditOp::Remove => old_line += 1,
                EditOp::Add => new_line += 1,
            }
        }

        let old_start = old_line;
        let new_start = new_line;
        let old_count = context_before.len() + removed.len() + context_after.len();
        let new_count = context_before.len() + added.len() + context_after.len();

        hunks.push(DiffHunk {
            old_start,
            old_count,
            new_start,
            new_count,
            context_before,
            removed,
            added,
            context_after,
        });
    }

    hunks
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Diff generation tests --

    #[test]
    fn test_generate_diff_identical() {
        let text = "fn foo() {}\nfn bar() {}\n";
        let diff = generate_diff(text, text, "test.rs");
        assert!(diff.is_empty());
    }

    #[test]
    fn test_generate_diff_single_line_change() {
        let original = "line1\nline2\nline3\n";
        let rewritten = "line1\nmodified\nline3\n";
        let diff = generate_diff(original, rewritten, "test.rs");

        assert!(!diff.is_empty());
        assert_eq!(diff.hunks.len(), 1);
        assert_eq!(diff.hunks[0].removed, vec!["line2"]);
        assert_eq!(diff.hunks[0].added, vec!["modified"]);
    }

    #[test]
    fn test_generate_diff_addition() {
        let original = "line1\nline3\n";
        let rewritten = "line1\nline2\nline3\n";
        let diff = generate_diff(original, rewritten, "test.rs");

        assert!(!diff.is_empty());
        assert_eq!(diff.total_added(), 1);
        assert_eq!(diff.total_removed(), 0);
    }

    #[test]
    fn test_generate_diff_deletion() {
        let original = "line1\nline2\nline3\n";
        let rewritten = "line1\nline3\n";
        let diff = generate_diff(original, rewritten, "test.rs");

        assert!(!diff.is_empty());
        assert_eq!(diff.total_removed(), 1);
        assert_eq!(diff.total_added(), 0);
    }

    #[test]
    fn test_generate_diff_empty_to_content() {
        let diff = generate_diff("", "hello\nworld\n", "new.rs");
        assert!(!diff.is_empty());
        assert_eq!(diff.total_added(), 2);
    }

    #[test]
    fn test_generate_diff_content_to_empty() {
        let diff = generate_diff("hello\nworld\n", "", "old.rs");
        assert!(!diff.is_empty());
        assert_eq!(diff.total_removed(), 2);
    }

    // -- Formatting tests --

    #[test]
    fn test_format_unified_basic() {
        let diff = generate_diff("a\nb\nc\n", "a\nB\nc\n", "file.rs");
        let formatted = format_unified(&diff);

        assert!(formatted.contains("--- a/file.rs"));
        assert!(formatted.contains("+++ b/file.rs"));
        assert!(formatted.contains("@@"));
        assert!(formatted.contains("-b"));
        assert!(formatted.contains("+B"));
    }

    #[test]
    fn test_format_colored_has_ansi() {
        let diff = generate_diff("old\n", "new\n", "f.rs");
        let colored = format_colored(&diff);

        assert!(colored.contains("\x1b[31m")); // Red
        assert!(colored.contains("\x1b[32m")); // Green
        assert!(colored.contains("\x1b[36m")); // Cyan
        assert!(colored.contains("\x1b[0m")); // Reset
    }

    #[test]
    fn test_format_github_fenced() {
        let diff = generate_diff("x\n", "y\n", "g.rs");
        let github = format_github(&diff);

        assert!(github.starts_with("```diff\n"));
        assert!(github.ends_with("```\n"));
    }

    #[test]
    fn test_display_impl() {
        let diff = generate_diff("a\n", "b\n", "d.rs");
        let display = format!("{diff}");
        assert!(display.contains("---"));
        assert!(display.contains("+++"));
    }

    // -- Apply tests --

    #[test]
    fn test_apply_diff_roundtrip() {
        let original = "fn foo() {\n    let x = 1;\n    let y = 2;\n}\n";
        let rewritten = "fn foo() {\n    let x = 42;\n    let y = 2;\n}\n";

        let diff = generate_diff(original, rewritten, "test.rs");
        let applied = apply_diff(original, &diff).expect("apply should succeed");
        assert_eq!(applied, rewritten);
    }

    #[test]
    fn test_apply_diff_addition_roundtrip() {
        let original = "line1\nline3\n";
        let rewritten = "line1\nline2\nline3\n";

        let diff = generate_diff(original, rewritten, "test.rs");
        let applied = apply_diff(original, &diff).expect("apply should succeed");
        assert_eq!(applied, rewritten);
    }

    #[test]
    fn test_apply_diff_deletion_roundtrip() {
        let original = "line1\nline2\nline3\n";
        let rewritten = "line1\nline3\n";

        let diff = generate_diff(original, rewritten, "test.rs");
        let applied = apply_diff(original, &diff).expect("apply should succeed");
        assert_eq!(applied, rewritten);
    }

    #[test]
    fn test_apply_empty_diff() {
        let source = "unchanged\n";
        let diff = UnifiedDiff {
            original_path: "a/f.rs".into(),
            modified_path: "b/f.rs".into(),
            hunks: vec![],
        };
        let applied = apply_diff(source, &diff).expect("should succeed");
        assert_eq!(applied, source);
    }

    // -- Reverse tests --

    #[test]
    fn test_reverse_diff_basic() {
        let original = "a\nb\nc\n";
        let rewritten = "a\nB\nc\n";
        let diff = generate_diff(original, rewritten, "test.rs");
        let reversed = reverse_diff(&diff);

        assert_eq!(reversed.original_path, diff.modified_path);
        assert_eq!(reversed.modified_path, diff.original_path);
        assert_eq!(reversed.hunks.len(), diff.hunks.len());

        // Reversed diff's removed should be the forward diff's added.
        for (fwd, rev) in diff.hunks.iter().zip(reversed.hunks.iter()) {
            assert_eq!(fwd.removed, rev.added);
            assert_eq!(fwd.added, rev.removed);
        }
    }

    #[test]
    fn test_reverse_diff_apply_restores_original() {
        let original = "fn foo() {\n    1 + 2\n}\n";
        let rewritten = "fn foo() {\n    1.checked_add(2).unwrap()\n}\n";

        let diff = generate_diff(original, rewritten, "test.rs");
        let reversed = reverse_diff(&diff);
        let restored = apply_diff(rewritten, &reversed).expect("reverse apply");
        assert_eq!(restored, original);
    }

    // -- Merge tests --

    #[test]
    fn test_merge_diffs_non_overlapping() {
        let diff1 = UnifiedDiff {
            original_path: "a/f.rs".into(),
            modified_path: "b/f.rs".into(),
            hunks: vec![DiffHunk {
                old_start: 1,
                old_count: 1,
                new_start: 1,
                new_count: 1,
                context_before: vec![],
                removed: vec!["old1".into()],
                added: vec!["new1".into()],
                context_after: vec![],
            }],
        };
        let diff2 = UnifiedDiff {
            original_path: "a/f.rs".into(),
            modified_path: "b/f.rs".into(),
            hunks: vec![DiffHunk {
                old_start: 10,
                old_count: 1,
                new_start: 10,
                new_count: 1,
                context_before: vec![],
                removed: vec!["old10".into()],
                added: vec!["new10".into()],
                context_after: vec![],
            }],
        };

        let merged = merge_diffs(&[diff1, diff2]).expect("should merge");
        assert_eq!(merged.hunks.len(), 2);
        assert_eq!(merged.hunks[0].old_start, 1);
        assert_eq!(merged.hunks[1].old_start, 10);
    }

    #[test]
    fn test_merge_diffs_overlapping_fails() {
        let diff1 = UnifiedDiff {
            original_path: "a/f.rs".into(),
            modified_path: "b/f.rs".into(),
            hunks: vec![DiffHunk {
                old_start: 1,
                old_count: 5,
                new_start: 1,
                new_count: 5,
                context_before: vec![],
                removed: vec![],
                added: vec![],
                context_after: vec![],
            }],
        };
        let diff2 = UnifiedDiff {
            original_path: "a/f.rs".into(),
            modified_path: "b/f.rs".into(),
            hunks: vec![DiffHunk {
                old_start: 3,
                old_count: 2,
                new_start: 3,
                new_count: 2,
                context_before: vec![],
                removed: vec![],
                added: vec![],
                context_after: vec![],
            }],
        };

        let result = merge_diffs(&[diff1, diff2]);
        assert!(result.is_err());
    }

    #[test]
    fn test_merge_empty_diffs() {
        let merged = merge_diffs(&[]).expect("should merge empty");
        assert!(merged.hunks.is_empty());
    }

    // -- DiffGenerator custom context tests --

    #[test]
    fn test_diff_generator_custom_context() {
        let generator = DiffGenerator::with_context(0);
        let diff = generator.generate("a\nb\nc\n", "a\nB\nc\n", "test.rs");
        // With 0 context, hunks should have no context_before/after.
        for hunk in &diff.hunks {
            assert!(hunk.context_before.is_empty());
            assert!(hunk.context_after.is_empty());
        }
    }

    #[test]
    fn test_diff_hunk_has_changes() {
        let hunk_with_changes = DiffHunk {
            old_start: 1,
            old_count: 1,
            new_start: 1,
            new_count: 1,
            context_before: vec![],
            removed: vec!["old".into()],
            added: vec!["new".into()],
            context_after: vec![],
        };
        assert!(hunk_with_changes.has_changes());

        let hunk_no_changes = DiffHunk {
            old_start: 1,
            old_count: 1,
            new_start: 1,
            new_count: 1,
            context_before: vec!["ctx".into()],
            removed: vec![],
            added: vec![],
            context_after: vec![],
        };
        assert!(!hunk_no_changes.has_changes());
    }

    // -- Multi-hunk tests --

    #[test]
    fn test_generate_diff_multiple_changes() {
        // Changes at line 2 and line 5 (separated by enough context to be separate hunks).
        let original = "1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n";
        let rewritten = "1\nTWO\n3\n4\n5\n6\n7\n8\nNINE\n10\n";
        let generator = DiffGenerator::with_context(1);
        let diff = generator.generate(original, rewritten, "test.rs");

        assert!(diff.hunks.len() >= 2, "should have at least 2 hunks, got {}", diff.hunks.len());
    }

    #[test]
    fn test_apply_overlapping_hunks_error() {
        let diff = UnifiedDiff {
            original_path: "a/f.rs".into(),
            modified_path: "b/f.rs".into(),
            hunks: vec![
                DiffHunk {
                    old_start: 1,
                    old_count: 3,
                    new_start: 1,
                    new_count: 3,
                    context_before: vec![],
                    removed: vec!["a".into()],
                    added: vec!["b".into()],
                    context_after: vec![],
                },
                DiffHunk {
                    old_start: 1,
                    old_count: 2,
                    new_start: 1,
                    new_count: 2,
                    context_before: vec![],
                    removed: vec!["c".into()],
                    added: vec!["d".into()],
                    context_after: vec![],
                },
            ],
        };
        let result = apply_diff("a\nb\nc\n", &diff);
        assert!(result.is_err());
    }
}
