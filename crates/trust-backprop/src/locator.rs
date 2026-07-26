//! Function locator: finds function declarations in Rust source and computes byte offsets.
//!
//! Uses simple string matching (not a full parser) to find `fn name(` patterns,
//! handling common prefixes like `pub`, `pub(crate)`, `async`, `unsafe`, etc.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

/// Information about a located function in source text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionLocation {
    /// Byte offset of the start of the function item (including any `pub` prefix).
    pub item_offset: usize,
    /// Byte offset of the `fn` keyword itself.
    pub fn_offset: usize,
    /// The line number (1-based) where the function starts.
    pub line: usize,
    /// The indentation string (spaces/tabs) before the function.
    pub indent: String,
}

/// Find all occurrences of `fn <name>(` in source, returning their locations.
///
/// Handles common Rust function declaration patterns:
/// - `fn name(`
/// - `pub fn name(`
/// - `pub(crate) fn name(`
/// - `async fn name(`
/// - `pub async fn name(`
/// - `unsafe fn name(`
/// - `pub unsafe fn name(`
/// - `const fn name(`
/// - `pub const unsafe fn name(`
///
/// This is intentionally simple: it matches `fn <name>(` as a token sequence,
/// then walks backward to find the true item start (visibility, qualifiers).
#[must_use]
pub fn find_function(source: &str, name: &str) -> Vec<FunctionLocation> {
    let target = format!("fn {name}(");
    let mut results = Vec::new();

    for (fn_byte_offset, _) in source.match_indices(&target) {
        // Verify this is a token boundary: the char before `fn` must be whitespace
        // or start-of-file (not part of another identifier like `cfg_fn`)
        if fn_byte_offset > 0 {
            let prev = source.as_bytes()[fn_byte_offset - 1];
            if prev != b' ' && prev != b'\t' && prev != b'\n' && prev != b'\r' {
                continue;
            }
        }

        // Walk backward from `fn` to find the true item start (visibility + qualifiers).
        let item_offset = find_item_start(source, fn_byte_offset);

        // Compute line number and indentation.
        let line = source[..item_offset].matches('\n').count() + 1;
        let indent = extract_indent(source, item_offset);

        results.push(FunctionLocation { item_offset, fn_offset: fn_byte_offset, line, indent });
    }

    results
}

/// Find the first occurrence of `fn <name>(` in source.
#[must_use]
pub fn find_function_first(source: &str, name: &str) -> Option<FunctionLocation> {
    find_function(source, name).into_iter().next()
}

/// Walk backward from `fn` keyword to find the start of the item,
/// skipping qualifiers like `pub`, `pub(crate)`, `async`, `unsafe`, `const`, `extern`.
fn find_item_start(source: &str, fn_offset: usize) -> usize {
    // Start just before the `fn` keyword and work backward through qualifiers
    let mut pos = fn_offset;

    // Repeatedly try to strip known qualifiers (with whitespace) from before current pos
    loop {
        let before = pos;

        // Skip whitespace backward
        let trimmed_pos = source[..pos].trim_end().len();
        if trimmed_pos == 0 {
            pos = 0;
            break;
        }

        let current = &source[..trimmed_pos];

        // Try stripping known qualifiers from the end of current
        let mut matched = false;
        for qualifier in
            &["pub(super)", "pub(crate)", "pub(self)", "pub", "async", "unsafe", "const", "extern"]
        {
            if current.ends_with(qualifier) {
                let start = current.len() - qualifier.len();
                // Check it's a token boundary (not part of another word)
                if start == 0 || {
                    let c = source.as_bytes()[start - 1];
                    !c.is_ascii_alphanumeric() && c != b'_'
                } {
                    pos = start;
                    matched = true;
                    break;
                }
            }
        }

        if !matched {
            break;
        }
        if pos == before {
            break;
        }
    }

    // Now `pos` points to the start of qualifiers.
    // Find the start of the line containing pos.
    let line_start = source[..pos].rfind('\n').map_or(0, |i| i + 1);

    // If everything between line_start and pos is whitespace,
    // the item starts at line_start (preserving indentation context).
    let between = &source[line_start..pos];
    if between.chars().all(|c| c == ' ' || c == '\t') { line_start } else { pos }
}

/// Extract the indentation (leading whitespace) of the line containing `offset`.
fn extract_indent(source: &str, offset: usize) -> String {
    let line_start = source[..offset].rfind('\n').map_or(0, |i| i + 1);
    let line_rest = &source[line_start..];
    line_rest.chars().take_while(|c| *c == ' ' || *c == '\t').collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_simple_function() {
        let source = "fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n";
        let locs = find_function(source, "get_midpoint");
        assert_eq!(locs.len(), 1);
        assert_eq!(locs[0].item_offset, 0);
        assert_eq!(locs[0].fn_offset, 0);
        assert_eq!(locs[0].line, 1);
        assert_eq!(locs[0].indent, "");
    }

    #[test]
    fn test_find_pub_function() {
        let source = "pub fn calculate(x: i32) -> i32 {\n    x * 2\n}\n";
        let locs = find_function(source, "calculate");
        assert_eq!(locs.len(), 1);
        assert_eq!(locs[0].item_offset, 0);
        assert_eq!(locs[0].fn_offset, 4); // "pub " = 4 bytes
        assert_eq!(locs[0].line, 1);
    }

    #[test]
    fn test_find_pub_crate_function() {
        let source = "pub(crate) fn helper(n: usize) -> bool {\n    n > 0\n}\n";
        let locs = find_function(source, "helper");
        assert_eq!(locs.len(), 1);
        assert_eq!(locs[0].item_offset, 0);
        assert_eq!(locs[0].fn_offset, 11); // "pub(crate) " = 11 bytes
    }

    #[test]
    fn test_find_indented_function() {
        let source = "impl Foo {\n    pub fn bar(&self) -> u32 {\n        42\n    }\n}\n";
        let locs = find_function(source, "bar");
        assert_eq!(locs.len(), 1);
        assert_eq!(locs[0].line, 2);
        assert_eq!(locs[0].indent, "    ");
    }

    #[test]
    fn test_find_async_function() {
        let source = "pub async fn fetch(url: &str) -> String {\n    String::new()\n}\n";
        let locs = find_function(source, "fetch");
        assert_eq!(locs.len(), 1);
        assert_eq!(locs[0].item_offset, 0);
    }

    #[test]
    fn test_find_unsafe_function() {
        let source = "unsafe fn raw_ptr(p: *const u8) -> u8 {\n    *p\n}\n";
        let locs = find_function(source, "raw_ptr");
        assert_eq!(locs.len(), 1);
        assert_eq!(locs[0].item_offset, 0);
    }

    #[test]
    fn test_find_function_not_found() {
        let source = "fn foo() {}\n";
        let locs = find_function(source, "bar");
        assert!(locs.is_empty());
    }

    #[test]
    fn test_find_function_not_prefix_match() {
        // "cfg_fn" should not match "fn"
        let source = "fn cfg_fn_helper() {}\nfn helper() {}\n";
        let locs = find_function(source, "helper");
        assert_eq!(locs.len(), 1);
        assert_eq!(locs[0].line, 2);
    }

    #[test]
    fn test_find_multiple_functions_same_name() {
        let source = "mod a {\n    fn process() {}\n}\nmod b {\n    fn process() {}\n}\n";
        let locs = find_function(source, "process");
        assert_eq!(locs.len(), 2);
        assert_eq!(locs[0].line, 2);
        assert_eq!(locs[1].line, 5);
    }

    #[test]
    fn test_find_function_first_returns_first() {
        let source = "fn a() {}\nfn a() {}\n";
        let loc = find_function_first(source, "a");
        assert!(loc.is_some());
        assert_eq!(loc.unwrap().line, 1);
    }

    #[test]
    fn test_find_function_first_returns_none() {
        let source = "fn foo() {}\n";
        assert!(find_function_first(source, "bar").is_none());
    }

    #[test]
    fn test_find_function_with_comment_before() {
        let source = "/// Does a thing.\npub fn thing() {}\n";
        let locs = find_function(source, "thing");
        assert_eq!(locs.len(), 1);
        // item_offset points to `pub`, not the doc comment
        assert_eq!(&source[locs[0].item_offset..locs[0].item_offset + 3], "pub");
    }

    #[test]
    fn test_extract_indent_no_indent() {
        assert_eq!(extract_indent("fn foo() {}", 0), "");
    }

    #[test]
    fn test_extract_indent_with_spaces() {
        assert_eq!(extract_indent("    fn foo() {}", 4), "    ");
    }

    #[test]
    fn test_extract_indent_second_line() {
        assert_eq!(extract_indent("first\n    fn foo() {}", 10), "    ");
    }
}
