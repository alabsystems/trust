// trust-strengthen/source_reader.rs: Function-level source reading for context-aware proposals
//
// Given a file path and function name, extracts the function source body,
// parameter names and types, and return type. Used by the proposer to generate
// specs with real variable names instead of generic placeholders.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

/// Extracted context from a function's source code.
#[derive(Debug, Clone, PartialEq)]
pub struct SourceContext {
    /// The function name.
    pub function_name: String,
    /// Parameters: (name, type_string).
    pub params: Vec<(String, String)>,
    /// Return type, if any.
    pub return_type: Option<String>,
    /// The full function signature line.
    pub signature: String,
    /// The function body source (between outermost braces).
    pub body: String,
    /// The full function source (signature + body).
    pub full_source: String,
}

/// Read a source file and extract the function with the given name.
///
/// Returns `None` if the file cannot be read or the function is not found.
/// Used only in tests (proposer).
#[must_use]
pub fn read_function(path: impl AsRef<Path>, function_name: &str) -> Option<SourceContext> {
    let source = std::fs::read_to_string(path.as_ref()).ok()?;
    extract_function(&source, function_name)
}

/// Extract a function from source text by name (no file I/O).
///
/// Finds `fn <name>(` and extracts the full function including body.
/// Used only in tests (proposer).
#[must_use]
pub fn extract_function(source: &str, function_name: &str) -> Option<SourceContext> {
    // Find the function declaration: `fn function_name(` or `fn function_name<`
    let needle_paren = format!("fn {function_name}(");
    let needle_generic = format!("fn {function_name}<");
    let fn_start = source.find(&needle_paren).or_else(|| source.find(&needle_generic))?;

    // Walk backward to find any attributes or visibility modifiers on this line
    let decl_start = source[..fn_start].rfind('\n').map(|pos| pos + 1).unwrap_or(0);

    // Extract the signature: everything from fn_start to the opening brace
    let after_fn = &source[fn_start..];
    let open_brace = after_fn.find('{')?;
    let signature = after_fn[..open_brace].trim().to_string();

    // Extract parameters from the signature
    let params = extract_params(&signature);

    // Extract return type
    let return_type = extract_return_type(&signature);

    // Extract body: match braces to find the closing brace
    let body_start = fn_start + open_brace;
    let body_end = find_matching_brace(&source[body_start..])?;
    let full_end = body_start + body_end + 1; // include closing brace

    // The body is between the outermost braces (exclusive)
    let body = source[body_start + 1..body_start + body_end].trim().to_string();
    let full_source = source[decl_start..full_end].trim().to_string();

    Some(SourceContext {
        function_name: function_name.to_string(),
        params,
        return_type,
        signature,
        body,
        full_source,
    })
}

/// Extract parameter names and types from a function signature.
///
/// Handles `fn name(a: usize, b: usize) -> usize` and
/// `fn name(arr: &[i32], target: i32) -> Option<usize>`.
fn extract_params(signature: &str) -> Vec<(String, String)> {
    // Find the parameter list between the first `(` and its matching `)`
    let open = match signature.find('(') {
        Some(pos) => pos,
        None => return vec![],
    };
    let close = match find_matching_paren(&signature[open..]) {
        Some(pos) => open + pos,
        None => return vec![],
    };

    let params_str = &signature[open + 1..close];
    if params_str.trim().is_empty() {
        return vec![];
    }

    // Split by commas, respecting nested generics and closures
    split_params(params_str)
        .iter()
        .filter_map(|param| {
            let param = param.trim();
            if param.is_empty() || param == "self" || param == "&self" || param == "&mut self" {
                return None;
            }
            // Split at the first `:` to get name and type
            let colon = param.find(':')?;
            let name = param[..colon].trim().to_string();
            let ty = param[colon + 1..].trim().to_string();
            Some((name, ty))
        })
        .collect()
}

/// Extract the return type from a function signature, if present.
fn extract_return_type(signature: &str) -> Option<String> {
    // Find `) -> Type` pattern
    let close_paren = signature.rfind(')')?;
    let after_close = signature[close_paren + 1..].trim();
    after_close.strip_prefix("->").map(|rest| rest.trim().to_string())
}

/// Find the position of the matching closing brace for an opening brace at position 0.
fn find_matching_brace(s: &str) -> Option<usize> {
    let mut depth = 0;
    let mut in_string = false;
    let mut in_char = false;
    let mut escape_next = false;
    let mut in_line_comment = false;
    let mut in_block_comment = false;
    let chars: Vec<char> = s.chars().collect();

    for (i, &ch) in chars.iter().enumerate() {
        if escape_next {
            escape_next = false;
            continue;
        }

        if in_line_comment {
            if ch == '\n' {
                in_line_comment = false;
            }
            continue;
        }

        if in_block_comment {
            if ch == '*' && chars.get(i + 1) == Some(&'/') {
                in_block_comment = false;
            }
            continue;
        }

        if ch == '/' && !in_string && !in_char {
            if chars.get(i + 1) == Some(&'/') {
                in_line_comment = true;
                continue;
            }
            if chars.get(i + 1) == Some(&'*') {
                in_block_comment = true;
                continue;
            }
        }

        if ch == '\\' && (in_string || in_char) {
            escape_next = true;
            continue;
        }

        if ch == '"' && !in_char {
            in_string = !in_string;
            continue;
        }

        if ch == '\'' && !in_string {
            in_char = !in_char;
            continue;
        }

        if in_string || in_char {
            continue;
        }

        if ch == '{' {
            depth += 1;
        } else if ch == '}' {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
    }
    None
}

/// Find the position of the matching closing paren for an opening paren at position 0.
fn find_matching_paren(s: &str) -> Option<usize> {
    let mut depth = 0;
    for (i, ch) in s.chars().enumerate() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Split parameter string by commas, respecting nested `<>`, `()`, `[]`.
fn split_params(s: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut current = String::new();
    let mut depth = 0i32; // tracks <>, (), []

    for ch in s.chars() {
        match ch {
            '<' | '(' | '[' => {
                depth += 1;
                current.push(ch);
            }
            '>' | ')' | ']' => {
                depth -= 1;
                current.push(ch);
            }
            ',' if depth == 0 => {
                result.push(current.clone());
                current.clear();
            }
            _ => current.push(ch),
        }
    }
    if !current.trim().is_empty() {
        result.push(current);
    }
    result
}

/// Convenience: find parameter names that look like divisors.
///
/// Heuristic: a parameter used as the RHS of `/` or `%` in the body.
#[must_use]
pub(crate) fn find_divisor_params(ctx: &SourceContext) -> Vec<String> {
    ctx.params
        .iter()
        .filter(|(name, _)| {
            // Check if this parameter appears as a divisor in the body
            let div_pattern = format!("/ {name}");
            let rem_pattern = format!("% {name}");
            ctx.body.contains(&div_pattern) || ctx.body.contains(&rem_pattern)
        })
        .map(|(name, _)| name.clone())
        .collect()
}

/// Convenience: find parameter names used as a SHIFT AMOUNT.
///
/// Heuristic: a parameter appearing as the RHS of `<<` or `>>` in the body
/// (`x << k` / `x >> k`). Mirrors `find_divisor_params`; the safe precondition
/// is `<param> < <operand bit width>` (the width comes from the VC's
/// `operand_ty`, not the source).
#[must_use]
pub(crate) fn find_shift_params(ctx: &SourceContext) -> Vec<String> {
    ctx.params
        .iter()
        .filter(|(name, _)| {
            let shl_pattern = format!("<< {name}");
            let shr_pattern = format!(">> {name}");
            ctx.body.contains(&shl_pattern) || ctx.body.contains(&shr_pattern)
        })
        .map(|(name, _)| name.clone())
        .collect()
}

/// Convenience: find parameter names that look like array indices.
///
/// Heuristic: a parameter used inside `[param]` in the body.
#[must_use]
pub(crate) fn find_index_params(ctx: &SourceContext) -> Vec<(String, Option<String>)> {
    let mut results = Vec::new();

    for (name, _) in &ctx.params {
        // Check for `something[name]` pattern
        let bracket_pattern = format!("[{name}]");
        if ctx.body.contains(&bracket_pattern) {
            // Try to find the array being indexed: look for `array_name[name]`
            let array_name = find_array_for_index(&ctx.body, name);
            results.push((name.clone(), array_name));
        }
    }
    results
}

/// Find the array/slice variable being indexed by a given index variable.
fn find_array_for_index(body: &str, index_name: &str) -> Option<String> {
    let pattern = format!("[{index_name}]");
    let pos = body.find(&pattern)?;

    // Walk backward from `[` to find the identifier
    let before = &body[..pos];
    let ident_end = before.len();
    let ident_start =
        before.rfind(|c: char| !c.is_alphanumeric() && c != '_').map(|p| p + 1).unwrap_or(0);

    let ident = &before[ident_start..ident_end];
    if ident.is_empty() { None } else { Some(ident.to_string()) }
}

/// Find the source parameter that most plausibly drives a bulk allocation's
/// element count: the first integer-typed parameter (`usize`/`u*`/`i*`). Used to
/// synthesize a `requires param < CEILING` remedy for an UnboundedAllocation.
/// Returns `None` when the function has no integer parameter — i.e. the size is a
/// constant or otherwise not caller-controllable — in which case NO precondition
/// can soundly excuse the allocation and the obligation must stand (the guard
/// that keeps the auto-fix from erasing a ground L0 hard error).
pub(crate) fn find_size_param(ctx: &SourceContext) -> Option<String> {
    ctx.params.iter().find(|(_, ty)| is_integer_type(ty)).map(|(name, _)| name.clone())
}

fn is_integer_type(ty: &str) -> bool {
    let t = ty.trim().trim_start_matches('&').trim();
    matches!(
        t,
        "usize"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
    )
}

/// Find parameter pairs involved in arithmetic operations that could overflow.
///
/// Returns pairs of (left_operand, right_operand, operator).
#[must_use]
pub(crate) fn find_arithmetic_operands(ctx: &SourceContext) -> Vec<(String, String, char)> {
    let mut results = Vec::new();
    let param_names: Vec<&str> = ctx.params.iter().map(|(n, _)| n.as_str()).collect();

    for op in ['+', '-', '*'] {
        let op_str = format!(" {op} ");
        for occurrence in ctx.body.match_indices(&op_str) {
            let pos = occurrence.0;
            // Look for parameter names on either side
            let before = &ctx.body[..pos];
            let after = &ctx.body[pos + op_str.len()..];

            let left = extract_trailing_ident(before);
            let right = extract_leading_ident(after);

            if let (Some(l), Some(r)) = (left, right)
                && (param_names.contains(&l.as_str()) || param_names.contains(&r.as_str()))
            {
                results.push((l, r, op));
            }
        }
    }
    results
}

/// Extract the trailing identifier from a string.
fn extract_trailing_ident(s: &str) -> Option<String> {
    let trimmed = s.trim_end();
    let start =
        trimmed.rfind(|c: char| !c.is_alphanumeric() && c != '_').map(|p| p + 1).unwrap_or(0);
    let ident = &trimmed[start..];
    if ident.is_empty() { None } else { Some(ident.to_string()) }
}

/// Extract the leading identifier from a string.
fn extract_leading_ident(s: &str) -> Option<String> {
    let trimmed = s.trim_start();
    let end = trimmed.find(|c: char| !c.is_alphanumeric() && c != '_').unwrap_or(trimmed.len());
    let ident = &trimmed[..end];
    if ident.is_empty() { None } else { Some(ident.to_string()) }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MIDPOINT_SOURCE: &str = r#"fn get_midpoint(a: usize, b: usize) -> usize {
    (a + b) / 2
}"#;

    const BINARY_SEARCH_SOURCE: &str = r#"fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1;

    while low <= high {
        let mid = (low + high) / 2;

        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }

    None
}"#;

    const DIVIDE_SOURCE: &str = r#"fn safe_divide(x: u64, y: u64) -> u64 {
    x / y
}"#;

    const INDEXED_SOURCE: &str = r#"fn get_element(arr: &[i32], i: usize) -> i32 {
    arr[i]
}"#;

    // --- extract_function tests ---

    #[test]
    fn test_extract_midpoint_function() {
        let ctx =
            extract_function(MIDPOINT_SOURCE, "get_midpoint").expect("should extract get_midpoint");
        assert_eq!(ctx.function_name, "get_midpoint");
        assert_eq!(ctx.params.len(), 2);
        assert_eq!(ctx.params[0], ("a".to_string(), "usize".to_string()));
        assert_eq!(ctx.params[1], ("b".to_string(), "usize".to_string()));
        assert_eq!(ctx.return_type, Some("usize".to_string()));
        assert!(ctx.body.contains("(a + b) / 2"));
    }

    #[test]
    fn test_extract_binary_search_function() {
        let ctx = extract_function(BINARY_SEARCH_SOURCE, "binary_search")
            .expect("should extract binary_search");
        assert_eq!(ctx.function_name, "binary_search");
        assert_eq!(ctx.params.len(), 2);
        assert_eq!(ctx.params[0], ("arr".to_string(), "&[i32]".to_string()));
        assert_eq!(ctx.params[1], ("target".to_string(), "i32".to_string()));
        assert_eq!(ctx.return_type, Some("Option<usize>".to_string()));
        assert!(ctx.body.contains("while low <= high"));
    }

    #[test]
    fn test_extract_divide_function() {
        let ctx =
            extract_function(DIVIDE_SOURCE, "safe_divide").expect("should extract safe_divide");
        assert_eq!(ctx.params.len(), 2);
        assert_eq!(ctx.params[0], ("x".to_string(), "u64".to_string()));
        assert_eq!(ctx.params[1], ("y".to_string(), "u64".to_string()));
        assert_eq!(ctx.return_type, Some("u64".to_string()));
    }

    #[test]
    fn test_extract_indexed_function() {
        let ctx =
            extract_function(INDEXED_SOURCE, "get_element").expect("should extract get_element");
        assert_eq!(ctx.params.len(), 2);
        assert_eq!(ctx.params[0], ("arr".to_string(), "&[i32]".to_string()));
        assert_eq!(ctx.params[1], ("i".to_string(), "usize".to_string()));
    }

    #[test]
    fn test_extract_nonexistent_function_returns_none() {
        assert!(extract_function(MIDPOINT_SOURCE, "nonexistent").is_none());
    }

    #[test]
    fn test_extract_empty_source_returns_none() {
        assert!(extract_function("", "foo").is_none());
    }

    // --- find_divisor_params tests ---

    #[test]
    fn test_find_divisor_params_safe_divide() {
        let ctx = extract_function(DIVIDE_SOURCE, "safe_divide").unwrap();
        let divisors = find_divisor_params(&ctx);
        assert_eq!(divisors, vec!["y".to_string()]);
    }

    #[test]
    fn test_find_divisor_params_midpoint_no_param_divisor() {
        let ctx = extract_function(MIDPOINT_SOURCE, "get_midpoint").unwrap();
        let divisors = find_divisor_params(&ctx);
        // Divides by 2 (literal), not a parameter
        assert!(divisors.is_empty());
    }

    // --- find_index_params tests ---

    #[test]
    fn test_find_index_params_get_element() {
        let ctx = extract_function(INDEXED_SOURCE, "get_element").unwrap();
        let indices = find_index_params(&ctx);
        assert_eq!(indices.len(), 1);
        assert_eq!(indices[0].0, "i");
        assert_eq!(indices[0].1, Some("arr".to_string()));
    }

    // --- find_arithmetic_operands tests ---

    #[test]
    fn test_find_arithmetic_operands_midpoint() {
        let ctx = extract_function(MIDPOINT_SOURCE, "get_midpoint").unwrap();
        let ops = find_arithmetic_operands(&ctx);
        assert!(!ops.is_empty());
        // Should find a + b
        let add_op = ops.iter().find(|(_, _, op)| *op == '+');
        assert!(add_op.is_some(), "should find addition of a + b");
        let (l, r, _) = add_op.unwrap();
        assert_eq!(l, "a");
        assert_eq!(r, "b");
    }

    // --- read_function (file I/O) tests ---

    #[test]
    fn test_read_function_from_midpoint_example() {
        // This test reads the actual examples/midpoint.rs file
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/midpoint.rs");
        if !Path::new(path).exists() {
            // Skip gracefully if examples dir not accessible from test runner
            return;
        }
        let ctx =
            read_function(path, "get_midpoint").expect("should read get_midpoint from midpoint.rs");
        assert_eq!(ctx.function_name, "get_midpoint");
        assert_eq!(ctx.params.len(), 2);
        assert_eq!(ctx.params[0].0, "a");
        assert_eq!(ctx.params[1].0, "b");
    }

    #[test]
    fn test_read_function_from_binary_search_example() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/binary_search.rs");
        if !Path::new(path).exists() {
            return;
        }
        let ctx = read_function(path, "binary_search")
            .expect("should read binary_search from binary_search.rs");
        assert_eq!(ctx.function_name, "binary_search");
        assert_eq!(ctx.params.len(), 2);
        assert_eq!(ctx.params[0].0, "arr");
        assert_eq!(ctx.params[1].0, "target");
        assert_eq!(ctx.return_type, Some("Option<usize>".to_string()));
    }

    #[test]
    fn test_read_function_nonexistent_file() {
        assert!(read_function("/nonexistent/path.rs", "foo").is_none());
    }

    // --- Edge cases ---

    #[test]
    fn test_extract_function_with_generics() {
        let source = r#"fn find<T: PartialEq>(items: &[T], needle: &T) -> Option<usize> {
    items.iter().position(|x| x == needle)
}"#;
        let ctx = extract_function(source, "find").expect("should extract generic function");
        assert_eq!(ctx.params.len(), 2);
        assert_eq!(ctx.params[0].0, "items");
        assert_eq!(ctx.params[1].0, "needle");
    }

    #[test]
    fn test_extract_function_no_params() {
        let source = "fn hello() -> &'static str {\n    \"hello\"\n}";
        let ctx = extract_function(source, "hello").expect("should extract no-param function");
        assert!(ctx.params.is_empty());
        assert_eq!(ctx.return_type, Some("&'static str".to_string()));
    }

    #[test]
    fn test_extract_function_with_comments_in_body() {
        let source = r#"fn tricky(x: i32) -> i32 {
    // This has braces in comments: { }
    let y = x + 1; // and more: }
    y
}"#;
        let ctx = extract_function(source, "tricky").expect("should handle comments");
        assert!(ctx.body.contains("let y = x + 1"));
    }

    #[test]
    fn test_extract_function_with_string_braces() {
        let source = r#"fn stringy(x: i32) -> String {
    format!("braces: {{ {} }}", x)
}"#;
        let ctx = extract_function(source, "stringy").expect("should handle string braces");
        assert!(ctx.body.contains("format!"));
    }

    #[test]
    fn test_extract_function_multiple_functions() {
        let source = r#"fn first(a: i32) -> i32 {
    a + 1
}

fn second(b: i32) -> i32 {
    b * 2
}"#;
        let ctx1 = extract_function(source, "first").expect("should find first");
        assert_eq!(ctx1.params[0].0, "a");

        let ctx2 = extract_function(source, "second").expect("should find second");
        assert_eq!(ctx2.params[0].0, "b");
    }

    // --- split_params edge cases ---

    #[test]
    fn test_extract_params_with_nested_generics() {
        let source =
            "fn complex(map: HashMap<String, Vec<u8>>, count: usize) -> bool {\n    true\n}";
        let ctx = extract_function(source, "complex").expect("should parse complex params");
        assert_eq!(ctx.params.len(), 2);
        assert_eq!(ctx.params[0].0, "map");
        assert_eq!(ctx.params[0].1, "HashMap<String, Vec<u8>>");
        assert_eq!(ctx.params[1].0, "count");
        assert_eq!(ctx.params[1].1, "usize");
    }
}
