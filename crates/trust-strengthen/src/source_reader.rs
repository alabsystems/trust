// trust-strengthen/source_reader.rs: Function-level source reading for context-aware proposals
//
// Given a file path and function name, extracts the function source body,
// parameter names and types, and return type. Used by the proposer to generate
// specs with real variable names instead of generic placeholders.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

use trust_types::fx::FxHashSet;

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
/// Used by [`crate::run`] when a function's path names a source file.
#[must_use]
pub fn read_function(path: impl AsRef<Path>, function_name: &str) -> Option<SourceContext> {
    let source = std::fs::read_to_string(path.as_ref()).ok()?;
    extract_function(&source, function_name)
}

/// Extract a function from source text by name (no file I/O).
///
/// Finds `fn <name>(` and extracts the full function including body.
#[must_use]
pub fn extract_function(source: &str, function_name: &str) -> Option<SourceContext> {
    // Find the function declaration: `fn function_name(` or `fn function_name<` without format! allocations.
    let fn_start = find_delimited(source, "fn ", function_name, b'(')
        .or_else(|| find_delimited(source, "fn ", function_name, b'<'))?;

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
    let mut iter = s.char_indices().peekable();

    while let Some((i, ch)) = iter.next() {
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
            if ch == '*' && iter.peek().is_some_and(|&(_, next)| next == '/') {
                in_block_comment = false;
            }
            continue;
        }

        if ch == '/' && !in_string && !in_char {
            if iter.peek().is_some_and(|&(_, next)| next == '/') {
                in_line_comment = true;
                continue;
            }
            if iter.peek().is_some_and(|&(_, next)| next == '*') {
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
    for (i, ch) in s.char_indices() {
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
fn split_params(s: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let mut start = 0;
    let mut depth = 0i32; // tracks <>, (), []

    for (i, ch) in s.char_indices() {
        match ch {
            '<' | '(' | '[' => depth += 1,
            '>' | ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                result.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    let tail = &s[start..];
    if !tail.trim().is_empty() {
        result.push(tail);
    }
    result
}

/// Zero-allocation search for `{prefix}{mid}{suffix}` in `haystack`, where `prefix` starts
/// with an ASCII byte and `suffix` is a single ASCII byte.
fn find_delimited(haystack: &str, prefix: &str, mid: &str, suffix: u8) -> Option<usize> {
    let total_len = prefix.len() + mid.len() + 1;
    if haystack.len() < total_len {
        return None;
    }
    let bytes = haystack.as_bytes();
    let mid_bytes = mid.as_bytes();
    let mut offset = 0;
    while let Some(rel) = haystack[offset..].find(prefix) {
        let pos = offset + rel;
        let after_prefix = pos + prefix.len();
        if bytes.len() >= after_prefix + mid_bytes.len() + 1
            && bytes[after_prefix..].starts_with(mid_bytes)
            && bytes[after_prefix + mid_bytes.len()] == suffix
        {
            return Some(pos);
        }
        offset = pos + 1;
    }
    None
}

/// Zero-allocation check for `{prefix}{name}` in `body`, where `prefix` starts with ASCII.
fn body_contains_prefixed(body: &str, prefix: &str, name: &str) -> bool {
    let need = prefix.len() + name.len();
    if body.len() < need {
        return false;
    }
    let bytes = body.as_bytes();
    let name_bytes = name.as_bytes();
    let mut offset = 0;
    while let Some(rel) = body[offset..].find(prefix) {
        let pos = offset + rel;
        let after = pos + prefix.len();
        if bytes[after..].starts_with(name_bytes) {
            return true;
        }
        offset = pos + 1;
    }
    false
}

#[inline]
fn is_divisor_in_body(body: &str, name: &str) -> bool {
    body_contains_prefixed(body, "/ ", name) || body_contains_prefixed(body, "% ", name)
}

#[inline]
fn is_shift_in_body(body: &str, name: &str) -> bool {
    body_contains_prefixed(body, "<< ", name) || body_contains_prefixed(body, ">> ", name)
}

/// Convenience: find the first parameter name that looks like a divisor.
#[must_use]
pub(crate) fn find_first_divisor_param(ctx: &SourceContext) -> Option<&str> {
    ctx.params
        .iter()
        .find(|(name, _)| is_divisor_in_body(&ctx.body, name))
        .map(|(name, _)| name.as_str())
}

/// Convenience: find parameter names that look like divisors.
///
/// Heuristic: a parameter used as the RHS of `/` or `%` in the body.
#[cfg_attr(not(test), allow(dead_code))]
#[must_use]
pub(crate) fn find_divisor_params(ctx: &SourceContext) -> Vec<String> {
    ctx.params
        .iter()
        .filter(|(name, _)| is_divisor_in_body(&ctx.body, name))
        .map(|(name, _)| name.clone())
        .collect()
}

/// Convenience: find the first parameter name used as a SHIFT AMOUNT.
#[must_use]
pub(crate) fn find_first_shift_param(ctx: &SourceContext) -> Option<&str> {
    ctx.params
        .iter()
        .find(|(name, _)| is_shift_in_body(&ctx.body, name))
        .map(|(name, _)| name.as_str())
}

/// Convenience: find parameter names used as a SHIFT AMOUNT.
///
/// Heuristic: a parameter appearing as the RHS of `<<` or `>>` in the body
/// (`x << k` / `x >> k`). Mirrors `find_divisor_params`; the safe precondition
/// is `<param> < <operand bit width>` (the width comes from the VC's
/// `operand_ty`, not the source).
#[cfg_attr(not(test), allow(dead_code))]
#[must_use]
pub(crate) fn find_shift_params(ctx: &SourceContext) -> Vec<String> {
    ctx.params
        .iter()
        .filter(|(name, _)| is_shift_in_body(&ctx.body, name))
        .map(|(name, _)| name.clone())
        .collect()
}

/// Convenience: find the first parameter name that looks like an array index.
#[must_use]
pub(crate) fn find_first_index_param(ctx: &SourceContext) -> Option<(&str, Option<&str>)> {
    for (name, _) in &ctx.params {
        if let Some(pos) = find_delimited(&ctx.body, "[", name, b']') {
            let array_name = array_before_bracket(&ctx.body, pos);
            return Some((name.as_str(), array_name));
        }
    }
    None
}

/// Convenience: find parameter names that look like array indices.
///
/// Heuristic: a parameter used inside `[param]` in the body.
#[must_use]
pub(crate) fn find_index_params(ctx: &SourceContext) -> Vec<(String, Option<String>)> {
    let mut results = Vec::new();

    for (name, _) in &ctx.params {
        // Check for `something[name]` pattern in one pass without format! allocation.
        if let Some(pos) = find_delimited(&ctx.body, "[", name, b']') {
            let array_name = array_before_bracket(&ctx.body, pos).map(str::to_string);
            results.push((name.clone(), array_name));
        }
    }
    results
}

/// Extract the identifier immediately preceding `[` at byte position `pos` in `body`.
fn array_before_bracket(body: &str, pos: usize) -> Option<&str> {
    let before = &body[..pos];
    let ident_end = before.len();
    let ident_start =
        before.rfind(|c: char| !c.is_alphanumeric() && c != '_').map(|p| p + 1).unwrap_or(0);

    let ident = &before[ident_start..ident_end];
    if ident.is_empty() { None } else { Some(ident) }
}

/// Find the source parameter that most plausibly drives a bulk allocation's
/// element count: the first integer-typed parameter (`usize`/`u*`/`i*`). Used to
/// synthesize a `requires param < CEILING` remedy for an UnboundedAllocation.
/// Returns `None` when the function has no integer parameter — i.e. the size is a
/// constant or otherwise not caller-controllable — in which case NO precondition
/// can soundly excuse the allocation and the obligation must stand (the guard
/// that keeps the auto-fix from erasing a ground L0 hard error).
pub(crate) fn find_size_param(ctx: &SourceContext) -> Option<&str> {
    ctx.params.iter().find(|(_, ty)| is_integer_type(ty)).map(|(name, _)| name.as_str())
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

/// An operand pair recovered from a binary arithmetic expression in the body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArithmeticOperands {
    /// Left operand: a bare variable name bound in the function.
    pub left: String,
    /// Right operand: a bare variable name bound in the function.
    pub right: String,
    /// The operator (`+`, `-` or `*`).
    pub op: char,
    /// Whether BOTH operands are function parameters. Only then may a
    /// `requires` clause name them; a body local is out of scope in a
    /// precondition.
    pub both_params: bool,
}

/// Find the first variable pair involved in `op` (`+`, `-`, or `*`) in the body.
#[must_use]
pub(crate) fn find_first_arithmetic_operand_pair(
    ctx: &SourceContext,
    op: char,
) -> Option<ArithmeticOperands> {
    let op_str = match op {
        '+' => " + ",
        '-' => " - ",
        '*' => " * ",
        _ => return None,
    };
    let mut locals: Option<FxHashSet<&str>> = None;
    let has_param = |name: &str| ctx.params.iter().any(|(n, _)| n == name);

    for (pos, _) in ctx.body.match_indices(op_str) {
        let before = &ctx.body[..pos];
        let after = &ctx.body[pos + op_str.len()..];

        let (Some(l), Some(r)) = (bare_trailing_ident(before), bare_leading_ident(after)) else {
            continue;
        };
        let l_param = has_param(l);
        if !l_param && !locals.get_or_insert_with(|| find_let_bindings(&ctx.body)).contains(l) {
            continue;
        }
        let r_param = has_param(r);
        if !r_param && !locals.get_or_insert_with(|| find_let_bindings(&ctx.body)).contains(r) {
            continue;
        }
        return Some(ArithmeticOperands {
            left: l.to_string(),
            right: r.to_string(),
            op,
            both_params: l_param && r_param,
        });
    }
    None
}

/// Find variable pairs involved in arithmetic operations that could overflow.
///
/// An operand is accepted only when it is a bare identifier (not a field
/// access, method receiver, call, or index) that the function
/// actually binds: a parameter or a `let` binding in the body. Nothing is ever
/// synthesized, so every returned name occurs in the function's source.
#[must_use]
pub(crate) fn find_arithmetic_operand_pairs(ctx: &SourceContext) -> Vec<ArithmeticOperands> {
    let mut results = Vec::new();
    let param_set: FxHashSet<&str> = ctx.params.iter().map(|(n, _)| n.as_str()).collect();
    let locals = find_let_bindings(&ctx.body);

    for (op, op_str) in [('+', " + "), ('-', " - "), ('*', " * ")] {
        for (pos, _) in ctx.body.match_indices(op_str) {
            let before = &ctx.body[..pos];
            let after = &ctx.body[pos + op_str.len()..];

            let (Some(l), Some(r)) = (bare_trailing_ident(before), bare_leading_ident(after))
            else {
                continue;
            };
            let l_param = param_set.contains(l);
            if !l_param && !locals.contains(l) {
                continue;
            }
            let r_param = param_set.contains(r);
            if !r_param && !locals.contains(r) {
                continue;
            }
            results.push(ArithmeticOperands {
                left: l.to_string(),
                right: r.to_string(),
                op,
                both_params: l_param && r_param,
            });
        }
    }
    results
}

/// Names bound by `let` / `let mut` in a function body (simple identifier
/// patterns only; destructuring patterns are not recovered).
fn find_let_bindings(body: &str) -> FxHashSet<&str> {
    let mut names = FxHashSet::default();
    for (pos, _) in body.match_indices("let ") {
        if body[..pos].chars().next_back().is_some_and(is_ident_char) {
            continue;
        }
        let rest = body[pos + "let ".len()..].trim_start();
        let rest = rest.strip_prefix("mut ").map_or(rest, str::trim_start);
        if let Some(name) = extract_leading_ident(rest)
            && is_variable_name(name)
        {
            names.insert(name);
        }
    }
    names
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// A plausible variable name: starts with a letter or `_`, is not a keyword.
fn is_variable_name(name: &str) -> bool {
    name.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')
        && name != "_"
        && !matches!(
            name,
            "as" | "break"
                | "const"
                | "continue"
                | "crate"
                | "else"
                | "false"
                | "fn"
                | "for"
                | "if"
                | "impl"
                | "in"
                | "let"
                | "loop"
                | "match"
                | "mod"
                | "move"
                | "mut"
                | "ref"
                | "return"
                | "self"
                | "Self"
                | "static"
                | "struct"
                | "super"
                | "true"
                | "unsafe"
                | "use"
                | "where"
                | "while"
        )
}

/// The identifier ending `s`, only when it stands alone as an operand: not a
/// field (`x.f`), a path segment (`m::x`), or a lifetime/label.
fn bare_trailing_ident(s: &str) -> Option<&str> {
    let trimmed = s.trim_end();
    let ident = extract_trailing_ident(trimmed)?;
    let prefix = &trimmed[..trimmed.len() - ident.len()];
    if matches!(prefix.chars().next_back(), Some('.' | ':' | '\'')) {
        return None;
    }
    is_variable_name(ident).then_some(ident)
}

/// The identifier starting `s`, only when it stands alone as an operand: not a
/// method receiver, call, index, path, or macro (`x.f`, `x(..)`, `x[..]`,
/// `x::y`, `x!`).
fn bare_leading_ident(s: &str) -> Option<&str> {
    let trimmed = s.trim_start();
    let ident = extract_leading_ident(trimmed)?;
    let suffix = trimmed[ident.len()..].trim_start();
    if matches!(suffix.chars().next(), Some('.' | '(' | '[' | ':' | '!' | '{')) {
        return None;
    }
    is_variable_name(ident).then_some(ident)
}

/// Extract the trailing identifier from a string.
fn extract_trailing_ident(s: &str) -> Option<&str> {
    let trimmed = s.trim_end();
    let start =
        trimmed.rfind(|c: char| !c.is_alphanumeric() && c != '_').map(|p| p + 1).unwrap_or(0);
    let ident = &trimmed[start..];
    if ident.is_empty() { None } else { Some(ident) }
}

/// Extract the leading identifier from a string.
fn extract_leading_ident(s: &str) -> Option<&str> {
    let trimmed = s.trim_start();
    let end = trimmed.find(|c: char| !c.is_alphanumeric() && c != '_').unwrap_or(trimmed.len());
    let ident = &trimmed[..end];
    if ident.is_empty() { None } else { Some(ident) }
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

    // --- find_arithmetic_operand_pairs tests ---

    #[test]
    fn test_find_arithmetic_operands_midpoint() {
        let ctx = extract_function(MIDPOINT_SOURCE, "get_midpoint").unwrap();
        let ops = find_arithmetic_operand_pairs(&ctx);
        // Should find a + b, both parameters
        let add_op = ops.iter().find(|pair| pair.op == '+').expect("should find a + b");
        assert_eq!(add_op.left, "a");
        assert_eq!(add_op.right, "b");
        assert!(add_op.both_params);
    }

    #[test]
    fn test_find_arithmetic_operand_pairs_accepts_locals() {
        let ctx = extract_function(BINARY_SEARCH_SOURCE, "binary_search").unwrap();
        let pairs = find_arithmetic_operand_pairs(&ctx);
        let add = pairs.iter().find(|p| p.op == '+').expect("low + high is a local pair");
        assert_eq!((add.left.as_str(), add.right.as_str()), ("low", "high"));
        assert!(!add.both_params, "low/high are body locals, not parameters");
        // `arr.len() - 1` and `mid + 1` name no bound variable pair.
        assert!(pairs.iter().all(|p| p.left != "len" && p.right != "1"));
        // No pair here is parameter-only, so no precondition may name one.
        assert!(pairs.iter().all(|p| !p.both_params));
    }

    #[test]
    fn test_find_arithmetic_operand_pairs_rejects_fields_and_unbound_names() {
        let source = "fn f(s: &S, y: u32) -> u32 {\n    s.x + y + z.len() + w\n}";
        let ctx = extract_function(source, "f").unwrap();
        let pairs = find_arithmetic_operand_pairs(&ctx);
        assert!(
            pairs.is_empty(),
            "field `x`, receiver `z` and unbound `w` are not operands: {pairs:?}"
        );
    }

    // --- read_function (file I/O) tests ---

    #[test]
    fn test_read_function_from_midpoint_example() {
        // This test reads the actual examples/midpoint.rs file
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/midpoint.rs");
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

    #[test]
    fn wave492_zero_alloc_matchers_and_lazy_locals_parity() {
        let source = r#"
fn helper_prefix(x: u32) -> u32 { x }
fn helper<T: Copy>(arr: &[T], idx: usize, shift: u32, div: u32, a: u32) -> u32 {
    let local = a << shift;
    let _ = &arr[idx];
    let sum = local + a;
    sum / div
}
"#;
        let ctx = extract_function(source, "helper").expect("should find generic helper, not helper_prefix");
        assert_eq!(find_first_divisor_param(&ctx), Some("div"));
        assert_eq!(find_divisor_params(&ctx), vec!["div".to_string()]);
        assert_eq!(find_first_shift_param(&ctx), Some("shift"));
        assert_eq!(find_shift_params(&ctx), vec!["shift".to_string()]);
        assert_eq!(find_first_index_param(&ctx), Some(("idx", Some("arr"))));
        assert_eq!(find_index_params(&ctx), vec![("idx".to_string(), Some("arr".to_string()))]);
        let pair = find_first_arithmetic_operand_pair(&ctx, '+').expect("should find local + a");
        assert_eq!(pair.left, "local");
        assert_eq!(pair.right, "a");
        assert!(!pair.both_params);
    }
}
