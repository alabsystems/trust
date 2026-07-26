//! Helper/utility functions for validation checks.
//!
//! Extraction of function signatures, native clauses/compatibility attributes, identifiers,
//! and other source-level analysis utilities.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use super::semantic::is_fn_start;

/// Count occurrences of a pattern in source text.
pub(crate) fn count_occurrences(source: &str, pattern: &str) -> usize {
    source.matches(pattern).count()
}

fn spec_attr_kind(line: &str) -> Option<&str> {
    let inner = line.strip_prefix("#[")?.trim_start();
    let name_end = inner.find(['(', '=', ' ', ']']).unwrap_or(inner.len());
    let name = inner[..name_end].trim();
    let name = name.rsplit("::").next().unwrap_or(name);

    match name {
        "requires" | "contracts_requires" | "trust_requires" => Some("requires"),
        "ensures" | "contracts_ensures" | "trust_ensures" => Some("ensures"),
        "invariant" | "trust_invariant" => Some("invariant"),
        _ => None,
    }
}

/// Extract the body string from a native clause or compatibility attribute.
///
/// Given `#[requires("x > 0")]`, returns `Some("x > 0")`.
pub(crate) fn extract_spec_body(spec_line: &str) -> Option<String> {
    let trimmed = spec_line.trim();
    for keyword in ["requires", "ensures", "invariant"] {
        if let Some(body) = trimmed.strip_prefix(keyword)
            && body.chars().next().is_some_and(char::is_whitespace)
        {
            let body = body.trim();
            return (!body.is_empty()).then(|| body.to_string());
        }
    }
    // Find the opening parenthesis and quote
    let open_paren = spec_line.find('(')?;
    let close_paren = spec_line.rfind(')')?;
    if close_paren <= open_paren + 1 {
        return None;
    }
    let inner = spec_line[open_paren + 1..close_paren].trim();
    // Strip surrounding quotes
    let inner = inner.strip_prefix('"').unwrap_or(inner);
    let inner = inner.strip_suffix('"').unwrap_or(inner);
    Some(inner.to_string())
}

/// Strip native clauses, compatibility attributes, and assertion lines for comparison.
pub(crate) fn strip_spec_lines(source: &str) -> String {
    let masked = crate::ast_rewriter::mask_native_contract_clauses(source)
        .unwrap_or_else(|_| source.to_owned());
    let stripped = masked
        .lines()
        .filter(|line| {
            let t = line.trim();
            spec_attr_kind(t).is_none()
                && !t.starts_with("assert!(")
                && !t.starts_with("debug_assert!(")
        })
        .collect::<Vec<_>>()
        .join("\n");
    match syn::parse_file(&stripped) {
        Ok(file) => quote::ToTokens::to_token_stream(&file).to_string(),
        Err(_) => stripped,
    }
}

/// Extract all parameter names from all function signatures in source.
pub(crate) fn extract_all_param_names(source: &str) -> Vec<String> {
    let mut names = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        if is_fn_start(trimmed) {
            let params = super::semantic::extract_fn_params(trimmed);
            for param in params {
                // Extract the name part before the `:` type annotation
                if let Some(name) = param.split(':').next() {
                    let name = name.trim().trim_start_matches('&').trim_start_matches("mut ");
                    if !name.is_empty() && name != "self" && name != "&self" && name != "&mut self"
                    {
                        names.push(name.to_string());
                    }
                }
            }
        }
    }
    names
}

/// Extract simple identifiers from a spec expression body.
pub(crate) fn extract_identifiers(expr: &str) -> Vec<String> {
    let mut idents = Vec::new();
    let mut current = String::new();

    for ch in expr.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            current.push(ch);
        } else {
            if !current.is_empty() && !current.chars().next().unwrap_or('0').is_ascii_digit() {
                idents.push(std::mem::take(&mut current));
            } else {
                current.clear();
            }
        }
    }
    if !current.is_empty() && !current.chars().next().unwrap_or('0').is_ascii_digit() {
        idents.push(current);
    }
    idents
}

/// Check if an identifier looks like a type constant (e.g., `u64`, `MAX`, `i32`).
pub(crate) fn is_type_constant(ident: &str) -> bool {
    // Common Rust type-associated constants
    let type_patterns = [
        "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
        "f32", "f64", "bool", "char", "MAX", "MIN", "INFINITY", "NAN", "len", "is_empty",
    ];
    type_patterns.contains(&ident)
}

/// Count heuristic warning patterns in source (unused variables, dead code markers, etc.).
pub(crate) fn count_warning_patterns(source: &str) -> usize {
    let mut count = 0;
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[allow(") || trimmed.starts_with("#[warn(") {
            count += 1;
        }
        if trimmed.starts_with("let _") && !trimmed.starts_with("let __") {
            count += 1;
        }
    }
    count
}

/// Extract function signatures from source (lines starting with `fn ` or `pub fn `).
pub(crate) fn extract_fn_signatures(source: &str) -> Vec<String> {
    source
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            if trimmed.starts_with("fn ")
                || trimmed.starts_with("pub fn ")
                || trimmed.starts_with("pub(crate) fn ")
                || trimmed.starts_with("pub(super) fn ")
                || trimmed.starts_with("async fn ")
                || trimmed.starts_with("pub async fn ")
                || trimmed.starts_with("unsafe fn ")
                || trimmed.starts_with("pub unsafe fn ")
            {
                // Extract up to the opening brace or semicolon
                let sig = if let Some(pos) = trimmed.find('{') {
                    trimmed[..pos].trim()
                } else if let Some(pos) = trimmed.find(';') {
                    trimmed[..pos].trim()
                } else {
                    trimmed
                };
                Some(sig.to_string())
            } else {
                None
            }
        })
        .collect()
}

/// Extract native clauses plus explicitly ingested compatibility attributes.
pub(crate) fn extract_spec_attributes(source: &str) -> Vec<String> {
    let mut specs = source
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            if spec_attr_kind(trimmed).is_some() { Some(trimmed.to_string()) } else { None }
        })
        .collect::<Vec<_>>();
    if let Ok(native) = crate::ast_rewriter::native_contract_clause_spans(source) {
        specs.extend(native.into_iter().filter_map(|clause| {
            source
                .get(clause.expression)
                .map(|expression| format!("{} {}", clause.kind.keyword(), expression.trim()))
        }));
    }
    specs
}
