//! Simplified AST parsing and semantic preservation checking.
//!
//! Parses source into a simplified AST for structural comparison and
//! checks that rewrites preserve semantics (only additive changes).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use super::types::{AstNode, SemanticDiff};

/// Parse source into a simplified AST for structural comparison.
#[must_use]
pub fn parse_simplified_ast(source: &str) -> Vec<AstNode> {
    let mut nodes = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let trimmed = lines[i].trim();

        if trimmed.is_empty() {
            i += 1;
            continue;
        }

        // Attribute
        if trimmed.starts_with("#[") {
            nodes.push(AstNode::Attribute { text: trimmed.to_string() });
            i += 1;
            continue;
        }

        // Function definition
        if is_fn_start(trimmed) {
            let name = extract_fn_name(trimmed).unwrap_or_default();
            let params = extract_fn_params(trimmed);
            let return_type = extract_return_type(trimmed);

            // Collect the body until we find the matching closing brace
            let body_start = i + 1;
            let body_end = find_closing_brace(&lines, i);
            let body_lines = if body_end > body_start {
                lines[body_start..body_end].join("\n")
            } else {
                String::new()
            };
            let body = parse_simplified_ast(&body_lines);

            nodes.push(AstNode::Function { name, params, return_type, body });
            i = body_end + 1;
            continue;
        }

        // If expression
        if trimmed.starts_with("if ") || trimmed == "if" {
            let condition =
                trimmed.strip_prefix("if ").unwrap_or("").trim_end_matches('{').trim().to_string();
            nodes.push(AstNode::If {
                condition,
                then_branch: Box::new(AstNode::Block { children: Vec::new() }),
                else_branch: None,
            });
            i += 1;
            continue;
        }

        // Return
        if trimmed.starts_with("return ") || trimmed == "return" || trimmed == "return;" {
            let expr = trimmed
                .strip_prefix("return")
                .map(|s| s.trim().trim_end_matches(';').to_string())
                .filter(|s| !s.is_empty());
            nodes.push(AstNode::Return { expr });
            i += 1;
            continue;
        }

        // Loop/while/for
        if trimmed.starts_with("loop ")
            || trimmed.starts_with("while ")
            || trimmed.starts_with("for ")
        {
            nodes.push(AstNode::Loop { body: Box::new(AstNode::Block { children: Vec::new() }) });
            i += 1;
            continue;
        }

        // Generic statement
        nodes.push(AstNode::Statement { text: trimmed.to_string() });
        i += 1;
    }

    nodes
}

/// Check semantic preservation between original and rewritten source.
///
/// Parses both into simplified ASTs and compares. Only additive changes
/// (new attributes, new assertions) are considered semantics-preserving.
#[must_use]
pub fn check_semantic_preservation(original: &str, rewritten: &str) -> SemanticDiff {
    let orig_ast = parse_simplified_ast(original);
    let new_ast = parse_simplified_ast(rewritten);

    let mut added = Vec::new();
    let mut removed = Vec::new();

    // Find nodes in new that are not in original
    for node in &new_ast {
        if !orig_ast.contains(node) {
            added.push(node.clone());
        }
    }

    // Find nodes in original that are not in new
    for node in &orig_ast {
        if !new_ast.contains(node) {
            removed.push(node.clone());
        }
    }

    // Semantics preserved if:
    // 1. No non-attribute/non-assertion nodes were removed
    // 2. Only attributes or assertions were added
    let only_attrs_added = added.iter().all(|n| matches!(n, AstNode::Attribute { .. }));
    let no_structural_removals = removed.iter().all(|n| matches!(n, AstNode::Attribute { .. }));
    let preserves = only_attrs_added && no_structural_removals;

    let summary = if added.is_empty() && removed.is_empty() {
        "No structural changes detected".to_string()
    } else {
        format!(
            "{} node(s) added, {} node(s) removed, semantics {}",
            added.len(),
            removed.len(),
            if preserves { "preserved" } else { "may be changed" }
        )
    };

    SemanticDiff { added, removed, preserves_semantics: preserves, summary }
}

// --- Helper functions for AST parsing ---

pub(crate) fn is_fn_start(line: &str) -> bool {
    line.starts_with("fn ")
        || line.starts_with("pub fn ")
        || line.starts_with("pub(crate) fn ")
        || line.starts_with("async fn ")
        || line.starts_with("pub async fn ")
        || line.starts_with("unsafe fn ")
        || line.starts_with("pub unsafe fn ")
}

pub(crate) fn extract_fn_name(line: &str) -> Option<String> {
    // Find "fn " and extract the name before "("
    let fn_pos = line.find("fn ")?;
    let after_fn = &line[fn_pos + 3..];
    let name_end = after_fn.find('(')?;
    Some(after_fn[..name_end].trim().to_string())
}

pub(crate) fn extract_fn_params(line: &str) -> Vec<String> {
    let open = match line.find('(') {
        Some(p) => p,
        None => return Vec::new(),
    };
    let close = match line.find(')') {
        Some(p) => p,
        None => return Vec::new(),
    };
    if close <= open + 1 {
        return Vec::new();
    }
    let params_str = &line[open + 1..close];
    params_str.split(',').map(|p| p.trim().to_string()).filter(|p| !p.is_empty()).collect()
}

pub(crate) fn extract_return_type(line: &str) -> Option<String> {
    let close_paren = line.find(')')?;
    let after_close = &line[close_paren + 1..];
    let arrow = after_close.find("->")?;
    let ret = after_close[arrow + 2..].trim().trim_end_matches('{').trim();
    if ret.is_empty() { None } else { Some(ret.to_string()) }
}

fn find_closing_brace(lines: &[&str], start: usize) -> usize {
    let mut depth: i32 = 0;
    for (i, line) in lines.iter().enumerate().skip(start) {
        for ch in line.chars() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        return i;
                    }
                }
                _ => {}
            }
        }
    }
    lines.len().saturating_sub(1)
}
