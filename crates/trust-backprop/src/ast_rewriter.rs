//! AST-aware source rewriting using `syn` for semantic targeting.
//!
//! Resolves rewrite targets by parsing source with `syn`, locating AST nodes,
//! and extracting byte offsets from their spans. This replaces the fragile
//! string-matching approach in `locator.rs` with structurally correct targeting
//! while preserving the existing `RewriteEngine` for actual text mutation.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use syn::visit::Visit;

use crate::{ClaimProvenance, ContractClauseKind, RewriteKind, SourceRewrite};

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from AST-aware rewriting.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum AstRewriteError {
    /// The source file could not be parsed by syn.
    #[error("source parse error: {0}")]
    SourceParseError(String),

    /// The target function was not found in the AST.
    #[error("function `{name}` not found (occurrence {occurrence})")]
    FunctionNotFound { name: String, occurrence: usize },

    /// A short name matched more than one qualified function identity.
    #[error("function selector `{selector}` is ambiguous ({matches} matches): {identities:?}")]
    AmbiguousFunction { selector: String, matches: usize, identities: Vec<String> },

    /// The function appears to be inside a macro invocation.
    #[error("function `{name}` is inside a macro and cannot be targeted")]
    FunctionInMacro { name: String },

    /// The target expression was not found in the function body.
    #[error(
        "expression `{pattern}` not found in function (occurrence {occurrence}, total matches: {total_matches})"
    )]
    ExpressionNotFound { pattern: String, occurrence: usize, total_matches: usize },

    /// The expression pattern could not be parsed by syn.
    #[error("expression pattern parse error for `{pattern}`: {error}")]
    PatternParseError { pattern: String, error: String },

    /// A statement index was out of range.
    #[error("statement index {index} out of range (function has {total} statements)")]
    StatementIndexOutOfRange { index: usize, total: usize },

    /// The rewrite produced source that does not parse.
    #[error("rewrite produced unparseable source")]
    ResultParseError,

    /// A first-class native clause was malformed or unterminated.
    #[error("malformed native contract clause at byte {offset}: {reason}")]
    MalformedNativeContract { offset: usize, reason: String },

    /// A contract parameter could not be bound to one source identifier.
    #[error("function `{function}` has unsupported contract parameter pattern `{pattern}`")]
    UnsupportedSignatureBinding { function: String, pattern: String },

    /// A source binding collides with contract language syntax or an internal place.
    #[error("function `{function}` uses reserved contract parameter name `{name}`")]
    ReservedContractBinding { function: String, name: String },

    /// A proc-macro span did not identify a valid UTF-8 character position.
    #[error("invalid source span position at line {line}, UTF-8 column {column}")]
    InvalidSpanPosition { line: usize, column: usize },

    /// The underlying rewrite engine reported an error.
    #[error("rewrite engine error: {0}")]
    RewriteEngine(#[from] crate::RewriteError),
}

// ---------------------------------------------------------------------------
// Rewrite target types
// ---------------------------------------------------------------------------

/// A rewrite target identified by AST structure, not byte offset.
///
/// Targets are resolved against the parsed AST at application time,
/// producing byte offsets that are guaranteed to be correct for the
/// current source text.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AstRewriteTarget {
    /// Insert an attribute before a function item.
    ///
    /// Resolves to the byte offset of the first token of the function item
    /// (after any doc comments, before the first attribute or visibility keyword).
    FunctionAttribute {
        fn_name: String,
        /// Which occurrence if the function name appears multiple times
        /// (e.g., in different impl blocks). 0-based.
        occurrence: usize,
    },

    /// Insert a first-class `requires`/`ensures` clause after the return type
    /// and before a `where` clause or function body.
    FunctionSignatureClause { fn_name: String, occurrence: usize },

    /// Replace a specific expression within a function body.
    ///
    /// Uses syn's expression visitor to find the exact AST node matching
    /// the pattern, disambiguating multiple textual occurrences.
    ExpressionInFunction {
        fn_name: String,
        /// The expression to match, as a parseable Rust expression string.
        /// Matched structurally (AST equality via token stream), not textually.
        expr_pattern: String,
        /// Which occurrence of the matching expression (0-based).
        occurrence: usize,
    },

    /// Insert a statement at the beginning of a function body.
    ///
    /// Resolves to the byte offset just after the opening `{` of the
    /// function body.
    FunctionBodyStart { fn_name: String, occurrence: usize },

    /// Insert a statement before a specific statement index in a function body.
    FunctionBodyBefore { fn_name: String, stmt_index: usize, occurrence: usize },
}

/// A source rewrite identified by semantic target rather than byte offset.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SemanticRewrite {
    /// Path to the source file to modify.
    pub file_path: String,
    /// What to target in the AST.
    pub target: AstRewriteTarget,
    /// What kind of rewrite to perform.
    pub kind: RewriteKind,
    /// The function this rewrite targets.
    pub function_name: String,
    /// Human-readable rationale.
    pub rationale: String,
}

/// One native signature clause located in source text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeContractClauseSpan {
    /// Byte offset of the owning function's `fn` keyword.
    pub function_offset: usize,
    /// Source spelling of the owning function name.
    pub function_name: String,
    /// Clause kind.
    pub kind: ContractClauseKind,
    /// Byte range containing only the predicate (not the keyword).
    pub expression: std::ops::Range<usize>,
    /// Byte range containing the keyword and predicate.
    pub clause: std::ops::Range<usize>,
}

// ---------------------------------------------------------------------------
// Resolved target
// ---------------------------------------------------------------------------

/// The result of resolving an `AstRewriteTarget` against parsed source.
#[derive(Debug, Clone)]
pub(crate) struct ResolvedTarget {
    /// Byte offset for insertion or replacement start.
    pub(crate) offset: usize,
    /// Exact end of an AST expression replacement, when applicable.
    pub(crate) end: Option<usize>,
}

// ---------------------------------------------------------------------------
// Line offset table
// ---------------------------------------------------------------------------

/// Pre-computed line-offset table for converting Span positions to byte offsets.
struct LineOffsets<'a> {
    source: &'a str,
    /// Byte offset of the start of each line (0-indexed in the vec,
    /// representing 1-based line numbers: offsets[0] = line 1 start).
    offsets: Vec<usize>,
}

impl<'a> LineOffsets<'a> {
    fn new(source: &'a str) -> Self {
        let mut offsets = vec![0];
        for (i, byte) in source.as_bytes().iter().enumerate() {
            if *byte == b'\n' {
                offsets.push(i + 1);
            }
        }
        Self { source, offsets }
    }

    /// Convert a line/column position to a byte offset.
    ///
    /// `line` is 1-based (as returned by `Span::start().line`).
    /// `column` is 0-based (as returned by `Span::start().column`).
    fn byte_offset(&self, line: usize, column: usize) -> Result<usize, AstRewriteError> {
        let Some(line_index) = line.checked_sub(1) else {
            return Err(AstRewriteError::InvalidSpanPosition { line, column });
        };
        let Some(line_start) = self.offsets.get(line_index).copied() else {
            return Err(AstRewriteError::InvalidSpanPosition { line, column });
        };
        let line_end = self.offsets.get(line_index + 1).copied().unwrap_or(self.source.len());
        let line_source = &self.source[line_start..line_end];
        let relative = line_source
            .char_indices()
            .nth(column)
            .map(|(offset, _)| offset)
            .or_else(|| (column == line_source.chars().count()).then_some(line_source.len()));
        relative
            .map(|relative| line_start + relative)
            .ok_or(AstRewriteError::InvalidSpanPosition { line, column })
    }
}

fn span_start_byte_offset(source: &str, span: proc_macro2::Span) -> Result<usize, AstRewriteError> {
    let table = LineOffsets::new(source);
    let start = span.start();
    table.byte_offset(start.line, start.column)
}

fn span_end_byte_offset(source: &str, span: proc_macro2::Span) -> Result<usize, AstRewriteError> {
    let table = LineOffsets::new(source);
    let end = span.end();
    table.byte_offset(end.line, end.column)
}

// ---------------------------------------------------------------------------
// Native contract masking
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy)]
struct LexToken {
    start: usize,
    end: usize,
    byte: u8,
    ident: bool,
}

impl LexToken {
    fn text<'a>(self, source: &'a str) -> &'a str {
        &source[self.start..self.end]
    }
}

fn is_ident_start(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphabetic()
}

fn is_ident_continue(byte: u8) -> bool {
    is_ident_start(byte) || byte.is_ascii_digit()
}

fn quoted_end(bytes: &[u8], start: usize, quote: u8) -> usize {
    let mut index = start + 1;
    let mut escaped = false;
    while index < bytes.len() {
        let byte = bytes[index];
        index += 1;
        if escaped {
            escaped = false;
        } else if byte == b'\\' {
            escaped = true;
        } else if byte == quote {
            break;
        } else if byte == b'\n' && quote == b'\'' {
            return start + 1;
        }
    }
    index
}

fn raw_string_end(bytes: &[u8], start: usize, prefix_len: usize) -> Option<usize> {
    let mut index = start + prefix_len;
    let mut hashes = 0usize;
    while bytes.get(index) == Some(&b'#') {
        hashes += 1;
        index += 1;
    }
    if bytes.get(index) != Some(&b'"') {
        return None;
    }
    index += 1;
    while index < bytes.len() {
        if bytes[index] == b'"'
            && bytes
                .get(index + 1..index + 1 + hashes)
                .is_some_and(|suffix| suffix.iter().all(|byte| *byte == b'#'))
        {
            return Some(index + 1 + hashes);
        }
        index += 1;
    }
    Some(bytes.len())
}

fn lex_for_contracts(source: &str) -> Vec<LexToken> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0usize;
    while index < bytes.len() {
        let byte = bytes[index];
        if byte.is_ascii_whitespace() {
            index += 1;
            continue;
        }
        if bytes.get(index..index + 2) == Some(b"//") {
            index += 2;
            while index < bytes.len() && bytes[index] != b'\n' {
                index += 1;
            }
            continue;
        }
        if bytes.get(index..index + 2) == Some(b"/*") {
            index += 2;
            let mut depth = 1usize;
            while index < bytes.len() && depth > 0 {
                if bytes.get(index..index + 2) == Some(b"/*") {
                    depth += 1;
                    index += 2;
                } else if bytes.get(index..index + 2) == Some(b"*/") {
                    depth -= 1;
                    index += 2;
                } else {
                    index += 1;
                }
            }
            continue;
        }

        let raw_prefix = if byte == b'r' {
            Some(1)
        } else if bytes.get(index..index + 2) == Some(b"br")
            || bytes.get(index..index + 2) == Some(b"cr")
        {
            Some(2)
        } else {
            None
        };
        if let Some(prefix_len) = raw_prefix
            && let Some(end) = raw_string_end(bytes, index, prefix_len)
        {
            tokens.push(LexToken { start: index, end, byte: b'"', ident: false });
            index = end;
            continue;
        }

        if byte == b'"' || ((byte == b'b' || byte == b'c') && bytes.get(index + 1) == Some(&b'"')) {
            let quote = if byte == b'"' { index } else { index + 1 };
            let end = quoted_end(bytes, quote, b'"');
            tokens.push(LexToken { start: index, end, byte: b'"', ident: false });
            index = end;
            continue;
        }
        if byte == b'\'' && index.checked_sub(1).is_none_or(|prev| !is_ident_continue(bytes[prev]))
        {
            let end = quoted_end(bytes, index, b'\'');
            if end > index + 1 && bytes.get(end - 1) == Some(&b'\'') {
                tokens.push(LexToken { start: index, end, byte: b'\'', ident: false });
                index = end;
                continue;
            }
        }
        if is_ident_start(byte) {
            let start = index;
            index += 1;
            while index < bytes.len() && is_ident_continue(bytes[index]) {
                index += 1;
            }
            tokens.push(LexToken { start, end: index, byte, ident: true });
            continue;
        }
        tokens.push(LexToken { start: index, end: index + 1, byte, ident: false });
        index += 1;
    }
    tokens
}

fn matching_close(open: u8, close: u8) -> bool {
    matches!((open, close), (b'(', b')') | (b'[', b']') | (b'{', b'}'))
}

fn find_matching_delimiter(tokens: &[LexToken], open_index: usize) -> Option<usize> {
    let mut stack = vec![tokens[open_index].byte];
    for (index, token) in tokens.iter().enumerate().skip(open_index + 1) {
        match token.byte {
            b'(' | b'[' | b'{' => stack.push(token.byte),
            b')' | b']' | b'}' => {
                if !stack.last().is_some_and(|open| matching_close(*open, token.byte)) {
                    return None;
                }
                stack.pop();
                if stack.is_empty() {
                    return Some(index);
                }
            }
            _ => {}
        }
    }
    None
}

fn scan_native_contract_clauses(
    source: &str,
) -> Result<Vec<NativeContractClauseSpan>, AstRewriteError> {
    let tokens = lex_for_contracts(source);
    let mut clauses = Vec::new();
    let mut cursor = 0usize;
    while cursor < tokens.len() {
        if !tokens[cursor].ident || tokens[cursor].text(source) != "fn" {
            cursor += 1;
            continue;
        }
        let function_offset = tokens[cursor].start;
        let function_name = tokens
            .iter()
            .skip(cursor + 1)
            .find(|token| token.ident)
            .map(|token| token.text(source).to_string())
            .unwrap_or_default();

        // Find the real parameter list, ignoring parentheses inside generic
        // bounds such as `T: Fn(i32)`.
        let mut angle_depth = 0usize;
        let mut params_open = None;
        let mut probe = cursor + 1;
        while probe < tokens.len() {
            let token = tokens[probe];
            match token.byte {
                b'<' => angle_depth += 1,
                b'>' => angle_depth = angle_depth.saturating_sub(1),
                b'(' if angle_depth == 0 => {
                    params_open = Some(probe);
                    break;
                }
                b'{' | b';' if angle_depth == 0 => break,
                _ => {}
            }
            probe += 1;
        }
        let Some(params_open) = params_open else {
            cursor += 1;
            continue;
        };
        let Some(params_close) = find_matching_delimiter(&tokens, params_open) else {
            cursor += 1;
            continue;
        };

        probe = params_close + 1;
        let mut groups = Vec::new();
        let mut type_angles = 0usize;
        while probe < tokens.len() {
            let token = tokens[probe];
            let text = token.text(source);
            if groups.is_empty() && type_angles == 0 {
                if token.ident && text == "where" || token.byte == b'{' || token.byte == b';' {
                    break;
                }
                if token.ident && matches!(text, "requires" | "ensures") {
                    let kind = if text == "requires" {
                        ContractClauseKind::Requires
                    } else {
                        ContractClauseKind::Ensures
                    };
                    let keyword_start = token.start;
                    let mut clause_probe = probe + 1;
                    let mut clause_groups = Vec::new();
                    let mut pending_block = false;
                    let mut first_expression = None;
                    let mut last_expression = None;
                    while clause_probe < tokens.len() {
                        let part = tokens[clause_probe];
                        let part_text = part.text(source);
                        if clause_groups.is_empty() {
                            if (part.ident && matches!(part_text, "requires" | "ensures" | "where"))
                                || part.byte == b';'
                            {
                                break;
                            }
                            if part.byte == b'{' && !pending_block {
                                break;
                            }
                        }
                        first_expression.get_or_insert(part.start);
                        last_expression = Some(part.end);
                        match part.byte {
                            b'(' | b'[' => clause_groups.push(part.byte),
                            b'{' => {
                                clause_groups.push(part.byte);
                                pending_block = false;
                            }
                            b')' | b']' | b'}' => {
                                if !clause_groups
                                    .last()
                                    .is_some_and(|open| matching_close(*open, part.byte))
                                {
                                    return Err(AstRewriteError::MalformedNativeContract {
                                        offset: part.start,
                                        reason: "unbalanced delimiter".to_string(),
                                    });
                                }
                                clause_groups.pop();
                            }
                            _ => {}
                        }
                        if clause_groups.is_empty()
                            && part.ident
                            && matches!(
                                part_text,
                                "match" | "if" | "else" | "loop" | "while" | "unsafe"
                            )
                        {
                            pending_block = true;
                        }
                        clause_probe += 1;
                    }
                    let (Some(expression_start), Some(expression_end)) =
                        (first_expression, last_expression)
                    else {
                        return Err(AstRewriteError::MalformedNativeContract {
                            offset: keyword_start,
                            reason: "empty predicate".to_string(),
                        });
                    };
                    if !clause_groups.is_empty() {
                        return Err(AstRewriteError::MalformedNativeContract {
                            offset: keyword_start,
                            reason: "unterminated predicate delimiter".to_string(),
                        });
                    }
                    clauses.push(NativeContractClauseSpan {
                        function_offset,
                        function_name: function_name.clone(),
                        kind,
                        expression: expression_start..expression_end,
                        clause: keyword_start..expression_end,
                    });
                    probe = clause_probe;
                    continue;
                }
            }
            match token.byte {
                b'(' | b'[' | b'{' => groups.push(token.byte),
                b')' | b']' | b'}' => {
                    if groups.last().is_some_and(|open| matching_close(*open, token.byte)) {
                        groups.pop();
                    }
                }
                b'<' if groups.is_empty() => type_angles += 1,
                b'>' if groups.is_empty() => type_angles = type_angles.saturating_sub(1),
                _ => {}
            }
            probe += 1;
        }
        cursor = probe.max(cursor + 1);
    }
    Ok(clauses)
}

/// Return all first-class signature clauses in a source file.
///
/// Compatibility attributes are intentionally excluded: callers that ingest
/// those must label that compatibility origin explicitly.
pub fn native_contract_clause_spans(
    source: &str,
) -> Result<Vec<NativeContractClauseSpan>, AstRewriteError> {
    scan_native_contract_clauses(source)
}

/// Replace native clauses with same-length whitespace so stock Rust parsers
/// can validate the surrounding program without treating Trust syntax as a
/// parse failure. Newlines and byte offsets are preserved exactly.
pub(crate) fn mask_native_contract_clauses(source: &str) -> Result<String, AstRewriteError> {
    let clauses = scan_native_contract_clauses(source)?;
    if clauses.is_empty() {
        return Ok(source.to_owned());
    }
    let mut bytes = source.as_bytes().to_vec();
    for clause in clauses {
        for byte in &mut bytes[clause.clause] {
            if *byte != b'\n' && *byte != b'\r' {
                *byte = b' ';
            }
        }
    }
    String::from_utf8(bytes).map_err(|_| AstRewriteError::ResultParseError)
}

// ---------------------------------------------------------------------------
// Indentation preservation
// ---------------------------------------------------------------------------

/// Compute the indentation string for an insertion point.
///
/// For attribute insertion: matches the indentation of the function item.
/// For assertion insertion: matches the indentation of the containing block + one level.
#[must_use]
pub fn compute_indentation(source: &str, offset: usize, kind: &RewriteKind) -> String {
    // Find the start of the line containing `offset`
    let line_start = source[..offset].rfind('\n').map_or(0, |i| i + 1);

    // Extract leading whitespace from that line
    let base_indent: String =
        source[line_start..].chars().take_while(|c| *c == ' ' || *c == '\t').collect();

    match kind {
        RewriteKind::InsertAttribute { .. } | RewriteKind::InsertContractClause { .. } => {
            // Attributes go at the same indentation as the function
            base_indent
        }
        RewriteKind::InsertAssertion { .. } => {
            // Assertions go inside the function body, one level deeper.
            let indent_unit = detect_indent_unit(source);
            format!("{base_indent}{indent_unit}")
        }
        RewriteKind::ReplaceExpression { .. } => {
            // Expression replacement preserves existing indentation
            base_indent
        }
    }
}

/// Detect the indentation unit used in the source (spaces vs tabs, width).
#[must_use]
pub fn detect_indent_unit(source: &str) -> &'static str {
    let mut spaces_4 = 0usize;
    let mut spaces_2 = 0usize;
    let mut tabs = 0usize;

    for line in source.lines().take(100) {
        if line.starts_with("    ") && !line.starts_with("     ") {
            spaces_4 += 1;
        } else if line.starts_with("  ") && !line.starts_with("   ") {
            spaces_2 += 1;
        } else if line.starts_with('\t') {
            tabs += 1;
        }
    }

    if tabs > spaces_4 && tabs > spaces_2 {
        "\t"
    } else if spaces_2 > spaces_4 {
        "  "
    } else {
        "    "
    }
}

// ---------------------------------------------------------------------------
// Core: resolve_target
// ---------------------------------------------------------------------------

/// Resolve a `SemanticRewrite` against parsed source to produce a `SourceRewrite`.
///
/// Parses the source file with `syn`, locates the target AST node, and
/// extracts its byte offset to produce a `SourceRewrite` that can be
/// applied by the existing `RewriteEngine`.
///
/// # Errors
///
/// Returns `AstRewriteError` if the source cannot be parsed, the target
/// cannot be found, or the expression pattern is invalid.
pub fn resolve_target(
    source: &str,
    rewrite: &SemanticRewrite,
) -> Result<SourceRewrite, AstRewriteError> {
    let parse_source = mask_native_contract_clauses(source)?;
    let file = syn::parse_file(&parse_source)
        .map_err(|e| AstRewriteError::SourceParseError(e.to_string()))?;

    let resolved = resolve_target_from_ast(&file, &parse_source, &rewrite.target)?;

    let mut kind = rewrite.kind.clone();
    if let (RewriteKind::ReplaceExpression { old_text, .. }, Some(end)) = (&mut kind, resolved.end)
    {
        // Bind replacement to the exact AST span, not the proposal's normalized
        // token spelling. This preserves comments/whitespace and makes
        // RewriteEngine's source precondition exact.
        *old_text =
            source.get(resolved.offset..end).ok_or(AstRewriteError::ResultParseError)?.to_string();
    }

    Ok(SourceRewrite {
        file_path: rewrite.file_path.clone(),
        offset: resolved.offset,
        kind,
        function_name: rewrite.function_name.clone(),
        rationale: rewrite.rationale.clone(),
        expected_source_hash: Some(trust_types::stable_sha256_hex(source.as_bytes())),
        provenance: ClaimProvenance::Authoritative,
    })
}

/// Resolve a target against an already-parsed AST.
pub(crate) fn resolve_target_from_ast(
    file: &syn::File,
    source: &str,
    target: &AstRewriteTarget,
) -> Result<ResolvedTarget, AstRewriteError> {
    match target {
        AstRewriteTarget::FunctionAttribute { fn_name, occurrence } => {
            let offset = resolve_function_attribute(file, source, fn_name, *occurrence)?;
            Ok(ResolvedTarget { offset, end: None })
        }
        AstRewriteTarget::FunctionSignatureClause { fn_name, occurrence } => {
            let offset = resolve_function_signature_clause(file, source, fn_name, *occurrence)?;
            Ok(ResolvedTarget { offset, end: None })
        }
        AstRewriteTarget::ExpressionInFunction { fn_name, expr_pattern, occurrence } => {
            let (start, end) =
                resolve_expression_in_function(file, source, fn_name, expr_pattern, *occurrence)?;
            Ok(ResolvedTarget { offset: start, end: Some(end) })
        }
        AstRewriteTarget::FunctionBodyStart { fn_name, occurrence } => {
            let offset = resolve_function_body_start(file, source, fn_name, *occurrence)?;
            Ok(ResolvedTarget { offset, end: None })
        }
        AstRewriteTarget::FunctionBodyBefore { fn_name, stmt_index, occurrence } => {
            let offset =
                resolve_function_body_before(file, source, fn_name, *stmt_index, *occurrence)?;
            Ok(ResolvedTarget { offset, end: None })
        }
    }
}

// ---------------------------------------------------------------------------
// Target resolvers
// ---------------------------------------------------------------------------

/// Collected function info for target resolution.
struct FoundFn<'a> {
    identity: String,
    attrs_span_start: Option<proc_macro2::Span>,
    /// Span of the first visible token of the function item (visibility keyword
    /// or `fn` keyword if visibility is inherited).
    item_start_span: proc_macro2::Span,
    signature: &'a syn::Signature,
    block: &'a syn::Block,
}

/// Find one function by exact qualified identity or a globally unique short name.
///
/// Qualified selectors use `module::function`, `Type::method`,
/// `<Type as Trait>::method`, or combinations with an inline-module prefix.
/// Short names are compatibility-only and fail closed when ambiguous.
fn find_function_in_ast<'a>(
    file: &'a syn::File,
    selector: &str,
) -> Result<FoundFn<'a>, AstRewriteError> {
    let mut functions = Vec::new();
    collect_functions(&file.items, &[], &mut functions);
    let normalized_selector = normalize_identity(selector);
    let qualified = normalized_selector.contains("::") || normalized_selector.starts_with('<');
    let mut matches: Vec<_> = functions
        .into_iter()
        .filter(|function| {
            let identity = normalize_identity(&function.identity);
            if qualified {
                identity == normalized_selector
                    || identity.strip_prefix("crate::") == Some(normalized_selector.as_str())
                    || normalized_selector.strip_prefix("crate::") == Some(identity.as_str())
            } else {
                identity.rsplit("::").next() == Some(normalized_selector.as_str())
            }
        })
        .collect();
    match matches.len() {
        0 => Err(AstRewriteError::FunctionNotFound { name: selector.to_string(), occurrence: 0 }),
        1 => Ok(matches.pop().expect("one function match")),
        count => {
            let mut identities =
                matches.iter().map(|found| found.identity.clone()).collect::<Vec<_>>();
            identities.sort();
            Err(AstRewriteError::AmbiguousFunction {
                selector: selector.to_string(),
                matches: count,
                identities,
            })
        }
    }
}

fn collect_functions<'a>(items: &'a [syn::Item], modules: &[String], out: &mut Vec<FoundFn<'a>>) {
    use quote::ToTokens;

    for item in items {
        match item {
            syn::Item::Fn(item_fn) => {
                let identity = qualify(modules, &item_fn.sig.ident.to_string());
                out.push(FoundFn {
                    identity,
                    attrs_span_start: item_fn.attrs.first().map(|attr| attr.pound_token.span),
                    item_start_span: item_start_span_fn(&item_fn.vis, &item_fn.sig),
                    signature: &item_fn.sig,
                    block: &item_fn.block,
                });
            }
            syn::Item::Mod(item_mod) => {
                if let Some((_, nested)) = &item_mod.content {
                    let mut path = modules.to_vec();
                    path.push(item_mod.ident.to_string());
                    collect_functions(nested, &path, out);
                }
            }
            syn::Item::Impl(item_impl) => {
                let self_ty = item_impl.self_ty.to_token_stream().to_string();
                let owner = if let Some((_, trait_path, _)) = &item_impl.trait_ {
                    format!("<{self_ty} as {}>", trait_path.to_token_stream())
                } else {
                    self_ty
                };
                for impl_item in &item_impl.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        let identity = qualify(modules, &format!("{owner}::{}", method.sig.ident));
                        out.push(FoundFn {
                            identity,
                            attrs_span_start: method
                                .attrs
                                .first()
                                .map(|attr| attr.pound_token.span),
                            item_start_span: item_start_span_fn(&method.vis, &method.sig),
                            signature: &method.sig,
                            block: &method.block,
                        });
                    }
                }
            }
            syn::Item::Trait(item_trait) => {
                for trait_item in &item_trait.items {
                    if let syn::TraitItem::Fn(method) = trait_item
                        && let Some(default) = &method.default
                    {
                        let identity = qualify(
                            modules,
                            &format!("{}::{}", item_trait.ident, method.sig.ident),
                        );
                        out.push(FoundFn {
                            identity,
                            attrs_span_start: method
                                .attrs
                                .first()
                                .map(|attr| attr.pound_token.span),
                            item_start_span: method.sig.fn_token.span,
                            signature: &method.sig,
                            block: default,
                        });
                    }
                }
            }
            _ => {}
        }
    }
}

fn qualify(modules: &[String], tail: &str) -> String {
    if modules.is_empty() { tail.to_string() } else { format!("{}::{tail}", modules.join("::")) }
}

fn normalize_identity(identity: &str) -> String {
    identity.chars().filter(|character| !character.is_whitespace()).collect()
}

/// Return the source-contract sort environment for one exact/unambiguous function.
///
/// Contract arithmetic uses mathematical `Int` for Rust integer-like values;
/// `bool` parameters/returns retain `Bool`. Shared-reference deref spellings are
/// included so `*flag` is typed from the pointee rather than the reference.
pub fn contract_sort_environment(
    source: &str,
    selector: &str,
) -> Result<std::collections::BTreeMap<String, trust_types::Sort>, AstRewriteError> {
    use quote::ToTokens;
    use trust_types::Sort;

    let parse_source = mask_native_contract_clauses(source)?;
    let file = syn::parse_file(&parse_source)
        .map_err(|error| AstRewriteError::SourceParseError(error.to_string()))?;
    let found = find_function_in_ast(&file, selector)?;
    let mut sorts = std::collections::BTreeMap::new();
    for input in &found.signature.inputs {
        match input {
            syn::FnArg::Receiver(_) => {
                sorts.insert("self".to_string(), Sort::Int);
            }
            syn::FnArg::Typed(argument) => {
                let syn::Pat::Ident(binding) = argument.pat.as_ref() else {
                    return Err(AstRewriteError::UnsupportedSignatureBinding {
                        function: found.identity.clone(),
                        pattern: argument.pat.to_token_stream().to_string(),
                    });
                };
                let name = binding.ident.to_string();
                if matches!(name.as_str(), "_0" | "result") {
                    return Err(AstRewriteError::ReservedContractBinding {
                        function: found.identity.clone(),
                        name,
                    });
                }
                sorts.insert(name.clone(), source_contract_sort(&argument.ty));
                if let syn::Type::Reference(reference) = argument.ty.as_ref() {
                    sorts.insert(format!("{name}*"), source_contract_sort(&reference.elem));
                }
            }
        }
    }
    if let syn::ReturnType::Type(_, ty) = &found.signature.output {
        sorts.insert("_0".to_string(), source_contract_sort(ty));
    }
    Ok(sorts)
}

fn source_contract_sort(ty: &syn::Type) -> trust_types::Sort {
    if let syn::Type::Path(path) = ty
        && path.qself.is_none()
        && path.path.segments.last().is_some_and(|segment| segment.ident == "bool")
    {
        trust_types::Sort::Bool
    } else {
        trust_types::Sort::Int
    }
}

/// Get the span of the first real token in a function declaration.
///
/// For `pub fn foo`, this is the span of `pub`.
/// For `fn foo` (inherited visibility), this is the span of `fn`.
fn item_start_span_fn(vis: &syn::Visibility, sig: &syn::Signature) -> proc_macro2::Span {
    use quote::ToTokens;
    // Try visibility first
    let vis_tokens: proc_macro2::TokenStream = vis.to_token_stream();
    if let Some(first) = vis_tokens.into_iter().next() {
        return first.span();
    }
    // Fall back to the fn keyword
    sig.fn_token.span
}

/// Resolve the insertion point for a function attribute.
///
/// Returns the byte offset where an attribute should be inserted -- before
/// the first existing attribute, or before the visibility/fn keyword.
fn resolve_function_attribute(
    file: &syn::File,
    source: &str,
    fn_name: &str,
    occurrence: usize,
) -> Result<usize, AstRewriteError> {
    if occurrence != 0 {
        return Err(AstRewriteError::FunctionNotFound { name: fn_name.to_string(), occurrence });
    }
    let found = find_function_in_ast(file, fn_name)?;

    let target_span = found.attrs_span_start.unwrap_or(found.item_start_span);

    let offset = span_start_byte_offset(source, target_span)?;

    // Walk back to the start of the line so the attribute gets its own line.
    let line_start = source[..offset].rfind('\n').map_or(0, |i| i + 1);
    let between = &source[line_start..offset];
    if between.chars().all(|c| c == ' ' || c == '\t') { Ok(line_start) } else { Ok(offset) }
}

/// Resolve the grammar position for a native function contract: immediately
/// before `where` when present, otherwise immediately before the body `{`.
fn resolve_function_signature_clause(
    file: &syn::File,
    source: &str,
    fn_name: &str,
    occurrence: usize,
) -> Result<usize, AstRewriteError> {
    if occurrence != 0 {
        return Err(AstRewriteError::FunctionNotFound { name: fn_name.to_string(), occurrence });
    }
    let found = find_function_in_ast(file, fn_name)?;
    if let Some(where_token) =
        found.signature.generics.where_clause.as_ref().map(|where_clause| &where_clause.where_token)
    {
        span_start_byte_offset(source, where_token.span)
    } else {
        span_start_byte_offset(source, found.block.brace_token.span.open())
    }
}

/// Resolve the byte offset just after the opening `{` of a function body.
fn resolve_function_body_start(
    file: &syn::File,
    source: &str,
    fn_name: &str,
    occurrence: usize,
) -> Result<usize, AstRewriteError> {
    if occurrence != 0 {
        return Err(AstRewriteError::FunctionNotFound { name: fn_name.to_string(), occurrence });
    }
    let found = find_function_in_ast(file, fn_name)?;
    let brace_span = found.block.brace_token.span.open();
    let brace_offset = span_start_byte_offset(source, brace_span)?;
    // The insertion point is just after the `{`.
    Ok(brace_offset + 1)
}

/// Resolve the byte offset before a specific statement in a function body.
fn resolve_function_body_before(
    file: &syn::File,
    source: &str,
    fn_name: &str,
    stmt_index: usize,
    occurrence: usize,
) -> Result<usize, AstRewriteError> {
    if occurrence != 0 {
        return Err(AstRewriteError::FunctionNotFound { name: fn_name.to_string(), occurrence });
    }
    let found = find_function_in_ast(file, fn_name)?;

    if stmt_index >= found.block.stmts.len() {
        return Err(AstRewriteError::StatementIndexOutOfRange {
            index: stmt_index,
            total: found.block.stmts.len(),
        });
    }

    let stmt = &found.block.stmts[stmt_index];
    let stmt_span = stmt_span(stmt);
    let offset = span_start_byte_offset(source, stmt_span)?;

    // Walk back to line start for clean insertion.
    let line_start = source[..offset].rfind('\n').map_or(0, |i| i + 1);
    let between = &source[line_start..offset];
    if between.chars().all(|c| c == ' ' || c == '\t') { Ok(line_start) } else { Ok(offset) }
}

/// Get the span of a statement.
fn stmt_span(stmt: &syn::Stmt) -> proc_macro2::Span {
    use quote::ToTokens;
    stmt.to_token_stream()
        .into_iter()
        .next()
        .map(|t| t.span())
        .unwrap_or_else(proc_macro2::Span::call_site)
}

// ---------------------------------------------------------------------------
// Expression resolution
// ---------------------------------------------------------------------------

/// Find the byte span of a specific expression occurrence within a function.
fn resolve_expression_in_function(
    file: &syn::File,
    source: &str,
    fn_name: &str,
    expr_pattern: &str,
    occurrence: usize,
) -> Result<(usize, usize), AstRewriteError> {
    // 1. Parse the pattern as a syn::Expr
    let pattern: syn::Expr =
        syn::parse_str(expr_pattern).map_err(|e| AstRewriteError::PatternParseError {
            pattern: expr_pattern.to_string(),
            error: e.to_string(),
        })?;

    // 2. Find the function in the file
    let found = find_function_in_ast(file, fn_name)?;

    // 3. Walk the function body with a visitor that matches expressions
    struct ExprFinder<'a> {
        pattern: &'a syn::Expr,
        matches: Vec<proc_macro2::Span>,
    }

    impl<'ast, 'a> Visit<'ast> for ExprFinder<'a> {
        fn visit_expr(&mut self, expr: &'ast syn::Expr) {
            if exprs_structurally_equal(expr, self.pattern) {
                self.matches.push(expr_full_span(expr));
            }
            syn::visit::visit_expr(self, expr);
        }
    }

    let mut finder = ExprFinder { pattern: &pattern, matches: Vec::new() };
    syn::visit::visit_block(&mut finder, found.block);

    // 4. Select the requested occurrence
    let span =
        finder.matches.get(occurrence).ok_or_else(|| AstRewriteError::ExpressionNotFound {
            pattern: expr_pattern.to_string(),
            occurrence,
            total_matches: finder.matches.len(),
        })?;

    let start = span_start_byte_offset(source, *span)?;
    let end = span_end_byte_offset(source, *span)?;
    Ok((start, end))
}

/// Get a span covering the full expression (from first to last token).
fn expr_full_span(expr: &syn::Expr) -> proc_macro2::Span {
    use quote::ToTokens;
    let tokens: Vec<proc_macro2::TokenTree> = expr.to_token_stream().into_iter().collect();
    match (tokens.first(), tokens.last()) {
        (Some(first), Some(last)) => first.span().join(last.span()).unwrap_or(first.span()),
        (Some(only), None) | (None, Some(only)) => only.span(),
        (None, None) => proc_macro2::Span::call_site(),
    }
}

/// Compare two expressions for structural equality, ignoring spans.
///
/// Uses the `quote::ToTokens` representation normalized to strings.
fn exprs_structurally_equal(a: &syn::Expr, b: &syn::Expr) -> bool {
    use quote::ToTokens;
    let a_tokens = a.to_token_stream().to_string();
    let b_tokens = b.to_token_stream().to_string();
    a_tokens == b_tokens
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::RewriteKind;

    // --- LineOffsets ---

    #[test]
    fn test_line_offsets_single_line() {
        let table = LineOffsets::new("hello world");
        assert_eq!(table.byte_offset(1, 0).unwrap(), 0);
        assert_eq!(table.byte_offset(1, 5).unwrap(), 5);
    }

    #[test]
    fn test_line_offsets_multi_line() {
        let source = "line1\nline2\nline3\n";
        let table = LineOffsets::new(source);
        assert_eq!(table.byte_offset(1, 0).unwrap(), 0); // start of line1
        assert_eq!(table.byte_offset(2, 0).unwrap(), 6); // start of line2
        assert_eq!(table.byte_offset(3, 0).unwrap(), 12); // start of line3
        assert_eq!(table.byte_offset(2, 3).unwrap(), 9); // "e" in "line2"
    }

    #[test]
    fn test_line_offsets_no_trailing_newline() {
        let source = "abc\ndef";
        let table = LineOffsets::new(source);
        assert_eq!(table.byte_offset(1, 0).unwrap(), 0);
        assert_eq!(table.byte_offset(2, 0).unwrap(), 4);
        assert_eq!(table.byte_offset(2, 2).unwrap(), 6);
    }

    #[test]
    fn native_clause_scanner_handles_multiline_match_and_primed_outputs() {
        let source = "fn choose(x: i32) -> i32\n    requires x >= 0\n    ensures match result {\n        value => value >= x && x' >= x,\n    }\n{ x }\n";
        let clauses = native_contract_clause_spans(source).unwrap();
        assert_eq!(clauses.len(), 2);
        assert_eq!(clauses[0].kind, ContractClauseKind::Requires);
        assert_eq!(&source[clauses[0].expression.clone()], "x >= 0");
        assert_eq!(clauses[1].kind, ContractClauseKind::Ensures);
        assert_eq!(
            &source[clauses[1].expression.clone()],
            "match result {\n        value => value >= x && x' >= x,\n    }"
        );
        let masked = mask_native_contract_clauses(source).unwrap();
        syn::parse_file(&masked).expect("mask preserves the surrounding Rust program");
        assert_eq!(masked.len(), source.len());
    }

    #[test]
    fn native_clause_scanner_ignores_comments_and_strings() {
        let source = "const NOTE: &str = \"fn fake() requires false { }\";\n// fn nope() ensures false {}\nfn real() {}\n";
        assert!(native_contract_clause_spans(source).unwrap().is_empty());
    }

    #[test]
    fn native_clause_scanner_rejects_empty_predicates() {
        let source = "fn bad() requires { }";
        assert!(matches!(
            native_contract_clause_spans(source),
            Err(AstRewriteError::MalformedNativeContract { .. })
        ));
    }

    #[test]
    fn line_offsets_convert_utf8_character_columns_to_bytes() {
        let source = "πé fn target() {}";
        let table = LineOffsets::new(source);
        assert_eq!(table.byte_offset(1, 0).unwrap(), 0);
        assert_eq!(table.byte_offset(1, 2).unwrap(), "πé".len());
        assert!(table.byte_offset(1, 10_000).is_err());
        assert!(table.byte_offset(0, 0).is_err());
        assert!(table.byte_offset(2, 0).is_err());
    }

    // --- Indentation detection ---

    #[test]
    fn test_detect_indent_unit_4_spaces() {
        let source = "fn foo() {\n    let x = 1;\n    let y = 2;\n}\n";
        assert_eq!(detect_indent_unit(source), "    ");
    }

    #[test]
    fn test_detect_indent_unit_2_spaces() {
        let source = "fn foo() {\n  let x = 1;\n  let y = 2;\n}\n";
        assert_eq!(detect_indent_unit(source), "  ");
    }

    #[test]
    fn test_detect_indent_unit_tabs() {
        let source = "fn foo() {\n\tlet x = 1;\n\tlet y = 2;\n}\n";
        assert_eq!(detect_indent_unit(source), "\t");
    }

    #[test]
    fn test_detect_indent_unit_default_no_indentation() {
        let source = "fn foo() {}\n";
        assert_eq!(detect_indent_unit(source), "    ");
    }

    // --- Indentation computation ---

    #[test]
    fn test_compute_indentation_attribute() {
        let source = "    fn foo() {}\n";
        let indent = compute_indentation(
            source,
            4, // offset of "fn"
            &RewriteKind::InsertAttribute { attribute: "#[requires(\"x > 0\")]".into() },
        );
        assert_eq!(indent, "    ");
    }

    #[test]
    fn test_compute_indentation_assertion() {
        let source = "fn foo() {\n    let x = 1;\n}\n";
        let indent = compute_indentation(
            source,
            11, // offset of "    let"
            &RewriteKind::InsertAssertion { assertion: "assert!(x > 0);".into() },
        );
        assert_eq!(indent, "        ");
    }

    // --- Function attribute resolution ---

    #[test]
    fn test_resolve_function_attribute_simple() {
        let source = "fn foo() {}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_attribute(&file, source, "foo", 0).unwrap();
        assert_eq!(offset, 0);
    }

    #[test]
    fn test_resolve_function_attribute_pub() {
        let source = "pub fn foo() {}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_attribute(&file, source, "foo", 0).unwrap();
        assert_eq!(offset, 0);
    }

    #[test]
    fn test_resolve_function_attribute_with_existing_attrs() {
        let source = "#[inline]\nfn foo() {}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_attribute(&file, source, "foo", 0).unwrap();
        assert_eq!(offset, 0);
    }

    #[test]
    fn test_resolve_function_attribute_indented() {
        let source = "impl Foo {\n    fn bar() {}\n}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_attribute(&file, source, "bar", 0).unwrap();
        // Should point to start of the line containing "    fn bar"
        assert_eq!(&source[offset..offset + 6], "    fn");
    }

    #[test]
    fn test_resolve_function_attribute_not_found() {
        let source = "fn foo() {}\n";
        let file = syn::parse_file(source).unwrap();
        let result = resolve_function_attribute(&file, source, "bar", 0);
        assert!(matches!(result, Err(AstRewriteError::FunctionNotFound { .. })));
    }

    #[test]
    fn test_duplicate_short_function_name_is_ambiguous() {
        let source = "fn process() {}\n\nfn process() {}\n";
        let file = syn::parse_file(source).unwrap();
        assert!(matches!(
            resolve_function_attribute(&file, source, "process", 0),
            Err(AstRewriteError::AmbiguousFunction { matches: 2, .. })
        ));
    }

    #[test]
    fn nested_module_requires_and_accepts_qualified_identity() {
        let source = "mod left { fn run() {} } mod right { fn run() {} }";
        let file = syn::parse_file(source).unwrap();
        assert!(matches!(
            resolve_function_attribute(&file, source, "run", 0),
            Err(AstRewriteError::AmbiguousFunction { matches: 2, .. })
        ));
        let offset = resolve_function_attribute(&file, source, "right::run", 0).unwrap();
        assert!(source[offset..].starts_with("fn run"));
    }

    #[test]
    fn trait_default_and_two_impls_require_exact_owner_identity() {
        let source = r#"
trait Runner { fn run(&self) {} }
struct A; struct B;
impl Runner for A { fn run(&self) {} }
impl Runner for B { fn run(&self) {} }
"#;
        let file = syn::parse_file(source).unwrap();
        assert!(matches!(
            resolve_function_attribute(&file, source, "run", 0),
            Err(AstRewriteError::AmbiguousFunction { matches: 3, .. })
        ));
        let offset = resolve_function_attribute(&file, source, "<B as Runner>::run", 0).unwrap();
        assert!(source[offset..].starts_with("fn run"));
    }

    // --- Function body start resolution ---

    #[test]
    fn test_resolve_function_body_start() {
        let source = "fn foo() {\n    let x = 1;\n}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_body_start(&file, source, "foo", 0).unwrap();
        // Should be right after the `{`
        assert_eq!(&source[offset - 1..offset], "{");
    }

    #[test]
    fn test_resolve_function_body_start_empty() {
        let source = "fn foo() {}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_body_start(&file, source, "foo", 0).unwrap();
        assert_eq!(&source[offset - 1..offset], "{");
        assert_eq!(&source[offset..offset + 1], "}");
    }

    // --- Function body before resolution ---

    #[test]
    fn test_resolve_function_body_before_first_stmt() {
        let source = "fn foo() {\n    let x = 1;\n    let y = 2;\n}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_body_before(&file, source, "foo", 0, 0).unwrap();
        // Should point to start of line with "    let x"
        assert!(source[offset..].starts_with("    let x"));
    }

    #[test]
    fn test_resolve_function_body_before_second_stmt() {
        let source = "fn foo() {\n    let x = 1;\n    let y = 2;\n}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_body_before(&file, source, "foo", 1, 0).unwrap();
        assert!(source[offset..].starts_with("    let y"));
    }

    #[test]
    fn test_resolve_function_body_before_out_of_range() {
        let source = "fn foo() {\n    let x = 1;\n}\n";
        let file = syn::parse_file(source).unwrap();
        let result = resolve_function_body_before(&file, source, "foo", 5, 0);
        assert!(matches!(result, Err(AstRewriteError::StatementIndexOutOfRange { .. })));
    }

    // --- Expression resolution ---

    #[test]
    fn test_resolve_expression_single_match() {
        let source = "fn foo(a: u64, b: u64) -> u64 {\n    a + b\n}\n";
        let file = syn::parse_file(source).unwrap();
        let (start, end) =
            resolve_expression_in_function(&file, source, "foo", "a + b", 0).unwrap();
        assert_eq!(&source[start..end], "a + b");
    }

    #[test]
    fn expression_resolution_carries_exact_spaced_commented_slice() {
        let source = "fn foo(a: u64, b: u64) -> u64 { a /* keep */  +   b }";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::ExpressionInFunction {
                fn_name: "foo".into(),
                expr_pattern: "a+b".into(),
                occurrence: 0,
            },
            kind: RewriteKind::ReplaceExpression {
                old_text: "a+b".into(),
                new_text: "a.checked_add(b).unwrap()".into(),
            },
            function_name: "foo".into(),
            rationale: "test".into(),
        };
        let resolved = resolve_target(source, &rewrite).unwrap();
        assert!(matches!(
            &resolved.kind,
            RewriteKind::ReplaceExpression { old_text, .. }
                if old_text == "a /* keep */  +   b"
        ));
        let rewritten = crate::RewriteEngine::new().apply_rewrite(source, &resolved).unwrap();
        assert!(rewritten.contains("a.checked_add(b).unwrap()"));
    }

    #[test]
    fn comments_and_strings_never_count_as_expression_targets() {
        let source = r#"fn foo(a: i32, b: i32) -> i32 {
    // a + b
    let _text = "a + b";
    a - b
}"#;
        let file = syn::parse_file(source).unwrap();
        assert!(matches!(
            resolve_expression_in_function(&file, source, "foo", "a + b", 0),
            Err(AstRewriteError::ExpressionNotFound { total_matches: 0, .. })
        ));
    }

    #[test]
    fn const_generic_braces_and_unicode_prefix_keep_byte_offsets_exact() {
        let source = "const π: &str = \"{not a body}\";\nfn foo<const N: usize>(a: usize) -> usize { a + N }\n";
        let file = syn::parse_file(source).unwrap();
        let (start, end) =
            resolve_expression_in_function(&file, source, "foo", "a + N", 0).unwrap();
        assert_eq!(&source[start..end], "a + N");
    }

    #[test]
    fn same_line_unicode_prefix_keeps_ast_spans_on_utf8_boundaries() {
        let source = "const π: usize = 3; fn foo(a: usize) -> usize { a + π }";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_attribute(&file, source, "foo", 0).unwrap();
        assert_eq!(&source[offset..offset + "fn foo".len()], "fn foo");
        let (start, end) =
            resolve_expression_in_function(&file, source, "foo", "a + π", 0).unwrap();
        assert_eq!(&source[start..end], "a + π");
        assert!(source.is_char_boundary(start));
        assert!(source.is_char_boundary(end));
    }

    #[test]
    fn contract_environment_retypes_bool_parameter_and_return() {
        let source = "fn gate(flag: bool, n: u8) -> bool { flag && n > 0 }";
        let sorts = contract_sort_environment(source, "gate").unwrap();
        assert_eq!(sorts.get("flag"), Some(&trust_types::Sort::Bool));
        assert_eq!(sorts.get("n"), Some(&trust_types::Sort::Int));
        assert_eq!(sorts.get("_0"), Some(&trust_types::Sort::Bool));
    }

    #[test]
    fn contract_environment_rejects_return_place_name_collisions() {
        for name in ["_0", "result"] {
            let source = format!("fn bad({name}: i32) -> i32 {{ {name} }}");
            assert!(matches!(
                contract_sort_environment(&source, "bad"),
                Err(AstRewriteError::ReservedContractBinding { name: rejected, .. })
                    if rejected == name
            ));
        }
    }

    #[test]
    fn test_resolve_expression_not_found() {
        let source = "fn foo(a: u64) -> u64 {\n    a * 2\n}\n";
        let file = syn::parse_file(source).unwrap();
        let result = resolve_expression_in_function(&file, source, "foo", "a + b", 0);
        assert!(matches!(
            result,
            Err(AstRewriteError::ExpressionNotFound { total_matches: 0, .. })
        ));
    }

    #[test]
    fn test_resolve_expression_pattern_parse_error() {
        let source = "fn foo() { 1 }\n";
        let file = syn::parse_file(source).unwrap();
        let result = resolve_expression_in_function(&file, source, "foo", "{{invalid", 0);
        assert!(matches!(result, Err(AstRewriteError::PatternParseError { .. })));
    }

    // --- Structural equality ---

    #[test]
    fn test_exprs_structurally_equal_same() {
        let a: syn::Expr = syn::parse_str("a + b").unwrap();
        let b: syn::Expr = syn::parse_str("a + b").unwrap();
        assert!(exprs_structurally_equal(&a, &b));
    }

    #[test]
    fn test_exprs_structurally_equal_different() {
        let a: syn::Expr = syn::parse_str("a + b").unwrap();
        let b: syn::Expr = syn::parse_str("a * b").unwrap();
        assert!(!exprs_structurally_equal(&a, &b));
    }

    #[test]
    fn test_exprs_structurally_equal_parens_differ() {
        let a: syn::Expr = syn::parse_str("a + b").unwrap();
        let b: syn::Expr = syn::parse_str("(a + b)").unwrap();
        assert!(!exprs_structurally_equal(&a, &b));
    }

    // --- End-to-end: resolve_target ---

    #[test]
    fn test_resolve_target_function_attribute() {
        let source = "fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::FunctionAttribute {
                fn_name: "get_midpoint".into(),
                occurrence: 0,
            },
            kind: RewriteKind::InsertAttribute {
                attribute: "#[requires(\"a + b < u64::MAX\")]".into(),
            },
            function_name: "get_midpoint".into(),
            rationale: "prevent overflow".into(),
        };

        let resolved = resolve_target(source, &rewrite).unwrap();
        assert_eq!(resolved.offset, 0);
        assert_eq!(resolved.function_name, "get_midpoint");
    }

    #[test]
    fn test_resolve_target_expression_replacement() {
        let source = "fn foo(a: u64, b: u64) -> u64 {\n    a + b\n}\n";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::ExpressionInFunction {
                fn_name: "foo".into(),
                expr_pattern: "a + b".into(),
                occurrence: 0,
            },
            kind: RewriteKind::ReplaceExpression {
                old_text: "a + b".into(),
                new_text: "a.checked_add(b).unwrap()".into(),
            },
            function_name: "foo".into(),
            rationale: "safe arithmetic".into(),
        };

        let resolved = resolve_target(source, &rewrite).unwrap();
        // The offset should point to where "a + b" begins in the source
        assert_eq!(&source[resolved.offset..resolved.offset + 5], "a + b");
    }

    #[test]
    fn test_resolve_target_body_start() {
        let source = "fn foo() {\n    let x = 1;\n}\n";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::FunctionBodyStart { fn_name: "foo".into(), occurrence: 0 },
            kind: RewriteKind::InsertAssertion { assertion: "assert!(true);".into() },
            function_name: "foo".into(),
            rationale: "test".into(),
        };

        let resolved = resolve_target(source, &rewrite).unwrap();
        assert_eq!(&source[resolved.offset - 1..resolved.offset], "{");
    }

    #[test]
    fn test_resolve_target_unparseable_source() {
        let source = "fn foo( {{ broken";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::FunctionAttribute { fn_name: "foo".into(), occurrence: 0 },
            kind: RewriteKind::InsertAttribute { attribute: "#[requires(\"x\")]".into() },
            function_name: "foo".into(),
            rationale: "test".into(),
        };

        assert!(matches!(
            resolve_target(source, &rewrite),
            Err(AstRewriteError::SourceParseError(_))
        ));
    }

    // --- End-to-end: resolve + apply ---

    #[test]
    fn test_end_to_end_insert_attribute() {
        let source = "fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::FunctionAttribute {
                fn_name: "get_midpoint".into(),
                occurrence: 0,
            },
            kind: RewriteKind::InsertAttribute {
                attribute: "#[requires(\"a + b < u64::MAX\")]".into(),
            },
            function_name: "get_midpoint".into(),
            rationale: "prevent overflow".into(),
        };

        let source_rewrite = resolve_target(source, &rewrite).unwrap();
        let engine = crate::RewriteEngine::new();
        let result = engine.apply_rewrite(source, &source_rewrite).unwrap();

        assert!(result.starts_with("#[requires(\"a + b < u64::MAX\")]"));
        assert!(result.contains("fn get_midpoint"));
        // Verify the result still parses
        syn::parse_file(&result).expect("rewritten source should parse");
    }

    #[test]
    fn test_end_to_end_insert_attribute_in_impl() {
        let source = "impl Calculator {\n    fn add(&self, a: u64, b: u64) -> u64 {\n        a + b\n    }\n}\n";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::FunctionAttribute { fn_name: "add".into(), occurrence: 0 },
            kind: RewriteKind::InsertAttribute {
                attribute: "    #[requires(\"a + b < u64::MAX\")]".into(),
            },
            function_name: "add".into(),
            rationale: "prevent overflow".into(),
        };

        let source_rewrite = resolve_target(source, &rewrite).unwrap();
        let engine = crate::RewriteEngine::new();
        let result = engine.apply_rewrite(source, &source_rewrite).unwrap();

        assert!(result.contains("#[requires(\"a + b < u64::MAX\")]"));
        assert!(result.contains("fn add"));
    }
}
