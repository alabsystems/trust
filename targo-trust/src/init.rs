// targo trust init: scaffold verification annotations for a crate.
//
// Scans Rust source files for public functions and generates inert, commented
// native signature-clause candidates. Candidates require human review and
// editing before they are moved into the function signature.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::input_limits::{MAX_SAVED_PROOF_REPORT_BYTES, read_bounded_utf8_file};
use crate::source_analysis::{self, ParsedFunction};

const NATIVE_SURFACE_GUIDANCE: &str = "native contract surface: move reviewed `requires` / `ensures` clauses into the Rust function signature immediately before its body `{`";
const NO_SHIM_GUIDANCE: &str = "no contract crate, import, macro, or attribute is required; compatibility attributes are reserved for upstream corpus ingestion";
const SHARED_IR_GUIDANCE: &str = "Rust clauses and `clean { ... }` proof items share the program namespace and lower to Trust-IR";
const REVIEW_GUIDANCE: &str = "review required: generated clauses are inert comments; validate and edit every expression before moving it into the signature";
const REVIEW_REQUIRED_SOURCE_COMMENT: &str = "TRUST REVIEW REQUIRED: inert native signature-clause candidates below; move reviewed clauses into the function signature before `{`.";
const LEGACY_REVIEW_REQUIRED_SOURCE_COMMENT: &str = "TRUST REVIEW REQUIRED: inert candidates below; validate and edit every expression before uncommenting.";
const REVIEWED_PRECONDITION_PLACEHOLDER: &str =
    "REPLACE_WITH_REVIEWED_PRECONDITION /* human review required */";
const REVIEWED_POSTCONDITION_PLACEHOLDER: &str =
    "REPLACE_WITH_REVIEWED_POSTCONDITION /* human review required */";

// ---------------------------------------------------------------------------
// Annotation scaffolding
// ---------------------------------------------------------------------------

/// A scaffolded annotation for a single function.
#[derive(Debug, Clone)]
pub(crate) struct ScaffoldedAnnotation {
    pub(crate) function_name: String,
    pub(crate) file: PathBuf,
    pub(crate) line: usize,
    pub(crate) requires: Vec<String>,
    pub(crate) ensures: Vec<String>,
}

/// Summary of the init scaffolding operation.
#[derive(Debug, Clone)]
pub(crate) struct InitSummary {
    pub(crate) files_scanned: usize,
    pub(crate) functions_found: usize,
    pub(crate) functions_annotated: usize,
    pub(crate) functions_already_annotated: usize,
    pub(crate) annotations: Vec<ScaffoldedAnnotation>,
}

/// Generate scaffold annotations for all public functions in a crate.
pub(crate) fn scaffold_crate(crate_root: &Path) -> InitSummary {
    let files = source_analysis::find_source_files(crate_root);
    let mut all_functions = Vec::new();

    for file in &files {
        all_functions.extend(source_analysis::extract_functions(file));
    }

    scaffold_from_functions(&all_functions, files.len())
}

/// Generate scaffold annotations for functions in a single file.
pub(crate) fn scaffold_file(file: &Path) -> InitSummary {
    let functions = source_analysis::extract_functions(file);
    scaffold_from_functions(&functions, 1)
}

fn scaffold_from_functions(functions: &[ParsedFunction], files_scanned: usize) -> InitSummary {
    let mut annotations = Vec::new();
    let mut already_annotated = 0usize;
    let mut source_by_file: BTreeMap<PathBuf, Option<String>> = BTreeMap::new();

    for func in functions {
        // Skip private functions -- only scaffold public API
        if !func.is_public {
            continue;
        }

        // Cache each file once: large modules can contain many public
        // functions, and init needs the source both for review-marker detection
        // and signature heuristics.
        let source = source_by_file
            .entry(func.file.clone())
            .or_insert_with(|| {
                read_bounded_utf8_file(&func.file, MAX_SAVED_PROOF_REPORT_BYTES).ok()
            })
            .as_deref()
            .unwrap_or("");

        // Skip functions that already have active annotations or an inert
        // candidate block awaiting review. This keeps repeated `init --inline`
        // runs idempotent without treating the commented candidates as proof.
        if func.has_requires || func.has_ensures || has_review_pending_candidates(func, source) {
            already_annotated += 1;
            continue;
        }

        let scaffold = generate_annotations_from_source(func, source);
        if !scaffold.requires.is_empty() || !scaffold.ensures.is_empty() {
            annotations.push(scaffold);
        }
    }

    InitSummary {
        files_scanned,
        functions_found: functions.len(),
        functions_annotated: annotations.len(),
        functions_already_annotated: already_annotated,
        annotations,
    }
}

fn has_review_pending_candidates(func: &ParsedFunction, source: &str) -> bool {
    let lines: Vec<&str> = source.lines().collect();
    let mut index = func.line.saturating_sub(1).min(lines.len());

    while index > 0 {
        index -= 1;
        let line = lines[index].trim();
        if let Some(comment) = line.strip_prefix("// ") {
            if comment == REVIEW_REQUIRED_SOURCE_COMMENT
                || comment == LEGACY_REVIEW_REQUIRED_SOURCE_COMMENT
            {
                return true;
            }
            continue;
        }
        break;
    }

    false
}

/// Generate heuristic annotations for a function based on its signature.
#[cfg(test)]
fn generate_annotations(func: &ParsedFunction) -> ScaffoldedAnnotation {
    let source =
        read_bounded_utf8_file(&func.file, MAX_SAVED_PROOF_REPORT_BYTES).unwrap_or_default();
    generate_annotations_from_source(func, &source)
}

fn generate_annotations_from_source(func: &ParsedFunction, source: &str) -> ScaffoldedAnnotation {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();

    // Analyze parameters for preconditions
    for param in &func.params {
        if param == "self" {
            continue;
        }
        // We only have param names from the lightweight parser, but we can
        // still generate useful scaffolds based on naming conventions.
    }

    // Analyze parameter types from the raw signature for division-like patterns
    // The source_analysis parser gives us param names; for type-based heuristics
    // we re-read the function line.
    let fn_line = source.lines().nth(func.line.saturating_sub(1)).unwrap_or("");
    generate_param_preconditions(fn_line, &func.params, &mut requires);

    // Analyze return type for postconditions
    if let Some(ref ret) = func.return_type {
        generate_return_postconditions(ret, &mut ensures);
    }

    // Unsafe functions get a safety precondition scaffold
    if func.is_unsafe {
        requires.push(
            "REPLACE_WITH_REVIEWED_PRECONDITION /* SAFETY: document invariants */".to_string(),
        );
    }

    // If nothing was generated, add a placeholder
    if requires.is_empty() && ensures.is_empty() {
        requires.push(REVIEWED_PRECONDITION_PLACEHOLDER.to_string());
        ensures.push(REVIEWED_POSTCONDITION_PLACEHOLDER.to_string());
    }

    ScaffoldedAnnotation {
        function_name: func.name.clone(),
        file: func.file.clone(),
        line: func.line,
        requires,
        ensures,
    }
}

/// Generate preconditions from parameter types in the function signature line.
fn generate_param_preconditions(fn_line: &str, param_names: &[String], requires: &mut Vec<String>) {
    // Extract the full parameter list from the function line
    let params_str = extract_params_with_types(fn_line);

    for (name, ty) in &params_str {
        if name == "self" {
            continue;
        }

        // Division-related: parameters that could be divisors
        if is_numeric_type(ty) && is_likely_divisor(name) {
            requires.push(format!("{name} != 0"));
        }

        // Slice/array parameters: non-empty requirement is common
        if ty.contains("&[") || ty.contains("&mut [") {
            requires.push(format!("{name}.len() > 0"));
        }

        // Raw pointer parameters
        if ty.contains("*const") || ty.contains("*mut") {
            requires.push(format!("!{name}.is_null()"));
        }

        // Index-like numeric parameters with slices
        if is_index_param(name) && is_unsigned_type(ty) {
            // Look for a corresponding slice parameter
            for (other_name, other_ty) in &params_str {
                if (other_ty.contains("&[") || other_ty.contains("Vec<")) && other_name != name {
                    requires.push(format!("{name} < {other_name}.len()"));
                    break;
                }
            }
        }
    }

    // If param_names mentions names not in the parsed types, this is fine --
    // the heuristics just won't fire for those.
    let _ = param_names;
}

/// Generate postconditions from the return type.
fn generate_return_postconditions(ret_type: &str, ensures: &mut Vec<String>) {
    let ret = ret_type.trim();

    if ret.starts_with("Option<") {
        ensures.push(
            "REPLACE_WITH_REVIEWED_POSTCONDITION /* specify when result.is_some() */".to_string(),
        );
    } else if ret.starts_with("Result<") {
        ensures.push(
            "REPLACE_WITH_REVIEWED_POSTCONDITION /* specify when result.is_ok() */".to_string(),
        );
    } else if ret == "bool" {
        ensures.push(
            "REPLACE_WITH_REVIEWED_POSTCONDITION /* specify boolean postcondition */".to_string(),
        );
    } else if is_numeric_type(ret) {
        ensures.push("REPLACE_WITH_REVIEWED_POSTCONDITION /* specify numeric range */".to_string());
    }
}

/// Extract parameter (name, type) pairs from a function signature line.
fn extract_params_with_types(fn_line: &str) -> Vec<(String, String)> {
    let paren_start = match fn_line.find('(') {
        Some(i) => i,
        None => return Vec::new(),
    };
    // Find matching close paren, handling nested parens/generics
    let mut depth = 0i32;
    let mut paren_end = paren_start;
    for (i, ch) in fn_line[paren_start..].char_indices() {
        match ch {
            '(' | '<' => depth += 1,
            ')' | '>' => {
                depth -= 1;
                if depth == 0 && ch == ')' {
                    paren_end = paren_start + i;
                    break;
                }
            }
            _ => {}
        }
    }

    let params_str = &fn_line[paren_start + 1..paren_end];
    if params_str.trim().is_empty() {
        return Vec::new();
    }

    // Split on commas, but only at depth 0 (not inside generics)
    let mut result = Vec::new();
    let mut current = String::new();
    let mut depth = 0i32;

    for ch in params_str.chars() {
        match ch {
            '<' | '(' => {
                depth += 1;
                current.push(ch);
            }
            '>' | ')' => {
                depth -= 1;
                current.push(ch);
            }
            ',' if depth == 0 => {
                if let Some(pair) = parse_param_pair(&current) {
                    result.push(pair);
                }
                current.clear();
            }
            _ => current.push(ch),
        }
    }
    if let Some(pair) = parse_param_pair(&current) {
        result.push(pair);
    }

    result
}

/// Parse "name: Type" into (name, type) pair.
fn parse_param_pair(param: &str) -> Option<(String, String)> {
    let param = param.trim();
    if param == "self" || param == "&self" || param == "&mut self" || param == "mut self" {
        return Some(("self".to_string(), "Self".to_string()));
    }
    let colon_pos = param.find(':')?;
    let name = param[..colon_pos].trim().to_string();
    let ty = param[colon_pos + 1..].trim().to_string();
    if name.is_empty() { None } else { Some((name, ty)) }
}

fn is_numeric_type(ty: &str) -> bool {
    let ty = ty.trim();
    matches!(
        ty,
        "i8" | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "f32"
            | "f64"
    )
}

fn is_unsigned_type(ty: &str) -> bool {
    let ty = ty.trim();
    matches!(ty, "u8" | "u16" | "u32" | "u64" | "u128" | "usize")
}

fn is_likely_divisor(name: &str) -> bool {
    let lower = name.to_lowercase();
    lower == "divisor"
        || lower == "denominator"
        || lower == "denom"
        || lower == "div"
        || lower == "b" // common in `fn divide(a, b)`
        || lower == "rhs"
        || lower == "modulus"
        || lower == "mod_val"
}

fn is_index_param(name: &str) -> bool {
    let lower = name.to_lowercase();
    lower == "index"
        || lower == "idx"
        || lower == "pos"
        || lower == "position"
        || lower == "offset"
        || lower == "i"
}

// ---------------------------------------------------------------------------
// `[trust]` table generation
// ---------------------------------------------------------------------------

/// The commented `[trust]` table `targo trust init` appends to a manifest that
/// does not yet declare one. Every key is shown at its default so a reader can
/// see the whole policy surface without consulting the reference.
pub(crate) fn generate_trust_table() -> String {
    r#"
# Trust verification policy for this project.
# Generated by `targo trust init`.
[trust]
# Enable/disable verification
enabled = true

# Verification level: L0 (basic), L1 (standard), L2 (maximal default)
level = "L2"

# Solver timeout in milliseconds
timeout_ms = 5000

# Whole-function verification budget in milliseconds. This bounds all proof
# work for one function, not just one solver call.
function_budget_ms = 120000

# Optional codegen backend override: "llvm" (P9 compatibility default) or
# "trust-cg" (native Trust-IR backend for its currently supported targets)
# codegen_backend = "llvm"

# Hardened boundary verification is on by default with unix_hardened.
# Set hardened = false only for compatibility triage, or choose a profile label.
# hardened = true
# trust_profile = "unix_hardened"

# A design document or captured conversation describing what this project is
# meant to do. It guides AI repair; it never decides whether a proof holds.
# intent = "docs/intent.md"

# Functions protected from automated rewrite-loop edits.
# This does not filter ordinary check/build verification today.
skip_functions = []
"#
    .to_string()
}

/// Append the starter `[trust]` table to a project manifest.
///
/// Appending, rather than rewriting the document, keeps every comment and key
/// ordering the author chose. A `[trust]` table is a top-level table, so it can
/// only go at the end of the file: anywhere earlier would silently capture the
/// keys of whatever table follows it.
pub(crate) fn append_trust_table(manifest_path: &Path) -> std::io::Result<()> {
    use std::io::Write as _;

    let existing = std::fs::read_to_string(manifest_path)?;
    let mut file = std::fs::OpenOptions::new().append(true).open(manifest_path)?;
    if !existing.ends_with('\n') {
        file.write_all(b"\n")?;
    }
    file.write_all(generate_trust_table().as_bytes())
}

fn format_contract_candidate(indent: &str, kind: &str, expr: &str) -> String {
    format!("{indent}// {kind} {expr}")
}

fn format_annotation_lines(ann: &ScaffoldedAnnotation, indent: &str) -> Vec<String> {
    let mut lines = Vec::with_capacity(1 + ann.requires.len() + ann.ensures.len());
    lines.push(format!("{indent}// {REVIEW_REQUIRED_SOURCE_COMMENT}"));
    for requires in &ann.requires {
        lines.push(format_contract_candidate(indent, "requires", requires));
    }
    for ensures in &ann.ensures {
        lines.push(format_contract_candidate(indent, "ensures", ensures));
    }
    lines
}

fn init_surface_guidance_lines() -> [&'static str; 4] {
    [REVIEW_GUIDANCE, NATIVE_SURFACE_GUIDANCE, NO_SHIM_GUIDANCE, SHARED_IR_GUIDANCE]
}

// ---------------------------------------------------------------------------
// Inline annotation writing
// ---------------------------------------------------------------------------

/// Write inert, commented contract candidates into the source files.
///
/// For each annotation, inserts commented native `requires` and `ensures`
/// candidates plus a mandatory-review notice immediately before the function
/// declaration. Processes files in reverse line order to preserve line numbers.
pub(crate) fn write_inline_annotations(
    annotations: &[ScaffoldedAnnotation],
) -> Result<usize, String> {
    // Group annotations by file
    let mut by_file: BTreeMap<PathBuf, Vec<&ScaffoldedAnnotation>> = BTreeMap::new();
    for ann in annotations {
        by_file.entry(ann.file.clone()).or_default().push(ann);
    }

    let mut total_written = 0usize;

    for (file, mut anns) in by_file {
        let content = read_bounded_utf8_file(&file, MAX_SAVED_PROOF_REPORT_BYTES)
            .map_err(|e| format!("failed to read {}: {e}", file.display()))?;

        let mut lines: Vec<String> = content.lines().map(String::from).collect();

        // Sort by line number descending so insertions don't shift earlier lines
        anns.sort_by_key(|ann| std::cmp::Reverse(ann.line));

        for ann in &anns {
            // Insert before the function line (0-indexed: line - 1)
            let insert_idx = ann.line.saturating_sub(1);
            if insert_idx > lines.len() {
                continue;
            }

            // Detect indentation from the function line
            let indent = if insert_idx < lines.len() {
                let fn_line = &lines[insert_idx];
                let trimmed_len = fn_line.trim_start().len();
                &fn_line[..fn_line.len() - trimmed_len]
            } else {
                ""
            };

            let new_lines = format_annotation_lines(ann, indent);

            for (offset, line) in new_lines.into_iter().enumerate() {
                lines.insert(insert_idx + offset, line);
            }
            total_written += 1;
        }

        // Write back
        let output = lines.join("\n");
        // Preserve trailing newline if original had one
        let output =
            if content.ends_with('\n') && !output.ends_with('\n') { output + "\n" } else { output };
        trust_backprop::file_io::write_source(&file, &output)
            .map_err(|e| format!("failed to write {} atomically: {e}", file.display()))?;
    }

    Ok(total_written)
}

// ---------------------------------------------------------------------------
// Display formatting
// ---------------------------------------------------------------------------

/// Render scaffolded annotations to stdout (non-inline mode).
pub(crate) fn render_annotations_stdout(annotations: &[ScaffoldedAnnotation]) {
    let mut current_file: Option<&Path> = None;

    for ann in annotations {
        if current_file != Some(&ann.file) {
            if current_file.is_some() {
                println!();
            }
            println!("// {}", ann.file.display());
            current_file = Some(&ann.file);
        }
        println!();
        for line in format_annotation_lines(ann, "") {
            println!("{line}");
        }
        println!("// ^ for: {} (line {})", ann.function_name, ann.line);
    }
}

/// Render the init summary to stderr.
pub(crate) fn render_summary(summary: &InitSummary) {
    eprintln!();
    eprintln!("=== targo trust init ===");
    eprintln!("  Files scanned:          {}", summary.files_scanned);
    eprintln!("  Functions found:        {}", summary.functions_found);
    eprintln!("  Annotated/review-pending: {}", summary.functions_already_annotated);
    eprintln!("  Annotations generated:  {}", summary.functions_annotated);
    for line in init_surface_guidance_lines() {
        eprintln!("  {line}");
    }
    eprintln!("========================");
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_annotations_division() {
        let func = ParsedFunction {
            name: "divide".into(),
            file: PathBuf::from("test.rs"),
            line: 1,
            is_public: true,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: Some("i32".into()),
            params: vec!["a".into(), "b".into()],
            typed_params: vec![],
        };
        // Write a temp file so generate_annotations can read the line
        let dir = std::env::temp_dir().join("trust_init_test_div");
        let _ = std::fs::create_dir_all(&dir);
        let file = dir.join("test.rs");
        std::fs::write(&file, "pub fn divide(a: i32, b: i32) -> i32 { a / b }\n").unwrap();

        let func = ParsedFunction { file: file.clone(), ..func };
        let ann = generate_annotations(&func);
        assert_eq!(ann.function_name, "divide");
        assert!(
            ann.requires.iter().any(|r| r.contains("b != 0")),
            "expected b != 0 precondition, got: {:?}",
            ann.requires
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_generate_annotations_slice_param() {
        let dir = std::env::temp_dir().join("trust_init_test_slice");
        let _ = std::fs::create_dir_all(&dir);
        let file = dir.join("test.rs");
        std::fs::write(&file, "pub fn search(data: &[i32], target: i32) -> Option<usize> {}\n")
            .unwrap();

        let func = ParsedFunction {
            name: "search".into(),
            file: file.clone(),
            line: 1,
            is_public: true,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: Some("Option<usize>".into()),
            params: vec!["data".into(), "target".into()],
            typed_params: vec![],
        };
        let ann = generate_annotations(&func);
        assert!(
            ann.requires.iter().any(|r| r.contains("data.len() > 0")),
            "expected slice non-empty precondition, got: {:?}",
            ann.requires
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_generate_annotations_result_return() {
        let dir = std::env::temp_dir().join("trust_init_test_result");
        let _ = std::fs::create_dir_all(&dir);
        let file = dir.join("test.rs");
        std::fs::write(&file, "pub fn parse(input: &str) -> Result<i32, String> {}\n").unwrap();

        let func = ParsedFunction {
            name: "parse".into(),
            file: file.clone(),
            line: 1,
            is_public: true,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: Some("Result<i32, String>".into()),
            params: vec!["input".into()],
            typed_params: vec![],
        };
        let ann = generate_annotations(&func);
        assert!(
            ann.ensures.iter().any(|e| e.contains("result.is_ok()")),
            "expected Result postcondition, got: {:?}",
            ann.ensures
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_generate_annotations_unsafe_fn() {
        let dir = std::env::temp_dir().join("trust_init_test_unsafe");
        let _ = std::fs::create_dir_all(&dir);
        let file = dir.join("test.rs");
        std::fs::write(&file, "pub unsafe fn deref(ptr: *const u8) -> u8 { *ptr }\n").unwrap();

        let func = ParsedFunction {
            name: "deref".into(),
            file: file.clone(),
            line: 1,
            is_public: true,
            is_unsafe: true,
            has_requires: false,
            has_ensures: false,
            return_type: Some("u8".into()),
            params: vec!["ptr".into()],
            typed_params: vec![],
        };
        let ann = generate_annotations(&func);
        assert!(
            ann.requires.iter().any(|r| r.contains("is_null")),
            "expected null check precondition for pointer, got: {:?}",
            ann.requires
        );
        assert!(
            ann.requires.iter().any(|r| r.contains("SAFETY")),
            "expected SAFETY comment for unsafe fn, got: {:?}",
            ann.requires
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_scaffold_skips_already_annotated() {
        let functions = vec![
            ParsedFunction {
                name: "annotated".into(),
                file: PathBuf::from("test.rs"),
                line: 1,
                is_public: true,
                is_unsafe: false,
                has_requires: true,
                has_ensures: false,
                return_type: None,
                params: vec![],
                typed_params: vec![],
            },
            ParsedFunction {
                name: "unannotated".into(),
                file: PathBuf::from("test.rs"),
                line: 5,
                is_public: true,
                is_unsafe: false,
                has_requires: false,
                has_ensures: false,
                return_type: None,
                params: vec![],
                typed_params: vec![],
            },
        ];
        let summary = scaffold_from_functions(&functions, 1);
        assert_eq!(summary.functions_already_annotated, 1);
        // unannotated will get placeholder annotations
        assert!(summary.functions_annotated > 0);
    }

    #[test]
    fn test_scaffold_skips_private_functions() {
        let functions = vec![ParsedFunction {
            name: "helper".into(),
            file: PathBuf::from("test.rs"),
            line: 1,
            is_public: false,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: None,
            params: vec![],
            typed_params: vec![],
        }];
        let summary = scaffold_from_functions(&functions, 1);
        assert_eq!(summary.functions_annotated, 0);
    }

    #[test]
    fn test_generate_trust_table() {
        let toml = generate_trust_table();
        assert!(toml.contains("[trust]"));
        assert!(toml.contains("enabled = true"));
        assert!(toml.contains("level = \"L2\""));
        assert!(toml.contains("timeout_ms = 5000"));
        assert!(toml.contains("function_budget_ms = 120000"));
        assert!(toml.contains("Hardened boundary verification is on by default"));
        assert!(toml.contains("skip_functions = []"));
        assert!(
            !toml.contains("verify_functions"),
            "init must not generate the removed, never-wired verification scope key"
        );

        let table = toml.split_once("[trust]").expect("table header").1;
        let parsed: toml::Value = table.parse().expect("the generated table must parse");
        assert_eq!(parsed.get("level").and_then(toml::Value::as_str), Some("L2"));
    }

    #[test]
    fn appending_the_table_preserves_the_existing_manifest() {
        let dir = std::env::temp_dir().join("trust-init-append-table");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create fixture dir");
        let manifest = dir.join("Cargo.toml");
        std::fs::write(&manifest, "[package]\nname = \"demo\"\nversion = \"0.1.0\"")
            .expect("write manifest");

        append_trust_table(&manifest).expect("append table");

        let content = std::fs::read_to_string(&manifest).expect("read manifest");
        let parsed: toml::Value = content.parse().expect("the manifest must still parse");
        assert_eq!(
            parsed.get("package").and_then(|p| p.get("name")).and_then(toml::Value::as_str),
            Some("demo")
        );
        assert_eq!(
            parsed.get("trust").and_then(|t| t.get("level")).and_then(toml::Value::as_str),
            Some("L2")
        );
    }

    #[test]
    fn test_write_inline_annotations() {
        let dir = std::env::temp_dir().join("trust_init_test_inline");
        let _ = std::fs::create_dir_all(&dir);
        let file = dir.join("lib.rs");
        std::fs::write(&file, "pub fn add(a: i32, b: i32) -> i32 {\n    a + b\n}\n").unwrap();

        let annotations = vec![ScaffoldedAnnotation {
            function_name: "add".into(),
            file: file.clone(),
            line: 1,
            requires: vec!["true".into()],
            ensures: vec!["result == a + b".into()],
        }];

        let written = write_inline_annotations(&annotations).unwrap();
        assert_eq!(written, 1);

        let content = std::fs::read_to_string(&file).unwrap();
        assert!(
            content.starts_with(
                "// TRUST REVIEW REQUIRED: inert native signature-clause candidates below; move reviewed clauses into the function signature before `{`.\n\
                 // requires true\n\
                 // ensures result == a + b\n"
            ),
            "expected inert, review-required candidates, got:\n{content}"
        );
        assert!(
            !content.lines().any(|line| {
                let line = line.trim_start();
                line.starts_with("requires ") || line.starts_with("ensures ")
            }),
            "init must never write an active generated contract:\n{content}"
        );
        // Function should still be there
        assert!(content.contains("pub fn add(a: i32, b: i32) -> i32"));

        let second = scaffold_file(&file);
        assert_eq!(second.functions_already_annotated, 1);
        assert!(second.annotations.is_empty(), "re-running init must not duplicate candidates");

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_extract_params_with_types_simple() {
        let line = "pub fn divide(a: i32, b: i32) -> i32 {";
        let params = extract_params_with_types(line);
        assert_eq!(params.len(), 2);
        assert_eq!(params[0], ("a".into(), "i32".into()));
        assert_eq!(params[1], ("b".into(), "i32".into()));
    }

    #[test]
    fn test_extract_params_with_types_generic() {
        let line = "pub fn search(data: &[i32], target: i32) -> Option<usize> {";
        let params = extract_params_with_types(line);
        assert_eq!(params.len(), 2);
        assert_eq!(params[0].0, "data");
        assert!(params[0].1.contains("&[i32]"));
    }

    #[test]
    fn test_extract_params_with_types_self() {
        let line = "pub fn method(&self, x: i32) -> bool {";
        let params = extract_params_with_types(line);
        assert_eq!(params.len(), 2);
        assert_eq!(params[0], ("self".into(), "Self".into()));
        assert_eq!(params[1], ("x".into(), "i32".into()));
    }

    #[test]
    fn test_extract_params_with_types_empty() {
        let line = "fn empty() {}";
        let params = extract_params_with_types(line);
        assert!(params.is_empty());
    }

    #[test]
    fn test_is_likely_divisor() {
        assert!(is_likely_divisor("b"));
        assert!(is_likely_divisor("divisor"));
        assert!(is_likely_divisor("denom"));
        assert!(is_likely_divisor("rhs"));
        assert!(!is_likely_divisor("a"));
        assert!(!is_likely_divisor("value"));
    }

    #[test]
    fn test_is_index_param() {
        assert!(is_index_param("index"));
        assert!(is_index_param("idx"));
        assert!(is_index_param("pos"));
        assert!(is_index_param("i"));
        assert!(!is_index_param("value"));
        assert!(!is_index_param("name"));
    }

    #[test]
    fn test_scaffold_crate_with_temp_dir() {
        let dir = std::env::temp_dir().join("trust_init_test_crate");
        let src_dir = dir.join("src");
        let _ = std::fs::create_dir_all(&src_dir);
        std::fs::write(
            src_dir.join("lib.rs"),
            r#"
pub fn add(x: i32, y: i32) -> i32 { x + y }

pub fn already_annotated(n: u32) -> u32
    requires n > 0
{ n }

fn private_helper() {}
"#,
        )
        .unwrap();

        let summary = scaffold_crate(&dir);
        assert_eq!(summary.files_scanned, 1);
        assert_eq!(summary.functions_found, 3);
        assert_eq!(summary.functions_already_annotated, 1);
        // `add` is public and unannotated -> gets scaffolded
        // `already_annotated` is skipped
        // `private_helper` is skipped (private)
        assert_eq!(summary.functions_annotated, 1);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_format_annotation_lines_use_native_signature_clauses() {
        let ann = ScaffoldedAnnotation {
            function_name: "add".into(),
            file: PathBuf::from("lib.rs"),
            line: 1,
            requires: vec!["x > 0".into()],
            ensures: vec!["result >= x".into()],
        };

        let lines = format_annotation_lines(&ann, "    ");
        assert_eq!(
            lines[0],
            "    // TRUST REVIEW REQUIRED: inert native signature-clause candidates below; move reviewed clauses into the function signature before `{`."
        );
        assert_eq!(lines[1], "    // requires x > 0");
        assert_eq!(lines[2], "    // ensures result >= x");
        assert!(lines.iter().all(|line| {
            let line = line.trim_start();
            !line.starts_with("requires ") && !line.starts_with("ensures ")
        }));
    }

    #[test]
    fn test_init_surface_guidance_uses_native_shared_ir_contracts() {
        let guidance = init_surface_guidance_lines().join("\n");
        assert!(guidance.contains("review required"));
        assert!(guidance.contains("inert comments"));
        assert!(guidance.contains("function signature"));
        assert!(guidance.contains("no contract crate"));
        assert!(guidance.contains("compatibility attributes"));
        assert!(guidance.contains("clean { ... }"));
        assert!(guidance.contains("Trust-IR"));
        assert!(!guidance.contains("trust-spec"));
        assert!(!guidance.contains("#[trust::requires"));
    }

    #[test]
    fn test_fallback_placeholders_are_not_vacuous_true_contracts() {
        let func = ParsedFunction {
            name: "unconstrained".into(),
            file: PathBuf::from("missing.rs"),
            line: 1,
            is_public: true,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: None,
            params: vec![],
            typed_params: vec![],
        };

        let ann = generate_annotations(&func);
        assert_eq!(ann.requires, vec![REVIEWED_PRECONDITION_PLACEHOLDER]);
        assert_eq!(ann.ensures, vec![REVIEWED_POSTCONDITION_PLACEHOLDER]);
        assert!(!ann.requires.iter().chain(&ann.ensures).any(|candidate| candidate == "true"));
    }

    #[test]
    fn test_index_bounds_annotation() {
        let dir = std::env::temp_dir().join("trust_init_test_idx");
        let _ = std::fs::create_dir_all(&dir);
        let file = dir.join("test.rs");
        std::fs::write(&file, "pub fn get(data: &[i32], index: usize) -> i32 { data[index] }\n")
            .unwrap();

        let func = ParsedFunction {
            name: "get".into(),
            file: file.clone(),
            line: 1,
            is_public: true,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: Some("i32".into()),
            params: vec!["data".into(), "index".into()],
            typed_params: vec![],
        };
        let ann = generate_annotations(&func);
        assert!(
            ann.requires.iter().any(|r| r.contains("index < data.len()")),
            "expected index bounds precondition, got: {:?}",
            ann.requires
        );

        let _ = std::fs::remove_dir_all(&dir);
    }
}
