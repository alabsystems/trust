use trust_types::assumption::{
    is_safety_comment_assumption_row, strict_policy_publishes_assumption_row,
};

use super::*;

/// The forbidden full-verifier classifier substrings (targo
/// `is_full_verifier_text`); no field of an assumption row may contain one.
const FULL_VERIFIER_MARKERS: &[&str] = &[
    "native full verifier",
    "full verifier",
    "full-verifier",
    "trust-verify-full",
    "fullverification::",
];

/// clippy's scan over `src`, whose FIRST line is the enclosing item's first line
/// (never read) and whose LAST line is the line the block starts on.
fn scan(src: &str) -> Option<usize> {
    let starts: Vec<usize> =
        std::iter::once(0).chain(src.match_indices('\n').map(|(at, _)| at + 1)).collect();
    // `lines()[body_line + 1..=unsafe_line]`, the last start being the block's line.
    let block_line = src.matches('\n').count();
    text_safety_comment(src, &starts[1..=block_line])
}

/// The offset of the `occurrence`-th `needle` in `src`.
fn at(src: &str, needle: &str, occurrence: usize) -> usize {
    src.match_indices(needle).nth(occurrence).map(|(at, _)| at).expect("needle")
}

#[test]
fn a_line_comment_directly_above_the_block_declares_it() {
    let src = "fn f() {\n    // SAFETY: `g` has no precondition.\n    unsafe { g() }";
    assert_eq!(scan(src), Some(at(src, "SAFETY:", 0)));
    // Any case, as clippy reads it.
    let src = "fn f() {\n    // Safety: `g` has no precondition.\n    unsafe { g() }";
    assert_eq!(scan(src), Some(at(src, "Safety:", 0)));
}

#[test]
fn the_aterm_shape_a_two_line_comment_above_the_let_declares_the_block() {
    let src = "fn dispatch_link() {\n    let run = || {\n        // SAFETY: this early startup \
               route takes the launcher's unclaimed lanes\n        // once, before bridge \
               threads.\n        let (verb, push) = unsafe { adopt() }?;";
    assert_eq!(scan(src), Some(at(src, "SAFETY:", 0)));
}

#[test]
fn blank_and_attribute_lines_between_the_comment_and_the_block_are_skipped() {
    let src = "fn f() {\n    // SAFETY: x\n\n    #[allow(unused_unsafe)]\n    unsafe { g() }";
    assert_eq!(scan(src), Some(at(src, "SAFETY:", 0)));
}

#[test]
fn a_comment_separated_from_the_block_by_code_declares_nothing() {
    let src = "fn f() {\n    // SAFETY: x\n    let y = 1;\n    unsafe { g(y) }";
    assert_eq!(scan(src), None);
    // A run of plain `//` lines ends at code; a SAFETY line above the code is
    // another statement's.
    let src = "fn f() {\n    // SAFETY: x\n    h();\n    // plain note\n    unsafe { g() }";
    assert_eq!(scan(src), None);
}

#[test]
fn a_comment_without_the_safety_marker_declares_nothing() {
    for src in [
        "fn f() {\n    // this is fine\n    unsafe { g() }",
        "fn f() {\n    // SAFETY without the colon\n    unsafe { g() }",
        "fn f() {\n    unsafe { g() }",
        // The enclosing item's own first line is never read.
        "fn f() { // SAFETY: x\n    unsafe { g() }",
    ] {
        assert_eq!(scan(src), None, "{src:?}");
    }
}

#[test]
fn a_safety_line_inside_a_doc_code_fence_declares_nothing() {
    let src = "fn f() {\n    /// ```\n    /// // SAFETY: example\n    /// ```\n    unsafe { g() }";
    assert_eq!(scan(src), None);
}

#[test]
fn a_trailing_comment_after_code_on_the_line_above_declares_the_block() {
    let src = "fn f() {\n    let p = // SAFETY: x\n        unsafe { g() };";
    assert_eq!(scan(src), Some(at(src, "SAFETY:", 0)));
    // Only whitespace may sit between the marker and `SAFETY:`.
    let src = "fn f() {\n    let p = // note, SAFETY: x\n        unsafe { g() };";
    assert_eq!(scan(src), None);
}

#[test]
fn a_block_comment_needs_only_whitespace_after_it() {
    let src = "fn f() {\n    /* SAFETY: x\n       continued */\n    unsafe { g() }";
    assert_eq!(scan(src), Some(at(src, "SAFETY:", 0)));
    let src = "fn f() {\n    /* SAFETY: x */\n    let y = 1;\n    unsafe { g(y) }";
    assert_eq!(scan(src), None);
    let src = "fn f() {\n    /* a note */\n    unsafe { g() }";
    assert_eq!(scan(src), None);
}

#[test]
fn an_inner_comment_right_after_the_brace_declares_the_block() {
    let snippet = "unsafe { // SAFETY: x\n    g() }";
    assert_eq!(inner_safety_comment(snippet), Some(at(snippet, "SAFETY:", 0)));
    let snippet = "unsafe {/* safety: x */ g() }";
    assert_eq!(inner_safety_comment(snippet), Some(at(snippet, "safety:", 0)));
    for snippet in ["unsafe { g(); // SAFETY: x\n }", "unsafe { g() }", "unsafe { /* note */ g() }"]
    {
        assert_eq!(inner_safety_comment(snippet), None, "{snippet:?}");
    }
}

#[test]
fn attribute_lines_are_recognised_as_clippy_recognises_them() {
    assert!(is_attribute("#[allow(unused)]\n"));
    assert!(is_attribute("#![allow(unused)]"));
    assert!(!is_attribute("#[allow(unused)] let x = 1;"));
    assert!(!is_attribute("// #[allow]"));
}

#[test]
fn an_operation_belongs_to_its_innermost_block_and_a_tie_decides_nothing() {
    rustc_span::create_default_session_globals_then(|| {
        let span = |lo: u32, hi: u32| Span::with_root_ctxt(BytePos(lo), BytePos(hi));
        let comment = Some(span(5, 5));
        // A declared block holding an undocumented (or compiler-generated) one.
        let sites = vec![
            UnsafeBlockSite { span: span(10, 100), comment },
            UnsafeBlockSite { span: span(20, 40), comment: None },
        ];
        assert!(innermost_site(&sites, span(25, 30)).is_some_and(|site| site.comment.is_none()));
        assert!(innermost_site(&sites, span(50, 60)).is_some_and(|site| site.comment.is_some()));
        assert!(innermost_site(&sites, span(5, 6)).is_none());
        // Order does not matter.
        let reversed: Vec<UnsafeBlockSite> = sites
            .iter()
            .rev()
            .map(|site| UnsafeBlockSite { span: site.span, comment: site.comment })
            .collect();
        assert!(innermost_site(&reversed, span(25, 30)).is_some_and(|site| site.comment.is_none()));
        // Two blocks of one extent: nothing is decided.
        let tied = vec![
            UnsafeBlockSite { span: span(10, 100), comment },
            UnsafeBlockSite { span: span(10, 100), comment: None },
        ];
        assert!(innermost_site(&tied, span(50, 60)).is_none());
    });
}

fn position(file: &str, line: u32, col: u32) -> SourceSpan {
    SourceSpan { file: file.into(), line_start: line, col_start: col, line_end: line, col_end: col }
}

fn row() -> TransportObligationResult {
    safety_comment_row("c::f", position("lib.rs", 4, 4), &position("lib.rs", 3, 7))
}

#[test]
fn the_charge_row_is_the_admitted_assumption_shape() {
    let row = row();
    assert_eq!(row.kind, "assumption:safety-comment");
    assert_eq!(row.outcome, Outcome::Skipped);
    assert_eq!(row.solver, SAFETY_COMMENT_ROW_SOLVER);
    assert!(row.typed_kind.is_none() && !row.design_mandate);
    assert!(row.native_trust_ir.is_none() && row.proof_evidence.is_none());
    assert!(is_safety_comment_assumption_row(&row.kind, &row.solver));
    assert!(strict_policy_publishes_assumption_row(&row.kind, &row.solver, &row.description));
    // The block is the row's location; the comment's position is named in the text.
    assert_eq!(row.location, Some(position("lib.rs", 4, 4)));
    assert!(row.description.starts_with("unverified assumption: "), "{}", row.description);
    assert!(row.description.contains("lib.rs:4:5"), "{}", row.description);
    assert!(row.description.contains("comment at lib.rs:3:8"), "{}", row.description);
    assert!(row.description.contains("`c::f`"), "{}", row.description);
    // Never a missing-comment claim, never an `[unsafe` demand the refutation pass
    // would select, never full-verifier text.
    for text in [&row.kind, &row.description, row.reason.as_ref().unwrap(), &row.solver] {
        let lower = text.to_ascii_lowercase();
        assert!(!lower.contains("missing safety comment"), "{text}");
        assert!(!text.contains("[unsafe"), "{text}");
        for marker in FULL_VERIFIER_MARKERS {
            assert!(!lower.contains(marker), "`{text}` contains `{marker}`");
        }
    }
}

fn charge() -> SafetyCommentCharge {
    SafetyCommentCharge { rows: vec![row()], blocks: Vec::new() }
}

#[test]
fn the_charge_is_appended_and_a_stale_row_of_its_kind_is_stripped() {
    let mut other = row();
    other.kind = "panic".to_string();
    other.outcome = Outcome::Proved;
    let mut stale = row();
    stale.description = "unverified assumption: forged".to_string();
    // No charge and nothing to strip: unchanged.
    assert!(rows_with_safety_comment_assumptions(std::slice::from_ref(&other), None).is_none());
    // No charge: a stale row of the kind is stripped.
    let rows = rows_with_safety_comment_assumptions(&[other.clone(), stale.clone()], None).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].kind, "panic");
    // A charge replaces it.
    let rows = rows_with_safety_comment_assumptions(&[other, stale], Some(&charge())).unwrap();
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[1].description, row().description);
}

#[test]
fn a_charged_zero_obligation_body_publishes_no_proved_no_obligations_row() {
    let mut no_obligations = row();
    no_obligations.kind = "no_obligations".to_string();
    no_obligations.outcome = Outcome::Proved;
    let charged = zero_obligation_rows(vec![no_obligations.clone()], Some(&charge()));
    assert_eq!(charged.len(), 1);
    assert_eq!(charged[0].kind, "assumption:safety-comment");
    // Uncharged: byte-identical.
    let uncharged = zero_obligation_rows(vec![no_obligations], None);
    assert_eq!(uncharged.len(), 1);
    assert_eq!(uncharged[0].kind, "no_obligations");
}
