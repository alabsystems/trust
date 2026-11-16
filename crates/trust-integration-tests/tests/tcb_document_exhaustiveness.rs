// trust-integration-tests/tests/tcb_document_exhaustiveness.rs: docs/TCB.md guard
//
// The trust boundary of a default build is decided by
// `ResultProofAuthority` + `trust_disposition_for_authority` in the compiler's
// verification pass. Prose describing that boundary rots the moment a variant
// is added or a disposition is retuned, and a stale TCB document is worse than
// none: it is a published claim about which verdicts a kernel checked.
//
// The compiler already refuses to build when a variant has no disposition arm.
// This test is the other half — it refuses to pass when the DOCUMENT has no row
// for it, or names a status/strength the code does not return. It parses the
// source rather than linking the compiler crate, which is private to bootstrap;
// every parse failure is a hard failure, so a refactor that moves this surface
// forces a look at the document instead of silently disarming the guard.
//
// Beyond status and strength, it pins the two consequences the table is FOR.
// `Independent static proof` is the predicate that decides whether a row may
// serve as someone else's premise, and check elision is the only thing a
// passing verdict is allowed to DELETE from the compiled program. Both were
// prose-only until they were pinned here; a table whose consequences are
// unchecked documents a trust boundary it does not hold anyone to.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

const AUTHORITY_ENUM: &str = "enum ResultProofAuthority {";
const DISPOSITION_FN: &str = "fn trust_disposition_for_authority(";
const GRADE_FN: &str = "fn trust_grade_for_authority(";
const STATIC_PROOF_FN: &str = "fn is_static_proof_for(";
const UNCONDITIONAL_FN: &str = "fn is_unconditional_static_proof_for(";
const KERNEL_EVIDENCE_FN: &str = "fn kernel_evidence_for(";
const ELIDE_FN: &str = "fn elide_kernel_certified_checks";
const CALCULUS_DISPOSITION_FN: &str = "fn calculus_row_disposition(";
const VERIFY_PASS: &str = "compiler/rustc_mir_transform/src/trust_verify.rs";
const TCB_DOC: &str = "docs/TCB.md";
const GATE_MANIFEST: &str = "tests/run_trust_comprehensive_harness.sh";
const THIS_TEST_TARGET: &str = "tcb_document_exhaustiveness";

/// Live (undated) documents that CITE the proof-authority class total:
/// `README.md` and `docs/TCB.md`.
///
/// Fixing the guarded document silently leaves every unguarded citation of it
/// stale, and a reader who follows the cross-reference lands on the wrong
/// number. So every live document that states the total is listed here, and a
/// document that states it must be added.
///
/// DATED documents are deliberately absent: they are snapshots of what was true
/// when written, so guarding them would force a false edit. Add a row here only
/// for a document that claims CURRENT status.
const TOTAL_CITING_DOCS: &[&str] = &[
    "README.md",
    "docs/TCB.md",
];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("crates/<pkg> is two levels below the repo root")
        .to_path_buf()
}

fn read(relative: &str) -> String {
    let path = repo_root().join(relative);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()))
}

/// Drop `//` line comments so brace counting is not thrown off by prose. Every
/// region this file scans was checked to contain no string literal holding a
/// `//`, so a comment marker in one of them is always a comment. A future
/// region must be checked the same way before it is added below.
fn strip_line_comments(src: &str) -> String {
    src.lines()
        .map(|line| match line.find("//") {
            Some(at) => &line[..at],
            None => line,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The brace-balanced block that starts at the first `{` at or after `from`.
fn balanced_block(src: &str, from: usize) -> String {
    let open = src[from..].find('{').expect("expected an opening brace") + from;
    let mut depth = 0usize;
    for (offset, ch) in src[open..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return src[open + 1..open + offset].to_string();
                }
            }
            _ => {}
        }
    }
    panic!("unterminated block");
}

/// The brace-balanced body of the one item introduced by `needle`.
///
/// A second occurrence is a hard failure rather than a silent first-match: two
/// definitions of a predicate this document quotes means the document is
/// quoting one of them and the compiler may be using the other.
fn item_body(pass_src: &str, needle: &str) -> String {
    let src = strip_line_comments(pass_src);
    let occurrences = src.matches(needle).count();
    assert_eq!(
        occurrences, 1,
        "expected exactly one `{needle}` in {VERIFY_PASS}, found {occurrences}; this test can no \
         longer tell which definition {TCB_DOC} describes"
    );
    let at = src.find(needle).expect("occurrence counted above");
    balanced_block(&src, at + needle.len())
}

/// Variant names of `ResultProofAuthority`, in declaration order.
fn enum_variants(pass_src: &str) -> Vec<String> {
    let src = strip_line_comments(pass_src);
    let at = src.find(AUTHORITY_ENUM).unwrap_or_else(|| panic!("{AUTHORITY_ENUM} not found"));
    let body = balanced_block(&src, at);

    let mut variants = Vec::new();
    let mut depth = 0usize;
    for line in body.lines() {
        let trimmed = line.trim();
        if depth == 0
            && trimmed.starts_with(|c: char| c.is_ascii_uppercase())
            && let Some(end) = trimmed.find(['{', '(', ','])
        {
            let name = trimmed[..end].trim();
            if !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                variants.push(name.to_string());
            }
        }
        depth = depth + line.matches('{').count() - line.matches('}').count();
    }
    assert!(!variants.is_empty(), "parsed no ResultProofAuthority variants");
    variants
}

/// The `ResultProofAuthority` variants `region` names, whether it reaches them
/// through `Self::` or the full path. Names that are not declared variants are
/// dropped: an associated function called on `Self` is not a verdict class, and
/// a variant the code invents but the enum does not declare cannot compile.
fn variants_named(region: &str, variants: &[String]) -> BTreeSet<String> {
    let mut found = BTreeSet::new();
    for prefix in ["Self::", "ResultProofAuthority::"] {
        for (offset, _) in region.match_indices(prefix) {
            let rest = &region[offset + prefix.len()..];
            let end =
                rest.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(rest.len());
            let name = &rest[..end];
            if variants.iter().any(|variant| variant == name) {
                found.insert(name.to_string());
            }
        }
    }
    found
}

/// `(variants matched, arm body)` for each arm of the `match self` in `body`.
///
/// Arms are split on a `=>` and a `,` at bracket depth zero, so a struct-shaped
/// pattern's inner commas and a block-bodied arm both stay inside their arm.
fn match_self_arms(body: &str, variants: &[String]) -> Vec<(BTreeSet<String>, String)> {
    let at = body.find("match self {").expect("`match self {` block");
    let src = balanced_block(body, at);

    let mut arms = Vec::new();
    let mut depth = 0i32;
    let mut cursor = 0usize;
    let mut pattern: Option<String> = None;
    let mut index = 0usize;
    while index < src.len() {
        let rest = &src[index..];
        let ch = rest.chars().next().expect("non-empty remainder");
        match ch {
            '{' | '(' | '[' => depth += 1,
            '}' | ')' | ']' => depth -= 1,
            _ => {}
        }
        if depth == 0 && pattern.is_none() && rest.starts_with("=>") {
            pattern = Some(src[cursor..index].to_string());
            index += 2;
            cursor = index;
            continue;
        }
        if depth == 0 && ch == ',' && pattern.is_some() {
            let matched = variants_named(&pattern.take().expect("checked above"), variants);
            arms.push((matched, src[cursor..index].to_string()));
            index += ch.len_utf8();
            cursor = index;
            continue;
        }
        index += ch.len_utf8();
    }
    if let Some(trailing) = pattern {
        arms.push((variants_named(&trailing, variants), src[cursor..].to_string()));
    }
    assert!(!arms.is_empty(), "parsed no arms from a `match self` block");
    arms
}

/// `(variant, TrustStatus, TrustProofStrength expression)` per match arm of
/// `trust_disposition_for_authority`, in arm order.
fn disposition_arms(pass_src: &str) -> Vec<(String, String, String)> {
    let function = item_body(pass_src, DISPOSITION_FN);
    const MATCH: &str = "match authority {";
    assert_eq!(function.matches(MATCH).count(), 1, "one authority match required");
    let start = function.find(MATCH).expect("count checked");
    let preamble: String = function[..start].chars().filter(|c| !c.is_whitespace()).collect();
    // The production preamble can only decline a missing/mismatched authority.
    // An empty preamble is also disposition-preserving (and used by the parser
    // controls). Do not ignore a new favorable early return or delegation.
    assert!(
        preamble.is_empty()
            || preamble
                == "letauthority=authority?;if!authority.matches_row(index,vc,binding)||!authority.matches_compiler_result(result){returnNone;}",
        "unrecognized disposition preamble"
    );
    let open = start + MATCH.len() - 1;
    let body = balanced_block(&function, open);
    assert!(
        function[open + body.len() + 2..].trim().is_empty(),
        "authority match has a trailing transformation"
    );

    let mut arms = Vec::new();
    let mut rest = body.trim();
    while !rest.is_empty() {
        let arrow = rest.find("=>").expect("disposition arm arrow");
        // A grouped pattern names several variants before ONE arm body. Only
        // recognize unguarded variant patterns, not arbitrary Rust expressions
        // containing another variant name or a later arm's favorable return.
        // Consume EVERY arm: scanning only named occurrences would silently
        // ignore a preceding/intervening wildcard that actually wins the match.
        let mut variants = Vec::new();
        for alternative in rest[..arrow].split('|') {
            let compact: String = alternative.chars().filter(|c| !c.is_whitespace()).collect();
            let pattern =
                compact.strip_prefix("ResultProofAuthority::").expect("qualified alternative");
            let end = pattern
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(pattern.len());
            assert!(end > 0, "empty disposition variant");
            let variant = &pattern[..end];
            assert!(
                matches!(&pattern[end..], "" | "{..}"),
                "unsupported disposition pattern for {variant}: {pattern}"
            );
            variants.push(variant.to_string());
        }
        assert!(rest[arrow + 2..].trim_start().starts_with('{'), "expected block arm");
        let open = arrow + 2 + rest[arrow + 2..].find('{').expect("block checked");
        let arm = balanced_block(rest, open);
        let following = rest[open + arm.len() + 2..].trim_start();
        assert!(
            following.is_empty()
                || following.starts_with(',')
                || following.starts_with("ResultProofAuthority::"),
            "disposition arm has a trailing transformation for {variants:?}"
        );
        let compact: String = arm.chars().filter(|c| !c.is_whitespace()).collect();
        // Each accepted arm has exactly one literal disposition. A conditional,
        // delegated or missing return is a hard parse failure, not an inferred
        // grade. A refactor beyond this grammar needs an explicit guard update.
        //
        // The one delegation admitted (VF5): the calculus row's arm reads the
        // owner's E4.7 ruling through `calculus_row_disposition`, whose body is
        // pinned below; it reads as the literal that ruling's shipped value
        // selects, and only for `CalculusRowProved`.
        let calculus = calculus_disposition_literal(pass_src, &compact, &variants);
        let payload = calculus
            .as_deref()
            .or_else(|| {
                compact.strip_prefix("Some((TrustStatus::").and_then(|s| s.strip_suffix("))"))
            })
            .unwrap_or_else(|| panic!("{variants:?} has no single literal disposition"));
        let (status, tail) = payload.split_once(',').expect("disposition tuple");
        let strength = tail.strip_prefix("TrustProofStrength::").expect("qualified strength");
        for name in [status, strength] {
            assert!(
                !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'),
                "non-literal disposition for {variants:?}"
            );
        }
        arms.extend(
            variants.into_iter().map(|variant| (variant, status.to_string(), strength.to_string())),
        );
        rest = following.strip_prefix(',').unwrap_or(following).trim_start();
    }
    assert!(!arms.is_empty(), "parsed no disposition arms");
    arms
}

/// The calculus arm's delegation (`Some(calculus_row_disposition(E4_7))`, for
/// `CalculusRowProved` alone) read as the literal disposition the shipped E4.7
/// ruling selects: `Status,TrustProofStrength::Strength` (the shape the literal
/// arms are parsed in). `None` for every other arm body. The delegate's body
/// must be exactly the two-way literal below, so the ruling's value is the only
/// thing that chooses.
fn calculus_disposition_literal(
    pass_src: &str,
    compact: &str,
    variants: &[String],
) -> Option<String> {
    const ARM: &str = "Some(calculus_row_disposition(trust_types::authority_grade::E4_7_CALCULUS_ROWS_CERTIFIED))";
    // rustfmt may leave a trailing comma after the one argument.
    if compact.replace(",)", ")") != ARM {
        return None;
    }
    assert_eq!(variants, ["CalculusRowProved"], "only the calculus row reads the E4.7 ruling");
    let delegate: String = item_body(pass_src, CALCULUS_DISPOSITION_FN)
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    assert_eq!(
        delegate,
        "ife4_7{(TrustStatus::Certified,TrustProofStrength::Constructive)}else{(TrustStatus::Trusted,TrustProofStrength::Constructive)}",
        "calculus_row_disposition is not the two-way E4.7 literal"
    );
    let status = if trust_types::authority_grade::E4_7_CALCULUS_ROWS_CERTIFIED {
        "Certified"
    } else {
        "Trusted"
    };
    Some(format!("{status},TrustProofStrength::Constructive"))
}

#[test]
fn disposition_parser_preserves_each_grouped_variant() {
    let source = "fn trust_disposition_for_authority() { match authority {
        ResultProofAuthority::First { .. } | ResultProofAuthority::Second { .. } => {
            Some((TrustStatus::Trusted, TrustProofStrength::Inductive))
        }
        ResultProofAuthority::Third { .. } => {
            Some((TrustStatus::Certified, TrustProofStrength::Constructive))
        }
    }}";
    assert_eq!(
        disposition_arms(source),
        vec![
            ("First".into(), "Trusted".into(), "Inductive".into()),
            ("Second".into(), "Trusted".into(), "Inductive".into()),
            ("Third".into(), "Certified".into(), "Constructive".into()),
        ]
    );
}

#[test]
fn disposition_parser_refuses_ambiguous_or_borrowed_returns() {
    let returned = "Some((TrustStatus::Trusted, TrustProofStrength::Inductive))";
    let mut accepted = Vec::new();
    for arms in [
        format!(
            "ResultProofAuthority::First {{ .. }} => {{ None }}
            ResultProofAuthority::Second {{ .. }} => {{ {returned} }}"
        ),
        format!(
            "ResultProofAuthority::First {{ .. }} => {{
            let other = ResultProofAuthority::Second {{}}; {returned} }}"
        ),
        format!("ResultProofAuthority::First {{ .. }} if guard() => {{ {returned} }}"),
        format!("ResultProofAuthority::First {{ .. }} | Second {{ .. }} => {{ {returned} }}"),
        format!(
            "ResultProofAuthority::First {{ .. }} => {{
            if guard() {{ {returned} }} else {{ None }} }}"
        ),
        format!(
            "ResultProofAuthority::First {{ .. }} => {{ {returned} }}
            .map(|_| (TrustStatus::Certified, TrustProofStrength::Constructive)),"
        ),
        format!(
            "ResultProofAuthority::First {{ .. }} => {{ {returned} }}
            .filter(|_| false),"
        ),
        format!("_ => {{ None }}, ResultProofAuthority::First {{ .. }} => {{ {returned} }}"),
        format!(
            "ResultProofAuthority::First {{ .. }} => {{ {returned} }}
            _ => {{ None }}, ResultProofAuthority::Second {{ .. }} => {{ {returned} }}"
        ),
        "ResultProofAuthority::First { .. } => { delegated_disposition() }".into(),
    ] {
        let source =
            format!("fn trust_disposition_for_authority() {{ match authority {{ {arms} }} }}");
        if std::panic::catch_unwind(|| disposition_arms(&source)).is_ok() {
            accepted.push(source);
        }
    }
    let source = format!(
        "fn trust_disposition_for_authority() {{ match authority {{
        ResultProofAuthority::First {{ .. }} => {{ {returned} }}
    }}.map(|_| (TrustStatus::Certified, TrustProofStrength::Constructive)) }}"
    );
    if std::panic::catch_unwind(|| disposition_arms(&source)).is_ok() {
        accepted.push(source);
    }
    let source = format!(
        "fn trust_disposition_for_authority() {{
        if guard() {{ return Some((TrustStatus::Certified, TrustProofStrength::Constructive)); }}
        match authority {{ ResultProofAuthority::First {{ .. }} => {{ {returned} }} }} }}"
    );
    if std::panic::catch_unwind(|| disposition_arms(&source)).is_ok() {
        accepted.push(source);
    }
    assert!(accepted.is_empty(), "ambiguous dispositions accepted: {accepted:#?}");
}

/// The variants `trust_disposition_for_authority` reports as `Certified`.
fn certified_variants(pass_src: &str) -> BTreeSet<String> {
    disposition_arms(pass_src)
        .into_iter()
        .filter(|(_, status, _)| status == "Certified")
        .map(|(variant, ..)| variant)
        .collect()
}

/// The cells of one markdown table line, trimmed, split on every `|` that is
/// NOT escaped as `\|` — GitHub's only spelling of a literal pipe inside a
/// table cell, code spans included — with each `\|` read back as `|`.
fn table_cells(line: &str) -> Vec<String> {
    let mut cells = Vec::new();
    let mut cell = String::new();
    let mut chars = line.trim().chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '\\' if chars.peek() == Some(&'|') => {
                cell.push('|');
                chars.next();
            }
            '|' => cells.push(std::mem::take(&mut cell)),
            _ => cell.push(ch),
        }
    }
    cells.push(cell);
    // The leading and trailing `|` delimit the row; they open no cell.
    if cells.first().is_some_and(|c| c.trim().is_empty()) {
        cells.remove(0);
    }
    if cells.last().is_some_and(|c| c.trim().is_empty()) {
        cells.pop();
    }
    cells.into_iter().map(|c| c.trim().to_string()).collect()
}

/// A table's rows, each with the 1-based document line it came from.
type NumberedRows = Vec<(usize, Vec<String>)>;

/// Every table in `doc` (outside fenced code blocks), as `(1-based line of
/// the header, rows)`.
fn markdown_tables(doc: &str) -> Vec<(usize, NumberedRows)> {
    let mut tables: Vec<(usize, NumberedRows)> = Vec::new();
    let mut fenced = false;
    let mut in_table = false;
    for (index, line) in doc.lines().enumerate() {
        if line.trim_start().starts_with("```") {
            fenced = !fenced;
        }
        if fenced || !line.starts_with('|') {
            in_table = false;
            continue;
        }
        if !in_table {
            tables.push((index + 1, Vec::new()));
            in_table = true;
        }
        tables.last_mut().expect("pushed above").1.push((index + 1, table_cells(line)));
    }
    tables
}

/// A table row with more (or fewer) cells than its header is a RENDERING
/// failure, not a style nit: GitHub drops every cell past the header's count,
/// so an unescaped `|` inside a code span silently truncates the row at that
/// pipe — measured 2026-09-29 on the `EnsuresCitationDischarge` row, where
/// eight unescaped pipes in `&&`/`||` spans hid most of the I3′/I4′
/// disclosure while every assertion below stayed green (they read cells 0–4
/// only).
fn assert_rows_match_header(table_line: usize, rows: &[(usize, Vec<String>)]) {
    let Some((_, header)) = rows.first() else { return };
    for (line, row) in rows {
        assert_eq!(
            row.len(),
            header.len(),
            "{TCB_DOC}:{line}: a row of the table at line {table_line} has {} cells, its header \
             has {}. An unescaped `|` inside a cell (a code span included) splits the row and \
             GitHub drops every cell past the header's count; write it as `\\|`. Row begins: \
             {:?}",
            row.len(),
            header.len(),
            row.first().map(|c| c.chars().take(80).collect::<String>()).unwrap_or_default()
        );
    }
}

/// Rows of the first markdown table under `heading`, cells trimmed, header and
/// separator dropped. Every row must have the header's cell count.
fn table_under(doc: &str, heading: &str) -> Vec<Vec<String>> {
    let (before, section) =
        doc.split_once(heading).unwrap_or_else(|| panic!("{TCB_DOC} has no `{heading}` heading"));
    // The 1-based document line of the section's first line, so a failure
    // names the line an editor opens.
    let first_line = before.matches('\n').count() + heading.matches('\n').count() + 1;
    let rows: NumberedRows = section
        .lines()
        .enumerate()
        .skip_while(|(_, line)| !line.starts_with('|'))
        .take_while(|(_, line)| line.starts_with('|'))
        .map(|(offset, line)| (first_line + offset, table_cells(line)))
        .collect();
    assert!(rows.len() > 2, "`{heading}` table has no body rows");
    assert_rows_match_header(rows[0].0, &rows);
    rows[2..].iter().map(|(_, row)| row.clone()).collect()
}

/// EVERY table in the document, not only the ones the assertions below read:
/// each row has exactly its header's cell count.
#[test]
fn every_tcb_table_row_has_the_header_cell_count() {
    let doc = read(TCB_DOC);
    let tables = markdown_tables(&doc);
    assert!(tables.len() >= 3, "parsed only {} tables from {TCB_DOC}", tables.len());
    for (line, rows) in &tables {
        assert_rows_match_header(*line, rows);
    }
}

/// The splitter is not vacuous: an unescaped pipe in a code span adds a cell,
/// the escaped spelling does not, and `\|` reads back as a literal `|`.
#[test]
fn table_cells_splits_only_on_unescaped_pipes() {
    assert_eq!(table_cells("| `A` | yes | x |"), ["`A`", "yes", "x"]);
    assert_eq!(table_cells("| `A` | `&&`/`||` | x |").len(), 5);
    assert_eq!(table_cells(r"| `A` | `&&`/`\|\|` | x |"), ["`A`", "`&&`/`||`", "x"]);
    let rows = markdown_tables("| h1 | h2 |\n|---|---|\n| a | `b|c` |\n");
    let [(1, table)] = rows.as_slice() else { panic!("one table at line 1: {rows:?}") };
    assert_eq!(table.len(), 3);
    let caught = std::panic::catch_unwind(|| assert_rows_match_header(1, table));
    assert!(caught.is_err(), "an unescaped pipe in a code span must fail the cell count");
}

fn authority_table(doc: &str) -> Vec<Vec<String>> {
    table_under(doc, "\n## The authority table\n")
}

/// The first `` `backticked` `` token of a cell.
fn code_span(cell: &str) -> String {
    let rest = cell.split_once('`').unwrap_or_else(|| panic!("no code span in cell {cell:?}")).1;
    rest.split_once('`')
        .unwrap_or_else(|| panic!("unterminated code span in {cell:?}"))
        .0
        .to_string()
}

/// A yes/no column cell. Everything after the verdict is the reason, which the
/// document is free to reword; the verdict itself is not.
fn yes_no(cell: &str, column: &str, variant: &str) -> bool {
    match cell.split(&[' ', ','][..]).next().unwrap_or_default() {
        "yes" => true,
        "no" => false,
        _ => panic!(
            "{TCB_DOC}'s `{column}` cell for {variant} must start with `yes` or `no`, got {cell:?}"
        ),
    }
}

/// `**N of the M**` claims in the section, paired with the first
/// `TrustStatus::…` named after each.
fn count_claims(doc: &str, heading: &str) -> Vec<(usize, usize, String)> {
    let section =
        doc.split_once(heading).unwrap_or_else(|| panic!("{TCB_DOC} has no `{heading}` heading")).1;
    let section = section.split("\n## ").next().expect("section body");
    let flat = section.replace('\n', " ");

    let segments: Vec<&str> = flat.split("**").collect();
    let mut claims = Vec::new();
    for (index, segment) in segments.iter().enumerate() {
        if index % 2 == 0 {
            continue;
        }
        let Some((count, total)) = segment.split_once(" of the ") else { continue };
        let (Ok(count), Ok(total)) = (count.trim().parse(), total.trim().parse()) else { continue };
        let following = segments.get(index + 1).copied().unwrap_or_default();
        let status = ["Trusted", "Certified"]
            .into_iter()
            .filter_map(|status| {
                following.find(&format!("`TrustStatus::{status}`")).map(|at| (at, status))
            })
            .min()
            .unwrap_or_else(|| panic!("claim `{segment}` names no TrustStatus"))
            .1;
        claims.push((count, total, status.to_string()));
    }
    claims
}

/// The gate-manifest rows, as the six columns the harness reads.
fn gate_manifest_rows(harness: &str) -> Vec<Vec<String>> {
    let start = harness.find("emit_gate_manifest() {").expect("gate manifest function");
    let body_start = harness[start..].find("<<'EOF'").expect("gate manifest heredoc") + start;
    let body_end =
        harness[body_start..].find("\nEOF\n").expect("gate manifest heredoc end") + body_start;
    let rows: Vec<Vec<String>> = harness[body_start..body_end]
        .lines()
        .filter(|line| line.contains('|'))
        .map(|line| line.split('|').map(str::to_string).collect())
        .filter(|row: &Vec<String>| row.len() == 6)
        .collect();
    assert!(
        rows.len() > 10,
        "parsed {} gate-manifest rows, expected the full manifest",
        rows.len()
    );
    rows
}

#[test]
fn tcb_document_enumerates_every_proof_authority() {
    let pass = read(VERIFY_PASS);
    let doc = read(TCB_DOC);

    let variants = enum_variants(&pass);
    let arms = disposition_arms(&pass);
    let documented = authority_table(&doc);

    // The compiler's own match is exhaustive, so this holds unless the parse
    // drifted — in which case every assertion below is meaningless. Arm order
    // is the author's grouping, not the declaration order, so compare as sets.
    let mut arm_names: Vec<&str> = arms.iter().map(|(variant, ..)| variant.as_str()).collect();
    let mut declared: Vec<&str> = variants.iter().map(String::as_str).collect();
    arm_names.sort_unstable();
    declared.sort_unstable();
    assert_eq!(
        declared, arm_names,
        "trust_disposition_for_authority arms do not match the enum; the parse in this test is \
         out of date with {VERIFY_PASS}"
    );

    let doc_names: Vec<String> = documented.iter().map(|row| code_span(&row[0])).collect();
    for variant in &variants {
        assert!(
            doc_names.contains(variant),
            "ResultProofAuthority::{variant} has no row in {TCB_DOC}. A new verdict class is a \
             new trust-boundary claim: add the row before landing it."
        );
    }
    for name in &doc_names {
        assert!(
            variants.contains(name),
            "{TCB_DOC} documents `{name}`, which is no longer a ResultProofAuthority variant"
        );
    }
    assert_eq!(
        doc_names, variants,
        "{TCB_DOC} lists the variants in a different order than they are declared"
    );

    for (variant, status, strength) in &arms {
        let row = documented
            .iter()
            .find(|row| &code_span(&row[0]) == variant)
            .expect("row presence checked above");
        assert_eq!(
            &code_span(&row[1]),
            status,
            "{TCB_DOC} reports ResultProofAuthority::{variant} as {}, the compiler returns \
             TrustStatus::{status}",
            code_span(&row[1])
        );
        assert_eq!(
            &code_span(&row[2]),
            strength,
            "{TCB_DOC} reports the strength of ResultProofAuthority::{variant} as {}, the \
             compiler returns {strength}",
            code_span(&row[2])
        );
    }
}

/// One authority's grade as `trust_grade_for_authority` spells it: the encoding,
/// the discharge and the premise classes, each in its serialized (kebab-case)
/// spelling.
type GradeTriple = (String, String, Vec<String>);

/// `UnvalidatedEncoder` → `unvalidated-encoder`: the serde `kebab-case`
/// spelling of a Rust variant name, which `trust_types::authority_grade`
/// writes and `docs/TCB.md` quotes.
fn kebab(ident: &str) -> String {
    let mut out = String::new();
    for (index, ch) in ident.char_indices() {
        if ch.is_ascii_uppercase() {
            if index > 0 {
                out.push('-');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

/// `GradeEncoding::E6Reflector` → `E6Reflector`, refusing any other path or a
/// non-literal.
fn grade_axis<'a>(compact: &'a str, axis: &str, variants: &[String]) -> &'a str {
    let name = compact
        .strip_prefix(axis)
        .and_then(|rest| rest.strip_prefix("::"))
        .unwrap_or_else(|| panic!("{variants:?}: `{compact}` is not a literal `{axis}::…`"));
    assert!(
        !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric()),
        "{variants:?}: `{compact}` is not a literal `{axis}::…`"
    );
    name
}

/// `(variant, grade)` per match arm of `trust_grade_for_authority`, in arm
/// order. Each arm is exactly one literal `trust_grade(GradeEncoding::…,
/// GradeDischarge::…, &[GradePremise::…, …])`, bare or in a block; anything
/// else (a guard, a wildcard, a computed axis, a delegation) is a hard parse
/// failure, as it is for the disposition arms, so one variant can never carry
/// two grades.
fn grade_arms(pass_src: &str) -> Vec<(String, GradeTriple)> {
    let function = item_body(pass_src, GRADE_FN);
    const MATCH: &str = "match authority {";
    assert_eq!(function.matches(MATCH).count(), 1, "one authority match required");
    let start = function.find(MATCH).expect("count checked");
    let preamble: String = function[..start].chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        preamble.is_empty()
            || preamble
                == "usetrust_types::authority_grade::{GradeDischarge,GradeEncoding,GradePremise};\
                    lettrust_grade=trust_types::authority_grade::ObligationGrade::new;",
        "unrecognized grade preamble: {preamble}"
    );
    let open = start + MATCH.len() - 1;
    let body = balanced_block(&function, open);
    assert!(
        function[open + body.len() + 2..].trim().is_empty(),
        "authority match has a trailing transformation"
    );

    let mut arms = Vec::new();
    let mut rest = body.trim();
    while !rest.is_empty() {
        let arrow = rest.find("=>").expect("grade arm arrow");
        let mut variants = Vec::new();
        for alternative in rest[..arrow].split('|') {
            let compact: String = alternative.chars().filter(|c| !c.is_whitespace()).collect();
            let pattern =
                compact.strip_prefix("ResultProofAuthority::").expect("qualified alternative");
            let end = pattern
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(pattern.len());
            assert!(end > 0, "empty grade variant");
            let variant = &pattern[..end];
            assert!(
                matches!(&pattern[end..], "" | "{..}"),
                "unsupported grade pattern for {variant}: {pattern}"
            );
            variants.push(variant.to_string());
        }
        let after = rest[arrow + 2..].trim_start();
        // The arm's expression: a block, or everything up to the next `,` at
        // depth zero.
        let (expression, following) = if after.starts_with('{') {
            let block = balanced_block(after, 0);
            (block.clone(), after[block.len() + 2..].trim_start())
        } else {
            let mut depth = 0i32;
            let mut end = after.len();
            for (offset, ch) in after.char_indices() {
                match ch {
                    '{' | '(' | '[' => depth += 1,
                    '}' | ')' | ']' => depth -= 1,
                    ',' if depth == 0 => {
                        end = offset;
                        break;
                    }
                    _ => {}
                }
            }
            (after[..end].to_string(), after[end..].trim_start())
        };
        assert!(
            following.is_empty()
                || following.starts_with(',')
                || following.starts_with("ResultProofAuthority::"),
            "grade arm has a trailing transformation for {variants:?}"
        );
        let compact: String = expression.chars().filter(|c| !c.is_whitespace()).collect();
        let args = compact
            .strip_prefix("trust_grade(")
            .and_then(|s| s.strip_suffix(')'))
            .unwrap_or_else(|| panic!("{variants:?} has no single literal grade: {compact}"));
        let args = args.strip_suffix(',').unwrap_or(args);
        let (encoding, tail) = args.split_once(',').expect("grade encoding argument");
        let (discharge, premises) = tail.split_once(',').expect("grade discharge argument");
        let encoding = kebab(grade_axis(encoding, "GradeEncoding", &variants));
        let discharge = kebab(grade_axis(discharge, "GradeDischarge", &variants));
        let premises = premises
            .strip_prefix("&[")
            .and_then(|s| s.strip_suffix(']'))
            .unwrap_or_else(|| panic!("{variants:?}: premises are not a literal slice"));
        let premises: Vec<String> = premises
            .split(',')
            .filter(|premise| !premise.is_empty())
            .map(|premise| kebab(grade_axis(premise, "GradePremise", &variants)))
            .collect();
        arms.extend(
            variants
                .into_iter()
                .map(|variant| (variant, (encoding.clone(), discharge.clone(), premises.clone()))),
        );
        rest = following.strip_prefix(',').unwrap_or(following).trim_start();
    }
    assert!(!arms.is_empty(), "parsed no grade arms");
    arms
}

#[test]
fn grade_parser_reads_grouped_bare_and_block_arms() {
    let source = "fn trust_grade_for_authority() { match authority {
        ResultProofAuthority::First { .. } | ResultProofAuthority::Second { .. } => {
            trust_grade(GradeEncoding::UnvalidatedEncoder, GradeDischarge::SolverAsserted, &[])
        }
        ResultProofAuthority::Third { .. } => trust_grade(
            GradeEncoding::E6Reflector,
            GradeDischarge::KernelReconstructed,
            &[GradePremise::ParameterView, GradePremise::RequiresLink],
        ),
    }}";
    let triple = |e: &str, d: &str, p: &[&str]| -> GradeTriple {
        (e.into(), d.into(), p.iter().map(|s| s.to_string()).collect())
    };
    assert_eq!(
        grade_arms(source),
        vec![
            ("First".into(), triple("unvalidated-encoder", "solver-asserted", &[])),
            ("Second".into(), triple("unvalidated-encoder", "solver-asserted", &[])),
            (
                "Third".into(),
                triple(
                    "e6-reflector",
                    "kernel-reconstructed",
                    &["parameter-view", "requires-link"]
                )
            ),
        ]
    );
}

#[test]
fn grade_parser_refuses_ambiguous_or_computed_grades() {
    let literal = "trust_grade(GradeEncoding::UnvalidatedEncoder, GradeDischarge::Assumed, &[])";
    let mut accepted = Vec::new();
    for arms in [
        format!("ResultProofAuthority::First {{ .. }} if guard() => {literal},"),
        format!("_ => {literal},"),
        format!("ResultProofAuthority::First {{ .. }} => {{ if g() {{ {literal} }} else {{ x() }} }}"),
        "ResultProofAuthority::First { .. } => delegated_grade(),".into(),
        "ResultProofAuthority::First { .. } => trust_grade(encoding(), GradeDischarge::Assumed, &[]),"
            .into(),
        "ResultProofAuthority::First { .. } => trust_grade(GradeEncoding::A, GradeDischarge::B, premises),"
            .into(),
        format!("ResultProofAuthority::First {{ .. }} => {literal}.with(x),"),
    ] {
        let source = format!("fn trust_grade_for_authority() {{ match authority {{ {arms} }} }}");
        if std::panic::catch_unwind(|| grade_arms(&source)).is_ok() {
            accepted.push(source);
        }
    }
    assert!(accepted.is_empty(), "ambiguous grades accepted: {accepted:#?}");
}

/// VF1: every `ResultProofAuthority` variant has exactly one (encoding,
/// discharge, premises) grade in `trust_grade_for_authority`, each spelled in
/// `trust_types::authority_grade`'s vocabulary, and the authority table's
/// `Encoding`, `Discharge` and `Premises` columns carry that same triple.
#[test]
fn tcb_grade_columns_match_trust_grade_for_authority() {
    use trust_types::authority_grade::{GradeDischarge, GradeEncoding, GradePremise};
    let pass = read(VERIFY_PASS);
    let doc = read(TCB_DOC);

    let variants = enum_variants(&pass);
    let arms = grade_arms(&pass);
    let mut graded: Vec<&str> = arms.iter().map(|(variant, _)| variant.as_str()).collect();
    let mut declared: Vec<&str> = variants.iter().map(String::as_str).collect();
    graded.sort_unstable();
    declared.sort_unstable();
    assert_eq!(
        graded, declared,
        "trust_grade_for_authority does not give every ResultProofAuthority variant exactly one \
         grade"
    );

    let documented = authority_table(&doc);
    for (variant, (encoding, discharge, premises)) in &arms {
        assert!(
            GradeEncoding::parse(encoding).is_some(),
            "{variant}: `{encoding}` is not a GradeEncoding spelling"
        );
        assert!(
            GradeDischarge::parse(discharge).is_some(),
            "{variant}: `{discharge}` is not a GradeDischarge spelling"
        );
        for premise in premises {
            assert!(
                GradePremise::parse(premise).is_some(),
                "{variant}: `{premise}` is not a GradePremise spelling"
            );
        }
        let row = documented
            .iter()
            .find(|row| &code_span(&row[0]) == variant)
            .unwrap_or_else(|| panic!("ResultProofAuthority::{variant} has no row in {TCB_DOC}"));
        assert_eq!(
            &code_span(&row[5]),
            encoding,
            "{TCB_DOC}'s Encoding for ResultProofAuthority::{variant} is not the compiler's"
        );
        assert_eq!(
            &code_span(&row[6]),
            discharge,
            "{TCB_DOC}'s Discharge for ResultProofAuthority::{variant} is not the compiler's"
        );
        let cell = row[7].trim();
        let documented_premises = if cell == "none" { Vec::new() } else { code_spans(cell) };
        assert!(
            cell == "none" || !documented_premises.is_empty(),
            "{TCB_DOC}'s Premises for ResultProofAuthority::{variant} must be `none` or code spans, \
             got {cell:?}"
        );
        assert_eq!(
            &documented_premises, premises,
            "{TCB_DOC}'s Premises for ResultProofAuthority::{variant} are not the compiler's"
        );
    }

    // Every class grade is one a record may state (`ObligationGrade::admitted`:
    // premises in declaration order, none repeated), and the (encoding,
    // discharge) pairs the function spells are exactly `ADMITTED_AXES`, the
    // list the `trust.obligations.v1` reader admits: a pair the compiler
    // stops stating, or one the reader admits that no authority states, fails.
    let mut spelled = std::collections::BTreeSet::new();
    for (variant, (encoding, discharge, premises)) in &arms {
        let parse_premises: Vec<GradePremise> = premises
            .iter()
            .map(|premise| GradePremise::parse(premise).expect("checked above"))
            .collect();
        let grade = trust_types::authority_grade::ObligationGrade::new(
            GradeEncoding::parse(encoding).expect("checked above"),
            GradeDischarge::parse(discharge).expect("checked above"),
            &parse_premises,
        );
        if let Err(error) = grade.admitted() {
            panic!("ResultProofAuthority::{variant}'s grade is not admitted: {error}");
        }
        spelled.insert((grade.encoding, grade.discharge));
    }
    let admitted: std::collections::BTreeSet<_> =
        trust_types::authority_grade::ADMITTED_AXES.into_iter().collect();
    assert_eq!(
        spelled, admitted,
        "trust_grade_for_authority's (encoding, discharge) pairs are not \
         trust_types::authority_grade::ADMITTED_AXES"
    );

    // The E6 rows get the E6 reflector's grade, never calculus credit, and the
    // one calculus authority is VF5's: `CalculusRowProved`, through the
    // reference entry, stating exactly `CALCULUS_ROW_PREMISES`.
    for (variant, (encoding, discharge, premises)) in &arms {
        if variant.starts_with("EnsuresCitation") {
            assert_eq!(encoding, "e6-reflector", "{variant} is an E6 row");
        }
        if variant == "CalculusRowProved" {
            assert_eq!(encoding, "proven-calculus");
            assert_eq!(discharge, "kernel-reference-checked");
            let expected: Vec<String> = trust_types::authority_grade::CALCULUS_ROW_PREMISES
                .iter()
                .map(|premise| premise.as_str().to_string())
                .collect();
            assert_eq!(premises, &expected, "the VF5 authority states its three premises");
        } else {
            assert_ne!(
                encoding, "proven-calculus",
                "{variant} claims calculus credit; only VF5's CalculusRowProved is proved sound"
            );
        }
    }
}

/// VF5 / E4.7: the calculus authority stays out of `Certified` totals while
/// the owner's ruling is not taken. The document says `Trusted` and the
/// disposition parses to `Trusted` exactly because the shipped flag is false;
/// the negative control is the parser's own reading under the flag's other
/// value, checked against the same pinned delegate.
#[test]
fn calculus_rows_stay_out_of_certified_totals_until_e4_7() {
    let pass = read(VERIFY_PASS);
    let doc = read(TCB_DOC);
    assert!(
        !trust_types::authority_grade::E4_7_CALCULUS_ROWS_CERTIFIED,
        "E4.7 is the owner's ruling; flipping it is a deliberate TCB change, not this guard's"
    );
    let calculus: Vec<_> = disposition_arms(&pass)
        .into_iter()
        .filter(|(variant, ..)| variant == "CalculusRowProved")
        .collect();
    assert_eq!(
        calculus,
        vec![("CalculusRowProved".into(), "Trusted".into(), "Constructive".into())]
    );
    assert!(!certified_variants(&pass).contains("CalculusRowProved"));
    let row = authority_table(&doc)
        .into_iter()
        .find(|row| code_span(&row[0]) == "CalculusRowProved")
        .expect("the VF5 row");
    assert_eq!(code_span(&row[1]), "Trusted");
    assert!(!yes_no(&row[3], "Kernel-checked", "CalculusRowProved"));
    // Negative control: the delegate's other branch is `Certified`, so the
    // flag, and only the flag, keeps the row out of the totals.
    let delegate: String =
        item_body(&pass, CALCULUS_DISPOSITION_FN).chars().filter(|c| !c.is_whitespace()).collect();
    let (taken, not_taken) = delegate
        .strip_prefix("ife4_7{")
        .and_then(|rest| rest.split_once("}else{"))
        .expect("the two-way delegate");
    assert!(taken.starts_with("(TrustStatus::Certified,"), "{taken}");
    assert!(not_taken.starts_with("(TrustStatus::Trusted,"), "{not_taken}");
}

#[test]
fn tcb_document_counts_match_the_table() {
    let pass = read(VERIFY_PASS);
    let doc = read(TCB_DOC);

    let arms = disposition_arms(&pass);
    let total = arms.len();
    let certified = arms.iter().filter(|(_, status, _)| status == "Certified").count();
    let trusted = arms.iter().filter(|(_, status, _)| status == "Trusted").count();
    assert_eq!(
        certified + trusted,
        total,
        "a disposition arm returns neither Trusted nor Certified; {TCB_DOC}'s two-way summary no \
         longer describes the code"
    );

    let claims = count_claims(&doc, "\n## The one-sentence answer\n");
    for expected in [(trusted, total, "Trusted"), (certified, total, "Certified")] {
        let (count, of, status) = expected;
        assert!(
            claims.iter().any(|(c, o, s)| (*c, *o, s.as_str()) == (count, of, status)),
            "{TCB_DOC} must state `**{count} of the {of}**` for TrustStatus::{status}; it states \
             {claims:?}"
        );
    }
    assert_eq!(claims.len(), 2, "unexpected extra count claims in {TCB_DOC}: {claims:?}");
}

/// The docs spell this count both ways ("8 of the 10", "eight of the ten"), so
/// the guard has to read both.
const NUMBER_WORDS: &[&str] = &[
    "zero",
    "one",
    "two",
    "three",
    "four",
    "five",
    "six",
    "seven",
    "eight",
    "nine",
    "ten",
    "eleven",
    "twelve",
    "thirteen",
    "fourteen",
    "fifteen",
    "sixteen",
    "seventeen",
    "eighteen",
];

fn parse_count(token: &str) -> Option<usize> {
    let token = token.trim_matches(|c: char| !c.is_ascii_alphanumeric());
    if let Ok(n) = token.parse::<usize>() {
        return Some(n);
    }
    NUMBER_WORDS.iter().position(|w| *w == token.to_ascii_lowercase())
}

/// Every TOTAL cited next to "proof-authority class" in a live document must be
/// the live total. The count beside it is left alone on purpose: these sentences
/// use it for different things ("eight ... report `Trusted`", "one of ten
/// classes"), so only the total is unambiguous across all of them — and the
/// total is what went stale in all five unguarded documents.
#[test]
fn live_documents_cite_the_current_proof_authority_total() {
    let pass = read(VERIFY_PASS);
    let total = disposition_arms(&pass).len();
    assert!(
        total < NUMBER_WORDS.len(),
        "total {total} is outside the spellable range; extend NUMBER_WORDS"
    );

    let mut checked = 0usize;
    for doc in TOTAL_CITING_DOCS {
        let text = read(doc).replace('*', " ");
        let flat = text.split_whitespace().collect::<Vec<_>>().join(" ");
        // "<N> proof-authority class..." where N is preceded by "of", "of the",
        // or "the" — the three shapes every citation in the tree uses.
        for (at, _) in flat.match_indices("proof-authority class") {
            let before: Vec<&str> = flat[..at].split_whitespace().rev().take(3).collect();
            let Some(cited) = before.first().and_then(|t| parse_count(t)) else { continue };
            let anchored = matches!(
                before.get(1).map(|s| s.to_ascii_lowercase()).as_deref(),
                Some("of") | Some("the")
            );
            if !anchored {
                continue;
            }
            assert_eq!(
                cited, total,
                "{doc} cites {cited} proof-authority classes; `{DISPOSITION_FN}` in \
                 {VERIFY_PASS} has {total}. Fix the document — and if you changed the enum, \
                 every document in TOTAL_CITING_DOCS cites this number."
            );
            checked += 1;
        }
    }
    assert!(
        checked >= TOTAL_CITING_DOCS.len(),
        "expected at least one guarded citation per document in TOTAL_CITING_DOCS, found \
         {checked} across {} documents; a citation was reworded out of the guard's reach",
        TOTAL_CITING_DOCS.len()
    );
}

/// The `Kernel-checked` column is the document's headline claim per row: that
/// the Clean kernel re-checked THIS obligation. In the code that claim is
/// exactly `TrustStatus::Certified`, so the two must agree in both directions —
/// a `Certified` row the document calls unchecked understates the base, and a
/// `Trusted` row the document calls kernel-checked is a false proof claim.
#[test]
fn tcb_kernel_checked_column_is_exactly_the_certified_rows() {
    let pass = read(VERIFY_PASS);
    let doc = read(TCB_DOC);

    let certified = certified_variants(&pass);
    for row in authority_table(&doc) {
        let variant = code_span(&row[0]);
        let claimed = yes_no(&row[3], "Kernel-checked", &variant);
        assert_eq!(
            claimed,
            certified.contains(&variant),
            "{TCB_DOC} reports Kernel-checked={} for ResultProofAuthority::{variant}, but \
             trust_disposition_for_authority returns {}. Kernel-checked and Certified are the \
             same claim.",
            if claimed { "yes" } else { "no" },
            if certified.contains(&variant) { "Certified" } else { "Trusted" }
        );
    }

    // A consumer that asks for a row's kernel proof term must be asking a row
    // the table calls kernel-checked — and, since the E9 discharge began
    // retaining its kernel-audited `CleanCic` payload, the converse holds too:
    // EVERY kernel-checked variant hands its proof term out. That converse is
    // what keeps a `Certified` row publishable: the authenticated publication
    // boundary withholds any favorable row that ships no `clean_cic` artifact,
    // so a `Certified` variant with no carrier arm is unpublishable by
    // construction (measured on the E9 lanes before they carried one).
    //
    // A carrier is any arm whose body is not `None` — an arm that forwards an
    // `Option` (`evidence.as_ref()`) hands a term out exactly as a `Some(..)`
    // arm does, and must not slip past a substring match. A block-bodied
    // `{ None }` is the same non-carrier as a bare `None`, so strip the braces
    // before comparing rather than reading a brace as evidence.
    let variants = enum_variants(&pass);
    let evidence_body = item_body(&pass, KERNEL_EVIDENCE_FN);
    let carriers: BTreeSet<String> = match_self_arms(&evidence_body, &variants)
        .into_iter()
        .filter(|(_, arm)| {
            arm.trim().trim_start_matches('{').trim_end_matches('}').trim() != "None"
        })
        .flat_map(|(matched, _)| matched)
        .collect();
    assert!(!carriers.is_empty(), "kernel_evidence_for hands out no proof term to anyone");
    for carrier in &carriers {
        assert!(
            certified.contains(carrier),
            "kernel_evidence_for returns a proof term for ResultProofAuthority::{carrier}, which \
             {TCB_DOC} does not report as Certified. A row that hands out a kernel proof term is \
             claiming a kernel check."
        );
    }
    for variant in &certified {
        assert!(
            carriers.contains(variant),
            "ResultProofAuthority::{variant} reports Certified but kernel_evidence_for hands out \
             no proof term for it, so the publication boundary can never publish its rows. Retain \
             the kernel-checked term on the variant and return it here."
        );
    }
}

/// `Independent static proof` decides whether a row may be someone else's
/// premise (the panic-free callee registry, the R1 lowering-abort
/// suppression). A `no` row the code admits would let bookkeeping or a derived
/// aggregate stand in for a proof, which is the composition failure the column
/// exists to prevent.
#[test]
fn tcb_static_proof_column_matches_the_predicate() {
    let pass = read(VERIFY_PASS);
    let doc = read(TCB_DOC);

    let variants = enum_variants(&pass);
    let admitted = variants_named(&item_body(&pass, STATIC_PROOF_FN), &variants);
    let excluded = variants_named(&item_body(&pass, UNCONDITIONAL_FN), &variants);
    assert!(!admitted.is_empty(), "is_static_proof_for admits no variant at all");

    for row in authority_table(&doc) {
        let variant = code_span(&row[0]);
        let cell = &row[4];
        let claimed = yes_no(cell, "Independent static proof", &variant);
        assert_eq!(
            claimed,
            admitted.contains(&variant),
            "{TCB_DOC} reports Independent static proof={cell:?} for \
             ResultProofAuthority::{variant}, but is_static_proof_for {} it",
            if admitted.contains(&variant) { "admits" } else { "excludes" }
        );
        // The qualifier is not decoration: `is_unconditional_static_proof_for`
        // is what a consumer calls when a closed-world claim will not do.
        assert_eq!(
            cell.contains("conditional"),
            excluded.contains(&variant),
            "{TCB_DOC} reports Independent static proof={cell:?} for \
             ResultProofAuthority::{variant}, but is_unconditional_static_proof_for {} it",
            if excluded.contains(&variant) { "excludes" } else { "admits" }
        );
    }
}

/// Check elision is the only thing a passing verdict DELETES from the compiled
/// program: the panic edge of an overflow `Assert` stops existing, and nothing
/// downstream replaces it. `elide_kernel_certified_checks` gates on the
/// authority VARIANT, not on the status, so `Certified` being necessary is a
/// property of the variant list — which is what this pins.
#[test]
fn tcb_check_elision_is_licensed_only_by_certified_variants() {
    let pass = read(VERIFY_PASS);
    let doc = read(TCB_DOC);

    let variants = enum_variants(&pass);
    let certified = certified_variants(&pass);
    let elide_body = item_body(&pass, ELIDE_FN);
    let licensing = variants_named(&elide_body, &variants);
    assert!(
        !licensing.is_empty(),
        "elide_kernel_certified_checks names no ResultProofAuthority variant; either the elision \
         lane moved or it no longer gates on authority at all"
    );

    // Reading the variant pattern is only sound if the pattern is the WHOLE
    // authority decision. A delegation added beside it — `is_static_proof_for`,
    // a status comparison, any new predicate — would widen the gate while this
    // parse still reported the narrow set, so the calls made on the bound
    // authority are whitelisted rather than assumed.
    const AUTHORITY_QUERIES: [&str; 2] = ["matches_row", "matches_compiler_result"];
    for (offset, _) in elide_body.match_indices("auth.") {
        let rest = &elide_body[offset + "auth.".len()..];
        let end =
            rest.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(rest.len());
        let call = &rest[..end];
        assert!(
            AUTHORITY_QUERIES.contains(&call),
            "elide_kernel_certified_checks asks the authority `{call}`, which this test does not \
             know how to follow. The elision gate's authority decision must stay readable as the \
             variant pattern plus {AUTHORITY_QUERIES:?}, or this guard reports a narrower \
             licensing set than the compiler actually honours."
        );
    }

    for variant in &licensing {
        assert!(
            certified.contains(variant),
            "elide_kernel_certified_checks licenses check elision for \
             ResultProofAuthority::{variant}, which trust_disposition_for_authority reports as \
             Trusted. Trusted does not license elision: a check would be deleted on the word of \
             an engine no kernel re-checked."
        );
    }

    let documented: BTreeSet<String> = table_under(&doc, "\n## What licenses check elision\n")
        .iter()
        .map(|row| code_span(&row[0]))
        .collect();
    assert_eq!(
        documented, licensing,
        "{TCB_DOC}'s elision table and elide_kernel_certified_checks disagree about which \
         authorities license check elision"
    );
}

#[test]
fn tcb_document_names_live_pre_solver_producers() {
    let doc = read(TCB_DOC);
    let producers = table_under(&doc, "\n## Pre-solver trusted producers\n");
    assert!(producers.len() >= 5, "the pre-solver producer table lost rows");

    for row in &producers {
        let path = code_span(&row[0]);
        assert!(
            repo_root().join(&path).exists(),
            "{TCB_DOC} names `{path}` as a trusted producer, but it does not exist. Either the \
             base moved or the row is stale — both need the document updated."
        );
    }
}

// Complete callee-summary carrier inventory: facts, identity filters,
// checked candidate inputs and invariant-use sets. A field is not itself
// a proof authority. This guard requires its role to be disclosed.
const SUMMARY_HEADING: &str = "\n## Callee-summary carriers";

/// `(source file, struct header)` of each callee-summary carrier, in the order
/// the document's table lists them.
const SUMMARY_CARRIERS: &[(&str, &str)] = &[
    ("crates/trust-vcgen/src/lib.rs", "struct CalleeSummaryFacts {"),
    ("crates/trust-ir-bridge/src/lower.rs", "pub struct NativeCalleeSummaryContext {"),
];

/// Named fields of the one struct introduced by `header`, in declaration order.
///
/// A field is a depth-zero line `name: Type` (`name` an identifier followed by a
/// single `:`), so the continuation lines of a multi-line generic type
/// (`trust_types::CalleeIdentity,`) never read as fields. A second definition, a
/// tuple struct, or an empty parse is a hard failure.
fn struct_fields(src: &str, header: &str) -> Vec<String> {
    let src = strip_line_comments(src);
    assert_eq!(src.matches(header).count(), 1, "expected exactly one `{header}`");
    let at = src.find(header).expect("occurrence counted above");
    let body = balanced_block(&src, at);
    let mut fields = Vec::new();
    let mut depth = 0usize;
    for line in body.lines() {
        let trimmed = line.trim().trim_start_matches("pub(crate) ").trim_start_matches("pub ");
        if depth == 0
            && let Some((name, rest)) = trimmed.split_once(':')
            && !rest.starts_with(':')
            && !name.is_empty()
            && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            && name.starts_with(|c: char| c.is_ascii_lowercase() || c == '_')
        {
            fields.push(name.to_string());
        }
        depth = depth + line.matches('{').count() - line.matches('}').count();
    }
    assert!(!fields.is_empty(), "parsed no fields from `{header}`");
    fields
}

#[test]
fn struct_field_parser_reads_named_fields_only() {
    let source = "struct CalleeSummaryFacts {
        /// a doc comment: not a field
        return_bounds: FxHashMap<String, i128>,
        pub(crate) visible: bool,
        clean_origin_definitional_models: FxHashMap<
            trust_types::CalleeIdentity,
            modular::CleanOriginDefinitionalCallModel,
        >,
    }";
    assert_eq!(
        struct_fields(source, "struct CalleeSummaryFacts {"),
        vec!["return_bounds", "visible", "clean_origin_definitional_models"]
    );
    let twice = format!("{source}\n{source}");
    assert!(
        std::panic::catch_unwind(|| struct_fields(&twice, "struct CalleeSummaryFacts {")).is_err(),
        "a second definition must be refused, not first-matched"
    );
}

#[test]
fn tcb_document_enumerates_every_callee_summary_family() {
    let doc = read(TCB_DOC);
    let pass = read(VERIFY_PASS);
    let variants = enum_variants(&pass);

    let mut expected = Vec::new();
    for (path, header) in SUMMARY_CARRIERS {
        let carrier =
            header.trim_start_matches("pub ").trim_start_matches("struct ").trim_end_matches(" {");
        for field in struct_fields(&read(path), header) {
            expected.push(format!("{carrier}::{field}"));
        }
    }
    let rows = table_under(&doc, SUMMARY_HEADING);
    let documented: Vec<String> = rows.iter().map(|row| code_span(&row[0])).collect();
    for family in &expected {
        assert!(
            documented.contains(family),
            "{family} has no row under `{}` in {TCB_DOC}. An installed callee-context field \
             changes what generation assumes, filters or checks: document its producer, role, \
             identity/evidence gate and assurance boundary before landing it.",
            SUMMARY_HEADING.trim()
        );
    }
    assert_eq!(
        documented, expected,
        "{TCB_DOC}'s callee-summary table must list exactly the carrier fields, in declaration \
         order"
    );

    // Backticked authority names in the assurance column must be declared
    // variants. This checks names; it grants no authority to a carrier.
    for row in &rows {
        assert_eq!(row.len(), 5, "callee-summary rows have five columns: {row:?}");
        for span in code_spans(&row[4]) {
            assert!(
                variants.contains(&span),
                "{TCB_DOC}'s callee-summary row `{}` cites `{span}` as an authority, which is \
                 not a ResultProofAuthority variant",
                code_span(&row[0])
            );
        }
    }

    // Every field is installed through an explicit context builder. A renamed
    // or removed builder forces review of the documented installation boundary.
    for (path, header) in SUMMARY_CARRIERS {
        let source = strip_line_comments(&read(path));
        for field in struct_fields(&source, header) {
            assert!(
                source.contains(&format!("fn with_{field}(")),
                "the installation builder for {field} changed in {path}; re-read its TCB row"
            );
        }
    }
}

/// The `InterproceduralCalleeClosure` row names the gate that actually decides
/// it and every arm that gate admits a call through. The row once named the
/// narrower zero-obligation gate (`all_calls_target_proven_panic_free`) and a
/// two-registry callee set while the seam admitted additional arms; an arm added
/// to the gate is a new premise of an UNCONDITIONAL static proof.
#[test]
fn tcb_callee_closure_row_names_its_gate_and_every_call_arm() {
    let pass = read(VERIFY_PASS);
    let doc = read(TCB_DOC);
    let row = authority_table(&doc)
        .into_iter()
        .find(|row| code_span(&row[0]) == "InterproceduralCalleeClosure")
        .expect("the authority table has an InterproceduralCalleeClosure row");
    let text = row.last().expect("authority row has a details column");

    // The seam: the recorded gate fact the installer reads is exactly
    // `others_all_proved && all_calls_discharge_panic_free`, unconditional tag only.
    let compact_pass = compact(&strip_line_comments(&pass));
    for shape in [
        "letcalls_discharged=others_all_proved&&all_calls_discharge_panic_free(sess,func,panic_calls_proven_unreachable,rows);",
        "record_interprocedural_pf_call_closure(sess,&func.def_path,calls_discharged&&!under_precondition,);",
    ] {
        assert!(
            compact_pass.contains(shape),
            "the interprocedural seam's recorded gate changed shape (expected `{shape}`); re-read \
             `refute_full_assert_obligations` and correct the InterproceduralCalleeClosure row"
        );
    }
    assert!(
        text.contains("`all_calls_discharge_panic_free`"),
        "the InterproceduralCalleeClosure row must name its gate `all_calls_discharge_panic_free`"
    );

    // Every arm label: the pure core's `Some("…")` returns, and the gate's own
    // `arm=…` trace labels for the arms it decides in place.
    let mut arms = BTreeSet::new();
    let core = item_body(&pass, "fn discharge_call_arm_admits(");
    for (at, _) in core.match_indices("Some(\"") {
        let rest = &core[at + "Some(\"".len()..];
        arms.insert(rest[..rest.find('"').expect("closed label")].to_string());
    }
    let gate = item_body(&pass, "fn all_calls_discharge_panic_free(");
    for (at, _) in gate.match_indices("arm=") {
        let rest = &gate[at + "arm=".len()..];
        let end = rest.find(|c: char| !(c.is_ascii_lowercase() || c == '-')).unwrap_or(rest.len());
        if end > 0 {
            arms.insert(rest[..end].to_string());
        }
    }
    // Each pure-core admission is a literal labelled Some; each direct
    // gate admission (plus the unreachable-panic exemption) continues the
    // call-site loop. New unlabelled admissions must also force a review.
    assert_eq!(
        core.matches("Some(").count(),
        core.matches("Some(\"").count(),
        "a computed call-arm label needs a fresh TCB inventory"
    );
    assert_eq!(
        gate.matches("continue;").count(),
        5,
        "the call gate's admission/exemption shape changed; audit its TCB row"
    );
    assert!(arms.len() >= 6, "parsed too few call-discharge arms: {arms:?}");
    for arm in &arms {
        assert!(
            text.contains(&format!("`{arm}`")),
            "`all_calls_discharge_panic_free` admits a call through arm `{arm}`, which the \
             InterproceduralCalleeClosure row in {TCB_DOC} does not name"
        );
    }
    if gate.contains("panic_free_under_precondition") {
        assert!(
            text.contains("`panic_free_under_precondition`"),
            "the gate admits under-precondition callees; the row must name that arm"
        );
    }
}

/// A guard in no runner is not enforcement. This one was in none until
/// 2026-07-25: the pre-push hook runs three unrelated lanes, the harness's
/// `quick.crates-lib-tests` row is `--lib` only, and `scripts/
/// run_tests_after_build.sh` names one other integration target by hand. The
/// row asserted here is what makes the document's claim about itself true;
/// `scripts/check_gate_lane_coverage.py` fails if it is deleted.
#[test]
fn tcb_guard_runs_in_a_named_gate_lane() {
    let harness = read(GATE_MANIFEST);
    let rows = gate_manifest_rows(&harness);
    let running: Vec<&Vec<String>> = rows
        .iter()
        .filter(|row| {
            row[5].contains(&format!("--test {THIS_TEST_TARGET}"))
                && row[5].contains("-p trust-integration-tests")
        })
        .collect();
    assert!(
        !running.is_empty(),
        "no row in {GATE_MANIFEST} runs `--test {THIS_TEST_TARGET}` for trust-integration-tests. \
         This test can only keep {TCB_DOC} honest if something invokes it."
    );
    for row in running {
        assert_eq!(
            row[3], "true",
            "{GATE_MANIFEST} row `{}` runs this guard but is not required, so a failure would \
             not stop the profile",
            row[0]
        );
    }
}

// ---------------------------------------------------------------------------
// TRUST-02 — an `Unchecked` solver `Proved` never reaches a premise consumer.
//
// `ProofStrength::smt_unsat_unvalidated()` (`AssuranceLevel::Unchecked`: "solver
// said so, no independent validation") is what a bare `unsat` from the
// subprocess `IncrementalAYSession` becomes — the session never sends
// `:produce-proofs` — and what its per-process `smtlib_backend` fallback
// becomes. Since plan P4 / T4.1 (2026-10-10) the compiler builds neither: the
// router's SMT lane is the in-process ay. Publication already refuses such a
// row: `convert_result` reads the row-bound authority, never the strength.
// Whether one could be CONSUMED as a premise BEFORE publication was the open
// question, and the answer rests on the PRODUCER side: some consumers read the
// bare `Proved` label — the two catch-all grounding lanes
// (`refute_full_assert_obligations`' `others_all_proved` and
// `ground_panic_freedom_catchall`), whose output `certify_all` then certifies,
// the R1 flip's `unproved` partition, and check elision's hardened-twin guard
// (`hardened_overflow_twin_is_unproved`) — and would accept one if it were
// there. What keeps it out is that the compiler builds NO Unchecked producer,
// the router it builds instead (fresh per call, in process) has ONE consumer,
// that consumer re-derives its verdict in the Clean kernel, and the native lane
// refuses non-publication-grade evidence. The tests below pin exactly those
// facts, and
// that the check-elision seam reads no label the consumer table omits;
// `docs/TCB.md` ("Unvalidated solver verdicts") records the trace they encode.
// A failure here means an unvalidated solver answer may now reach a premise:
// re-trace the consumers that section lists before changing the expectation.
// ---------------------------------------------------------------------------

const UNCHECKED_TCB_HEADING: &str = "\n## Unvalidated solver verdicts";

/// The one consumer of the router `discover_router_backends` feeds, compacted
/// (comments and whitespace removed). The verdict is accepted only when
/// `trust_certify::certify_vc` independently re-derives it in the Clean
/// kernel, so whatever label a solver puts on it is a scheduling hint and never
/// a premise for the dynamic-dispatch summary callers assume. The one other
/// read of the router's results is the `TRUST_DYN_PROBE` line that counts
/// them, which prints and decides nothing.
const LISKOV_CONSUMER: &str = "\
    letresults=build_router(tcx.sess).verify_all(&liskov_vcs);\
    ifprobe{letproved=results.iter().filter(|(_,r)|r.is_proved()).count();\
    letrefuted=results.iter().filter(|(_,r)|matches!(r,VerificationResult::Failed{..})).count();\
    eprintln!(\"TRUST_DYN_PROBE:{impl_type}Liskovrouter:{}VC(s),{proved}proved,{refuted}refuted\",\
    results.len());}\
    letrefined=results.iter().all(|(vc,r)|r.is_proved()&&\
    trust_certify::certify_vc(vc).is_some());\
    if!refined{ifprobe{eprintln!(\"TRUST_DYN_PROBE:impls_verified=false(\
    {impl_type}failsLiskovrefinement)\");}returnfalse;}";

/// `(callee, its only caller)` from backend discovery to the one consumer.
/// Plan P4 / T4.1 deleted the Session cache (`get_router_backends`) that sat
/// between the first two: `build_router` builds a fresh inventory per call.
const UNCHECKED_ROUTER_CHAIN: &[(&str, &str)] =
    &[("discover_router_backends", "build_router"), ("build_router", "all_trait_impls_verified")];

/// The whole body of `build_router`, compacted: a router over a fresh backend
/// inventory, built per call from the tracked timeout and effort scale, with no
/// Session state between calls.
const FRESH_ROUTER_BODY: &str = "trust_router::Router::with_backends(discover_router_backends(\
    vc_timeout_ms(sess),effort_scale(sess),))";

/// Names that would put the subprocess solver back on a `trustc` path: the
/// session type, its constructor, and its module.
const SUBPROCESS_SOLVER_NAMES: &[&str] =
    &["IncrementalAYSession", "with_solver_path", "incremental_ay"];

fn compact(text: &str) -> String {
    text.chars().filter(|c| !c.is_whitespace()).collect()
}

/// Every `.rs` file under `compiler/` except dedicated test modules
/// (`tests.rs`, `*_tests.rs`), comment-stripped, keyed by repo-relative path.
fn compiler_production_sources() -> Vec<(String, String)> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let entries =
            std::fs::read_dir(dir).unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()));
        for entry in entries {
            let path = entry.expect("readable directory entry").path();
            if path.is_dir() {
                walk(&path, out);
            } else if path.extension().is_some_and(|ext| ext == "rs") {
                out.push(path);
            }
        }
    }
    let root = repo_root();
    let mut files = Vec::new();
    walk(&root.join("compiler"), &mut files);
    files.sort();
    let sources: Vec<(String, String)> = files
        .into_iter()
        .filter(|path| {
            let name = path.file_name().and_then(|name| name.to_str()).unwrap_or_default();
            name != "tests.rs" && !name.ends_with("_tests.rs")
        })
        .map(|path| {
            let bytes = std::fs::read(&path)
                .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
            let relative = path
                .strip_prefix(&root)
                .expect("walked below the repo root")
                .to_string_lossy()
                .replace('\\', "/");
            (relative, strip_line_comments(&String::from_utf8_lossy(&bytes)))
        })
        .collect();
    assert!(
        sources.iter().any(|(path, _)| path == VERIFY_PASS),
        "the compiler walk did not reach {VERIFY_PASS}; the guard below would be vacuous"
    );
    sources
}

/// Offsets where `needle` starts an identifier path (the previous character is
/// not an identifier character), so `build_router` never matches inside
/// `rebuild_router`.
fn identifier_occurrences(code: &str, needle: &str) -> Vec<usize> {
    code.match_indices(needle)
        .map(|(at, _)| at)
        .filter(|&at| {
            code[..at].chars().next_back().is_none_or(|c| !(c.is_ascii_alphanumeric() || c == '_'))
        })
        .collect()
}

/// A call site: an occurrence that is not the item's own definition.
fn call_sites(code: &str, callee: &str) -> Vec<usize> {
    identifier_occurrences(code, &format!("{callee}("))
        .into_iter()
        .filter(|&at| !code[..at].ends_with("fn "))
        .collect()
}

/// Name of the top-level (unindented) `fn` item that encloses byte `at`. Every
/// site this guard inspects is in a top-level fn today; a site that moves into
/// an `impl` or `mod` resolves to a DIFFERENT name and fails the equality it
/// feeds, which is the intended outcome — the trace must be redone.
fn enclosing_fn(code: &str, at: usize) -> String {
    let start = ["\nfn ", "\npub fn ", "\npub(crate) fn ", "\npub(super) fn "]
        .iter()
        .filter_map(|intro| code[..at].rfind(intro).map(|pos| pos + intro.len()))
        .max()
        .unwrap_or_else(|| panic!("no top-level fn encloses byte {at}"));
    let rest = &code[start..];
    let end = rest.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(rest.len());
    rest[..end].to_string()
}

/// The body of the innermost `{ … }` block enclosing byte `at`.
fn enclosing_block(code: &str, at: usize) -> String {
    let mut depth = 0usize;
    for (offset, ch) in code[..at].char_indices().rev() {
        match ch {
            '}' => depth += 1,
            '{' if depth == 0 => return balanced_block(code, offset),
            '{' => depth -= 1,
            _ => {}
        }
    }
    panic!("no block encloses byte {at}");
}

/// Plan P4 / T4.1: no `trustc` path builds the subprocess solver. The compiler
/// names neither the Unchecked subprocess producer (`IncrementalAYSession`,
/// its `with_solver_path` constructor, its `incremental_ay` module) nor the
/// other Unchecked producer (`smtlib_backend`'s parsed bare `unsat`) nor the
/// Unchecked stamp itself anywhere. Until T4.1 the session was built at one
/// site, `discover_router_backends`, over a snapshot of the `ay` beside
/// `trustc`, and shared by every function of the Session behind a mutex.
#[test]
fn no_trustc_path_builds_the_subprocess_solver() {
    let sources = compiler_production_sources();
    let mut sites = Vec::new();
    let mut stamps = Vec::new();
    for (path, code) in &sources {
        for needle in SUBPROCESS_SOLVER_NAMES {
            for at in identifier_occurrences(code, needle) {
                sites.push(format!("{path}: `{needle}` in `{}`", enclosing_fn(code, at)));
            }
        }
        for needle in ["smtlib_backend", "smt_unsat_unvalidated", "AssuranceLevel::Unchecked"] {
            if !identifier_occurrences(code, needle).is_empty() {
                stamps.push(format!("{path} names `{needle}`"));
            }
        }
    }
    assert!(
        sites.is_empty(),
        "compiler code names the subprocess solver again: {sites:?}. trustc's SMT lane is the \
         in-process ay (plan P4 / T4.1): a subprocess session shared across functions makes a \
         verdict depend on scheduling, and every bare `unsat` it reads is Unchecked. Re-trace \
         {TCB_DOC}'s `Unvalidated solver verdicts` before accepting this"
    );
    assert!(
        stamps.is_empty(),
        "compiler code now names an Unchecked producer or stamp: {stamps:?}. An Unchecked \
         `Proved` must never enter the verdict vector the pre-authority consumers read"
    );
}

/// Non-vacuity for the census above: the identifier scan finds the session in
/// the one non-compiler file that still builds it, and finds the in-process
/// backend the compiler builds instead.
#[test]
fn subprocess_solver_census_is_not_vacuous() {
    let verify_binary = strip_line_comments(&read("crates/trust-router/src/incremental_ay.rs"));
    assert!(
        !identifier_occurrences(&verify_binary, "IncrementalAYSession").is_empty(),
        "control: the identifier scan no longer finds `IncrementalAYSession` where it is defined"
    );
    let pass = strip_line_comments(&read(VERIFY_PASS));
    let in_process: Vec<String> = identifier_occurrences(&pass, "InProcessAyBackend")
        .into_iter()
        .map(|at| enclosing_fn(&pass, at))
        .collect();
    assert!(
        in_process.contains(&"discover_router_backends".to_string()),
        "control: `discover_router_backends` no longer builds the in-process ay backend \
         ({in_process:?}); the router's SMT lane moved and this guard must be re-traced"
    );
}

/// The router those backends feed has exactly one consumer, it is kernel
/// gated, and it is built fresh per call: no Session router state exists.
#[test]
fn unchecked_router_has_one_consumer_and_it_is_kernel_gated() {
    let sources = compiler_production_sources();
    for (callee, caller) in UNCHECKED_ROUTER_CHAIN {
        let calls: Vec<(String, String)> = sources
            .iter()
            .flat_map(|(path, code)| {
                call_sites(code, callee)
                    .into_iter()
                    .map(|at| (path.clone(), enclosing_fn(code, at)))
            })
            .collect();
        assert_eq!(
            calls,
            vec![(VERIFY_PASS.to_string(), caller.to_string())],
            "`{callee}` must have exactly one caller, `{caller}`: it carries the one router \
             trustc builds outside the native lanes, whose answers are accepted only through the \
             Clean kernel. A new consumer may take a router label as a premise; re-trace \
             {TCB_DOC}'s `Unvalidated solver verdicts`"
        );
    }

    let pass = strip_line_comments(&read(VERIFY_PASS));
    assert!(
        identifier_occurrences(&pass, "SessionRouterState").is_empty(),
        "Session router state is back: plan P4 / T4.1 builds the router fresh per call, so no \
         solver context or learned lemma outlives one Liskov check"
    );
    assert_eq!(
        compact(&item_body(&pass, "fn build_router(")),
        FRESH_ROUTER_BODY,
        "`build_router` no longer builds a fresh backend inventory per call"
    );

    let consumer =
        call_sites(&pass, "build_router").into_iter().next().expect("the consumer counted above");
    assert_eq!(
        compact(&enclosing_block(&pass, consumer)),
        LISKOV_CONSUMER,
        "the only consumer of the router changed shape. It must accept a router verdict only \
         when `trust_certify::certify_vc` re-derives it in the Clean kernel and use it for \
         nothing else; re-trace {TCB_DOC}'s `Unvalidated solver verdicts`"
    );
}

/// Native full-verifier evidence below publication grade — `Unchecked`
/// included — never becomes a `Proved` row: every `EvidenceStatus::Proved`
/// match arm in the pass is guarded by `is_unbounded_proof()`.
#[test]
fn native_evidence_below_publication_grade_never_becomes_proved() {
    let pass = compact(&strip_line_comments(&read(VERIFY_PASS)));
    let needle = "EvidenceStatus::Proved";
    let mut guarded_arms = 0usize;
    for (at, _) in pass.match_indices(needle) {
        let rest = &pass[at + needle.len()..];
        let arm_guard = if rest.starts_with("=>") {
            Some(rest.starts_with(
                "=>{if!evidence.is_unbounded_proof(){returnVerificationResult::Unknown{",
            ))
        } else if rest.starts_with("if") {
            Some(rest.starts_with("if!evidence.is_unbounded_proof()=>"))
        } else if rest.starts_with('|') {
            // An or-pattern is an ARM only when its `=>` comes before the `)`
            // that closes a `matches!`; either way it must not skip the guard.
            let arrow = rest.find("=>");
            let close = rest.find(')');
            match (arrow, close) {
                (Some(arrow), Some(close)) if arrow < close => Some(false),
                (Some(_), None) => Some(false),
                _ => None,
            }
        } else {
            None
        };
        match arm_guard {
            Some(true) => guarded_arms += 1,
            Some(false) => panic!(
                "an `{needle}` match arm in {VERIFY_PASS} is not guarded by \
                 `is_unbounded_proof()`: `{}…`. Native evidence below publication grade \
                 (Unchecked included) could become a `Proved` row that pre-authority \
                 consumers read",
                rest.chars().take(120).collect::<String>()
            ),
            None => {}
        }
    }
    assert_eq!(
        guarded_arms, 2,
        "expected exactly the two guarded native-evidence arms (`legacy_result_from_api_evidence` \
         and `transport_proof_status`); the parse no longer sees them"
    );
}

/// A `Proved` label publishes only through a row-bound authority:
/// `convert_result` names `Proved` in one arm only, mints no favorable status
/// itself, never consults a strength or assurance label, and that arm ends in
/// the authority lookup with an `(Unknown, None)` fallthrough.
#[test]
fn a_proved_label_publishes_only_through_a_row_bound_authority() {
    let pass = read(VERIFY_PASS);
    let body = compact(&item_body(&pass, "fn convert_result("));
    // Checked over the WHOLE body, not only the arm below: a strength-guarded
    // `Proved` arm placed ahead of it, or an early return on a label, would
    // publish without an authority and leave that arm untouched.
    assert_eq!(
        body.matches("Proved").count(),
        1,
        "convert_result names `Proved` outside its one authority arm: {body}"
    );
    for favorable in ["TrustStatus::Trusted", "TrustStatus::Certified"] {
        assert!(
            !body.contains(favorable),
            "convert_result mints `{favorable}` itself; a favorable status must come only from \
             `trust_disposition_for_authority`: {body}"
        );
    }
    for label in ["strength", "assurance", "is_proved"] {
        assert!(
            !body.contains(label),
            "convert_result consults `{label}`; a label is not authority: {body}"
        );
    }
    let start = body.find("VerificationResult::Proved{..}=>{").expect("convert_result Proved arm");
    let end = body[start..]
        .find("VerificationResult::Failed{..}=>")
        .map(|offset| offset + start)
        .expect("convert_result Failed arm follows the Proved arm");
    let arm = &body[start..end];
    assert!(
        arm.ends_with(
            "ifletSome(disposition)=trust_disposition_for_authority(authority,index,vc,result,\
             binding){returndisposition;}(TrustStatus::Unknown,TrustProofStrength::None)}"
        ),
        "convert_result's Proved arm no longer ends in the authority lookup and the \
         `(Unknown, None)` fallthrough: {arm}"
    );
}

/// The trace these guards encode is recorded where readers of the trust
/// boundary look for it, and names this guard.
#[test]
fn tcb_document_records_the_unchecked_premise_trace() {
    let doc = read(TCB_DOC);
    let section = doc
        .split_once(UNCHECKED_TCB_HEADING)
        .unwrap_or_else(|| panic!("{TCB_DOC} has no `{UNCHECKED_TCB_HEADING}` section"))
        .1;
    let section = section.split("\n## ").next().expect("section body");
    for named in [
        THIS_TEST_TARGET,
        "IncrementalAYSession",
        "others_all_proved",
        "verify-binary",
        "The producer walk covers `compiler/` only",
    ] {
        assert!(
            section.contains(named),
            "{TCB_DOC}'s `Unvalidated solver verdicts` section no longer names `{named}`"
        );
    }
}

/// Names of the top-level (unindented) `fn` items of comment-stripped source.
fn top_level_fn_names(code: &str) -> BTreeSet<String> {
    code.lines()
        .filter_map(|line| {
            ["fn ", "pub fn ", "pub(crate) fn ", "pub(super) fn "]
                .iter()
                .find_map(|intro| line.strip_prefix(intro))
        })
        .map(|rest| {
            let end =
                rest.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(rest.len());
            rest[..end].to_string()
        })
        .collect()
}

/// Body of the one top-level `fn name` item (generic or not) of comment-stripped
/// source. A second definition is a hard failure, as in `item_body`.
fn top_level_fn_body(code: &str, name: &str) -> String {
    let starts: Vec<usize> = ["\nfn ", "\npub fn ", "\npub(crate) fn ", "\npub(super) fn "]
        .iter()
        .flat_map(|intro| {
            let head = format!("{intro}{name}");
            code.match_indices(&head)
                .map(|(at, _)| at + head.len())
                .filter(|&end| code[end..].starts_with(['(', '<']))
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(
        starts.len(),
        1,
        "expected exactly one top-level `fn {name}` in {VERIFY_PASS}, found {}",
        starts.len()
    );
    balanced_block(code, starts[0])
}

/// Every `` `backticked` `` token of a cell.
fn code_spans(cell: &str) -> Vec<String> {
    cell.split('`').skip(1).step_by(2).map(str::to_string).collect()
}

/// Check elision is the one consumer that DELETES a runtime check, and its gates
/// may consult a bare `Proved` label only where `docs/TCB.md`'s consumer table
/// says so. Every top-level function of the pass that the elision seam reaches
/// through calls (transitively, within the pass) and that reads `is_proved()`
/// must be named in the table row that cites `elide_kernel_certified_checks`,
/// with the verdict `yes`, and that row may name no other one. This pins gate
/// (6), `hardened_overflow_twin_is_unproved`, which was live in the code while
/// the table omitted it. Methods and helpers in `trust_verify/` submodules are
/// outside the walk; the elision seam's own methods are authority checks
/// (`matches_row`, `matches_compiler_result`), not label reads.
#[test]
fn unchecked_consumer_table_names_every_label_reading_elision_gate() {
    let code = strip_line_comments(&read(VERIFY_PASS));
    let fns = top_level_fn_names(&code);
    let elide = "elide_kernel_certified_checks";
    let elide_body = top_level_fn_body(&code, elide);
    assert!(
        !elide_body.contains(".is_proved()"),
        "`{elide}` now reads a `Proved` label itself; name it as a consumer in {TCB_DOC}'s \
         `Unvalidated solver verdicts` table and extend this guard"
    );

    let mut reached = BTreeSet::new();
    let mut frontier = vec![elide_body];
    while let Some(body) = frontier.pop() {
        for name in &fns {
            if name != elide && !reached.contains(name) && !call_sites(&body, name).is_empty() {
                reached.insert(name.clone());
                frontier.push(top_level_fn_body(&code, name));
            }
        }
    }
    let label_readers: BTreeSet<String> = reached
        .into_iter()
        .filter(|name| top_level_fn_body(&code, name).contains(".is_proved()"))
        .collect();

    let doc = read(TCB_DOC);
    let section = doc
        .split_once(UNCHECKED_TCB_HEADING)
        .unwrap_or_else(|| panic!("{TCB_DOC} has no `{UNCHECKED_TCB_HEADING}` section"))
        .1;
    let consumers = table_under(section, "These are the consumers:");
    let elision_rows: Vec<&Vec<String>> =
        consumers.iter().filter(|row| code_spans(&row[0]).iter().any(|s| s == elide)).collect();
    let mut documented = BTreeSet::new();
    for row in &elision_rows {
        assert_eq!(row.len(), 3, "malformed consumer row {row:?}");
        assert!(
            yes_no(&row[2], "Would a bare `Unchecked` label pass it?", &row[0]),
            "{TCB_DOC}'s check-elision consumer row must answer `yes`: its guard reads the bare \
             `Proved` label. Row: {row:?}"
        );
        documented
            .extend(code_spans(&row[0]).into_iter().filter(|s| s != elide && fns.contains(s)));
    }
    assert_eq!(
        documented, label_readers,
        "{TCB_DOC}'s `Unvalidated solver verdicts` consumer table must name exactly the \
         functions the check-elision seam reaches that read a bare `Proved` label (left: named \
         in the table, right: found in {VERIFY_PASS})"
    );
}

// ---------------------------------------------------------------------------
// Dependency-TCB scopes — what an excluded Cargo Unit's `Conditional` row rests
// on.
//
// A verified Targo run declares every active Cargo Unit, and each one outside
// the proof frontier reaches the report as a `Conditional` crate-scope row
// whose tag `resolved_exclusion_scope` (`targo-trust/src/dep_tcb.rs`) chooses.
// The whole-crate verification gate then PASSES over the subset of those Units
// that `report_unit_is_dep_tcb_admitted` admits. Until 2026-10-01 docs/TCB.md
// named none of the six tags (0 of 6), so the premises a strict PASS rests on
// for a build script, a scoped-out dependency or an empty doctest Unit had no
// row in the document that is the boundary. The tags are now one `const`
// slice, `DEP_TCB_SCOPES`, which the classification is a lookup in; the tests
// below parse that slice and require one TCB row per entry, stating the
// entry's tag, exclusion reason, graph roles and whole-crate gate admission
// exactly as the code does.
// ---------------------------------------------------------------------------

const DEP_TCB_SOURCE: &str = "targo-trust/src/dep_tcb.rs";
const DEP_TCB_TRANSPORT: &str = "targo-trust/src/pipeline/transport.rs";
const DEP_TCB_SCOPES_ITEM: &str = "const DEP_TCB_SCOPES: &[DepTcbScope] = &[";
const DEP_TCB_CLASSIFIER_FN: &str = "resolved_exclusion_scope";
const DEP_TCB_GATE_FN: &str = "report_unit_is_dep_tcb_admitted";
const DEP_TCB_HEADING: &str = "\n## Dependency-TCB scopes\n";
/// The words a graph-roles cell carries exactly when its entry's
/// `only_when_dependencies_excluded` is set.
const DEP_TCB_DEPENDENCIES_EXCLUDED_QUALIFIER: &str = "only when dependencies are not verified";

/// One `DEP_TCB_SCOPES` entry as the source states it.
#[derive(Debug)]
struct DepTcbScopeEntry {
    tag: String,
    exclusion_reason: String,
    graph_roles: Vec<String>,
    only_when_dependencies_excluded: bool,
    whole_crate_gate_admits: bool,
}

/// The text between the bracket that opens at `open` and its match, skipping
/// string literals, so a bracket inside a detail string cannot end the block.
fn bracket_block(src: &str, open: usize, open_ch: char, close_ch: char) -> String {
    assert_eq!(src[open..].chars().next(), Some(open_ch), "expected `{open_ch}` at {open}");
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    for (offset, ch) in src[open..].char_indices() {
        if in_string {
            match (escaped, ch) {
                (true, _) => escaped = false,
                (false, '\\') => escaped = true,
                (false, '"') => in_string = false,
                _ => {}
            }
            continue;
        }
        if ch == '"' {
            in_string = true;
        } else if ch == open_ch {
            depth += 1;
        } else if ch == close_ch {
            depth -= 1;
            if depth == 0 {
                return src[open + 1..open + offset].to_string();
            }
        }
    }
    panic!("unterminated `{open_ch}` block at {open}");
}

/// The one occurrence of `needle` in `src`. A second is a hard failure: this
/// test could no longer tell which definition the document describes.
fn unique_at(src: &str, needle: &str, file: &str) -> usize {
    let occurrences = src.matches(needle).count();
    assert_eq!(
        occurrences, 1,
        "expected exactly one `{needle}` in {file}, found {occurrences}; this test can no longer \
         tell which definition {TCB_DOC} describes"
    );
    src.find(needle).expect("occurrence counted above")
}

/// The string literal assigned to `const <name>: &str` in `src`.
fn str_const(src: &str, name: &str, file: &str) -> String {
    let at = unique_at(src, &format!("const {name}: &str ="), file);
    let rest = &src[at..];
    let open = rest.find('"').unwrap_or_else(|| panic!("`{name}` in {file} is not a literal"));
    let value = &rest[open + 1..];
    value[..value.find('"').expect("terminated literal")].to_string()
}

/// The value of `field:` inside one struct-literal entry: the rest of the
/// line that starts with it, without the trailing comma.
fn entry_field<'a>(entry: &'a str, field: &str) -> &'a str {
    let needle = format!("{field}:");
    let line = entry
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with(&needle))
        .unwrap_or_else(|| panic!("a `DEP_TCB_SCOPES` entry has no `{field}` field: {entry}"));
    line[needle.len()..].trim().trim_end_matches(',').trim()
}

/// A field written as a literal `true` or `false`.
fn entry_bool(entry: &str, field: &str) -> bool {
    match entry_field(entry, field) {
        "true" => true,
        "false" => false,
        other => panic!("`{field}` must be a literal bool in {DEP_TCB_SOURCE}, got {other}"),
    }
}

/// The string literals of a field written as `&["a", "b"]`.
fn entry_str_list(entry: &str, field: &str) -> Vec<String> {
    let value = entry_field(entry, field);
    let inner = value
        .strip_prefix("&[")
        .and_then(|rest| rest.strip_suffix(']'))
        .unwrap_or_else(|| panic!("`{field}` must be a `&[..]` literal, got {value}"));
    inner
        .split(',')
        .map(str::trim)
        .filter(|item| !item.is_empty())
        .map(|item| {
            item.strip_prefix('"')
                .and_then(|rest| rest.strip_suffix('"'))
                .unwrap_or_else(|| panic!("`{field}` must list string literals, got {item}"))
                .to_string()
        })
        .collect()
}

/// Every `DEP_TCB_SCOPES` entry, in declaration order, with its exclusion
/// reason resolved to the wire string the transport declares.
fn dep_tcb_scopes() -> Vec<DepTcbScopeEntry> {
    let source = strip_line_comments(&read(DEP_TCB_SOURCE));
    let transport = read(DEP_TCB_TRANSPORT);
    let at = unique_at(&source, DEP_TCB_SCOPES_ITEM, DEP_TCB_SOURCE);
    let body = bracket_block(&source, at + DEP_TCB_SCOPES_ITEM.len() - 1, '[', ']');

    let mut entries = Vec::new();
    let mut cursor = 0;
    while let Some(found) = body[cursor..].find("DepTcbScope {") {
        let open = cursor + found + "DepTcbScope ".len();
        let entry = bracket_block(&body, open, '{', '}');
        let tag = entry_field(&entry, "tag");
        let tag = tag
            .strip_prefix('"')
            .and_then(|rest| rest.strip_suffix('"'))
            .unwrap_or_else(|| panic!("a `DEP_TCB_SCOPES` tag must be a string literal: {tag}"));
        entries.push(DepTcbScopeEntry {
            tag: tag.to_string(),
            exclusion_reason: str_const(
                &transport,
                entry_field(&entry, "exclusion_reason"),
                DEP_TCB_TRANSPORT,
            ),
            graph_roles: entry_str_list(&entry, "graph_roles"),
            only_when_dependencies_excluded: entry_bool(&entry, "only_when_dependencies_excluded"),
            whole_crate_gate_admits: entry_bool(&entry, "whole_crate_gate_admits"),
        });
        cursor = open + entry.len() + 2;
    }
    assert!(!entries.is_empty(), "parsed no `DEP_TCB_SCOPES` entries from {DEP_TCB_SOURCE}");
    entries
}

/// The parser is not vacuous: it reads a two-entry slice whose detail strings
/// hold brackets and braces, and refuses a tag that is not a literal.
#[test]
fn dep_tcb_entry_parser_reads_fields_and_skips_strings() {
    let src = "x &[\n    DepTcbScope {\n        tag: \"a-scope\",\n        \
               graph_roles: &[\"primary\", \"control\"],\n        \
               detail: \"a ] b } c [ {\",\n    },\n    DepTcbScope {\n        \
               tag: \"b-scope\",\n        graph_roles: &[],\n    },\n] y";
    let body = bracket_block(src, src.find('[').unwrap(), '[', ']');
    assert!(body.trim_end().ends_with("},"), "the slice ends at its own `]`: {body:?}");
    let first = bracket_block(&body, body.find('{').unwrap(), '{', '}');
    assert_eq!(entry_field(&first, "tag"), "\"a-scope\"");
    assert_eq!(entry_str_list(&first, "graph_roles"), ["primary", "control"]);
    let second_at = body.rfind("DepTcbScope {").unwrap() + "DepTcbScope ".len();
    let second = bracket_block(&body, second_at, '{', '}');
    assert_eq!(entry_field(&second, "tag"), "\"b-scope\"");
    assert!(entry_str_list(&second, "graph_roles").is_empty());
    assert!(std::panic::catch_unwind(|| entry_bool("flag: maybe,", "flag")).is_err());
    assert!(std::panic::catch_unwind(|| entry_str_list("roles: &[primary],", "roles")).is_err());
}

/// The classifier and the whole-crate gate read the slice and spell no string
/// of their own, so the slice is the one list the document has to match.
#[test]
fn dep_tcb_classification_reads_only_the_scope_slice() {
    let source = strip_line_comments(&read(DEP_TCB_SOURCE));
    for (name, reads) in
        [(DEP_TCB_CLASSIFIER_FN, "DEP_TCB_SCOPES"), (DEP_TCB_GATE_FN, "whole_crate_gate_admits")]
    {
        unique_at(&source, &format!("fn {name}("), DEP_TCB_SOURCE);
        let body = top_level_fn_body(&source, name);
        assert!(body.contains(reads), "`{name}` in {DEP_TCB_SOURCE} no longer reads `{reads}`");
        assert!(
            !body.contains('"'),
            "`{name}` in {DEP_TCB_SOURCE} spells a string of its own, so a tag, role or reason \
             can bypass `DEP_TCB_SCOPES` and the {TCB_DOC} table that mirrors it: {body}"
        );
    }
}

/// B5 step B: one `docs/TCB.md` row per tag `resolved_exclusion_scope` can
/// attach to a verdict, in declaration order, each stating the entry as the
/// code does. Measured red on 2026-10-01 before the table landed: 0 of the 6
/// tags were named anywhere in the document.
#[test]
fn tcb_document_has_a_row_for_every_dependency_tcb_scope() {
    let scopes = dep_tcb_scopes();
    let doc = read(TCB_DOC);

    let unnamed: Vec<&str> = scopes
        .iter()
        .map(|scope| scope.tag.as_str())
        .filter(|tag| !doc.contains(&format!("`{tag}`")))
        .collect();
    assert!(
        unnamed.is_empty(),
        "{} of the {} dependency-TCB scope tags `{DEP_TCB_CLASSIFIER_FN}` can attach to a \
         verdict are named nowhere in {TCB_DOC}: {unnamed:?}. Add their rows under `{}`.",
        unnamed.len(),
        scopes.len(),
        DEP_TCB_HEADING.trim()
    );

    let rows = table_under(&doc, DEP_TCB_HEADING);
    let documented: Vec<String> = rows.iter().map(|row| code_span(&row[0])).collect();
    let declared: Vec<String> = scopes.iter().map(|scope| scope.tag.clone()).collect();
    assert_eq!(
        documented,
        declared,
        "{TCB_DOC}'s `{}` table must list exactly the `DEP_TCB_SCOPES` tags, in declaration \
         order (left: the table, right: {DEP_TCB_SOURCE})",
        DEP_TCB_HEADING.trim()
    );
    for (row, scope) in rows.iter().zip(&scopes) {
        let tag = &scope.tag;
        assert_eq!(
            code_span(&row[1]),
            scope.exclusion_reason,
            "{TCB_DOC}: the `{tag}` row names the wrong exclusion reason"
        );
        assert_eq!(
            code_spans(&row[2]),
            scope.graph_roles,
            "{TCB_DOC}: the `{tag}` row's graph roles disagree with {DEP_TCB_SOURCE}"
        );
        assert_eq!(
            row[2].contains(DEP_TCB_DEPENDENCIES_EXCLUDED_QUALIFIER),
            scope.only_when_dependencies_excluded,
            "{TCB_DOC}: the `{tag}` row must say `{DEP_TCB_DEPENDENCIES_EXCLUDED_QUALIFIER}` \
             exactly when its entry sets `only_when_dependencies_excluded`"
        );
        assert_eq!(
            yes_no(&row[3], "Whole-crate gate admits", tag),
            scope.whole_crate_gate_admits,
            "{TCB_DOC}: the `{tag}` row's gate column disagrees with `whole_crate_gate_admits` \
             in {DEP_TCB_SOURCE}"
        );
        assert!(!row[4].is_empty(), "{TCB_DOC}: the `{tag}` row says nothing it rests on");
    }

    let section = doc.split_once(DEP_TCB_HEADING).expect("table_under found the heading").1;
    let section = section.split("\n## ").next().unwrap_or(section);
    let unresolved = str_const(
        &strip_line_comments(&read(DEP_TCB_SOURCE)),
        "UNRESOLVED_SCOPE_TAG",
        DEP_TCB_SOURCE,
    );
    assert!(
        section.contains(&format!("`{unresolved}`")),
        "{TCB_DOC}'s `{}` section must name the unresolved tag `{unresolved}` every \
         unmatched exclusion gets",
        DEP_TCB_HEADING.trim()
    );
}
