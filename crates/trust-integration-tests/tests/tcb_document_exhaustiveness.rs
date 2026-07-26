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
const STATIC_PROOF_FN: &str = "fn is_static_proof_for(";
const UNCONDITIONAL_FN: &str = "fn is_unconditional_static_proof_for(";
const KERNEL_EVIDENCE_FN: &str = "fn kernel_evidence_for(";
const ELIDE_FN: &str = "fn elide_kernel_certified_checks";
const VERIFY_PASS: &str = "compiler/rustc_mir_transform/src/trust_verify.rs";
const TCB_DOC: &str = "docs/TCB.md";
const GATE_MANIFEST: &str = "tests/run_trust_comprehensive_harness.sh";
const THIS_TEST_TARGET: &str = "tcb_document_exhaustiveness";

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
    let src = strip_line_comments(pass_src);
    let at = src.find(DISPOSITION_FN).unwrap_or_else(|| panic!("{DISPOSITION_FN} not found"));
    let body = balanced_block(&src, at + DISPOSITION_FN.len());

    let mut arms = Vec::new();
    for (offset, _) in body.match_indices("ResultProofAuthority::") {
        let rest = &body[offset + "ResultProofAuthority::".len()..];
        let name_end =
            rest.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(rest.len());
        let variant = rest[..name_end].to_string();

        const RETURN: &str = "Some((TrustStatus::";
        let ret = rest.find(RETURN).unwrap_or_else(|| panic!("{variant} has no disposition"));
        // A later arm's return must not be attributed to this one.
        if let Some(next) = rest.find("ResultProofAuthority::")
            && next < ret
        {
            panic!("{variant} has no disposition before the next arm");
        }
        let payload = &rest[ret + RETURN.len()..];
        let (status, tail) = payload.split_once(',').expect("disposition tuple");
        let strength = tail
            .split_once("))")
            .expect("disposition tuple close")
            .0
            .trim()
            .trim_start_matches("TrustProofStrength::")
            .to_string();
        arms.push((variant, status.trim().to_string(), strength));
    }
    assert!(!arms.is_empty(), "parsed no disposition arms");
    arms
}

/// The variants `trust_disposition_for_authority` reports as `Certified`.
fn certified_variants(pass_src: &str) -> BTreeSet<String> {
    disposition_arms(pass_src)
        .into_iter()
        .filter(|(_, status, _)| status == "Certified")
        .map(|(variant, ..)| variant)
        .collect()
}

/// Rows of the first markdown table under `heading`, cells trimmed, header and
/// separator dropped.
fn table_under(doc: &str, heading: &str) -> Vec<Vec<String>> {
    let section =
        doc.split_once(heading).unwrap_or_else(|| panic!("{TCB_DOC} has no `{heading}` heading")).1;
    let rows: Vec<Vec<String>> = section
        .lines()
        .skip_while(|line| !line.starts_with('|'))
        .take_while(|line| line.starts_with('|'))
        .map(|line| line.trim_matches('|').split('|').map(|cell| cell.trim().to_string()).collect())
        .collect();
    assert!(rows.len() > 2, "`{heading}` table has no body rows");
    rows[2..].to_vec()
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
    // the table calls kernel-checked. Equality is deliberately NOT asserted:
    // `EnsuresCitationDischarge` is kernel-checked at grade time and retains
    // the graded theorem's name, not a `trust_ir::ProofEvidence`.
    let variants = enum_variants(&pass);
    let evidence_body = item_body(&pass, KERNEL_EVIDENCE_FN);
    let carriers: BTreeSet<String> = match_self_arms(&evidence_body, &variants)
        .into_iter()
        .filter(|(_, arm)| arm.contains("Some("))
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
